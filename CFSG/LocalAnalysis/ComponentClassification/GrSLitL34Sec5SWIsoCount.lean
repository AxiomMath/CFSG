module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoReal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem card_conjSet_eq {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ PSL3Four.S, ∃ e, q e = s)
    (hqS : ∀ e, q e ∈ PSL3Four.S) (hqker : q.ker = center (Jhat J)) {r : Equiv.Perm (Fin 42)}
    (hr : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹) :
    Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} =
      Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) *
        Nat.card (zStarIn J) := by
  set φ : ↥J →* Equiv.Perm (Fin 42) := q.comp (jq J) with hφ
  set C := centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S with hC
  have hCφ : C ≤ φ.range := by
    intro s hs
    obtain ⟨e, he⟩ := hqsurj s hs.2
    obtain ⟨j, rfl⟩ := jq_surjective J e
    exact ⟨j, he⟩
  have h1 := card_comap_eq φ C hCφ
  have hker : Nat.card φ.ker = Nat.card (zStarIn J) := by
    have hk : φ.ker = Open.fusionZStar J := by
      ext j
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hqker,
        ← mem_zStarIn_iff j.2, zStarIn, mem_map]
      constructor
      · rintro ⟨j', hj', hjj⟩
        rwa [Subtype.ext hjj] at hj'
      · intro hj
        exact ⟨j, hj, rfl⟩
    rw [hk, zStarIn, Subgroup.card_map_of_injective Subtype.val_injective]
  have hset : Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = Nat.card (C.comap φ) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun j => ?_
    have hmem : (j : G)⁻¹ * x⁻¹ * j * x ∈ J := by
      have := conj_mem_of_mem_normalizer hxN j.2
      have e1 : (j : G)⁻¹ * x⁻¹ * j * x = (j : G)⁻¹ * (x⁻¹ * j * x) := by group
      rw [e1]
      exact J.mul_mem (J.inv_mem j.2) this
    rw [mem_zStarIn_iff hmem]
    have e1 : (⟨(j : G)⁻¹ * x⁻¹ * j * x, hmem⟩ : J) = j⁻¹ * conjJ J hxN j := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, ← hqker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, ← betaHat_jq, hr,
      mem_comap, hC, mem_inf, mem_centralizer_singleton_iff, inv_mul_conj_eq_one_iff]
    simp only [hφ, MonoidHom.comp_apply]
    exact ⟨fun h => ⟨h, hqS _⟩, fun h => h.1⟩
  rw [hset, h1, hker]

theorem card_centralizer_conj {c r : Equiv.Perm (Fin 42)}
    (hc : c ∈ PSL3Four.R) :
    Nat.card ↥(centralizer ({c * r * c⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) =
      Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) := by
  have hmap : (centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S).map
      (MulAut.conj c).toMonoidHom =
      centralizer ({c * r * c⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨g', ⟨hg'r, hg'S⟩, rfl⟩
      refine ⟨?_, PSL3Four.conj_mem_S hc hg'S⟩
      calc c * g' * c⁻¹ * (c * r * c⁻¹) = c * (g' * r) * c⁻¹ := by group
        _ = c * (r * g') * c⁻¹ := by rw [hg'r]
        _ = c * r * c⁻¹ * (c * g' * c⁻¹) := by group
    · rintro ⟨hgr, hgS⟩
      refine ⟨c⁻¹ * g * c, ⟨?_, ?_⟩, by group⟩
      · have h1 : c⁻¹ * (g * (c * r * c⁻¹)) * c = c⁻¹ * (c * r * c⁻¹ * g) * c := by rw [hgr]
        calc c⁻¹ * g * c * r = c⁻¹ * (g * (c * r * c⁻¹)) * c := by group
          _ = c⁻¹ * (c * r * c⁻¹ * g) * c := h1
          _ = r * (c⁻¹ * g * c) := by group
      · have h1 := PSL3Four.conj_mem_S (PSL3Four.R.inv_mem hc) hgS
        rwa [inv_inv] at h1
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]

variable {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)}

namespace WStd

theorem card_conjSet_of_label (D : WStd J S hSN) {e : G}
    (he : e ∈ S) {t i : ℕ} (hi : i < 36) (hy : (D.ψ ⟨e, he⟩)⁻¹ = yPerm t i) {lab : ℕ}
    (hlab : typeOf t i = lab) (hlab3 : lab < 3) :
    Nat.card {j : J // (j : G)⁻¹ * e⁻¹ * j * e ∈ zStarIn J} =
      Nat.card ↥(centralizer ({rhoPerm lab} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) *
        Nat.card (zStarIn J) := by
  obtain ⟨t', -, j, -, hconj⟩ := typeOf_spec hlab hlab3
  rw [card_conjSet_eq (hSN he) D.hQ.qsurj D.hQ.qS D.hQ.ker (r := yPerm t i) fun x => by
      rw [D.hψ ⟨e, he⟩ x, ← hy, inv_inv], ← hconj, card_centralizer_conj (yPerm_mem_R t' j)]

theorem isL34Unitary_of_label (D : WStd J S hSN) {e : G}
    (he : e ∈ S) (he2 : e * e = 1) (heK : e ∉ withKernel J) {t i : ℕ} (hi : i < 36)
    (hy : (D.ψ ⟨e, he⟩)⁻¹ = yPerm t i) (hlab : typeOf t i = 2) : IsL34Unitary J e := by
  refine ⟨hSN he, he2, heK, ?_⟩
  rw [D.card_conjSet_of_label he hi hy hlab (by norm_num)]
  have h72 : Nat.card ↥(centralizer ({rhoPerm 2} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) = 72 :=
    PSL3Four.card_C₄
  rw [h72]

theorem isL34Field_of_label (D : WStd J S hSN) {e : G}
    (he : e ∈ S) (he2 : e * e = 1) (heK : e ∉ withKernel J) {t i : ℕ} (hi : i < 36)
    (hy : (D.ψ ⟨e, he⟩)⁻¹ = yPerm t i) (hlab : typeOf t i = 0) :
    HarrisLit.EndB.IsL34Field J e := by
  refine ⟨hSN he, he2, heK, ?_⟩
  rw [D.card_conjSet_of_label he hi hy hlab (by norm_num)]
  have h168 : Nat.card ↥(centralizer ({rhoPerm 0} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) =
      168 :=
    PSL3Four.card_C₂
  rw [h168]

theorem zEquiv (D : WStd J S hSN) (hS2 : IsPGroup 2 S) :
    Nonempty (↥(S ⊓ zStarIn J) ≃* ↥D.q.ker) := by
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have hPJ : S ⊓ J ≤ J := inf_le_right
  have hZJ : ∀ z ∈ S ⊓ zStarIn J, z ∈ S ⊓ J := fun z hz =>
    mem_inf.mpr ⟨(mem_inf.mp hz).1, (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp hz).2⟩
  have hmem : ∀ z : ↥(S ⊓ zStarIn J), jq J ⟨z, hPJ (hZJ z z.2)⟩ ∈ D.q.ker := fun z => by
    rw [D.hQ.ker]
    exact (mem_zStarIn_iff _).1 (mem_inf.mp z.2).2
  let f : ↥(S ⊓ zStarIn J) →* ↥D.q.ker :=
    { toFun := fun z => ⟨jq J ⟨z, hPJ (hZJ z z.2)⟩, hmem z⟩
      map_one' := Subtype.ext (map_one (jq J))
      map_mul' := fun z z' => Subtype.ext
        (map_mul (jq J) ⟨z, hPJ (hZJ z z.2)⟩ ⟨z', hPJ (hZJ z' z'.2)⟩) }
  have hinj : Function.Injective f := fun z z' h => Subtype.ext
    (eq_of_jq_eq hPJ hP2 (hZJ z z.2) (hZJ z' z'.2) (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    have he1 : D.q e ∈ T0 := by
      rw [MonoidHom.mem_ker.mp he]
      exact one_mem _
    obtain ⟨p, hpP, hpJ, rfl⟩ := (D.hT0 e).1 he1
    have hpZ : p ∈ zStarIn J := by
      rw [mem_zStarIn_iff hpJ, ← D.hQ.ker]
      exact he
    exact ⟨⟨p, mem_inf.mpr ⟨(mem_inf.mp hpP).1, hpZ⟩⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem card_Z_of_kbZero (D : WStd J S hSN) (hS2 : IsPGroup 2 S) (hz : kbZero D.kb = true) :
    Nat.card ↥(S ⊓ zStarIn J) = 16 := by
  obtain ⟨f⟩ := D.zEquiv hS2
  rw [Nat.card_congr f.toEquiv, card_ker_of_kbZero D.hQ D.hkb hz]

theorem isCyclic_Z_of_kbCyc (D : WStd J S hSN) (hS2 : IsPGroup 2 S) (hc : kbCyc D.kb = true) :
    IsCyclic ↥(S ⊓ zStarIn J) ∧ Nat.card ↥(S ⊓ zStarIn J) ≤ 4 := by
  obtain ⟨f⟩ := D.zEquiv hS2
  obtain ⟨g, hg, hg4⟩ := exists_ker_eq_zpowers D.hQ D.hkb hc
  have hcyc : IsCyclic ↥D.q.ker := by
    rw [hg]
    infer_instance
  refine ⟨isCyclic_of_surjective f.symm.toMonoidHom f.symm.surjective, ?_⟩
  rw [Nat.card_congr f.toEquiv, hg, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) hg4

theorem Z_eq_bot_of_kbFull (D : WStd J S hSN) (hS2 : IsPGroup 2 S) (hf : kbFull D.kb = true) :
    S ⊓ zStarIn J = ⊥ := by
  obtain ⟨f⟩ := D.zEquiv hS2
  have hk := ker_eq_bot_of_kbFull D.hQ D.hkb hf
  rw [eq_bot_iff]
  intro z hz
  have hinj := (MonoidHom.ker_eq_bot_iff D.q).mp hk
  have h1 : f ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    apply hinj
    rw [MonoidHom.mem_ker.mp (f ⟨z, hz⟩).2, OneMemClass.coe_one, map_one]
  have h2 : (⟨z, hz⟩ : ↥(S ⊓ zStarIn J)) = 1 := f.injective (h1.trans (map_one f).symm)
  rw [mem_bot]
  exact congrArg Subtype.val h2

end WStd

end CFSG.ComponentClassification.GrSLit.GrS5S
