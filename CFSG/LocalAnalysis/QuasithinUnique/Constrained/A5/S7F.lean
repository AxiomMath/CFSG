module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7E

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] noncomputable def A4W : Subgroup G :=
  (alternatingGroup (Fin 4)).map
    (H.subtype.comp (X.huHom.comp (MonoidHom.inr (DihedralGroup 4) (Equiv.Perm (Fin 4)))))

theorem mem_A4W {x : G} : x ∈ X.A4W ↔
    ∃ s : Equiv.Perm (Fin 4), Equiv.Perm.sign s = 1 ∧ ((X.huHom (1, s) : ↥H) : G) = x := by
  unfold A4W
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Equiv.Perm.mem_alternatingGroup.mp hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Equiv.Perm.mem_alternatingGroup.mpr hs, rfl⟩

theorem pResidual_Hu
    : pResidualOf 2 (H ⊓ centralizerElem C.u0) = X.A4W := by
  rw [pResidualOf_eq_opResidual, opResidual]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxHu, hcop⟩
    obtain ⟨⟨d, s⟩, hy⟩ := X.huHom_surj (h := ⟨x, hxHu.1⟩) hxHu.2
    have hodd : Odd (orderOf x) := by
      have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop.symm
      exact Nat.odd_iff.mpr (by omega)
    have hpow : (⟨x, hxHu.1⟩ : ↥H) ^ orderOf x = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one x)
    rw [← hy, ← map_pow] at hpow
    have h1 : ((d, s) : DihedralGroup 4 × Equiv.Perm (Fin 4)) ^ orderOf x = 1 :=
      X.huHom_inj (hpow.trans (map_one _).symm)
    have hd : d ^ orderOf x = 1 := congrArg Prod.fst h1
    have hs : s ^ orderOf x = 1 := congrArg Prod.snd h1
    have hd1 : d = 1 := by
      have := (pow_gcd_eq_one (a := d)).mpr ⟨dihedral4_pow d, hd⟩
      have hg : Nat.gcd 4 (orderOf x) = 1 := by
        have h2 : Nat.Coprime (2 ^ 2) (orderOf x) :=
          Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
        simpa using h2
      rwa [hg, pow_one] at this
    have hsign : Equiv.Perm.sign s = 1 := by
      have h2 : Equiv.Perm.sign s ^ orderOf x = 1 := by
        rw [← map_pow, hs, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
      · exact h
      · rw [h, hodd.neg_one_pow] at h2
        exact absurd h2 (by decide)
    show x ∈ X.A4W
    rw [mem_A4W]
    refine ⟨s, hsign, ?_⟩
    subst hd1
    exact congrArg Subtype.val hy
  · show X.A4W ≤ _
    unfold A4W
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨c, hc, rfl⟩
    have hc3 : orderOf c = 3 := hc.orderOf
    refine ⟨⟨(X.huHom (1, c)).2, X.huHom_mem_cent (1, c)⟩, ?_⟩
    have hdvd : orderOf (H.subtype.comp (X.huHom.comp (MonoidHom.inr (DihedralGroup 4)
        (Equiv.Perm (Fin 4)))) c) ∣ 3 := hc3 ▸ orderOf_map_dvd _ c
    exact Nat.Coprime.coprime_dvd_left hdvd (by decide)

theorem U_cent_A4W_iff (v : evenWeight 5) :
    ((C.iV v : ↥H) : G) ∈ Subgroup.centralizer (X.A4W : Set G) ↔
      v.1 = 0 ∨ v.1 = g1 ∨ v.1 = gW1 ∨ v.1 = gW1' := by
  have hpi : ∀ s : Equiv.Perm (Fin 4), C.D.π (X.huHom (1, s)) = (ptab s).2 := by
    intro s
    rw [X.pi_huHom]
    show (dtab 1).2 * (ptab s).2 = _
    rw [dtab_one]
    exact one_mul _
  constructor
  · intro hc
    apply fix_A4 v.1 v.2
    intro s hs
    have hmem : ((X.huHom (1, s) : ↥H) : G) ∈ (X.A4W : Set G) :=
      (X.mem_A4W).mpr ⟨s, hs, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hmem
    have h2 : X.huHom (1, s) * C.iV v = C.iV v * X.huHom (1, s) := Subtype.ext h1
    have := X.vact_fixed_of_comm _ v h2
    rw [hpi] at this
    exact congrArg Subtype.val this
  · intro hv
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨s, hs, rfl⟩ := (X.mem_A4W).mp hz
    obtain ⟨h0, h1, h2, h3⟩ := fix_A4_mem s hs
    have hfix : vact (C.D.π (X.huHom (1, s))) v = v := by
      rw [hpi]
      apply Subtype.ext
      show pact (ptab s).2 v.1 = v.1
      rcases hv with h | h | h | h
      · rw [h]
        exact h0
      · rw [h]
        exact h1
      · rw [h]
        exact h2
      · rw [h]
        exact h3
    have hc := C.conj_iV X.hTC (X.huHom (1, s)) v
    rw [hfix] at hc
    have : X.huHom (1, s) * C.iV v = C.iV v * X.huHom (1, s) := by
      calc X.huHom (1, s) * C.iV v =
          (X.huHom (1, s) * C.iV v * (X.huHom (1, s))⁻¹) * X.huHom (1, s) := by group
        _ = C.iV v * X.huHom (1, s) := by rw [hc]
    exact congrArg Subtype.val this

theorem CU_card :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer
      (pResidualOf 2 (H ⊓ centralizerElem C.u0) : Set G)) = 4 := by
  rw [X.pResidual_Hu]
  let f : Fin 4 → ↥(blockU L ⊓ Subgroup.centralizer (X.A4W : Set G)) := fun i =>
    ⟨((C.iV ⟨vecF i, vecF_even i⟩ : ↥H) : G), C.iV_mem_U _,
      (X.U_cent_A4W_iff _).mpr (vecF_mem i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have h0 := congrArg Subtype.val hij
      have h1 : C.iV ⟨vecF i, vecF_even i⟩ = C.iV ⟨vecF j, vecF_even j⟩ := Subtype.ext h0
      have h2 := C.iV_inj X.hTC h1
      exact vecF_inj i j (congrArg Subtype.val h2)
    · rintro ⟨x, hxU, hxC⟩
      obtain ⟨w, rfl⟩ := C.exists_iV_of_mem_U hxU
      obtain ⟨i, hi⟩ := vecF_cover w.1 ((X.U_cent_A4W_iff w).mp hxC)
      refine ⟨i, Subtype.ext ?_⟩
      have : (⟨vecF i, vecF_even i⟩ : evenWeight 5) = w := Subtype.ext hi
      show ((C.iV ⟨vecF i, vecF_even i⟩ : ↥H) : G) = ((C.iV w : ↥H) : G)
      rw [this]
  exact (Nat.card_eq_of_bijective f hf).symm.trans (by simp)

theorem CU_conj {z : G} (hz : z = C.zU) {v : G}
    (hv : v ∈ blockU L ⊓ Subgroup.centralizer
      (pResidualOf 2 (H ⊓ centralizerElem C.u0) : Set G))
    (hv1 : v ≠ 1) (hvu : v ≠ C.u0) : ∃ l ∈ L, v = l⁻¹ * z * l := by
  rw [X.pResidual_Hu] at hv
  obtain ⟨w, rfl⟩ := C.exists_iV_of_mem_U hv.1
  have hw := (X.U_cent_A4W_iff w).mp hv.2
  have hw0 : w.1 ≠ 0 := by
    intro h
    apply hv1
    have : w = 0 := Subtype.ext h
    rw [this, C.iV_zero]
    rfl
  have hwg : w.1 ≠ g1 := by
    intro h
    apply hvu
    have : w = g1w := Subtype.ext h
    rw [this]
    rfl
  have hw2 : w.1 = gW1 ∨ w.1 = gW1' := by
    rcases hw with h | h | h | h
    · exact absurd h hw0
    · exact absurd h hwg
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨σ, hsign, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ pact σ z0 = w.1 := by
    rcases hw2 with h | h
    · rw [h]
      exact gW1_conj_z0
    · rw [h]
      exact gW1'_conj_z0
  obtain ⟨h, hh⟩ := C.hsurj σ
  refine ⟨((h⁻¹ : ↥H) : G), ?_, ?_⟩
  · rw [X.mem_L_iff (h⁻¹), map_inv, hh]
    exact Equiv.Perm.mem_alternatingGroup.mpr (by rw [Equiv.Perm.sign_inv]; exact hsign)
  · have hc := C.conj_iV X.hTC h StdCfg.z0V
    rw [hh] at hc
    have hvw : vact σ StdCfg.z0V = w := Subtype.ext hσ
    rw [hvw] at hc
    rw [hz, C.zU_eq_iV]
    have h3 := congrArg Subtype.val hc.symm
    show ((C.iV w : ↥H) : G) = ((h : G)⁻¹)⁻¹ * ((C.iV StdCfg.z0V : ↥H) : G) * (h : G)⁻¹
    rw [inv_inv]
    exact h3

end Sec

end CFSG.QuasithinUnique.A5
