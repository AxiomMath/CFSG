module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoPlane
public import CFSG.LieType.SeitzGeneration.InnerSymplecticThree
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness

public section

namespace CFSG.LieType.SeitzGeneration.UnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial

section Abstract

theorem closure_centralizers_map {G Q : Type*} [Group G] [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) {X : Set G}
    (hX : Subgroup.closure {g : G | ∃ x ∈ X, g * x = x * g} = ⊤) {E : Subgroup Q}
    (hE : ∀ x ∈ X, π x ≠ 1 ∧ π x ∈ E) :
    Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  rw [eq_top_iff]
  have h : (Subgroup.closure {g : G | ∃ x ∈ X, g * x = x * g}).map π ≤
      Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π x, (hE x hx).2, (hE x hx).1, ?_⟩
    rw [← map_mul, ← map_mul, hgx]
  rw [hX, Subgroup.map_top_of_surjective π hπ] at h
  exact h

end Abstract

section Proj

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

@[expose] noncomputable def projSU (hU : UnitaryFieldData ℓ f K) (n : ℕ) :
    SUid (unitaryInvolution K ℓ f) n →* StatedProj (StatedSU n (ℓ ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K))).comp
    (Subgroup.inclusion (SUid_eq_statedSU hU.card_eq_sq n).le)

theorem projSU_surjective (hU : UnitaryFieldData ℓ f K) :
    Function.Surjective (projSU hU n) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
    ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) y
  exact ⟨⟨z, (SUid_eq_statedSU hU.card_eq_sq n).symm ▸ z.2⟩, rfl⟩

theorem projSU_eq_one_iff (hU : UnitaryFieldData ℓ f K) (x : SUid (unitaryInvolution K ℓ f) n) :
    projSU hU n x = 1 ↔ (x : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
  rw [projSU, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

end Proj

section Scalar

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem not_mem_scalars_of_eigen (g : SUid σ n) (i j : Fin n) {a b : K}
    (hi : ∀ v : Fin n → K, (g • v) i = a * v i) (hj : ∀ v : Fin n → K, (g • v) j = b * v j)
    (hab : a ≠ b) : (g : GL (Fin n) K) ∉ StatedScalars (Fin n) K := by
  intro h
  obtain ⟨c, hc⟩ := h
  have hm : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hg : ∀ (v : Fin n → K) (i : Fin n), (g • v) i = (c : K) * v i := fun v i => by
    rw [smul_def, hm, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h1 := hi (Pi.single i 1)
  have h2 := hj (Pi.single j 1)
  rw [hg] at h1 h2
  simp only [Pi.single_eq_same, mul_one] at h1 h2
  exact hab (h1.symm.trans h2)

end Scalar

section Plane

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_plane_proj (hU : UnitaryFieldData ℓ f K) (hq2 : ℓ ^ f = 2) (hn : 5 ≤ n) :
    ∃ E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 ∧
      Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K ℓ f) :=
    isUnitaryInvolution_unitaryInvolution hU.card_eq_sq
  have hcard4 : Nat.card K = 4 := by
    rw [hU.card_eq_sq, hq2]
    norm_num
  have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).1
    (hq2 ▸ dvd_pow_self ℓ (by have := hU.one_le; omega))
  have h2 : (1 : K) + 1 = 0 := by
    have h := CharP.cast_eq_zero K ℓ
    rw [hℓ2] at h
    rw [one_add_one_eq_two]
    exact_mod_cast h
  have hq : ∀ c : K, c ≠ 0 → unitaryInvolution K ℓ f c * c = 1 := fun c hc => by
    have hc3 : c ^ 3 = 1 := by
      have := Fintype.ofFinite K
      have h := FiniteField.pow_card_sub_one_eq_one c hc
      rwa [← Nat.card_eq_fintype_card, hcard4] at h
    rw [unitaryInvolution_apply, hq2]
    linear_combination hc3
  have hKunits : Nat.card Kˣ = 3 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard4]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω', hω'⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hKunits])
  have hω3 : (ω' : K) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω'
    rw [hω'] at this
    simpa using congrArg Units.val this
  have hω1 : (ω' : K) ≠ 1 := fun h => by
    have : ω' = 1 := Units.ext h
    rw [this, orderOf_one] at hω'
    omega
  have hω : unitaryInvolution K ℓ f ω' * ω' = 1 := hq _ ω'.ne_zero
  have hω0 : (ω' : K) ≠ 0 := ω'.ne_zero
  have hgen := closure_cent_eq_top hω hω3 hσ hq h2 hn
  set x₁' := x₁ (unitaryInvolution K ℓ f) hω hω3 hn with hx₁
  set x₂' := x₂ (unitaryInvolution K ℓ f) hω hω3 hn with hx₂
  have hX : Subgroup.closure {g : SUid (unitaryInvolution K ℓ f) n |
      ∃ x ∈ ({x₁', x₂', x₁' * x₂'} : Set (SUid (unitaryInvolution K ℓ f) n)),
        g * x = x * g} = ⊤ := by
    have hset : {g : SUid (unitaryInvolution K ℓ f) n |
        ∃ x ∈ ({x₁', x₂', x₁' * x₂'} : Set (SUid (unitaryInvolution K ℓ f) n)), g * x = x * g} =
        {g | g * x₁' = x₁' * g ∨ g * x₂' = x₂' * g ∨ g * (x₁' * x₂') = (x₁' * x₂') * g} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl | rfl | rfl, h⟩
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]
      · rintro (h | h | h)
        exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr (Or.inl rfl), h⟩, ⟨_, Or.inr (Or.inr rfl), h⟩]
    rw [hset]
    exact hgen
  have ns₁ : (x₁' : GL (Fin n) K) ∉ StatedScalars (Fin n) K :=
    not_mem_scalars_of_eigen x₁' ⟨0, by omega⟩ ⟨2, by omega⟩ (a := (ω' : K)) (b := 1)
      (fun v => by rw [hx₁, x₁_smul_apply hω hω3 hn]; simp)
      (fun v => by rw [hx₁, x₁_smul_apply hω hω3 hn]; simp) hω1
  have ns₂ : (x₂' : GL (Fin n) K) ∉ StatedScalars (Fin n) K :=
    not_mem_scalars_of_eigen x₂' ⟨0, by omega⟩ ⟨2, by omega⟩ (a := 1) (b := (ω' : K))
      (fun v => by rw [hx₂, x₂_smul_apply hω hω3 hn]; simp)
      (fun v => by rw [hx₂, x₂_smul_apply hω hω3 hn]; simp) (Ne.symm hω1)
  have hωω : (ω' : K) ≠ (ω' : K) * ω' := fun h => hω1 (by
    have : (ω' : K) * ((ω' : K) - 1) = 0 := by linear_combination -h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0)))
  have ns₁₂ : ((x₁' * x₂' : SUid (unitaryInvolution K ℓ f) n) : GL (Fin n) K) ∉
      StatedScalars (Fin n) K :=
    not_mem_scalars_of_eigen (x₁' * x₂') ⟨0, by omega⟩ ⟨4, by omega⟩ (a := (ω' : K))
      (b := (ω' : K) * ω')
      (fun v => by rw [hx₁, hx₂, x₁_mul_x₂_smul_apply hω hω3 hn]; simp)
      (fun v => by rw [hx₁, hx₂, x₁_mul_x₂_smul_apply hω hω3 hn]; simp [mul_assoc]) hωω
  have ns₂₁ : ((x₂' * (x₁' * x₁') : SUid (unitaryInvolution K ℓ f) n) : GL (Fin n) K) ∉
      StatedScalars (Fin n) K :=
    not_mem_scalars_of_eigen (x₂' * (x₁' * x₁')) ⟨0, by omega⟩ ⟨2, by omega⟩
      (a := (ω' : K) * ω') (b := (ω' : K))
      (fun v => by
        rw [mul_smul, mul_smul, hx₂, x₂_smul_apply hω hω3 hn, hx₁, x₁_smul_apply hω hω3 hn,
          x₁_smul_apply hω hω3 hn]
        simp [mul_assoc])
      (fun v => by
        rw [mul_smul, mul_smul, hx₂, x₂_smul_apply hω hω3 hn, hx₁, x₁_smul_apply hω hω3 hn,
          x₁_smul_apply hω hω3 hn]
        simp)
      (Ne.symm hωω)
  set π := projSU hU n with hπ
  have ha1 : π x₁' ≠ 1 := fun h => ns₁ ((projSU_eq_one_iff hU x₁').1 h)
  have hb1 : π x₂' ≠ 1 := fun h => ns₂ ((projSU_eq_one_iff hU x₂').1 h)
  have hab1 : π (x₁' * x₂') ≠ 1 := fun h => ns₁₂ ((projSU_eq_one_iff hU _).1 h)
  have hcommπ : Commute (π x₁') (π x₂') := by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, x₁_comm_x₂ hω hω3 hn]
  have ha3 : π x₁' ^ 3 = 1 := by rw [← map_pow, x₁_cube hω hω3 hn, map_one]
  have hb3 : π x₂' ^ 3 = 1 := by rw [← map_pow, x₂_cube hω hω3 hn, map_one]
  have hao : orderOf (π x₁') = 3 := orderOf_eq_prime ha3 ha1
  have hbo : orderOf (π x₂') = 3 := orderOf_eq_prime hb3 hb1
  have hind : π x₂' ∉ Subgroup.zpowers (π x₁') := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk3 : π x₁' ^ (k % 3) = π x₂' := by
      rw [← hk]
      have := zpow_mod_orderOf (π x₁') k
      rw [hao] at this
      exact_mod_cast this
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with h | h | h
    · rw [h, zpow_zero] at hk3
      exact hb1 hk3.symm
    · rw [h, zpow_one] at hk3
      apply ns₂₁ ((projSU_eq_one_iff hU _).1 _)
      rw [← hπ, map_mul, map_mul, ← hk3]
      exact (pow_three (π x₁')).symm.trans ha3
    · rw [h] at hk3
      apply ns₁₂ ((projSU_eq_one_iff hU _).1 _)
      rw [← hπ, map_mul, ← hk3, zpow_two]
      exact (pow_three (π x₁')).symm.trans ha3
  refine ⟨Subgroup.closure {π x₁', π x₂'}, isElemAbelian_closure_of_comm ?_ ?_,
    card_closure_pair' Nat.prime_three hcommπ hao hbo hind, ?_⟩
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | exact Commute.refl _ | exact hcommπ | exact hcommπ.symm
  · intro x hx
    rcases hx with rfl | rfl
    · exact ha3
    · exact hb3
  · refine closure_centralizers_map π (projSU_surjective hU) hX fun x hx => ?_
    rcases hx with rfl | rfl | rfl
    · exact ⟨ha1, Subgroup.subset_closure (Or.inl rfl)⟩
    · exact ⟨hb1, Subgroup.subset_closure (Or.inr rfl)⟩
    · refine ⟨hab1, ?_⟩
      rw [map_mul]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))

end Plane

end CFSG.LieType.SeitzGeneration.UnitaryTwo

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration.UnitaryTwo

theorem innerEx_unitaryTwo_model {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) (hq2 : q.card = 2) (hm : 4 ≤ m)
    (hex : ∃ E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩)), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 ∧ InnerPlane ⟨.twistedA m q, hv⟩ 3 E) :
    ∃ E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩)), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      InnerPlane ⟨.twistedA m q, hv⟩ 3 E ∧ PlaneGen E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, -⟩ := Prod.mk.inj h32
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  obtain ⟨E₀, -, hE₀c, hE₀⟩ := hex
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA m q, hv⟩)
    (range_conj_ne_bot_of_inner Nat.prime_three hE₀c hE₀)
  obtain ⟨Ē, hĒ, hĒc, hĒgen⟩ := exists_plane_proj hU (by rw [hqcard]; exact hq2)
    (by omega : 5 ≤ m + 1)
  exact exists_planeGen_of_model hinj e hĒ hĒc hĒgen

theorem innerEx_unitaryTwo :
    ∀ (d : TauCeti.ValidLieTypeIndex),
      (∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧ q.card = 2 ∧ 4 ≤ m) →
      ∀ p : ℕ, p = 3 → p ≠ d.1.characteristic → ¬ IsD2SeitzException p d.1 →
      (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        InnerPlane d p E) →
      ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        InnerPlane d p E ∧ PlaneGen E := by
  rintro ⟨d, hv⟩ ⟨m, q, rfl, hq2, hm⟩ p rfl hpd hex hE
  exact innerEx_unitaryTwo_model hv hq2 hm hE

end CFSG.LieType.SeitzGeneration
