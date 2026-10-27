module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentLift
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial

theorem not_mem_zpowers_of_apply {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
    {a b : ∀ i, M i} {j : ι} (ha : a j = 1) (hb : b j ≠ 1) : b ∉ Subgroup.zpowers a := by
  rintro ⟨k, rfl⟩
  apply hb
  change (a ^ k) j = 1
  rw [Pi.pow_apply, ha, _root_.one_zpow]

theorem map_not_mem_zpowers {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {a b : G} (h : b ∉ Subgroup.zpowers a) :
    φ b ∉ Subgroup.zpowers (φ a) := by
  rintro ⟨k, hk⟩
  exact h ⟨k, hφ (by rw [map_zpow]; exact hk)⟩

theorem commutator_subgroupOf_of_le {G : Type*} [Group G] {H P : Subgroup G} (hPH : P ≤ H)
    (hP : ⁅P, P⁆ = P) : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
  have hmap : (P.subgroupOf H).map H.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH]
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Subgroup.map_commutator, hmap, hP]

theorem PerfectNoncycThreeIn.top_of_le {G : Type*} [Group G] {C H : Subgroup G}
    (h : PerfectNoncycThreeIn C) (hCH : C ≤ H) : PerfectNoncycThreeIn (⊤ : Subgroup H) := by
  obtain ⟨V, hVC, hV, Q, hQV, hQ, hnc⟩ := h
  have hVH := hVC.trans hCH
  have hQH := hQV.trans hVH
  refine ⟨V.subgroupOf H, le_top, commutator_subgroupOf_of_le hVH hV, Q.subgroupOf H,
    Subgroup.subgroupOf_mono H hQV, ?_, fun hc => hnc ?_⟩
  · exact hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  · have e := Subgroup.subgroupOfEquivOfLe hQH
    exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem PerfectThreeIn.top_of_le {G : Type*} [Group G] {C H : Subgroup G} (h : PerfectThreeIn C)
    (hCH : C ≤ H) : PerfectThreeIn (⊤ : Subgroup H) := by
  obtain ⟨V, hVC, hV, x, hxV, hx3, hx1⟩ := h
  have hVH := hVC.trans hCH
  exact ⟨V.subgroupOf H, le_top, commutator_subgroupOf_of_le hVH hV, ⟨x, hVH hxV⟩, hxV,
    Subtype.ext (by simpa using hx3), fun h1 => hx1 (congrArg Subtype.val h1)⟩

section Diagonal

variable {m : ℕ} {E : Type} [Field E]

@[expose] noncomputable def diagGL (m : ℕ) (E : Type) [Field E] : (Fin m → Eˣ) →* GL (Fin m) E :=
  ((diagonalRingHom (Fin m) E).toMonoidHom.comp
    (MonoidHom.compLeft (Units.coeHom E) (Fin m))).toHomUnits

theorem coe_diagGL (c : Fin m → Eˣ) :
    ((diagGL m E c : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = diagonal fun i => (c i : E) :=
  rfl

theorem diagGL_injective : Function.Injective (diagGL m E) := by
  intro c d h
  funext i
  have := congrArg (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E) i i) h
  simp only [coe_diagGL, diagonal_apply_eq] at this
  exact Units.ext this

@[expose] def twoDiag (i j : Fin m) (μ : Eˣ) : Fin m → Eˣ :=
  Pi.mulSingle i μ * Pi.mulSingle j μ⁻¹

theorem twoDiag_apply_of_ne {i j k : Fin m} (hki : k ≠ i) (hkj : k ≠ j) (μ : Eˣ) :
    twoDiag i j μ k = 1 := by
  rw [twoDiag, Pi.mul_apply, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj, one_mul]

theorem twoDiag_apply_right {i j : Fin m} (hij : i ≠ j) (μ : Eˣ) : twoDiag i j μ j = μ⁻¹ := by
  rw [twoDiag, Pi.mul_apply, Pi.mulSingle_eq_of_ne (Ne.symm hij), Pi.mulSingle_eq_same, one_mul]

theorem prod_twoDiag (i j : Fin m) (μ : Eˣ) : ∏ k, (twoDiag i j μ k : E) = 1 := by
  rw [← Units.coe_prod]
  simp only [twoDiag, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle',
    mul_inv_cancel, Units.val_one]

theorem twoDiag_pow_three {i j : Fin m} {μ : Eˣ} (hμ : μ ^ 3 = 1) : twoDiag i j μ ^ 3 = 1 := by
  rw [twoDiag, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hμ, inv_pow, hμ, inv_one,
    Pi.mulSingle_one, Pi.mulSingle_one, mul_one]

theorem twoDiag_ne_one {i j : Fin m} (hij : i ≠ j) {μ : Eˣ} (hμ : μ ≠ 1) : twoDiag i j μ ≠ 1 := by
  intro h
  have := congrFun h j
  rw [twoDiag_apply_right hij, Pi.one_apply, inv_eq_one] at this
  exact hμ this

theorem det_diagGL_twoDiag (i j : Fin m) (μ : Eˣ) :
    ((diagGL m E (twoDiag i j μ) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).det = 1 := by
  rw [coe_diagGL, det_diagonal, prod_twoDiag]

theorem diag_pair (hm : 3 ≤ m) {μ : Eˣ} (hμ3 : μ ^ 3 = 1) (hμ1 : μ ≠ 1) :
    let i₀ : Fin m := ⟨0, by omega⟩
    let i₁ : Fin m := ⟨1, by omega⟩
    let i₂ : Fin m := ⟨2, by omega⟩
    Commute (diagGL m E (twoDiag i₀ i₁ μ)) (diagGL m E (twoDiag i₁ i₂ μ)) ∧
      diagGL m E (twoDiag i₀ i₁ μ) ^ 3 = 1 ∧ diagGL m E (twoDiag i₁ i₂ μ) ^ 3 = 1 ∧
      diagGL m E (twoDiag i₀ i₁ μ) ≠ 1 ∧
      diagGL m E (twoDiag i₁ i₂ μ) ∉ Subgroup.zpowers (diagGL m E (twoDiag i₀ i₁ μ)) := by
  intro i₀ i₁ i₂
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have h20 : i₂ ≠ i₀ := by simp [i₀, i₂, Fin.ext_iff]
  refine ⟨(Commute.all _ _).map _, by rw [← map_pow, twoDiag_pow_three hμ3, map_one],
    by rw [← map_pow, twoDiag_pow_three hμ3, map_one],
    fun h => twoDiag_ne_one h01 hμ1 (diagGL_injective (h.trans (map_one _).symm)),
    map_not_mem_zpowers diagGL_injective (not_mem_zpowers_of_apply (j := i₂)
      (twoDiag_apply_of_ne h20 (Ne.symm h12) μ) ?_)⟩
  rw [twoDiag_apply_right h12, Ne, inv_eq_one]
  exact hμ1

end Diagonal

theorem exists_unit_of_orderOf_eq_three {E : Type} [Field E] {μ : E} (hμ : orderOf μ = 3) :
    ∃ ν : Eˣ, (ν : E) = μ ∧ ν ^ 3 = 1 ∧ ν ≠ 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [orderOf_eq_zero_iff'.mpr fun n hn => by simp [zero_pow hn.ne']] at hμ
    omega
  refine ⟨Units.mk0 μ hμ0, rfl, Units.ext (by simp [← hμ, pow_orderOf_eq_one]), fun h => ?_⟩
  have : μ = 1 := by simpa using congrArg Units.val h
  rw [this, orderOf_one] at hμ
  omega

section Linear

variable {m : ℕ} {E : Type} [Field E] [Finite E]

omit [Finite E] in
theorem diagGL_twoDiag_mem_range (i j : Fin m) (μ : Eˣ) :
    diagGL m E (twoDiag i j μ) ∈ (SpecialLinearGroup.toGL (n := Fin m) (R := E)).range :=
  ⟨⟨_, det_diagGL_twoDiag i j μ⟩, Units.ext rfl⟩

theorem perfectNoncycThreeIn_gl (hm : 3 ≤ m) {μ : E} (hμ : orderOf μ = 3) :
    PerfectNoncycThreeIn (⊤ : Subgroup (GL (Fin m) E)) := by
  obtain ⟨ν, -, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three hμ
  have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (F := E) (m := m) (by omega)
    (Or.inl hm)
  have hperf : ⁅(SpecialLinearGroup.toGL (n := Fin m) (R := E)).range,
      (SpecialLinearGroup.toGL (n := Fin m) (R := E)).range⁆ =
      (SpecialLinearGroup.toGL (n := Fin m) (R := E)).range := by
    have := hq.1
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  obtain ⟨hc, hx3, hy3, hx1, hyx⟩ := diag_pair hm hν3 hν1
  exact PerfectNoncycThreeIn.of_pair le_top hperf (diagGL_twoDiag_mem_range _ _ ν)
    (diagGL_twoDiag_mem_range _ _ ν) hc hx3 hy3 hx1 hyx

theorem perfectThreeIn_gl (hm : 2 ≤ m) (hE : 4 ≤ Nat.card E) {μ : E} (hμ : orderOf μ = 3) :
    PerfectThreeIn (⊤ : Subgroup (GL (Fin m) E)) := by
  obtain ⟨ν, -, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three hμ
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hE)
  have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (F := E) (m := m) hm
    (Or.inr ⟨t, ht⟩)
  have hperf : ⁅(SpecialLinearGroup.toGL (n := Fin m) (R := E)).range,
      (SpecialLinearGroup.toGL (n := Fin m) (R := E)).range⁆ =
      (SpecialLinearGroup.toGL (n := Fin m) (R := E)).range := by
    have := hq.1
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨_, le_top, hperf, _, diagGL_twoDiag_mem_range _ _ ν,
    by rw [← map_pow, twoDiag_pow_three hν3, map_one],
    fun h => twoDiag_ne_one h01 hν1 (diagGL_injective (h.trans (map_one _).symm))⟩

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag (gramSU)

variable {ℓ f m : ℕ} {E : Type} [Field E] {hE : UnitaryFieldData ℓ f E}

theorem diagGL_twoDiag_mem_gramSU (i j : Fin m) {μ : Eˣ} (hμ : hE.bar (μ : E) = (μ : E)⁻¹) :
    diagGL m E (twoDiag i j μ) ∈ gramSU hE (1 : Matrix (Fin m) (Fin m) E) := by
  have hμ' : μ ^ (ℓ ^ f + 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, pow_succ, ← hE.bar_apply, hμ, Units.val_one,
      inv_mul_cancel₀ μ.ne_zero])
  have hc : twoDiag i j μ ^ (ℓ ^ f + 1) = 1 := by
    rw [twoDiag, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hμ', inv_pow, hμ', inv_one,
      Pi.mulSingle_one, Pi.mulSingle_one, mul_one]
  refine ⟨?_, det_diagGL_twoDiag i j μ⟩
  rw [coe_diagGL, Matrix.diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  have h1 := congrFun hc k
  rw [Pi.pow_apply, Pi.one_apply] at h1
  rw [hE.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, h1, Units.val_one]

variable [Finite E] {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}

omit [Finite E] [FiniteDimensional E W] in
theorem toLin'_diagGL_mem (e : Module.Basis (Fin m) E W)
    (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) (i j : Fin m) {μ : Eˣ}
    (hμ : hE.bar (μ : E) = (μ : E)⁻¹) :
    Matrix.GeneralLinearGroup.toLin' e (diagGL m E (twoDiag i j μ)) ∈
      sesqSpecialUnitaryGroup Hf :=
  (CFSG.RankThree.CentralLift.toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU hE e
    (fun i j => by rw [he, Matrix.one_apply]) _).mpr (diagGL_twoDiag_mem_gramSU i j hμ)

theorem finite_generalLinearGroup : Finite (LinearMap.GeneralLinearGroup E W) := by
  have : Finite W := Module.finite_of_finite E
  have : Finite (W →ₗ[E] W) := Module.finite_of_finite E
  exact Finite.of_injective _ Units.val_injective

theorem perfectNoncycThreeIn_sesqUnitary (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (e : Module.Basis (Fin m) E W) (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0)
    (hm : 3 ≤ m) (hq : m = 3 → 3 ≤ ℓ ^ f) {μ : E} (hμ : orderOf μ = 3)
    (hbar : hE.bar μ = μ⁻¹) : PerfectNoncycThreeIn (⊤ : Subgroup (sesqUnitaryGroup Hf)) := by
  have := finite_generalLinearGroup (E := E) (W := W)
  obtain ⟨ν, rfl, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three hμ
  have hm' : Module.finrank E W = m := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
    hHf hHfl (by omega) ⟨fun h2 => by omega, fun h3 => hq (by omega)⟩
  set ψ := (Matrix.GeneralLinearGroup.toLin' e).toMonoidHom
  have hψ : Function.Injective ψ := (Matrix.GeneralLinearGroup.toLin' e).injective
  obtain ⟨hc, hx3, hy3, hx1, hyx⟩ := diag_pair hm hν3 hν1
  refine (PerfectNoncycThreeIn.of_pair (sesqSpecialUnitaryGroup_le Hf)
    (Subgroup.isPerfect_iff.mp hSU.1) (toLin'_diagGL_mem e he _ _ hbar)
    (toLin'_diagGL_mem e he _ _ hbar) (hc.map ψ) (by rw [← map_pow, hx3, map_one])
    (by rw [← map_pow, hy3, map_one]) (fun h => hx1 (hψ (h.trans (map_one ψ).symm)))
    (map_not_mem_zpowers hψ hyx)).top_of_le le_rfl

omit [Finite E] in
theorem perfectThreeIn_sesqUnitary (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (e : Module.Basis (Fin m) E W) (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0)
    (hm : 2 ≤ m) (hq : 4 ≤ ℓ ^ f) {μ : E} (hμ : orderOf μ = 3) (hbar : hE.bar μ = μ⁻¹) :
    PerfectThreeIn (⊤ : Subgroup (sesqUnitaryGroup Hf)) := by
  obtain ⟨ν, rfl, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three hμ
  have hm' : Module.finrank E W = m := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
    hHf hHfl (by omega) ⟨fun _ => hq, fun _ => by omega⟩
  set ψ := (Matrix.GeneralLinearGroup.toLin' e).toMonoidHom
  have hψ : Function.Injective ψ := (Matrix.GeneralLinearGroup.toLin' e).injective
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine PerfectThreeIn.top_of_le ⟨_, sesqSpecialUnitaryGroup_le Hf,
    Subgroup.isPerfect_iff.mp hSU.1, _, toLin'_diagGL_mem e he _ _ hbar,
    by rw [← map_pow, ← map_pow, twoDiag_pow_three hν3, map_one, map_one],
    fun h => twoDiag_ne_one h01 hν1 (diagGL_injective (hψ (h.trans (map_one ψ).symm)))⟩ le_rfl

end Unitary

end CFSG.AGLEmbedding.ToralCensus
