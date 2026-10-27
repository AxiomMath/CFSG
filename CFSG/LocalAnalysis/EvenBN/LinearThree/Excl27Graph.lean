module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.LocalAnalysis.SteinbergCDEvenLinearThreeSemilinearFixed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModuleAbstract

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_linear_canonical_graph_symplectic_centralizers)
open CFSG.ComponentClassification.RankTwoHypIIL3 (nonempty_matrixIsometryGroup_one_mulEquiv_SL2)

section Generic

variable {P : Type*} [Group P]

theorem commutator_self_eq_of_mulEquiv {S : Type*} [Group S] (hS : commutator S = ⊤)
    {L : Subgroup P} (e : L ≃* S) : ⁅L, L⁆ = L := by
  have hL : commutator L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ commutator S := hS ▸ mem_top _
    have h := mem_map_of_mem e.symm.toMonoidHom hx
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, commutator_def, map_commutator,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ e.symm.surjective] at h
    exact h
  have h := congrArg (Subgroup.map L.subtype) hL
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem fix_map_inv_of_eq_conj {x y γ : MulAut P} (h : y = γ * x * γ⁻¹) {L : Subgroup P}
    (hL : ∀ p ∈ L, y p = p) : ∀ p ∈ L.map (γ⁻¹ : MulAut P).toMonoidHom, x p = p := by
  rintro _ ⟨p, hp, rfl⟩
  have h1 := hL p hp
  rw [h, MulAut.mul_apply, MulAut.mul_apply] at h1
  change x (γ⁻¹ p) = γ⁻¹ p
  calc x (γ⁻¹ p) = γ⁻¹ (γ (x (γ⁻¹ p))) := by rw [MulAut.inv_apply_self]
    _ = γ⁻¹ p := by rw [h1]

end Generic

variable {K : Type} [Field K] [Finite K]

section Semilinear

variable [CharP K 2]

theorem false_of_fix_conjAut_mul_fieldAut (A : GL (Fin 3) K) (σ : K ≃+* K)
    (hβ : orderOf (conjAut 3 K A * fieldAut 3 K σ) = 2) {L : Subgroup (projectiveSL 3 K)}
    (hL : Nonempty (L ≃* SpecialLinearGroup (Fin 2) K))
    (hLβ : ∀ p ∈ L, (conjAut 3 K A * fieldAut 3 K σ) p = p) : False := by
  have h := (SteinbergCD.characteristic_two_linear_three_semilinear_involution_fixed_order
    K A σ hβ).2.2.2.2 L (fun p hp => TauCeti.mem_fixedSubgroup.mpr (hLβ p hp))
  obtain ⟨e⟩ := hL
  exact h.false e

end Semilinear

theorem isCoprime_sq_add_one (t : ℤ) :
    IsCoprime ((2 * t) ^ 2 + 1) ((2 * t) ^ 3 * ((2 * t) ^ 2 - 1) * ((2 * t) ^ 3 + 1)) := by
  have h1 : IsCoprime ((2 * t) ^ 2 + 1) (2 * t) := ⟨1, -(2 * t), by ring⟩
  have h2 : IsCoprime ((2 * t) ^ 2 + 1) ((2 * t) ^ 2 - 1) :=
    ⟨1 - 2 * t ^ 2, 2 * t ^ 2, by ring⟩
  have h3 : IsCoprime ((2 * t) ^ 2 + 1) ((2 * t) ^ 3 + 1) :=
    ⟨-t - 2 * t ^ 2 - 4 * t ^ 3, 1 + t + 2 * t ^ 2, by ring⟩
  exact ((h1.pow_right (n := 3)).mul_right h2).mul_right h3

theorem not_dvd_card_su_three {e : ℕ} (he : 1 ≤ e) :
    ¬ (2 ^ (2 * e) * ((2 ^ (2 * e)) ^ 2 - 1)) ∣
      (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
  intro hd
  set s := 2 ^ e with hs
  have hs2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hse : s = 2 * 2 ^ (e - 1) := by
    rw [hs, ← pow_succ']
    congr 1
    omega
  have hq : 2 ^ (2 * e) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
  rw [hq] at hd
  have hdvd1 : s ^ 2 + 1 ∣ s ^ 2 * ((s ^ 2) ^ 2 - 1) := by
    have h4 : (s ^ 2) ^ 2 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by
      have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this, Nat.one_le_pow 2 (s ^ 2) (by positivity)]
      ring
    rw [h4]
    exact (dvd_mul_left (s ^ 2 + 1) (s ^ 2 - 1)).mul_left (s ^ 2)
  have hdvd := hdvd1.trans hd
  have hz : ((s ^ 2 + 1 : ℕ) : ℤ) ∣ ((s ^ 3 * (s ^ 2 - 1) * (s ^ 3 + 1) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd
  have hs1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  push_cast [hs1] at hz
  have hcop := isCoprime_sq_add_one (2 ^ (e - 1) : ℤ)
  have hsz : (s : ℤ) = 2 * 2 ^ (e - 1) := by exact_mod_cast hse
  rw [← hsz] at hcop
  have hu := hcop.isUnit_of_dvd' (dvd_refl _) hz
  rw [Int.isUnit_iff] at hu
  have : (4 : ℤ) ≤ (s : ℤ) ^ 2 := by
    have : (2 : ℤ) ≤ s := by exact_mod_cast hs2
    nlinarith
  rcases hu with hu | hu <;> linarith

theorem exists_eq_conj_dualAut {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : MulAut (projectiveSL 3 K)} (hy : orderOf y = 2) {L : Subgroup (projectiveSL 3 K)}
    (hL : Nonempty (L ≃* SpecialLinearGroup (Fin 2) K)) (hLy : ∀ p ∈ L, y p = p) :
    y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      ∃ γ : MulAut (projectiveSL 3 K), y = γ * dualAut 3 K * γ⁻¹ := by
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  obtain ⟨e⟩ := hL
  have hout : y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    rintro ⟨p, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 K p
    rw [← conjAut_toGL] at hy hLy
    refine false_of_fix_conjAut_mul_fieldAut (SpecialLinearGroup.toGL g) 1 ?_ ⟨e⟩ ?_
    · rw [map_one, mul_one]
      exact hy
    · intro p hp
      rw [map_one, mul_one]
      exact hLy p hp
  refine ⟨hout, ?_⟩
  have hLmap : ∀ γ : MulAut (projectiveSL 3 K),
      Nonempty ((L.map (γ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom) ≃*
        SpecialLinearGroup (Fin 2) K) := fun γ =>
    ⟨(L.equivMapOfInjective _ (γ⁻¹ : MulAut (projectiveSL 3 K)).injective).symm.trans e⟩
  have horder : ∀ {x γ : MulAut (projectiveSL 3 K)}, y = γ * x * γ⁻¹ → orderOf x = 2 := by
    intro x γ h
    rw [← hy, h]
    exact (MulEquiv.orderOf_eq (MulAut.conj γ) x).symm
  rcases exists_conj_canonical_of_not_mem_range (by omega) hK hy2 hout with
    ⟨-, σ, -, γ, hγ⟩ | h | ⟨⟨e', he'⟩, σ, hσx, γ, hγ⟩
  ·
    exfalso
    have hfix := fix_map_inv_of_eq_conj hγ hLy
    refine false_of_fix_conjAut_mul_fieldAut 1 σ ?_ (hLmap γ) ?_
    · rw [map_one, one_mul]
      exact horder hγ
    · intro p hp
      rw [map_one, one_mul]
      exact hfix p hp
  · exact h
  ·
    exfalso
    have hud : UnitaryFieldData 2 e' K := ⟨Nat.prime_two, by omega, by rw [hK, he', two_mul]⟩
    have hσbar : ∀ x, σ x = hud.bar x := fun x => by
      rw [hσx, UnitaryFieldData.bar_apply, show f / 2 = e' by omega]
    have hfix := fix_map_inv_of_eq_conj hγ hLy
    set L' := L.map (γ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom with hL'
    obtain ⟨e₁⟩ := hLmap γ
    have h4 : (4 : ℕ) ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hperf : commutator (SpecialLinearGroup (Fin 2) K) = ⊤ := by
      obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun a _ => by
          by_cases ha : a = 0
          · exact Or.inl ha
          · exact Or.inr (hcon a ha)
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at this
        omega
      refine Matrix.SL2.commutator_eq_top ha0 fun h => ha1 ?_
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have h3 : (a - 1) ^ 2 = 0 := by linear_combination h - a * h2 + h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
    have hL'p := commutator_self_eq_of_mulEquiv hperf e₁
    have hle : L' ≤ CFSG.SeitzReduction.LinearPilot.autFixSubgroup
        (fieldAut 3 K σ * dualAut 3 K) := fun p hp => hfix p hp
    have hcore := CFSG.Quasithin.le_perfectCore_of_perfect hle hL'p
    have hdvd := (Subgroup.card_dvd_of_le hcore).trans
      (CFSG.SeitzReduction.LinearPilot.card_perfectCore_graphField_dvd hud le_rfl σ hσbar)
    rw [CFSG.RankThree.PartTwo.KFacts.card_unitarySU_three hud, Nat.card_congr e₁.toEquiv,
      CaseBModule.card_sl2 hK, show f = 2 * e' by omega] at hdvd
    exact not_dvd_card_su_three (by omega) hdvd

theorem eq_one_of_commute_conj_dualAut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (γ : MulAut (projectiveSL 3 K)) {L : Subgroup (projectiveSL 3 K)}
    (hL : Nonempty (L ≃* SpecialLinearGroup (Fin 2) K))
    (hLy : ∀ p ∈ L, (γ * dualAut 3 K * γ⁻¹) p = p) {x : MulAut (projectiveSL 3 K)}
    (hxy : x * (γ * dualAut 3 K * γ⁻¹) = (γ * dualAut 3 K * γ⁻¹) * x)
    (hxL : ∀ p ∈ L, x p = p) (hx : Odd (orderOf x)) : x = 1 := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hinjc := CFSG.ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
  obtain ⟨e⟩ := hL
  obtain ⟨hinj, -, hβ2, hM, -, -, hrest⟩ :=
    even_linear_canonical_graph_symplectic_centralizers
      (n := 3) hf hK le_rfl 1 (Or.inl rfl)
  obtain ⟨hC, -⟩ := hrest (Or.inr ⟨rfl, by decide⟩)
  have hβ : conjAut 3 K 1 * dualAut 3 K = dualAut 3 K := by rw [map_one, one_mul]
  rw [hβ] at hβ2 hM hC
  set O := FourGroupEvenCanonical.matrixIsometryGroup
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hO
  set N := O.map (conjAut 3 K) with hN
  set x' := γ⁻¹ * x * γ with hx'
  set L' := L.map (γ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom with hL'
  have hδL : ∀ p ∈ L', dualAut 3 K p = p :=
    fix_map_inv_of_eq_conj (x := dualAut 3 K) rfl hLy
  have hx'L : ∀ p ∈ L', x' p = p :=
    fix_map_inv_of_eq_conj (x := x') (by rw [hx']; group) hxL
  have hx'δ : x' * dualAut 3 K = dualAut 3 K * x' := by
    have h1 : γ⁻¹ * (x * (γ * dualAut 3 K * γ⁻¹)) * γ =
        γ⁻¹ * ((γ * dualAut 3 K * γ⁻¹) * x) * γ := by rw [hxy]
    rw [hx']
    calc γ⁻¹ * x * γ * dualAut 3 K = γ⁻¹ * (x * (γ * dualAut 3 K * γ⁻¹)) * γ := by group
      _ = γ⁻¹ * ((γ * dualAut 3 K * γ⁻¹) * x) * γ := h1
      _ = dualAut 3 K * (γ⁻¹ * x * γ) := by group
  set M' := L'.map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) with hM'
  have hM'N : M' ≤ N := by
    rintro _ ⟨p, hp, rfl⟩
    have hcen : MulAut.conj p ∈ centralizer {dualAut 3 K} := by
      rw [mem_centralizer_singleton_iff]
      have h1 := CFSG.SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj (dualAut 3 K) p
      rw [hδL p hp] at h1
      calc MulAut.conj p * dualAut 3 K = (dualAut 3 K * MulAut.conj p * (dualAut 3 K)⁻¹) *
          dualAut 3 K := by rw [h1]
        _ = dualAut 3 K * MulAut.conj p := by group
    have hcen' : MulAut.conj p ∈ (centralizer {dualAut 3 K} : Set (MulAut (projectiveSL 3 K))) :=
      hcen
    rw [hM] at hcen'
    obtain ⟨g, hg, φ, ε, hε, hα⟩ := hcen'
    obtain ⟨g₀, rfl⟩ := proj_surjective 3 K p
    have hform : conjAut 3 K (SpecialLinearGroup.toGL g₀) * fieldAut 3 K 1 * dualAut 3 K ^ 0 =
        conjAut 3 K g * fieldAut 3 K φ * dualAut 3 K ^ ε := by
      rw [map_one, mul_one, pow_zero, mul_one, conjAut_toGL, ← hα]
    obtain ⟨hφ, hε0⟩ := ProjectivePlane.standard_form_unique le_rfl (by norm_num) hε hform
    rw [← hφ, ← hε0, map_one, mul_one, pow_zero, mul_one] at hα
    exact ⟨g, hg, hα.symm⟩
  have hcardM' : Nat.card M' = Nat.card (SpecialLinearGroup (Fin 2) K) := by
    rw [hM', ← Nat.card_congr (L'.equivMapOfInjective _ hinjc).toEquiv, hL',
      ← Nat.card_congr
        (L.equivMapOfInjective _ (γ⁻¹ : MulAut (projectiveSL 3 K)).injective).toEquiv,
      Nat.card_congr e.toEquiv]
  have hcardN : Nat.card N = Nat.card (SpecialLinearGroup (Fin 2) K) := by
    obtain ⟨eO⟩ := nonempty_matrixIsometryGroup_one_mulEquiv_SL2 (K := K)
    have hNO : ((conjAut 3 K).comp O.subtype).range = N := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hNO, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr eO.toEquiv]
  have : Finite (MulAut (projectiveSL 3 K)) :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_mulAut_projectiveSL
  have hM'eq : M' = N := Subgroup.eq_of_le_of_card_ge hM'N (by rw [hcardM', hcardN])
  have hx'C : x' ∈ centralizer {dualAut 3 K} ⊓
      centralizer ((N : Subgroup (MulAut (projectiveSL 3 K))) :
        Set (MulAut (projectiveSL 3 K))) := by
    refine Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hx'δ, ?_⟩
    rw [← hM'eq, mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    have h1 := CFSG.SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj x' p
    rw [hx'L p hp] at h1
    calc MulAut.conj p * x' = x' * MulAut.conj p * x'⁻¹ * x' := by rw [h1]
      _ = x' * MulAut.conj p := by group
  rw [hC] at hx'C
  rcases CFSG.ComponentClassification.RankTwoHypIIY.eq_one_or_eq_of_mem_zpowers hβ2 hx'C with
    h | h
  ·
    have : x = γ * x' * γ⁻¹ := by rw [hx']; group
    rw [this, h, mul_one, mul_inv_cancel]
  ·
    exfalso
    have hδ1 : dualAut 3 K ≠ 1 := by
      intro h1
      apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
      rw [h1]
      exact one_mem _
    have hord : orderOf x' = orderOf x := by
      rw [hx', show γ⁻¹ * x * γ = MulAut.conj γ⁻¹ x by simp]
      exact MulEquiv.orderOf_eq _ x
    have h2 : orderOf (dualAut 3 K) = 2 := orderOf_eq_prime hβ2 hδ1
    rw [← hord, h, h2] at hx
    exact (Nat.not_odd_iff_even.mpr even_two) hx

end CFSG.LocalAnalysis.EvenBN.LinearThree
