module

public import CFSG.GroupTheory.AschbacherBlock
import CFSG.CGT.PushingUpLit.Glue.BlockInX

public section

namespace CFSG.GroupTheory

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.Glue Subgroup
open scoped commutatorElement

private theorem commutator_mul_eq_conj_nmc {G : Type*} [Group G] (l u : G) :
    ⁅l, u⁆ * u = l * u * l⁻¹ := by
  rw [commutatorElement_def]
  group

private theorem conj_mem_shortU_nmc {B : Type} [Group B] (l : B) {u : B} (hu : u ∈ shortU B) :
    l * u * l⁻¹ ∈ shortU B :=
  shortU_normal.conj_mem u hu l

private theorem shortC_lt_shortU_of_not_le_nmc {B : Type} [Group B]
    (hnc : ¬ ⁅shortU B, (⊤ : Subgroup B)⁆ ≤ shortC B) : shortC B < shortU B := by
  refine lt_of_le_of_ne inf_le_left (fun hEq => hnc ?_)
  rw [hEq]
  exact Subgroup.commutator_le_left (H₁ := shortU B) (H₂ := ⊤)

private theorem shortC_normal_nmc {B : Type} [Group B] : (shortC B).Normal := by
  unfold shortC
  infer_instance

private theorem sl2_fix_of_commutator_le_shortC_nmc {B : Type} [Group B] {n : ℕ}
    (h : IsNaturalSLTwoModule B n) (hc : ⁅shortU B, (⊤ : Subgroup B)⁆ ≤ shortC B) :
    ∀ (A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (v : Fin 2 → GaloisField 2 n),
      (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec v = v := by
  obtain ⟨φ, ψ, hs, hk, he⟩ := h
  intro A v
  obtain ⟨l, hl⟩ : ∃ l : B, φ (l : B ⧸ pCore 2 B) = A := by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (φ.symm A)
    exact ⟨q, by rw [hq]; exact φ.apply_symm_apply A⟩
  rw [← hl]
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd v)
  have hu' : l * (u : B) * l⁻¹ ∈ shortU B := conj_mem_shortU_nmc l u.2
  have hmem : ⁅l, (u : B)⁆ ∈ shortC B := by
    have hbase : ⁅(u : B), l⁻¹⁆ ∈ shortC B :=
      hc (Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_top l⁻¹))
    have hconj : l * ⁅(u : B), l⁻¹⁆ * l⁻¹ = ⁅l, (u : B)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [← hconj]
    exact (shortC_normal_nmc (B := B)).conj_mem _ hbase l
  have hmemU : ⁅l, (u : B)⁆ ∈ shortU B := (Subgroup.mem_inf.mp hmem).1
  have hker : (⟨⁅l, (u : B)⁆, hmemU⟩ : ↥(shortU B)) ∈ ψ.ker := by
    rw [hk, Subgroup.mem_subgroupOf]
    exact hmem
  have hcomm1 : ψ ⟨⁅l, (u : B)⁆, hmemU⟩ = 1 := MonoidHom.mem_ker.mp hker
  have h1 : ψ ⟨l * (u : B) * l⁻¹, hu'⟩ = ψ u := by
    have hsplit : (⟨l * (u : B) * l⁻¹, hu'⟩ : ↥(shortU B)) =
        ⟨⁅l, (u : B)⁆, hmemU⟩ * u := by
      refine Subtype.ext ?_
      show l * (u : B) * l⁻¹ = ⁅l, (u : B)⁆ * u
      exact (commutator_mul_eq_conj_nmc l (u : B)).symm
    rw [hsplit, map_mul, hcomm1, one_mul]
  have h2 := he l u u.2 hu'
  rw [h1] at h2
  have hv : Multiplicative.toAdd (ψ u) = v := by
    simpa using congrArg Multiplicative.toAdd hu
  have h3 : Multiplicative.toAdd (ψ u) =
      (φ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (Multiplicative.toAdd (ψ u)) := by
    have := congrArg Multiplicative.toAdd h2
    simpa using this
  rw [hv] at h3
  exact h3.symm

private theorem not_commutator_shortU_le_shortC_of_isNaturalSLTwoModule_nmc {B : Type} [Group B]
    {n : ℕ} (h : IsNaturalSLTwoModule B n) :
    ¬ ⁅shortU B, (⊤ : Subgroup B)⁆ ≤ shortC B := by
  intro hc
  have hfix := sl2_fix_of_commutator_le_shortC_nmc h hc
  let F2 : Fin 2 → Type := fun _ => GaloisField 2 n
  have hv : Pi.single (M := F2) (0 : Fin 2) (1 : F2 0) ≠ 0 := by
    intro hh
    have h1 := congrFun hh (0 : Fin 2)
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hw : Pi.single (M := F2) (1 : Fin 2) (1 : F2 1) ≠ 0 := by
    intro hh
    have h1 := congrFun hh (1 : Fin 2)
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq_of_ne_zero (F := GaloisField 2 n) hv hw
  have h := hfix A (Pi.single (M := F2) (0 : Fin 2) (1 : F2 0))
  rw [hA] at h
  have h1 := congrFun h (1 : Fin 2)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at h1
  exact one_ne_zero h1

private theorem alt_fix_of_commutator_le_shortC_nmc {B : Type} [Group B] {n : ℕ}
    (h : IsNaturalAltModule B n) (hc : ⁅shortU B, (⊤ : Subgroup B)⁆ ≤ shortC B) :
    ∀ (σ : Equiv.Perm (Fin (2 * n + 1))) (_ : σ ∈ alternatingGroup (Fin (2 * n + 1)))
      (v : Fin (2 * n + 1) → ZMod 2), (∑ i, v i = 0) → permActionTwo σ v = v := by
  obtain ⟨φ, ψ, -, hs, hk, he⟩ := h
  intro σ hσ v hv
  obtain ⟨l, hl⟩ : ∃ l : B, φ (l : B ⧸ pCore 2 B) = ⟨σ, hσ⟩ := by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (φ.symm ⟨σ, hσ⟩)
    exact ⟨q, by rw [hq]; exact φ.apply_symm_apply _⟩
  obtain ⟨u, hu⟩ := hs v hv
  have hu' : l * (u : B) * l⁻¹ ∈ shortU B := conj_mem_shortU_nmc l u.2
  have hmem : ⁅l, (u : B)⁆ ∈ shortC B := by
    have hbase : ⁅(u : B), l⁻¹⁆ ∈ shortC B :=
      hc (Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_top l⁻¹))
    have hconj : l * ⁅(u : B), l⁻¹⁆ * l⁻¹ = ⁅l, (u : B)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [← hconj]
    exact (shortC_normal_nmc (B := B)).conj_mem _ hbase l
  have hmemU : ⁅l, (u : B)⁆ ∈ shortU B := (Subgroup.mem_inf.mp hmem).1
  have hker : (⟨⁅l, (u : B)⁆, hmemU⟩ : ↥(shortU B)) ∈ ψ.ker := by
    rw [hk, Subgroup.mem_subgroupOf]
    exact hmem
  have hcomm1 : ψ ⟨⁅l, (u : B)⁆, hmemU⟩ = 1 := MonoidHom.mem_ker.mp hker
  have h1 : ψ ⟨l * (u : B) * l⁻¹, hu'⟩ = ψ u := by
    have hsplit : (⟨l * (u : B) * l⁻¹, hu'⟩ : ↥(shortU B)) =
        ⟨⁅l, (u : B)⁆, hmemU⟩ * u := by
      refine Subtype.ext ?_
      show l * (u : B) * l⁻¹ = ⁅l, (u : B)⁆ * u
      exact (commutator_mul_eq_conj_nmc l (u : B)).symm
    rw [hsplit, map_mul, hcomm1, one_mul]
  have h2 := he l u u.2 hu'
  rw [h1] at h2
  have hv' : Multiplicative.toAdd (ψ u) = v := by
    simpa using congrArg Multiplicative.toAdd hu
  have h3 : permActionTwo σ (Multiplicative.toAdd (ψ u)) = Multiplicative.toAdd (ψ u) := by
    have := congrArg Multiplicative.toAdd h2
    simpa [hl] using this.symm
  rw [hv'] at h3
  exact h3

private theorem not_commutator_shortU_le_shortC_of_isNaturalAltModule_nmc {B : Type} [Group B]
    {n : ℕ} (hn : 1 ≤ n) (h : IsNaturalAltModule B n) :
    ¬ ⁅shortU B, (⊤ : Subgroup B)⁆ ≤ shortC B := by
  intro hc
  have hfix := alt_fix_of_commutator_le_shortC_nmc h hc
  let a : Fin (2 * n + 1) := ⟨0, by omega⟩
  let b : Fin (2 * n + 1) := ⟨1, by omega⟩
  let c : Fin (2 * n + 1) := ⟨2, by omega⟩
  have hab : a ≠ b := by
    intro hh; have := congrArg Fin.val hh; simp [a, b] at this
  have hac : a ≠ c := by
    intro hh; have := congrArg Fin.val hh; simp [a, c] at this
  have hbc : b ≠ c := by
    intro hh; have := congrArg Fin.val hh; simp [b, c] at this
  have hσ : Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin (2 * n + 1)) :=
    swap_mul_swap_mem_alternatingGroup hab hbc
  have hv : ∑ i, pairVec a b i = 0 :=
    (mem_evenWeight_iff (pairVec a b)).mp (pairVec_mem_evenWeight a b)
  have hfixσ := hfix (Equiv.swap a b * Equiv.swap b c) hσ (pairVec a b) hv
  have hperm : permActionTwo (Equiv.swap a b * Equiv.swap b c) (pairVec a b) = pairVec b c := by
    have hperm' : permVec (Equiv.swap a b * Equiv.swap b c) (pairVec a b) = pairVec b c := by
      obtain ⟨h1, h2, -⟩ := threeCycle_apply hab hac hbc
      unfold pairVec
      rw [permVec_add, permVec_single, permVec_single, h1, h2]
    exact hperm'
  rw [hperm] at hfixσ
  have hne : pairVec b c ≠ pairVec a b := by
    intro hh
    have hh0 : (0 : ZMod 2) = 1 := by
      have := congrFun hh a
      simp [pairVec, hac.symm, hab] at this
    exact zero_ne_one hh0
  exact hne hfixσ

private theorem exists_chief_of_isNaturalSLTwoModule_nmc {B : Type} [Group B] {n : ℕ} (hn : 2 ≤ n)
    (h : IsNaturalSLTwoModule B n) :
    ∃ X Y₀ : Subgroup B, X.Normal ∧ Y₀.Normal ∧ Y₀ < X ∧ X ≤ pCore 2 B ∧
      Y₀ ≤ center B ∧ ⁅pCore 2 B, (⊤ : Subgroup B)⁆ ≤ X ∧
      (∀ N : Subgroup B, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X) ∧
      ¬ ⁅X, (⊤ : Subgroup B)⁆ ≤ Y₀ ∧
      ((∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor B X Y₀ n) ∨
        (∃ n, 1 ≤ n ∧ IsNaturalAltFactor B X Y₀ n)) := by
  have hnc := not_commutator_shortU_le_shortC_of_isNaturalSLTwoModule_nmc h
  exact ⟨shortU B, shortC B, inferInstance, shortC_normal_nmc,
    shortC_lt_shortU_of_not_le_nmc hnc,
    Subgroup.commutator_le_left (H₁ := pCore 2 B) (H₂ := ⊤), inf_le_right, le_rfl,
    fun N hN hY hX =>
      @irreducible_of_isNaturalSLTwoModule B _ n h N hN hX hY, hnc,
    Or.inl ⟨n, hn, h⟩⟩

private theorem exists_chief_of_isNaturalAltModule_nmc {B : Type} [Group B] {n : ℕ} (hn : 1 ≤ n)
    (h : IsNaturalAltModule B n) :
    ∃ X Y₀ : Subgroup B, X.Normal ∧ Y₀.Normal ∧ Y₀ < X ∧ X ≤ pCore 2 B ∧
      Y₀ ≤ center B ∧ ⁅pCore 2 B, (⊤ : Subgroup B)⁆ ≤ X ∧
      (∀ N : Subgroup B, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X) ∧
      ¬ ⁅X, (⊤ : Subgroup B)⁆ ≤ Y₀ ∧
      ((∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor B X Y₀ n) ∨
        (∃ n, 1 ≤ n ∧ IsNaturalAltFactor B X Y₀ n)) := by
  have hnc := not_commutator_shortU_le_shortC_of_isNaturalAltModule_nmc hn h
  exact ⟨shortU B, shortC B, inferInstance, shortC_normal_nmc,
    shortC_lt_shortU_of_not_le_nmc hnc,
    Subgroup.commutator_le_left (H₁ := pCore 2 B) (H₂ := ⊤), inf_le_right, le_rfl,
    fun N hN hY hX =>
      @irreducible_of_isNaturalAltModule B _ n hn h N hN hX hY, hnc,
    Or.inr ⟨n, hn, h⟩⟩

theorem exists_chief_of_isNaturalModule {B : Type} [Group B]
    (h : (∃ n, 2 ≤ n ∧ IsNaturalSLTwoModule B n) ∨ ∃ n, 1 ≤ n ∧ IsNaturalAltModule B n) :
    ∃ X Y₀ : Subgroup B, X.Normal ∧ Y₀.Normal ∧ Y₀ < X ∧ X ≤ pCore 2 B ∧
      Y₀ ≤ center B ∧ ⁅pCore 2 B, (⊤ : Subgroup B)⁆ ≤ X ∧
      (∀ N : Subgroup B, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X) ∧
      ¬ ⁅X, (⊤ : Subgroup B)⁆ ≤ Y₀ ∧
      ((∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor B X Y₀ n) ∨
        (∃ n, 1 ≤ n ∧ IsNaturalAltFactor B X Y₀ n)) := by
  rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
  · exact exists_chief_of_isNaturalSLTwoModule_nmc hn h
  · exact exists_chief_of_isNaturalAltModule_nmc hn h

end CFSG.GroupTheory
