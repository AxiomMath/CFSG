module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Basic
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Conj

variable
  {L : Type} [Field L] {t₁ : ModGL Tag.E8 L} {w₁ : WeylGroup Tag.E8}

private theorem normOrder_conj_pinnedX (ht₁ : t₁ ∈ torusGroup Tag.E8 L)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) :
    ∃ μ : Lˣ, ∀ c : L, t₁ * canonicalRep (coxeterSystem Tag.E8) L w₁ * pinnedX Tag.E8 L γ c *
        (t₁ * canonicalRep (coxeterSystem Tag.E8) L w₁)⁻¹ =
      pinnedX Tag.E8 L (w₁ • γ) (μ * c) := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₁
  obtain ⟨ε, hε, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w₁ hγ
  refine ⟨rootChar a (w₁ • γ) * Units.mkOfMulEqOne ε ε hε, fun c => ?_⟩
  calc rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w₁ *
        pinnedX Tag.E8 L γ c *
          (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w₁)⁻¹ =
      rootDiagUnit Tag.E8 a * (canonicalRep (coxeterSystem Tag.E8) L w₁ * pinnedX Tag.E8 L γ c *
        (canonicalRep (coxeterSystem Tag.E8) L w₁)⁻¹) * (rootDiagUnit Tag.E8 a)⁻¹ := by group
    _ = pinnedX Tag.E8 L (w₁ • γ) ((rootChar a (w₁ • γ) : L) * (ε * c)) := by
        rw [hX, rootDiagUnit_conj_pinnedX a (CFSG.LieType.Chevalley.IsRoot.smul hγ w₁)]
    _ = _ := by
        rw [Units.val_mul, Units.val_mkOfMulEqOne, mul_assoc]

private theorem normOrder_orbitNorm_pinnedX (ht₁ : t₁ ∈ torusGroup Tag.E8 L)
    {d : Fin Tag.E8.rank → ℤ} (hd : IsRoot Tag.E8 d) :
    ∃ μ₁ μ₂ : Lˣ, ∀ c : L,
      orbitNorm (t₁ * canonicalRep (coxeterSystem Tag.E8) L w₁) (pinnedX Tag.E8 L d c) =
        pinnedX Tag.E8 L d c * pinnedX Tag.E8 L (w₁ • d) (μ₁ * c) *
          pinnedX Tag.E8 L (w₁ ^ 2 • d) (μ₂ * c) := by
  obtain ⟨μ, hμ⟩ := normOrder_conj_pinnedX (w₁ := w₁) ht₁ hd
  obtain ⟨μ', hμ'⟩ :=
    normOrder_conj_pinnedX (w₁ := w₁) ht₁ (CFSG.LieType.Chevalley.IsRoot.smul hd w₁)
  have key : ∀ z y : ModGL Tag.E8 L, z ^ 2 * y * (z ^ 2)⁻¹ = z * (z * y * z⁻¹) * z⁻¹ :=
    fun z y => by rw [pow_two]; group
  refine ⟨μ, μ' * μ, fun c => ?_⟩
  rw [orbitNorm, key, hμ, hμ', pow_two, mul_smul, Units.val_mul, mul_assoc (μ' : L)]

end Conj

section Roots


private theorem normOrder_not_isRoot_add {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (hβ : IsRoot Tag.E8 β) (h0 : iform α β = 0) : ¬ IsRoot Tag.E8 (α + β) := by
  intro h
  have e := CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E8 h
  rw [iform_add_left, iform_add_right, iform_add_right,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E8 hα,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E8 hβ, h0, iform_comm β α, h0] at e
  omega

private theorem normOrder_ne_of_iform_eq_zero {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (h0 : iform α β = 0) : α ≠ β := by
  rintro rfl
  have e := CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E8 hα
  omega

end Roots

section Main

variable
  {L : Type} [Field L] {t₁ : ModGL Tag.E8 L} {w₁ : WeylGroup Tag.E8}

theorem orbitNorm_pinnedX_ne_one (ht₁ : t₁ ∈ torusGroup Tag.E8 L) {d : Fin Tag.E8.rank → ℤ}
    (hd : IsRoot Tag.E8 d) (horth : IsOrthTriple w₁ d) {c : L} (hc : c ≠ 0) :
    orbitNorm (t₁ * canonicalRep (coxeterSystem Tag.E8) L w₁) (pinnedX Tag.E8 L d c) ≠ 1 := by
  obtain ⟨μ₁, μ₂, hN⟩ := normOrder_orbitNorm_pinnedX (w₁ := w₁) ht₁ hd
  obtain ⟨h01, h02, h12⟩ := horth
  have hd1 := CFSG.LieType.Chevalley.IsRoot.smul hd w₁
  have hd2 := CFSG.LieType.Chevalley.IsRoot.smul hd (w₁ ^ 2)
  set γ : Fin 3 → Fin Tag.E8.rank → ℤ := ![d, w₁ • d, w₁ ^ 2 • d] with hγ
  have hr : ∀ i, IsRoot Tag.E8 (γ i) := by
    intro i
    fin_cases i
    · exact hd
    · exact hd1
    · exact hd2
  have horth' : ∀ i k, i ≠ k → iform (γ i) (γ k) = 0 := by
    intro i k hik
    fin_cases i <;> fin_cases k
    all_goals first
      | exact absurd rfl hik
      | simp only [hγ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        first
          | exact h01
          | exact h02
          | exact h12
          | rw [iform_comm]; exact h01
          | rw [iform_comm]; exact h02
          | rw [iform_comm]; exact h12
  have hinj : Function.Injective γ := by
    intro i k hik
    by_contra hne
    exact normOrder_ne_of_iform_eq_zero (hr i) (horth' i k hne) hik
  have hcard : (Finset.univ.filter fun i => height (γ i) < 0).card ≤ 3 :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hne := CFSG.LieType.SeitzGeneration.ExcHighThree.prod_ne_one_aux (τ := Tag.E8) (L := L) 3
    3 γ ![c, (μ₁ : L) * c, (μ₂ : L) * c] 0 hr hinj horth' hcard hc
  intro h
  apply hne
  rw [← h, hN c]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, hγ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_assoc]

theorem orbitNorm_pinnedX_pow_char (p : ℕ) [CharP L p] (ht₁ : t₁ ∈ torusGroup Tag.E8 L)
    {d : Fin Tag.E8.rank → ℤ} (hd : IsRoot Tag.E8 d) (horth : IsOrthTriple w₁ d) (c : L) :
    orbitNorm (t₁ * canonicalRep (coxeterSystem Tag.E8) L w₁) (pinnedX Tag.E8 L d c) ^ p = 1 := by
  obtain ⟨μ₁, μ₂, hN⟩ := normOrder_orbitNorm_pinnedX (w₁ := w₁) ht₁ hd
  obtain ⟨h01, h02, h12⟩ := horth
  have hd1 := CFSG.LieType.Chevalley.IsRoot.smul hd w₁
  have hd2 := CFSG.LieType.Chevalley.IsRoot.smul hd (w₁ ^ 2)
  have hcomm : ∀ {α β : Fin Tag.E8.rank → ℤ}, IsRoot Tag.E8 α → IsRoot Tag.E8 β →
      iform α β = 0 → ∀ a b : L, Commute (pinnedX Tag.E8 L α a) (pinnedX Tag.E8 L β b) :=
    fun hα hβ h0 a b =>
      pinnedX_commute_of_iform_eq_zero L hα hβ h0 (normOrder_not_isRoot_add hα hβ h0) a b
  rw [hN c, ((hcomm hd hd2 h02 c _).mul_left (hcomm hd1 hd2 h12 _ _)).mul_pow,
    (hcomm hd hd1 h01 c _).mul_pow,
    CFSG.LieType.SeitzGeneration.ExcHighThree.pinnedX_pow_char p d c,
    CFSG.LieType.SeitzGeneration.ExcHighThree.pinnedX_pow_char p (w₁ • d) _,
    CFSG.LieType.SeitzGeneration.ExcHighThree.pinnedX_pow_char p (w₁ ^ 2 • d) _, one_mul, one_mul]

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
