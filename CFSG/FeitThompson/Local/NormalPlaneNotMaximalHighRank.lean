module

public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.NormalSubgroupsOfEveryPrimePowerOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {p n : ℕ} {R : Type*} [Group R] {X Y E : Subgroup R}

theorem IsElementaryAbelian.sup_of_le_centralizer (hX : IsElementaryAbelian p X)
    (hY : IsElementaryAbelian p Y) [Y.Normal] (hc : X ≤ centralizer (Y : Set R)) :
    IsElementaryAbelian p (X ⊔ Y) := by
  have key : ∀ g ∈ X ⊔ Y, ∃ a ∈ X, ∃ b ∈ Y, g = a * b := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ : g ∈ (X : Set R) * (Y : Set R) := by
      rw [← X.mul_normal Y]; exact hg
    exact ⟨a, ha, b, hb, rfl⟩
  have hcomm : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (hc ha) b hb).symm
  refine isElementaryAbelian_iff.2 ⟨IsMulCommutative.of_comm fun g₁ g₂ => Subtype.ext ?_, ?_⟩
  · obtain ⟨a₁, ha₁, b₁, hb₁, he₁⟩ := key g₁ g₁.2
    obtain ⟨a₂, ha₂, b₂, hb₂, he₂⟩ := key g₂ g₂.2
    simp only [Subgroup.coe_mul, he₁, he₂]
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hcomm a₂ ha₂ b₁ hb₁]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
      _ = a₂ * a₁ * (b₂ * b₁) := by rw [hX.mul_comm ha₁ ha₂, hY.mul_comm hb₁ hb₂]
      _ = a₂ * (a₁ * b₂) * b₁ := by group
      _ = a₂ * (b₂ * a₁) * b₁ := by rw [hcomm a₁ ha₁ b₂ hb₂]
      _ = a₂ * b₂ * (a₁ * b₁) := by group
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := key g hg
    have c : Commute a b := hcomm a ha b hb
    rw [c.mul_pow, hX.pow_eq_one ha, hY.pow_eq_one hb, one_mul]

theorem normal_omega1Subgroup (p : ℕ) (A : Subgroup R) [A.Normal] :
    (omega1Subgroup p A).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [omega1Subgroup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      exact mem_omega1Subgroup ((inferInstance : A.Normal).conj_mem y hy.1 g)
        (by rw [conj_pow, hy.2, mul_one, mul_inv_cancel])
  | one => simp
  | mul a b _ _ ha hb =>
      have h : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
      rw [h]; exact mul_mem ha hb
  | inv a _ ha =>
      have h : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [h]; exact inv_mem ha

theorem isElementaryAbelian_omega1Subgroup (p : ℕ) (A : Subgroup R)
    (hA : IsMulCommutative ↥A) : IsElementaryAbelian p (omega1Subgroup p A) := by
  have := hA
  refine isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_, fun x hx =>
      ((mem_omega1Subgroup_iff_of_isMulCommutative hA).1 hx).2⟩
  exact setLike_mul_comm (s := A)
    ((mem_omega1Subgroup_iff_of_isMulCommutative hA).1 x.2).1
    ((mem_omega1Subgroup_iff_of_isMulCommutative hA).1 y.2).1

theorem exists_normal_isElementaryAbelian_gt_of_natCard_eq_sq (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card R = p ^ n) (hrank : 3 ≤ elementaryAbelianPRank p R) [E.Normal]
    (hEea : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    ∃ D : Subgroup R, D.Normal ∧ IsElementaryAbelian p D ∧ E < D := by
  have hfp := Fact.mk hp
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  have hRp : IsPGroup p R := IsPGroup.of_card hcard
  obtain ⟨A, hAn, hAc, -, B, hBA, hB⟩ :=
    exists_abelian_normal_mulEquiv_pi_of_three_le_elementaryAbelianPRank hp hodd hcard hrank
  have := hAn
  have hWn : (omega1Subgroup p A).Normal := normal_omega1Subgroup p A
  have hWea : IsElementaryAbelian p (omega1Subgroup p A) :=
    isElementaryAbelian_omega1Subgroup p A hAc
  have hBW : B ≤ omega1Subgroup p A := fun x hx =>
    mem_omega1Subgroup (hBA hx) ((isElementaryAbelian_of_nonempty_mulEquiv_pi hB).pow_eq_one hx)
  have hBcard : Nat.card B = p ^ 3 := natCard_eq_pow_of_nonempty_mulEquiv_pi hB
  have hdvd : p ^ 3 ∣ Nat.card (omega1Subgroup p A) := hBcard ▸ Subgroup.card_dvd_of_le hBW
  obtain ⟨B', hB'W, hB'n, hB'card⟩ :=
    exists_normal_le_natCard_eq_pow_of_isPGroup hp hRp (omega1Subgroup p A) hdvd
  have := hB'n
  have hB'ea : IsElementaryAbelian p B' := hWea.mono hB'W
  set K := B' ⊓ centralizer (E : Set R) with hKdef
  have hKea : IsElementaryAbelian p K := hB'ea.mono inf_le_left
  have hKc : K ≤ centralizer (E : Set R) := inf_le_right
  refine ⟨E ⊔ K, inferInstance, by rw [sup_comm]; exact hKea.sup_of_le_centralizer hEea hKc, ?_⟩
  refine lt_of_le_of_ne le_sup_left fun hEq => ?_
  have hKE : K ≤ E := by
    intro x hx
    have hmem : x ∈ E ⊔ K := mem_sup_right hx
    rwa [← hEq] at hmem
  obtain ⟨L, hLle, hL⟩ := exists_elementaryAbelian_rank_two_le_inf_centralizer (D := E) (E := B')
    ⟨(nonempty_mulEquiv_pi_of_isElementaryAbelian hp hEea hEcard).some.trans
      (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod p).symm⟩
    ⟨(nonempty_mulEquiv_pi_of_isElementaryAbelian hp hB'ea hB'card).some.trans
      (MulEquiv.piMultiplicative fun _ : Fin 3 => ZMod p).symm⟩
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLcard : Nat.card L = p ^ 2 :=
    natCard_eq_pow_of_nonempty_mulEquiv_pi
      ⟨hL.some.trans (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod p)⟩
  have hp2K : p ^ 2 ≤ Nat.card K := hLcard ▸ Subgroup.card_le_of_le hLle
  have hKeqE : K = E := Subgroup.eq_of_le_of_card_ge hKE (by rw [hEcard]; exact hp2K)
  have hEB' : E ≤ B' := hKeqE ▸ inf_le_left
  have hB'K : B' ≤ K := le_inf le_rfl (hB'ea.le_centralizer hEB')
  have hKeqB' : K = B' := le_antisymm inf_le_left hB'K
  have h32 : p ^ 3 = p ^ 2 := by rw [← hB'card, ← hKeqB', hKeqE, hEcard]
  have := Nat.pow_right_injective hp.two_le h32
  omega

theorem exists_normal_isElementaryAbelian_gt_of_mulEquiv_pi (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card R = p ^ n) (hrank : 3 ≤ elementaryAbelianPRank p R) [E.Normal]
    (hE : Nonempty (↥E ≃* (Fin 2 → Multiplicative (ZMod p)))) :
    ∃ D : Subgroup R, D.Normal ∧ E < D ∧
      ∃ d, Nonempty (↥D ≃* (Fin d → Multiplicative (ZMod p))) := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨D, hDn, hDea, hED⟩ := exists_normal_isElementaryAbelian_gt_of_natCard_eq_sq hp hodd hcard
    hrank (isElementaryAbelian_of_nonempty_mulEquiv_pi hE)
    (natCard_eq_pow_of_nonempty_mulEquiv_pi hE)
  obtain ⟨d, hd⟩ := hDea.exists_natCard_eq_pow hp
  exact ⟨D, hDn, hED, d, nonempty_mulEquiv_pi_of_isElementaryAbelian hp hDea hd⟩

theorem not_maximal_isElementaryAbelian_of_normal_of_natCard_eq_sq (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card R = p ^ n) (hrank : 3 ≤ elementaryAbelianPRank p R) [E.Normal]
    (hEea : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    ¬ Maximal (IsElementaryAbelian p) E := by
  intro hmax
  obtain ⟨D, -, hDea, hED⟩ :=
    exists_normal_isElementaryAbelian_gt_of_natCard_eq_sq hp hodd hcard hrank hEea hEcard
  exact absurd (hmax.le_of_ge hDea hED.le) hED.not_ge

end

end CFSG.FeitThompson
