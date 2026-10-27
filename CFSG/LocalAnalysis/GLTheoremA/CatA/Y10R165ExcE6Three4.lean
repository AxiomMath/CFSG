module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165LayerPullback
public import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.SectionRank
open scoped MatrixGroups Pointwise

variable {G : Type*} [Group G] [Finite G] {K : Type*} [Field K] [Finite K]

theorem exists_rank_three_qTorus {J₀ J₁ : Subgroup G} (e : ↥J₀ ≃* SL(3, K))
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card K - 1)
    (hcomm : ∀ a ∈ J₀, ∀ b ∈ J₁, a * b = b * a)
    (hdisj : J₀ ⊓ J₁ = ⊥) {s : G} (hs₁ : s ∈ J₁) (hsq : orderOf s = q) :
    ∃ F : Subgroup G, F ≤ J₀ ⊔ J₁ ∧ IsElemAbelian q F ∧ Nat.card F = q ^ 3 ∧
      3 ≤ CFSG.Open.pRank q F := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  classical
  obtain ⟨F₀, hF₀le, hF₀el, hF₀card⟩ :=
    exists_elemAbelian_le_of_mulEquiv
      (e := e.trans (Subgroup.topEquiv (G := SL(3, K))).symm)
      (T := LinEngine.diagSLSub (F := K) 2 q) le_top
      (LinEngine.isElemAbelian_diagSLSub (F := K))
      (LinEngine.card_diagSLSub (F := K) hdvd)
  set F₁ : Subgroup G := Subgroup.zpowers s with hF₁
  have hF₁le : F₁ ≤ J₁ := Subgroup.zpowers_le.mpr hs₁
  have hF₁card : Nat.card F₁ = q := by rw [hF₁, Nat.card_zpowers, hsq]
  have hsq' : s ^ q = 1 := by
    rw [← hsq]
    exact pow_orderOf_eq_one s
  have hF₁el : IsElemAbelian q F₁ := by
    rw [hF₁]
    exact CFSG.Open.isElemAbelian_zpowers hsq'
  have hcommF : ∀ a ∈ F₀, ∀ b ∈ F₁, a * b = b * a := by
    intro a ha b hb
    exact hcomm a (hF₀le ha) b (hF₁le hb)
  have hinf : F₀ ⊓ F₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hxJ₀ : x ∈ J₀ := hF₀le hxF
    have hxJ₁ : x ∈ J₁ := hF₁le hxZ
    have hxbot : x ∈ J₀ ⊓ J₁ := Subgroup.mem_inf.mpr ⟨hxJ₀, hxJ₁⟩
    rwa [hdisj, Subgroup.mem_bot] at hxbot
  have hel : IsElemAbelian q (F₀ ⊔ F₁ : Subgroup G) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hF₀el hF₁el hcommF
  have hcard : Nat.card (F₀ ⊔ F₁ : Subgroup G) = q ^ 3 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F₀ F₁ hcommF).1
    rw [hinf, Subgroup.card_bot, hF₀card, hF₁card] at h
    simpa [pow_succ, mul_comm] using h
  refine ⟨(F₀ ⊔ F₁ : Subgroup G),
    sup_le_iff.mpr ⟨hF₀le.trans le_sup_left, hF₁le.trans le_sup_right⟩, hel, hcard, ?_⟩
  exact le_pRank hq.one_lt le_rfl hel (by rw [hcard])

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
