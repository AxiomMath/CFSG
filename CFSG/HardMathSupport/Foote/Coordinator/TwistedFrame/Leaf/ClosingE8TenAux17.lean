module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux15

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem Uθ_comm_Qθ' {τ : Tag} {K : Type} [Field K] {u q : ModGL τ K} (hu : u ∈ Uθ τ K)
    (hq : q ∈ Qθ τ K) : u * q = q * u :=
  CoordAux.Uθ_comm hu (parabolicRadical_le_posUnipotent (Jθ τ) hq)

section Reduce

variable (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w)

open Classical in
theorem opposite_reduce (hb : TwBasic (c.X₁ D) (c.X₂ D))
    {H : Subgroup (ModGL c.tag K)} (hXH : c.X₁ D ⊔ c.X₂ D ≤ H)
    {q : ModGL c.tag K} (hq : q ∈ Qθ c.tag K)
    (hBH : conjSub q (Heis.Uneg c.tag K) ≤ H)
    (hBX : ¬ conjSub q (Heis.Uneg c.tag K) ≤ c.X₁ D ⊔ c.X₂ D) :
    ∃ v : ModGL c.tag K, v ∈ Qθ c.tag K ∧ conjSub v (Heis.Uneg c.tag K) ≤ H ∧
      (∀ β, CoordsAux.κ D v β ≠ 0 → β ∈ Deg1 c.tag ∧ β ∉ CoordsAux.Bset c) ∧
      ∃ β, CoordsAux.κ D v β ≠ 0 := by
  have hw : c.w • highRoot c.tag = highRoot c.tag := CoordsAux.w_smul_highRoot c
  obtain ⟨ε, -, hε⟩ := CoordsAux.exists_monomial (τ := c.tag) (F := D.L) hw
  have hε' : CoordsAux.MonomialProp c.w ε := hε
  have hsig := CoordsAux.κ_isSig D hw hε' hq
  obtain ⟨qS, hqS, hκS⟩ : ∃ qS : ModGL c.tag K, qS ∈ Qθ c.tag K ∧
      CoordsAux.κ D qS = fun β => if β ∈ CoordsAux.Bset c then CoordsAux.κ D q β else 0 :=
    CoordsAux.exists_lift D hw hε' (TwCoordsAux.isSig_pB c D hsig)
  obtain ⟨qM, hqM, hκM⟩ : ∃ qM : ModGL c.tag K, qM ∈ Qθ c.tag K ∧
      CoordsAux.κ D qM = fun β => if β ∈ CoordsAux.Bset c then 0 else CoordsAux.κ D q β :=
    CoordsAux.exists_lift D hw hε' (TwCoordsAux.isSig_pM c D hsig)
  have hqSX : qS ∈ c.X₁ D := CoordsAux.mem_X₁_of_support c D hqS fun β hβ => by
    by_contra hB
    apply hβ
    rw [hκS]
    simp [hB]
  have hX₁X : c.X₁ D ≤ c.X₁ D ⊔ c.X₂ D := le_sup_left
  have hqSH : qS ∈ H := hXH (hX₁X hqSX)
  have hU : q * (qS * qM)⁻¹ ∈ Uθ c.tag K := split_mem c D hq hqS hqM hκS hκM
  have hSM : qS * qM ∈ Qθ c.tag K := mul_mem hqS hqM
  set v : ModGL c.tag K := qS⁻¹ * q with hv
  have hvQ : v ∈ Qθ c.tag K := mul_mem (inv_mem hqS) hq
  have hvU : v * qM⁻¹ ∈ Uθ c.tag K := by
    have e : v * qM⁻¹ = qS⁻¹ * (q * (qS * qM)⁻¹) * qS := by
      rw [hv]
      group
    rw [e]
    have hc : (q * (qS * qM)⁻¹) * qS = qS * (q * (qS * qM)⁻¹) := Uθ_comm_Qθ' hU hqS
    have e2 : qS⁻¹ * (q * (qS * qM)⁻¹) * qS = q * (qS * qM)⁻¹ := by
      calc qS⁻¹ * (q * (qS * qM)⁻¹) * qS = qS⁻¹ * ((q * (qS * qM)⁻¹) * qS) := by group
        _ = qS⁻¹ * (qS * (q * (qS * qM)⁻¹)) := by rw [hc]
        _ = q * (qS * qM)⁻¹ := by group
    rw [e2]
    exact hU
  have hκv : CoordsAux.κ D v = CoordsAux.κ D qM := by
    have h0 : CoordsAux.κ D (v * qM⁻¹) = 0 := (CoordsAux.κ_eq_zero_iff D (mul_mem hvQ (inv_mem hqM))).2 hvU
    have := CoordsAux.κ_mul D hvQ (inv_mem hqM)
    rw [h0, TwCoordsAux.κ_inv c D hqM] at this
    funext β
    have hβ := congrFun this β
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hβ
    exact (add_neg_eq_zero.1 hβ.symm)
  have hB'eq : conjSub v (Heis.Uneg c.tag K) = conjSub qS⁻¹ (conjSub q (Heis.Uneg c.tag K)) := by
    rw [hv, conjSub_mul]
  have hB'H : conjSub v (Heis.Uneg c.tag K) ≤ H := by
    rw [hB'eq]
    exact conjSub_le_of_mem_of_le (inv_mem hqSH) hBH
  have hB'X : ¬ conjSub v (Heis.Uneg c.tag K) ≤ c.X₁ D ⊔ c.X₂ D := by
    intro hle
    apply hBX
    have e : conjSub q (Heis.Uneg c.tag K) = conjSub qS (conjSub v (Heis.Uneg c.tag K)) := by
      rw [hB'eq]
      exact (conjSub_conjSub_inv qS _).symm
    rw [e]
    exact conjSub_le_of_mem_of_le (hX₁X hqSX) hle
  refine ⟨v, hvQ, hB'H, fun β hβ => ?_, ?_⟩
  · have hβ' : CoordsAux.κ D qM β ≠ 0 := by rw [← hκv]; exact hβ
    rw [hκM] at hβ'
    dsimp only at hβ'
    split_ifs at hβ' with hB
    · exact absurd rfl hβ'
    · refine ⟨?_, hB⟩
      by_contra hn
      exact hβ' (CoordsAux.κ_support D hq hn)
  · by_contra hno
    push Not at hno
    have hv0 : CoordsAux.κ D v = 0 := funext hno
    have hvU' : v ∈ Uθ c.tag K := (CoordsAux.κ_eq_zero_iff D hvQ).1 hv0
    apply hB'X
    have hvX : v ∈ c.X₁ D ⊔ c.X₂ D := hX₁X (TwCoordsAux.Uθ_le_X₁ c D hvU')
    exact conjSub_le_of_mem_of_le hvX (hb.Uneg_le.trans hX₁X)

end Reduce

section NCalc

variable {L : Type} [Field L]

theorem comm_root {α β : Fin Tag.E8.rank → ℤ} (hα : α ∈ rootFinset Tag.E8)
    (hβ : β ∈ rootFinset Tag.E8) (hne : α ≠ β) (hne' : α ≠ -β) (hs : α + β ∈ rootFinset Tag.E8)
    (c d : L) :
    ∃ ε : L, (ε = 1 ∨ ε = -1) ∧
      ⁅pinnedX Tag.E8 L α c, pinnedX Tag.E8 L β d⁆ = pinnedX Tag.E8 L (α + β) (ε * c * d) := by
  obtain ⟨hε, hform⟩ := (simply_laced_root_commutator_unit.{0} Tag.E8
    (Or.inr (Or.inr (Or.inr rfl))) (mem_rootFinset.1 hα) (mem_rootFinset.1 hβ) hne hne').1
    (mem_rootFinset.1 hs)
  refine ⟨(commConst Tag.E8 α β (1, 1) : L), ?_, hform L c d⟩
  rcases hε with h | h <;> rw [h] <;> simp

structure AdjPair (β₀ β₁ : Fin Tag.E8.rank → ℤ) : Prop where
  h₀ : β₀ ∈ rootFinset Tag.E8
  h₁ : β₁ ∈ rootFinset Tag.E8
  r₀ : -highRoot Tag.E8 + β₀ ∈ rootFinset Tag.E8
  r₁ : -highRoot Tag.E8 + β₁ ∈ rootFinset Tag.E8
  m₀ : -highRoot Tag.E8 ≠ β₀
  m₀' : -highRoot Tag.E8 ≠ -β₀
  m₁ : -highRoot Tag.E8 ≠ β₁
  m₁' : -highRoot Tag.E8 ≠ -β₁
  p₀ : highRoot Tag.E8 ≠ -highRoot Tag.E8 + β₀
  p₀' : highRoot Tag.E8 ≠ -(-highRoot Tag.E8 + β₀)
  p₁ : highRoot Tag.E8 ≠ -highRoot Tag.E8 + β₁
  p₁' : highRoot Tag.E8 ≠ -(-highRoot Tag.E8 + β₁)
  c₀ : β₀ ≠ -highRoot Tag.E8 + β₁
  c₀' : β₀ ≠ -(-highRoot Tag.E8 + β₁)
  c₀s : β₀ + (-highRoot Tag.E8 + β₁) ∉ rootFinset Tag.E8
  c₁ : -highRoot Tag.E8 + β₀ ≠ β₁
  c₁' : -highRoot Tag.E8 + β₀ ≠ -β₁
  c₁s : -highRoot Tag.E8 + β₀ + β₁ ∉ rootFinset Tag.E8

theorem N_calc {β₀ β₁ : Fin Tag.E8.rank → ℤ} (hA : AdjPair β₀ β₁) (s d t₁ t₂ : L) :
    ∃ ε₀ ε₁ : L, (ε₀ = 1 ∨ ε₀ = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧
      ⁅pinnedX Tag.E8 L (highRoot Tag.E8) t₁, ⁅pinnedX Tag.E8 L (-highRoot Tag.E8) t₂,
        pinnedX Tag.E8 L β₀ s * pinnedX Tag.E8 L β₁ d⁆⁆ =
      pinnedX Tag.E8 L β₀ (ε₀ * t₁ * t₂ * s) * pinnedX Tag.E8 L β₁ (ε₁ * t₁ * t₂ * d) := by
  set θ := highRoot Tag.E8 with hθ
  have hθr : θ ∈ rootFinset Tag.E8 := mem_rootFinset.2 (isRoot_highRoot _)
  have hnθr : -θ ∈ rootFinset Tag.E8 := mem_rootFinset.2 (isRoot_neg_highRoot _)
  obtain ⟨ε₀, hε₀, e₀⟩ := comm_root (L := L) hnθr hA.h₀ hA.m₀ hA.m₀' hA.r₀ t₂ s
  obtain ⟨ε₁, hε₁, e₁⟩ := comm_root (L := L) hnθr hA.h₁ hA.m₁ hA.m₁' hA.r₁ t₂ d
  have s₀ : θ + (-θ + β₀) = β₀ := by abel
  have s₁ : θ + (-θ + β₁) = β₁ := by abel
  obtain ⟨ε₀', hε₀', e₀'⟩ := comm_root (L := L) hθr hA.r₀ hA.p₀ hA.p₀' (by rw [s₀]; exact hA.h₀)
    t₁ (ε₀ * t₂ * s)
  obtain ⟨ε₁', hε₁', e₁'⟩ := comm_root (L := L) hθr hA.r₁ hA.p₁ hA.p₁' (by rw [s₁]; exact hA.h₁)
    t₁ (ε₁ * t₂ * d)
  rw [s₀] at e₀'
  rw [s₁] at e₁'
  rw [commutatorElement_def] at e₀ e₁ e₀' e₁'
  have hcomm1 : ∀ a b : L, pinnedX Tag.E8 L β₀ a * pinnedX Tag.E8 L (-θ + β₁) b =
      pinnedX Tag.E8 L (-θ + β₁) b * pinnedX Tag.E8 L β₀ a := fun a b =>
    pinnedX_commute_of_not_root hA.h₀ hA.r₁ hA.c₀ hA.c₀' hA.c₀s a b
  have hcomm2 : ∀ a b : L, pinnedX Tag.E8 L (-θ + β₀) a * pinnedX Tag.E8 L β₁ b =
      pinnedX Tag.E8 L β₁ b * pinnedX Tag.E8 L (-θ + β₀) a := fun a b =>
    pinnedX_commute_of_not_root hA.r₀ hA.h₁ hA.c₁ hA.c₁' hA.c₁s a b
  set a' := pinnedX Tag.E8 L (-θ) t₂ with ha'
  set aθ := pinnedX Tag.E8 L θ t₁ with haθ
  set X₀ := pinnedX Tag.E8 L β₀ s with hX₀
  set X₁ := pinnedX Tag.E8 L β₁ d with hX₁
  set Q₀ := pinnedX Tag.E8 L (-θ + β₀) (ε₀ * t₂ * s) with hQ₀
  set Q₁ := pinnedX Tag.E8 L (-θ + β₁) (ε₁ * t₂ * d) with hQ₁
  set Y₀ := pinnedX Tag.E8 L β₀ (ε₀' * t₁ * (ε₀ * t₂ * s)) with hY₀
  set Y₁ := pinnedX Tag.E8 L β₁ (ε₁' * t₁ * (ε₁ * t₂ * d)) with hY₁
  have k₀ : a' * X₀ * a'⁻¹ = Q₀ * X₀ := by
    calc a' * X₀ * a'⁻¹ = (a' * X₀ * a'⁻¹ * X₀⁻¹) * X₀ := by group
      _ = Q₀ * X₀ := by rw [e₀]
  have k₁ : a' * X₁ * a'⁻¹ = Q₁ * X₁ := by
    calc a' * X₁ * a'⁻¹ = (a' * X₁ * a'⁻¹ * X₁⁻¹) * X₁ := by group
      _ = Q₁ * X₁ := by rw [e₁]
  have l₀ : aθ * Q₀ * aθ⁻¹ = Y₀ * Q₀ := by
    calc aθ * Q₀ * aθ⁻¹ = (aθ * Q₀ * aθ⁻¹ * Q₀⁻¹) * Q₀ := by group
      _ = Y₀ * Q₀ := by rw [e₀']
  have l₁ : aθ * Q₁ * aθ⁻¹ = Y₁ * Q₁ := by
    calc aθ * Q₁ * aθ⁻¹ = (aθ * Q₁ * aθ⁻¹ * Q₁⁻¹) * Q₁ := by group
      _ = Y₁ * Q₁ := by rw [e₁']
  have hA' : ⁅a', X₀ * X₁⁆ = Q₀ * Q₁ := by
    rw [commutatorElement_def]
    have : a' * (X₀ * X₁) * a'⁻¹ * (X₀ * X₁)⁻¹ =
        (a' * X₀ * a'⁻¹) * (a' * X₁ * a'⁻¹) * X₁⁻¹ * X₀⁻¹ := by group
    rw [this, k₀, k₁]
    have hc : X₀ * Q₁ = Q₁ * X₀ := hcomm1 s _
    calc Q₀ * X₀ * (Q₁ * X₁) * X₁⁻¹ * X₀⁻¹ = Q₀ * (X₀ * Q₁ * X₀⁻¹) := by group
      _ = Q₀ * Q₁ := by rw [hc]; group
  rw [hA']
  have hN : ⁅aθ, Q₀ * Q₁⁆ = Y₀ * Y₁ := by
    rw [commutatorElement_def]
    have : aθ * (Q₀ * Q₁) * aθ⁻¹ * (Q₀ * Q₁)⁻¹ =
        (aθ * Q₀ * aθ⁻¹) * (aθ * Q₁ * aθ⁻¹) * Q₁⁻¹ * Q₀⁻¹ := by group
    rw [this, l₀, l₁]
    have hc : Q₀ * Y₁ = Y₁ * Q₀ := hcomm2 _ _
    calc Y₀ * Q₀ * (Y₁ * Q₁) * Q₁⁻¹ * Q₀⁻¹ = Y₀ * (Q₀ * Y₁ * Q₀⁻¹) := by group
      _ = Y₀ * Y₁ := by rw [hc]; group
  rw [hN]
  refine ⟨ε₀' * ε₀, ε₁' * ε₁, ?_, ?_, ?_⟩
  · rcases hε₀ with h | h <;> rcases hε₀' with h' | h' <;> simp [h, h']
  · rcases hε₁ with h | h <;> rcases hε₁' with h' | h' <;> simp [h, h']
  · have e1 : ε₀' * t₁ * (ε₀ * t₂ * s) = ε₀' * ε₀ * t₁ * t₂ * s := by ring
    have e2 : ε₁' * t₁ * (ε₁ * t₂ * d) = ε₁' * ε₁ * t₁ * t₂ * d := by ring
    rw [hY₀, hY₁, e1, e2]

end NCalc

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
