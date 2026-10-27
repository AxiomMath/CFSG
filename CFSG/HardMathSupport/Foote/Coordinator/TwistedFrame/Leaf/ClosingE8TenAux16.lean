module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux15
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.MElement
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.EqTop
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Quasi
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Central
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureA

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open MElt

set_option linter.unusedSectionVars false


section Opp

variable {τ : Tag} {K : Type} [Field K]

open MElt in
theorem core_commute_gen {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂)
    (hopp : ∀ q ∈ Qθ τ K, conjSub q (Heis.Uneg τ K) ≤ H →
      ¬ conjSub q (Heis.Uneg τ K) ≤ X₁ ⊔ X₂ →
      ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂))
    (hHG : H ≤ adjointGroup τ K) (hXH : X₁ ⊔ X₂ ≤ H)
    (hno : ∀ m ∈ H, m ∈ Qθ τ K → heisCoord τ K m ∈ VS (X₁ ⊔ X₂))
    {g : ModGL τ K} (hgH : g ∈ H) (hgX : ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂) :
    ∀ a ∈ Uθ τ K, ∀ b ∈ conjSub g (Uθ τ K), a * b = b * a := by
  classical
  have hUθX : Uθ τ K ≤ X₁ ⊔ X₂ := hb.Uθ_le.trans le_sup_left
  have hUθH : Uθ τ K ≤ H := hUθX.trans hXH
  obtain ⟨p, hpP, β, hβ, hw, hnf⟩ := exists_normalForm τ K (hHG hgH)
  have hBH : conjSub p (rootSubgroup τ K β) ≤ H := by
    rw [← hnf]
    exact conjSub_le_of_mem_of_le hgH hUθH
  rw [hnf] at hgX ⊢
  have noM : ¬ ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
    rintro ⟨m, hm, hmQ, hmS⟩
    exact hmS (hno m hm hmQ)
  rcases deg_cases hβ with hd | hd | hd | hd | hd
  · exfalso
    have hβθ : β = highRoot τ := CoordAux.eq_highRoot_of_two_le hβ (by omega)
    apply hgX
    rw [hβθ]
    show conjSub p (Uθ τ K) ≤ _
    rw [conjSub_Uθ_of_mem_Pθ hpP]
    exact hUθX
  · exfalso
    apply noM
    exact exists_M_of_le_Qθ hco hBH
      (conjSub_le_Qθ hpP (rootSubgroup_le_Qθ_of_mem_Deg1 (CoordAux.mem_Deg1.2 ⟨hβ, hd⟩))) hgX
  · exact commute_Uθ_conjSub_of_deg_zero hpP hβ hd
  · rcases exists_M_of_special hb hco hp hXH hpP hw hd hBH hgX with h | h
    · exact absurd h noM
    · exact h
  · exfalso
    apply noM
    have hβ' := eq_neg_highRoot_of_deg_neg_two hβ hd
    subst hβ'
    obtain ⟨q, hq, hpq⟩ := exists_conjSub_Pθ_Uneg τ K hpP
    refine hopp q hq ?_ ?_
    · rw [← hpq]
      exact hBH
    · rw [← hpq]
      exact hgX

open MElt in
theorem exists_M_element_gen {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hc : TwCentral X₁ X₂) (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂)
    (hopp : ∀ q ∈ Qθ τ K, conjSub q (Heis.Uneg τ K) ≤ H →
      ¬ conjSub q (Heis.Uneg τ K) ≤ X₁ ⊔ X₂ →
      ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂))
    (hHG : H ≤ adjointGroup τ K) (hXH : X₁ ⊔ X₂ ≤ H) {g : ModGL τ K}
    (hgH : g ∈ H) (hgX : ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂) :
    ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
  classical
  by_contra! hno
  have hX₁X : X₁ ≤ X₁ ⊔ X₂ := le_sup_left
  refine hgX fun b hb₀ => ?_
  have hbc : ∀ x ∈ X₁, b * x = x * b := by
    have hle : (⨆ x ∈ X₁, conjSub x (Uθ τ K)) ≤ Subgroup.centralizer ({b} : Set (ModGL τ K)) := by
      refine iSup₂_le fun x hx y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxH : x⁻¹ ∈ H := inv_mem (hXH (hX₁X hx))
      have hg'H : x⁻¹ * g ∈ H := mul_mem hxH hgH
      have hg'X : ¬ conjSub (x⁻¹ * g) (Uθ τ K) ≤ X₁ ⊔ X₂ := by
        intro hle
        apply hgX
        have e : conjSub g (Uθ τ K) = conjSub x (conjSub (x⁻¹ * g) (Uθ τ K)) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
        rw [e]
        exact conjSub_le_of_mem_of_le (hX₁X hx) hle
      have ha : x⁻¹ * y * x ∈ Uθ τ K := mem_conjSub_iff.1 hy
      have hb' : x⁻¹ * b * x ∈ conjSub (x⁻¹ * g) (Uθ τ K) := by
        rw [mem_conjSub_iff]
        have e : (x⁻¹ * g)⁻¹ * (x⁻¹ * b * x) * (x⁻¹ * g) = g⁻¹ * b * g := by group
        rw [e]
        exact mem_conjSub_iff.1 hb₀
      have h := core_commute_gen hb hco hp hopp hHG hXH hno hg'H hg'X _ ha _ hb'
      calc y * b = x * ((x⁻¹ * y * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * b * x) * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
        _ = b * y := by group
    rw [hb.gen] at hle
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hbG : b ∈ adjointGroup τ K := by
    have hu := mem_conjSub_iff.1 hb₀
    have e : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hHG hgH)
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) (highRoot τ) hu)) (inv_mem (hHG hgH))
  have hbp : b ^ ringChar K = 1 := by
    obtain ⟨c, hc'⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hb₀)
    have e : b = g * pinnedX τ K (highRoot τ) c * g⁻¹ := by rw [hc']; group
    rw [e, conj_pow, pinnedX_pow, ringChar.Nat.cast_ringChar, zero_mul, pinnedX_zero]
    group
  exact hc.unipotent_le b hbG hbc hbp


end Opp

section Final


variable (K : Type) [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem e8Ten_minQ_le (h2 : 2 ≤ Nat.card K) : TwClass.e8Ten.minQ ≤ Nat.card K := h2

theorem twClosing_e8Ten_three (h3 : 3 ≤ Nat.card K) :
    TwFrameClosing TwClass.e8Ten.tag K (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  intro H hHG hXH hN
  have hK : TwClass.e8Ten.minQ ≤ Nat.card K := by
    have : TwClass.e8Ten.minQ = 2 := rfl
    omega
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hb := twBasic TwClass.e8Ten K hK D
  have hq := twQuasi_of_ne_e6Six TwClass.e8Ten (by decide) K hK D
  have hc := twCentral TwClass.e8Ten K hK D
  have hco := twCoords TwClass.e8Ten K hK D
  have hp := twPure_A TwClass.e8Ten (by decide) K hK D
  obtain ⟨g, hgH, hgX⟩ := exists_conj_not_le hb hq hc hHG hXH hN
  obtain ⟨m, hmH, hmQ, hmS⟩ := exists_M_element hb hc hco hp h3 hHG hXH hgH hgX
  have hQθ := Qθ_le_of_Melement D H hHG hXH ⟨m, hmH, hmQ, hmS⟩
  exact eq_top_of_Qθ_Uneg_le_of_any _ K hHG hQθ (hb.Uneg_le.trans (le_sup_left.trans hXH))

theorem twClosing_e8Ten_of_opp
    (hopp : ∀ H : Subgroup (ModGL Tag.E8 K), H ≤ adjointGroup Tag.E8 K →
      TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H →
      ∀ q ∈ Qθ Tag.E8 K, conjSub q (Heis.Uneg Tag.E8 K) ≤ H →
        ¬ conjSub q (Heis.Uneg Tag.E8 K) ≤ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D →
        ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
          heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) :
    TwFrameClosing TwClass.e8Ten.tag K (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  intro H hHG hXH hN
  have hK : TwClass.e8Ten.minQ ≤ Nat.card K := by
    have : 2 ≤ Nat.card K := Finite.one_lt_card
    exact this
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hb := twBasic TwClass.e8Ten K hK D
  have hq := twQuasi_of_ne_e6Six TwClass.e8Ten (by decide) K hK D
  have hc := twCentral TwClass.e8Ten K hK D
  have hco := twCoords TwClass.e8Ten K hK D
  have hp := twPure_A TwClass.e8Ten (by decide) K hK D
  obtain ⟨g, hgH, hgX⟩ := exists_conj_not_le hb hq hc hHG hXH hN
  obtain ⟨m, hmH, hmQ, hmS⟩ := exists_M_element_gen hb hc hco hp (hopp H hHG hXH) hHG hXH hgH hgX
  have hQθ := Qθ_le_of_Melement D H hHG hXH ⟨m, hmH, hmQ, hmS⟩
  exact eq_top_of_Qθ_Uneg_le_of_any _ K hHG hQθ (hb.Uneg_le.trans (le_sup_left.trans hXH))

end Final

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
