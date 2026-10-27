module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSympData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSympB2der
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSympSize
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSympBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSympClash
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamSymp)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

set_option linter.unusedSectionVars false

private theorem i167CSymp_holds_aux1 {S : Type} [Group S] {p : ℕ} {α : MulAut S}
    (hp : p.Prime) (hord : orderOf α = p) : α ^ p = 1 ∧ α ≠ 1 := by
  constructor
  · rw [← hord]; exact pow_orderOf_eq_one α
  · intro h
    rw [h, orderOf_one] at hord
    exact hp.ne_one hord.symm

private theorem i167CSymp_holds_aux2 {labK : GLALabel}
    (hFam : FamSymp labK) (hbc : ¬ (labK.tag = .B ∨ labK.tag = .C)) : labK.tag = .B2der := by
  unfold FamSymp at hFam
  rcases hFam with h | h | h
  · exact absurd (Or.inl h) hbc
  · exact absurd (Or.inr h) hbc
  · exact h

private theorem i167CSymp_holds_aux3 {S : Type} [Group S] [Finite S] {labK : GLALabel}
    {α : MulAut S} {p : ℕ} {J : Subgroup S} (hcen : Subgroup.center S = ⊥)
    (h2der : labK.tag = .B2der) (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labK α)
    (hbig : 720 < Nat.card (PSimple p J)) : False := by
  have hS := i167CS_card_B2der hcen h2der hin
  have hsurj : Function.Surjective (fun y : ↥J =>
      QuotientGroup.mk' (Subgroup.center (PQuot p J))
        (QuotientGroup.mk' (GLAPPrimeCore p ↥J) y)) :=
    (QuotientGroup.mk'_surjective (N := Subgroup.center (PQuot p J))).comp
      (QuotientGroup.mk'_surjective (N := GLAPPrimeCore p ↥J))
  have hleJ : Nat.card (PSimple p J) ≤ Nat.card ↥J := Nat.card_le_card_of_surjective _ hsurj
  have hleS : Nat.card ↥J ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun y : ↥J => (y : S)) Subtype.val_injective
  omega

private theorem i167CSymp_holds_aux4 {S : Type} [Group S] [Finite S] {p a k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup S} {lab : GLALabel}
    (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hT : (p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
      (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
      (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
        canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩))
    (hlab : HasLabel (PQuot p J) (fun l : GLALabel => l = lab))
    {E : Type} [Field E] [Finite E] (ha : 2 ≤ a) (hE : Nat.card E = 2 ^ k)
    (hd : a = 2 ∨ p ∣ 2 ^ k - 1)
    (e : PSimple p J ≃* StatedProj (StatedSL a E)) : False := by
  have hdict := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig
    (PQuot p J) lab a k E ha hE hlab ⟨e⟩
  exact i167CS_clash hp hp2 hT (Or.inl ⟨a, k, ha, hd, hdict⟩)

private theorem i167CSymp_holds_aux5 {S : Type} [Group S] [Finite S] {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup S} {lab : GLALabel}
    (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hT : (p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
      (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
      (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
        canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩))
    (hlab : HasLabel (PQuot p J) (fun l : GLALabel => l = lab))
    {a : ℕ} {E : Type} [Field E] [Finite E] (τ : E ≃+* E) (hτ : ∀ y, τ (τ y) = y)
    (ha : 2 ≤ a) (hτk : ∀ y, τ y = y ^ 2 ^ k) (hE : Nat.card E = (2 ^ k) ^ 2)
    (e : PSimple p J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ)) : False := by
  rcases CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC.uniLabel_cases hRig τ hτ ha hτk hE hlab ⟨e⟩
    with h | h
  · exact i167CS_clash hp hp2 hT (Or.inr (Or.inl ⟨a, k, Or.inl h⟩))
  · exact i167CS_clash hp hp2 hT (Or.inr (Or.inl ⟨a, k, Or.inr h⟩))

private theorem i167CSymp_holds_aux6 {S : Type} [Group S] [Finite S] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup S} {lab : GLALabel}
    (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hT : (p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
      (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
      (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
        canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩))
    (hlab : HasLabel (PQuot p J) (fun l : GLALabel => l = lab))
    {K : Type} [Field K] [Finite K] {s : ℕ} (hs2 : 2 ≤ s)
    (hKcard : Nat.card K = 2 ^ n) (hne : ¬ (s = 2 ∧ Nat.card K = 2))
    (e : PSimple p J ≃* StatedProj (StatedSp s K)) : False := by
  have h := CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs2
    hKcard hne hlab e
  exact i167CS_clash hp hp2 hT (Or.inr (Or.inr ⟨s, n, h⟩))

private theorem i167CSymp_holds_aux7 {S T : Type} [Group S] [Group T] {p : ℕ}
    {J : Subgroup S} {J' : Subgroup T}
    (hbig : 720 < Nat.card (PSimple p J)) (ePS : PSimple p J ≃* PSimple p J')
    (hcard : Nat.card (PSimple p J') ≤ 720) : False := by
  have hc : Nat.card (PSimple p J) = Nat.card (PSimple p J') := Nat.card_congr ePS.toEquiv
  omega


theorem i167CSymp_holds : I167CSymp := by
  intro S _ _ p Bb α J labK hp hp2 hFam hcen hBb hαB hord hin hSc hCJ hhalf hJ htype; exfalso
  have hRig : CFSG.StandardType.GGLabelRigidInput := CFSG.StandardType.ggLabelRigidInput_holds
  have hb : CatDistinct.OrderBridge := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  obtain ⟨hαp, hα1⟩ := i167CSymp_holds_aux1 hp hord
  have hbig : 720 < Nat.card (PSimple p J) := i167CS_card_gt hb htype
  by_cases hbc : labK.tag = .B ∨ labK.tag = .C
  · obtain ⟨K, hK, hKf, n, m, x, J', hn, hKcard, h2, hm, hxp, hx1, hJ', ⟨ePQ⟩⟩ :=
    i167CS_data hp hcen hbc hαp hα1 hin hJ
    have hQ : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
    obtain ⟨lab, hlab, hT⟩ : ∃ lab : GLALabel, HasLabel (PQuot p J) (fun l : GLALabel => l = lab) ∧
        ((p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
         (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
         (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
           canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩)) := by
      rcases htype with ⟨h3, n, -, hn5, h⟩ | ⟨h3, n, -, hn6, h⟩ | ⟨n, k, -, hn3, hnk, hk, hpk, h⟩
      · subst h3
        obtain ⟨lab, hl, hc⟩ := i167COrth_label_isLnA hQ hn5 h
        exact ⟨lab, hl, Or.inl ⟨rfl, n, hn5, hc⟩⟩
      · subst h3
        obtain ⟨lab, hl, hc⟩ := i167COrth_label_isOmMA hQ (n := n) (k := 1) (by omega) le_rfl
          (by rw [pow_one]; exact h)
        exact ⟨lab, hl, Or.inr (Or.inl ⟨rfl, n, hn6, hc⟩)⟩
      · obtain ⟨lab, hl, hc⟩ := i167COrth_label_isOmPA hQ hn3 hk
          (fun h3 => by
            by_contra hk2
            have := hnk (by omega)
            omega) h
        exact ⟨lab, hl, Or.inr (Or.inr ⟨n, k, hn3, hk, hpk, hc⟩)⟩
    have ePS : PSimple p J ≃* PSimple p J' :=
      QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)
    rcases i167CS_block hKcard hn (by omega) hp hp2 x hxp hJ' with
      ⟨a, k, E, hE, hEf, ha2, hEk, hd, ⟨e⟩⟩ |
      ⟨a, k, E, hE, hEf, τ, hτ, ha2, hτk, hEc, ⟨e⟩⟩ |
      ⟨s, hs2, hne, ⟨e⟩⟩ | ⟨-, hcard⟩
    ·
      exact i167CSymp_holds_aux4 hp hp2 hRig hT hlab ha2 hEk hd (ePS.trans e)
    ·
      exact i167CSymp_holds_aux5 hp hp2 hRig hT hlab τ hτ ha2 hτk hEc (ePS.trans e)
    ·
      exact i167CSymp_holds_aux6 hp hp2 hRig hT hlab hs2 hKcard hne (ePS.trans e)
    ·
      exact i167CSymp_holds_aux7 hbig ePS hcard
  ·
    exact i167CSymp_holds_aux3 hcen (i167CSymp_holds_aux2 hFam hbc) hin hbig

end CFSG.LocalAnalysis.GLTheoremA.I167

end
