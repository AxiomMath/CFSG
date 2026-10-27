module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagLift
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.CommonNbrQTwo

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

private theorem le_qPerp_span_singleton_of_polar {n : ℕ}
    {p : Submodule K (Fin n ⊕ Fin n → K)} {y : Fin n ⊕ Fin n → K}
    (h : ∀ v ∈ p, polar (quadPlus n K) v y = 0) :
    p ≤ qPerp n K (K ∙ y) := by
  intro v hv
  rw [mem_qPerp]
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [polar_smul_left, polar_comm, h v hv, smul_zero]

private theorem le_flipOrth_span_singleton_of_flipHerm {n : ℕ} (hσ : ∀ x, σ (σ x) = x)
    {p : Submodule K (Fin n ⊕ Fin n → K)} {y : Fin n ⊕ Fin n → K}
    (h : ∀ v ∈ p, flipHerm σ v y = 0) :
    p ≤ flipOrth σ (K ∙ y) := by
  intro v hv
  rw [mem_flipOrth]
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [flipHerm_smul_left, (flipHerm_eq_zero_iff hσ).mp (h v hv), mul_zero]

private theorem cycleHomotopic_pentWalk_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {m : ℕ} (hm : 4 ≤ m)
    (h4 : NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 4) {a b c d e : FlipPt σ (m + 1)}
    (hab : (flipGraph σ (m + 1)).Adj a b) (hbc : (flipGraph σ (m + 1)).Adj b c)
    (hcd : (flipGraph σ (m + 1)).Adj c d) (hde : (flipGraph σ (m + 1)).Adj d e)
    (hea : (flipGraph σ (m + 1)).Adj e a) :
    CycleHomotopic (flagNullWalks σ (Nat.le_of_succ_le hm))
      (pentWalk hab hbc hcd hde hea) .nil := by
  have h3 : NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 3 :=
    nullLen_three_flagNullWalks_of_card_eq_four hσ hK (Nat.le_of_succ_le hm)
  let X : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := c.1 ⊔ d.1
  have hX : IsFlipflopSub σ X := hcd.2
  have hXfin : Module.finrank K X = 2 := (hcd.isFlipLine c.2 d.2).2
  obtain ⟨α, haα, -, -⟩ := a.2.exists_eq_span
  have hdim : Module.finrank K X + 3 ≤ m + 1 := by omega
  obtain ⟨p, hp, hpXq, hpXh, hpα⟩ :=
    exists_isFlipflopPt_orth_orth_of_card_eq_four hσ hK hX hdim α
  have hpqc : p ≤ qPerp (m + 1) K c.1 := by
    refine le_trans hpXq ?_
    dsimp only [X]
    rw [qPerp_sup]
    exact inf_le_left
  have hphc : p ≤ flipOrth σ c.1 := by
    refine le_trans hpXh ?_
    dsimp only [X]
    rw [flipOrth_sup]
    exact inf_le_left
  have hpqd : p ≤ qPerp (m + 1) K d.1 := by
    refine le_trans hpXq ?_
    dsimp only [X]
    rw [qPerp_sup]
    exact inf_le_right
  have hphd : p ≤ flipOrth σ d.1 := by
    refine le_trans hpXh ?_
    dsimp only [X]
    rw [flipOrth_sup]
    exact inf_le_right
  have hpaq : p ≤ qPerp (m + 1) K a.1 := by
    rw [haα]
    exact le_qPerp_span_singleton_of_polar fun v hv => (hpα v hv).1
  have hpah : p ≤ flipOrth σ a.1 := by
    rw [haα]
    exact le_flipOrth_span_singleton_of_flipHerm hσ.invol fun v hv => (hpα v hv).2
  have hfc : FlipColl σ p c.1 := flipColl_of_orth hσ.invol hp c.2 hpqc hphc
  have hfd : FlipColl σ p d.1 := flipColl_of_orth hσ.invol hp d.2 hpqd hphd
  have haf' : FlipColl σ p a.1 := flipColl_of_orth hσ.invol hp a.2 hpaq hpah
  have haf : FlipColl σ a.1 p := ⟨haf'.1.symm, by rw [sup_comm]; exact haf'.2⟩
  refine cycleHomotopic_pent_nil_of_apex (flagNullWalks σ (Nat.le_of_succ_le hm)) h3 h4
    (f := ⟨p, hp⟩) hab hbc hcd hde hea ?_ ?_ ?_
  · exact hfc
  · exact hfd
  · exact haf

theorem nullLen_five_flagNullWalks_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 4 ≤ m)
    (h4 : NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 4) :
    NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 5 := by
  intro u p hp
  match u, p, hp with
  | _, .nil, hp => simp at hp
  | _, .cons _ .nil, hp => simp at hp
  | _, .cons _ (.cons _ .nil), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ .nil)), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ (.cons _ .nil))), hp => simp at hp
  | _, .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil)))), _ =>
    exact cycleHomotopic_pentWalk_of_card_eq_four hσ hK hm h4 hab hbc hcd hde hea
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

end CFSG.ClassicalInvolution.PhanDn
