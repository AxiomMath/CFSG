module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Core
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem noL2RankBound_of_tables (T : Tables113) : NoL2RankBound := by
  intro Q _ _ _hO B L hB hL hLT hidx hmax
  obtain ⟨x, hx, hxn⟩ : ∃ x ∈ B, x ∉ Subgroup.normalizer (L : Set Q) := by
    by_contra hcon
    push Not at hcon
    have h1 : (Subgroup.normalizer (L : Set Q)).relIndex B = 1 :=
      Subgroup.relIndex_eq_one.2 hcon
    omega
  obtain ⟨h2L, h3L, hcen⟩ := T.T0 ↥L hLT
  have Tr : Triple113 B L x := ⟨hB, hL, hcen, hx, hxn, hidx⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB0pos : 0 < Nat.card (t113B0 B L) := Nat.card_pos
  have hcardB := Tr.card_B
  have hKB : t113K B L ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B := le_sup_left
  have hBle : B ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B := le_sup_right
  obtain ⟨y0', hy0'⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hy0L : (y0' : Q) ∈ L := y0'.2
  have hy0o : orderOf (y0' : Q) = 3 := by rw [Subgroup.orderOf_coe, hy0']
  obtain ⟨eY, cY, hYK, hYB0⟩ := Tr.Y_spec hy0L hy0o
  have hE1 : IsElemAbelian 3 (t113B0 B L ⊔ t113Y x (y0' : Q)) ∧
      Nat.card ↥(t113B0 B L ⊔ t113Y x (y0' : Q)) = Nat.card (t113B0 B L) * 27 := by
    have hi : t113B0 B L ⊓ t113Y x (y0' : Q) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact hYB0 z hz.2 hz.1
    obtain ⟨h1, h2⟩ := t113_sup_elemAbelian Tr.B0_elem eY
      (fun p hp r hr => (Tr.B0_comm_K hp r (hYK hr)).symm) hi
    exact ⟨h1, by rw [h2, cY]⟩
  have hE1le : t113B0 B L ⊔ t113Y x (y0' : Q) ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B :=
    sup_le ((inf_le_left : t113B0 B L ≤ B).trans hBle) (hYK.trans hKB)
  have h9 : 9 ≤ Nat.card (t113H B L) := by
    have := hmax _ hE1.1 hE1le
    rw [hE1.2, hcardB] at this
    by_contra hlt
    push Not at hlt
    nlinarith
  obtain ⟨hH9, hHin⟩ := T.T2 ↥L hLT (t113H B L) Tr.H_elem
  have hH : Nat.card (t113H B L) = 9 := le_antisymm hH9 h9
  obtain ⟨α, hαH, hαout⟩ : ∃ α ∈ t113H B L, α ∉ innerAut113 ↥L := by
    by_contra hcon
    push Not at hcon
    have : t113H B L ⊓ innerAut113 ↥L = t113H B L := inf_eq_left.2 hcon
    rw [this] at hHin
    omega
  obtain ⟨⟨a, ha⟩, rfl⟩ := hαH
  have hα3 : t113Rho B L ⟨a, ha⟩ ^ 3 = 1 := Tr.H_elem.2 _ ⟨⟨a, ha⟩, rfl⟩
  have hα1 : t113Rho B L ⟨a, ha⟩ ≠ 1 := fun h => hαout (h ▸ (innerAut113 ↥L).one_mem)
  have hαo : orderOf (t113Rho B L ⟨a, ha⟩) = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨⟨y', hy'o, hy'fix⟩, -⟩ := T.T4 ↥L hLT _ hαo hαout
  have hyL : (y' : Q) ∈ L := y'.2
  have hyo : orderOf (y' : Q) = 3 := by rw [Subgroup.orderOf_coe, hy'o]
  have hay : a * (y' : Q) = (y' : Q) * a := by
    have h := congrArg Subtype.val hy'fix
    have e : ((t113Rho B L ⟨a, ha⟩ y' : ↥L) : Q) = a * (y' : Q) * a⁻¹ := rfl
    rw [e] at h
    calc a * (y' : Q) = (a * (y' : Q) * a⁻¹) * a := by group
      _ = (y' : Q) * a := by rw [h]
  obtain ⟨eY2, cY2, hYK2, hYB02⟩ := Tr.Y_spec hyL hyo
  obtain ⟨eF, cF, hFB, hFY⟩ := Tr.F_spec ha hαout
  have hE2 : IsElemAbelian 3 (Subgroup.zpowers a ⊔ t113B0 B L ⊔ t113Y x (y' : Q)) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ t113B0 B L ⊔ t113Y x (y' : Q)) =
        3 * Nat.card (t113B0 B L) * 27 := by
    have hi : (Subgroup.zpowers a ⊔ t113B0 B L) ⊓ t113Y x (y' : Q) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact hFY _ hYK2 hYB02 z hz.1 hz.2
    have hFy : ∀ f ∈ Subgroup.zpowers a ⊔ t113B0 B L, f * (y' : Q) = (y' : Q) * f := by
      have hle : Subgroup.zpowers a ⊔ t113B0 B L ≤ Subgroup.centralizer ({(y' : Q)} : Set Q) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (fun b hb => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hay
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Tr.B0_comm_K hb _ (Tr.L_le_K hyL)).symm
      intro f hf
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hf))
    obtain ⟨h1, h2⟩ := t113_sup_elemAbelian eF eY2
      (fun f hf z hz => Tr.Y_comm (hFB hf) (hFy f hf) z hz) hi
    exact ⟨h1, by rw [h2, cF, cY2]⟩
  have hE2le : Subgroup.zpowers a ⊔ t113B0 B L ⊔ t113Y x (y' : Q) ≤
      (⨆ g ∈ B, GLBConj g L) ⊔ B :=
    sup_le (hFB.trans hBle) (hYK2.trans hKB)
  have := hmax _ hE2.1 hE2le
  rw [hE2.2, hcardB, hH] at this
  nlinarith

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
