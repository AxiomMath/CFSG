module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PBlock
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkCycle
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PConj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P

open CFSG.Open Subgroup
open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

variable {G : Type} [Group G] [Finite G]

theorem exists_abelian_normalized {B N Y T : Subgroup G}
    (hBN : B ≤ normalizer (N : Set G)) (hchar : IsCharacteristicP 2 ↥N)
    (hY : IsBlockOfInX N Y) (hTY : T ≤ Y) (hT3 : Nat.card T = 3)
    (hST : B ⊓ normalizer (Y : Set G) ≤ normalizer (T : Set G)) :
    ∃ E : Subgroup G, (∀ b ∈ B, cj T b ≤ E) ∧ E ≤ N ∧ (∀ u ∈ E, ∀ v ∈ E, u * v = v * u) ∧
      (∀ β ∈ B, cj E β ≤ E) ∧ IsPGroup 3 E := by
  obtain ⟨t, -, hTt⟩ := exists_zpowers_eq hT3
  have hTab : ∀ s ∈ T, ∀ s' ∈ T, s * s' = s' * s := by
    intro s hs s' hs'
    rw [hTt] at hs hs'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hs'
    exact (Commute.zpow_zpow_self t i j).eq
  have hT3exp : ∀ s ∈ T, s ^ 3 = 1 := by
    intro s hs
    have h := pow_card_eq_one' (G := ↥T) (x := ⟨s, hs⟩)
    rw [hT3] at h
    simpa using congrArg Subtype.val h
  have hblock : ∀ b ∈ B, IsBlockOfInX N (cj Y b) := by
    intro b hb
    have := isBlockOfInX_conjugate_of_normalizes hY (g := b⁻¹) (Subgroup.inv_mem _ (hBN hb))
    rwa [ThreeFromEight.conjugate_inv_eq_map] at this
  have hdiff : ∀ b ∈ B, ∀ b' ∈ B, cj Y b ≠ cj Y b' → ∀ u ∈ cj Y b, ∀ v ∈ cj Y b',
      u * v = v * u := by
    intro b hb b' hb' hne u hu v hv
    have h := distinct_blocks_commute_of_isBlockOfInX hchar (hblock b hb) (hblock b' hb') hne
    have h1 := Subgroup.commutator_mem_commutator hu hv
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hsame : ∀ b ∈ B, ∀ b' ∈ B, cj Y b = cj Y b' → cj T b = cj T b' := by
    intro b hb b' hb' h
    have hc : b'⁻¹ * b ∈ B := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb') hb
    have hcY : cj Y (b'⁻¹ * b) = Y := by
      calc cj Y (b'⁻¹ * b) = cj (cj Y b) b'⁻¹ := (cj_cj Y b b'⁻¹).symm
        _ = cj (cj Y b') b'⁻¹ := by rw [h]
        _ = cj Y (b'⁻¹ * b') := cj_cj Y b' b'⁻¹
        _ = Y := by rw [inv_mul_cancel, cj_one]
    have hcT : cj T (b'⁻¹ * b) = T :=
      cj_eq_of_mem_normalizer (hST ⟨hc, mem_normalizer_of_cj_eq hcY⟩)
    calc cj T b = cj T (b' * (b'⁻¹ * b)) := by rw [mul_inv_cancel_left]
      _ = cj (cj T (b'⁻¹ * b)) b' := (cj_cj T _ _).symm
      _ = cj T b' := by rw [hcT]
  set E : Subgroup G := ⨆ b : B, cj T (b : G) with hE
  have hcjT : ∀ b ∈ B, cj T b ≤ E := fun b hb =>
    le_iSup (fun b' : B => cj T (b' : G)) ⟨b, hb⟩
  have hfam : ∀ b b' : B, ∀ u ∈ cj T (b : G), ∀ v ∈ cj T (b' : G), u * v = v * u := by
    intro b b' u hu v hv
    by_cases hY' : cj Y (b : G) = cj Y (b' : G)
    · have hTT := hsame b b.2 b' b'.2 hY'
      rw [← hTT] at hv
      rw [mem_cj] at hu hv
      have h := hTab _ hu _ hv
      calc u * v = (b : G) * (((b : G)⁻¹ * u * b) * ((b : G)⁻¹ * v * b)) * (b : G)⁻¹ := by group
        _ = (b : G) * (((b : G)⁻¹ * v * b) * ((b : G)⁻¹ * u * b)) * (b : G)⁻¹ := by rw [h]
        _ = v * u := by group
    · exact hdiff b b.2 b' b'.2 hY' u (cj_mono hTY _ hu) v (cj_mono hTY _ hv)
  have hEab : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    commute_of_iSup (fun b : B => cj T (b : G)) hfam hu hv
  have hEN : E ≤ N := iSup_le fun b => (cj_mono hTY _).trans (hblock b b.2).1
  have hcjE : ∀ β ∈ B, cj E β ≤ E := by
    intro β hβ
    rw [hE, cj_iSup]
    refine iSup_le fun b => ?_
    rw [cj_cj]
    exact hcjT _ (Subgroup.mul_mem _ hβ b.2)
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    refine Subgroup.iSup_induction' (fun b : B => cj T (b : G))
      (C := fun e _ => e ^ 3 = 1) ?_ ?_ ?_ he
    · intro b s hs
      rw [mem_cj] at hs
      have h1 := hT3exp _ hs
      have e1 : s = (b : G) * ((b : G)⁻¹ * s * b) * (b : G)⁻¹ := by group
      rw [e1, conj_pow, h1]
      group
    · simp
    · intro x y hx hy ihx ihy
      have hc : Commute x y := hEab x hx y hy
      rw [hc.mul_pow, ihx, ihy, one_mul]
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
  exact ⟨E, hcjT, hEN, hEab, hcjE, hEp⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P
