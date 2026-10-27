module

public import CFSG.ClassicalInvolution.Asc77.WP3SCVPart
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.SCV

section Third

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem tq_of_third (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {M N : Subgroup G}
    {a w : G} (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) (hN : N ∈ Ω) (hNM : N ≠ M)
    (hw : IsUniqueInvolution N w) (haN : a ∈ trivialOnQuot N) : w ∈ trivialOnQuot M := by
  have h1 : N ∈ omegaNbr Ω M := mem_omegaNbr_of_trivialOnQuot hp hq hΩ hM ha hN hNM haN
  have h2 : M ∈ omegaNbr Ω N := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hM hN h1
  obtain ⟨b, hb, hMb⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical hN h2
  have hbw : b = w := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hb).eq hw
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := M)).mpr (hbw ▸ hMb)

theorem fuzzyFrame_of_third (hs : ChainFrameSetting p f Ω K J K' z t z') {N : Subgroup G}
    (hN : N ∈ Ω) (hNK : N ≠ K) (hNJ : N ≠ J) (hzN : z ∈ trivialOnQuot N)
    (htN : t ∈ trivialOnQuot N) {w : G} (hw : IsUniqueInvolution N w) (hne : w ≠ z * t) :
    Theorem5.FuzzyFrameOn p f Ω (Subgroup.closure ({z, t, w} : Set G)) := by
  have hΩ := hs.hyp
  have hp := hs.odd
  have hq := hs.five
  have hfd := hs.frame
  have hzt : z * t = t * z := hfd.comm_zt hp hΩ
  have hzw : z * w = w * z := by
    have := conj_eq_of_isUniqueInvolution hw hzN.1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have htw : t * w = w * t := by
    have := conj_eq_of_isUniqueInvolution hw htN.1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hwz : w ≠ z := by
    intro h
    exact hNK (hs.noTwins K hfd.mem N ⟨hN, z, hfd.hz, h ▸ hw⟩)
  have hwt : w ≠ t := by
    intro h
    exact hNJ (hs.noTwins J hfd.memJ N ⟨hN, t, hfd.ht, h ▸ hw⟩)
  have hsq : ∀ a ∈ ({z, t, w} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact hfd.hz.sq
    · exact hfd.ht.sq
    · exact hw.sq
  have hcomm : ∀ a ∈ ({z, t, w} : Set G), ∀ b ∈ ({z, t, w} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | rfl | assumption | exact (by assumption : _ = _).symm
  have hcl := ChainFrame.commutes_closure hcomm
  have hcard : Nat.card (Subgroup.closure ({z, t, w} : Set G)) = 8 :=
    ChainFrame.card_closure_triple_eq_eight hfd.hz.sq hfd.ht.sq hw.sq hzt hzw htw hfd.hz.ne_one
      hfd.ht.ne_one (hfd.t_ne_z hp hq hΩ) hw.ne_one hwz hwt hne
  have hel : IsElemAbelian 2 (Subgroup.closure ({z, t, w} : Set G)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcl _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact ChainFrame.sq_closure hsq hcomm x hx
  have tK : w ∈ trivialOnQuot K :=
    tq_of_third hΩ hp hq hfd.mem hfd.hz hN hNK hw hzN
  have tJ : w ∈ trivialOnQuot J :=
    tq_of_third hΩ hp hq hfd.memJ hfd.ht hN hNJ hw htN
  have tN : w ∈ trivialOnQuot N := trivialOnQuot_of_isUniqueInvolution hp hq hΩ hN hw
  have tKz : z ∈ trivialOnQuot K := trivialOnQuot_of_isUniqueInvolution hp hq hΩ hfd.mem hfd.hz
  have tJt : t ∈ trivialOnQuot J :=
    trivialOnQuot_of_isUniqueInvolution hp hq hΩ hfd.memJ hfd.ht
  refine ⟨![K, J, N], ![z, t, w], ?_, ?_, hel, hcard, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hfd.mem, isClassicalMember_of_twin hΩ hfd.mem hfd.hz⟩
    · exact ⟨hfd.memJ, isClassicalMember_of_twin hΩ hfd.memJ hfd.ht⟩
    · exact ⟨hN, isClassicalMember_of_twin hΩ hN hw⟩
  · congr 1
    ext x
    simp
    tauto
  · intro i
    fin_cases i
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact tKz
      · exact hfd.tq_t hp hq hΩ
      · exact tK
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact hfd.tq_z_J hp hq hΩ
      · exact tJt
      · exact tJ
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact hzN
      · exact htN
      · exact tN

end Third

end CFSG.ClassicalInvolution.Asc77.S28B
