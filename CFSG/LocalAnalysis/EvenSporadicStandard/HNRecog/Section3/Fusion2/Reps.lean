module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Klein
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.NoA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Cover

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem reps_bu_classes (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hA8 : A8Shapes a z) {z₀ b u : ↥(Gx a)}
    (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) :
    (IsConj a (b : G) ∧ IsConj a (a * b) ∧ (b : G) ∉ derivedOf (Gx a) ∧
      IsShapeTwoTwoTimesA8 ↥(Gxy a (b : G))) ∧
    (IsConj z (u : G) ∧ IsConj z (a * u) ∧ IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a (u : G))) := by
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 : orderOf a = 2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 : orderOf z = 2 := h.orderOf_z
    rw [h1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hbA8 : IsShapeTwoTwoTimesA8 ↥(Gxy a (b : G)) := by
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxy (G := G) (a := a) (x := (b : G)) b.2
    exact IsShapeTwoTwoTimesA8.of_mulEquiv e.symm hF.cent_b
  have huA5 : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a (u : G)) := by
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxy (G := G) (a := a) (x := (u : G)) u.2
    exact IsShapeTwoTwoTimesTwoFourA5.of_mulEquiv e.symm hF.cent_z₁
  have hK : derivedOf (Gxy a (b : G)) ≤ Gx a := by
    calc derivedOf (Gxy a (b : G)) ≤ Gxy a (b : G) := derivedOf_le _
      _ ≤ Gx a := by rw [Gxy_eq_inf]; exact inf_le_left
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hbA8
  obtain ⟨b₀, u₀, hb₀mem, hu₀mem, hb₀sq, hu₀sq, hab₀, hab0', hzu₀, hzu0'⟩ :=
    exists_two_A_two_B hA8 hK φ
  have hb₀ne1 : b₀ ≠ 1 := by
    intro h1
    exact ha1 (isConj_one_left.mp (by simpa [h1] using hab₀))
  have hu₀ne1 : u₀ ≠ 1 := by
    intro h1
    exact hz1 (isConj_one_left.mp (by simpa [h1] using hzu₀))
  have hb₀ne_a : b₀ ≠ a := by
    intro h1
    exact ha1 (isConj_one_left.mp (by simpa [h1, haa] using hab0'))
  have hb₀not : b₀ ∉ derivedOf (Gx a) :=
    not_mem_derivedOf_of_isConj hI h hF1 hab₀ hab0' hb₀ne_a
  have hu₀ne_a : u₀ ≠ a := by
    intro h1
    exact hnot (IsConj.symm (h1 ▸ hzu₀))
  have hu₀ord : orderOf u₀ = 2 := orderOf_eq_prime (p := 2) hu₀sq hu₀ne1
  have hu₀not : u₀ ∉ derivedOf (Gx a) := by
    intro hmem
    rcases inv_mem_derivedOf_cases hI h hF1 hmem hu₀ord with h1 | ⟨-, ha, -⟩ | ⟨ha, -⟩
    · exact hu₀ne_a h1
    · exact hnot (ha.trans (IsConj.symm hzu0'))
    · exact hnot (ha.trans (IsConj.symm hzu₀))
  have hb0_bu : (∃ k ∈ Gx a, k * (b : G) * k⁻¹ = b₀) ∨
      (∃ k ∈ Gx a, k * (u : G) * k⁻¹ = b₀) := by
    rcases exists_conj_rep hF hb₀mem hb₀sq hb₀ne1 with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hb₀ne_a
    · exact absurd (mem_derivedOf_of_conj_inner hF (Or.inl h1)) hb₀not
    · exact absurd (mem_derivedOf_of_conj_inner hF (Or.inr h1)) hb₀not
    · exact Or.inl h1
    · exact Or.inr h1
  have hu0_bu : (∃ k ∈ Gx a, k * (b : G) * k⁻¹ = u₀) ∨
      (∃ k ∈ Gx a, k * (u : G) * k⁻¹ = u₀) := by
    rcases exists_conj_rep hF hu₀mem hu₀sq hu₀ne1 with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hu₀ne_a
    · exact absurd (mem_derivedOf_of_conj_inner hF (Or.inl h1)) hu₀not
    · exact absurd (mem_derivedOf_of_conj_inner hF (Or.inr h1)) hu₀not
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hb0_bu with ⟨kb, hkb, hkb0⟩ | ⟨kb, hkb, hkb0⟩
  ·
    rcases hu0_bu with ⟨ku, hku, hku0⟩ | ⟨ku, hku, hku0⟩
    ·
      have hbu : IsConj b₀ u₀ :=
        (IsConj.symm (isConj_iff.mpr ⟨kb, hkb0⟩)).trans (isConj_iff.mpr ⟨ku, hku0⟩)
      exact absurd ((hab₀.trans hbu).trans (IsConj.symm hzu₀)) hnot
    ·
      have hkba : kb * a * kb⁻¹ = a := by
        rw [← mem_Gx.mp hkb, mul_assoc, mul_inv_cancel, mul_one]
      have hkua : ku * a * ku⁻¹ = a := by
        rw [← mem_Gx.mp hku, mul_assoc, mul_inv_cancel, mul_one]
      have hconj_ab : IsConj (a * b) (a * b₀) :=
        isConj_iff.mpr ⟨kb, by
          calc kb * (a * b) * kb⁻¹ = (kb * a * kb⁻¹) * (kb * b * kb⁻¹) := by group
            _ = a * b₀ := by rw [hkba, hkb0]⟩
      have hconj_au : IsConj (a * u) (a * u₀) :=
        isConj_iff.mpr ⟨ku, by
          calc ku * (a * u) * ku⁻¹ = (ku * a * ku⁻¹) * (ku * u * ku⁻¹) := by group
            _ = a * u₀ := by rw [hkua, hku0]⟩
      refine ⟨⟨?_, ?_, ?_, hbA8⟩, ⟨?_, ?_, huA5⟩⟩
      · exact hab₀.trans (IsConj.symm (isConj_iff.mpr ⟨kb, hkb0⟩))
      · exact hab0'.trans (IsConj.symm hconj_ab)
      · intro hbmem
        rw [derivedOf] at hbmem
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hbmem
        exact hF.not_mem_commutator.1 (by rwa [Subtype.ext hxeq] at hx)
      · exact hzu₀.trans (IsConj.symm (isConj_iff.mpr ⟨ku, hku0⟩))
      · exact hzu0'.trans (IsConj.symm hconj_au)
  ·
    rcases hu0_bu with ⟨ku, hku, hku0⟩ | ⟨ku, hku, hku0⟩
    ·
      exact absurd (hzu₀.trans (IsConj.symm (isConj_iff.mpr ⟨ku, hku0⟩)))
        (not_isConj_z_of_isShapeTwoTwoTimesA8 h hbA8)
    ·
      have hbu : IsConj b₀ u₀ :=
        (IsConj.symm (isConj_iff.mpr ⟨kb, hkb0⟩)).trans (isConj_iff.mpr ⟨ku, hku0⟩)
      exact absurd ((hab₀.trans hbu).trans (IsConj.symm hzu₀)) hnot

end CFSG.EvenSporadicStandard.HNRecog.Section3
