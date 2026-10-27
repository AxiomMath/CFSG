module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I91
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YDArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10

private theorem chev2L34_index {i : TauCeti.CFSGIndex} (h : chev2L34 i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩ ∧ q.card = 4 := by
  cases i with
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | A r q =>
      cases r with
      | zero => exact absurd h (by simp [chev2L34])
      | succ r =>
        cases r with
        | zero => exact absurd h (by simp [chev2L34])
        | succ r =>
          cases r with
          | zero => exact ⟨q, hv, rfl, h⟩
          | succ r => exact absurd h (by simp [chev2L34])
    | _ => exact absurd h (by simp [chev2L34])
  | _ => exact absurd h (by simp [chev2L34])

private theorem isD4any_index {i : TauCeti.CFSGIndex} (h : isD4any i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩ ∧ q.p = 2 := by
  cases i with
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | D r q =>
      cases r with
      | zero => exact absurd h (by simp [isD4any, onLie])
      | succ r =>
        cases r with
        | zero => exact absurd h (by simp [isD4any, onLie])
        | succ r =>
          cases r with
          | zero => exact absurd h (by simp [isD4any, onLie])
          | succ r =>
            cases r with
            | zero => exact absurd h (by simp [isD4any, onLie])
            | succ r =>
              cases r with
              | zero => exact ⟨q, hv, rfl, h⟩
              | succ r => exact absurd h (by simp [isD4any, onLie])
    | _ => exact absurd h (by simp [isD4any, onLie])
  | _ => exact absurd h (by simp [isD4any, onLie])

private theorem card_four_p_two {q : TauCeti.PrimePower} (hq : q.card = 4) : q.p = 2 := by
  have h1 : q.p ^ q.exponent = 4 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have h2 : q.p ∣ 4 := by
    rw [← h1]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  have h3 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow (show q.p ∣ 2 ^ 2 from h2)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h3

private theorem char_A_two {q : TauCeti.PrimePower} (hq : q.card = 4) :
    (TauCeti.LieTypeIndex.A 2 q).characteristic = 2 := by
  rw [TauCeti.LieTypeIndex.characteristic_A]
  exact card_four_p_two hq

private theorem chev2L34_isChevSimple {S : Type} [Group S] (h : catalogIs S chev2L34) :
    IsChevSimple 2 S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  obtain ⟨q, hv, rfl, hq⟩ := chev2L34_index hi
  exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩, char_A_two hq, ⟨e⟩⟩

private theorem canonLabel_n_eq_one_or_two {lab : CFSG.Open.GLALabel} (h : (canonLabel lab).n = 2) :
    lab.n = 1 ∨ lab.n = 2 := by
  obtain ⟨t, r, n⟩ := lab
  show n = 1 ∨ n = 2
  cases t <;> simp only [canonLabel] at h <;> (try split_ifs at h) <;> (try simp only at h) <;> omega

section L34


private theorem not_d4_of_chev2L34 {S : Type} [Group S] [Finite S]
    (hD : catalogIs S isD4any) (hL : catalogIs S chev2L34) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hD
  obtain ⟨j, hj, ⟨f⟩⟩ := hL
  obtain ⟨q, hv, rfl, hq2⟩ := isD4any_index hi
  obtain ⟨q', hv', rfl, hq'⟩ := chev2L34_index hj
  have hS1 : Nat.card S = orderD 4 q.card :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩ S ⟨e⟩
  have hS2 : Nat.card S = orderA 2 q'.card :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      ⟨TauCeti.LieTypeIndex.A 2 q', hv'⟩ S ⟨f⟩
  have hc : q.card = 2 ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def, hq2]
  have h27 : 27 ∣ orderA 2 q'.card := by
    rw [hS2.symm.trans hS1, hc]
    exact CFSG.LocalAnalysis.GLTheoremA.D4Y.dvd_orderD q.exponent q.exponent_pos
  rw [hq'] at h27
  exact CFSG.LocalAnalysis.GLTheoremA.D4Y.not_dvd27_orderA2 4 (by norm_num) h27

private theorem fieldOn_chev2L34_false {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup G} {y : G} (hc : catalogIs (PSimple p L) chev2L34) (hF : FieldOn p y L) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hc
  obtain ⟨q, hv, rfl, hq⟩ := chev2L34_index hi
  obtain ⟨hcomm, lab, hlab, hraw⟩ := FP.fieldNAt_marking hp hp2 hF hF.2
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hdvd : p ∣ lab.n := hP.2
  have hX : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel (PQuot p L) (· = lab) :=
    ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have h2 : 2 ^ (canonLabel lab).n = KD264Lie.fieldSize (TauCeti.LieTypeIndex.A 2 q) :=
    CanonSubcomp.two_pow_canonLabel_n_of_lie CFSG.StandardType.ggLabelRigidInput_holds hX
      ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩ (char_A_two hq) e
  have hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.A 2 q) = 4 := hq
  have h4 : 2 ^ (canonLabel lab).n = 2 ^ 2 := by
    rw [h2, hfs] <;> norm_num
  have hn : (canonLabel lab).n = 2 := Nat.pow_right_injective (le_refl 2) h4
  rcases canonLabel_n_eq_one_or_two hn with h1 | h1
  · rw [h1] at hdvd
    exact hp.ne_one (Nat.dvd_one.1 hdvd)
  · rw [h1] at hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (by have := hp.two_le; omega)

theorem t158L34NoFG_holds : T158L34NoFG := by
  intro G _ _ p hp hp2 X L y hL hc hy hFG
  have hF : FieldOn p y L := by
    rcases hFG with hF | hG
    · exact hF
    · rcases i91_holds G p hp hp2 X L y hL (chev2L34_isChevSimple hc) hG.1.1 hy hG.1 with
        hF | ⟨hp3, hD | hT⟩
      · exact hF
      · subst hp3
        exact (not_d4_of_chev2L34 hD hc).elim
      · exact (hG.2.1 ⟨hp3, hT⟩).elim
  exact fieldOn_chev2L34_false hp hp2 hc hF

end L34

end CFSG.LocalAnalysis.GLTheoremA.T158

end
