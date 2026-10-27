module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreTools
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.GLTheoremA.S4.L49b

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem kd264CoreGoal_of_isGood_of_nine_le (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ)
    {F : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)}
    (hFA : F ≤ A) (hgood : IsGood 3 F) (h1c : 1 ≤ c) (h9 : 9 ≤ Nat.card F) :
    KD264CoreGoal 3 d A m c := by
  refine Or.inl ⟨F, hFA, hgood, ?_⟩
  have h3c : 3 ≤ 3 ^ c := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ c := Nat.pow_le_pow_right (by norm_num) h1c
  calc 3 ^ 3 = 9 * 3 := by norm_num
    _ ≤ Nat.card F * 3 ^ c := Nat.mul_le_mul h9 h3c

private theorem kd264CoreGoal_of_isGood_of_three_le (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    {F : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)}
    (hFA : F ≤ A) (hgood : IsGood 3 F) (h3 : 3 ≤ Nat.card F) :
    KD264CoreGoal 3 d A m 2 := by
  refine Or.inl ⟨F, hFA, hgood, ?_⟩
  calc 3 ^ 3 = 3 * 3 ^ 2 := by norm_num
    _ ≤ Nat.card F * 3 ^ 2 := Nat.mul_le_mul h3 le_rfl

private theorem kd264CoreGoal_of_isGood_zpowers (p : ℕ) (hp : p.Prime)
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    {β : MulAut (TauCeti.CFSGIndex.lie d).Group}
    (hβA : β ∈ A) (hβ : β ^ p = 1) (hβ1 : β ≠ 1)
    (hgood : IsGood p (Subgroup.zpowers β)) : KD264CoreGoal p d A m 2 := by
  refine Or.inl ⟨Subgroup.zpowers β, Subgroup.zpowers_le.2 hβA, hgood, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hβ hβ1]
  have h : p ^ 3 = p * p ^ 2 := by ring
  rw [h]

private theorem kd264CoreGoal_of_caseX_twistedA (hI : KD264LieInputs)
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ)
    (h : KD264CoreHyp 3 d A m c) (hov2 : ov2Idx d.1)
    (hU : ∃ (n : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA n q ∧ 3 ∣ n + 1) :
    KD264CoreGoal 3 d A m c := by
  obtain ⟨n, q, hd, h3⟩ := hU
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize, hd] using hov2
  have hnotK3 : ¬ k3Lie d.1 := fun hk3 => h.notK3 ⟨rfl, hk3⟩
  have h8 : 8 ≤ n := eight_le_of_twistedA_two d hd hq h3 h.notK2
  have hlow : n - 1 ≤ m := by
    refine h.low (n - 1) ?_
    rw [hd]
    refine ⟨?_, rfl⟩
    omega
  have hrank : CFSG.Open.pRank 3 A = m := h.pRank_eq
  have hle : n - 1 ≤ CFSG.Open.pRank 3 A := by rw [hrank]; exact hlow
  obtain ⟨F, hFA, hFel, hFrank, hFgood⟩ :=
    hI.xUnRow d n q h.notChev h.notK2 hnotK3 hd hq h3 h8 A h.elem hle
  have h9 : 9 ≤ Nat.card F := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hFel]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 F := Nat.pow_le_pow_right (by norm_num) hFrank
  exact kd264CoreGoal_of_isGood_of_nine_le d A m c hFA hFgood h.one_le_c h9

private theorem kd264CoreGoal_of_caseX_twistedE6 (hI : KD264LieInputs)
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ)
    (h : KD264CoreHyp 3 d A m c) (hov2 : ov2Idx d.1)
    (hE : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) :
    KD264CoreGoal 3 d A m c := by
  obtain ⟨q, hd⟩ := hE
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize, hd] using hov2
  have hnotK3 : ¬ k3Lie d.1 := fun hk3 => h.notK3 ⟨rfl, hk3⟩
  have hlow : 5 ≤ m := by
    refine h.low 5 ?_
    rw [hd]
    refine ⟨rfl, ?_, rfl⟩
    omega
  have hrank : CFSG.Open.pRank 3 A = m := h.pRank_eq
  have hle : 5 ≤ CFSG.Open.pRank 3 A := by rw [hrank]; exact hlow
  obtain ⟨F, hFA, hFel, hFrank, hFgood⟩ :=
    hI.x2E6Row d q h.notChev h.notK2 hnotK3 hd hq A h.elem hle
  have hcard : Nat.card F = 9 := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hFel, hFrank]
    norm_num
  exact kd264CoreGoal_of_isGood_of_nine_le d A m c hFA hFgood h.one_le_c (by omega)

private theorem kd264CoreGoal_of_caseX_other (hI : KD264LieInputs)
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ)
    (h : KD264CoreHyp 3 d A m c) (hov2 : ov2Idx d.1)
    (hU : ¬ ∃ (n : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA n q ∧ 3 ∣ n + 1)
    (hE : ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) :
    KD264CoreGoal 3 d A m c := by
  have hnotK3 : ¬ k3Lie d.1 := fun hk3 => h.notK3 ⟨rfl, hk3⟩
  have hmin : ¬ multIdx 3 d.1 := not_multIdx_three_of_ov2Idx hov2 hU hE
  have hrank : CFSG.Open.pRank 3 A = m := h.pRank_eq
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤
      CFSG.Open.pRank 3 A := by
    rw [hrank]
    exact (h.noMult hmin).1
  obtain ⟨F, hFA, hFel, hFrank, hFgood⟩ :=
    hI.x1Row d h.notChev h.notK2 hnotK3 hov2 hU hE A h.elem hle
  have hc1 : 1 ≤ c := h.one_le_c
  have hc2 : c ≤ 2 := h.c_le_two
  interval_cases c
  · have hm3 : 2 ≤ m - 1 := by have := h.four_le; omega
    have hmin2 : 2 ≤ Nat.min 2 (CFSG.Open.pRank 3 A - 1) := by
      rw [hrank]
      exact le_min le_rfl hm3
    have h2 : 2 ≤ CFSG.Open.pRank 3 F := le_trans hmin2 hFrank
    have h9 : 9 ≤ Nat.card F := by
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hFel]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ CFSG.Open.pRank 3 F := Nat.pow_le_pow_right (by norm_num) h2
    exact kd264CoreGoal_of_isGood_of_nine_le d A m 1 hFA hFgood le_rfl h9
  · have hm2 : 1 ≤ m - 1 := by have := h.four_le; omega
    have hmin1 : 1 ≤ Nat.min 2 (CFSG.Open.pRank 3 A - 1) := by
      rw [hrank]
      exact le_min (by norm_num) hm2
    have h1 : 1 ≤ CFSG.Open.pRank 3 F := le_trans hmin1 hFrank
    have h3 : 3 ≤ Nat.card F := by
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hFel]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ CFSG.Open.pRank 3 F := Nat.pow_le_pow_right (by norm_num) h1
    exact kd264CoreGoal_of_isGood_of_three_le d A m hFA hFgood h3

theorem kd264CoreGoal_of_caseX (hI : KD264LieInputs) {p : ℕ}
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ)
    (h : KD264CoreHyp p d A m c) (hX : p = 3 ∧ ov2Idx d.1) : KD264CoreGoal p d A m c := by
  obtain ⟨rfl, hov2⟩ := hX
  by_cases hU : ∃ (n : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA n q ∧ 3 ∣ n + 1
  · exact kd264CoreGoal_of_caseX_twistedA hI d A m c h hov2 hU
  · by_cases hE : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q
    · exact kd264CoreGoal_of_caseX_twistedE6 hI d A m c h hov2 hE
    · exact kd264CoreGoal_of_caseX_other hI d A m c h hov2 hU hE

private theorem kd264CoreGoal_of_c_two_not_inner_triality (hI : KD264LieInputs) {p : ℕ}
    (hPL : KD264PL p) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    (h : KD264CoreHyp p d A m 2) (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (htri : p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) :
    KD264CoreGoal p d A m 2 := by
  obtain ⟨hp3, q, hd⟩ := htri
  subst hp3
  have h3char : 3 ≠ d.1.characteristic := h.characteristic_ne
  have hqne : q.card ≠ 2 := by
    intro hq2
    refine hX ⟨rfl, ?_⟩
    rw [hd]
    simpa [ov2Idx, fieldSize] using hq2
  have hq2 : 2 < q.card := by
    have h2 : 2 ≤ q.card := by
      have := two_le_fieldSize d.1
      rw [hd] at this
      simpa [fieldSize] using this
    omega
  have hm2 : 2 ≤ m := by have := h.four_le; omega
  have hcardA : 9 ≤ Nat.card A := by
    rw [h.card]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hout := hI.outCyc d 3 h.prime h.odd h3char A h.elem
  have hN : 3 ≤ Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) := by
    have h33 : 3 * 3 ≤
        3 * Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) := by
      calc 3 * 3 = 9 := by norm_num
        _ ≤ Nat.card A := hcardA
        _ ≤ 3 * Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) := hout
    exact Nat.le_of_mul_le_mul_left h33 (by norm_num)
  have hnt : Nontrivial ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hxAI, hx1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one _).mp hnt
  have hx3 : x ^ 3 = 1 := h.elem.2 x hxAI.1
  obtain ⟨P, hPF, hPP, hPdvd⟩ :=
    hI.triInnGood d ⟨q, hd, hq2⟩ h3char x hxAI.2 hx3 hx1
  obtain ⟨J, hJ, -⟩ := hPL d h3char x hx3 hx1 P hPF hPP hPdvd
  exact kd264CoreGoal_of_isGood_zpowers 3 h.prime d A m hxAI.1 hx3 hx1
    (isGood_zpowers_of_glaPComponent h.prime hJ)

private theorem kd264CoreGoal_of_c_two_not_inner (hI : KD264LieInputs) {p : ℕ}
    (hPL : KD264PL p) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    (h : KD264CoreHyp p d A m 2) (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (hA : ¬ A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :
    KD264CoreGoal p d A m 2 := by
  have hex : ∃ a ∈ A, a ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group := by
    by_contra hcon
    exact hA fun x hx => by
      by_contra hxout
      exact hcon ⟨x, hx, hxout⟩
  obtain ⟨a, haA, haout⟩ := hex
  have hap : a ^ p = 1 := h.elem.2 a haA
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact haout (Subgroup.one_mem _)
  by_cases htri : p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q
  · exact kd264CoreGoal_of_c_two_not_inner_triality hI hPL d A m h hX htri
  · by_cases h8 : p = 3 ∧ ∃ q : TauCeti.PrimePower,
        (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8
    · obtain ⟨hp3, q, hq, hq8⟩ := h8
      subst hp3
      rcases hq with hq | hq
      · exact absurd (k2Lie_three_of_card_eight (d := d.1) (Or.inl hq) hq8) h.notK2
      · exact absurd (k2Lie_three_of_card_eight (d := d.1) (Or.inr hq) hq8) h.notK2
    · by_cases h5 : p = 5 ∧ d.1 = .suzuki 2
      · obtain ⟨hp5, hd⟩ := h5
        subst hp5
        have hK2 := h.notK2
        rw [hd] at hK2
        exact absurd (show k2Lie 5 (.suzuki 2) from ⟨rfl, rfl⟩) hK2
      · have hexc : ¬ (p = 3 ∧
            ((∃ q : TauCeti.PrimePower,
                (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
              ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q)) := by
          rintro ⟨hp3, h1 | h2⟩
          · exact h8 ⟨hp3, h1⟩
          · exact htri ⟨hp3, h2⟩
        obtain ⟨J, hJ, -, -⟩ :=
          hI.outerIdx d p h.prime h.odd h.characteristic_ne h.dvd
            hexc h5 a hap haout
        exact kd264CoreGoal_of_isGood_zpowers p h.prime d A m haA hap ha1
          (isGood_zpowers_of_glaPComponent h.prime hJ)

private theorem kd264CoreGoal_of_c_two_inner (hI : KD264LieInputs) {p : ℕ}
    (hPL : KD264PL p) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    (h : KD264CoreHyp p d A m 2) (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (hA : A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :
    KD264CoreGoal p d A m 2 := by
  have hm2 : 2 ≤ m := by have := h.four_le; omega
  have hcard : p ^ 2 ≤ Nat.card A := by
    rw [h.card]
    exact Nat.pow_le_pow_right h.prime.pos hm2
  obtain ⟨D, hDA, hDcard⟩ := exists_le_card_eq_pow h.prime h.elem.isPGroup hcard
  have hDel : IsElemAbelian p D := h.elem.mono hDA
  have hDinn : D ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group := hDA.trans hA
  have hNotTits : ¬ (p = 5 ∧ d.1 = .tits) := by
    rintro ⟨hp5, ht⟩
    apply h.notK2
    rw [hp5, ht]
    exact Or.inr rfl
  rcases hI.innGood d p h.prime h.odd h.characteristic_ne hX hNotTits
      D hDel hDcard hDinn with
    ⟨β, hβD, hβ1, P, hPF, hPP, hPdvd⟩ | ⟨hlp, hcent⟩
  · have hβp : β ^ p = 1 := h.elem.2 β (hDA hβD)
    obtain ⟨J, hJ, -⟩ :=
      hPL d h.characteristic_ne β hβp hβ1 P hPF hPP hPdvd
    exact kd264CoreGoal_of_isGood_zpowers p h.prime d A m (hDA hβD) hβp hβ1
      (isGood_zpowers_of_glaPComponent h.prime hJ)
  · have hA_le_D : A ≤ D := by
      intro a ha
      rw [← hcent]
      exact ⟨hA ha, Subgroup.mem_centralizer_iff.2 fun d hd => h.elem.comm (hDA hd) ha⟩
    have hAD : A = D := le_antisymm hA_le_D hDA
    have hm_eq : m = 2 := by
      have hpow : p ^ m = p ^ 2 := by rw [← h.card, hAD, hDcard]
      exact Nat.pow_right_injective h.prime.two_le hpow
    have hp4 : p ≤ 4 := by
      have hle : p - 2 ≤ m := h.low (p - 2) (i5LowBound_of_lpEpsIdx hlp)
      omega
    have hp3 : p = 3 := by
      have hp2 : 2 ≤ p := h.prime.two_le
      interval_cases p
      · exact absurd rfl h.odd
      · rfl
      · exact absurd h.prime (by norm_num)
    subst hp3
    rcases k3Lie_or_k2Lie_three_of_lpEpsIdx d hlp with h3 | h2
    · exact absurd ⟨rfl, h3⟩ h.notK3
    · exact absurd h2 h.notK2

theorem kd264CoreGoal_of_c_eq_two (hI : KD264LieInputs) {p : ℕ} (hPL : KD264PL p)
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    (h : KD264CoreHyp p d A m 2) (hX : ¬ (p = 3 ∧ ov2Idx d.1)) :
    KD264CoreGoal p d A m 2 := by
  by_cases hA : A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group
  · exact kd264CoreGoal_of_c_two_inner hI hPL d A m h hX hA
  · exact kd264CoreGoal_of_c_two_not_inner hI hPL d A m h hX hA

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
