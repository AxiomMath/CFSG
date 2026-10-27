module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.L49b

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

private theorem kd264_pow_two_le_card_of_mul {p m : ℕ} (hp : 2 ≤ p) (hm : 3 ≤ m) {a d : ℕ}
    (ha : a = p ^ m) (hmul : a = p * d) : p ^ 2 ≤ d := by
  have hpow : p * p ^ (m - 1) = p ^ m := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hmul' : p * p ^ (m - 1) ≤ p * d := by rw [hpow, ← ha, hmul]
  have h1 : p ^ (m - 1) ≤ d := Nat.le_of_mul_le_mul_left hmul' (by omega : 0 < p)
  exact (Nat.pow_le_pow_right (by omega : 0 < p) (by omega : 2 ≤ m - 1)).trans h1

private theorem kd264_not_alternating_two_of_lpEpsIdx {p : ℕ} (hp5 : 5 ≤ p)
    {d : TauCeti.LieTypeIndex} (h : lpEpsIdx p d) :
    ¬ ∃ q : TauCeti.PrimePower, d = .A 2 q := by
  rintro ⟨q', hq'⟩
  obtain ⟨Q, hQ | hQ⟩ := h
  · have hEq : TauCeti.LieTypeIndex.A 2 q' = TauCeti.LieTypeIndex.A (p - 1) Q :=
      hq'.symm.trans hQ.1
    injection hEq with h2 _
    omega
  · have hEq : TauCeti.LieTypeIndex.A 2 q' = TauCeti.LieTypeIndex.twistedA (p - 1) Q :=
      hq'.symm.trans hQ.1
    cases hEq

private theorem kd264CoreGoal_of_trialityD4 {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m : ℕ}
    (hI : KD264LieInputs) (h : KD264CoreHyp p d A m 1) (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (hp : p = 3) (hd : ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q)
    (hout : ¬ A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :
    KD264CoreGoal p d A m 1 := by
  obtain ⟨q, hq⟩ := hd
  have hchar : p ≠ d.1.characteristic := h.characteristic_ne
  subst hp
  have hchar3 : d.1.characteristic ≠ 3 := hchar.symm
  have hov2 : ¬ ov2Idx d.1 := fun ho => hX ⟨rfl, ho⟩
  have hbig : isTrialityD4Big d.1 := isTrialityD4Big_of_trialityD4 hq hov2 hchar3
  have hq3 : q.p ≠ 3 := by
    have h := hchar3
    rwa [hq, TauCeti.LieTypeIndex.characteristic_trialityD4] at h
  have hrank :
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) ≤ 3 :=
    (hI.i5Aut d).1 ⟨q, hq, hq3⟩
  have hmle : m ≤ 3 :=
    (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤) (E := A) le_top h.elem
      h.card).trans hrank
  have hm3 : 3 ≤ m := by have := h.four_le; omega
  have hm : m = 3 := le_antisymm hmle hm3
  refine Or.inr ⟨rfl, hbig, hm, rfl, ?_⟩
  exact SetLike.not_le_iff_exists.mp hout

private theorem kd264_false_of_good_element_lie {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m : ℕ}
    (hAmb : KD264Amb p) (hY1 : KD264CaseY1) (hY2 : KD264CaseY2)
    (h : KD264CoreHyp p d A m 1)
    (hNo : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (hTri : p = 3 → (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group)
    {β : MulAut (TauCeti.CFSGIndex.lie d).Group} (hβA : β ∈ A) (hβne : β ≠ 1)
    {J : Subgroup (TauCeti.CFSGIndex.lie d).Group}
    (hJ : GLAPComponent p (fixSubgroup β) J) (hJp : p ∣ Nat.card J)
    {e : TauCeti.ValidLieTypeIndex}
    (hJi : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group))
    (hrel : compRel d.1 e.1)
    (hN4clause : p = 3 →
      (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
      fieldSize d.1 = 8 →
      ∀ x ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, x ^ 3 = 1 → β * x = x * β →
        ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut J,
          centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hx⟩) ∈
            innAutDerived (↥J ⧸ Subgroup.center ↥J))
    (hstab : A ≤ CFSG.GroupActions.subgroupStabAut J)
    (D' : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group))
    (hD'elem : IsElemAbelian p D') (hD'card : Nat.card A = p * Nat.card D')
    (hcase :
      (p = 3 ∧ ov2Idx e.1) ∨
      (p = 3 ∧
        (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) ∧
        ∃ a ∈ A, ∃ ha : a ∈ CFSG.GroupActions.subgroupStabAut J,
          centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨a, ha⟩) ∉
            innAutDerived (↥J ⧸ Subgroup.center ↥J)) ∨
      (p = 5 ∧ (e.1 = .suzuki 2 ∨ e.1 = .tits)) ∨
      (lpEpsIdx p e.1 ∧ Nat.card A = p ^ 3)) : False := by
  rcases hcase with ⟨hp3, hov2e⟩ | ⟨hp3, he8, hex⟩ | ⟨hp5, hsuz⟩ | ⟨hlpe, hAcard⟩
  · have hd3 : d.1.characteristic ≠ 3 := by
      rw [← hp3]
      exact h.characteristic_ne.symm
    exact hX ⟨hp3, ov2Idx_of_compRel hrel hov2e hd3⟩
  · subst hp3
    have hfe : fieldSize e.1 = 8 := by
      obtain ⟨q, hq, hqc⟩ := he8
      rcases hq with hq | hq
      · rw [hq]; simpa [fieldSize] using hqc
      · rw [hq]; simpa [fieldSize] using hqc
    have hfd : fieldSize d.1 = 2 ∨ fieldSize d.1 = 8 := fieldSize_of_compRel_of_eight hrel hfe
    have hfd8 : fieldSize d.1 = 8 := by
      rcases hfd with h2 | h8
      · exact absurd ⟨rfl, h2⟩ hX
      · exact h8
    have hov2 : ¬ ov2Idx d.1 := fun ho => hX ⟨rfl, ho⟩
    obtain ⟨F, hFA, hFc, hFg⟩ :=
      hY2 d A m h hov2 (fun hd => hTri rfl hd) β hβA J hJ e hJi hrel he8
        (hN4clause rfl he8 hfd8) hstab ⟨D', hD'elem, hD'card⟩ hex
    exact hNo F hFA (by rw [hFc]; norm_num) hFg
  · exact h.notK2 (hp5.symm ▸ k2Lie_five_of_compRel d hrel hsuz)
  · have hm : m = 3 := by
      have hpow : p ^ m = p ^ 3 := by rw [← h.card, hAcard]
      exact Nat.pow_right_injective h.prime.two_le hpow
    have hple : p - 1 ≤ 3 := by
      have := h.mrj β hβA hβne J hJ e hJi hlpe
      rwa [hm] at this
    have hp3 : p = 3 := by
      have hp2 : 2 ≤ p := h.prime.two_le
      have hp4 : p ≤ 4 := by omega
      have hne2 : p ≠ 2 := h.odd
      have hne4 : p ≠ 4 := by
        rintro rfl
        exact absurd h.prime (by norm_num)
      omega
    subst hp3
    subst hm
    have hov2 : ¬ ov2Idx d.1 := fun ho => hX ⟨rfl, ho⟩
    obtain ⟨F, hFA, hFc, hFg⟩ := hY1 d A h hov2 (fun hd => hTri rfl hd)
    exact hNo F hFA (by rw [hFc]; norm_num) hFg

private theorem kd264_false_of_good_element_cases {p : ℕ} (hBS : KD264BS p) (hAmb : KD264Amb p)
    (hY1 : KD264CaseY1) (hY2 : KD264CaseY2)
    {d : TauCeti.ValidLieTypeIndex} [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m : ℕ}
    (h : KD264CoreHyp p d A m 1)
    (hNo : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (hTri : p = 3 → (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group)
    (hA3 : p ^ 3 ≤ Nat.card A)
    {β : MulAut (TauCeti.CFSGIndex.lie d).Group} (hβA : β ∈ A) (hβne : β ≠ 1)
    {J : Subgroup (TauCeti.CFSGIndex.lie d).Group}
    (hJ : GLAPComponent p (fixSubgroup β) J) (hJp : p ∣ Nat.card J)
    (i : TauCeti.CFSGIndex) (hJi : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group))
    (hrel : compRelC d.1 i)
    (h3 : p = 3 → ∀ e : TauCeti.ValidLieTypeIndex, i = .lie e →
      (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
      fieldSize d.1 = 8 →
      ∀ x ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, x ^ 3 = 1 → β * x = x * β →
        ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut J,
          centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hx⟩) ∈
            innAutDerived (↥J ⧸ Subgroup.center ↥J)) : False := by
  cases i with
  | lie e =>
    obtain ⟨hstab, ⟨D', hD'elem, hD'card⟩, hExc⟩ :=
      hBS (TauCeti.CFSGIndex.lie d).Group A h.elem hA3 hNo β hβA hβne J hJ hJp (.lie e) hJi
    have hchar : p ≠ d.1.characteristic := h.characteristic_ne
    rcases characteristic_ne_of_compRelC h.odd hrel hchar hX with hne | ⟨hp7, q, heq, hqc⟩
    · exact kd264_false_of_good_element_lie hAmb hY1 hY2 h hNo hX hTri hβA hβne hJ hJp hJi
        hrel (fun hp3 he8 hfd => h3 hp3 e rfl he8 hfd) hstab D' hD'elem hD'card (hExc e rfl hne)
    · have hD'2 : p ^ 2 ≤ Nat.card D' :=
        kd264_pow_two_le_card_of_mul h.prime.two_le (by have := h.four_le; omega) h.card hD'card
      have hle : Nat.card D' ≤ p := hAmb.2 hp7 e ⟨q, heq, hqc⟩ D' hD'elem
      exact not_le.2 (lt_self_pow₀ h.prime.one_lt one_lt_two) (hD'2.trans hle)
  | alternating n hn =>
    obtain ⟨hstab, ⟨D', hD'elem, hD'card⟩, -⟩ :=
      hBS (TauCeti.CFSGIndex.lie d).Group A h.elem hA3 hNo β hβA hβne J hJ hJp
        (.alternating n hn) hJi
    have hD'2 : p ^ 2 ≤ Nat.card D' :=
      kd264_pow_two_le_card_of_mul h.prime.two_le (by have := h.four_le; omega) h.card hD'card
    obtain ⟨hlist, hcond⟩ := compRelC_alternating hrel
    by_cases h68 : p = 3 ∧ (n = 6 ∨ n = 8)
    · obtain ⟨hp3, hn68⟩ := h68
      rcases hcond hn68 with hf2 | hch
      · exact hX ⟨hp3, hf2⟩
      · have hchar3 : d.1.characteristic ≠ 3 := by
          rw [← hp3]
          exact h.characteristic_ne.symm
        exact hchar3 hch
    · have hle : Nat.card D' ≤ p := hAmb.1 n hn hlist h68 D' hD'elem
      exact not_le.2 (lt_self_pow₀ h.prime.one_lt one_lt_two) (hD'2.trans hle)
  | sporadic s => exfalso; simpa [compRelC] using hrel
  | cyclic a b => exfalso; simpa [compRelC] using hrel

private theorem kd264_false_of_good_element (hI : KD264LieInputs) {p : ℕ}
    (hPL : KD264PL p) (hBS : KD264BS p) (hAmb : KD264Amb p)
    (hY1 : KD264CaseY1) (hY2 : KD264CaseY2)
    {d : TauCeti.ValidLieTypeIndex} [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m : ℕ}
    (h : KD264CoreHyp p d A m 1)
    (hNo : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hX : ¬ (p = 3 ∧ ov2Idx d.1))
    (hTri : p = 3 → (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group)
    (hA3 : p ^ 3 ≤ Nat.card A)
    {β : MulAut (TauCeti.CFSGIndex.lie d).Group}
    (hβA : β ∈ A) (hβne : β ≠ 1)
    (hβinn : β ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group)
    (P : Subgroup (TauCeti.CFSGIndex.lie d).Group)
    (hPF : P ≤ fixSubgroup β) (hPperf : ⁅P, P⁆ = P) (hPp : p ∣ Nat.card P) : False := by
  have hchar : p ≠ d.1.characteristic := h.characteristic_ne
  obtain ⟨J, hJ, hJp⟩ :=
    hPL d hchar β (h.elem.2 β hβA) hβne P hPF hPperf hPp
  obtain ⟨i, hJi, hrel, h3⟩ :=
    hI.compIdx d p h.prime h.odd hchar β hβinn (h.elem.2 β hβA) hβne J hJ
  exact kd264_false_of_good_element_cases hBS hAmb hY1 hY2 h hNo hX hTri hA3 hβA hβne hJ hJp
    i hJi hrel h3

private theorem kd264_false_of_selfCentralizing_cases {p : ℕ} (hBS : KD264BS p)
    {d : TauCeti.ValidLieTypeIndex} [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m : ℕ}
    (h : KD264CoreHyp p d A m 1)
    (hNo : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hA3 : p ^ 3 ≤ Nat.card A)
    {b : MulAut (TauCeti.CFSGIndex.lie d).Group} (hbA : b ∈ A) (hbne : b ≠ 1)
    {J : Subgroup (TauCeti.CFSGIndex.lie d).Group}
    (hJ : GLAPComponent p (fixSubgroup b) J) (hJp : p ∣ Nat.card J)
    (i : TauCeti.CFSGIndex) (hJi : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group))
    (hrel : subRelC p d.1 i) (hlp : lpEpsIdx p d.1) (hp5 : 5 ≤ p) : False := by
  cases i with
  | lie e =>
    obtain ⟨-, ⟨D', hD'elem, hD'card⟩, hExc⟩ :=
      hBS (TauCeti.CFSGIndex.lie d).Group A h.elem hA3 hNo b hbA hbne J hJ hJp (.lie e) hJi
    have hchar : p ≠ d.1.characteristic := h.characteristic_ne
    rcases characteristic_ne_of_subRel h.prime h.odd hrel hchar with
      hne | ⟨hp7, ⟨q, heq, hqc⟩, q', hdq⟩ | ⟨hp3, -, -⟩
    · rcases hExc e rfl hne with ⟨hp3, -⟩ | ⟨hp3, -⟩ | ⟨hp5', hsuz⟩ | ⟨hlpe, hAcard⟩
      · omega
      · omega
      · exact absurd hsuz (not_suzuki_tits_of_subRel hrel hlp)
      · have hm : m = 3 := by
          have hpow : p ^ m = p ^ 3 := by rw [← h.card, hAcard]
          exact Nat.pow_right_injective h.prime.two_le hpow
        have hple : p - 1 ≤ 3 := by
          have := h.mrj b hbA hbne J hJ e hJi hlpe
          rwa [hm] at this
        omega
    · exact absurd ⟨q', hdq⟩ (kd264_not_alternating_two_of_lpEpsIdx hp5 hlp)
    · omega
  | alternating n hn => exact not_subRelC_alternating_of_lpEpsIdx hp5 hlp hrel
  | sporadic s => exfalso; simpa [subRelC] using hrel
  | cyclic a b => exfalso; simpa [subRelC] using hrel

private theorem kd264_false_of_selfCentralizing {p : ℕ} (hI : KD264LieInputs) (hBS : KD264BS p)
    {d : TauCeti.ValidLieTypeIndex} [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m : ℕ}
    (h : KD264CoreHyp p d A m 1)
    (hNo : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (D : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group))
    (hDle : D ≤ A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group)
    (hDcard : Nat.card D = p ^ 2) (hlp : lpEpsIdx p d.1)
    (hDeq : innAutDerived (TauCeti.CFSGIndex.lie d).Group ⊓
      Subgroup.centralizer (D : Set (MulAut (TauCeti.CFSGIndex.lie d).Group)) = D) : False := by
  have hchar : p ≠ d.1.characteristic := h.characteristic_ne
  have hA0eq : A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group = D := by
    refine le_antisymm ?_ hDle
    intro x hx
    have hx' : x ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group ⊓
        Subgroup.centralizer (D : Set (MulAut (TauCeti.CFSGIndex.lie d).Group)) :=
      Subgroup.mem_inf.mpr
        ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun y hy => h.elem.comm (hDle hy).1 hx.1⟩
    rwa [hDeq] at hx'
  have hm : m = 3 := by
    have hN1 := hI.outCyc d p h.prime h.odd hchar A h.elem
    have hle : p ^ m ≤ p ^ 3 := by
      calc p ^ m = Nat.card A := h.card.symm
        _ ≤ p * Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) := hN1
        _ = p * Nat.card D := by rw [hA0eq]
        _ = p * p ^ 2 := by rw [hDcard]
        _ = p ^ 3 := by ring
    exact le_antisymm ((Nat.pow_le_pow_iff_right h.prime.one_lt).1 hle)
      (by have := h.four_le; omega)
  have hAle : ¬ A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group := by
    intro hle
    have hAeq : A = D := by
      rw [← hA0eq]
      exact (inf_eq_left.mpr hle).symm
    have hpow : p ^ m = p ^ 2 := by rw [← h.card, hAeq, hDcard]
    have h32 : m = 2 := Nat.pow_right_injective h.prime.two_le hpow
    omega
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.mp hAle
  have hbne : b ≠ 1 := by
    rintro rfl
    exact hbout (Subgroup.one_mem _)
  have hA3 : p ^ 3 ≤ Nat.card A := by rw [h.card, hm]
  by_cases hp3 : p = 3
  · subst hp3
    rcases k3Lie_or_k2Lie_three_of_lpEpsIdx d hlp with h3 | h2
    · exact h.notK3 ⟨rfl, h3⟩
    · exact h.notK2 h2
  · have hp5 : 5 ≤ p := h.prime.five_le_of_ne_two_of_ne_three h.odd hp3
    have hexc : ¬ (p = 3 ∧
        ((∃ q : TauCeti.PrimePower,
            (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
          ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q)) := by
      rintro ⟨h3, -⟩
      omega
    have hsuz : ¬ (p = 5 ∧ d.1 = .suzuki 2) := by
      rintro ⟨h5, hd⟩
      apply h.notK2
      rw [hd, h5]
      exact ⟨rfl, rfl⟩
    obtain ⟨J, hJ, hJp, i, hJi, hrel⟩ :=
      hI.outerIdx d p h.prime h.odd hchar h.dvd hexc hsuz b (h.elem.2 b hbA) hbout
    exact kd264_false_of_selfCentralizing_cases hBS h hNo hA3 hbA hbne hJ hJp i hJi hrel hlp hp5

theorem kd264CoreGoal_of_c_eq_one (hI : KD264LieInputs) {p : ℕ} (hPL : KD264PL p)
    (hBS : KD264BS p) (hAmb : KD264Amb p) (hY1 : KD264CaseY1) (hY2 : KD264CaseY2)
    (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ)
    (h : KD264CoreHyp p d A m 1) (hX : ¬ (p = 3 ∧ ov2Idx d.1)) : KD264CoreGoal p d A m 1 := by
  classical
  have hchar : p ≠ d.1.characteristic := h.characteristic_ne
  by_cases hC : p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧
      ¬ A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group
  · obtain ⟨hp3, q, hq, hout⟩ := hC
    exact kd264CoreGoal_of_trialityD4 hI h hX hp3 ⟨q, hq⟩ hout
  have hTri : p = 3 → (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group := by
    intro hp3 hd
    by_contra hout
    obtain ⟨q, hq⟩ := hd
    exact hC ⟨hp3, q, hq, hout⟩
  by_cases hG : ∃ F ≤ A, Nat.card F = p ^ 2 ∧ IsGood p F
  · obtain ⟨F, hFA, hFcard, hFgood⟩ := hG
    refine Or.inl ⟨F, hFA, hFgood, ?_⟩
    rw [hFcard, pow_one, ← pow_succ]
  · have hNo : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F := by
      intro F hFA hFcard hFgood
      exact hG ⟨F, hFA, hFcard, hFgood⟩
    have hm3 : 3 ≤ m := by have := h.four_le; omega
    have hA3 : p ^ 3 ≤ Nat.card A := by
      rw [h.card]
      exact Nat.pow_le_pow_right h.prime.pos hm3
    have hN1 := hI.outCyc d p h.prime h.odd hchar A h.elem
    have hA0ge : p ^ 2 ≤ Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) := by
      have hN1' : p ^ m ≤
          p * Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) := by
        rw [← h.card]
        exact hN1
      have hpow : p ^ m = p * p ^ (m - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
      have h1 : p ^ (m - 1) ≤
          Nat.card ↥(A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :=
        Nat.le_of_mul_le_mul_left (by rw [← hpow]; exact hN1') h.prime.pos
      exact (Nat.pow_le_pow_right h.prime.pos (by omega : 2 ≤ m - 1)).trans h1
    obtain ⟨D, hDle, hDcard⟩ :=
      exists_le_card_eq_pow h.prime (h.elem.mono inf_le_left).isPGroup hA0ge
    have hDel : IsElemAbelian p D := h.elem.mono (hDle.trans inf_le_left)
    have hNotTits : ¬ (p = 5 ∧ d.1 = .tits) := by
      rintro ⟨hp5, ht⟩
      apply h.notK2
      rw [hp5, ht]
      exact Or.inr rfl
    rcases hI.innGood d p h.prime h.odd hchar hX hNotTits D hDel hDcard
        (hDle.trans inf_le_right) with
      ⟨β, hβD, hβne, P, hPF, hPperf, hPp⟩ | ⟨hlp, hDeq⟩
    ·
      have hβA0 : β ∈ A ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group := hDle hβD
      exact (kd264_false_of_good_element hI hPL hBS hAmb hY1 hY2 h hNo hX hTri hA3
        hβA0.1 hβne hβA0.2 P hPF hPperf hPp).elim
    ·
      exact (kd264_false_of_selfCentralizing hI hBS h hNo D hDle hDcard hlp hDeq).elim

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
