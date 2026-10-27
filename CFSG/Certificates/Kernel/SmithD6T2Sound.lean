module

public import Certificates.Data.Kernel.SmithD6.T2Defs
public import CFSG.Certificates.Kernel.PkTreeSound
public import CFSG.GF2Type.SmithTypeE.DMod.Siegel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KC.SmithD6T2

open CFSG.SmithD6 CFSG.KC.PkTree CFSG.KC.Loop CFSG.GF2Type.SmithTypeE.DMod

theorem d6GenPair_ts : ∀ g < 13, qf (d6GenPair g).1 = false ∧ qf (d6GenPair g).2 = false ∧
    bf (d6GenPair g).1 (d6GenPair g).2 = false ∧ (d6GenPair g).1 < 4096 ∧
    (d6GenPair g).2 < 4096 := by
  decide +kernel

theorem d6_bf_zero (y : Nat) : bf 0 y = false := by
  simp [bf]

theorem d6Step_qf {g : Nat} (hg : g < 13) (x : Nat) : qf (d6Step g x) = qf x := by
  obtain ⟨hu, hw, huw, -, -⟩ := d6GenPair_ts g hg
  apply bit_inj
  rw [← q12_dec12, ← q12_dec12, d6Step, ← siegelEquiv_dec12 hu hw huw,
    q12_siegelEquiv (tsPair_dec12 hu hw huw)]

theorem d6Step_bf {g : Nat} (hg : g < 13) (x y : Nat) :
    bf (d6Step g x) (d6Step g y) = bf x y := by
  obtain ⟨hu, hw, huw, -, -⟩ := d6GenPair_ts g hg
  apply bit_inj
  rw [← B12_dec12, ← B12_dec12, d6Step, d6Step, ← siegelEquiv_dec12 hu hw huw,
    ← siegelEquiv_dec12 hu hw huw, B12_siegelEquiv (tsPair_dec12 hu hw huw)]

theorem d6Step_lt {g x : Nat} (hg : g < 13) (hx : x < 4096) : d6Step g x < 4096 := by
  obtain ⟨-, -, -, hu, hw⟩ := d6GenPair_ts g hg
  unfold d6Step sgl
  refine Nat.xor_lt_two_pow (n := 12) (Nat.xor_lt_two_pow (n := 12) hx ?_) ?_
  · split
    · exact hu
    · exact Nat.two_pow_pos 12
  · split
    · exact hw
    · exact Nat.two_pow_pos 12

theorem d6Step_step {g x : Nat} (hg : g < 13) (hx : x < 4096) : d6Step g (d6Step g x) = x := by
  obtain ⟨hu, hw, huw, -, -⟩ := d6GenPair_ts g hg
  apply eq_of_dec12_eq (d6Step_lt hg (d6Step_lt hg hx)) hx
  rw [d6Step, d6Step, ← siegelEquiv_dec12 hu hw huw, ← siegelEquiv_dec12 hu hw huw,
    ← LinearEquiv.mul_apply, siegelEquiv_mul_self (tsPair_dec12 hu hw huw)]
  rfl

theorem d6Step_zero (g : Nat) : d6Step g 0 = 0 := by
  simp [d6Step, sgl, d6_bf_zero]

theorem d6Step_inj {g x y : Nat} (hg : g < 13) (hx : x < 4096) (hy : y < 4096)
    (h : d6Step g x = d6Step g y) : x = y := by
  rw [← d6Step_step hg hx, h, d6Step_step hg hy]

theorem d6Step_ne_zero {g x : Nat} (hg : g < 13) (hx : x < 4096) (h0 : x ≠ 0) :
    d6Step g x ≠ 0 := fun h => h0 (d6Step_inj hg hx (by decide) (h.trans (d6Step_zero g).symm))

theorem d6IsPt_iff {x : Nat} : d6IsPt x = true ↔ x ≠ 0 ∧ qf x = false := by
  simp [d6IsPt]

theorem d6IsRs_iff {x : Nat} :
    d6IsRs x = true ↔ x ≠ 0 ∧ x ≠ 1 ∧ qf x = false ∧ bf 1 x = false := by
  simp [d6IsRs, Bool.and_assoc]

theorem d6Pt_reach {D G : Nat} (h : d6PtTreeOK D G = true) {x : Nat} (hx : x < 4096)
    (h0 : x ≠ 0) (hq : qf x = false) :
    Relation.ReflTransGen (fun p y => ∃ g < 13, d6Step g y = p ∧ y < 4096) 1 x := by
  obtain ⟨r, hr, hrx⟩ := pkTree_sound h (by decide) x hx (d6IsPt_iff.mpr ⟨h0, hq⟩)
  rw [beq_iff_eq] at hr
  subst hr
  refine Relation.ReflTransGen.mono (fun p y hpy => ?_) _ _ hrx
  obtain ⟨g, hg, he, hy, -⟩ := hpy
  exact ⟨g, Nat.blt_eq.mp hg, he, hy⟩

theorem d6Rs_reach {D G : Nat} (h : d6RsTreeOK D G = true) {x : Nat} (hx : x < 4096)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (hq : qf x = false) (hb : bf 1 x = false) :
    Relation.ReflTransGen (fun p y => ∃ g < 13, d6Step g 1 = 1 ∧ d6Step g y = p) 2 x := by
  obtain ⟨r, hr, hrx⟩ := pkTree_sound h (by decide) x hx (d6IsRs_iff.mpr ⟨h0, h1, hq, hb⟩)
  rw [beq_iff_eq] at hr
  subst hr
  refine Relation.ReflTransGen.mono (fun p y hpy => ?_) _ _ hrx
  obtain ⟨g, hg, he, -, -⟩ := hpy
  simp only [d6FixE0, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hg
  exact ⟨g, hg.1, hg.2, he⟩

theorem d6Split_e0 {S : Nat} (h : d6SplitOK S = true) {w : Nat} (hw : w < 4096)
    (hb : bf 1 w = false) (hq : qf w = true) :
    ∃ s < 4096, s ≠ 0 ∧ qf s = false ∧ bf 1 s = false ∧ bf w s = true := by
  have hs := pkAllBelow_spec h (by decide) w hw
  simp only [d6SplitAt, hb, hq, Bool.false_or, Bool.not_true, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at hs
  refine ⟨pkGet S 12 w, ?_, hs.1.1.1, hs.1.1.2, hs.1.2, hs.2⟩
  have : pkGet S 12 w ≤ 4095 := Nat.and_le_right
  omega

theorem d6_split {D G S : Nat} (hP : d6PtTreeOK D G = true) (hS : d6SplitOK S = true) {p : Nat}
    (hp : p < 4096) (hp0 : p ≠ 0) (hpq : qf p = false) {w : Nat} (hw : w < 4096)
    (hpw : bf p w = false) (hwq : qf w = true) :
    ∃ s < 4096, s ≠ 0 ∧ qf s = false ∧ bf p s = false ∧ bf w s = true := by
  have hr := d6Pt_reach hP hp hp0 hpq
  clear hp hp0 hpq
  induction hr generalizing w with
  | refl => exact d6Split_e0 hS hw hpw hwq
  | tail _ hbc ih =>
    obtain ⟨g, hg, rfl, hc⟩ := hbc
    obtain ⟨s, hs, hs0, hsq, hsb, hsw⟩ := ih (d6Step_lt hg hw)
      (by rw [d6Step_bf hg]; exact hpw) (by rw [d6Step_qf hg]; exact hwq)
    refine ⟨d6Step g s, d6Step_lt hg hs, d6Step_ne_zero hg hs hs0, by rw [d6Step_qf hg]; exact hsq,
      ?_, ?_⟩
    · rw [← d6Step_bf hg, d6Step_step hg hs]
      exact hsb
    · rw [← d6Step_bf hg, d6Step_step hg hs]
      exact hsw

@[expose] def d6PairStep (x y : Nat × Nat) : Prop :=
  ∃ g < 13, d6Step g x.1 = y.1 ∧ d6Step g x.2 = y.2

theorem d6_pair_to_e0 {D G : Nat} (hP : d6PtTreeOK D G = true) {a : Nat} (ha : a < 4096)
    (ha0 : a ≠ 0) (haq : qf a = false) {b : Nat} (hb : b < 4096) (hb0 : b ≠ 0) (hab : a ≠ b)
    (hbq : qf b = false) (habf : bf a b = false) :
    ∃ b' < 4096, b' ≠ 0 ∧ b' ≠ 1 ∧ qf b' = false ∧ bf 1 b' = false ∧
      Relation.ReflTransGen d6PairStep (a, b) (1, b') := by
  have hr := d6Pt_reach hP ha ha0 haq
  clear ha ha0 haq
  induction hr generalizing b with
  | refl => exact ⟨b, hb, hb0, hab.symm, hbq, habf, .refl⟩
  | @tail c' c _ hbc ih =>
    obtain ⟨g, hg, rfl, hc⟩ := hbc
    obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := ih (d6Step_lt hg hb) (d6Step_ne_zero hg hb hb0)
      (fun h => hab (d6Step_inj hg hc hb h)) (by rw [d6Step_qf hg]; exact hbq)
      (by rw [d6Step_bf hg]; exact habf)
    exact ⟨b', h1, h2, h3, h4, h5, .head ⟨g, hg, rfl, rfl⟩ h6⟩

theorem d6_pair_at_e0 {D G : Nat} (hR : d6RsTreeOK D G = true) {b : Nat} (hb : b < 4096)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbq : qf b = false) (hbb : bf 1 b = false) :
    Relation.ReflTransGen d6PairStep (1, b) (1, 2) := by
  have hr := d6Rs_reach hR hb hb0 hb1 hbq hbb
  clear hb hb0 hb1 hbq hbb
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih =>
    obtain ⟨g, hg, h1, rfl⟩ := hbc
    exact .head ⟨g, hg, h1, rfl⟩ ih

theorem d6_pair_reach {D G D' G' : Nat} (hP : d6PtTreeOK D G = true)
    (hR : d6RsTreeOK D' G' = true) {a b : Nat} (ha : a < 4096) (hb : b < 4096) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : a ≠ b) (haq : qf a = false) (hbq : qf b = false)
    (habf : bf a b = false) : Relation.ReflTransGen d6PairStep (a, b) (1, 2) := by
  obtain ⟨b', h1, h2, h3, h4, h5, h6⟩ := d6_pair_to_e0 hP ha ha0 haq hb hb0 hab hbq habf
  exact h6.trans (d6_pair_at_e0 hR h1 h2 h3 h4 h5)

theorem d6_pt_count (h : d6PtCnt = 2079) :
    ((Finset.range 4096).filter fun x => x ≠ 0 ∧ qf x = false).card = 2079 := by
  rw [← h, d6PtCnt, pkSumBelow_eq _ (by decide), Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => by
    by_cases hx : d6IsPt x = true
    · rw [if_pos hx, if_pos (d6IsPt_iff.mp hx)]
    · rw [if_neg hx, if_neg (fun h' => hx (d6IsPt_iff.mpr h'))]

theorem d6_perp_count {D G : Nat} (hP : d6PtTreeOK D G = true) (h : d6RsCnt = 1054) {p : Nat}
    (hp : p < 4096) (hp0 : p ≠ 0) (hpq : qf p = false) :
    ((Finset.range 4096).filter fun x => x ≠ 0 ∧ x ≠ p ∧ qf x = false ∧ bf p x = false).card =
      1054 := by
  have hr := d6Pt_reach hP hp hp0 hpq
  clear hp hp0 hpq
  induction hr with
  | refl =>
    rw [← h, d6RsCnt, pkSumBelow_eq _ (by decide), Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases hx : d6IsRs x = true
      · rw [if_pos hx, if_pos (d6IsRs_iff.mp hx)]
      · rw [if_neg hx, if_neg (fun h' => hx (d6IsRs_iff.mpr h'))]
  | @tail c' c _ hbc ih =>
    obtain ⟨g, hg, rfl, hc⟩ := hbc
    rw [← ih]
    refine Finset.card_nbij' (d6Step g) (d6Step g) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨hx4, hx0, hxc, hxq, hxb⟩ := hx
      exact ⟨d6Step_lt hg hx4, d6Step_ne_zero hg hx4 hx0, fun e => hxc (d6Step_inj hg hx4 hc e),
        by rw [d6Step_qf hg]; exact hxq, by rw [d6Step_bf hg]; exact hxb⟩
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy ⊢
      obtain ⟨hy4, hy0, hyc, hyq, hyb⟩ := hy
      refine ⟨d6Step_lt hg hy4, d6Step_ne_zero hg hy4 hy0, fun e => hyc ?_,
        by rw [d6Step_qf hg]; exact hyq, ?_⟩
      · rw [← e, d6Step_step hg hy4]
      · rw [← d6Step_bf hg, d6Step_step hg hy4]
        exact hyb
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
      exact d6Step_step hg hx.1
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy
      exact d6Step_step hg hy.1

end CFSG.KC.SmithD6T2

end
