module

public import CFSG.Certificates.Kernel.Misc.O62SoundRank
public import CFSG.Certificates.Kernel.Misc.O62SoundWc

public section

namespace CFSG.KC.Misc.O62

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Check CFSG.LargeExtraspecial.O62.Code

@[expose] def checkSylowG (minus : Bool) (Tw : List (List ℕ)) : Bool :=
  let cs := Tw.map wordC
  Tw.all (fun w => w.all (qB minus)) && Tw.contains [] &&
    cs.all (fun x => cs.all fun y => cs.contains (mul x y)) &&
    Tw.all (fun w => cs.contains (wordC w.reverse)) && decide cs.Nodup &&
    Tw.length == 128 && (Tw.filter fun w => w.length % 2 == 0).length == 64

@[expose] def checkRankG (Tw : List (List ℕ)) : Bool :=
  let cs := (Tw.map wordC).filter isInv
  cs.all fun x₁ =>
    let s₁ := spanC [x₁]
    let c₁ := cs.filter fun y => comm x₁ y && !s₁.contains y
    c₁.all fun x₂ =>
      let s₂ := s₁ ++ s₁.map fun c => mul c x₂
      let c₂ := c₁.filter fun y => comm x₂ y && !s₂.contains y
      c₂.all fun x₃ =>
        let s₃ := s₂ ++ s₂.map fun c => mul c x₃
        let c₃ := c₂.filter fun y => comm x₃ y && !s₃.contains y
        c₃.all fun x₄ =>
          let s₄ := s₃ ++ s₃.map fun c => mul c x₄
          (c₃.filter fun y => comm x₄ y && !s₄.contains y).isEmpty

@[expose] def wcTripleG (minus : Bool) (C : List (ℕ × List ℕ)) (a b c : List ℕ) (x y z : ℕ) :
    Bool :=
  if comm x y && comm x z && comm y z && !(spanC [x]).contains y &&
      !(spanC [y, x]).contains z then
    let E := spanC [z, y, x]
    let ev := a.length % 2 == 0 && b.length % 2 == 0 && c.length % 2 == 0
    decide E.Nodup && ((!minus && ev) || C.any fun p =>
      p.1 == keyOf E && p.2.all (qB minus) && (!ev || p.2.length % 2 == 0) && certOK E p.2)
  else true

@[expose] def checkWCG (minus : Bool) (Tw : List (List ℕ)) (C : List (ℕ × List ℕ)) : Bool :=
  let ps := (Tw.filter fun w => isInv (wordC w)).map fun w => (w, wordC w)
  ps.all fun p => ps.all fun q =>
    if comm p.2 q.2 && !(spanC [p.2]).contains q.2 then
      ps.all fun r => wcTripleG minus C p.1 q.1 r.1 p.2 q.2 r.2
    else true

theorem checkSylow_eq (minus : Bool) : checkSylow minus = checkSylowG minus (sylowWords minus) :=
  rfl

theorem checkRank_eq (minus : Bool) : checkRank minus = checkRankG (sylowWords minus) := rfl

theorem checkWC_eq (minus : Bool) :
    checkWC minus = checkWCG minus (sylowWords minus) (certs minus) := rfl

theorem sylowK_sound {minus : Bool} {Tw : List (List ℕ)} {CS : List ℕ}
    (h : sylowK (if minus then 1 else 0) Tw CS = true) : checkSylowG minus Tw = true := by
  unfold sylowK at h
  simp only [andB_eq, Bool.and_eq_true, eqLN_iff, codesK_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hcs : CS = Tw.map wordC := by
    rw [← h1]; congr 1; funext w; exact wordCK_eq w
  subst hcs
  simp only [allLL_eq, allL_eq, anyLL_eq, List.all_eq_true, List.any_eq_true, qBK_eq, isNilN_iff,
    mulK_eq, memN_eq, wordCK_eq, revN_eq, nodupN_eq, lenW_eq, cntEven_eq, Nat.beq_eq,
    decide_eq_true_eq] at h2 h3 h4 h5 h6 h7 h8
  obtain ⟨x, hx, rfl⟩ := h3
  unfold checkSylowG
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨h2, hx⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩

theorem rankK_sound {m : ℕ} {Tw : List (List ℕ)} {CS IL : List ℕ} {IP n : ℕ}
    (hs : sylowK m Tw CS = true) (hp : rankPre CS IL IP = true) (hn : plCnt IP = n)
    (hx : ∀ i < n, rankX IP i = true) : checkRankG Tw = true := by
  obtain ⟨hIL', hILp, hlanes, hcl'⟩ := rankPre_facts hs hp
  have hlt : ∀ a ∈ IL, a < 2 ^ 36 := fun a ha => (hILp a ha).1
  unfold checkRankG
  rw [← hIL']
  simp only [List.all_eq_true]
  intro x₁ hx₁ x₂ hx₂ x₃ hx₃ x₄ hx₄
  rw [List.isEmpty_iff, List.filter_eq_nil_iff]
  intro x₅ hx₅ hcon
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hx₂ hx₃ hx₄ hx₅ hcon
  have hcm : ∀ a b, Check.comm a b = true → Code.mul a b = Code.mul b a := fun a b h => by
    simpa [Check.comm] using h
  obtain ⟨hx2IL, c12, n2⟩ := hx₂
  obtain ⟨⟨hx3IL, c13, -⟩, c23, n3⟩ := hx₃
  obtain ⟨⟨⟨hx4IL, c14, -⟩, c24, -⟩, c34, n4⟩ := hx₄
  obtain ⟨⟨⟨hx5IL, c15, -⟩, c25, -⟩, c35, -⟩ := hx₅
  obtain ⟨c45, n5⟩ := hcon
  have hxsIL : ∀ x ∈ [x₅, x₄, x₃, x₂, x₁], x ∈ IL := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hxsl : ∀ x ∈ [x₅, x₄, x₃, x₂, x₁], x < 2 ^ 36 := fun x hx => hlt x (hxsIL x hx)
  have hxss : ∀ x ∈ [x₅, x₄, x₃, x₂, x₁], Code.mul x x = Code.one :=
    fun x hx => (hILp x (hxsIL x hx)).2.1
  have hpw : [x₅, x₄, x₃, x₂, x₁].Pairwise (fun a b => Code.mul a b = Code.mul b a) :=
    pairwise_five (hcm _ _ c45).symm (hcm _ _ c35).symm (hcm _ _ c25).symm (hcm _ _ c15).symm
      (hcm _ _ c34).symm (hcm _ _ c24).symm (hcm _ _ c14).symm (hcm _ _ c23).symm
      (hcm _ _ c13).symm (hcm _ _ c12).symm
  have hind : Indep [x₅, x₄, x₃, x₂, x₁] :=
    Indep.cons n5 (Indep.cons n4 (Indep.cons n3 (Indep.cons n2 (Indep.cons
      (fun h => (hILp x₁ hx₁).2.2 (by simpa [Check.spanC] using h)) Indep.nil))))
  have hE := spanC_elAb _ hxsl hxss hpw
  have hEn := spanC_nodup _ hxsl hxss hpw hind
  have hE32 : (spanC [x₅, x₄, x₃, x₂, x₁]).length = 32 := by
    rw [length_spanC]; rfl
  have hEIL := spanC_sub hlt hcl' _ hxsIL hxss hpw hind
  exact rank_core hE hEn hE32 hlanes hlt hEIL (by rw [hn]; exact hx)

theorem wcK_sound {minus : Bool} {Tw : List (List ℕ)} {C : List (ℕ × List ℕ)} {IP n : ℕ}
    {EP : List ℕ} (hp : wcPre Tw IP = true) (hc : certK C EP = true) (hn : plCnt IP = n)
    (hx : ∀ i < n, wcX (if minus then 1 else 0) IP C EP i = true) :
    checkWCG minus Tw C = true := by
  have hlanes := wcPre_lanes hp
  have hx' : ∀ i < plCnt IP, wcX (if minus then 1 else 0) IP C EP i = true := by
    rw [hn]; exact hx
  unfold checkWCG
  simp only [List.all_eq_true, List.mem_map, List.mem_filter]
  rintro _ ⟨w₁, ⟨hw₁, hi₁⟩, rfl⟩ _ ⟨w₂, ⟨hw₂, hi₂⟩, rfl⟩
  dsimp only
  split_ifs with hcond
  · rw [List.all_eq_true]
    intro r hr
    obtain ⟨w₃, hw₃, rfl⟩ := List.mem_map.1 hr
    dsimp only
    unfold wcTripleG
    by_cases hcond3 : (Check.comm (wordC w₁) (wordC w₂) && Check.comm (wordC w₁) (wordC w₃) &&
        Check.comm (wordC w₂) (wordC w₃) && !(spanC [wordC w₁]).contains (wordC w₂) &&
        !(spanC [wordC w₂, wordC w₁]).contains (wordC w₃)) = true
    · rw [if_pos hcond3]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hcond3
      obtain ⟨⟨⟨⟨hxy, hxz⟩, hyz⟩, hy⟩, hz⟩ := hcond3
      obtain ⟨hnd, hmain⟩ := wc_triple (minus := minus) hlanes hc hx' (List.mem_filter.2 ⟨hw₁, hi₁⟩)
        (List.mem_filter.2 ⟨hw₂, hi₂⟩) hw₃
        hxy hy hxz hyz hz
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        List.any_eq_true, List.all_eq_true, beq_iff_eq]
      refine ⟨hnd, ?_⟩
      rcases hmain with ⟨hm, h1, h2, h3⟩ | ⟨p, hp, hk, hq, hpar, hcert⟩
      · exact Or.inl ⟨hm, ⟨h1, h2⟩, h3⟩
      · refine Or.inr ⟨p, hp, ⟨⟨hk, hq⟩, ?_⟩, hcert⟩
        by_cases hev : w₁.length % 2 = 0 ∧ w₂.length % 2 = 0 ∧ w₃.length % 2 = 0
        · exact Or.inr (hpar hev)
        · left
          cases hb : (w₁.length % 2 == 0 && w₂.length % 2 == 0 && w₃.length % 2 == 0)
          · rfl
          · exfalso
            apply hev
            simpa [Bool.and_eq_true, and_assoc] using hb
    · rw [if_neg hcond3]
  · rfl

end CFSG.KC.Misc.O62

end
