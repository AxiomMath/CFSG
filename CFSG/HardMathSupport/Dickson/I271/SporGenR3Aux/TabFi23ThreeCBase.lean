
module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Twin
public import Certificates.Data.TabFi23C

@[expose] public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.HardMathSupport.Dickson.I271.TabFi23C
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Bridge

theorem actW_eq (w : List ℕ) {m : ℕ} (hm : m < 31671) :
    actW orb (dTable orb) (genTables orb (-2)) w m = idx 31671 (w.map conjPt).prod m := by
  induction w generalizing m with
  | nil => simp [actW, idx_one]
  | cons k w ih =>
    have h1 : actW orb (dTable orb) (genTables orb (-2)) (k :: w) m =
        rf orb (dTable orb) (genTables orb (-2)) k
          (actW orb (dTable orb) (genTables orb (-2)) w m) := rfl
    rw [h1, ih hm]
    unfold rf
    rw [treeAct_dTable_spec k _ (idx_lt _ hm), ← idx_mul, List.map_cons, List.prod_cons]

theorem prod_eq_of_sigEq {u v : List ℕ}
    (h : sigEq orb (dTable orb) (genTables orb (-2)) u v = true) :
    (u.map conjPt).prod = (v.map conjPt).prod := by
  have h1 : ((u.map conjPt).prod)⁻¹ * (v.map conjPt).prod = 1 := by
    apply sep
    intro t ht
    have hq : chainQ[t]! < 31671 := chainQ_lt ht
    have h2 := (List.all_eq_true.1 h) t (List.mem_range.2 ht)
    rw [beq_iff_eq, actW_eq u hq, actW_eq v hq] at h2
    rw [idx_mul, ← h2]
    exact idx_inv_idx _ _
  exact inv_mul_eq_one.1 h1

theorem sigEq_of_prod_eq {u v : List ℕ} (h : (u.map conjPt).prod = (v.map conjPt).prod) :
    sigEq orb (dTable orb) (genTables orb (-2)) u v = true := by
  unfold sigEq
  rw [List.all_eq_true]
  intro t ht
  have hq : chainQ[t]! < 31671 := chainQ_lt (List.mem_range.1 ht)
  rw [beq_iff_eq, actW_eq u hq, actW_eq v hq, h]

theorem mem_twinPairs {F : List ℕ} {a b : ℕ} :
    (a, b) ∈ twinPairs orb (dTable orb) (genTables orb (-2)) F ↔
      a ∈ F ∧ b ∈ F ∧ twinB orb (dTable orb) (genTables orb (-2)) F a b = true := by
  unfold twinPairs
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', b', ⟨hb', ht⟩, rfl, rfl⟩
    exact ⟨ha', hb', ht⟩
  · rintro ⟨ha, hb, ht⟩
    exact ⟨a, ha, b, ⟨hb, ht⟩, rfl, rfl⟩

end Bridge

section Twins

@[expose] noncomputable def ePt (i : Fin 31671) : CFSG.Sporadic.Fi23.J := conjPt i.val

@[expose] noncomputable def thirdPt (a b : Fin 31671) : Fin 31671 := conjPt a.val • b

@[expose] noncomputable def cPt (k : ℕ) (t : Fin chainQ.size) : Fin 31671 :=
  conjPt k • (⟨chainQ[t.val]!, chainQ_lt t.2⟩ : Fin 31671)

theorem ePt_smul (g : CFSG.Sporadic.Fi23.J) (i : Fin 31671) : ePt (g • i) = g * ePt i * g⁻¹ := conjPt_smul g i

theorem thirdPt_val (a b : Fin 31671) :
    (thirdPt a b).val = rf orb (dTable orb) (genTables orb (-2)) a.val b.val := by
  unfold thirdPt rf
  rw [treeAct_dTable_spec a.val b.val b.2, idx_of_lt _ b.2]

theorem cPt_val (k : ℕ) (t : Fin chainQ.size) :
    (cPt k t).val = rf orb (dTable orb) (genTables orb (-2)) k chainQ[t.val]! := by
  unfold cPt rf
  rw [treeAct_dTable_spec k _ (chainQ_lt t.2), idx_of_lt _ (chainQ_lt t.2)]

theorem sep_cPt (k : ℕ) (s : CFSG.Sporadic.Fi23.J) (hs : ∀ t : Fin chainQ.size, s • cPt k t = cPt k t) : s = 1 := by
  set W : CFSG.Sporadic.Fi23.J := conjPt k with hW
  have hg : W⁻¹ * s * W = 1 := by
    apply sep
    intro t ht
    have h1 := hs ⟨t, ht⟩
    rw [idx_of_lt _ (chainQ_lt ht)]
    have h2 : (W⁻¹ * s * W) • (⟨chainQ[t]!, chainQ_lt ht⟩ : Fin 31671) =
        ⟨chainQ[t]!, chainQ_lt ht⟩ := by
      rw [mul_smul, mul_smul]
      have h3 : s • (W • (⟨chainQ[t]!, chainQ_lt ht⟩ : Fin 31671)) =
          W • (⟨chainQ[t]!, chainQ_lt ht⟩ : Fin 31671) := h1
      rw [h3, inv_smul_smul]
    exact congrArg Fin.val h2
  calc s = W * (W⁻¹ * s * W) * W⁻¹ := by group
    _ = 1 := by rw [hg]; group

theorem mem_fixList_iff' {T : Table} {x : CFSG.Sporadic.Fi23.J} (hT : Rep 31671 T x) (r : Fin 31671) :
    r.val ∈ fixList T ↔ x • r = r := by
  rw [mem_fixList_iff hT r.2, fix_iff_comm x r]

theorem commB_iff' (i j : Fin 31671) :
    commB orb (dTable orb) (genTables orb (-2)) i.val j.val = true ↔
      ePt i * ePt j = ePt j * ePt i := commB_iff i.2 j.2

theorem twin_iff {T : Table} {x : CFSG.Sporadic.Fi23.J} (hT : Rep 31671 T x) (a b : Fin 31671) :
    Twin ePt x a b ↔
      (a.val, b.val) ∈ twinPairs orb (dTable orb) (genTables orb (-2)) (fixList T) := by
  rw [mem_twinPairs]
  have hfix := mem_fixList_iff' hT
  have hcomm := commB_iff'
  unfold Twin twinB
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨ha, hb, hab, hnc, hc⟩
    refine ⟨(hfix a).2 ha, (hfix b).2 hb, ⟨fun h => hab (Fin.ext h), ?_⟩, ?_⟩
    · exact Bool.eq_false_iff.2 (fun h => hnc ((hcomm a b).1 h))
    · intro c hcF
      by_cases hca : c = a.val
      · exact Or.inl (Or.inl hca)
      by_cases hcb : c = b.val
      · exact Or.inl (Or.inr hcb)
      right
      have hlt := lt_of_mem_fixList hcF
      have h1 := hc ⟨c, hlt⟩ ((hfix ⟨c, hlt⟩).1 hcF) (fun h => hca (congrArg Fin.val h))
        (fun h => hcb (congrArg Fin.val h))
      exact Bool.eq_iff_iff.2 ((hcomm ⟨c, hlt⟩ a).trans (h1.trans (hcomm ⟨c, hlt⟩ b).symm))
  · rintro ⟨hFa, hFb, ⟨hne, hnc⟩, hall⟩
    refine ⟨(hfix a).1 hFa, (hfix b).1 hFb, fun h => hne (congrArg Fin.val h), ?_, ?_⟩
    · intro h
      have h1 := (hcomm a b).2 h
      rw [hnc] at h1
      exact absurd h1 (by decide)
    · intro c hcx hca hcb
      have hcF : c.val ∈ fixList T := (hfix c).2 hcx
      rcases hall c.val hcF with (h | h) | h
      · exact absurd (Fin.ext h) hca
      · exact absurd (Fin.ext h) hcb
      · exact (hcomm c a).symm.trans ((Bool.eq_iff_iff.1 h).trans (hcomm c b))

theorem goodPt_spec {T : Table} {x : CFSG.Sporadic.Fi23.J} (hT : Rep 31671 T x) (cF : Fin 31671)
    (h : goodPt orb (dTable orb) (genTables orb (-2)) T (fixList T) cF.val = true)
    (c' : Fin 31671)
    (hprof : ∀ a : Fin 31671, x • a = a →
      (ePt c' * ePt a = ePt a * ePt c' ↔ ePt cF * ePt a = ePt a * ePt cF)) :
    c' = cF ∨ c' = x • cF ∨ c' = x • x • cF := by
  have hfix := mem_fixList_iff' hT
  have hcomm := commB_iff'
  unfold goodPt at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, hall⟩ := h
  have h1 := (List.all_eq_true.1 hall) c'.val (List.mem_range.2 c'.2)
  have hF : (fixList T).all (fun a => commB orb (dTable orb) (genTables orb (-2)) c'.val a ==
      commB orb (dTable orb) (genTables orb (-2)) cF.val a) = true := by
    rw [List.all_eq_true]
    intro a ha
    have halt := lt_of_mem_fixList ha
    have h2 := hprof ⟨a, halt⟩ ((hfix ⟨a, halt⟩).1 ha)
    rw [beq_iff_eq]
    exact Bool.eq_iff_iff.2 ((hcomm c' ⟨a, halt⟩).trans (h2.trans (hcomm cF ⟨a, halt⟩).symm))
  rw [hF] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact Or.inl (Fin.ext h1)
  · exact Or.inr (Or.inl (Fin.ext (h1.trans (ap_eq_smul hT cF))))
  · refine Or.inr (Or.inr (Fin.ext ?_))
    rw [h1, ap_eq_smul hT cF]
    exact ap_eq_smul hT (x • cF)

theorem twinCheck_spec {T : Table} {x : CFSG.Sporadic.Fi23.J} (hT : Rep 31671 T x) {k : ℕ}
    (h : twinCheck orb (dTable orb) (genTables orb (-2)) T k = true) :
    (∀ a : Fin 31671, x • a = a → ∃ b, Twin ePt x a b) ∧
    (∀ a b a' b', Twin ePt x a b → Twin ePt x a' b' → ePt a' * ePt b' = ePt a * ePt b →
      (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = thirdPt a b) ∨ (a' = thirdPt a b ∧ b' = a)) ∧
    (∀ a b, Twin ePt x a b → thirdPt a b ≠ a ∧ thirdPt a b ≠ b) ∧
    (∀ a b a' b', Twin ePt x a b → Twin ePt x a' b' →
      ePt a * ePt b * (ePt a' * ePt b') = ePt a' * ePt b' * (ePt a * ePt b)) ∧
    (∀ (t : Fin chainQ.size) (c' : Fin 31671),
      (∀ a : Fin 31671, x • a = a → (ePt c' * ePt a = ePt a * ePt c' ↔
        ePt (cPt k t) * ePt a = ePt a * ePt (cPt k t))) →
      c' = cPt k t ∨ c' = x • cPt k t ∨ c' = x • x • cPt k t) := by
  have hfix := mem_fixList_iff' hT
  unfold twinCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have h5 := (List.all_eq_true.1 h1) a.val ((hfix a).2 ha)
    obtain ⟨p, hp, hp1⟩ := List.any_eq_true.1 h5
    have hp1' : p.1 = a.val := beq_iff_eq.1 hp1
    obtain ⟨-, hF2, -⟩ := mem_twinPairs.1 (show (p.1, p.2) ∈ _ from hp)
    refine ⟨⟨p.2, lt_of_mem_fixList hF2⟩, (twin_iff hT a _).2 ?_⟩
    rw [← hp1']
    exact hp
  · intro a b a' b' hab hab' hE
    have hP1 := (twin_iff hT a b).1 hab
    have hP2 := (twin_iff hT a' b').1 hab'
    have hsig : sigEq orb (dTable orb) (genTables orb (-2)) [a.val, b.val] [a'.val, b'.val] =
        true := by
      apply sigEq_of_prod_eq
      simpa [ePt, List.prod_cons, mul_one] using hE.symm
    have h6 := (List.all_eq_true.1 h2) (a.val, b.val) hP1
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h6
    obtain ⟨⟨hc1, hc2⟩, hq⟩ := h6
    have h7 := (List.all_eq_true.1 hq) (a'.val, b'.val) hP2
    rw [hsig] at h7
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq] at h7
    have e3 := thirdPt_val a b
    rcases h7 with (⟨h8, h9⟩ | ⟨h8, h9⟩) | ⟨h8, h9⟩
    · exact Or.inl ⟨Fin.ext h8, Fin.ext h9⟩
    · exact Or.inr (Or.inl ⟨Fin.ext h8, Fin.ext (h9.trans e3.symm)⟩)
    · exact Or.inr (Or.inr ⟨Fin.ext (h8.trans e3.symm), Fin.ext h9⟩)
  · intro a b hab
    have hP1 := (twin_iff hT a b).1 hab
    have h6 := (List.all_eq_true.1 h2) (a.val, b.val) hP1
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h6
    obtain ⟨⟨hc1, hc2⟩, -⟩ := h6
    have e3 := thirdPt_val a b
    exact ⟨fun h => hc1 (e3.symm.trans (congrArg Fin.val h)),
      fun h => hc2 (e3.symm.trans (congrArg Fin.val h))⟩
  · intro a b a' b' hab hab'
    have hP1 := (twin_iff hT a b).1 hab
    have hP2 := (twin_iff hT a' b').1 hab'
    have h6 := (List.all_eq_true.1 ((List.all_eq_true.1 h3) (a.val, b.val) hP1))
      (a'.val, b'.val) hP2
    have h7 := prod_eq_of_sigEq h6
    simpa [ePt, List.prod_cons, mul_assoc] using h7
  · intro t c' hprof
    have h5 := (List.all_eq_true.1 h4) t.val (List.mem_range.2 t.2)
    have hlt : rf orb (dTable orb) (genTables orb (-2)) k chainQ[t.val]! < 31671 := by
      rw [← cPt_val]
      exact (cPt k t).2
    have h6 : goodPt orb (dTable orb) (genTables orb (-2)) T (fixList T) (cPt k t).val = true := by
      rw [cPt_val]
      exact h5
    exact goodPt_spec hT (cPt k t) h6 c' hprof

end Twins

end CFSG.HardMathSupport.Dickson.I271.TabFi23
