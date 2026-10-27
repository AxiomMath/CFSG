module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint Subgroup

theorem step_getElem_ne {M V : Type} (O : Ops M V) [Inhabited M] (R : Array M) (op : Op) (i : ℕ)
    (h : i ≠ opTarget op) : (O.step R op)[i]! = R[i]! := by
  cases op with
  | mul a b k => exact Array.getElem!_set!_ne R k i _ (Ne.symm h)
  | pow e a k => exact Array.getElem!_set!_ne R k i _ (Ne.symm h)

theorem run_getElem_lt {M V : Type} (O : Ops M V) [Inhabited M] (prog : List Op) (i : ℕ)
    (h : ∀ op ∈ prog, i < opTarget op) (R : Array M) : (O.run prog R)[i]! = R[i]! := by
  induction prog generalizing R with
  | nil => rfl
  | cons op rest ih =>
    show (O.run rest (O.step R op))[i]! = R[i]!
    rw [ih (fun op' hop' => h op' (List.mem_cons_of_mem _ hop'))]
    exact step_getElem_ne O R op i (Nat.ne_of_lt (h op List.mem_cons_self))

theorem certRegs_zero_of_prog {M V : Type} {O : Ops M V} [Inhabited M] {sA sB : String}
    {C : MCert} (h2 : 2 ≤ C.nregs) (hp : ∀ op ∈ C.prog, 2 ≤ opTarget op) :
    (certRegs O sA sB C)[0]! = O.decode sA := by
  unfold certRegs Ops.regsOf
  rw [run_getElem_lt O C.prog 0 (fun op hop => by have := hp op hop; omega)]
  simp [Ops.initRegs, Array.getElem!_eq_getD, Array.getD_getElem?]
  intro h
  omega

theorem certRegs_one_of_prog {M V : Type} {O : Ops M V} [Inhabited M] {sA sB : String}
    {C : MCert} (h2 : 2 ≤ C.nregs) (hp : ∀ op ∈ C.prog, 2 ≤ opTarget op) :
    (certRegs O sA sB C)[1]! = O.decode sB := by
  unfold certRegs Ops.regsOf
  rw [run_getElem_lt O C.prog 1 (fun op hop => by have := hp op hop; omega)]
  simp [Ops.initRegs, Array.getElem!_eq_getD, Array.getD_getElem?]
  intro h
  omega

theorem mem_normalizer_zpowers_of_rel {G : Type*} [Group G] {z n : G} {k k' : ℕ}
    (h1 : n * z * n⁻¹ = z ^ k) (h2 : n * z ^ k' * n⁻¹ = z) :
    n ∈ normalizer (zpowers z : Set G) := by
  have h3 : n⁻¹ * z * n = z ^ k' := by
    calc n⁻¹ * z * n = n⁻¹ * (n * z ^ k' * n⁻¹) * n := by rw [h2]
      _ = z ^ k' := by group
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    have h4 : n * z ^ i * n⁻¹ = (z ^ k) ^ i := by rw [← h1, ← conj_zpow]
    rw [h4]
    exact zpow_mem (pow_mem (mem_zpowers z) k) i
  · intro hx
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hx
    have h5 : x = (n⁻¹ * z * n) ^ j := by
      have h6 : (n⁻¹ * z * n) ^ j = n⁻¹ * z ^ j * n := by
        have := conj_zpow (a := n⁻¹) (b := z) (i := j)
        simpa using this
      rw [h6, hj]
      group
    rw [h5, h3]
    exact zpow_mem (pow_mem (mem_zpowers z) k') j

theorem GClaim.genW_of_check {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : GClaim) (h : c.check O sA sB = true) :
    GenW (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ c.p := by
  unfold GClaim.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  have hn2 : 2 ≤ c.nregs := by
    have h' := hC
    unfold mcertCheck at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h'.1.1
  simp only [GClaim.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨⟨hp, hprog⟩, hmsj⟩, hwreg⟩ := hwf
  haveI : Fact c.p.Prime := ⟨hp⟩
  have hn2' : 2 ≤ (⟨c.nregs, c.prog, c.facts⟩ : MCert).nregs := hn2
  have hprog' : ∀ op ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).prog, 2 ≤ opTarget op := hprog
  have fa : MFact.ord 0 c.oa ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [GClaim.facts]
  have fb : MFact.ord 1 c.ob ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [GClaim.facts]
  have fz : MFact.ord c.rz c.p ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [GClaim.facts]
  have fzne : MFact.ne [(c.rz, 1)] [] c.zt ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [GClaim.facts]
  have fwa : MFact.eq [(0, 1)] c.wa ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [GClaim.facts]
  have fwb : MFact.eq [(1, 1)] c.wb ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [GClaim.facts]
  have fts : ∀ q ∈ c.ts, MFact.ord q.1 2 ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts ∧
      MFact.ne [(q.1, 1)] [] q.2 ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts ∧
      MFact.eq [(c.rz, 1), (q.1, 1)] [(q.1, 1), (c.rz, 1)] ∈
        (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    intro q hq
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [GClaim.facts, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inr ⟨q, hq, by simp⟩))
  have fns : ∀ n ∈ c.ns, MFact.ord n.1 n.2.2.2 ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts ∧
      MFact.eq [(n.1, 1), (c.rz, 1)] [(c.rz, n.2.1), (n.1, 1)] ∈
        (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts ∧
      MFact.eq [(n.1, 1), (c.rz, n.2.2.1)] [(c.rz, 1), (n.1, 1)] ∈
        (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    intro n hn
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [GClaim.facts, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨n, hn, by simp⟩)
  have fms : ∀ m ∈ c.ms, MFact.ord m.1 m.2.2 ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts ∧
      MFact.eq [(m.1, 1), ((c.ts.getD m.2.1 (0, 0)).1, 1)]
        [((c.ts.getD m.2.1 (0, 0)).1, 1), (m.1, 1)] ∈
        (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    intro m hm
    refine ⟨?_, ?_⟩ <;>
    · simp only [GClaim.facts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨m, hm, by simp⟩
  have hord : ∀ r, (r = 0 ∨ r = 1 ∨ r = c.rz ∨ (∃ q ∈ c.ts, q.1 = r) ∨ (∃ n ∈ c.ns, n.1 = r) ∨
      (∃ m ∈ c.ms, m.1 = r)) →
      ∃ e, MFact.ord r e ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    rintro r (rfl | rfl | rfl | ⟨q, hq, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact ⟨c.oa, fa⟩
    · exact ⟨c.ob, fb⟩
    · exact ⟨c.p, fz⟩
    · exact ⟨2, (fts q hq).1⟩
    · exact ⟨_, (fns n hn).1⟩
    · exact ⟨_, (fms m hm).1⟩
  have hnil : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [] := hasOrd_nil _
  have hzo : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, 1)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hord _ (Or.inr (Or.inr (Or.inl rfl)))
  have hS : certMonoid pf d sA sB = Submonoid.closure
      ({valHom (certMonoid pf d sA sB) (regUnit Sp hC 0),
        valHom (certMonoid pf d sA sB) (regUnit Sp hC 1)} :
        Set (Matrix (Fin d) (Fin d) (ZMod pf))) := by
    rw [val_regUnit Sp hC fa, val_regUnit Sp hC fb, certRegs_zero_of_prog hn2' hprog',
      certRegs_one_of_prog hn2' hprog', Sp.toMat_decode, Sp.toMat_decode]
    rfl
  have hcl0 : Subgroup.closure ({regUnit Sp hC 0, regUnit Sp hC 1} :
      Set (certMonoid pf d sA sB)ˣ) = ⊤ := closure_units_eq_top (certMonoid pf d sA sB) _ _ hS
  refine ⟨regUnit Sp hC c.rz, {x | ∃ n ∈ c.ns, x = regUnit Sp hC n.1},
    {x | ∃ m ∈ c.ms, x = regUnit Sp hC m.1}, ?_, ?_, ?_, ?_⟩
  · have hzpow := regUnit_pow Sp hC fz
    have hne := regUnit_ne Sp hC fzne hzo hnil
    simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
      mul_one] at hne
    exact orderOf_eq_prime hzpow hne
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨f0, f1, f2⟩ := fns n hn
    have hno : ∃ e, MFact.ord n.1 e ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts :=
      hord _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl⟩)))))
    have hzoo : ∃ e, MFact.ord c.rz e ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts :=
      hord _ (Or.inr (Or.inr (Or.inl rfl)))
    have w1 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(n.1, 1), (c.rz, 1)] := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hno
      · rw [List.mem_singleton] at hq
        subst hq
        exact hzoo
    have w2 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, n.2.1), (n.1, 1)] := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hzoo
      · rw [List.mem_singleton] at hq
        subst hq
        exact hno
    have w3 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(n.1, 1), (c.rz, n.2.2.1)] := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hno
      · rw [List.mem_singleton] at hq
        subst hq
        exact hzoo
    have w4 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, 1), (n.1, 1)] := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hzoo
      · rw [List.mem_singleton] at hq
        subst hq
        exact hno
    have e1 := regUnit_eq Sp hC f1 w1 w2
    have e2 := regUnit_eq Sp hC f2 w3 w4
    simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
      mul_one] at e1 e2
    exact mem_normalizer_zpowers_of_rel (mul_inv_eq_iff_eq_mul.mpr e1)
      (mul_inv_eq_iff_eq_mul.mpr e2)
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨f0, f1⟩ := fms m hm
    have hj : m.2.1 < c.ts.length := hmsj m hm
    have hq : c.ts.getD m.2.1 (0, 0) ∈ c.ts := by
      rw [List.getD_eq_getElem (hn := hj)]
      exact List.getElem_mem _
    obtain ⟨g0, g1, g2⟩ := fts _ hq
    have hqo : ∃ e, MFact.ord (c.ts.getD m.2.1 (0, 0)).1 e ∈
        (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts :=
      hord _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hq, rfl⟩))))
    have hmo : ∃ e, MFact.ord m.1 e ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts :=
      hord _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, rfl⟩)))))
    have hzoo : ∃ e, MFact.ord c.rz e ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts :=
      hord _ (Or.inr (Or.inr (Or.inl rfl)))
    have hqw : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert)
        [((c.ts.getD m.2.1 (0, 0)).1, 1)] := by
      intro q' hq'
      rw [List.mem_singleton] at hq'
      subst hq'
      exact hqo
    have hzq : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert)
        [(c.rz, 1), ((c.ts.getD m.2.1 (0, 0)).1, 1)] := by
      intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hzoo
      · rw [List.mem_singleton] at hq'
        subst hq'
        exact hqo
    have hqz : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert)
        [((c.ts.getD m.2.1 (0, 0)).1, 1), (c.rz, 1)] := by
      intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hqo
      · rw [List.mem_singleton] at hq'
        subst hq'
        exact hzoo
    have hmq : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert)
        [(m.1, 1), ((c.ts.getD m.2.1 (0, 0)).1, 1)] := by
      intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hmo
      · rw [List.mem_singleton] at hq'
        subst hq'
        exact hqo
    have hqm : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert)
        [((c.ts.getD m.2.1 (0, 0)).1, 1), (m.1, 1)] := by
      intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hqo
      · rw [List.mem_singleton] at hq'
        subst hq'
        exact hmo
    have ht2 := regUnit_pow Sp hC g0
    have htne := regUnit_ne Sp hC g1 hqw hnil
    have hzt := regUnit_eq Sp hC g2 hzq hqz
    have hmt := regUnit_eq Sp hC f1 hmq hqm
    simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
      mul_one] at htne hzt hmt
    exact ⟨regUnit Sp hC (c.ts.getD m.2.1 (0, 0)).1, by rw [← pow_two]; exact ht2, htne, hzt, hmt⟩
  ·
    have hreg : ∀ q ∈ c.wa ++ c.wb, (∃ n ∈ c.ns, n.1 = q.1) ∨ (∃ m ∈ c.ms, m.1 = q.1) := by
      intro q hq
      have h1 := hwreg q hq
      rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at h1
      rcases h1 with ⟨n, hn, hnq⟩ | ⟨m, hm, hmq⟩
      · exact Or.inl ⟨n, hn, of_decide_eq_true hnq⟩
      · exact Or.inr ⟨m, hm, of_decide_eq_true hmq⟩
    have hordq : ∀ q ∈ c.wa ++ c.wb,
        ∃ e, MFact.ord q.1 e ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
      intro q hq
      rcases hreg q hq with ⟨n, hn, hnq⟩ | ⟨m, hm, hmq⟩
      · exact hord _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hnq⟩)))))
      · exact hord _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, hmq⟩)))))
    have hmemS : ∀ q ∈ c.wa ++ c.wb, regUnit Sp hC q.1 ∈
        ({x | ∃ n ∈ c.ns, x = regUnit Sp hC n.1} ∪ {x | ∃ m ∈ c.ms, x = regUnit Sp hC m.1}) := by
      intro q hq
      rcases hreg q hq with ⟨n, hn, hnq⟩ | ⟨m, hm, hmq⟩
      · exact Or.inl ⟨n, hn, by rw [hnq]⟩
      · exact Or.inr ⟨m, hm, by rw [hmq]⟩
    have hwordS : ∀ w : List (ℕ × ℕ), (∀ q ∈ w, q ∈ c.wa ++ c.wb) →
        wordUnit Sp hC w ∈ Subgroup.closure
          ({x | ∃ n ∈ c.ns, x = regUnit Sp hC n.1} ∪ {x | ∃ m ∈ c.ms, x = regUnit Sp hC m.1}) := by
      intro w hw
      refine Subgroup.list_prod_mem _ ?_
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (hmemS q (hw q hq))) _
    have hone0 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(0, 1)] := by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨c.oa, fa⟩
    have hone1 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(1, 1)] := by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨c.ob, fb⟩
    have hwa : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) c.wa := fun q hq =>
      hordq q (List.mem_append_left _ hq)
    have hwb : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) c.wb := fun q hq =>
      hordq q (List.mem_append_right _ hq)
    have e0 := regUnit_eq Sp hC fwa hone0 hwa
    have e1 := regUnit_eq Sp hC fwb hone1 hwb
    have h0 : regUnit Sp hC 0 ∈ Subgroup.closure
        ({x | ∃ n ∈ c.ns, x = regUnit Sp hC n.1} ∪ {x | ∃ m ∈ c.ms, x = regUnit Sp hC m.1}) := by
      have e0' : wordUnit Sp hC [(0, 1)] = regUnit Sp hC 0 := by simp [wordUnit]
      rw [← e0', e0]
      exact hwordS _ (fun q hq => List.mem_append_left _ hq)
    have h1 : regUnit Sp hC 1 ∈ Subgroup.closure
        ({x | ∃ n ∈ c.ns, x = regUnit Sp hC n.1} ∪ {x | ∃ m ∈ c.ms, x = regUnit Sp hC m.1}) := by
      have e1' : wordUnit Sp hC [(1, 1)] = regUnit Sp hC 1 := by simp [wordUnit]
      rw [← e1', e1]
      exact hwordS _ (fun q hq => List.mem_append_right _ hq)
    rw [eq_top_iff, ← hcl0, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact h0
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
