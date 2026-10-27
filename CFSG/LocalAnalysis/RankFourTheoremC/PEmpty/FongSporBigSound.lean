module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint

theorem MGen.exists_norm_of_checkBase {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : MGen) (h : c.checkBase O sA sB = true)
    (n : PW × ℕ × ℕ) (hn : n ∈ c.g.ns) :
    ∃ z₀ n₀ : (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ,
      orderOf z₀ = c.g.p ∧ n₀ * z₀ * n₀⁻¹ = z₀ ^ n.2.1 := by
  unfold MGen.checkBase at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  simp only [MGen.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨⟨⟨hp, hlen⟩, hms⟩, -⟩, -⟩ := hwf
  haveI : Fact c.g.p.Prime := ⟨hp⟩
  have hf : ∀ f ∈ c.baseFacts, f ∈ (⟨2, [], c.baseFacts⟩ : MCert).facts := fun f hf => hf
  have hB := MGen.holdsBase_of_facts Sp hC c hlen hms hf
  unfold PGen.holdsBase at hB
  obtain ⟨hzp, hz1, -, hns, -⟩ := hB
  exact ⟨_, _, orderOf_eq_prime hzp hz1, (hns n hn).1⟩

theorem PClaim.exists_norm_of_check {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : PClaim) (h : c.check O sA sB = true) :
    ∃ z₀ n₀ : (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ,
      orderOf z₀ = c.p ∧ n₀ * z₀ * n₀⁻¹ = z₀ ^ c.k := by
  unfold PClaim.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp, hC⟩ := h
  haveI : Fact c.p.Prime := ⟨of_decide_eq_true hp⟩
  have hfz : MFact.ord c.rz c.p ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [PClaim.facts]
  have hfn : MFact.ord c.rn c.en ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [PClaim.facts]
  have hfne : MFact.ne [(c.rz, 1)] [] c.zt ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [PClaim.facts]
  have hfc : MFact.conj c.rn [(c.rz, 1)] [(c.rz, c.k)] ∈
      (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [PClaim.facts]
  have hz1 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, 1)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨c.p, hfz⟩
  have hzk : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, c.k)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨c.p, hfz⟩
  have hnil : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [] := hasOrd_nil _
  have hzpow : regUnit Sp hC c.rz ^ c.p = 1 := regUnit_pow Sp hC hfz
  have hne := regUnit_ne Sp hC hfne hz1 hnil
  have hconj := regUnit_conj Sp hC hfc hfn hz1 hzk
  simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
    mul_one] at hne hconj
  exact ⟨_, _, orderOf_eq_prime hzpow hne, hconj⟩

theorem OClaim.exists_orderOf_of_check {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : OClaim) (h : c.check O sA sB = true) :
    ∃ g : (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ, orderOf g = c.p ^ (c.n + 1) := by
  unfold OClaim.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp, hC⟩ := h
  haveI : Fact c.p.Prime := ⟨of_decide_eq_true hp⟩
  have hfg : MFact.ord c.rg (c.p ^ (c.n + 1)) ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [OClaim.facts]
  have hfne : MFact.ne [(c.rg, c.p ^ c.n)] [] c.t ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [OClaim.facts]
  have hw : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rg, c.p ^ c.n)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨_, hfg⟩
  have hnil : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [] := hasOrd_nil _
  have hfin := regUnit_pow Sp hC hfg
  have hne := regUnit_ne Sp hC hfne hw hnil
  simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one] at hne
  exact ⟨_, orderOf_eq_prime_pow hne hfin⟩

theorem BClaim.exists_bigW_of_check {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : BClaim) (h : c.check O sA sB = true) :
    BigW (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ c.p c.r := by
  unfold BClaim.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  simp only [BClaim.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] at hwf
  obtain ⟨⟨hp, hr⟩, hzwReg⟩ := hwf
  haveI : Fact c.p.Prime := ⟨hp⟩
  haveI : Fact c.r.Prime := ⟨hr⟩
  have hfz : MFact.ord c.rz c.p ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [BClaim.facts]
  have hfzne : MFact.ne [(c.rz, 1)] [] c.zt ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [BClaim.facts]
  have hft : MFact.ord c.rt 2 ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [BClaim.facts]
  have hftne : MFact.ne [(c.rt, 1)] [] c.tt ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [BClaim.facts]
  have hfzt : MFact.eq [(c.rz, 1), (c.rt, 1)] [(c.rt, 1), (c.rz, 1)] ∈
      (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [BClaim.facts]
  have hfzw : MFact.eq [(c.rz, 1)] c.zw ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
    simp [BClaim.facts]
  have hord1 : ∀ x, HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(x, 1)] → True := fun _ _ => trivial
  have hz1 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, 1)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨c.p, hfz⟩
  have ht1 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rt, 1)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨2, hft⟩
  have hnil : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [] := hasOrd_nil _
  have hzt12 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rz, 1), (c.rt, 1)] := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨c.p, hfz⟩
    · rw [List.mem_singleton] at hq
      subst hq
      exact ⟨2, hft⟩
  have hzt21 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rt, 1), (c.rz, 1)] := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨2, hft⟩
    · rw [List.mem_singleton] at hq
      subst hq
      exact ⟨c.p, hfz⟩
  have hzpow : regUnit Sp hC c.rz ^ c.p = 1 := regUnit_pow Sp hC hfz
  have hzne := regUnit_ne Sp hC hfzne hz1 hnil
  have htpow : regUnit Sp hC c.rt ^ 2 = 1 := regUnit_pow Sp hC hft
  have htne := regUnit_ne Sp hC hftne ht1 hnil
  have hzteq := regUnit_eq Sp hC hfzt hzt12 hzt21
  simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
    mul_one] at hzne htne hzteq
  refine ⟨regUnit Sp hC c.rz, regUnit Sp hC c.rt, {x | ∃ q ∈ c.ws, x = regUnit Sp hC q.1},
    orderOf_eq_prime hzpow hzne, by rw [← pow_two]; exact htpow, htne, hzteq, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hfq1 : MFact.ord q.1 c.r ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
      simp only [BClaim.facts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨q, hq, by simp⟩
    have hfq2 : MFact.ne [(q.1, 1)] [] q.2 ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
      simp only [BClaim.facts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨q, hq, by simp⟩
    have hfq3 : MFact.eq [(q.1, 1), (c.rt, 1)] [(c.rt, 1), (q.1, 1)] ∈
        (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
      simp only [BClaim.facts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨q, hq, by simp⟩
    have hq1 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(q.1, 1)] := by
      intro q' hq'
      rw [List.mem_singleton] at hq'
      subst hq'
      exact ⟨c.r, hfq1⟩
    have hq12 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(q.1, 1), (c.rt, 1)] := by
      intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact ⟨c.r, hfq1⟩
      · rw [List.mem_singleton] at hq'
        subst hq'
        exact ⟨2, hft⟩
    have hq21 : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) [(c.rt, 1), (q.1, 1)] := by
      intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact ⟨2, hft⟩
      · rw [List.mem_singleton] at hq'
        subst hq'
        exact ⟨c.r, hfq1⟩
    have hwpow : regUnit Sp hC q.1 ^ c.r = 1 := regUnit_pow Sp hC hfq1
    have hwne := regUnit_ne Sp hC hfq2 hq1 hnil
    have hweq := regUnit_eq Sp hC hfq3 hq12 hq21
    simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
      mul_one] at hwne hweq
    exact ⟨orderOf_eq_prime hwpow hwne, hweq⟩
  ·
    have hzw : HasOrd (⟨c.nregs, c.prog, c.facts⟩ : MCert) c.zw := by
      intro q hq
      obtain ⟨w, hw, hwq⟩ := hzwReg q hq
      have hfw : MFact.ord w.1 c.r ∈ (⟨c.nregs, c.prog, c.facts⟩ : MCert).facts := by
        simp only [BClaim.facts, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨w, hw, by simp⟩
      exact ⟨c.r, hwq ▸ hfw⟩
    have hzeq := regUnit_eq Sp hC hfzw hz1 hzw
    simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
      mul_one] at hzeq
    rw [hzeq]
    refine Subgroup.list_prod_mem _ ?_
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w, hw, hwq⟩ := hzwReg q hq
    have hmem : regUnit Sp hC q.1 ∈ {x | ∃ q ∈ c.ws, x = regUnit Sp hC q.1} :=
      ⟨w, hw, by rw [hwq]⟩
    exact Subgroup.pow_mem _ (Subgroup.subset_closure hmem) _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
