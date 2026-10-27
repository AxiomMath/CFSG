module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor

section Check

open Subgroup CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426
open scoped commutatorElement

theorem caseOK_card {D : Data} {k : Case} {x : Array ℕ} {A B : Equiv.Perm (Fin D.n)}
    (hA : Rep D.n D.A A) (hB : Rep D.n D.B B) (h : caseOK D k x = true) :
    permOfArr D.n x ^ 3 = 1 ∧
      Nat.card ↥(centralizer {permOfArr D.n x} ⊓ closure {A, B}) = k.card := by
  have hx : Rep D.n x (permOfArr D.n x) := rep_of_validA (caseOK_valid h)
  unfold caseOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hchain⟩, hnd⟩, hlt⟩, hn1⟩, hk2⟩, hcent⟩, hcube⟩, hcrit⟩ := h
  obtain ⟨bs, hbs, hbsm⟩ := exists_fin_list (n := D.n) k.base.toList hlt hnd
  have hbase : (bs.map Fin.val).toArray = k.base := by rw [hbsm]
  have hchain' : caseChainOK2P D.n k.S (bs.map Fin.val).toArray k.W D.A D.B = true := by
    rw [hbase]; exact hchain
  have hcent' : centOKP 3 D.n k.S (bs.map Fin.val).toArray x k.rels k.gens k.base.toList
      (enumBfs D.n k.gens k.base.toList (k.card + 1)) k.card = true := by
    rw [hbase]; exact hcent
  obtain ⟨hC, hCcard⟩ := case_centralizer2P (p := 3) hn1 hk2 hbs hA hB hchain' hx hlt hcent'
  refine ⟨(eqA_iff (rep_powArr hx 3) rep_idA).1 hcube, ?_⟩
  rw [← hC]
  exact hCcard

theorem card_conj_class {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {X k : Equiv.Perm (Fin n)}
    (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Nat.card ↥(centralizer {k * X ^ e * k⁻¹} ⊓ P) = Nat.card ↥(centralizer {X} ⊓ P) := by
  have hXe : (X ^ e) ^ e = X := by
    rcases he with rfl | rfl
    · simp
    · calc (X ^ 2) ^ 2 = X ^ 3 * X := by group
        _ = X := by rw [hX3, one_mul]
  have hmap : (centralizer {X} ⊓ P).map (MulAut.conj k).toMonoidHom =
      centralizer {k * X ^ e * k⁻¹} ⊓ P := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      have hz : z * X ^ e = X ^ e * z := (Commute.pow_right (show Commute z X from hzc) e).eq
      refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
      calc k * z * k⁻¹ * (k * X ^ e * k⁻¹) = k * (z * X ^ e) * k⁻¹ := by group
        _ = k * (X ^ e * z) * k⁻¹ := by rw [hz]
        _ = k * X ^ e * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hyc, hyP⟩
      refine ⟨k⁻¹ * y * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hyP) hk⟩, by group⟩
      have h1 : k⁻¹ * y * k * X ^ e = X ^ e * (k⁻¹ * y * k) := by
        calc k⁻¹ * y * k * X ^ e = k⁻¹ * (y * (k * X ^ e * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * X ^ e * k⁻¹) * y) * k := by rw [hyc]
          _ = X ^ e * (k⁻¹ * y * k) := by group
      have h2 : (Commute (k⁻¹ * y * k) (X ^ e)) := h1
      have h3 := Commute.pow_right h2 e
      rw [hXe] at h3
      exact h3.eq
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem check_card_lt (D : Data) {A B : Equiv.Perm (Fin D.n)} (hA : Rep D.n D.A A)
    (hB : Rep D.n D.B B) (h : check D = true)
    (hc : ∀ c < D.cases.size, D.cases[c]!.card < 60) :
    ∀ x ∈ closure {A, B}, orderOf x = 3 → Nat.card ↥(centralizer {x} ⊓ closure {A, B}) < 60 := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hprod⟩, hord⟩, hm3⟩, hN3⟩, hlines⟩, hsift⟩, htrans⟩, hrec⟩, hsz⟩, hcases⟩ := h
  have hc0 := allLt_spec hcases hpos
  obtain ⟨bs, hbs, hbsm, hn1, hk2, hlt, hchain⟩ := caseOK_chain hc0
  have hbase : (bs.map Fin.val).toArray = D.cases[0]!.base := by rw [hbsm]
  have hchain' : caseChainOK2P D.n D.cases[0]!.S (bs.map Fin.val).toArray D.cases[0]!.W D.A D.B
      = true := by rw [hbase]; exact hchain
  have hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin D.n)}, Rep D.n g G →
      siftA D.n (rawLevels D.n D.cases[0]!.S D.cases[0]!.base) D.cases[0]!.base 0 g = true →
      G ∈ closure {A, B} := by
    intro g G hG hs
    refine mem_closure_two_of_siftG hn1 hk2 hbs hA hB hchain' hG ?_
    rw [hbase]; exact hs
  have hcardP : Nat.card (closure {A, B}) = D.ord := by
    rw [card_closure_two_of_chainOK hn1 hk2 hbs hA hB hchain', hbase, hprod]
  have hfac : (Nat.card (closure {A, B})).factorization 3 = D.k3 := by
    rw [hcardP, hord]
    exact factorization_pow_mulG Nat.prime_three (fun hd => hm3 (Nat.mod_eq_zero_of_dvd hd))
  have hQcard : Nat.card (closure (permsA D.n D.QGens)) = D.N3 := linesOK3_card hlt hlines
  have hQP : closure (permsA D.n D.QGens) ≤ closure {A, B} := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hmemP (rep_of_validA (enumOK_gens_valid (linesOK3_parts hlines).1 hl))
      (allLt_spec hsift hl)
  have hQ : Nat.card (closure (permsA D.n D.QGens)) =
      3 ^ (Nat.card (closure {A, B})).factorization 3 := by
    rw [hQcard, hfac, hN3]
  have hcaseX : ∀ c < D.cases.size, validA D.n D.caseX[c]! = true := fun c hc =>
    caseOK_valid (allLt_spec hcases hc)
  have hrec' : ∀ j < D.lines.size, D.recs.getD j 0 < D.cases.size := fun j hj =>
    of_decide_eq_true (allLt_spec hrec hj)
  intro x hxP hxo
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := exists_conj_rep (r := D.lines.size) hQP hQ
    (fun j => permOfArr D.n D.lines[j]!) (fun c => permOfArr D.n D.caseX[c]!)
    (fun j => permOfArr D.n D.trans[j]!) (fun j => D.recs.getD j 0)
    (fun g hg hg3 => linesOK3_spec hlt hlines hg hg3)
    (fun j hj => transOK2_spec hmemP (fun j hj => hcaseX _ (hrec' j hj))
      (fun j hj => (linesOK3_line hlines hj).1) htrans hj) hxP hxo
  have hcj := hrec' j hj
  obtain ⟨hX3, hcard⟩ := caseOK_card hA hB (allLt_spec hcases hcj)
  rw [card_conj_class hX3 hk he, hcard]
  exact hc _ hcj


end Check


open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem catalogIs_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} : catalogIs S Q ↔ catalogIs T Q :=
  ⟨fun ⟨i, h, ⟨f⟩⟩ => ⟨i, h, ⟨e.symm.trans f⟩⟩, fun ⟨i, h, ⟨f⟩⟩ => ⟨i, h, ⟨e.trans f⟩⟩⟩

theorem kLevel_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (p : ℕ) :
    kLevel p S = kLevel p T := by
  have h1 : IsChevSimple p S ↔ IsChevSimple p T := by
    unfold IsChevSimple; rw [catalogIs_congr e, catalogIs_congr e]
  have h2 : catalogIs S (k2 p) ↔ catalogIs T (k2 p) := catalogIs_congr e
  have h3 : catalogIs S (k3 p) ↔ catalogIs T (k3 p) := catalogIs_congr e
  unfold kLevel
  by_cases a : IsChevSimple p S
  · rw [if_pos a, if_pos (h1.1 a)]
  · rw [if_neg a, if_neg (fun h => a (h1.2 h))]
    by_cases b : catalogIs S (k2 p)
    · rw [if_pos b, if_pos (h2.1 b)]
    · rw [if_neg b, if_neg (fun h => b (h2.2 h))]
      by_cases c : catalogIs S (k3 p)
      · rw [if_pos c, if_pos (h3.1 c)]
      · rw [if_neg c, if_neg (fun h => c (h3.2 h))]

theorem kLevel_le_two {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) : kLevel p S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | contradiction

theorem kLevel_le_three {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k3 p)) :
    kLevel p S ≤ 3 := by
  unfold kLevel
  split_ifs <;> first | omega | contradiction

theorem false_of_glaPComponent_of_solvable {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X I : Subgroup G} (hX : Group.IsSolvable X) (hI : GLAPComponent p X I) : False := by
  have hL : GLAPLayer p X = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt.glaPLayer_eq_bot_of_isSolvable hp
  have hle : I ≤ GLAPLayer p X := by unfold GLAPLayer; exact le_sSup hI
  rw [hL] at hle
  exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hI (eq_bot_iff.2 hle)

theorem eq_top_of_glaPComponent_top {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {p : ℕ}
    {I : Subgroup S} (hI : GLAPComponent p ⊤ I) : I = ⊤ := by
  by_contra hIt
  obtain ⟨M, hIM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hI.2.1 hIt
  have hMnorm : M.Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : M ≤ ⊤)).1 hMn
    exact Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 h1)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hI
      (eq_bot_iff.2 (h ▸ hIM))
  · exact hMne h

theorem nonempty_pSimple_top_equiv {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {p : ℕ}
    (hp : p.Prime) (hnc : ∃ a b : S, a * b ≠ b * a) (hI : GLAPComponent p ⊤ (⊤ : Subgroup S)) :
    Nonempty (PSimple p (⊤ : Subgroup S) ≃* S) := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hI
  haveI : IsSimpleGroup (⊤ : Subgroup S) := Subgroup.topEquiv.symm.isSimpleGroup_congr.1 inferInstance
  have hcore : GLAPPrimeCore p ↥(⊤ : Subgroup S) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥(⊤ : Subgroup S)) with h | h
    · exact h
    · exfalso
      have hnt := isQuasisimple_nontrivial hq
      have : Subsingleton (PQuot p (⊤ : Subgroup S)) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, h]
        trivial
      exact not_subsingleton _ this
  let e1 : PQuot p (⊤ : Subgroup S) ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  have hZ : Subgroup.center (PQuot p (⊤ : Subgroup S)) = ⊥ := by
    have hcS : Subgroup.center S = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnc
        exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
    rw [← Subgroup.map_center_eq e1.symm, hcS, Subgroup.map_bot]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e1⟩

theorem fixSubgroup_conj_eq {S : Type} [Group S] (k : S) :
    fixSubgroup (MulAut.conj k) = Subgroup.centralizer ({k} : Set S) := by
  ext x
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * k = k * x * k⁻¹ * k := by rw [h]
      _ = k * x := by group
  · intro h
    rw [← h]
    group

theorem downLe_of_centralizers {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2) {p j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (htop : kLevel p S ≤ j)
    (hcent : ∀ x : S, orderOf x = p → ∀ I : Subgroup S,
      GLAPComponent p (Subgroup.centralizer ({x} : Set S)) I → kLevel p (PSimple p I) ≤ j) :
    DownLe p j S := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro α hα I hI
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
  obtain ⟨s, rfl, hsp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout α hα
  by_cases hs1 : s = 1
  · subst hs1
    have hfix : fixSubgroup (MulAut.conj (1 : S)) = ⊤ := by
      ext g; simp [mem_fixSubgroup]
    rw [hfix] at hI
    have hIt := eq_top_of_glaPComponent_top hI
    subst hIt
    obtain ⟨e⟩ := nonempty_pSimple_top_equiv hp hnc hI
    rw [kLevel_congr e]
    exact htop
  · have hord : orderOf s = p := orderOf_eq_prime hsp hs1
    rw [fixSubgroup_conj_eq] at hI
    exact hcent s hord I hI

theorem downLe_of_small_centralizers {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2) {p j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (htop : kLevel p S ≤ j)
    (hsmall : ∀ x : S, orderOf x = p → Nat.card (Subgroup.centralizer ({x} : Set S)) < 60) :
    DownLe p j S :=
  downLe_of_centralizers hnc hout hp hp2 htop fun x hx I hI =>
    (false_of_glaPComponent_of_solvable hp
      (CFSG.GroupTheory.groups_order_below_sixty_solvable (hsmall x hx)) hI).elim

theorem card_centralizer_of_model {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {S : Type} [Group S]
    (b : ↥P ≃* S) (x : S) :
    Nat.card (Subgroup.centralizer ({x} : Set S)) =
      Nat.card ↥(Subgroup.centralizer ({((b.symm x : P) : Equiv.Perm (Fin n))} : Set _) ⊓ P) := by
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype,
    Subgroup.card_map_of_injective P.subtype_injective,
    ← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv b.symm x,
    Subgroup.card_map_of_injective b.symm.injective]

theorem kdSporRow_three_of_perm {name : TauCeti.SporadicName} {n : ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : ↥P ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hs : IsSimpleGroup ↥P)
    (hcard : ¬ (Nat.card ↥P).Prime)
    (hsmall : ∀ x ∈ P, orderOf x = 3 →
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) < 60) :
    KDSporRow name 3 := by
  set G := (TauCeti.CFSGIndex.sporadic name).Group
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr b).1 hs
  haveI : Finite G := Finite.of_equiv _ b.toEquiv
  have hcG : Nat.card G = Nat.card ↥P := (Nat.card_congr b.toEquiv).symm
  have hnc : ∃ a c : G, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcG]; exact hcard)
  have hout := hOut G inferInstance hnc name ⟨MulEquiv.refl _⟩
  have hsm : ∀ x : G, orderOf x = 3 → Nat.card (Subgroup.centralizer ({x} : Set G)) < 60 := by
    intro x hx
    rw [card_centralizer_of_model b x]
    refine hsmall _ (b.symm x).2 ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  refine ⟨fun h2 => downLe_of_small_centralizers hnc hout Nat.prime_three (by norm_num)
      (kLevel_le_two ⟨_, h2, ⟨MulEquiv.refl _⟩⟩) hsm,
    fun h3 => downLe_of_small_centralizers hnc hout Nat.prime_three (by norm_num)
      (kLevel_le_three ⟨_, h3, ⟨MulEquiv.refl _⟩⟩) hsm⟩

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem kdSporRow_M11_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KDSporRow .M11 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  refine kdSporRow_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num) fun x hx h3 => ?_
  exact check_card_lt m11S3Data rep_m11A rep_m11B Certificates.certificate13511.1
    (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem kdSporRow_M12_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KDSporRow .M12 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  refine kdSporRow_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) fun x hx h3 => ?_
  exact check_card_lt m12S3Data rep_m12A rep_m12B Certificates.certificate13511.2.1
    (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem kdSporRow_M22_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KDSporRow .M22 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  refine kdSporRow_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num) fun x hx h3 => ?_
  exact check_card_lt m22S3Data rep_m22A rep_m22B Certificates.certificate13511.2.2.1
    (by decide) x hx h3

end CFSG.LocalAnalysis.GLTheoremA.KDSpor
