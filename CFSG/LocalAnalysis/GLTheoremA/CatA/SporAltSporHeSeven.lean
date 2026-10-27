module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporAll
public import Certificates.Certificate10130

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426

theorem check_sylow_sound (D : Data) {A B : Equiv.Perm (Fin D.n)} (hA : Rep D.n D.A A)
    (hB : Rep D.n D.B B) (h : check D = true) :
    closure (permsA D.n D.QGens) ≤ closure {A, B} ∧
      Nat.card (closure (permsA D.n D.QGens)) = D.N3 ∧
      ∀ l < D.QGens.size, validA D.n D.QGens[l]! = true := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, -⟩, -⟩, -⟩, -⟩, hlines⟩, hsift⟩, -⟩, -⟩, -⟩, hcases⟩ := h
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
  refine ⟨?_, linesOK3_card hlt hlines, fun l hl => enumOK_gens_valid (linesOK3_parts hlines).1 hl⟩
  rw [closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact hmemP (rep_of_validA (enumOK_gens_valid (linesOK3_parts hlines).1 hl))
    (allLt_spec hsift hl)

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem exists_abelian_of_alt7_comp {Q : Type} [Group Q] [Finite Q] {k : Q} (hk : orderOf k = 3)
    (hC : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 7560) {J : Subgroup Q}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) J) (hA : IsAltPType 3 J 7) :
    ∃ H : Subgroup Q, Nat.card H = 27 ∧ ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hA
  have hJC : J ≤ Subgroup.centralizer ({k} : Set Q) := hJ.1
  have hPQ : Nat.card (PQuot 3 J) = 2520 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 7 (by norm_num)]
    decide
  have hJcard : Nat.card ↥J = Nat.card (PQuot 3 J) * Nat.card (GLAPPrimeCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hJdvd : Nat.card ↥J ∣ 7560 := (Subgroup.card_dvd_of_le hJC).trans hC
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
  have hcore1 : Nat.card (GLAPPrimeCore 3 ↥J) = 1 := by
    rw [hJcard, hPQ, show (7560 : ℕ) = 2520 * 3 by norm_num] at hJdvd
    have h3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2520) hJdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact h
    · rw [h] at hcop
      norm_num at hcop
  have hcore : GLAPPrimeCore 3 ↥J = ⊥ := Subgroup.eq_bot_of_card_eq _ hcore1
  have hJ2520 : Nat.card ↥J = 2520 := by rw [hJcard, hPQ, hcore1]
  have hkJ : k ∉ J := by
    intro hkJ
    have hcA : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hwc : (QuotientGroup.mk (⟨k, hkJ⟩ : ↥J) : PQuot 3 J) ∈ Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJC u.2)
    have h1 : e (QuotientGroup.mk (⟨k, hkJ⟩ : ↥J)) ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff] at hwc ⊢
      intro g
      obtain ⟨u, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hwc u]
    rw [hcA, Subgroup.mem_bot] at h1
    have h2 : (QuotientGroup.mk (⟨k, hkJ⟩ : ↥J) : PQuot 3 J) = 1 :=
      e.injective (h1.trans (map_one e).symm)
    have h3 : (⟨k, hkJ⟩ : ↥J) ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff _).1 h2
    rw [hcore, Subgroup.mem_bot] at h3
    have hk1 : k = 1 := congrArg Subtype.val h3
    rw [hk1, orderOf_one] at hk
    norm_num at hk
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥J) := inferInstance
  have hS : Nat.card ↥(S : Subgroup ↥J) = 3 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hJ2520, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)]
  have hScomm := IsPGroup.commutative_of_card_eq_prime_sq hS
  set S' : Subgroup Q := (S : Subgroup ↥J).map J.subtype with hS'def
  have hS'card : Nat.card ↥S' = 9 := by
    rw [hS'def, Subgroup.card_map_of_injective J.subtype_injective, hS]
    norm_num
  have hS'J : S' ≤ J := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hS'comm : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hScomm ⟨a, ha⟩ ⟨b, hb⟩
    have h' := congrArg (fun x : ↥(S : Subgroup ↥J) => ((x : ↥J) : Q)) this
    simpa using h'
  have hcomm : ∀ (s : ↥S') (z : ↥(Subgroup.zpowers k)),
      Commute (S'.subtype s) ((Subgroup.zpowers k).subtype z) := by
    rintro ⟨s, hs⟩ ⟨z, hz⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hsk : Commute s k := Subgroup.mem_centralizer_singleton_iff.1 (hJC (hS'J hs))
    exact hsk.zpow_right n
  let φ : ↥S' × ↥(Subgroup.zpowers k) →* Q :=
    MonoidHom.noncommCoprod S'.subtype (Subgroup.zpowers k).subtype hcomm
  have hφ : ∀ x, φ x = (x.1 : Q) * (x.2 : Q) := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨s, hs⟩, ⟨z, hz⟩⟩ h1
    rw [hφ] at h1
    have hzs : z = s⁻¹ := (eq_inv_of_mul_eq_one_right h1)
    have hzJ : z ∈ J := hzs ▸ J.inv_mem (hS'J hs)
    have hz1 : z = 1 := by
      classical
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 ((mem_zpowers_iff_mem_range_orderOf).1 hz)
      rw [Finset.mem_range, hk] at hn
      interval_cases n
      · exact pow_zero k
      · exact absurd (by simpa using hzJ) hkJ
      · exfalso
        apply hkJ
        have h4 : (k ^ 2) ^ 2 = k := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ← hk, pow_orderOf_eq_one,
            one_mul]
        rw [← h4]
        exact J.pow_mem hzJ 2
    have hs1 : s = 1 := by
      rw [hz1] at hzs
      exact inv_eq_one.1 hzs.symm
    subst hz1
    subst hs1
    rfl
  refine ⟨φ.range, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hS'card,
      Nat.card_zpowers, hk]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext (hS'comm _ x.1.2 _ y.1.2)) (Subtype.ext ?_)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2.2
    show (x.2 : Q) * y.2 = y.2 * x.2
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]

theorem false_of_alt7_comp {Q : Type} [Group Q] [Finite Q] {m : ℕ} (hQ : Nat.card Q = 3 ^ 3 * m)
    (hm : ¬ 3 ∣ m) {P : Subgroup Q} (hP : Nat.card P = 27) {a b : Q} (ha : a ∈ P) (hb : b ∈ P)
    (hab : a * b ≠ b * a) {k : Q} (hk : orderOf k = 3)
    (hC : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 7560) {J : Subgroup Q}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) J) (hA : IsAltPType 3 J 7) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH, hHc⟩ := exists_abelian_of_alt7_comp hk hC hJ hA
  have hfac : (Nat.card Q).factorization 3 = 3 := by
    rw [hQ]; exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three hm
  let SH : Sylow 3 Q := Sylow.ofCard H (by rw [hH, hfac]; norm_num)
  let SP : Sylow 3 Q := Sylow.ofCard P (by rw [hP, hfac]; norm_num)
  let f : (SP : Subgroup Q) ≃* (SH : Subgroup Q) := Sylow.equiv SP SH
  have hHc' : ∀ x y : ↥(SH : Subgroup Q), x * y = y * x := fun x y =>
    Subtype.ext (hHc _ (by simpa [SH] using x.2) _ (by simpa [SH] using y.2))
  apply hab
  have h := congrArg (fun z => ((f.symm z : ↥(SP : Subgroup Q)) : Q))
    (hHc' (f ⟨a, by simpa [SP] using ha⟩) (f ⟨b, by simpa [SP] using hb⟩))
  simpa only [← map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] using h

theorem facts_of_check (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data) (n' : ℕ)
    (hn : D.n = n') (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin n')}
    (hA : CFSG.Monster.B.Co2.Rep n' D.A A) (hB : CFSG.Monster.B.Co2.Rep n' D.B B)
    (P : Subgroup (Equiv.Perm (Fin n'))) (hP : P = Subgroup.closure {A, B}) {m : ℕ}
    (hord : D.ord = 3 ^ 3 * m) (hN3 : D.N3 = 27) (hn0 : 0 < D.n) (h2 : 2 ≤ D.QGens.size)
    (hne : (D.QGens[0]!)[(D.QGens[1]!)[0]!]! ≠ (D.QGens[1]!)[(D.QGens[0]!)[0]!]!)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 7560) :
    Nat.card ↥P = 3 ^ 3 * m ∧
      (∃ Pq : Subgroup ↥P, Nat.card Pq = 27 ∧ ∃ a ∈ Pq, ∃ b ∈ Pq, a * b ≠ b * a) ∧
      ∀ k : ↥P, orderOf k = 3 → Nat.card (Subgroup.centralizer ({k} : Set ↥P)) ∣ 7560 := by
  subst hn
  subst hP
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  obtain ⟨hle, hQcard, hval⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_sylow_sound D hA hB hD
  refine ⟨hcardP.trans hord, ?_, ?_⟩
  · set Qs := Subgroup.closure (CFSG.RankThree.Native.permsA D.n D.QGens)
    have r0 := CFSG.RankThree.Native.rep_of_validA (hval 0 (by omega))
    have r1 := CFSG.RankThree.Native.rep_of_validA (hval 1 (by omega))
    set g0 := CFSG.Monster.B.Co2.permOfArr D.n D.QGens[0]!
    set g1 := CFSG.Monster.B.Co2.permOfArr D.n D.QGens[1]!
    have hg0 : g0 ∈ Qs := Subgroup.subset_closure ⟨0, by show 0 < D.QGens.size; omega, rfl⟩
    have hg1 : g1 ∈ Qs := Subgroup.subset_closure ⟨1, by show 1 < D.QGens.size; omega, rfl⟩
    refine ⟨Qs.subgroupOf (Subgroup.closure {A, B}), ?_, ⟨g0, hle hg0⟩, hg0, ⟨g1, hle hg1⟩, hg1, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hQcard, hN3]
    · intro h
      apply hne
      have h' := congrArg (fun g : ↥(Subgroup.closure {A, B}) => ((g : Equiv.Perm (Fin D.n))
        ⟨0, hn0⟩ : ℕ)) h
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at h'
      rw [r1.apply hn0, r0 (g1 ⟨0, hn0⟩), r0.apply hn0, r1 (g0 ⟨0, hn0⟩)]
      exact h'
  · intro x hx
    have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
    have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
      (Subgroup.closure {A, B}) x
    have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
        Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
          Subgroup.closure {A, B}) := by
      rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
    rw [hcc', hcc]
    exact hsmall c hc

theorem altRow_seven_of_facts {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a) {m : ℕ}
    (hm : ¬ 3 ∣ m) (hQ : Nat.card Q = 3 ^ 3 * m)
    (hP : ∃ Pq : Subgroup Q, Nat.card Pq = 27 ∧ ∃ a ∈ Pq, ∃ b ∈ Pq, a * b ≠ b * a)
    (hC : ∀ k : Q, orderOf k = 3 → Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 7560) :
    AltRow 7 s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 K hK hA
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num) hcen
      hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  rw [KDSpor.fixSubgroup_conj_eq] at hK
  obtain ⟨Pq, hPq, a, ha, c, hc, hac⟩ := hP
  refine false_of_alt7_comp (Q := S) (m := m) (P := Pq.map φ.symm.toMonoidHom)
    ((Nat.card_congr φ.toEquiv).trans hQ) hm
    (by rw [Subgroup.card_map_of_injective φ.symm.injective, hPq]) ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    (fun h => hac (by simpa using congrArg φ h)) hxo ?_ hK hA
  have hk : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq, hxo]
  rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective,
    CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv]
  exact hC _ hk

set_option maxRecDepth 100000 in
theorem nonab_of_rep {gs : Array (Array ℕ)} {P : Subgroup (Equiv.Perm (Fin 8330))}
    (h2 : 2 ≤ gs.size) (hle : Subgroup.closure (CFSG.RankThree.Native.permsA 8330 gs) ≤ P)
    (hcard : Nat.card ↥(Subgroup.closure (CFSG.RankThree.Native.permsA 8330 gs)) = 27)
    (hrep : ∀ i < 2, CFSG.Monster.B.Co2.Rep 8330 gs[i]! (CFSG.Monster.B.Co2.permOfArr 8330 gs[i]!))
    (hne : (gs[0]!)[(gs[1]!)[0]!]! ≠ (gs[1]!)[(gs[0]!)[0]!]!) :
    ∃ Pq : Subgroup ↥P, Nat.card Pq = 27 ∧ ∃ a ∈ Pq, ∃ b ∈ Pq, a * b ≠ b * a := by
  set Qs := Subgroup.closure (CFSG.RankThree.Native.permsA 8330 gs)
  have r0 := hrep 0 (by norm_num)
  have r1 := hrep 1 (by norm_num)
  set g0 := CFSG.Monster.B.Co2.permOfArr 8330 gs[0]!
  set g1 := CFSG.Monster.B.Co2.permOfArr 8330 gs[1]!
  have hg0 : g0 ∈ Qs := Subgroup.subset_closure ⟨0, by change 0 < gs.size; omega, rfl⟩
  have hg1 : g1 ∈ Qs := Subgroup.subset_closure ⟨1, by change 1 < gs.size; omega, rfl⟩
  refine ⟨Qs.subgroupOf P, ?_, ⟨g0, hle hg0⟩, hg0, ⟨g1, hle hg1⟩, hg1, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  · intro h
    apply hne
    have hn0 : 0 < 8330 := by norm_num
    have h' := congrArg (fun g : ↥P => ((g : Equiv.Perm (Fin 8330)) ⟨0, hn0⟩ : ℕ)) h
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at h'
    rw [r1.apply hn0, r0 (g1 ⟨0, hn0⟩), r0.apply hn0, r1 (g0 ⟨0, hn0⟩)]
    exact h'

set_option maxRecDepth 100000 in
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem altRow_He_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : AltRow 7 .He := by
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have hcard : Nat.card ↥CFSG.Sporadic.HeldB.heP = 3 ^ 3 * 149273600 := by
    rw [CFSG.Sporadic.HeldB.card_heP]
    norm_num
  have hc : decide (2 ≤ heS3QGens.size) = true ∧
      ((heS3QGens[0]!)[(heS3QGens[1]!)[0]!]! != (heS3QGens[1]!)[(heS3QGens[0]!)[0]!]!) = true :=
    Bool.and_eq_true_iff.1 Certificates.certificate10130
  obtain ⟨hle, hQcard, hrep⟩ := Certificates.certificate13515.2.2.2.2.2
  have hP := nonab_of_rep (of_decide_eq_true hc.1) hle hQcard hrep (bne_iff_ne.1 hc.2)
  have hC : ∀ k : ↥CFSG.Sporadic.HeldB.heP, orderOf k = 3 →
      Nat.card (Subgroup.centralizer ({k} : Set ↥CFSG.Sporadic.HeldB.heP)) ∣ 7560 := by
    intro k hk
    have hk3 : orderOf (k : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe]; exact hk
    rw [← Subgroup.card_map_of_injective CFSG.Sporadic.HeldB.heP.subtype_injective,
      map_centralizer_subtype CFSG.Sporadic.HeldB.heP k]
    rcases he3_card k.2 hk3 with h | h <;> rw [h] <;> norm_num
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  have hfin : Finite ↥CFSG.Sporadic.HeldB.heP :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact @altRow_seven_of_facts .He _ _ hfin hs hOut (e.symm.trans (hbr .He).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [hcard]; norm_num)) 149273600 (by norm_num) hcard hP hC




















theorem i1415SevenSporS_of_residual2
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : AltRow 7 .B ∧ AltRow 7 .M) : I1415SevenSporS :=
  i1415SevenSporS_of_residual hOut hbr hOrd hb ⟨hres.1, hres.2, altRow_He_seven hOut hbr⟩

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
