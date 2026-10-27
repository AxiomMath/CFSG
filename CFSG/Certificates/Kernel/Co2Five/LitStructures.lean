module

public import CFSG.RankThree.Native.Co2FiveStructures
public import CFSG.RankThree.Native.Co2FiveMats
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.PartOne.KS.ConjWords
public import CFSG.Certificates.Kernel.Misc.EnumBfsOfOK
public import CFSG.Sporadic.Co2Cert.Order

public noncomputable section

namespace CFSG.RankThree.Native.Co2FiveLit

open CFSG.RankThree.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open scoped commutatorElement

structure Co2FiveC1LitFacts : Prop where
  cEnum : enumOK 2300 co2FiveC1GenArrs co2FiveKeyPts co2FiveC1Lit = true
  cSize : co2FiveC1Lit.pts.size = 600
  dEnum : enumOK 2300 co2FiveDGenArrs co2FiveKeyPts co2FiveDLit = true
  dSize : co2FiveDLit.pts.size = 60
  commX : allLt 3 (fun k => commA 2300 co2FiveC1GenArrs[k]! co2FiveX1Arr) = true
  bComm : eqA 2300 (compA 2300 (co2BWordG co2FiveC1GenArrs) (co2BWordH co2FiveC1GenArrs))
    (compA 2300 co2FiveC1GenArrs[2]!
      (compA 2300 (co2BWordH co2FiveC1GenArrs) (co2BWordG co2FiveC1GenArrs))) = true
  norm : allLt 3 (fun k => allLt 2 fun l => co2FiveDLit.pts.toList.any
    (eqA 2300 (conjA 2300 co2FiveC1GenArrs[k]! co2FiveDGenArrs[l]!))) = true
  comm : allLt 3 (fun k => allLt 3 fun l => co2FiveDLit.pts.toList.any
    (eqA 2300 (commutatorA 2300 co2FiveC1GenArrs[k]! co2FiveC1GenArrs[l]!))) = true
  nonab : commA 2300 co2FiveDGenArrs[0]! co2FiveDGenArrs[1]! = false
  simple : CFSG.RankThree.PartOne.conjWordsOK 2300 co2FiveDLit co2FiveDGenArrs co2FiveSimpSel
    co2FiveSimpW = true
  cent : allLt 600 (fun k => !(commA 2300 co2FiveC1Lit.pts[k]! co2FiveDGenArrs[0]! &&
      commA 2300 co2FiveC1Lit.pts[k]! co2FiveDGenArrs[1]!) ||
    (List.range 5).any fun e => eqA 2300 co2FiveC1Lit.pts[k]! (powArr 2300 co2FiveX1Arr e)) =
    true
  tValid : validA 2300 co2FiveTArr = true

@[expose] def Co2FiveLitChecks : Prop :=
  co2FiveChainCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveC0Lit = true ∧
    co2FiveQCheck co2FiveQLit co2FiveLines = true ∧
    co2FiveC0Check co2FiveC0Lit co2FiveQLit = true ∧ Co2FiveC1LitFacts

variable [Fact Co2FiveLitChecks]

theorem co2FiveKeyPts_lt : ∀ p ∈ co2FiveKeyPts, p < 2300 := by decide

theorem mem_co2P_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 2300)} (hG : Rep 2300 g G)
    (h : siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 g = true) :
    G ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1 hG).1 h

structure Co2FiveChainFacts : Prop where
  sift : ∀ a ∈ co2FiveSiftArrs,
    siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 a = true
  z0 : co2FiveZArr[0]! = 0
  z1 : co2FiveZArr[1]! = 1
  z2 : co2FiveZArr[2]! = 2
  z3 : co2FiveZArr[3]! = 3
  fix0 : fixLevCount 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveZArr 0 = 10
  fix1 : fixLevCount 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveZArr 1 = 3
  fix2 : fixLevCount 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveZArr 2 = 2
  fix3 : fixLevCount 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveZArr 3 = 2
  tail : tailOK 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveZArr co2FiveZPows 2 4
    (idA 2300) = true
  rels : ∀ r ∈ co2FiveRels, r.2.2 < co2FiveX0PowArrs.size ∧ r.1 < co2BaseArr.size ∧
    r.2.1 < co2BaseArr.size ∧ (co2FiveX0PowArrs[r.2.2]!)[co2BaseArr[r.1]!]! = co2BaseArr[r.2.1]!
  ptail : ptailOK 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr co2FiveX0Arr
    co2FiveX0PowArrs co2FiveRels co2FiveC0Lit.pts.toList 6 0 (idA 2300) = true

theorem co2Five_chain_facts : Co2FiveChainFacts := by
  have h := (Fact.out : Co2FiveLitChecks).1
  simp only [co2FiveChainCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, ⟨⟨⟨h20, h21⟩, h22⟩, h23⟩⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h20, h21, h22, h23, h3, h4, h5, h6, h7, fun r hr => ?_, h9⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h8 r hr
  exact ⟨a, b, c, d⟩

theorem co2Five_sift {a : Array ℕ} (ha : a ∈ co2FiveSiftArrs) :
    siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 a = true :=
  co2Five_chain_facts.sift a ha

structure Co2FiveQFacts : Prop where
  enum : enumOK 2300 co2FiveQGenArrs co2FiveKeyPts co2FiveQLit = true
  size : co2FiveQLit.pts.size = 125
  pow : allLt 125 (fun k => eqA 2300 (powArr 2300 co2FiveQLit.pts[k]! 5) (idA 2300)) = true
  cover : allLt 125 (fun k => eqA 2300 co2FiveQLit.pts[k]! (idA 2300) ||
    (List.range 31).any fun j => (List.range 5).any fun e =>
      eqA 2300 co2FiveQLit.pts[k]! (powArr 2300 co2FiveLines[j]! e)) = true
  dist : allLt 31 (fun j => allLt 31 fun j' => j == j' ||
    allLt 5 fun e => !(eqA 2300 co2FiveLines[j]! (powArr 2300 co2FiveLines[j']! e))) = true
  lines : allLt 31 (fun j => validA 2300 co2FiveLines[j]! &&
    eqA 2300 (powArr 2300 co2FiveLines[j]! 5) (idA 2300) &&
    !(eqA 2300 co2FiveLines[j]! (idA 2300)) &&
    co2FiveQLit.pts.toList.any (eqA 2300 co2FiveLines[j]!)) = true
  hValid : allLt 31 (fun j => validA 2300 (co2FiveHArr j)) = true

theorem co2Five_Q_facts : Co2FiveQFacts := by
  have h := (Fact.out : Co2FiveLitChecks).2.1
  simp only [co2FiveQCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hE, hS⟩, hP⟩, hC⟩, hD⟩, hL⟩, hH⟩ := h
  exact ⟨hE, hS, hP, hC, hD, hL, hH⟩

theorem co2FiveLines_get {j : ℕ} (hj : j < 31) : co2FiveLines[j]! = co2FiveLineArr j := by
  rw [co2FiveLines, getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]

theorem co2FiveLine_facts (j : Fin 31) :
    validA 2300 (co2FiveLineArr j) = true ∧
    eqA 2300 (powArr 2300 (co2FiveLineArr j) 5) (idA 2300) = true ∧
    eqA 2300 (co2FiveLineArr j) (idA 2300) = false ∧
    co2FiveQLit.pts.toList.any (eqA 2300 (co2FiveLineArr j)) = true := by
  have h := allLt_spec co2Five_Q_facts.lines j.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [co2FiveLines_get j.2] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_co2FiveLine (j : Fin 31) : Rep 2300 (co2FiveLineArr j) (co2FiveLine j) :=
  rep_of_validA (co2FiveLine_facts j).1

theorem co2FiveLineArr_zero : co2FiveLineArr 0 = co2FiveX0Arr := by simp [co2FiveLineArr]

theorem co2FiveLineArr_one : co2FiveLineArr 1 = co2FiveX1Arr := by simp [co2FiveLineArr]

theorem rep_co2FiveLine_zero : Rep 2300 co2FiveX0Arr (co2FiveLine 0) := by
  have h := rep_co2FiveLine 0
  rwa [Fin.val_zero, co2FiveLineArr_zero] at h

theorem rep_co2FiveLine_one : Rep 2300 co2FiveX1Arr (co2FiveLine 1) := by
  have h := rep_co2FiveLine 1
  rwa [Fin.val_one, co2FiveLineArr_one] at h

theorem co2FiveQ_spec :
    (∀ x, x ∈ co2FiveQ ↔ ∃ k < co2FiveQLit.pts.size,
      permOfArr 2300 co2FiveQLit.pts[k]! = x) ∧
    Nat.card co2FiveQ = 125 ∧ ∀ k < co2FiveQLit.pts.size,
      validA 2300 co2FiveQLit.pts[k]! = true := by
  obtain ⟨h1, h2, h3⟩ := enumOK_spec co2FiveKeyPts_lt co2Five_Q_facts.enum
  exact ⟨h1, h2.trans co2Five_Q_facts.size, h3⟩

theorem co2FiveQ_elem {x : Equiv.Perm (Fin 2300)} (hx : x ∈ co2FiveQ) :
    ∃ k < 125, Rep 2300 co2FiveQLit.pts[k]! x := by
  obtain ⟨k, hk, rfl⟩ := (co2FiveQ_spec.1 x).1 hx
  exact ⟨k, co2Five_Q_facts.size ▸ hk, rep_of_validA (co2FiveQ_spec.2.2 k hk)⟩

theorem co2FiveQ_le_P :
    co2FiveQ ≤ co2P := by
  rw [co2FiveQ, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := hk
  refine mem_co2P_of_sift (rep_of_validA (enumOK_gens_valid co2Five_Q_facts.enum hk))
    (co2Five_sift ?_)
  have hks : k < co2FiveQGenArrs.size := hk
  have hmem : co2FiveQGenArrs[k]! ∈ co2FiveQGenArrs.toList := by
    rw [getElem!_pos co2FiveQGenArrs k hks]
    exact Array.getElem_mem_toList hks
  rw [co2FiveSiftArrs]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr hmem))

theorem co2FiveQ_pow_five {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2FiveQ) : g ^ 5 = 1 := by
  obtain ⟨k, hk, hkg⟩ := co2FiveQ_elem hg
  exact (eqA_iff (rep_powArr hkg 5) rep_idA).1 (allLt_spec co2Five_Q_facts.pow hk)

theorem card_co2FiveQ : Nat.card co2FiveQ = 125 := co2FiveQ_spec.2.1

theorem co2FiveLine_mem_Q (j : Fin 31) : co2FiveLine j ∈ co2FiveQ :=
  enumOK_mem_of_any co2FiveKeyPts_lt co2Five_Q_facts.enum (rep_co2FiveLine j)
    (co2FiveLine_facts j).2.2.2

theorem co2FiveLine_ne_one (j : Fin 31) : co2FiveLine j ≠ 1 := fun h => by
  have := (eqA_iff (rep_co2FiveLine j) rep_idA).2 h
  rw [(co2FiveLine_facts j).2.2.1] at this
  exact Bool.false_ne_true this

theorem co2FiveLine_pow_five (j : Fin 31) : co2FiveLine j ^ 5 = 1 :=
  (eqA_iff (rep_powArr (rep_co2FiveLine j) 5) rep_idA).1 (co2FiveLine_facts j).2.1

theorem exponent_co2FiveQ : Monoid.exponent co2FiveQ = 5 := by
  have hdvd : Monoid.exponent co2FiveQ ∣ 5 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (co2FiveQ_pow_five g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 h
    have := congrArg Subtype.val
      (hs.elim (⟨co2FiveLine 0, co2FiveLine_mem_Q 0⟩ : co2FiveQ) 1)
    exact co2FiveLine_ne_one 0 this
  · exact h

theorem factorization_card_co2P_five :
    (Nat.card co2P).factorization 5 = 3 := by
  rw [card_co2P, show (42305421312000 : ℕ) = 5 ^ 3 * 338443370496 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem co2FiveQ_sylow :
    ∃ S : Sylow 5 co2P, (S : Subgroup co2P) = co2FiveQ.subgroupOf co2P := by
  have hcard : Nat.card (co2FiveQ.subgroupOf co2P) = 5 ^ (Nat.card co2P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co2FiveQ_le_P).toEquiv, card_co2FiveQ,
      factorization_card_co2P_five]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem co2FiveQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j)) ∧
      Function.Injective (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j)) := by
  apply prime_subgroups_eq_range co2FiveLine co2FiveLine_mem_Q co2FiveLine_ne_one
    co2FiveLine_pow_five
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := co2FiveQ_elem hg
    have h := allLt_spec co2Five_Q_facts.cover hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with h | ⟨j, hj, e, he, hje⟩
    · exact absurd ((eqA_iff hkg rep_idA).1 h) hg1
    · rw [co2FiveLines_get hj] at hje
      exact ⟨⟨j, hj⟩, e, (eqA_iff hkg (rep_powArr (rep_co2FiveLine ⟨j, hj⟩) e)).1 hje⟩
  · intro j j' k hk hjj'
    have h := allLt_spec (allLt_spec co2Five_Q_facts.dist j.2) j'.2
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact Fin.ext h
    · have h' := allLt_spec h hk
      rw [co2FiveLines_get j.2, co2FiveLines_get j'.2, Bool.not_eq_true'] at h'
      have := (eqA_iff (rep_co2FiveLine j) (rep_powArr (rep_co2FiveLine j') k)).2 hjj'
      rw [h'] at this
      exact absurd this Bool.false_ne_true

theorem rep_co2FiveH (j : Fin 31) : Rep 2300 (co2FiveHArr j) (co2FiveTransporter j) :=
  rep_of_validA (allLt_spec co2Five_Q_facts.hValid j.2)

theorem co2FiveTransporter_mem_P
    (j : Fin 31) : co2FiveTransporter j ∈ co2P := by
  refine mem_co2P_of_sift (rep_co2FiveH j) (co2Five_sift ?_)
  rw [co2FiveSiftArrs, List.mem_append]
  exact Or.inr (List.mem_map.2 ⟨j, List.mem_range.2 j.2, rfl⟩)

theorem co2FiveTransporter_eq_one {j : Fin 31} (hj : (j : ℕ) ≤ 1) : co2FiveTransporter j = 1 := by
  rw [co2FiveTransporter, co2FiveHArr, ite_eq_left hj]
  exact permOfArr_eq_of_rep rep_idA

theorem co2FiveTransporter_spec
    (j : Fin 31) :
    co2FiveTransporter j ∈ co2P ∧
      co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
        (co2FiveTransporter j)⁻¹ = co2FiveLine j := by
  refine ⟨co2FiveTransporter_mem_P j, ?_⟩
  by_cases h0 : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext h0
    subst hj
    rw [co2FiveTransporter_eq_one (by norm_num)]
    simp [co2FiveRecordOf, co2FiveRepLine]
  · have hrec : co2FiveRepLine (co2FiveRecordOf j) = 1 := by
      simp [co2FiveRecordOf, co2FiveRepLine, h0]
    rw [hrec]
    by_cases h1 : (j : ℕ) = 1
    · have hj : j = 1 := Fin.ext h1
      subst hj
      rw [co2FiveTransporter_eq_one (by norm_num)]
      simp
    · have hlt : ¬ (j : ℕ) ≤ 1 := by omega
      have hval : validA 2300 (co2FiveHArr j) = true := allLt_spec co2Five_Q_facts.hValid j.2
      have hrep := rep_conjA hval rep_co2FiveLine_one
      have hline : co2FiveLineArr j = conjA 2300 (co2FiveHArr j) co2FiveX1Arr := by
        rw [co2FiveLineArr, ite_eq_right h0, ite_eq_right h1]
      have e1 : co2FiveLine j = permOfArr 2300 (co2FiveHArr j) * co2FiveLine 1 *
          (permOfArr 2300 (co2FiveHArr j))⁻¹ := by
        rw [co2FiveLine, hline]
        exact permOfArr_eq_of_rep hrep
      rw [e1]
      rfl

structure Co2FiveC0Facts : Prop where
  enum : enumOK 2300 co2FiveC0GenArrs co2FiveKeyPts co2FiveC0Lit = true
  size : co2FiveC0Lit.pts.size = 3000
  comm : allLt 2 (fun k => commA 2300 co2FiveC0GenArrs[k]! co2FiveX0Arr) = true
  aMem : allLt 2 (fun k => co2FiveC0Lit.pts.toList.any (eqA 2300 co2FiveAGenArrs[k]!)) = true
  norm : allLt 2 (fun k => allLt 2 fun l => co2FiveQLit.pts.toList.any
    (eqA 2300 (conjA 2300 co2FiveC0GenArrs[k]! co2FiveAGenArrs[l]!))) = true
  cent : allLt 3000 (fun k => !(commA 2300 co2FiveC0Lit.pts[k]! co2FiveAGenArrs[0]! &&
      commA 2300 co2FiveC0Lit.pts[k]! co2FiveAGenArrs[1]!) ||
    (List.range 5).any fun e => eqA 2300 co2FiveC0Lit.pts[k]! (powArr 2300 co2FiveX0Arr e)) =
    true

theorem co2Five_C0_facts : Co2FiveC0Facts := by
  have h := (Fact.out : Co2FiveLitChecks).2.2.1
  simp only [co2FiveC0Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem co2FiveAGenArrs_eq : co2FiveAGenArrs = co2FiveQGenArrs := rfl

theorem co2FiveA_eq_Q : co2FiveA = co2FiveQ := by
  rw [co2FiveA, co2FiveQ, co2FiveAGenArrs_eq]

theorem rep_c0gen {k : ℕ} (hk : k < 2) :
    Rep 2300 co2FiveC0GenArrs[k]! (permOfArr 2300 co2FiveC0GenArrs[k]!) :=
  rep_of_validA (enumOK_gens_valid co2Five_C0_facts.enum hk)

theorem rep_agen {k : ℕ} (hk : k < 2) :
    Rep 2300 co2FiveAGenArrs[k]! (permOfArr 2300 co2FiveAGenArrs[k]!) :=
  rep_of_validA (enumOK_gens_valid co2Five_Q_facts.enum hk)

theorem co2FiveC0_le_centralizer : co2FiveC0 ≤ Subgroup.centralizer {co2FiveLine 0} := by
  rw [co2FiveC0, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 ((commA_iff (rep_c0gen hk)
    rep_co2FiveLine_zero).1 (allLt_spec co2Five_C0_facts.comm hk))

theorem co2FiveC0_le_P :
    co2FiveC0 ≤ co2P := by
  rw [co2FiveC0, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hks : k < co2FiveC0GenArrs.size := hk
  refine mem_co2P_of_sift (rep_c0gen hk) (co2Five_sift ?_)
  have hmem : co2FiveC0GenArrs[k]! ∈ co2FiveC0GenArrs.toList := by
    rw [getElem!_pos co2FiveC0GenArrs k hks]
    exact Array.getElem_mem_toList hks
  rw [co2FiveSiftArrs]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr hmem)))

theorem card_co2FiveC0 : Nat.card co2FiveC0 = 3000 :=
  (enumOK_spec co2FiveKeyPts_lt co2Five_C0_facts.enum).2.1.trans co2Five_C0_facts.size

theorem rep_co2FiveX0Pow {e : ℕ} (he : e < co2FiveX0PowArrs.size) :
    Rep 2300 co2FiveX0PowArrs[e]! (co2FiveLine 0 ^ e) := by
  rw [getElem!_pos co2FiveX0PowArrs e he]
  simp only [co2FiveX0PowArrs, Array.getElem_ofFn]
  exact rep_powArr rep_co2FiveLine_zero e

theorem co2FiveC0_eq :
    co2FiveC0 = Subgroup.centralizer {co2FiveLine 0} ⊓ co2P := by
  apply le_antisymm (le_inf co2FiveC0_le_centralizer co2FiveC0_le_P)
  intro g hg
  have hg' : g ∈ Subgroup.centralizer {co2FiveLine 0} ⊓ co2Q.originalSubgroup := by
    rwa [co2Q_originalSubgroup]
  have F := co2Five_chain_facts
  have htail : ptailOK 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr co2FiveX0Arr
      co2FiveX0PowArrs co2FiveRels co2FiveC0Lit.pts.toList co2Q.baseCount 0 (idA 2300) =
        true := by
    rw [co2Q_baseCount]
    exact F.ptail
  obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK co2Q_chainArrays
    (chainCheckFacts co2Chain_check.1) co2Q_valid.1 rep_co2FiveLine_zero
    (fun e he => rep_co2FiveX0Pow he) F.rels htail hg'
  exact enumOK_mem_of_mem co2FiveKeyPts_lt co2Five_C0_facts.enum hre he

theorem co2FiveLine_zero_mem_A : co2FiveLine 0 ∈ co2FiveA := by
  rw [co2FiveA_eq_Q]
  exact co2FiveLine_mem_Q 0

theorem co2FiveA_le_C0 : co2FiveA ≤ co2FiveC0 := by
  rw [co2FiveA, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact enumOK_mem_of_any co2FiveKeyPts_lt co2Five_C0_facts.enum (rep_agen hk)
    (allLt_spec co2Five_C0_facts.aMem hk)

theorem co2FiveA_normal : (co2FiveA.subgroupOf co2FiveC0).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer co2FiveA_le_C0, co2FiveC0, co2FiveA]
  apply closure_le_normalizer_closure
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  have h := allLt_spec (allLt_spec co2Five_C0_facts.norm hk) hl
  have hmem := enumOK_mem_of_any co2FiveKeyPts_lt co2Five_Q_facts.enum
    (rep_conjA (enumOK_gens_valid co2Five_C0_facts.enum hk) (rep_agen hl)) h
  rwa [← co2FiveAGenArrs_eq] at hmem

theorem co2FiveCentA_eq :
    Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 =
      Subgroup.zpowers (co2FiveLine 0) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep co2FiveKeyPts_lt co2Five_C0_facts.enum hgC
    rw [co2Five_C0_facts.size] at hk
    have hc : ∀ l < 2, commA 2300 co2FiveC0Lit.pts[k]! co2FiveAGenArrs[l]! = true := by
      intro l hl
      have ha : permOfArr 2300 co2FiveAGenArrs[l]! ∈ co2FiveA :=
        Subgroup.subset_closure (mem_permsA hl)
      exact (commA_iff hkg (rep_agen hl)).2 (Subgroup.mem_centralizer_iff.1 hgA _ ha).symm
    have h := allLt_spec co2Five_C0_facts.cent hk
    rw [hc 0 (by norm_num), hc 1 (by norm_num)] at h
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨e, -, he⟩ := h
    rw [(eqA_iff hkg (rep_powArr rep_co2FiveLine_zero e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun a ha => ?_,
      co2FiveA_le_C0 co2FiveLine_zero_mem_A⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (co2FiveC0_le_centralizer (co2FiveA_le_C0 ha))

theorem co2Five_C1_facts : Co2FiveC1LitFacts := (Fact.out : Co2FiveLitChecks).2.2.2

theorem valid_c1gen {k : ℕ} (hk : k < 3) : validA 2300 co2FiveC1GenArrs[k]! = true :=
  enumOK_gens_valid co2Five_C1_facts.cEnum hk

theorem rep_c1gen {k : ℕ} (hk : k < 3) :
    Rep 2300 co2FiveC1GenArrs[k]! (permOfArr 2300 co2FiveC1GenArrs[k]!) :=
  rep_of_validA (valid_c1gen hk)

theorem rep_dgen' {l : ℕ} (hl : l < 2) :
    Rep 2300 co2FiveDGenArrs[l]! (permOfArr 2300 co2FiveDGenArrs[l]!) :=
  rep_of_validA (enumOK_gens_valid co2Five_C1_facts.dEnum hl)

theorem co2FiveC1GenArrs_zero : co2FiveC1GenArrs[0]! = co2FiveX1Arr := by
  simp [co2FiveC1GenArrs]

theorem c1gen_zero : permOfArr 2300 co2FiveC1GenArrs[0]! = co2FiveLine 1 := by
  rw [co2FiveC1GenArrs_zero]
  exact (permOfArr_eq_of_rep rep_co2FiveLine_one)

theorem c1gen_mem {k : ℕ} (hk : k < 3) : permOfArr 2300 co2FiveC1GenArrs[k]! ∈ co2FiveC1 :=
  Subgroup.subset_closure (mem_permsA hk)

theorem co2FiveLine_one_mem_C1 : co2FiveLine 1 ∈ co2FiveC1 := by
  rw [← c1gen_zero]
  exact c1gen_mem (by norm_num)

theorem co2FiveC1_le_centralizer : co2FiveC1 ≤ Subgroup.centralizer {co2FiveLine 1} := by
  rw [co2FiveC1, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 ((commA_iff (rep_c1gen hk)
    rep_co2FiveLine_one).1 (allLt_spec co2Five_C1_facts.commX hk))

theorem c1gen_mem_P {k : ℕ}
    (hk : k < 3) : permOfArr 2300 co2FiveC1GenArrs[k]! ∈ co2P := by
  have hks : k < co2FiveC1GenArrs.size := hk
  refine mem_co2P_of_sift (rep_c1gen hk) (co2Five_sift ?_)
  have hmem : co2FiveC1GenArrs[k]! ∈ co2FiveC1GenArrs.toList := by
    rw [getElem!_pos co2FiveC1GenArrs k hks]
    exact Array.getElem_mem_toList hks
  rw [co2FiveSiftArrs]
  simp only [List.mem_append]
  exact Or.inl (Or.inr hmem)

theorem co2FiveC1_le_P :
    co2FiveC1 ≤ co2P := by
  rw [co2FiveC1, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact c1gen_mem_P hk

theorem card_co2FiveC1 : Nat.card co2FiveC1 = 600 :=
  (enumOK_spec co2FiveKeyPts_lt co2Five_C1_facts.cEnum).2.1.trans co2Five_C1_facts.cSize

theorem rep_co2FiveZ : Rep 2300 co2FiveZArr (permOfArr 2300 co2FiveTArr * co2FiveLine 1 *
    (permOfArr 2300 co2FiveTArr)⁻¹) :=
  rep_conjA co2Five_C1_facts.tValid rep_co2FiveLine_one

theorem co2FiveT_mem_P :
    permOfArr 2300 co2FiveTArr ∈ co2P :=
  mem_co2P_of_sift (rep_of_validA co2Five_C1_facts.tValid) (co2Five_sift (by
    rw [co2FiveSiftArrs]
    simp))

theorem co2FiveZ_fix {p : Fin 2300} (hp : co2FiveZArr[(p : ℕ)]! = p) :
    (permOfArr 2300 co2FiveTArr * co2FiveLine 1 * (permOfArr 2300 co2FiveTArr)⁻¹) p = p :=
  Fin.ext ((rep_co2FiveZ p).symm.trans hp)

theorem card_centralizer_co2FiveZ_le :
    Nat.card (Subgroup.centralizer {permOfArr 2300 co2FiveTArr * co2FiveLine 1 *
      (permOfArr 2300 co2FiveTArr)⁻¹} ⊓ co2P : Subgroup _) ≤ 600 := by
  have hA := co2Q_chainArrays
  have hF := chainCheckFacts co2Chain_check.1
  have hQ := co2Q_valid.1
  have F := co2Five_chain_facts
  have hbc : co2Q.baseCount = 6 := co2Q_baseCount
  have hb : ∀ (m : ℕ) (hm : m < co2Q.baseCount), ((co2Q.base.get ⟨m, hm⟩ : Fin 2300) : ℕ) =
      co2BaseArr[m]! := fun m hm => hA.base_val ⟨m, hm⟩
  have hbase : ∀ (m : ℕ) (hm : m < co2Q.baseCount), co2BaseArr[m]! = m → m < 4 →
      (permOfArr 2300 co2FiveTArr * co2FiveLine 1 * (permOfArr 2300 co2FiveTArr)⁻¹)
        (co2Q.base.get ⟨m, hm⟩) = co2Q.base.get ⟨m, hm⟩ := by
    intro m hm hbm hm4
    apply co2FiveZ_fix
    rw [hb m hm, hbm]
    obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    · exact F.z0
    · exact F.z1
    · exact F.z2
    · exact F.z3
  have hbv : ∀ m < 4, co2BaseArr[m]! = m := by
    intro m hm
    rw [co2BaseArr_eq]
    obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    all_goals decide
  have e0 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co2FiveZ (i := 0)
    (by rw [hbc]; norm_num) (hbase 0 _ (hbv 0 (by norm_num)) (by norm_num))
  have e1 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co2FiveZ (i := 1)
    (by rw [hbc]; norm_num) (hbase 1 _ (hbv 1 (by norm_num)) (by norm_num))
  have e2 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co2FiveZ (i := 2)
    (by rw [hbc]; norm_num) (hbase 2 _ (hbv 2 (by norm_num)) (by norm_num))
  have e3 := card_centralizer_inf_levelSubgroup_le hA hF hQ rep_co2FiveZ (i := 3)
    (by rw [hbc]; norm_num) (hbase 3 _ (hbv 3 (by norm_num)) (by norm_num))
  have htail : tailOK 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2FiveZArr co2FiveZPows
      (co2Q.baseCount - 4) 4 (idA 2300) = true := by
    rw [hbc]
    exact F.tail
  have e4 := card_centralizer_inf_levelSubgroup_le_of_tailOK hA hF hQ rep_co2FiveZ (m := 4)
    (by rw [hbc]; norm_num) htail
  have hlen : co2FiveZPows.length = 5 := by simp [co2FiveZPows]
  rw [F.fix0] at e0
  rw [F.fix1] at e1
  rw [F.fix2] at e2
  rw [F.fix3] at e3
  rw [hlen] at e4
  have hP : co2P = co2Q.levelSubgroup 0 := by
    rw [co2Q.levelSubgroup_zero_eq_original hQ, co2Q_originalSubgroup]
  rw [hP]
  calc _ ≤ 10 * _ := e0
    _ ≤ 10 * (3 * _) := Nat.mul_le_mul_left _ e1
    _ ≤ 10 * (3 * (2 * _)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
    _ ≤ 10 * (3 * (2 * (2 * _))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e3))
    _ ≤ 10 * (3 * (2 * (2 * 5))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e4)))
    _ = 600 := by norm_num

theorem co2FiveC1_eq :
    co2FiveC1 = Subgroup.centralizer {co2FiveLine 1} ⊓ co2P := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf co2FiveC1_le_centralizer co2FiveC1_le_P)
  rw [card_co2FiveC1, card_centralizer_inf_conj co2P co2FiveT_mem_P rfl]
  exact card_centralizer_co2FiveZ_le

theorem co2FiveDGenArrs_size : co2FiveDGenArrs.size = 2 := by simp [co2FiveDGenArrs]

theorem dgen_zero' : permOfArr 2300 co2FiveDGenArrs[0]! =
    ⁅permOfArr 2300 co2FiveC1GenArrs[1]!, permOfArr 2300 co2FiveC1GenArrs[2]!⁆ := by
  have e : co2FiveDGenArrs[0]! = commutatorA 2300 co2FiveC1GenArrs[1]! co2FiveC1GenArrs[2]! := by
    simp [co2FiveDGenArrs]
  rw [e]
  exact permOfArr_eq_of_rep (rep_commutatorA (valid_c1gen (by norm_num))
    (valid_c1gen (by norm_num)))

theorem dgen_one' : permOfArr 2300 co2FiveDGenArrs[1]! = permOfArr 2300 co2FiveC1GenArrs[2]! := by
  have e : co2FiveDGenArrs[1]! = co2FiveC1GenArrs[2]! := by simp [co2FiveDGenArrs]
  rw [e]

theorem c1gen_two_eq_commutator :
    permOfArr 2300 co2FiveC1GenArrs[2]! =
      ⁅permOfArr 2300 co2FiveC1GenArrs[1]! * ((permOfArr 2300 co2FiveC1GenArrs[2]!)⁻¹ *
          (permOfArr 2300 co2FiveC1GenArrs[2]!)⁻¹),
        permOfArr 2300 co2FiveC1GenArrs[1]! * (permOfArr 2300 co2FiveC1GenArrs[2]! *
          (permOfArr 2300 co2FiveC1GenArrs[1]! * permOfArr 2300 co2FiveC1GenArrs[2]!))⁆ := by
  set A := permOfArr 2300 co2FiveC1GenArrs[1]!
  set B := permOfArr 2300 co2FiveC1GenArrs[2]!
  have rA : Rep 2300 co2FiveC1GenArrs[1]! A := rep_c1gen (by norm_num)
  have rB : Rep 2300 co2FiveC1GenArrs[2]! B := rep_c1gen (by norm_num)
  have rBi : Rep 2300 (invCand 2300 co2FiveC1GenArrs[2]!) B⁻¹ :=
    rep_inv_of_validA (valid_c1gen (by norm_num))
  have rG : Rep 2300 (co2BWordG co2FiveC1GenArrs) (A * (B⁻¹ * B⁻¹)) :=
    rep_compA rA (rep_compA rBi rBi)
  have rH : Rep 2300 (co2BWordH co2FiveC1GenArrs) (A * (B * (A * B))) :=
    rep_compA rA (rep_compA rB (rep_compA rA rB))
  have e := (eqA_iff (rep_compA rG rH) (rep_compA rB (rep_compA rH rG))).1
    co2Five_C1_facts.bComm
  rw [commutatorElement_def]
  set G := A * (B⁻¹ * B⁻¹)
  set H := A * (B * (A * B))
  calc B = B * (H * G) * (H * G)⁻¹ := by group
    _ = G * H * (H * G)⁻¹ := by rw [← e]
    _ = G * H * G⁻¹ * H⁻¹ := by group

theorem co2FiveD_eq : co2FiveD = Subgroup.closure (permsA 2300 co2FiveDGenArrs) := by
  have F := co2Five_C1_facts
  have hA : permOfArr 2300 co2FiveC1GenArrs[1]! ∈ co2FiveC1 := c1gen_mem (by norm_num)
  have hB : permOfArr 2300 co2FiveC1GenArrs[2]! ∈ co2FiveC1 := c1gen_mem (by norm_num)
  rw [co2FiveD]
  conv_lhs => rw [co2FiveC1]
  apply commutator_closure_eq_closure
  · rintro _ ⟨l, hl, rfl⟩
    have hl2 : l < 2 := hl
    obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · dsimp only
      rw [dgen_zero']
      exact Subgroup.commutator_mem_commutator hA hB
    · dsimp only
      rw [dgen_one', c1gen_two_eq_commutator]
      exact Subgroup.commutator_mem_commutator
        (co2FiveC1.mul_mem hA (co2FiveC1.mul_mem (co2FiveC1.inv_mem hB) (co2FiveC1.inv_mem hB)))
        (co2FiveC1.mul_mem hA (co2FiveC1.mul_mem hB (co2FiveC1.mul_mem hA hB)))
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any co2FiveKeyPts_lt F.dEnum
      (rep_conjA (valid_c1gen hk) (rep_dgen' hl)) (allLt_spec (allLt_spec F.norm hk) hl)
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any co2FiveKeyPts_lt F.dEnum
      (rep_commutatorA (valid_c1gen hk) (valid_c1gen hl)) (allLt_spec (allLt_spec F.comm hk) hl)

theorem card_co2FiveD : Nat.card co2FiveD = 60 := by
  rw [co2FiveD_eq]
  exact (enumOK_spec co2FiveKeyPts_lt co2Five_C1_facts.dEnum).2.1.trans co2Five_C1_facts.dSize

theorem co2FiveD_isSimpleGroup : IsSimpleGroup co2FiveD := by
  rw [co2FiveD_eq]
  exact CFSG.RankThree.PartOne.isSimpleGroup_of_conjWordsOK co2FiveKeyPts_lt
    co2Five_C1_facts.dEnum (by rw [co2Five_C1_facts.dSize]; norm_num) co2Five_C1_facts.simple

theorem co2FiveD_nonabelian : ∃ g ∈ co2FiveD, ∃ h ∈ co2FiveD, g * h ≠ h * g := by
  rw [co2FiveD_eq]
  refine ⟨_, Subgroup.subset_closure
    (mem_permsA (k := 0) (by rw [co2FiveDGenArrs_size]; norm_num)), _,
    Subgroup.subset_closure (mem_permsA (k := 1) (by rw [co2FiveDGenArrs_size]; norm_num)),
    fun h => ?_⟩
  have := (commA_iff (rep_dgen' (by norm_num)) (rep_dgen' (by norm_num))).2 h
  rw [co2Five_C1_facts.nonab] at this
  exact Bool.false_ne_true this

theorem co2FiveD_le_C1 : co2FiveD ≤ co2FiveC1 := by
  rw [co2FiveD, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact co2FiveC1.mul_mem (co2FiveC1.mul_mem (co2FiveC1.mul_mem ha hb) (co2FiveC1.inv_mem ha))
    (co2FiveC1.inv_mem hb)

theorem co2FiveCentD_eq :
    Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC1 =
      Subgroup.zpowers (co2FiveLine 1) := by
  have F := co2Five_C1_facts
  apply le_antisymm
  · intro g hg
    obtain ⟨hgD, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep co2FiveKeyPts_lt F.cEnum hgC
    rw [F.cSize] at hk
    have hc : ∀ l < 2, commA 2300 co2FiveC1Lit.pts[k]! co2FiveDGenArrs[l]! = true := by
      intro l hl
      have hd : permOfArr 2300 co2FiveDGenArrs[l]! ∈ co2FiveD := by
        rw [co2FiveD_eq]
        exact Subgroup.subset_closure (mem_permsA (by rw [co2FiveDGenArrs_size]; exact hl))
      exact (commA_iff hkg (rep_dgen' hl)).2 (Subgroup.mem_centralizer_iff.1 hgD _ hd).symm
    have h := allLt_spec F.cent hk
    rw [hc 0 (by norm_num), hc 1 (by norm_num)] at h
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨e, -, he⟩ := h
    rw [(eqA_iff hkg (rep_powArr rep_co2FiveLine_one e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_,
      co2FiveLine_one_mem_C1⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (co2FiveC1_le_centralizer (co2FiveD_le_C1 hd))

theorem co2FiveQCert_spec :
    (∀ x, x ∈ co2FiveQ ↔ ∃ i < co2FiveQCert.pts.size, permOfArr 2300 co2FiveQCert.pts[i]! = x) ∧
      ∀ i < co2FiveQCert.pts.size,
        Rep 2300 co2FiveQCert.pts[i]! (permOfArr 2300 co2FiveQCert.pts[i]!) := by
  have h : enumOK 2300 co2FiveQGenArrs co2FiveKeyPts co2FiveQCert = true :=
    (CFSG.KC.EnumBfs.enumOK_enumBfs co2Five_Q_facts.enum
      (by rw [co2Five_Q_facts.size]; norm_num)).1
  obtain ⟨h1, -, h3⟩ := enumOK_spec co2FiveKeyPts_lt h
  exact ⟨h1, fun i hi => rep_of_validA (h3 i hi)⟩

theorem co2FiveC0Cert_spec :
    (∀ x, x ∈ co2FiveC0 ↔
      ∃ i < co2FiveC0Cert.pts.size, permOfArr 2300 co2FiveC0Cert.pts[i]! = x) ∧
      ∀ i < co2FiveC0Cert.pts.size,
        Rep 2300 co2FiveC0Cert.pts[i]! (permOfArr 2300 co2FiveC0Cert.pts[i]!) := by
  have h : enumOK 2300 co2FiveC0GenArrs co2FiveKeyPts co2FiveC0Cert = true :=
    (CFSG.KC.EnumBfs.enumOK_enumBfs co2Five_C0_facts.enum
      (by rw [co2Five_C0_facts.size]; norm_num)).1
  obtain ⟨h1, -, h3⟩ := enumOK_spec co2FiveKeyPts_lt h
  exact ⟨h1, fun i hi => rep_of_validA (h3 i hi)⟩

theorem co2FiveStructures_of_checks :
    Co2FiveStructures where
  q_le_P := co2FiveQ_le_P
  q_sylow := co2FiveQ_sylow
  card_Q := card_co2FiveQ
  exponent_Q := exponent_co2FiveQ
  lines := co2FiveQ_lines
  transporter := co2FiveTransporter_spec
  c0_eq := co2FiveC0_eq
  card_C0 := card_co2FiveC0
  a_le_C0 := co2FiveA_le_C0
  a_normal := co2FiveA_normal
  centA_eq := co2FiveCentA_eq
  c1_eq := co2FiveC1_eq
  card_C1 := card_co2FiveC1
  d_simple := co2FiveD_isSimpleGroup
  d_nonabelian := co2FiveD_nonabelian
  card_D := card_co2FiveD
  centD_eq := co2FiveCentD_eq
  line_rep := rep_co2FiveLine
  q_enum := co2FiveQCert_spec.1
  q_rep := co2FiveQCert_spec.2
  c0_enum := co2FiveC0Cert_spec.1
  c0_rep := co2FiveC0Cert_spec.2

end CFSG.RankThree.Native.Co2FiveLit

end
