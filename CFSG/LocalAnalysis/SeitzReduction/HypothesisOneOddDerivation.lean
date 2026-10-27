module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerTwo
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationTests

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

universe u

@[expose] def oddDerivShapeCheck (τ : Tag) : Bool :=
  τ.rootCertificate.roots.all fun c =>
    decide (oddDerivHeight (decodeVec (τ := τ) c) ≤ oddDerivMaxHeight τ) &&
      decide (-oddDerivMaxHeight τ ≤ oddDerivHeight (decodeVec (τ := τ) c)) &&
      !oddDerivMixedB (decodeVec (τ := τ) c) &&
      (oddDerivQuadValues τ).contains (oddDerivQuad τ (decodeVec c))

theorem oddDerivShapeCheck_eq_true : ∀ τ : Tag, oddDerivShapeCheck τ = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel

variable {τ : Tag}

theorem not_isRoot_of_oddDerivNotRootB
    {v : Fin τ.rank → ℤ} (h : oddDerivNotRootB τ v = true) : ¬IsRoot τ v := by
  intro hv
  have hb := isRootB_iff.2 hv
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hv
  have hc := List.all_eq_true.1 (oddDerivShapeCheck_eq_true τ) _
    (List.getElem_mem (l := τ.rootCertificate.roots) hk)
  rw [← List.getD_eq_getElem _ 0 hk] at hc
  change _ = true at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  simp only [oddDerivNotRootB, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  have e : τ.rootCertificate.root k = decodeVec (τ.rootCertificate.roots.getD k 0) := rfl
  rw [e] at h hb
  rcases h with (((h | h) | h) | h) | h
  · exact absurd h1 (not_le.2 h)
  · exact absurd h2 (not_le.2 h)
  · rw [h3] at h
    exact Bool.false_ne_true h
  · rw [h4] at h
    exact Bool.false_ne_true h.symm
  · rw [hb] at h
    exact Bool.false_ne_true h.symm

theorem mem_of_oddDerivMemNat {n : ℕ} : ∀ {L : List ℕ}, oddDerivMemNat n L = true → n ∈ L
  | [], h => absurd h (by simp [oddDerivMemNat])
  | c :: l, h => by
    simp only [oddDerivMemNat, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_oddDerivMemNat h)

theorem oddDerivCode_digit :
    ∀ (l : List ℤ), (∀ x ∈ l, -8 ≤ x ∧ x ≤ 7) → ∀ (j : ℕ) (hj : j < l.length),
      oddDerivCode l / 16 ^ j % 16 = (l[j] + 8).toNat
  | [], _, j, hj => absurd hj (by simp)
  | x :: l, hl, 0, _ => by
    have hx := hl x List.mem_cons_self
    simp only [oddDerivCode, pow_zero, Nat.div_one, List.getElem_cons_zero]
    omega
  | x :: l, hl, j + 1, hj => by
    have hx := hl x List.mem_cons_self
    have ih := oddDerivCode_digit l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) j
      (by simpa using hj)
    simp only [oddDerivCode, List.getElem_cons_succ]
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have e : ((x + 8).toNat + 16 * oddDerivCode l) / 16 = oddDerivCode l := by omega
    rw [e, ih]

theorem decodeVec_oddDerivCode {v : Fin τ.rank → ℤ}
    (hv : ∀ x ∈ List.ofFn v, -8 ≤ x ∧ x ≤ 7) : decodeVec (τ := τ) (oddDerivCode (List.ofFn v)) = v := by
  funext j
  have hj := hv (v j) (List.mem_ofFn.2 ⟨j, rfl⟩)
  simp only [decodeVec]
  rw [oddDerivCode_digit _ hv j (by simp), List.getElem_ofFn, Fin.eta]
  omega

theorem isRoot_of_oddDerivIsRootB {v : Fin τ.rank → ℤ}
    (h : oddDerivIsRootB τ v = true) : IsRoot τ v := by
  simp only [oddDerivIsRootB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hr, hm⟩ := h
  obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.1 (mem_of_oddDerivMemNat hm)
  have := RootCertificate.isRoot_root τ.rootCertificate_check k hk
  rwa [RootCertificate.root, List.getD_eq_getElem _ _ hk, hkc, decodeVec_oddDerivCode hr] at this

def OddDerivPair (τ : Tag) (a b : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ a ∧ IsRoot τ b ∧ a ≠ b ∧ a ≠ -b ∧ IsRoot τ (a + b) ∧ ¬IsRoot τ (a - b) ∧
    ¬IsRoot τ (2 • a + b) ∧ ¬IsRoot τ (a + 2 • b)

theorem oddDerivPair_smul_iff
    (w : WeylGroup τ) {a b : Fin τ.rank → ℤ} :
    OddDerivPair τ (w • a) (w • b) ↔ OddDerivPair τ a b := by
  have e1 : w • a + w • b = w • (a + b) := (smul_add w a b).symm
  have e2 : w • a - w • b = w • (a - b) := (smul_sub w a b).symm
  have e3 : 2 • (w • a) + w • b = w • (2 • a + b) := by rw [smul_add, smul_comm]
  have e4 : w • a + 2 • (w • b) = w • (a + 2 • b) := by rw [smul_add, smul_comm w 2 b]
  have e5 : -(w • b) = w • (-b) := (smul_neg w b).symm
  simp only [OddDerivPair, e1, e2, e3, e4, e5, isRoot_smul_iff, ne_eq, smul_left_cancel_iff]

@[expose] def oddDerivPairB (τ : Tag) (a b : Fin τ.rank → ℤ) : Bool :=
  isRootB τ a && isRootB τ b && !CFSG.LieType.Ree.vecBEq a b &&
    !CFSG.LieType.Ree.vecBEq a (-b) && isRootB τ (a + b) && !isRootB τ (a - b) &&
    !isRootB τ (2 • a + b) && !isRootB τ (a + 2 • b)

theorem oddDerivPairB_iff
    {a b : Fin τ.rank → ℤ} : oddDerivPairB τ a b = true ↔ OddDerivPair τ a b := by
  simp only [oddDerivPairB, OddDerivPair, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    isRootB_iff, ← Bool.not_eq_true, CFSG.LieType.Ree.vecBEq_iff, and_assoc]

@[expose] def oddDerivUnitFactorB (f : ℕ × ℕ × ℕ × ℤ) : Bool :=
  f.1 == 1 && f.2.1 == 1 && (f.2.2.2 == 1 || f.2.2.2 == -1)

@[expose] def oddDerivRowsCheck (τ : Tag) : Bool :=
  (pairTable τ).all fun r =>
    !oddDerivPairB τ (orbitCertRoot τ r.1) (orbitCertRoot τ r.2.1) ||
      (r.2.2.2.length == 1 && r.2.2.2.all oddDerivUnitFactorB)

theorem oddDerivRowsCheck_eq_true : ∀ τ : Tag, oddDerivRowsCheck τ = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel

@[expose] def oddDerivEmptyRowsCheck (τ : Tag) : Bool :=
  (pairTable τ).all fun r =>
    isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) || r.2.2.2.isEmpty

theorem oddDerivEmptyRowsCheck_eq_true : ∀ τ : Tag, oddDerivEmptyRowsCheck τ = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel

@[expose] def oddDerivLacedCheck (τ : Tag) : Bool :=
  (pairTable τ).all fun r =>
    !isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) ||
      (r.2.2.2.length == 1 && r.2.2.2.all oddDerivUnitFactorB)

theorem oddDerivLacedCheck_of_simplyLaced {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : oddDerivLacedCheck τ = true := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

@[expose] def oddDerivStringB (τ : Tag) (a b : Fin τ.rank → ℤ) : Bool :=
  oddDerivNotRootB τ (a - b) && oddDerivNotRootB τ (2 • a + b) && oddDerivNotRootB τ (a + 2 • b)

@[expose] def oddDerivStepB {n : ℕ} (SA SP : List (Fin n → ℤ))
    (e : (Fin n → ℤ) × (Fin n → ℤ) × (Fin n → ℤ)) : Bool :=
  oddDerivVecEq e.1 (e.2.1 + e.2.2) && oddDerivMemB e.1 SA &&
    ((oddDerivMemB e.2.1 SA && oddDerivMemB e.2.2 (SA ++ SP)) ||
      (oddDerivMemB e.2.1 (SA ++ SP) && oddDerivMemB e.2.2 SA)) &&
    !oddDerivVecEq e.2.1 e.2.2 && !oddDerivVecEq e.2.1 (-e.2.2)

@[expose] def oddDerivOK (τ : Tag) (SA SP : List (Fin τ.rank → ℤ))
    (D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) : Bool :=
  (SA ++ SP).all (oddDerivIsRootB τ) && D.all (oddDerivStepB SA SP) &&
    (oddDerivLacedCheck τ || D.all fun e => oddDerivStringB τ e.2.1 e.2.2)

@[expose] def oddDerivCovB {n : ℕ} (SA : List (Fin n → ℤ))
    (D : List ((Fin n → ℤ) × (Fin n → ℤ) × (Fin n → ℤ))) : Bool :=
  SA.all fun δ => D.any fun e => oddDerivVecEq e.1 δ

@[expose] def oddDerivCommB (τ : Tag) (γ σ : Fin τ.rank → ℤ) : Bool :=
  oddDerivVecEq γ σ || (!oddDerivVecEq γ (-σ) && oddDerivNotRootB τ (γ + σ))

@[expose] def oddDerivFrameB (τ : Tag) (F L : List (Fin τ.rank → ℤ)) : Bool :=
  F.all (oddDerivIsRootB τ) && L.all fun γ => F.all (oddDerivCommB τ γ)

@[expose] def oddDerivCheck (τ : Tag) (h : ℤ) (F SA SP : List (Fin τ.rank → ℤ))
    (D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) : Bool :=
  oddDerivOK τ SA SP D && oddDerivCovB SA D && oddDerivFrameB τ F (SA ++ SP) &&
    oddDerivTailB τ h SA

theorem oddDerivPair_of_oddDerivStringB
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b)
    (hne : a ≠ b) (hne' : a ≠ -b) (hab : IsRoot τ (a + b)) (h : oddDerivStringB τ a b = true) :
    OddDerivPair τ a b := by
  simp only [oddDerivStringB, Bool.and_eq_true] at h
  exact ⟨ha, hb, hne, hne', hab, not_isRoot_of_oddDerivNotRootB h.1.1,
    not_isRoot_of_oddDerivNotRootB h.1.2, not_isRoot_of_oddDerivNotRootB h.2⟩

theorem oddDeriv_cov_of_oddDerivCovB {n : ℕ} {SA : List (Fin n → ℤ)}
    {D : List ((Fin n → ℤ) × (Fin n → ℤ) × (Fin n → ℤ))}
    (h : oddDerivCovB SA D = true) : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ := fun δ hδ => by
  obtain ⟨e, he, hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 h δ hδ)
  exact ⟨e, he, eq_of_oddDerivVecEq hb⟩

theorem oddDeriv_cov_map_fst {n : ℕ} (D : List ((Fin n → ℤ) × (Fin n → ℤ) × (Fin n → ℤ))) :
    ∀ δ ∈ D.map Prod.fst, ∃ e ∈ D, e.1 = δ := fun _ hδ => List.mem_map.1 hδ

theorem pinnedX_mem_rootSpan_oddDeriv
    {R : Type u} [CommRing R] {S : Set (Fin τ.rank → ℤ)}
    {α : Fin τ.rank → ℤ} (hα : α ∈ S) (c : R) : pinnedX τ R α c ∈ rootSpan τ R S :=
  (le_iSup₂_of_le α hα le_rfl : rootSubgroup τ R α ≤ rootSpan τ R S)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem heightSeries_le_rootSpan_of_oddDerivTailB
    {R : Type u} [CommRing R] {h : ℤ}
    {SA : List (Fin τ.rank → ℤ)} (hc : oddDerivTailB τ h SA = true) :
    heightSeries τ R h ≤ rootSpan τ R {γ | γ ∈ SA} := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα.1
  have h1 := List.all_eq_true.1 hc _ (List.getElem_mem (l := τ.rootCertificate.roots) hk)
  rw [← List.getD_eq_getElem _ 0 hk] at h1
  change _ = true at h1
  have e : τ.rootCertificate.root k = decodeVec (τ.rootCertificate.roots.getD k 0) := rfl
  rw [← e, oddDerivHeight_eq] at h1
  simp only [hα.2.1, hα.2.2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at h1
  exact le_iSup₂_of_le _ (mem_of_oddDerivMemB h1) le_rfl

section Sound



theorem commutatorElement_pinnedX_of_rowFactor {R : Type u} [CommRing R] (h2 : (2 : R) = 0)
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) (hne : a ≠ b) (hne' : a ≠ -b)
    (hrow : ∀ r ∈ pairTable τ, ∀ w : WeylGroup τ, w • orbitCertRoot τ r.1 = a →
      w • orbitCertRoot τ r.2.1 = b →
        (r.2.2.2.length == 1 && r.2.2.2.all oddDerivUnitFactorB) = true)
    (x y : R) : ⁅pinnedX τ R a x, pinnedX τ R b y⁆ = pinnedX τ R (a + b) (x * y) := by
  obtain ⟨r, hr, w, hwa, hwb, -, hcomm⟩ :=
    exists_pairTable_commutatorElement_of_two_eq_zero ha hb hne hne'
  have hchk := hrow r hr w hwa hwb
  rw [Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨hlen, hf⟩ := hchk
  obtain ⟨⟨p, q, k, C⟩, hfeq⟩ := List.length_eq_one_iff.1 hlen
  rw [hfeq, List.all_cons, List.all_nil, Bool.and_true] at hf
  simp only [oddDerivUnitFactorB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨rfl, rfl⟩, hC⟩ := hf
  rw [hcomm R h2 x y, hfeq, List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one,
    pow_one, mul_assoc]
  congr 1
  rcases hC with rfl | rfl
  · rw [Int.cast_one, one_mul]
  · rw [Int.cast_neg, Int.cast_one, neg_one_mul]
    exact neg_eq_of_add_eq_zero_left (by rw [← two_mul, h2, zero_mul])

theorem commutatorElement_pinnedX_of_oddDerivPair {R : Type u} [CommRing R] (h2 : (2 : R) = 0)
    {a b : Fin τ.rank → ℤ} (h : OddDerivPair τ a b) (x y : R) :
    ⁅pinnedX τ R a x, pinnedX τ R b y⁆ = pinnedX τ R (a + b) (x * y) := by
  refine commutatorElement_pinnedX_of_rowFactor h2 h.1 h.2.1 h.2.2.1 h.2.2.2.1
    (fun r hr w hwa hwb => ?_) x y
  have hrow : oddDerivPairB τ (orbitCertRoot τ r.1) (orbitCertRoot τ r.2.1) = true := by
    rw [oddDerivPairB_iff, ← oddDerivPair_smul_iff w, hwa, hwb]
    exact h
  have hchk := List.all_eq_true.1 (oddDerivRowsCheck_eq_true τ) r hr
  rwa [hrow, Bool.not_true, Bool.false_or] at hchk

theorem commutatorElement_pinnedX_of_oddDerivLaced {R : Type u} [CommRing R] (h2 : (2 : R) = 0)
    (hτ : oddDerivLacedCheck τ = true) {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a)
    (hb : IsRoot τ b) (hne : a ≠ b) (hne' : a ≠ -b) (hab : IsRoot τ (a + b)) (x y : R) :
    ⁅pinnedX τ R a x, pinnedX τ R b y⁆ = pinnedX τ R (a + b) (x * y) := by
  refine commutatorElement_pinnedX_of_rowFactor h2 ha hb hne hne' (fun r hr w hwa hwb => ?_) x y
  have hrow : isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) = true := by
    rw [isRootB_iff, ← isRoot_smul_iff w, smul_add, hwa, hwb]
    exact hab
  have hchk := List.all_eq_true.1 hτ r hr
  rwa [hrow, Bool.not_true, Bool.false_or] at hchk

theorem not_isRoot_nsmul_add_nsmul_of_oddDeriv {γ σ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hσ : IsRoot τ σ) (hne : γ ≠ σ) (hne' : γ ≠ -σ) (hn : ¬IsRoot τ (γ + σ)) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) : ¬IsRoot τ (p • γ + q • σ) := by
  intro hpq
  obtain ⟨r, ⟨hr, horb⟩, -⟩ := (rank_two_pair_certificate τ).1 γ σ hγ hσ hne hne'
  obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.1 horb
  rw [Prod.smul_mk, Prod.mk.injEq] at hw
  have hfac := ((rank_two_pair_certificate τ).2 r hr).2.2.2.2.2.2.2.2.1
  have hsum : isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) = false := by
    rw [Bool.eq_false_iff, Ne, isRootB_iff, ← isRoot_smul_iff w, smul_add, hw.1, hw.2]
    exact hn
  have hchk := List.all_eq_true.1 (oddDerivEmptyRowsCheck_eq_true τ) r hr
  rw [hsum, Bool.false_or, List.isEmpty_iff] at hchk
  have hpq' : IsRoot τ (p • orbitCertRoot τ r.1 + q • orbitCertRoot τ r.2.1) := by
    rw [← isRoot_smul_iff w, smul_nsmul_add_nsmul_eq, hw.1, hw.2]
    exact hpq
  obtain ⟨a, ha, hae⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hpq'
  obtain ⟨C, hC⟩ := (hfac p q (certWitnessPos τ a)).2 ⟨hp, hq, certWitnessPos_lt ha,
    by rw [orbitCertRoot_certWitnessPos ha, hae]⟩
  rw [hchk] at hC
  exact List.not_mem_nil hC

theorem commute_pinnedX_of_oddDeriv {R : Type u} [CommRing R] {γ σ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hσ : IsRoot τ σ) (hne' : γ ≠ -σ) (hn : ¬IsRoot τ (γ + σ)) (c d : R) :
    Commute (pinnedX τ R γ c) (pinnedX τ R σ d) := by
  by_cases hne : γ = σ
  · subst hne
    show pinnedX τ R γ c * pinnedX τ R γ d = pinnedX τ R γ d * pinnedX τ R γ c
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula.{u} τ hγ hσ hne hne'
    have hnil : commPairs τ γ σ = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      obtain ⟨hp1, hp2, hpr⟩ := (hmem p).1 hp
      exact not_isRoot_nsmul_add_nsmul_of_oddDeriv hγ hσ hne hne' hn hp1 hp2 hpr
    have h0 := hF R c d
    rw [hnil, List.map_nil, List.prod_nil] at h0
    calc pinnedX τ R γ c * pinnedX τ R σ d =
          (pinnedX τ R γ c * pinnedX τ R σ d * pinnedX τ R γ (-c) * pinnedX τ R σ (-d)) *
            (pinnedX τ R σ d * pinnedX τ R γ c) := by
          rw [← pinnedX_neg, ← pinnedX_neg]
          group
      _ = pinnedX τ R σ d * pinnedX τ R γ c := by rw [h0, one_mul]

theorem pinnedX_mem_commutator_of_oddDerivOK {R : Type u} [CommRing R] (h2 : (2 : R) = 0)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) {e : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)}
    (he : e ∈ D) (c : R) :
    pinnedX τ R e.1 c ∈
      ⁅rootSpan τ R {γ | γ ∈ SA}, rootSpan τ R {γ | γ ∈ SA ∨ γ ∈ SP}⁆ := by
  simp only [oddDerivOK, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hD
  obtain ⟨⟨hroots, hsteps⟩, hlac⟩ := hD
  have hroot : ∀ γ ∈ SA ++ SP, IsRoot τ γ := fun γ hγ => isRoot_of_oddDerivIsRootB (hroots γ hγ)
  have hs := hsteps e he
  obtain ⟨δ, a, b⟩ := e
  simp only [oddDerivStepB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hs
  obtain ⟨⟨⟨⟨hsum, hδ⟩, hab⟩, hne⟩, hne'⟩ := hs
  have hsum' : δ = a + b := eq_of_oddDerivVecEq hsum
  have hδ' : IsRoot τ (a + b) :=
    hsum' ▸ hroot δ (List.mem_append_left _ (mem_of_oddDerivMemB hδ))
  have hne1 : a ≠ b := fun e => by rw [e, oddDerivVecEq_self] at hne; exact Bool.false_ne_true hne.symm
  have hne2 : a ≠ -b := fun e => by
    rw [e, oddDerivVecEq_self] at hne'
    exact Bool.false_ne_true hne'.symm
  have hmemP : ∀ γ ∈ SA ++ SP, γ ∈ {γ | γ ∈ SA ∨ γ ∈ SP} := fun γ hγ => List.mem_append.1 hγ
  have hcomm : ∀ (ha : IsRoot τ a) (hb : IsRoot τ b),
      ⁅pinnedX τ R a 1, pinnedX τ R b c⁆ = pinnedX τ R (a + b) (1 * c) := fun ha hb => by
    rcases hlac with hl | hl
    · exact commutatorElement_pinnedX_of_oddDerivLaced h2 hl ha hb hne1 hne2 hδ' 1 c
    · exact commutatorElement_pinnedX_of_oddDerivPair h2 (oddDerivPair_of_oddDerivStringB ha hb
        hne1 hne2 hδ' (hl (δ, a, b) he)) 1 c
  show pinnedX τ R δ c ∈ _
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' := mem_of_oddDerivMemB ha
    have hb' := mem_of_oddDerivMemB hb
    rw [hsum', ← one_mul c, ← hcomm (hroot a (List.mem_append_left _ ha')) (hroot b hb')]
    exact Subgroup.commutator_mem_commutator (pinnedX_mem_rootSpan_oddDeriv ha' 1)
      (pinnedX_mem_rootSpan_oddDeriv (hmemP b hb') c)
  · have ha' := mem_of_oddDerivMemB ha
    have hb' := mem_of_oddDerivMemB hb
    rw [hsum', ← one_mul c, ← hcomm (hroot a ha') (hroot b (List.mem_append_left _ hb')),
      Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (pinnedX_mem_rootSpan_oddDeriv (hmemP a ha') 1)
      (pinnedX_mem_rootSpan_oddDeriv hb' c)

theorem rootSpan_le_commutator_of_oddDerivOK {R : Type u} [CommRing R] (h2 : (2 : R) = 0)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) (hcov : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ) :
    rootSpan τ R {γ | γ ∈ SA} ≤
      ⁅rootSpan τ R {γ | γ ∈ SA}, rootSpan τ R {γ | γ ∈ SA ∨ γ ∈ SP}⁆ := by
  refine iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨e, he, rfl⟩ := hcov δ hδ
  exact pinnedX_mem_commutator_of_oddDerivOK h2 hD he c

theorem commute_pinnedX_list_prod_of_oddDerivCommB {R : Type u} [CommRing R]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ σ ∈ F, IsRoot τ σ) (h : F.all (oddDerivCommB τ γ) = true) (c : R)
    (cF : (Fin τ.rank → ℤ) → R) :
    Commute (pinnedX τ R γ c) (F.map fun σ => pinnedX τ R σ (cF σ)).prod := by
  refine Commute.list_prod_right _ _ fun g hg => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
  have h1 := List.all_eq_true.1 h σ hσ
  simp only [oddDerivCommB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h1
  rcases h1 with he | ⟨hne, hn⟩
  · rw [eq_of_oddDerivVecEq he]
    show pinnedX τ R σ c * pinnedX τ R σ (cF σ) = pinnedX τ R σ (cF σ) * pinnedX τ R σ c
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · refine commute_pinnedX_of_oddDeriv hγ (hF σ hσ) (fun e => ?_)
      (not_isRoot_of_oddDerivNotRootB hn) c (cF σ)
    rw [e, oddDerivVecEq_self] at hne
    exact Bool.false_ne_true hne.symm

variable {K : Type} [Field K]

theorem rootSpan_le_closure_odd_of_oddDerivOK [Finite K] [CharP K 2] {t : adjointGroup τ K}
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) (hcov : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ)
    (ht : ∀ γ ∈ SA ++ SP, ∀ c : K,
      (⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) * t =
        t * ⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩) :
    ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSpan τ K {γ | γ ∈ SA} →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)} := by
  intro x hx
  have : Finite (ModGL τ K) := finite_modGL
  have hsub : ∀ S : Set (Fin τ.rank → ℤ), rootSpan τ K S ≤ adjointGroup τ K :=
    fun S => iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  set A : Subgroup (adjointGroup τ K) := (rootSpan τ K {γ | γ ∈ SA}).subgroupOf (adjointGroup τ K)
    with hA
  set P : Subgroup (adjointGroup τ K) :=
    (rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP}).subgroupOf (adjointGroup τ K) with hP
  have hAP : A ≤ P := fun y hy => Subgroup.mem_subgroupOf.2
    ((biSup_mono fun γ hγ => Or.inl hγ : rootSpan τ K {γ | γ ∈ SA} ≤
      rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP}) (Subgroup.mem_subgroupOf.1 hy))
  have hcen : rootSpan τ K {γ | γ ∈ SA ∨ γ ∈ SP} ≤ Subgroup.centralizer {(t : ModGL τ K)} := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (ht γ (List.mem_append.2 hγ) c)
  have hPt : ∀ y ∈ P, y * t = t * y := fun y hy => Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.1 (hcen (Subgroup.mem_subgroupOf.1 hy)))
  have hcomm : A ≤ ⁅A, P⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective (adjointGroup τ K).subtype_injective,
      Subgroup.map_commutator, hA, hP, Subgroup.map_subgroupOf_eq_of_le (hsub _),
      Subgroup.map_subgroupOf_eq_of_le (hsub _)]
    exact rootSpan_le_commutator_of_oddDerivOK CharTwo.two_eq_zero hD hcov
  exact le_closure_odd_of_le_commutator hAP hPt hcomm (Subgroup.mem_subgroupOf.2 hx)

theorem rootSpan_le_closure_odd_of_oddDerivFrame [Finite K] [CharP K 2] {t : adjointGroup τ K}
    (F : List (Fin τ.rank → ℤ)) (cF : (Fin τ.rank → ℤ) → K)
    (htF : (t : ModGL τ K) = (F.map fun σ => pinnedX τ K σ (cF σ)).prod)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) (hcov : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ)
    (hF : oddDerivFrameB τ F (SA ++ SP) = true) :
    ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSpan τ K {γ | γ ∈ SA} →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)} := by
  have hroots : ∀ γ ∈ SA ++ SP, IsRoot τ γ := by
    simp only [oddDerivOK, Bool.and_eq_true, List.all_eq_true] at hD
    exact fun γ hγ => isRoot_of_oddDerivIsRootB (hD.1.1 γ hγ)
  simp only [oddDerivFrameB, Bool.and_eq_true, List.all_eq_true] at hF
  obtain ⟨hFr, hFc⟩ := hF
  refine rootSpan_le_closure_odd_of_oddDerivOK hD hcov fun γ hγ c => Subtype.ext ?_
  simp only [Subgroup.coe_mul, htF]
  exact (commute_pinnedX_list_prod_of_oddDerivCommB (hroots γ hγ)
    (fun σ hσ => isRoot_of_oddDerivIsRootB (hFr σ hσ)) (List.all_eq_true.2 (hFc γ hγ)) c cF).eq

theorem pinnedX_mem_closure_odd_of_oddDerivFrame [Finite K] [CharP K 2] {t : adjointGroup τ K}
    (F : List (Fin τ.rank → ℤ)) (cF : (Fin τ.rank → ℤ) → K)
    (htF : (t : ModGL τ K) = (F.map fun σ => pinnedX τ K σ (cF σ)).prod)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hD : oddDerivOK τ SA SP D = true) (hcov : ∀ δ ∈ SA, ∃ e ∈ D, e.1 = δ)
    (hF : oddDerivFrameB τ F (SA ++ SP) = true) :
    ∀ δ ∈ SA, ∀ a : K, (⟨pinnedX τ K δ a, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈
      closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)} :=
  fun _ hδ a => rootSpan_le_closure_odd_of_oddDerivFrame F cF htF hD hcov hF _
    (pinnedX_mem_rootSpan_oddDeriv (S := {γ | γ ∈ SA}) hδ a)

theorem heightSeries_le_closure_odd_of_oddDerivCheck [Finite K] [CharP K 2] {t : adjointGroup τ K}
    {h : ℤ} (F : List (Fin τ.rank → ℤ)) (cF : (Fin τ.rank → ℤ) → K)
    (htF : (t : ModGL τ K) = (F.map fun σ => pinnedX τ K σ (cF σ)).prod)
    {SA SP : List (Fin τ.rank → ℤ)}
    {D : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))}
    (hchk : oddDerivCheck τ h F SA SP D = true) :
    ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h →
      x ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)} := by
  simp only [oddDerivCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨hD, hcov⟩, hF⟩, htail⟩ := hchk
  exact fun x hx => rootSpan_le_closure_odd_of_oddDerivFrame F cF htF hD
    (oddDeriv_cov_of_oddDerivCovB hcov) hF x (heightSeries_le_rootSpan_of_oddDerivTailB htail hx)

end Sound

end CFSG.SeitzReduction
