module

public import CFSG.LieType.Chevalley.SignCharacterMasks

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] def listMask (l : List Bool) : Fin τ.rank → Bool :=
  fun j => l.getD j false

@[expose] def toFinWord (ω : List ℕ) : List (Fin τ.rank) :=
  ω.filterMap fun i => if h : i < τ.rank then some ⟨i, h⟩ else none

@[expose] def OrbitCheck (τ : Tag) (reps : List (List Bool))
    (entries : List (List Bool × ℕ × List ℕ)) : Prop :=
  ∀ b : Fin τ.rank → Bool, ∃ e ∈ entries, e.1 = List.ofFn b ∧ e.2.1 < reps.length ∧
    List.ofFn (maskAct (toFinWord e.2.2) (listMask (τ := τ) (reps.getD e.2.1 []))) = List.ofFn b

theorem exists_isCharConj_of_orbitCheck
    {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (h : OrbitCheck τ reps entries)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    ∃ ρ < reps.length, ∃ t : WeylGroup τ,
      IsCharConj (maskChar (listMask (reps.getD ρ []))) χ t := by
  rw [eq_maskChar χ]
  set b : Fin τ.rank → Bool := fun j => decide (χ (Multiplicative.ofAdd (Pi.single j 1)) = -1)
  obtain ⟨e, -, -, hρ, he⟩ := h b
  refine ⟨e.2.1, hρ, (coxeterSystem τ).wordProd (toFinWord e.2.2), fun v => ?_⟩
  rw [← List.ofFn_injective he, maskChar_maskAct]

end CFSG.LieType.Chevalley

namespace CFSG.Blueprint.Chevalley.RootCertificate

open CFSG.LieType.Chevalley

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def tupleVec (t : List ℕ) (c : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  ∑ j : Fin τ.rank, c j • C.root (t.getD j 0)

@[expose] def tupleImage (i : Fin τ.rank) (t : List ℕ) : List ℕ :=
  t.map fun k => C.image k i

@[expose] def dTest (Δ : List ℕ) (t : List ℕ) : Bool :=
  Δ.all fun β => decide (0 < height (C.tupleVec t (C.root β)))

@[expose] def chiTest (m : List Bool) (t : List ℕ) : Bool :=
  (List.finRange τ.rank).all fun j =>
    decide (Even (maskPairing (listMask m) (C.root (t.getD j 0)))) == !(listMask m j)

@[expose] def Represents
    (t : List ℕ) (w : WeylGroup τ) : Prop :=
  t.length = τ.rank ∧ ∀ j : Fin τ.rank, t.getD j 0 < C.roots.length ∧
    C.root (t.getD j 0) = w • (Pi.single j 1 : Fin τ.rank → ℤ)

variable {C}

theorem tupleVec_eq
    {t : List ℕ} {w : WeylGroup τ} (h : C.Represents t w) (c : Fin τ.rank → ℤ) :
    C.tupleVec t c = w • c := by
  have hc : c = ∑ j : Fin τ.rank, c j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  rw [Finset.smul_sum, tupleVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h.2 j).2, smul_comm]

theorem image_spec (hC : C.check = true) {k : ℕ} (hk : k < C.roots.length) (i : Fin τ.rank) :
    C.image k i < C.roots.length ∧ C.root (C.image k i) = reflect τ i (C.root k) := by
  simp only [check, Bool.and_eq_true] at hC
  obtain ⟨-, ht⟩ := hC
  simp only [checkTable, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ⟨(ht k hk i).1, eq_of_ofFn_beq (ht k hk i).2⟩

theorem represents_tupleImage
    (hC : C.check = true) {t : List ℕ} {w : WeylGroup τ}
    (h : C.Represents t w) (i : Fin τ.rank) :
    C.Represents (C.tupleImage i t) (simple τ i * w) := by
  refine ⟨by rw [tupleImage, List.length_map, h.1], fun j => ?_⟩
  have hj : (j : ℕ) < t.length := by rw [h.1]; exact j.2
  have hget : (C.tupleImage i t).getD j 0 = C.image (t.getD j 0) i := by
    rw [tupleImage, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
      List.getElem_map, List.getD_eq_getElem _ _ hj]
  obtain ⟨h1, h2⟩ := image_spec hC (h.2 j).1 i
  rw [hget, h2, (h.2 j).2, mul_smul, simple_smul]
  exact ⟨h1, rfl⟩

theorem represents_one
    (hC : C.check = true) :
    C.Represents (List.range τ.rank) (1 : WeylGroup τ) := by
  simp only [check, Bool.and_eq_true] at hC
  obtain ⟨⟨hb, -⟩, -⟩ := hC
  simp only [checkBasis, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at hb
  refine ⟨List.length_range, fun j => ?_⟩
  have hget : (List.range τ.rank).getD j 0 = j := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact j.2), List.getElem_range]
  rw [hget, one_smul]
  exact ⟨lt_of_lt_of_le j.2 hb.1, eq_of_ofFn_beq (hb.2 j)⟩

theorem represents_unique
    {t : List ℕ} {w w' : WeylGroup τ} (h : C.Represents t w)
    (h' : C.Represents t w') : w = w' :=
  ext_single fun j => ((h.2 j).2).symm.trans (h'.2 j).2

end CFSG.Blueprint.Chevalley.RootCertificate

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootCertificate

variable {τ : Tag}

structure StabCert where
  mask : List Bool
  simple : List ℕ
  elems : List (List ℕ)

namespace StabCert

variable
    (C : RootCertificate τ) (S : StabCert)

@[expose] def passing : List (List ℕ) :=
  S.elems.filter (C.chiTest S.mask)

@[expose] def check : Bool :=
  S.elems.contains (List.range τ.rank) &&
  S.simple.all (fun β => decide (β < C.roots.length) && decide (0 < height (C.root β)) &&
    decide (Even (maskPairing (listMask S.mask) (C.root β)))) &&
  S.elems.all fun t => (List.finRange τ.rank).all fun i =>
    !(C.dTest S.simple (C.tupleImage i t)) || S.elems.contains (C.tupleImage i t)

@[expose] def checkElemAb : Bool :=
  (S.passing C).all (fun t => (List.finRange τ.rank).all fun j =>
    List.ofFn (C.tupleVec t (C.root (t.getD j 0))) ==
      List.ofFn (Pi.single j 1 : Fin τ.rank → ℤ)) &&
  (S.passing C).all fun t => (S.passing C).all fun t' => (List.finRange τ.rank).all fun j =>
    List.ofFn (C.tupleVec t (C.root (t'.getD j 0))) ==
      List.ofFn (C.tupleVec t' (C.root (t.getD j 0)))

variable {C S}

theorem dTest_iff
    {t : List ℕ} {w : WeylGroup τ} (h : C.Represents t w) :
    C.dTest S.simple t = true ↔ ∀ β ∈ S.simple, 0 < height (w • C.root β) := by
  simp only [dTest, List.all_eq_true, decide_eq_true_eq, tupleVec_eq h]

theorem exists_represents_of_check
    (hC : C.check = true) (hS : S.check C = true)
    (w : WeylGroup τ) (hw : ∀ β ∈ S.simple, 0 < height (w • C.root β)) :
    ∃ t ∈ S.elems, C.Represents t w := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hS
  obtain ⟨⟨hid, hsimple⟩, hclosed⟩ := hS
  suffices key : ∀ n : ℕ, ∀ w : WeylGroup τ, (coxeterSystem τ).length w = n →
      (∀ β ∈ S.simple, 0 < height (w • C.root β)) → ∃ t ∈ S.elems, C.Represents t w from
    key _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw
    by_cases h1 : w = 1
    · subst h1
      exact ⟨_, List.contains_iff_mem.1 hid, represents_one hC⟩
    obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_leftDescent_of_ne_one h1
    have hlen : (coxeterSystem τ).length (CFSG.LieType.Chevalley.simple τ i * w) < n := by
      rw [← hn]
      exact hi
    have hneg : w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) ≤ 0 := by
      have := (CFSG.LieType.RootSystem.isRightDescent_iff (isFiniteType_cartan τ) w⁻¹ i).1
        ((coxeterSystem τ).isRightDescent_inv_iff.2 hi)
      exact this
    have hw' : ∀ β ∈ S.simple, 0 < height ((CFSG.LieType.Chevalley.simple τ i * w) • C.root β) := by
      intro β hβ
      have hβ' := hsimple β hβ
      have hr : IsRoot τ (C.root β) := RootCertificate.isRoot_root hC β hβ'.1.1
      have hr' : IsRoot τ (w • C.root β) := IsRoot.smul hr w
      have hne : w • C.root β ≠ Pi.single i 1 := by
        intro e
        have : C.root β = w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [← e, inv_smul_smul]
        have hpos := hβ'.1.2
        rw [this] at hpos
        have : height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) ≤ 0 :=
          Finset.sum_nonpos fun j _ => hneg j
        omega
      rw [mul_smul, simple_smul]
      exact height_reflect_pos hr' (hw β hβ) hne
    obtain ⟨t, ht, hrep⟩ := ih _ hlen _ rfl hw'
    have hrep' := represents_tupleImage hC hrep i
    rw [← mul_assoc, (coxeterSystem τ).simple_mul_simple_self, one_mul] at hrep'
    have hd : C.dTest S.simple (C.tupleImage i t) = true := (dTest_iff hrep').2 hw
    rcases hclosed t ht i (List.mem_finRange i) with h | h
    · rw [hd] at h
      exact absurd h (by decide)
    · exact ⟨_, List.contains_iff_mem.1 h, hrep'⟩

theorem simple_mem_posRoots
    (hC : C.check = true) (hS : S.check C = true) {β : ℕ}
    (hβ : β ∈ S.simple) :
    C.root β ∈ posRoots (kernelRoots (maskChar (listMask S.mask))) := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨-, hsimple⟩, -⟩ := hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hsimple β hβ
  exact ⟨mem_kernelRoots_maskChar.2 ⟨RootCertificate.isRoot_root hC β h1, h3⟩, h2⟩

theorem exists_passing_of_mem
    (hC : C.check = true) (hS : S.check C = true) {ω : WeylGroup τ}
    (hω : ω ∈ kernelPosStabilizer (maskChar (listMask S.mask))) :
    ∃ t ∈ S.passing C, C.Represents t ω := by
  obtain ⟨hχ, himg⟩ := hω
  have hpos : ∀ β ∈ S.simple, 0 < height (ω • C.root β) := by
    intro β hβ
    have h := simple_mem_posRoots hC hS hβ
    have : ω • C.root β ∈ posRoots (kernelRoots (maskChar (listMask S.mask))) := by
      rw [← himg]
      exact ⟨_, h, rfl⟩
    exact this.2
  obtain ⟨t, ht, hrep⟩ := exists_represents_of_check hC hS ω hpos
  refine ⟨t, List.mem_filter.2 ⟨ht, ?_⟩, hrep⟩
  simp only [chiTest, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  intro j
  rw [(hrep.2 j).2]
  have h := hχ (Pi.single j 1)
  rw [maskChar_apply, maskChar_apply, neg_one_zpow_eq_ite, neg_one_zpow_eq_ite] at h
  have hpair : maskPairing (listMask S.mask) (Pi.single j 1) =
      if listMask S.mask j then 1 else 0 := by
    rw [maskPairing, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [hpair] at h
  by_cases hm : listMask S.mask j
  · simp only [hm, ↓reduceIte] at h
    have : ¬Even (maskPairing (listMask S.mask) (ω • Pi.single j 1)) := by
      intro he
      simp only [he, ↓reduceIte] at h
      exact absurd h (by decide)
    simp [hm, this]
  · simp only [hm, ↓reduceIte, Bool.false_eq_true] at h
    have : Even (maskPairing (listMask S.mask) (ω • Pi.single j 1)) := by
      by_contra he
      simp only [he, ↓reduceIte] at h
      exact absurd h (by decide)
    simp [hm, this]

theorem card_kernelPosStabilizer_le
    (hC : C.check = true) (hS : S.check C = true) :
    Nat.card (kernelPosStabilizer (maskChar (τ := τ) (listMask S.mask))) ≤
      (S.passing C).length := by
  classical
  have key : ∀ ω : kernelPosStabilizer (maskChar (τ := τ) (listMask S.mask)),
      ∃ t ∈ (S.passing C).toFinset, C.Represents t ω := fun ω => by
    obtain ⟨t, ht, hrep⟩ := exists_passing_of_mem hC hS ω.2
    exact ⟨t, List.mem_toFinset.2 ht, hrep⟩
  choose f hf hrep using key
  have hinj : Function.Injective fun ω => (⟨f ω, hf ω⟩ : (S.passing C).toFinset) := by
    intro ω ω' h
    have h' : f ω = f ω' := congrArg Subtype.val h
    exact Subtype.ext (represents_unique (hrep ω) (h' ▸ hrep ω'))
  calc Nat.card (kernelPosStabilizer (maskChar (τ := τ) (listMask S.mask)))
      ≤ Nat.card (S.passing C).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (S.passing C).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (S.passing C).length := List.toFinset_card_le _

theorem kernelPosStabilizer_comm_sq
    (hC : C.check = true) (hS : S.check C = true)
    (hE : S.checkElemAb C = true) {ω ω' : WeylGroup τ}
    (hω : ω ∈ kernelPosStabilizer (maskChar (listMask S.mask)))
    (hω' : ω' ∈ kernelPosStabilizer (maskChar (listMask S.mask))) :
    ω * ω' = ω' * ω ∧ ω * ω = 1 := by
  simp only [checkElemAb, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at hE
  obtain ⟨hsq, hcomm⟩ := hE
  obtain ⟨t, ht, hrep⟩ := exists_passing_of_mem hC hS hω
  obtain ⟨t', ht', hrep'⟩ := exists_passing_of_mem hC hS hω'
  refine ⟨ext_single fun j => ?_, ext_single fun j => ?_⟩
  · have h := List.ofFn_injective (hcomm t ht t' ht' j)
    rw [tupleVec_eq hrep, tupleVec_eq hrep', (hrep'.2 j).2, (hrep.2 j).2] at h
    rw [mul_smul, mul_smul]
    exact h
  · have h := List.ofFn_injective (hsq t ht j)
    rw [tupleVec_eq hrep, (hrep.2 j).2] at h
    rw [mul_smul, h, one_smul]

end StabCert

end CFSG.LieType.Chevalley
