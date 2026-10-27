module

public import CFSG.FeitThompson.Representations.CommonColumnCoordinateFailureThreeVector
public import CFSG.FeitThompson.Representations.FourTwoDefectTablePrefixes
public import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

section SuppLt

variable {d r r' : ℕ}

@[expose] def SuppLt (r : ℕ) (u : Fin d → ℤ) : Prop := ∀ k : Fin d, r ≤ (k : ℕ) → u k = 0

theorem suppLt_iff {u : Fin d → ℤ} : SuppLt r u ↔ ∀ k : Fin d, r ≤ (k : ℕ) → u k = 0 := Iff.rfl

theorem SuppLt.mono (h : r ≤ r') {u : Fin d → ℤ} (hu : SuppLt r u) : SuppLt r' u :=
  fun k hk => hu k (by omega)

theorem suppLt_labVec3 {L : ℤ × ℤ × ℤ} (h1 : L.1.natAbs ≤ r) (h2 : L.2.1.natAbs ≤ r)
    (h3 : L.2.2.natAbs ≤ r) : SuppLt r (labVec3 d L) :=
  fun _ hk => labVec3_eq_zero_of_le h1 h2 h3 hk

theorem suppLt_triLevel_labVec3 {L : ℤ × ℤ × ℤ} (h1 : L.1.natAbs < L.2.1.natAbs)
    (h2 : L.2.1.natAbs < L.2.2.natAbs) : SuppLt (triLevel r L) (labVec3 d L) := by
  have hb : L.2.2.natAbs ≤ triLevel r L := natAbs_le_labLevel _ _
  exact suppLt_labVec3 (by omega) (by omega) hb

end SuppLt

section Levels

variable {r r' : ℕ}

theorem labLevel_mono (h : r ≤ r') (a : ℤ) : labLevel r a ≤ labLevel r' a := by
  rw [labLevel, labLevel]; omega

theorem triLevel_mono (h : r ≤ r') (L : ℤ × ℤ × ℤ) : triLevel r L ≤ triLevel r' L :=
  labLevel_mono (labLevel_mono (labLevel_mono h L.1) L.2.1) L.2.2

theorem le_triLevel (r : ℕ) (L : ℤ × ℤ × ℤ) : r ≤ triLevel r L :=
  le_trans (le_trans (le_labLevel _ _) (le_labLevel _ _)) (le_labLevel _ _)

theorem triLevel_le_of_labBounded {d : ℕ} {L : ℤ × ℤ × ℤ} (hL : LabBounded d L) (hr : r ≤ d) :
    triLevel r L ≤ d := by
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩⟩ := hL
  rw [triLevel, labLevel, labLevel, labLevel]
  omega

end Levels

section Normalize

variable {d r : ℕ}

theorem exists_isNormalTri_labVec3_eq {u : Fin d → ℤ} (hu : u ⬝ᵥ u = 3)
    (hpos : ∀ k : Fin d, r ≤ (k : ℕ) → u k = 0 ∨ u k = 1)
    (hdown : ∀ k k' : Fin d, r ≤ (k : ℕ) → (k : ℕ) < (k' : ℕ) → u k' ≠ 0 → u k ≠ 0) :
    ∃ L : ℤ × ℤ × ℤ, IsNormalTri r L ∧ u = labVec3 d L := by
  classical
  have hcard : #({i | u i ≠ 0} : Finset (Fin d)) = 3 :=
    card_support_eq_three_of_dotProduct_self_eq_three hu
  obtain ⟨i₀, i₁, i₂, h01, h12, hu0, hu1, hu2, heq⟩ := exists_sorted_support u hcard
  have hs0 : u i₀ = 1 ∨ u i₀ = -1 := eq_one_or_neg_one_of_dotProduct_self_eq_three hu hu0
  have hs1 : u i₁ = 1 ∨ u i₁ = -1 := eq_one_or_neg_one_of_dotProduct_self_eq_three hu hu1
  have hs2 : u i₂ = 1 ∨ u i₂ = -1 := eq_one_or_neg_one_of_dotProduct_self_eq_three hu hu2
  have hsupp : ∀ k : Fin d, u k ≠ 0 → k = i₀ ∨ k = i₁ ∨ k = i₂ := by
    intro k hk
    by_contra hc
    simp only [not_or] at hc
    exact hk (by rw [heq]; simp [hc.1, hc.2.1, hc.2.2])
  have hlt : ∀ (j : ℕ) (k : Fin d), r ≤ j → j < (k : ℕ) → u k ≠ 0 →
      (j = (i₀ : ℕ) ∨ j = (i₁ : ℕ) ∨ j = (i₂ : ℕ)) := by
    intro j k hrj hjk hk
    have hjd : j < d := lt_trans hjk k.2
    rcases hsupp _ (hdown ⟨j, hjd⟩ k hrj hjk hk) with h | h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (Or.inl (congrArg Fin.val h))
    · exact Or.inr (Or.inr (congrArg Fin.val h))
  refine ⟨(labOf i₀ (u i₀), labOf i₁ (u i₁), labOf i₂ (u i₂)), ⟨labOf_ne_zero i₀ hs0, ?_, ?_,
    ?_, ?_, ?_⟩, ?_⟩
  · change (labOf i₀ (u i₀)).natAbs < (labOf i₁ (u i₁)).natAbs
    rw [natAbs_labOf i₀ hs0, natAbs_labOf i₁ hs1]; omega
  · change (labOf i₁ (u i₁)).natAbs < (labOf i₂ (u i₂)).natAbs
    rw [natAbs_labOf i₁ hs1, natAbs_labOf i₂ hs2]; omega
  · change IsFreshLab r (labOf i₀ (u i₀))
    rw [IsFreshLab, natAbs_labOf i₀ hs0]
    rcases Nat.lt_or_ge (i₀ : ℕ) r with h | h
    · exact Or.inl (by omega)
    · have hr0 : (i₀ : ℕ) = r := by
        by_contra hne
        rcases hlt r i₀ le_rfl (by omega) hu0 with h' | h' | h' <;> omega
      have h1 : u i₀ = 1 := by rcases hpos i₀ h with h' | h' <;> [exact absurd h' hu0; exact h']
      exact Or.inr (by rw [h1, labOf_one]; omega)
  · change IsFreshLab (labLevel r (labOf i₀ (u i₀))) (labOf i₁ (u i₁))
    rw [IsFreshLab, labLevel, natAbs_labOf i₀ hs0, natAbs_labOf i₁ hs1]
    rcases Nat.lt_or_ge (i₁ : ℕ) r with h | h
    · exact Or.inl (by omega)
    · have hr1 : (i₁ : ℕ) = max r ((i₀ : ℕ) + 1) := by
        by_contra hne
        rcases hlt (max r ((i₀ : ℕ) + 1)) i₁ (le_max_left _ _) (by omega) hu1 with
          h' | h' | h' <;> omega
      have h1 : u i₁ = 1 := by rcases hpos i₁ h with h' | h' <;> [exact absurd h' hu1; exact h']
      exact Or.inr (by rw [h1, labOf_one]; omega)
  · change IsFreshLab (labLevel (labLevel r (labOf i₀ (u i₀))) (labOf i₁ (u i₁)))
      (labOf i₂ (u i₂))
    rw [IsFreshLab, labLevel, labLevel, natAbs_labOf i₀ hs0, natAbs_labOf i₁ hs1,
      natAbs_labOf i₂ hs2]
    rcases Nat.lt_or_ge (i₂ : ℕ) r with h | h
    · exact Or.inl (by omega)
    · have hr2 : (i₂ : ℕ) = max (max r ((i₀ : ℕ) + 1)) ((i₁ : ℕ) + 1) := by
        by_contra hne
        rcases hlt (max (max r ((i₀ : ℕ) + 1)) ((i₁ : ℕ) + 1)) i₂
          (le_trans (le_max_left _ _) (le_max_left _ _)) (by omega) hu2 with h' | h' | h' <;> omega
      have h1 : u i₂ = 1 := by rcases hpos i₂ h with h' | h' <;> [exact absurd h' hu2; exact h']
      exact Or.inr (by rw [h1, labOf_one]; omega)
  · rw [labVec3_eq, labVec_labOf i₀ hs0, labVec_labOf i₁ hs1, labVec_labOf i₂ hs2]
    exact heq

theorem exists_signedPermVec_isNormalTri (hr : r ≤ d) {u : Fin d → ℤ} (hu : u ⬝ᵥ u = 3) :
    ∃ (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (L : ℤ × ℤ × ℤ),
      (∀ k : Fin d, (k : ℕ) < r → σ k = k) ∧
      (∀ k : Fin d, r ≤ (k : ℕ) → r ≤ ((σ k : Fin d) : ℕ)) ∧
      (∀ k : Fin d, (k : ℕ) < r → ε k = 1) ∧ (∀ k, ε k = 1 ∨ ε k = -1) ∧
      IsNormalTri r L ∧ signedPermVec σ ε u = labVec3 d L := by
  obtain ⟨σ, ε, S, hσfix, hσge, hεlt, hεsign, hSlt, hScard, hu1, hlen, heq⟩ :=
    exists_signedPermVec_eq_enumCandidate hr hu
  have hw3 : signedPermVec σ ε u ⬝ᵥ signedPermVec σ ε u = 3 := by
    rw [signedPermVec_dotProduct σ hεsign]; exact hu
  have hpos : ∀ k : Fin d, r ≤ (k : ℕ) →
      signedPermVec σ ε u k = 0 ∨ signedPermVec σ ε u k = 1 := by
    intro k hk
    rw [heq, enumCandidate_apply, if_neg (fun h => absurd (hSlt k h) (by omega))]
    by_cases hkn : k ∈ enumNewIdx d r (3 - #S) <;> simp [hkn]
  have hdown : ∀ k k' : Fin d, r ≤ (k : ℕ) → (k : ℕ) < (k' : ℕ) →
      signedPermVec σ ε u k' ≠ 0 → signedPermVec σ ε u k ≠ 0 := by
    intro k k' hk hkk' hk'
    rw [heq, enumCandidate_apply] at hk' ⊢
    rw [if_neg (fun h => absurd (hSlt k h) (by omega))]
    have hk'S : k' ∉ S := fun h => absurd (hSlt k' h) (by omega)
    rw [if_neg hk'S, zero_add] at hk'
    have hk'N : k' ∈ enumNewIdx d r (3 - #S) := by
      by_contra h; rw [if_neg h] at hk'; exact hk' rfl
    rw [mem_enumNewIdx] at hk'N
    rw [if_pos (mem_enumNewIdx.mpr ⟨hk, by omega⟩), zero_add]
    exact one_ne_zero
  obtain ⟨L, hL, hLeq⟩ := exists_isNormalTri_labVec3_eq (r := r) hw3 hpos hdown
  exact ⟨σ, ε, L, hσfix, hσge, hεlt, hεsign, hL, hLeq⟩

end Normalize

section Transport

variable {d d' m n : ℕ}

theorem IsGramArray.signedPermVec {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b)
    (σ : Equiv.Perm (Fin d)) {ε : Fin d → ℤ} (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    IsGramArray (fun i j => signedPermVec σ ε (b i j)) :=
  isGramArray_of_dotProduct
    (fun i j => by rw [signedPermVec_dotProduct σ hε]; exact hb.dotProduct_self i j)
    (fun i _ _ h => by rw [signedPermVec_dotProduct σ hε]; exact hb.dotProduct_row i h)
    (fun h j => by rw [signedPermVec_dotProduct σ hε]; exact hb.dotProduct_col h j)
    (fun h h' => by rw [signedPermVec_dotProduct σ hε]; exact hb.dotProduct_eq_zero h h')

def padVec (d' : ℕ) (u : Fin d → ℤ) : Fin d' → ℤ :=
  fun k' => if h : (k' : ℕ) < d then u ⟨k', h⟩ else 0

theorem padVec_apply (d' : ℕ) (u : Fin d → ℤ) (k' : Fin d') :
    padVec d' u k' = if h : (k' : ℕ) < d then u ⟨k', h⟩ else 0 := (rfl)

theorem padVec_castLE (h : d ≤ d') (u : Fin d → ℤ) (k : Fin d) :
    padVec d' u (Fin.castLE h k) = u k := by
  rw [padVec_apply]
  have hlt : ((Fin.castLE h k : Fin d') : ℕ) < d := k.2
  rw [dif_pos hlt]
  congr 1

theorem padVec_eq_zero {u : Fin d → ℤ} {k' : Fin d'} (hk : d ≤ (k' : ℕ)) :
    padVec d' u k' = 0 := by
  rw [padVec_apply, dif_neg (by omega)]

theorem padVec_dotProduct (h : d ≤ d') (u v : Fin d → ℤ) :
    padVec d' u ⬝ᵥ padVec d' v = u ⬝ᵥ v := by
  classical
  set f : ℕ → ℤ := fun i => (if hi : i < d then u ⟨i, hi⟩ else 0) *
    (if hi : i < d then v ⟨i, hi⟩ else 0) with hf
  have h1 : padVec d' u ⬝ᵥ padVec d' v = ∑ i ∈ Finset.range d', f i := by
    rw [dotProduct, ← Fin.sum_univ_eq_sum_range f d']
    exact Finset.sum_congr rfl fun k _ => rfl
  have h2 : u ⬝ᵥ v = ∑ i ∈ Finset.range d, f i := by
    rw [dotProduct, ← Fin.sum_univ_eq_sum_range f d]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    simp only [dif_pos k.2]
  rw [h1, h2]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) fun i _ hi => ?_).symm
  rw [Finset.mem_range] at hi
  rw [hf]
  simp only [dif_neg (show ¬ i < d by omega), mul_zero]

theorem IsGramArray.padVec (h : d ≤ d') {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) :
    IsGramArray (fun i j => padVec d' (b i j)) := by
  refine isGramArray_of_dotProduct (fun i j => ?_) (fun i _ _ hjl => ?_) (fun hik j => ?_)
    (fun hik hjl => ?_) <;> rw [padVec_dotProduct h]
  · exact hb.dotProduct_self i j
  · exact hb.dotProduct_row i hjl
  · exact hb.dotProduct_col hik j
  · exact hb.dotProduct_eq_zero hik hjl

theorem padVec_labVec3 (h : d ≤ d') {L : ℤ × ℤ × ℤ} (hL : LabBounded d L) :
    padVec d' (labVec3 d L) = labVec3 d' L := by
  obtain ⟨⟨-, hL1⟩, ⟨-, hL2⟩, ⟨-, hL3⟩⟩ := hL
  funext k'
  by_cases hk : (k' : ℕ) < d
  · rw [padVec_apply, dif_pos hk, labVec3_apply, labVec3_apply, labVec_apply, labVec_apply,
      labVec_apply, labVec_apply, labVec_apply, labVec_apply]
  · rw [padVec_apply, dif_neg hk]
    exact (labVec3_eq_zero_of_le (r := d) hL1 hL2 hL3 (by omega)).symm

end Transport

section Shared

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

def sharedSignedCoord (u : ι → ℤ) (a : ι) : ι → ℤ := Pi.single a (u a)

theorem sharedSignedCoord_apply (u : ι → ℤ) (a c : ι) :
    sharedSignedCoord u a c = (Pi.single a (u a) : ι → ℤ) c := (rfl)

theorem isSignedCoordVec_sharedSignedCoord {u : ι → ℤ} {a : ι} (ha : u a = 1 ∨ u a = -1) :
    IsSignedCoordVec (sharedSignedCoord u a) :=
  isSignedCoordVec_single ha

theorem dotProduct_sharedSignedCoord (z u : ι → ℤ) (a : ι) :
    z ⬝ᵥ sharedSignedCoord u a = z a * u a := by
  rw [sharedSignedCoord, dotProduct_single]

end Shared

section SameLine

variable {ι μ ν : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq μ] [DecidableEq ν]

theorem IsGramArray.dotProduct_sharedSignedCoord_eq_zero_or_one [Nontrivial μ] [Nontrivial ν]
    {b : μ → ν → ι → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ : μ} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (j : ν) {a : ι} (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a})
    (ha1 : b i₁ j a = 1 ∨ b i₁ j a = -1) :
    b i₃ j ⬝ᵥ sharedSignedCoord (b i₁ j) a = if b i₃ j a = 0 then 0 else 1 := by
  rw [dotProduct_sharedSignedCoord]
  by_cases h0 : b i₃ j a = 0
  · rw [if_pos h0, h0, zero_mul]
  · rw [if_neg h0]
    have hsign : 0 ≤ b i₃ j a * b i₁ j a :=
      hb.mul_nonneg (i := i₃) (j := j) (k := i₁) (l := j) (by simp [Ne.symm h13]) (Or.inr rfl) a
    have h3 : b i₃ j a = 1 ∨ b i₃ j a = -1 :=
      eq_one_or_neg_one_of_dotProduct_self_eq_three (hb.dotProduct_self i₃ j) h0
    rcases h3 with h | h <;> rcases ha1 with h' | h' <;> rw [h, h'] at hsign ⊢ <;> omega

end SameLine

section LabelObstructions

variable {d : ℕ}

@[expose] def NoOppLab (L M : ℤ × ℤ × ℤ) : Prop :=
  labDot L.1 M.1 ≠ -1 ∧ labDot L.1 M.2.1 ≠ -1 ∧ labDot L.1 M.2.2 ≠ -1 ∧
  labDot L.2.1 M.1 ≠ -1 ∧ labDot L.2.1 M.2.1 ≠ -1 ∧ labDot L.2.1 M.2.2 ≠ -1 ∧
  labDot L.2.2 M.1 ≠ -1 ∧ labDot L.2.2 M.2.1 ≠ -1 ∧ labDot L.2.2 M.2.2 ≠ -1

instance (L M : ℤ × ℤ × ℤ) : Decidable (NoOppLab L M) := by
  unfold NoOppLab; infer_instance

theorem labVec3_apply_eq_sign {L : ℤ × ℤ × ℤ} (h1 : L.1.natAbs < L.2.1.natAbs)
    (h2 : L.2.1.natAbs < L.2.2.natAbs) {k : Fin d} {a : ℤ}
    (ha : a = L.1 ∨ a = L.2.1 ∨ a = L.2.2) (hk : (k : ℕ) + 1 = a.natAbs) :
    labVec3 d L k = a.sign := by
  rw [labVec3_apply, labVec_apply, labVec_apply, labVec_apply]
  rcases ha with rfl | rfl | rfl
  · rw [if_pos hk, if_neg (by omega), if_neg (by omega), add_zero, add_zero]
  · rw [if_neg (by omega), if_pos hk, if_neg (by omega), add_zero, zero_add]
  · rw [if_neg (by omega), if_neg (by omega), if_pos hk, zero_add, zero_add]

theorem labDot_ne_neg_one_of_mul_nonneg {L M : ℤ × ℤ × ℤ}
    (hL1 : L.1.natAbs < L.2.1.natAbs) (hL2 : L.2.1.natAbs < L.2.2.natAbs)
    (hM1 : M.1.natAbs < M.2.1.natAbs) (hM2 : M.2.1.natAbs < M.2.2.natAbs)
    (hLb : LabBounded d L)
    (hsign : ∀ k : Fin d, 0 ≤ labVec3 d L k * labVec3 d M k)
    {a b : ℤ} (ha : a = L.1 ∨ a = L.2.1 ∨ a = L.2.2) (hb : b = M.1 ∨ b = M.2.1 ∨ b = M.2.2) :
    labDot a b ≠ -1 := by
  intro h
  rw [labDot] at h
  have hne : a ≠ b := by intro hc; rw [if_pos hc] at h; omega
  rw [if_neg hne] at h
  have hab : a = -b := by by_contra hc; rw [if_neg hc] at h; omega
  have ha0 : a ≠ 0 := by rintro rfl; exact hne (by omega)
  have hled : a.natAbs ≤ d := by
    obtain ⟨⟨-, e1⟩, ⟨-, e2⟩, ⟨-, e3⟩⟩ := hLb
    rcases ha with rfl | rfl | rfl <;> assumption
  have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  have hkval : ((⟨a.natAbs - 1, by omega⟩ : Fin d) : ℕ) + 1 = a.natAbs := by
    change (a.natAbs - 1) + 1 = a.natAbs
    omega
  have h1 : labVec3 d L (⟨a.natAbs - 1, by omega⟩ : Fin d) = a.sign :=
    labVec3_apply_eq_sign hL1 hL2 ha hkval
  have h2 : labVec3 d M (⟨a.natAbs - 1, by omega⟩ : Fin d) = b.sign :=
    labVec3_apply_eq_sign hM1 hM2 hb (by rw [hkval, hab]; omega)
  have hbs : b.sign = -a.sign := by rw [hab, Int.sign_neg, neg_neg]
  have hkey := hsign (⟨a.natAbs - 1, by omega⟩ : Fin d)
  rw [h1, h2, hbs] at hkey
  rcases ha0.lt_or_gt with hlt | hlt
  · rw [Int.sign_eq_neg_one_of_neg hlt] at hkey; omega
  · rw [Int.sign_eq_one_of_pos hlt] at hkey; omega

theorem noOppLab_of_mul_nonneg {L M : ℤ × ℤ × ℤ}
    (hL1 : L.1.natAbs < L.2.1.natAbs) (hL2 : L.2.1.natAbs < L.2.2.natAbs)
    (hM1 : M.1.natAbs < M.2.1.natAbs) (hM2 : M.2.1.natAbs < M.2.2.natAbs)
    (hLb : LabBounded d L)
    (hsign : ∀ k : Fin d, 0 ≤ labVec3 d L k * labVec3 d M k) : NoOppLab L M :=
  ⟨labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inl rfl) (Or.inl rfl),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inl rfl) (Or.inr (Or.inl rfl)),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inl rfl) (Or.inr (Or.inr rfl)),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inr (Or.inl rfl)) (Or.inl rfl),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inr (Or.inl rfl))
     (Or.inr (Or.inl rfl)),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inr (Or.inl rfl))
     (Or.inr (Or.inr rfl)),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inr (Or.inr rfl)) (Or.inl rfl),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inr (Or.inr rfl))
     (Or.inr (Or.inl rfl)),
   labDot_ne_neg_one_of_mul_nonneg hL1 hL2 hM1 hM2 hLb hsign (Or.inr (Or.inr rfl))
     (Or.inr (Or.inr rfl))⟩

theorem labE_of_isNormalTri {T : ℤ × ℤ × ℤ} (hT : IsNormalTri 6 T)
    (hA : triDot T labA = 1) (hB : triDot T labB = 1) (hC : triDot T labC = 1)
    (nA : NoOppLab T labA) (nB : NoOppLab T labB) (nC : NoOppLab T labC) :
    T = labE 1 ∨ T = labE 2 ∨ T = labE 3 ∨ T = labE 4 :=
  labE_enum T (mem_freshTriples_of_isNormalTri hT) hA hB hC nA nB nC
where
  labE_enum : ∀ T ∈ freshTriples 6, triDot T labA = 1 → triDot T labB = 1 →
      triDot T labC = 1 → NoOppLab T labA → NoOppLab T labB → NoOppLab T labC →
      T = labE 1 ∨ T = labE 2 ∨ T = labE 3 ∨ T = labE 4 := by decide +kernel

@[expose] def IsDefectRowZ (t : ℕ) (U V W Z : ℤ × ℤ × ℤ) : Prop :=
  triDot Z labA = 0 ∧ triDot Z labB = 0 ∧ triDot Z labC = 0 ∧ triDot Z (labE t) = 1 ∧
    triDot Z U = 1 ∧ triDot Z V = 1 ∧ triDot Z W = 1

instance (t : ℕ) (U V W Z : ℤ × ℤ × ℤ) : Decidable (IsDefectRowZ t U V W Z) := by
  unfold IsDefectRowZ; infer_instance

theorem defectTable_no_extension {q : ℕ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)}
    (hq : q ∈ defectTable) {Z : ℤ × ℤ × ℤ}
    (hZ : IsNormalTri (triLevel (triLevel (triLevel 7 q.2.1) q.2.2.1) q.2.2.2) Z) :
    ¬ IsDefectRowZ q.1 q.2.1 q.2.2.1 q.2.2.2 Z :=
  enum q hq Z (mem_freshTriples_of_isNormalTri hZ)
where
  enum : ∀ q ∈ defectTable,
      ∀ Z ∈ freshTriples (triLevel (triLevel (triLevel 7 q.2.1) q.2.2.1) q.2.2.2),
        ¬ IsDefectRowZ q.1 q.2.1 q.2.2.1 q.2.2.2 Z := by decide +kernel

end LabelObstructions

section ABC

variable {d : ℕ}

theorem labBounded_labA' (hd : 6 ≤ d) : LabBounded d labA :=
  ⟨⟨by decide, by change (1 : ℕ) ≤ d; omega⟩, ⟨by decide, by change (2 : ℕ) ≤ d; omega⟩,
    ⟨by decide, by change (3 : ℕ) ≤ d; omega⟩⟩

theorem labBounded_labB' (hd : 6 ≤ d) : LabBounded d labB :=
  ⟨⟨by decide, by change (1 : ℕ) ≤ d; omega⟩, ⟨by decide, by change (4 : ℕ) ≤ d; omega⟩,
    ⟨by decide, by change (5 : ℕ) ≤ d; omega⟩⟩

theorem labBounded_labC' (hd : 6 ≤ d) : LabBounded d labC :=
  ⟨⟨by decide, by change (2 : ℕ) ≤ d; omega⟩, ⟨by decide, by change (4 : ℕ) ≤ d; omega⟩,
    ⟨by decide, by change (6 : ℕ) ≤ d; omega⟩⟩

theorem suppLt_labVec3_labA : SuppLt 6 (labVec3 d labA) :=
  suppLt_labVec3 (by decide) (by decide) (by decide)

theorem suppLt_labVec3_labB : SuppLt 6 (labVec3 d labB) :=
  suppLt_labVec3 (by decide) (by decide) (by decide)

theorem suppLt_labVec3_labC : SuppLt 6 (labVec3 d labC) :=
  suppLt_labVec3 (by decide) (by decide) (by decide)

theorem suppLt_labVec3_labE (t : ℕ) : SuppLt 7 (labVec3 d (labE t)) := by
  rcases labE_cases t with h | h | h | h <;> rw [h] <;>
    exact suppLt_labVec3 (by decide) (by decide) (by decide)

theorem labBounded_labE' (hd : 7 ≤ d) (t : ℕ) : LabBounded d (labE t) := labBounded_labE hd t

theorem labVec3_eq_three_single {i₀ i₁ i₂ : Fin d} {a b c : ℤ}
    (h0 : a = ((i₀ : ℕ) : ℤ) + 1) (h1 : b = ((i₁ : ℕ) : ℤ) + 1) (h2 : c = ((i₂ : ℕ) : ℤ) + 1) :
    labVec3 d (a, b, c) = Pi.single i₀ 1 + Pi.single i₁ 1 + Pi.single i₂ 1 := by
  subst h0 h1 h2
  simpa only [labOf_one] using labVec3_of_labOf i₀ i₁ i₂ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)

theorem labVec3_labA' (h6 : 6 ≤ d) :
    labVec3 d labA = Pi.single (Fin.castLE h6 0) 1 + Pi.single (Fin.castLE h6 1) 1
      + Pi.single (Fin.castLE h6 2) 1 :=
  labVec3_eq_three_single (by simp) (by simp) (by simp)

theorem labVec3_labB' (h6 : 6 ≤ d) :
    labVec3 d labB = Pi.single (Fin.castLE h6 0) 1 + Pi.single (Fin.castLE h6 3) 1
      + Pi.single (Fin.castLE h6 4) 1 :=
  labVec3_eq_three_single (by simp) (by simp) (by simp)

theorem labVec3_labC' (h6 : 6 ≤ d) :
    labVec3 d labC = Pi.single (Fin.castLE h6 1) 1 + Pi.single (Fin.castLE h6 3) 1
      + Pi.single (Fin.castLE h6 5) 1 :=
  labVec3_eq_three_single (by simp) (by simp) (by simp)

end ABC

section Main

variable {d m n r r' : ℕ}

theorem exists_isGramArray_normalize_entry (hr : r ≤ d)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) (i₀ : Fin m) (j₀ : Fin n) :
    ∃ (b' : Fin m → Fin n → Fin d → ℤ) (L : ℤ × ℤ × ℤ), IsGramArray b' ∧ IsNormalTri r L ∧
      b' i₀ j₀ = labVec3 d L ∧ ∀ i j, SuppLt r (b i j) → b' i j = b i j := by
  obtain ⟨σ, ε, L, hσfix, hσge, hεlt, hεsign, hL, hLeq⟩ :=
    exists_signedPermVec_isNormalTri hr (hb.dotProduct_self i₀ j₀)
  exact ⟨fun i j => signedPermVec σ ε (b i j), L, hb.signedPermVec σ hεsign, hL, hLeq,
    fun i j hij => signedPermVec_eq_self hσfix hσge hεlt hij⟩

theorem triDot_of_dotProduct {L M : ℤ × ℤ × ℤ} {u v : Fin d → ℤ} {x : ℤ}
    (hL : LabBounded d L) (hM : LabBounded d M) (hu : u = labVec3 d L) (hv : v = labVec3 d M)
    (h : u ⬝ᵥ v = x) : triDot L M = x := by
  rw [← labVec3_dotProduct hL hM, ← hu, ← hv]; exact h

theorem labBounded_of_eq_labVec3 {L : ℤ × ℤ × ℤ} {u : Fin d → ℤ} (hL : IsNormalTri r L)
    (hu : u = labVec3 d L) (h3 : u ⬝ᵥ u = 3) : LabBounded d L :=
  hL.labBounded_of_dotProduct_self (by rw [← hu]; exact h3)

theorem noOppLab_of_isGramArray {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b)
    {i k : Fin m} {j l : Fin n} (hne : (i, j) ≠ (k, l)) (hline : i = k ∨ j = l)
    (hm : 2 ≤ m) (hn : 2 ≤ n) {L M : ℤ × ℤ × ℤ} (hL : IsNormalTri r L) (hM : IsNormalTri r' M)
    (hu : b i j = labVec3 d L) (hv : b k l = labVec3 d M) : NoOppLab L M := by
  refine noOppLab_of_mul_nonneg hL.2.1 hL.2.2.1 hM.2.1 hM.2.2.1
    (labBounded_of_eq_labVec3 hL hu (hb.dotProduct_self i j)) fun x => ?_
  rw [← hu, ← hv]
  exact mul_nonneg_of_isGramArray_fin hm hn hb hne hline x

theorem isNormalTri_labA : IsNormalTri 6 labA := by decide
theorem isNormalTri_labB : IsNormalTri 6 labB := by decide
theorem isNormalTri_labC : IsNormalTri 6 labC := by decide

theorem exists_labE_fourth (hm : 4 ≤ m) (hn : 2 ≤ n) (hd : 10 ≤ d)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ i₄ : Fin m}
    (h14 : i₁ ≠ i₄) (h24 : i₂ ≠ i₄) (h34 : i₃ ≠ i₄) (j : Fin n)
    (hA : b i₁ j = labVec3 d labA) (hB : b i₂ j = labVec3 d labB)
    (hC : b i₃ j = labVec3 d labC) :
    ∃ (b' : Fin m → Fin n → Fin d → ℤ) (t : ℕ), IsGramArray b' ∧
      (t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) ∧
      b' i₁ j = labVec3 d labA ∧ b' i₂ j = labVec3 d labB ∧ b' i₃ j = labVec3 d labC ∧
      b' i₄ j = labVec3 d (labE t) := by
  have h6 : (6 : ℕ) ≤ d := by omega
  obtain ⟨b', T, hb', hT, hTeq, hfix⟩ :=
    exists_isGramArray_normalize_entry (r := 6) h6 hb i₄ j
  have hA' : b' i₁ j = labVec3 d labA := by
    rw [hfix i₁ j (hA ▸ suppLt_labVec3_labA), hA]
  have hB' : b' i₂ j = labVec3 d labB := by
    rw [hfix i₂ j (hB ▸ suppLt_labVec3_labB), hB]
  have hC' : b' i₃ j = labVec3 d labC := by
    rw [hfix i₃ j (hC ▸ suppLt_labVec3_labC), hC]
  have hbdT : LabBounded d T := labBounded_of_eq_labVec3 hT hTeq (hb'.dotProduct_self i₄ j)
  have hm2 : 2 ≤ m := by omega
  have dA : triDot T labA = 1 := triDot_of_dotProduct hbdT (labBounded_labA' h6) hTeq hA'
    (hb'.dotProduct_col (Ne.symm h14) j)
  have dB : triDot T labB = 1 := triDot_of_dotProduct hbdT (labBounded_labB' h6) hTeq hB'
    (hb'.dotProduct_col (Ne.symm h24) j)
  have dC : triDot T labC = 1 := triDot_of_dotProduct hbdT (labBounded_labC' h6) hTeq hC'
    (hb'.dotProduct_col (Ne.symm h34) j)
  have nA : NoOppLab T labA := noOppLab_of_isGramArray hb'
    (i := i₄) (j := j) (k := i₁) (l := j) (by simp [Ne.symm h14]) (Or.inr rfl) hm2 hn hT
    isNormalTri_labA hTeq hA'
  have nB : NoOppLab T labB := noOppLab_of_isGramArray hb'
    (i := i₄) (j := j) (k := i₂) (l := j) (by simp [Ne.symm h24]) (Or.inr rfl) hm2 hn hT
    isNormalTri_labB hTeq hB'
  have nC : NoOppLab T labC := noOppLab_of_isGramArray hb'
    (i := i₄) (j := j) (k := i₃) (l := j) (by simp [Ne.symm h34]) (Or.inr rfl) hm2 hn hT
    isNormalTri_labC hTeq hC'
  rcases labE_of_isNormalTri hT dA dB dC nA nB nC with h | h | h | h
  · exact ⟨b', 1, hb', Or.inl rfl, hA', hB', hC', by rw [hTeq, h]⟩
  · exact ⟨b', 2, hb', Or.inr (Or.inl rfl), hA', hB', hC', by rw [hTeq, h]⟩
  · exact ⟨b', 3, hb', Or.inr (Or.inr (Or.inl rfl)), hA', hB', hC', by rw [hTeq, h]⟩
  · exact ⟨b', 4, hb', Or.inr (Or.inr (Or.inr rfl)), hA', hB', hC', by rw [hTeq, h]⟩

theorem no_defect_extension_of_normalized (hd : 10 ≤ d) {t : ℕ}
    (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ i₄ : Fin m}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄)
    (h34 : i₃ ≠ i₄) {j j' : Fin n} (hjj' : j ≠ j') {U V W Z : ℤ × ℤ × ℤ}
    (hU : IsNormalTri 7 U) (hV : IsNormalTri (triLevel 7 U) V)
    (hW : IsNormalTri (triLevel (triLevel 7 U) V) W)
    (hZ : IsNormalTri (triLevel (triLevel (triLevel 7 U) V) W) Z)
    (hbdU : LabBounded d U) (hbdV : LabBounded d V) (hbdW : LabBounded d W)
    (hbdZ : LabBounded d Z)
    (hA : b i₁ j = labVec3 d labA) (hB : b i₂ j = labVec3 d labB)
    (hC : b i₃ j = labVec3 d labC) (hE : b i₄ j = labVec3 d (labE t))
    (hU' : b i₁ j' = labVec3 d U) (hV' : b i₂ j' = labVec3 d V)
    (hW' : b i₃ j' = labVec3 d W) (hZ' : b i₄ j' = labVec3 d Z) : False := by
  have h7 : (7 : ℕ) ≤ d := by omega
  have hbdA : LabBounded d labA := labBounded_labA' (by omega)
  have hbdB : LabBounded d labB := labBounded_labB' (by omega)
  have hbdC : LabBounded d labC := labBounded_labC' (by omega)
  have hbdE : LabBounded d (labE t) := labBounded_labE' h7 t
  have hmem : (t, U, V, W) ∈ defectTable := by
    refine defectTriple_mem_defectTable ht hU hV hW
      ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact triDot_of_dotProduct hbdU hbdA hU' hA (hb.dotProduct_row i₁ (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdU hbdB hU' hB (hb.dotProduct_eq_zero h12 (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdU hbdC hU' hC (hb.dotProduct_eq_zero h13 (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdU hbdE hU' hE (hb.dotProduct_eq_zero h14 (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdV hbdB hV' hB (hb.dotProduct_row i₂ (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdV hbdA hV' hA
        (hb.dotProduct_eq_zero (Ne.symm h12) (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdV hbdC hV' hC (hb.dotProduct_eq_zero h23 (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdV hbdE hV' hE (hb.dotProduct_eq_zero h24 (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdU hbdV hU' hV' (hb.dotProduct_col h12 j')
    · exact triDot_of_dotProduct hbdW hbdC hW' hC (hb.dotProduct_row i₃ (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdW hbdA hW' hA
        (hb.dotProduct_eq_zero (Ne.symm h13) (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdW hbdB hW' hB
        (hb.dotProduct_eq_zero (Ne.symm h23) (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdW hbdE hW' hE (hb.dotProduct_eq_zero h34 (Ne.symm hjj'))
    · exact triDot_of_dotProduct hbdU hbdW hU' hW' (hb.dotProduct_col h13 j')
    · exact triDot_of_dotProduct hbdV hbdW hV' hW' (hb.dotProduct_col h23 j')
  refine defectTable_no_extension hmem hZ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact triDot_of_dotProduct hbdZ hbdA hZ' hA
      (hb.dotProduct_eq_zero (Ne.symm h14) (Ne.symm hjj'))
  · exact triDot_of_dotProduct hbdZ hbdB hZ' hB
      (hb.dotProduct_eq_zero (Ne.symm h24) (Ne.symm hjj'))
  · exact triDot_of_dotProduct hbdZ hbdC hZ' hC
      (hb.dotProduct_eq_zero (Ne.symm h34) (Ne.symm hjj'))
  · exact triDot_of_dotProduct hbdZ hbdE hZ' hE (hb.dotProduct_row i₄ (Ne.symm hjj'))
  · exact triDot_of_dotProduct hbdZ hbdU hZ' hU' (hb.dotProduct_col (Ne.symm h14) j')
  · exact triDot_of_dotProduct hbdZ hbdV hZ' hV' (hb.dotProduct_col (Ne.symm h24) j')
  · exact triDot_of_dotProduct hbdZ hbdW hZ' hW' (hb.dotProduct_col (Ne.symm h34) j')

theorem no_defect_extension (hn : 2 ≤ n) (hd : 10 ≤ d) {t : ℕ}
    (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ i₄ : Fin m}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄)
    (h34 : i₃ ≠ i₄) {j j' : Fin n} (hjj' : j ≠ j')
    (hA : b i₁ j = labVec3 d labA) (hB : b i₂ j = labVec3 d labB)
    (hC : b i₃ j = labVec3 d labC) (hE : b i₄ j = labVec3 d (labE t)) : False := by
  have h7 : (7 : ℕ) ≤ d := by omega
  obtain ⟨b1, U, hb1, hU, hUeq, hfix1⟩ :=
    exists_isGramArray_normalize_entry (r := 7) h7 hb i₁ j'
  have hA1 : b1 i₁ j = labVec3 d labA := by
    rw [hfix1 i₁ j (hA ▸ (suppLt_labVec3_labA.mono (by omega))), hA]
  have hB1 : b1 i₂ j = labVec3 d labB := by
    rw [hfix1 i₂ j (hB ▸ (suppLt_labVec3_labB.mono (by omega))), hB]
  have hC1 : b1 i₃ j = labVec3 d labC := by
    rw [hfix1 i₃ j (hC ▸ (suppLt_labVec3_labC.mono (by omega))), hC]
  have hE1 : b1 i₄ j = labVec3 d (labE t) := by
    rw [hfix1 i₄ j (hE ▸ suppLt_labVec3_labE t), hE]
  have hbdU : LabBounded d U := labBounded_of_eq_labVec3 hU hUeq (hb1.dotProduct_self i₁ j')
  have hr2d : triLevel 7 U ≤ d := triLevel_le_of_labBounded hbdU h7
  have hr27 : 7 ≤ triLevel 7 U := le_triLevel _ _
  obtain ⟨b2, V, hb2, hV, hVeq, hfix2⟩ :=
    exists_isGramArray_normalize_entry (r := triLevel 7 U) hr2d hb1 i₂ j'
  have hA2 : b2 i₁ j = labVec3 d labA := by
    rw [hfix2 i₁ j (hA1 ▸ (suppLt_labVec3_labA.mono (by omega))), hA1]
  have hB2 : b2 i₂ j = labVec3 d labB := by
    rw [hfix2 i₂ j (hB1 ▸ (suppLt_labVec3_labB.mono (by omega))), hB1]
  have hC2 : b2 i₃ j = labVec3 d labC := by
    rw [hfix2 i₃ j (hC1 ▸ (suppLt_labVec3_labC.mono (by omega))), hC1]
  have hE2 : b2 i₄ j = labVec3 d (labE t) := by
    rw [hfix2 i₄ j (hE1 ▸ ((suppLt_labVec3_labE t).mono (by omega))), hE1]
  have hU2 : b2 i₁ j' = labVec3 d U := by
    rw [hfix2 i₁ j' (hUeq ▸ suppLt_triLevel_labVec3 hU.2.1 hU.2.2.1), hUeq]
  have hbdV : LabBounded d V := labBounded_of_eq_labVec3 hV hVeq (hb2.dotProduct_self i₂ j')
  have hr3d : triLevel (triLevel 7 U) V ≤ d := triLevel_le_of_labBounded hbdV hr2d
  have hr32 : triLevel 7 U ≤ triLevel (triLevel 7 U) V := le_triLevel _ _
  obtain ⟨b3, W, hb3, hW, hWeq, hfix3⟩ :=
    exists_isGramArray_normalize_entry (r := triLevel (triLevel 7 U) V) hr3d hb2 i₃ j'
  have hA3 : b3 i₁ j = labVec3 d labA := by
    rw [hfix3 i₁ j (hA2 ▸ (suppLt_labVec3_labA.mono (by omega))), hA2]
  have hB3 : b3 i₂ j = labVec3 d labB := by
    rw [hfix3 i₂ j (hB2 ▸ (suppLt_labVec3_labB.mono (by omega))), hB2]
  have hC3 : b3 i₃ j = labVec3 d labC := by
    rw [hfix3 i₃ j (hC2 ▸ (suppLt_labVec3_labC.mono (by omega))), hC2]
  have hE3 : b3 i₄ j = labVec3 d (labE t) := by
    rw [hfix3 i₄ j (hE2 ▸ ((suppLt_labVec3_labE t).mono (by omega))), hE2]
  have hU3 : b3 i₁ j' = labVec3 d U := by
    rw [hfix3 i₁ j' (hU2 ▸ ((suppLt_triLevel_labVec3 (r := 7) hU.2.1 hU.2.2.1).mono hr32)), hU2]
  have hV3 : b3 i₂ j' = labVec3 d V := by
    rw [hfix3 i₂ j' (hVeq ▸ suppLt_triLevel_labVec3 hV.2.1 hV.2.2.1), hVeq]
  have hbdW : LabBounded d W := labBounded_of_eq_labVec3 hW hWeq (hb3.dotProduct_self i₃ j')
  have hr4d : triLevel (triLevel (triLevel 7 U) V) W ≤ d := triLevel_le_of_labBounded hbdW hr3d
  have hr43 : triLevel (triLevel 7 U) V ≤ triLevel (triLevel (triLevel 7 U) V) W :=
    le_triLevel _ _
  obtain ⟨b4, Z, hb4, hZ, hZeq, hfix4⟩ := exists_isGramArray_normalize_entry
    (r := triLevel (triLevel (triLevel 7 U) V) W) hr4d hb3 i₄ j'
  have hA4 : b4 i₁ j = labVec3 d labA := by
    rw [hfix4 i₁ j (hA3 ▸ (suppLt_labVec3_labA.mono (by omega))), hA3]
  have hB4 : b4 i₂ j = labVec3 d labB := by
    rw [hfix4 i₂ j (hB3 ▸ (suppLt_labVec3_labB.mono (by omega))), hB3]
  have hC4 : b4 i₃ j = labVec3 d labC := by
    rw [hfix4 i₃ j (hC3 ▸ (suppLt_labVec3_labC.mono (by omega))), hC3]
  have hE4 : b4 i₄ j = labVec3 d (labE t) := by
    rw [hfix4 i₄ j (hE3 ▸ ((suppLt_labVec3_labE t).mono (by omega))), hE3]
  have hU4 : b4 i₁ j' = labVec3 d U := by
    rw [hfix4 i₁ j' (hU3 ▸ ((suppLt_triLevel_labVec3 (r := 7) hU.2.1 hU.2.2.1).mono
      (by omega))), hU3]
  have hV4 : b4 i₂ j' = labVec3 d V := by
    rw [hfix4 i₂ j' (hV3 ▸ ((suppLt_triLevel_labVec3 (r := triLevel 7 U) hV.2.1
      hV.2.2.1).mono hr43)), hV3]
  have hW4 : b4 i₃ j' = labVec3 d W := by
    rw [hfix4 i₃ j' (hWeq ▸ suppLt_triLevel_labVec3 hW.2.1 hW.2.2.1), hWeq]
  have hbdZ : LabBounded d Z := labBounded_of_eq_labVec3 hZ hZeq (hb4.dotProduct_self i₄ j')
  exact no_defect_extension_of_normalized hd ht hb4 h12 h13 h14 h23 h24 h34 hjj' hU hV hW hZ
    hbdU hbdV hbdW hbdZ hA4 hB4 hC4 hE4 hU4 hV4 hW4 hZeq

theorem IsGramArray.mem_support_of_four_rows (hn : 2 ≤ n) {b : Fin m → Fin n → Fin d → ℤ}
    (hb : IsGramArray b) {i₁ i₂ i₃ i₄ : Fin m} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h34 : i₃ ≠ i₄) (j : Fin n) {a : Fin d}
    (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a}) :
    b i₃ j a ≠ 0 := by
  intro hza
  have hm4 : 4 ≤ m := by
    have : Function.Injective ![i₁, i₂, i₃, i₄] := by
      rw [← List.nodup_ofFn]
      simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or,
        and_true, not_false_eq_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
    simpa using Fintype.card_le_of_injective _ this
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j', hj'⟩ := exists_ne j
  obtain ⟨h6, σ, ε, hεsign, hA, hB, hC⟩ :=
    exists_signedPermVec_normalization_of_isGramArray_fin hn hb h12 h13 h23 j ha hza
  rw [← labVec3_labA' h6] at hA
  rw [← labVec3_labB' h6] at hB
  rw [← labVec3_labC' h6] at hC
  have hdd' : d ≤ max d 10 := le_max_left _ _
  have h10 : 10 ≤ max d 10 := le_max_right _ _
  set c : Fin m → Fin n → Fin (max d 10) → ℤ :=
    fun i k => CFSG.FeitThompson.padVec (max d 10)
      (CFSG.FeitThompson.signedPermVec σ ε (b i k)) with hcdef
  have hc : IsGramArray c := (hb.signedPermVec σ hεsign).padVec hdd'
  have hcA : c i₁ j = labVec3 (max d 10) labA := by
    rw [hcdef]; simp only []; rw [hA, padVec_labVec3 hdd' (labBounded_labA' h6)]
  have hcB : c i₂ j = labVec3 (max d 10) labB := by
    rw [hcdef]; simp only []; rw [hB, padVec_labVec3 hdd' (labBounded_labB' h6)]
  have hcC : c i₃ j = labVec3 (max d 10) labC := by
    rw [hcdef]; simp only []; rw [hC, padVec_labVec3 hdd' (labBounded_labC' h6)]
  obtain ⟨c', t, hc', ht, hA', hB', hC', hE'⟩ :=
    exists_labE_fourth hm4 hn h10 hc h14 h24 h34 j hcA hcB hcC
  exact no_defect_extension hn h10 ht hc' h12 h13 h14 h23 h24 h34 (Ne.symm hj')
    hA' hB' hC' hE'

theorem dotProduct_sharedSignedCoord_eq_one_of_four_rows (hm : 4 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ i₄ : Fin m}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄)
    (h34 : i₃ ≠ i₄) (j : Fin n) {a : Fin d}
    (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a})
    (ha1 : b i₁ j a = 1 ∨ b i₁ j a = -1) :
    b i₃ j ⬝ᵥ sharedSignedCoord (b i₁ j) a = 1 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [hb.dotProduct_sharedSignedCoord_eq_zero_or_one h12 h13 j ha ha1,
    if_neg (hb.mem_support_of_four_rows hn h12 h13 h14 h23 h24 h34 j ha)]

theorem exists_sharedSignedCoord_dotProduct_eq_one (hm : 4 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ i₄ : Fin m}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄)
    (h34 : i₃ ≠ i₄) (j : Fin n) :
    ∃ a : Fin d, Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a} ∧
      IsSignedCoordVec (sharedSignedCoord (b i₁ j) a) ∧
      b i₃ j ⬝ᵥ sharedSignedCoord (b i₁ j) a = 1 := by
  obtain ⟨a, ha, -, ha1⟩ := exists_support_inter_eq_singleton_of_isGramArray_fin
    (by omega : 2 ≤ m) hn hb (i := i₁) (j := j) (k := i₂) (l := j) (by simp [h12]) (Or.inr rfl)
  exact ⟨a, ha, isSignedCoordVec_sharedSignedCoord ha1,
    dotProduct_sharedSignedCoord_eq_one_of_four_rows hm hn hb h12 h13 h14 h23 h24 h34 j ha ha1⟩

end Main

end CFSG.FeitThompson
