module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Cand
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix Finset

@[expose] def reps : List M4 :=
  (fVecs.filter fun w => w ≠ 0).map fun w =>
    (q0List.find? fun A => decide (A *ᵥ zpVec = tVec + w)).getD 1

@[expose] def omList : List V4 :=
  (List.range 16).map fun k => fun i : Fin 4 => if k.testBit i.val then (2 : ZMod 4) else 0

@[expose] def q0R : List R4 := q0List.map toR4

@[expose] def shatR : List R4 := shatList.map toR4

@[expose] def repsR : List R4 := reps.map toR4

@[expose] def candR : List R4 := candList.map toR4

@[expose] def fR : List RV := fVecs.map toRV

@[expose] def omR : List RV := omList.map toRV

@[expose] def tRV : RV := toRV tVec

@[expose] def zpRV : RV := toRV zpVec

@[expose] def sList (α : M4) : List M4 :=
  q0List ++ reps.flatMap fun r => q0List.map fun q => r * α * q

@[expose] def sListR (α : R4) : List R4 :=
  q0R ++ repsR.flatMap fun r => q0R.map fun q => rmul (rmul r α) q

theorem map_ofR4_toR4 (l : List M4) : (l.map toR4).map ofR4 = l := by
  simp [List.map_map, Function.comp_def, ofR4_toR4]

theorem sList_eq (α : M4) : sList α = (sListR (toR4 α)).map ofR4 := by
  simp only [sList, sListR, q0R, repsR, List.map_append, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, ofR4_rmul, ofR4_toR4, List.map_id']

@[expose] def cListR (α : R4) : List R4 :=
  (sListR α).filter fun a => fR.all fun v => rmv a v == v

@[expose] def tListR (α : R4) : List R4 :=
  ((cListR α).flatMap fun c => shatR.map fun s => rmul c s).dedup

@[expose] def tList (α : M4) : List M4 := (tListR (toR4 α)).map ofR4

@[expose] def invPairs (tl : List M4) : List (M4 × M4) :=
  tl.flatMap fun A => (tl.filter fun A' => decide (A * A' = 1)).map fun A' => (A, A')

@[expose] def clSet (tl : List M4) (B : M4) : Finset M4 :=
  ((invPairs tl).map fun p => p.1 * B * p.2).toFinset

theorem mem_invPairs_iff {tl : List M4} {p : M4 × M4} :
    p ∈ invPairs tl ↔ p.1 ∈ tl ∧ p.2 ∈ tl ∧ p.1 * p.2 = 1 := by
  simp only [invPairs, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨A, hA, A', ⟨hA', hAA⟩, rfl⟩
    exact ⟨hA, hA', hAA⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p.1, h1, p.2, ⟨h2, h3⟩, rfl⟩

theorem mem_invPairs {tl : List M4} {p : M4 × M4} (hp : p ∈ invPairs tl) :
    p.1 ∈ tl ∧ p.2 ∈ tl ∧ p.1 * p.2 = 1 := mem_invPairs_iff.1 hp

theorem mem_clSet {tl : List M4} {B B' : M4} :
    B' ∈ clSet tl B ↔ ∃ p ∈ invPairs tl, p.1 * B * p.2 = B' := by
  simp [clSet]

@[expose] def imSet (B : M4) : Finset V4 := Finset.univ.image fun v : V4 => (1 - B) *ᵥ v

structure TFactsOf (sl tl : List M4) : Prop where
  one_mem : (1 : M4) ∈ tl
  mul_mem : ∀ A ∈ tl, ∀ B ∈ tl, A * B ∈ tl
  inv_mem : ∀ A ∈ tl, ∃ B ∈ tl, A * B = 1
  sub_s : ∀ A ∈ tl, A ∈ sl
  shat_sub : ∀ s ∈ shatList, s ∈ tl
  pow128 : ∀ A ∈ tl, A ^ 128 = 1
  star : ∀ B ∈ tl, B ≠ 1 → B * B = 1 → 5 ≤ ∑ B' ∈ clSet (tl) B, (imSet B').card
  fsmall : ∀ v ∈ fVecs, ((tl).map fun A => A *ᵥ v).toFinset.card ≤ 4
  tflarge : ∀ v ∈ fVecs, 4 < ((tl).map fun A => A *ᵥ (tVec + v)).toFinset.card
  ftrans : ∀ v ∈ fVecs, ∃ A ∈ tl, A *ᵥ tVec = tVec + v
  cfsq : ∀ A ∈ tl, (∀ v ∈ fVecs, A *ᵥ v = v) → A * A = 1
  kker : ∀ A ∈ tl, (∀ v : V4, v + v = 0 → A *ᵥ v = v) → A = 1 ∨ A = -1
  stab_t : ∀ A ∈ tl, A *ᵥ tVec = tVec → A ∈ shatList
  normalizer : ∀ B ∈ sl, B ∉ tl → ∃ A ∈ tl, ∀ A' ∈ tl, B * A ≠ A' * B

abbrev TFacts (α : M4) : Prop := TFactsOf (sList α) (tList α)

structure Q0Facts : Prop where
  shat_sub : ∀ s ∈ shatList, s ∈ q0List
  fix_t : ∀ A ∈ q0List, A *ᵥ tVec = tVec
  f_zero : (0 : V4) ∈ fVecs
  f_add : ∀ u ∈ fVecs, ∀ v ∈ fVecs, u + v ∈ fVecs
  f_two : ∀ v ∈ fVecs, v + v = 0
  om_f : ∀ v : V4, v + v = 0 → v ∈ fVecs ∨ v - tVec ∈ fVecs
  om_card : (Finset.univ.filter fun v : V4 => v + v = 0).card = 16
  om_list : ∀ v ∈ omList, v + v = 0
  om_sq : ∀ v : V4, v + v = 0 → ∃ w, w + w = v
  zm_mem : zmVec ∈ fVecs
  zp_eq : zpVec = tVec + zmVec
  t_two : tVec + tVec = 0
  zm_trans : ∀ w ∈ fVecs, w ≠ 0 → ∃ A ∈ q0List, A *ᵥ zmVec = w
  reps_mem : ∀ r ∈ reps, r ∈ q0List
  reps_spec : ∀ w ∈ fVecs, w ≠ 0 → ∃ r ∈ reps, r *ᵥ zpVec = tVec + w
  two_f : fVec + fVec = tVec
  neg_f : -fVec ≠ fVec
  sq_coset : ∀ v : V4, (∃ u ∈ fVecs, v + v = tVec + u) → ∃ u ∈ fVecs, (v - fVec) + (v - fVec) = u

@[expose] def Norm1 (A : M4) : Prop := ∀ s ∈ shatList, ∃ s' ∈ shatList, A * s = s' * A

@[expose] def Norm2 (A : M4) : Prop := ∀ s' ∈ shatList, ∃ s ∈ shatList, A * s = s' * A

@[expose] def Concl (A : M4) : Prop :=
  A *ᵥ tVec = tVec ∨ (A *ᵥ tVec = zpVec ∧ A ∈ candList)

@[expose] def NormComplete : Prop :=
  ∀ A : M4, (∃ A' : M4, A * A' = 1 ∧ A' * A = 1) → Norm1 A → Norm2 A → Concl A

@[expose] def alpha1 : M4 := matOfList [3, 3, 1, 0, 0, 3, 2, 1, 2, 0, 3, 0, 0, 0, 0, 1]

@[expose] def alpha2 : M4 := matOfList [3, 3, 3, 0, 0, 3, 2, 1, 2, 0, 3, 0, 0, 0, 0, 1]

@[expose] def alphaReps : List M4 := [alpha1, alpha2]

@[expose] def CandFacts : Prop :=
  (∀ A ∈ candList, A *ᵥ tVec = zpVec ∧ A *ᵥ zpVec = tVec) ∧ (∀ α ∈ alphaReps, α ∈ candList) ∧
  ∀ A ∈ candList, (∀ p ∈ q0List, p *ᵥ zpVec = zpVec → ∃ q ∈ q0List, p * A = A * q) →
    A * A ∈ q0List → ∃ α₀ ∈ alphaReps, ∃ r ∈ reps, ∃ q ∈ q0List, A = r * α₀ * q

@[expose] def AlphaFacts : Prop := ∀ α₀ ∈ alphaReps, TFacts α₀

theorem alphaFacts_of (h1 : TFacts alpha1) (h2 : TFacts alpha2) : AlphaFacts := by
  intro α₀ hα₀
  simp only [alphaReps, List.mem_cons, List.not_mem_nil, or_false] at hα₀
  rcases hα₀ with rfl | rfl
  · exact h1
  · exact h2

end CFSG.EvenSporadicStandard.TwoHS
