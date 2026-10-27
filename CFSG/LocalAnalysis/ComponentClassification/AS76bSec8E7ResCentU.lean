module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF4Perfect
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7LineTransport
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcResCent

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)
open scoped commutatorElement

local instance e7ResCentUNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem commutatorElement_mul_left_eq_three {G : Type*} [Group G] (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, ⁅y, z⁆⁆ * ⁅y, z⁆ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

theorem sum_map_single_apply_ite {K : Type} [Field K] {l : List (Fin Tag.E7.rank → ℤ)}
    (hnd : l.Nodup) (β₀ : Fin Tag.E7.rank → ℤ) (v : K) :
    (l.map fun β => (Pi.single β₀ v : (Fin Tag.E7.rank → ℤ) → K) β).sum =
      if β₀ ∈ l then v else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, ih hnd.2]
    by_cases ha : a = β₀
    · subst ha
      rw [Pi.single_eq_same, ite_eq_left List.mem_cons_self, ite_eq_right hnd.1, add_zero]
    · rw [Pi.single_eq_of_ne ha, zero_add]
      by_cases hb : β₀ ∈ l
      · rw [ite_eq_left hb, ite_eq_left (List.mem_cons_of_mem _ hb)]
      · have : β₀ ∉ a :: l := by
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm ha, hb⟩
        rw [ite_eq_right hb, ite_eq_right this]

theorem mem_uPsi_of_decide {β : Fin Tag.E7.rank → ℤ} (h : decide (β ∈ uPsi) = true) :
    β ∈ uPsi :=
  of_decide_eq_true h

theorem mem_uHigh_of_decide {β : Fin Tag.E7.rank → ℤ} (h : decide (β ∈ uHigh) = true) :
    β ∈ uHigh :=
  of_decide_eq_true h

section Radical

variable {K : Type} [Field K]

theorem e7FrameElt_uFrame (d : K) :
    e7FrameElt K uFrame d =
      EPilot.pinnedElt .E7 uφ d * EPilot.pinnedElt .E7 uψ d * EPilot.pinnedElt .E7 uθ d := by
  apply Subtype.ext
  rw [coe_e7FrameElt, uFrame_eq]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Subgroup.coe_mul]
  rw [mul_assoc]

theorem e7RepConj_three_eq_e7WeylRep : e7RepConj K 3 = e7WeylRep K (e7RepWeyl 3) :=
  rfl

theorem mem_parabolicRadicalRoots_of_mem_uPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) :
    β ∈ parabolicRadicalRoots .E7 uNodes := by
  refine ⟨pos_of_mem_uPsi hβ, fun h => ?_⟩
  have h6 : β 6 = 0 := h.1.2 6 (by simp [uNodes])
  have h1 := level_of_mem_uPsi hβ
  simp only [uLevel] at h1
  omega

variable (K) in
noncomputable abbrev radicalAS : Subgroup (adjointGroup .E7 K) :=
  (parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K)

theorem pinnedElt_mem_radicalAS {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) (t : K) :
    EPilot.pinnedElt .E7 β t ∈ radicalAS K :=
  mem_subgroupOf.2 (pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_of_mem_uPsi hβ) t)

theorem commutator_mem_radicalAS_uF4AS {g x : adjointGroup .E7 K} (hg : g ∈ uF4AS K)
    (hx : x ∈ radicalAS K) : ⁅g, x⁆ ∈ ⁅radicalAS K, uF4AS K⁆ := by
  rw [commutator_comm]
  exact commutator_mem_commutator hg hx

end Radical

section Main

variable {K : Type} [Field K]


theorem exists_rootProd_uPsi_of_mem_parabolicRadical {q : ModGL .E7 K}
    (hq : q ∈ parabolicRadical .E7 K uNodes) : ∃ c, q = rootProd .E7 K uPsi c := by
  let R : Subgroup (ModGL .E7 K) :=
    { carrier := {g | ∃ c, g = rootProd .E7 K uPsi c}
      mul_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
        exact ⟨c + d, (E6Pilot.rootProd_add uPsi_comm c d).symm⟩
      one_mem' := ⟨0, (E6Pilot.rootProd_zero uPsi).symm⟩
      inv_mem' := by
        rintro _ ⟨c, rfl⟩
        refine ⟨-c, (eq_inv_of_mul_eq_one_left ?_).symm⟩
        rw [← E6Pilot.rootProd_add uPsi_comm, neg_add_cancel, E6Pilot.rootProd_zero] }
  have hle : parabolicRadical .E7 K uNodes ≤ R :=
    iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
      rintro _ ⟨t, rfl⟩
      exact ⟨Pi.single α t, (E6Pilot.rootProd_single uPsi_nodup
        (mem_uPsi_of_mem_parabolicRadicalRoots hα) t).symm⟩)
  exact hle hq

theorem conjCoeff_apply_ite {l : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (hlr : ∀ β ∈ l, IsRoot .E7 β) (α : Fin Tag.E7.rank → ℤ) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ l) :
    conjCoeff α t l c ρ = c ρ + if ρ - α ∈ l ∧ α ≠ ρ - α then t * c (ρ - α) else 0 := by
  classical
  rw [conjCoeff, E6Pilot.list_sum_apply, List.map_map]
  have e : ∀ β ∈ l, ((fun f : (Fin Tag.E7.rank → ℤ) → K => f ρ) ∘ fun β => Pi.single β (c β) +
      if α ≠ β ∧ IsRoot .E7 (α + β) then Pi.single (α + β) (t * c β) else 0) β =
      (Pi.single β (c β) : (Fin Tag.E7.rank → ℤ) → K) ρ +
        (Pi.single (ρ - α) (if α ≠ ρ - α then t * c (ρ - α) else 0) :
          (Fin Tag.E7.rank → ℤ) → K) β := by
    intro β _
    simp only [Function.comp_apply, Pi.add_apply]
    congr 1
    by_cases hβ : β = ρ - α
    · subst hβ
      have hs : α + (ρ - α) = ρ := by abel
      rw [Pi.single_eq_same]
      by_cases hne : α ≠ ρ - α
      · have hr : IsRoot .E7 (α + (ρ - α)) := by rw [hs]; exact hlr ρ hρ
        rw [ite_eq_left ⟨hne, hr⟩, ite_eq_left hne, hs, Pi.single_eq_same]
      · rw [ite_eq_right fun h => hne h.1, ite_eq_right hne]
        rfl
    · have hs : α + β ≠ ρ := fun h => hβ (by rw [← h]; abel)
      rw [Pi.single_eq_of_ne hβ]
      split_ifs
      · exact Pi.single_eq_of_ne (Ne.symm hs) _
      · rfl
  rw [List.map_congr_left e, List.sum_map_add, E6Pilot.list_sum_single_apply hnd hρ c,
    sum_map_single_apply_ite hnd]
  congr 1
  by_cases h1 : ρ - α ∈ l <;> by_cases h2 : α ≠ ρ - α <;> simp [h1, h2]

theorem conjCoeff_uPsi_apply {α : Fin Tag.E7.rank → ℤ} (hα0 : uLevel α = 0) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ uPsi) :
    conjCoeff α t uPsi c ρ = c ρ + if ρ - α ∈ uPsi then t * c (ρ - α) else 0 := by
  rw [conjCoeff_apply_ite uPsi_nodup (fun _ h => isRoot_of_mem_uPsi h) α t c hρ]
  by_cases h : ρ - α ∈ uPsi
  · rw [ite_eq_left ⟨h, (ne_of_uLevel_zero hα0 h).1⟩, ite_eq_left h]
  · rw [ite_eq_right fun h' => h h'.1, ite_eq_right h]

theorem conjCoeff_eq_of_commute [CharP K 2] {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hα0 : uLevel α = 0) {c : (Fin Tag.E7.rank → ℤ) → K}
    (h : pinnedX .E7 K α 1 * rootProd .E7 K uPsi c = rootProd .E7 K uPsi c * pinnedX .E7 K α 1) :
    ∀ ρ ∈ uPsi, conjCoeff α 1 uPsi c ρ = c ρ := by
  have e := conj_rootProd_uPsi hα hα0.ge 1 c
  rw [h, mul_inv_cancel_right] at e
  exact E6Pilot.rootProd_injective uPsi_nodup (fun β hβ => pos_of_mem_uPsi hβ) e.symm

theorem conjCoeff_pair_eq_of_commute [CharP K 2] {a b : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (ha0 : uLevel a = 0) (hb0 : uLevel b = 0)
    {c : (Fin Tag.E7.rank → ℤ) → K}
    (h : pinnedX .E7 K a 1 * pinnedX .E7 K b 1 * rootProd .E7 K uPsi c =
      rootProd .E7 K uPsi c * (pinnedX .E7 K a 1 * pinnedX .E7 K b 1)) :
    ∀ ρ ∈ uPsi, conjCoeff a 1 uPsi (conjCoeff b 1 uPsi c) ρ = c ρ := by
  have e : rootProd .E7 K uPsi (conjCoeff a 1 uPsi (conjCoeff b 1 uPsi c)) =
      rootProd .E7 K uPsi c := by
    rw [← conj_rootProd_uPsi ha ha0.ge, ← conj_rootProd_uPsi hb hb0.ge]
    calc pinnedX .E7 K a 1 * (pinnedX .E7 K b 1 * rootProd .E7 K uPsi c *
          (pinnedX .E7 K b 1)⁻¹) * (pinnedX .E7 K a 1)⁻¹ =
        pinnedX .E7 K a 1 * pinnedX .E7 K b 1 * rootProd .E7 K uPsi c *
          (pinnedX .E7 K a 1 * pinnedX .E7 K b 1)⁻¹ := by group
      _ = rootProd .E7 K uPsi c := by rw [h]; group
  exact E6Pilot.rootProd_injective uPsi_nodup (fun β hβ => pos_of_mem_uPsi hβ) e

@[expose] def uKillB (α ρ β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ uPsi) && decide (ρ - α = β) && decide (β ∈ uPsi)

theorem uKill {α : Fin Tag.E7.rank → ℤ} {c : (Fin Tag.E7.rank → ℤ) → K}
    (hc : uLevel α = 0 ∧ ∀ ρ ∈ uPsi, conjCoeff α 1 uPsi c ρ = c ρ) {ρ β : Fin Tag.E7.rank → ℤ}
    (h : uKillB α ρ β = true) : c β = 0 := by
  simp only [uKillB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hρ, hβ⟩, hβΨ⟩ := h
  have e := hc.2 ρ hρ
  rw [conjCoeff_uPsi_apply hc.1 1 c hρ, hβ, ite_eq_left hβΨ, one_mul, add_eq_left] at e
  exact e

theorem uPairRel {a b : Fin Tag.E7.rank → ℤ} {c : (Fin Tag.E7.rank → ℤ) → K}
    (hc : uLevel a = 0 ∧ uLevel b = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff a 1 uPsi (conjCoeff b 1 uPsi c) ρ = c ρ)
    {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ uPsi) :
    ((if ρ - b ∈ uPsi then c (ρ - b) else 0) +
      if ρ - a ∈ uPsi then c (ρ - a) + (if ρ - a - b ∈ uPsi then c (ρ - a - b) else 0)
        else 0) = 0 := by
  obtain ⟨ha0, hb0, hc⟩ := hc
  have h := hc ρ hρ
  rw [conjCoeff_uPsi_apply ha0 1 _ hρ, conjCoeff_uPsi_apply hb0 1 c hρ] at h
  by_cases h1 : ρ - a ∈ uPsi
  · rw [ite_eq_left h1, conjCoeff_uPsi_apply hb0 1 c h1] at h
    rw [ite_eq_left h1]
    simp only [one_mul] at h
    linear_combination h
  · rw [ite_eq_right h1] at h ⊢
    simp only [one_mul, add_zero] at h ⊢
    linear_combination h

@[expose] def uPairKillBB (a b ρ β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ uPsi) && decide (ρ - b = β) && decide (β ∈ uPsi) && decide (ρ - a ∉ uPsi)

@[expose] def uPairKillAB (a b ρ β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ uPsi) && decide (ρ - b ∉ uPsi) && decide (ρ - a = β) && decide (β ∈ uPsi) &&
    decide (β - b ∉ uPsi)

@[expose] def uPairThreeB (a b ρ β₁ β₂ β₃ : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ uPsi) && decide (ρ - b = β₁) && decide (β₁ ∈ uPsi) && decide (ρ - a = β₂) &&
    decide (β₂ ∈ uPsi) && decide (β₂ - b = β₃) && decide (β₃ ∈ uPsi)

theorem uPairKillB {a b : Fin Tag.E7.rank → ℤ} {c : (Fin Tag.E7.rank → ℤ) → K}
    (hc : uLevel a = 0 ∧ uLevel b = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff a 1 uPsi (conjCoeff b 1 uPsi c) ρ = c ρ)
    {ρ β : Fin Tag.E7.rank → ℤ} (h : uPairKillBB a b ρ β = true) : c β = 0 := by
  simp only [uPairKillBB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hρ, hb⟩, hβ⟩, ha⟩ := h
  have e := uPairRel hc hρ
  rw [ite_eq_right ha, add_zero, hb, ite_eq_left hβ] at e
  exact e

theorem uPairKillA {a b : Fin Tag.E7.rank → ℤ} {c : (Fin Tag.E7.rank → ℤ) → K}
    (hc : uLevel a = 0 ∧ uLevel b = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff a 1 uPsi (conjCoeff b 1 uPsi c) ρ = c ρ)
    {ρ β : Fin Tag.E7.rank → ℤ} (h : uPairKillAB a b ρ β = true) : c β = 0 := by
  simp only [uPairKillAB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hρ, hb⟩, ha⟩, hβ⟩, hab⟩ := h
  have e := uPairRel hc hρ
  rw [ite_eq_right hb, zero_add, ha, ite_eq_left hβ, ite_eq_right hab, add_zero] at e
  exact e

theorem uPairThree {a b : Fin Tag.E7.rank → ℤ} {c : (Fin Tag.E7.rank → ℤ) → K}
    (hc : uLevel a = 0 ∧ uLevel b = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff a 1 uPsi (conjCoeff b 1 uPsi c) ρ = c ρ)
    {ρ β₁ β₂ β₃ : Fin Tag.E7.rank → ℤ} (h : uPairThreeB a b ρ β₁ β₂ β₃ = true) :
    c β₁ + (c β₂ + c β₃) = 0 := by
  simp only [uPairThreeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hρ, hb⟩, h1⟩, ha⟩, h2⟩, hab⟩, h3⟩ := h
  have e := uPairRel hc hρ
  rw [hb, ite_eq_left h1, ha, ite_eq_left h2, hab, ite_eq_left h3] at e
  exact e

theorem mem_e7FrameLine_uFrame_of_commute_gens [CharP K 2] {q : adjointGroup .E7 K}
    (hq : (q : ModGL .E7 K) ∈ parabolicRadical .E7 K uNodes)
    (hX : ∀ j, q * uGX K j 1 = uGX K j 1 * q) (hY : ∀ j, q * uGY K j 1 = uGY K j 1 * q) :
    q ∈ e7FrameLine K uFrame := by
  obtain ⟨c, hc⟩ := exists_rootProd_uPsi_of_mem_parabolicRadical hq
  obtain ⟨x0, x1, x2, x3⟩ := uOrbitX_eq (K := K) 1
  obtain ⟨y0, y1, -, y3⟩ := uOrbitY_eq (K := K) 1
  have cX : ∀ j, uOrbitX K j 1 * rootProd .E7 K uPsi c =
      rootProd .E7 K uPsi c * uOrbitX K j 1 := by
    intro j
    have h := congrArg Subtype.val (hX j)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc] at h
    exact h.symm
  have cY : ∀ j, uOrbitY K j 1 * rootProd .E7 K uPsi c =
      rootProd .E7 K uPsi c * uOrbitY K j 1 := by
    intro j
    have h := congrArg Subtype.val (hY j)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc] at h
    exact h.symm
  have l : ∀ i : Fin Tag.E7.rank, i ≠ 6 → uLevel (Pi.single i 1) = 0 ∧
      uLevel (-Pi.single i 1) = 0 := uLevel_single_check
  have hX0 : uLevel (Pi.single 1 1) = 0 ∧ ∀ ρ ∈ uPsi, conjCoeff (Pi.single 1 1) 1 uPsi c ρ = c ρ :=
    ⟨(l 1 (by decide)).1, conjCoeff_eq_of_commute (isRoot_single .E7 1) (l 1 (by decide)).1
      (by rw [← x0]; exact cX 0)⟩
  have hY0 : uLevel (-Pi.single 1 1) = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff (-Pi.single 1 1) 1 uPsi c ρ = c ρ :=
    ⟨(l 1 (by decide)).2, conjCoeff_eq_of_commute (isRoot_neg_single .E7 1) (l 1 (by decide)).2
      (by rw [← y0]; exact cY 0)⟩
  have hX1 : uLevel (Pi.single 3 1) = 0 ∧ ∀ ρ ∈ uPsi, conjCoeff (Pi.single 3 1) 1 uPsi c ρ = c ρ :=
    ⟨(l 3 (by decide)).1, conjCoeff_eq_of_commute (isRoot_single .E7 3) (l 3 (by decide)).1
      (by rw [← x1]; exact cX 1)⟩
  have hY1 : uLevel (-Pi.single 3 1) = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff (-Pi.single 3 1) 1 uPsi c ρ = c ρ :=
    ⟨(l 3 (by decide)).2, conjCoeff_eq_of_commute (isRoot_neg_single .E7 3) (l 3 (by decide)).2
      (by rw [← y1]; exact cY 1)⟩
  have hX2 : uLevel (Pi.single 2 1) = 0 ∧ uLevel (Pi.single 4 1) = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff (Pi.single 2 1) 1 uPsi (conjCoeff (Pi.single 4 1) 1 uPsi c) ρ = c ρ :=
    ⟨(l 2 (by decide)).1, (l 4 (by decide)).1, conjCoeff_pair_eq_of_commute
      (isRoot_single .E7 2) (isRoot_single .E7 4) (l 2 (by decide)).1 (l 4 (by decide)).1
      (by rw [← x2]; exact cX 2)⟩
  have hX3 : uLevel (Pi.single 0 1) = 0 ∧ uLevel (Pi.single 5 1) = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff (Pi.single 0 1) 1 uPsi (conjCoeff (Pi.single 5 1) 1 uPsi c) ρ = c ρ :=
    ⟨(l 0 (by decide)).1, (l 5 (by decide)).1, conjCoeff_pair_eq_of_commute
      (isRoot_single .E7 0) (isRoot_single .E7 5) (l 0 (by decide)).1 (l 5 (by decide)).1
      (by rw [← x3]; exact cX 3)⟩
  have hY3 : uLevel (-Pi.single 0 1) = 0 ∧ uLevel (-Pi.single 5 1) = 0 ∧
      ∀ ρ ∈ uPsi, conjCoeff (-Pi.single 0 1) 1 uPsi (conjCoeff (-Pi.single 5 1) 1 uPsi c) ρ =
        c ρ :=
    ⟨(l 0 (by decide)).2, (l 5 (by decide)).2, conjCoeff_pair_eq_of_commute
      (isRoot_neg_single .E7 0) (isRoot_neg_single .E7 5) (l 0 (by decide)).2
      (l 5 (by decide)).2 (by rw [← y3]; exact cY 3)⟩
  have k0000111 : c ![0, 0, 0, 0, 1, 1, 1] = 0 := uKill hX1 (ρ := ![0, 0, 0, 1, 1, 1, 1])
    (by decide +kernel)
  have k0001111 : c ![0, 0, 0, 1, 1, 1, 1] = 0 := uKill hY1 (ρ := ![0, 0, 0, 0, 1, 1, 1])
    (by decide +kernel)
  have k0101111 : c ![0, 1, 0, 1, 1, 1, 1] = 0 := uKill hY0 (ρ := ![0, 0, 0, 1, 1, 1, 1])
    (by decide +kernel)
  have k0011111 : c ![0, 0, 1, 1, 1, 1, 1] = 0 := uKill hX0 (ρ := ![0, 1, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k0111111 : c ![0, 1, 1, 1, 1, 1, 1] = 0 := uKill hY0 (ρ := ![0, 0, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k1011111 : c ![1, 0, 1, 1, 1, 1, 1] = 0 := uKill hX0 (ρ := ![1, 1, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k0112111 : c ![0, 1, 1, 2, 1, 1, 1] = 0 := uKill hY1 (ρ := ![0, 1, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k1111111 : c ![1, 1, 1, 1, 1, 1, 1] = 0 := uKill hY0 (ρ := ![1, 0, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k1112111 : c ![1, 1, 1, 2, 1, 1, 1] = 0 := uKill hY1 (ρ := ![1, 1, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k1122211 : c ![1, 1, 2, 2, 2, 1, 1] = 0 := uKill hX1 (ρ := ![1, 1, 2, 3, 2, 1, 1])
    (by decide +kernel)
  have k1123211 : c ![1, 1, 2, 3, 2, 1, 1] = 0 := uKill hY1 (ρ := ![1, 1, 2, 2, 2, 1, 1])
    (by decide +kernel)
  have k1122221 : c ![1, 1, 2, 2, 2, 2, 1] = 0 := uKill hX1 (ρ := ![1, 1, 2, 3, 2, 2, 1])
    (by decide +kernel)
  have k1123221 : c ![1, 1, 2, 3, 2, 2, 1] = 0 := uKill hY1 (ρ := ![1, 1, 2, 2, 2, 2, 1])
    (by decide +kernel)
  have k1223211 : c ![1, 2, 2, 3, 2, 1, 1] = 0 := uKill hY0 (ρ := ![1, 1, 2, 3, 2, 1, 1])
    (by decide +kernel)
  have k1223221 : c ![1, 2, 2, 3, 2, 2, 1] = 0 := uKill hY0 (ρ := ![1, 1, 2, 3, 2, 2, 1])
    (by decide +kernel)
  have k1123321 : c ![1, 1, 2, 3, 3, 2, 1] = 0 := uKill hX0 (ρ := ![1, 2, 2, 3, 3, 2, 1])
    (by decide +kernel)
  have k1223321 : c ![1, 2, 2, 3, 3, 2, 1] = 0 := uKill hY0 (ρ := ![1, 1, 2, 3, 3, 2, 1])
    (by decide +kernel)
  have k1224321 : c ![1, 2, 2, 4, 3, 2, 1] = 0 := uKill hY1 (ρ := ![1, 2, 2, 3, 3, 2, 1])
    (by decide +kernel)
  have k0000011 : c ![0, 0, 0, 0, 0, 1, 1] = 0 := uPairKillB hX2 (ρ := ![0, 0, 0, 0, 1, 1, 1])
    (by decide +kernel)
  have k1112221 : c ![1, 1, 1, 2, 2, 2, 1] = 0 := uPairKillA hX2 (ρ := ![1, 1, 2, 2, 2, 2, 1])
    (by decide +kernel)
  have k0000001 : c ![0, 0, 0, 0, 0, 0, 1] = 0 := uPairKillB hX3 (ρ := ![0, 0, 0, 0, 0, 1, 1])
    (by decide +kernel)
  have k0112211 : c ![0, 1, 1, 2, 2, 1, 1] = 0 := uPairKillB hX3 (ρ := ![0, 1, 1, 2, 2, 2, 1])
    (by decide +kernel)
  have k1234321 : c ![1, 2, 3, 4, 3, 2, 1] = 0 := uPairKillA hX3 (ρ := ![2, 2, 3, 4, 3, 2, 1])
    (by decide +kernel)
  have k2234321 : c ![2, 2, 3, 4, 3, 2, 1] = 0 := uPairKillA hY3 (ρ := ![1, 2, 3, 4, 3, 2, 1])
    (by decide +kernel)
  have fψ : c ![1, 1, 2, 2, 1, 1, 1] + (c ![1, 1, 1, 2, 2, 1, 1] + c ![1, 1, 1, 2, 1, 1, 1]) = 0 :=
    uPairThree hX2 (ρ := ![1, 1, 2, 2, 2, 1, 1]) (by decide +kernel)
  have fθ : c ![1, 1, 1, 2, 2, 1, 1] + (c ![0, 1, 1, 2, 2, 2, 1] + c ![0, 1, 1, 2, 2, 1, 1]) = 0 :=
    uPairThree hX3 (ρ := ![1, 1, 1, 2, 2, 2, 1]) (by decide +kernel)
  rw [k1112111, add_zero] at fψ
  rw [k0112211, add_zero] at fθ
  have hd : ∀ β ∈ uPsi, c β = if β ∈ uFrame then c uφ else 0 := by
    intro β hβ
    simp only [uPsi, List.mem_append] at hβ
    rcases hβ with (hβ | hβ) | hβ
    · rw [ite_eq_left hβ]
      rw [uFrame_eq] at hβ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
      rcases hβ with rfl | rfl | rfl
      · rfl
      · exact (eq_neg_of_add_eq_zero_left fψ).trans (CharTwo.neg_eq _)
      · exact ((eq_neg_of_add_eq_zero_left fθ).trans (CharTwo.neg_eq _)).symm
    · rw [ite_eq_right fun h => uLowHigh_not_mem_uFrame.1 β hβ h]
      iterate 11 (rcases List.mem_cons.1 hβ with rfl | hβ <;> try assumption)
      rcases List.mem_singleton.1 hβ with rfl
      assumption
    · rw [ite_eq_right fun h => uLowHigh_not_mem_uFrame.2 β hβ h]
      iterate 11 (rcases List.mem_cons.1 hβ with rfl | hβ <;> try assumption)
      rcases List.mem_singleton.1 hβ with rfl
      assumption
  have hq' : q = e7FrameElt K uFrame (c uφ) := by
    apply Subtype.ext
    rw [coe_e7FrameElt, hc, E6Pilot.rootProd_congr hd,
      show (fun β => if β ∈ uFrame then c uφ else 0) =
        fun ρ => if ρ ∈ uFrame then (fun _ => c uφ) ρ else 0 from rfl,
      E6Pilot.rootProd_ite_mem, uPsi_filter_uFrame]
    rfl
  rw [hq']
  exact e7FrameElt_mem_e7FrameLine uFrame (c uφ)

theorem commutator_pinnedX_one [CharP K 2] {a bp β : Fin Tag.E7.rank → ℤ}
    (h : commB a bp = true) (hβ : a + bp = β) (t : K) :
    ⁅pinnedX .E7 K a 1, pinnedX .E7 K bp t⁆ = pinnedX .E7 K β t := by
  rw [commutator_pinnedX_of_commB h, hβ, one_mul]

@[expose] def uOffLongB (a bp β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (bp ∈ uPsi) && commB a bp && decide (a + bp = β)

@[expose] def uOffPairLB (a b bp β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (bp ∈ uPsi) && commuteB b bp && commB a bp && decide (a + bp = β)

@[expose] def uOffPairRB (a b bp β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (bp ∈ uPsi) && commB b bp && commuteB a bp && commuteB a β && decide (b + bp = β)

@[expose] def uThreeB (a b bp β₁ β₂ β₃ : Fin Tag.E7.rank → ℤ) : Bool :=
  commB b bp && decide (b + bp = β₁) && commB a bp && decide (a + bp = β₂) && commB a β₁ &&
    decide (a + β₁ = β₃)

theorem uThree [CharP K 2] {a b bp β₁ β₂ β₃ : Fin Tag.E7.rank → ℤ}
    (h : uThreeB a b bp β₁ β₂ β₃ = true) (t : K) :
    ⁅pinnedX .E7 K a 1 * pinnedX .E7 K b 1, pinnedX .E7 K bp t⁆ =
      pinnedX .E7 K β₃ t * pinnedX .E7 K β₁ t * pinnedX .E7 K β₂ t := by
  simp only [uThreeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, e1⟩, h2⟩, e2⟩, h3⟩, e3⟩ := h
  rw [commutatorElement_mul_left_eq_three, commutator_pinnedX_one h1 e1,
    commutator_pinnedX_one h3 e3, commutator_pinnedX_one h2 e2]

theorem pinnedElt_mem_commutator_of {g : adjointGroup .E7 K} (hg : g ∈ uF4AS K)
    {bp β : Fin Tag.E7.rank → ℤ} (hbp : bp ∈ uPsi) (t : K)
    (h : ⁅(g : ModGL .E7 K), pinnedX .E7 K bp t⁆ = pinnedX .E7 K β t) :
    EPilot.pinnedElt .E7 β t ∈ ⁅radicalAS K, uF4AS K⁆ := by
  have hc := commutator_mem_radicalAS_uF4AS hg (pinnedElt_mem_radicalAS hbp t)
  convert hc using 1
  apply Subtype.ext
  rw [coe_commutator_adjointGroup]
  exact h.symm

theorem uOffLong [CharP K 2] {g : adjointGroup .E7 K} (hg : g ∈ uF4AS K)
    {a bp β : Fin Tag.E7.rank → ℤ} (hga : (g : ModGL .E7 K) = pinnedX .E7 K a 1)
    (h : uOffLongB a bp β = true) (t : K) :
    EPilot.pinnedElt .E7 β t ∈ ⁅radicalAS K, uF4AS K⁆ := by
  simp only [uOffLongB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hbp, h1⟩, e⟩ := h
  exact pinnedElt_mem_commutator_of hg hbp t (by rw [hga, commutator_pinnedX_one h1 e])

theorem uOffPairL [CharP K 2] {g : adjointGroup .E7 K} (hg : g ∈ uF4AS K)
    {a b bp β : Fin Tag.E7.rank → ℤ}
    (hgab : (g : ModGL .E7 K) = pinnedX .E7 K a 1 * pinnedX .E7 K b 1)
    (h : uOffPairLB a b bp β = true) (t : K) :
    EPilot.pinnedElt .E7 β t ∈ ⁅radicalAS K, uF4AS K⁆ := by
  simp only [uOffPairLB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbp, h1⟩, h2⟩, e⟩ := h
  refine pinnedElt_mem_commutator_of hg hbp t ?_
  rw [hgab, commutatorElement_mul_left_eq_three,
    commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_of_commuteB h1 1 t),
    commutatorElement_one_right, one_mul, one_mul, commutator_pinnedX_one h2 e]

theorem uOffPairR [CharP K 2] {g : adjointGroup .E7 K} (hg : g ∈ uF4AS K)
    {a b bp β : Fin Tag.E7.rank → ℤ}
    (hgab : (g : ModGL .E7 K) = pinnedX .E7 K a 1 * pinnedX .E7 K b 1)
    (h : uOffPairRB a b bp β = true) (t : K) :
    EPilot.pinnedElt .E7 β t ∈ ⁅radicalAS K, uF4AS K⁆ := by
  simp only [uOffPairRB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hbp, h1⟩, h2⟩, h3⟩, e⟩ := h
  refine pinnedElt_mem_commutator_of hg hbp t ?_
  rw [hgab, commutatorElement_mul_left_eq_three, commutator_pinnedX_one h1 e,
    commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_of_commuteB h3 1 t),
    commutatorElement_eq_one_iff_commute.2 (commute_pinnedX_of_commuteB h2 1 t), one_mul,
    mul_one]

theorem radicalAS_le_commutator_sup [CharP K 2] :
    radicalAS K ≤ ⁅radicalAS K, uF4AS K⁆ ⊔ e7FrameLine K uFrame := by
  set S := ⁅radicalAS K, uF4AS K⁆ ⊔ e7FrameLine K uFrame
  have hcomm : ⁅radicalAS K, uF4AS K⁆ ≤ S := le_sup_left
  have gX0 : (uGX K 0 1 : ModGL .E7 K) = pinnedX .E7 K (Pi.single 1 1) 1 := (uOrbitX_eq 1).1
  have gX1 : (uGX K 1 1 : ModGL .E7 K) = pinnedX .E7 K (Pi.single 3 1) 1 := (uOrbitX_eq 1).2.1
  have gX2 : (uGX K 2 1 : ModGL .E7 K) =
      pinnedX .E7 K (Pi.single 2 1) 1 * pinnedX .E7 K (Pi.single 4 1) 1 := (uOrbitX_eq 1).2.2.1
  have gX3 : (uGX K 3 1 : ModGL .E7 K) =
      pinnedX .E7 K (Pi.single 0 1) 1 * pinnedX .E7 K (Pi.single 5 1) 1 := (uOrbitX_eq 1).2.2.2
  have gY3 : (uGY K 3 1 : ModGL .E7 K) =
      pinnedX .E7 K (-Pi.single 0 1) 1 * pinnedX .E7 K (-Pi.single 5 1) 1 :=
    (uOrbitY_eq 1).2.2.2
  have offLow : ∀ β ∈ uLow, ∀ t : K, EPilot.pinnedElt .E7 β t ∈ ⁅radicalAS K, uF4AS K⁆ :=
    List.forall_mem_cons.2 ⟨uOffPairR (uGY_mem 3 1) gY3 (bp := ![0, 0, 0, 0, 0, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairR (uGX_mem 3 1) gX3 (bp := ![0, 0, 0, 0, 0, 0, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairR (uGX_mem 2 1) gX2 (bp := ![0, 0, 0, 0, 0, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 1 1) gX1 (bp := ![0, 0, 0, 0, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 2 1) gX2 (bp := ![0, 0, 0, 1, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 0 1) gX0 (bp := ![0, 0, 0, 1, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 0 1) gX0 (bp := ![0, 0, 1, 1, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 3 1) gX3 (bp := ![0, 0, 1, 1, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 1 1) gX1 (bp := ![0, 1, 1, 1, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 3 1) gX3 (bp := ![0, 1, 1, 1, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairR (uGX_mem 2 1) gX2 (bp := ![0, 1, 1, 2, 1, 1, 1])
      (by decide +kernel),
    List.forall_mem_singleton.2 (uOffPairL (uGX_mem 3 1) gX3 (bp := ![0, 1, 1, 2, 1, 1, 1])
      (by decide +kernel))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have offHigh : ∀ β ∈ uHigh, ∀ t : K, EPilot.pinnedElt .E7 β t ∈ ⁅radicalAS K, uF4AS K⁆ :=
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 3 1) gX3 (bp := ![0, 1, 1, 2, 2, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 2 1) gX2 (bp := ![1, 1, 1, 2, 2, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 2 1) gX2 (bp := ![1, 1, 1, 2, 2, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 1 1) gX1 (bp := ![1, 1, 2, 2, 2, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 1 1) gX1 (bp := ![1, 1, 2, 2, 2, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 0 1) gX0 (bp := ![1, 1, 2, 3, 2, 1, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairR (uGX_mem 2 1) gX2 (bp := ![1, 1, 2, 3, 2, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 0 1) gX0 (bp := ![1, 1, 2, 3, 2, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 0 1) gX0 (bp := ![1, 1, 2, 3, 3, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffLong (uGX_mem 1 1) gX1 (bp := ![1, 2, 2, 3, 3, 2, 1])
      (by decide +kernel),
    List.forall_mem_cons.2 ⟨uOffPairL (uGX_mem 2 1) gX2 (bp := ![1, 2, 2, 4, 3, 2, 1])
      (by decide +kernel),
    List.forall_mem_singleton.2 (uOffPairL (uGX_mem 3 1) gX3 (bp := ![1, 2, 3, 4, 3, 2, 1])
      (by decide +kernel))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hP : ∀ t : K, EPilot.pinnedElt .E7 uφ t * EPilot.pinnedElt .E7 uψ t ∈ S := by
    intro t
    have e3 := uThree (K := K) (a := Pi.single 2 1) (b := Pi.single 4 1)
      (bp := ![1, 1, 1, 2, 1, 1, 1]) (β₁ := uφ) (β₂ := uψ) (β₃ := ![1, 1, 2, 2, 2, 1, 1])
      (by decide +kernel) t
    rw [← gX2] at e3
    have e : EPilot.pinnedElt .E7 uφ t * EPilot.pinnedElt .E7 uψ t =
        (EPilot.pinnedElt .E7 ![1, 1, 2, 2, 2, 1, 1] t)⁻¹ *
          ⁅uGX K 2 1, EPilot.pinnedElt .E7 ![1, 1, 1, 2, 1, 1, 1] t⁆ := by
      apply Subtype.ext
      show pinnedX .E7 K uφ t * pinnedX .E7 K uψ t =
        (pinnedX .E7 K ![1, 1, 2, 2, 2, 1, 1] t)⁻¹ *
          ⁅(uGX K 2 1 : ModGL .E7 K), pinnedX .E7 K ![1, 1, 1, 2, 1, 1, 1] t⁆
      rw [e3]
      group
    rw [e]
    exact mul_mem (inv_mem (hcomm (offHigh _ (mem_uHigh_of_decide (by decide +kernel)) t)))
      (hcomm (commutator_mem_radicalAS_uF4AS
      (uGX_mem 2 1) (pinnedElt_mem_radicalAS (mem_uPsi_of_decide (by decide +kernel)) t)))
  have hR : ∀ t : K, EPilot.pinnedElt .E7 uθ t * EPilot.pinnedElt .E7 uφ t ∈ S := by
    intro t
    have e3 := uThree (K := K) (a := Pi.single 0 1) (b := Pi.single 5 1)
      (bp := ![0, 1, 1, 2, 2, 1, 1]) (β₁ := uθ) (β₂ := uφ) (β₃ := ![1, 1, 1, 2, 2, 2, 1])
      (by decide +kernel) t
    rw [← gX3] at e3
    have e : EPilot.pinnedElt .E7 uθ t * EPilot.pinnedElt .E7 uφ t =
        (EPilot.pinnedElt .E7 ![1, 1, 1, 2, 2, 2, 1] t)⁻¹ *
          ⁅uGX K 3 1, EPilot.pinnedElt .E7 ![0, 1, 1, 2, 2, 1, 1] t⁆ := by
      apply Subtype.ext
      show pinnedX .E7 K uθ t * pinnedX .E7 K uφ t =
        (pinnedX .E7 K ![1, 1, 1, 2, 2, 2, 1] t)⁻¹ *
          ⁅(uGX K 3 1 : ModGL .E7 K), pinnedX .E7 K ![0, 1, 1, 2, 2, 1, 1] t⁆
      rw [e3]
      group
    rw [e]
    exact mul_mem (inv_mem (hcomm (offHigh _ (mem_uHigh_of_decide (by decide +kernel)) t)))
      (hcomm (commutator_mem_radicalAS_uF4AS
      (uGX_mem 3 1) (pinnedElt_mem_radicalAS (mem_uPsi_of_decide (by decide +kernel)) t)))
  have hL : ∀ t : K, EPilot.pinnedElt .E7 uφ t * EPilot.pinnedElt .E7 uψ t *
      EPilot.pinnedElt .E7 uθ t ∈ S := fun t => by
    rw [← e7FrameElt_uFrame]
    exact mem_sup_right (e7FrameElt_mem_e7FrameLine uFrame t)
  have hθ : ∀ t : K, EPilot.pinnedElt .E7 uθ t ∈ S := fun t => by
    rw [← inv_mul_cancel_left (EPilot.pinnedElt .E7 uφ t * EPilot.pinnedElt .E7 uψ t)
      (EPilot.pinnedElt .E7 uθ t)]
    exact mul_mem (inv_mem (hP t)) (hL t)
  have hφ : ∀ t : K, EPilot.pinnedElt .E7 uφ t ∈ S := fun t => by
    rw [← inv_mul_cancel_left (EPilot.pinnedElt .E7 uθ t) (EPilot.pinnedElt .E7 uφ t)]
    exact mul_mem (inv_mem (hθ t)) (hR t)
  have hψ : ∀ t : K, EPilot.pinnedElt .E7 uψ t ∈ S := fun t => by
    rw [← inv_mul_cancel_left (EPilot.pinnedElt .E7 uφ t) (EPilot.pinnedElt .E7 uψ t)]
    exact mul_mem (inv_mem (hφ t)) (hP t)
  have key : ∀ β ∈ uPsi, ∀ t : K, EPilot.pinnedElt .E7 β t ∈ S := by
    intro β hβ t
    simp only [uPsi, List.mem_append] at hβ
    rcases hβ with (hβ | hβ) | hβ
    · rw [uFrame_eq] at hβ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
      rcases hβ with rfl | rfl | rfl
      exacts [hφ t, hψ t, hθ t]
    · exact hcomm (offLow β hβ t)
    · exact hcomm (offHigh β hβ t)
  have hle : parabolicRadical .E7 K uNodes ≤ S.map (adjointGroup .E7 K).subtype :=
    iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
      rintro _ ⟨t, rfl⟩
      exact ⟨EPilot.pinnedElt .E7 α t, key α (mem_uPsi_of_mem_parabolicRadicalRoots hα) t, rfl⟩)
  intro g hg
  obtain ⟨s, hs, hsg⟩ := hle (mem_subgroupOf.1 hg)
  rwa [show s = g from Subtype.ext hsg] at hs

theorem commutator_radicalAS_le : ⁅radicalAS K, uF4AS K⁆ ≤ radicalAS K := by
  obtain ⟨hQP, hN, -, hLP, -⟩ := parabolic_root_radical_Levi_factors .E7 K uNodes
  rw [Subgroup.commutator_le]
  intro r hr f hf
  have hr' : (r : ModGL .E7 K) ∈ parabolicRadical .E7 K uNodes := mem_subgroupOf.1 hr
  have hfP : (f : ModGL .E7 K) ∈ parabolicSubgroup .E7 K uNodes :=
    hLP (mem_subgroupOf.1 (uF4AS_le_parabolicLevi hf))
  have hconj : (f : ModGL .E7 K) * (r : ModGL .E7 K)⁻¹ * (f : ModGL .E7 K)⁻¹ ∈
      parabolicRadical .E7 K uNodes := by
    have h := hN.conj_mem ⟨(r : ModGL .E7 K)⁻¹, inv_mem (hQP hr')⟩
      (mem_subgroupOf.2 (inv_mem hr')) ⟨f, hfP⟩
    rw [mem_subgroupOf] at h
    simpa using h
  rw [mem_subgroupOf, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
    show (r : ModGL .E7 K) * f * (r : ModGL .E7 K)⁻¹ * (f : ModGL .E7 K)⁻¹ =
      r * ((f : ModGL .E7 K) * (r : ModGL .E7 K)⁻¹ * (f : ModGL .E7 K)⁻¹) by group]
  exact mul_mem hr' hconj

theorem e7Rep_three_eq_e7FramePt : e7Rep K 3 = e7FramePt K e7FrameU := by
  rw [← e7FrameElt_one, ← e7FrameElt_perm (F := e7RepFrames 3) (by decide +kernel)
    (e7RepFrames_isRoot 3) (e7RepFrames_pairwise 3)]
  rfl

theorem map_conj_e7FrameLine_uFrame [CharP K 2] :
    (e7FrameLine K uFrame).map (MulAut.conj (e7RepConj K 3)).toMonoidHom =
      e7FrameLine K e7FrameU := by
  have h3 : uFrame.map (e7RepWeyl 3 • ·) = e7RepFrames 3 := e7RepWeyl_smul_e7ASFrame 3
  rw [e7RepConj_three_eq_e7WeylRep,
    map_conj_e7FrameLine_weyl _ fun σ hσ => isRoot_of_mem_uPsi (mem_uPsi_of_mem_uFrame hσ), h3]
  exact e7FrameLine_perm (by decide +kernel) (e7RepFrames_isRoot 3) (e7RepFrames_pairwise 3)

theorem mem_e7FrameLine_of_mem_radicalU_of_commute_uF4 [CharP K 2] {q : adjointGroup .E7 K}
    (hq : q ∈ radicalU K) (hc : ∀ f ∈ uF4 K, q * f = f * q) : q ∈ e7FrameLine K e7FrameU := by
  obtain ⟨q', hq', rfl⟩ := hq
  set n := e7RepConj K 3
  have key : ∀ f ∈ uF4AS K, q' * f = f * q' := by
    intro f hf
    have h := hc _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have e : n * (q' * f) * n⁻¹ = n * (f * q') * n⁻¹ := by
      calc n * (q' * f) * n⁻¹ = n * q' * n⁻¹ * (n * f * n⁻¹) := by group
        _ = n * f * n⁻¹ * (n * q' * n⁻¹) := h
        _ = n * (f * q') * n⁻¹ := by group
    simpa using e
  have hmem := mem_e7FrameLine_uFrame_of_commute_gens (mem_subgroupOf.1 hq')
    (fun j => key _ (uGX_mem j 1)) (fun j => key _ (uGY_mem j 1))
  rw [← map_conj_e7FrameLine_uFrame]
  exact ⟨q', hmem, rfl⟩

theorem radicalU_le_commutator_sup_e7FrameLine [CharP K 2] :
    radicalU K ≤ ⁅radicalU K, uF4 K⁆ ⊔ e7FrameLine K e7FrameU := by
  have h := Subgroup.map_mono (f := (MulAut.conj (e7RepConj K 3)).toMonoidHom)
    (radicalAS_le_commutator_sup (K := K))
  rwa [Subgroup.map_sup, Subgroup.map_commutator, map_conj_e7FrameLine_uFrame] at h

theorem commutator_radicalU_uF4_le : ⁅radicalU K, uF4 K⁆ ≤ radicalU K := by
  have h := Subgroup.map_mono (f := (MulAut.conj (e7RepConj K 3)).toMonoidHom)
    (commutator_radicalAS_le (K := K))
  rwa [Subgroup.map_commutator] at h

theorem eq_one_of_mem_leviU_of_commute {m : adjointGroup .E7 K} (hm : m ∈ leviU K)
    (hc : ∀ r ∈ radicalU K, r * m = m * r) : m = 1 := by
  obtain ⟨m', hm', rfl⟩ := hm
  set n := e7RepConj K 3
  have hm'L : (m' : ModGL .E7 K) ∈ parabolicLevi .E7 K uNodes := mem_subgroupOf.1 hm'
  obtain ⟨-, -, -, hLP, hQL, -⟩ := parabolic_root_radical_Levi_factors .E7 K uNodes
  have hJ : uNodes ≠ Set.univ := fun h => by
    have h6 : (6 : Fin Tag.E7.rank) ∈ uNodes := h ▸ Set.mem_univ _
    exact h6 rfl
  have hcent : (m' : ModGL .E7 K) ∈
      centralizer (parabolicRadical .E7 K uNodes : Set (ModGL .E7 K)) := by
    rw [mem_centralizer_iff]
    intro r hr
    have hrC : r ∈ adjointGroup .E7 K :=
      posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent _ hr)
    have h := hc _ ⟨⟨r, hrC⟩, mem_subgroupOf.2 hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have e : n * (⟨r, hrC⟩ * m') * n⁻¹ = n * (m' * ⟨r, hrC⟩) * n⁻¹ := by
      calc n * (⟨r, hrC⟩ * m') * n⁻¹ = n * ⟨r, hrC⟩ * n⁻¹ * (n * m' * n⁻¹) := by group
        _ = n * m' * n⁻¹ * (n * ⟨r, hrC⟩ * n⁻¹) := h
        _ = n * (m' * ⟨r, hrC⟩) * n⁻¹ := by group
    have e' : (⟨r, hrC⟩ : adjointGroup .E7 K) * m' = m' * ⟨r, hrC⟩ := by simpa using e
    exact congrArg Subtype.val e'
  have hQ := (Chevalley_proper_parabolic_root_radical_self_centralizing .E7 K hJ).2
    (mem_inf.2 ⟨hLP hm'L, hcent⟩)
  have h1 : (m' : ModGL .E7 K) ∈ parabolicRadical .E7 K uNodes ⊓ parabolicLevi .E7 K uNodes :=
    mem_inf.2 ⟨hQ, hm'L⟩
  rw [hQL, mem_bot] at h1
  rw [show m' = 1 from Subtype.ext h1, map_one]

theorem resCent_e7FrameU [CharP K 2]
    (hcent : ∀ z ∈ e7FrameLine K e7FrameU, ∀ g ∈ Exc.cent (e7FramePt K e7FrameU), z * g = g * z) :
    Exc.ResCent (e7FramePt K e7FrameU) (e7FrameLine K e7FrameU) := by
  intro y hy _ hyc
  rw [← e7Rep_three_eq_e7FramePt] at hy hyc
  obtain ⟨q, hq, m, hm, hmC, rfl⟩ := exists_mul_eq_of_mem_centralizer_e7Rep_three hy
  have hF : ∀ f ∈ uF4 K, q * m * f = f * (q * m) := fun f hf =>
    hyc f (uF4_le_perfectCore_centralizer hf)
  have hRF : ⁅radicalU K, uF4 K⁆ ≤ centralizer ({m} : Set (adjointGroup .E7 K)) := by
    intro r hr
    have hrQ := commutator_radicalU_uF4_le hr
    have h1 : q * m * r = r * (q * m) := hyc r (commutator_radicalU_uF4 hr)
    have h2 : q * r = r * q := radicalU_comm hq hrQ
    rw [mem_centralizer_singleton_iff]
    have : q * (r * m) = q * (m * r) := by
      calc q * (r * m) = r * (q * m) := by rw [← mul_assoc, h2, mul_assoc]
        _ = q * m * r := h1.symm
        _ = q * (m * r) := mul_assoc _ _ _
    exact mul_left_cancel this
  have hZ : e7FrameLine K e7FrameU ≤ centralizer ({m} : Set (adjointGroup .E7 K)) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    refine hcent z hz m ?_
    rw [← e7Rep_three_eq_e7FramePt]
    exact hmC
  have hQ := radicalU_le_commutator_sup_e7FrameLine.trans (sup_le hRF hZ)
  have hm1 : m = 1 := eq_one_of_mem_leviU_of_commute hm fun r hr =>
    mem_centralizer_singleton_iff.1 (hQ hr)
  subst hm1
  rw [mul_one] at hF ⊢
  exact mem_e7FrameLine_of_mem_radicalU_of_commute_uF4 hq hF

end Main

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
