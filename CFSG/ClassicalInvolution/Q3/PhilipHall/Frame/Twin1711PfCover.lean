module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCover

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.EvenSmallLie CFSG.Open
open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace Twin1711

abbrev ModSp0 : Type := ↥CFSG.Sporadic.Schreier.Co3.co3X36

abbrev ModSp1 : Type := HopfCover ModSp0

abbrev ModOm0 : Type := ↥OmegaEight.omegaT

abbrev ModOm1 : Type := ↥OmegaEight.Weyl.wPlus

abbrev ModOm2 : Type := HopfCover ModOm0

section Aux

theorem center_eq_bot_of_equiv {Q M : Type} [Group Q] [Group M] (e : Q ≃* M)
    (hM : Subgroup.center M = ⊥) : Subgroup.center Q = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  have h1 : e q ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    have := Subgroup.mem_center_iff.mp hq (e.symm m)
    have h2 := congrArg e this
    simpa using h2
  rw [hM, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact h1

variable {G : Type} [Group G]

theorem ncard_centerSet (X : Subgroup G) :
    (centerSet X).ncard = Nat.card (Subgroup.center ↥X) := by
  have : centerSet X = X.subtype '' (Subgroup.center ↥X : Set ↥X) := by
    ext c
    constructor
    · rintro ⟨hc, hz⟩
      exact ⟨⟨c, hc⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hz y y.2), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun x hx => congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hy ⟨x, hx⟩)⟩
  rw [this, Set.ncard_image_of_injective _ X.subtype_injective]
  exact (Nat.card_coe_set_eq _).symm

theorem center_eq_ker_of_centerless {E Q : Type} [Group E] [Group Q] (q : E →* Q)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center E)
    (hQ : Subgroup.center Q = ⊥) : Subgroup.center E = q.ker := by
  refine le_antisymm (fun c hc => ?_) hker
  rw [MonoidHom.mem_ker]
  have h1 : q c ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := hq y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc w]
  rwa [hQ, Subgroup.mem_bot] at h1

end Aux

section Classify

variable {E : Type} [Group E] [Finite E] [Group.IsPerfect E] {Q : Type} [Group Q]
  (f : E →* Q) (hf : Function.Surjective f) (hc : f.ker ≤ Subgroup.center E)
  (h2 : IsPGroup 2 ↥f.ker)

include hf hc in
theorem classify_sp
    (hQ : LieModel Q .PSp 3 2 1) :
    (Nat.card f.ker = 1 ∧ Nonempty (E ≃* ModSp0)) ∨
      (Nat.card f.ker = 2 ∧ Nonempty (E ≃* ModSp1)) := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hQ
  have hQ' : LieModel ModSp0 .PSp 3 2 1 := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hQ
  let q : E →* ModSp0 := e.toMonoidHom.comp f
  have hq : Function.Surjective q := e.surjective.comp hf
  have hqk : q.ker = f.ker := OmegaEight.Cover.ker_comp_mulEquiv f e
  have hqc : q.ker ≤ Subgroup.center E := hqk ▸ hc
  have hle : Nat.card q.ker ≤ 2 := SympSix.card_ker_le_two hQ' q hq hqc
  have hpos : 0 < Nat.card q.ker := Nat.card_pos
  rw [hqk] at hle hpos
  have hcase : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by omega
  rcases hcase with h1 | h1
  · left
    refine ⟨h1, ⟨MulEquiv.ofBijective q ⟨?_, hq⟩⟩⟩
    rw [← MonoidHom.ker_eq_bot_iff, hqk]
    exact Subgroup.eq_bot_of_card_eq _ h1
  · right
    refine ⟨h1, ⟨?_⟩⟩
    have hb := SympSix.hopfLift_bijective hQ' q hq hqc (by rw [hqk]; exact h1)
    exact (MulEquiv.ofBijective _ hb).symm

include hf hc h2 in
theorem classify_om
    (hQ : LieModel Q .POmegaPlus 4 2 1) :
    (Nat.card f.ker = 1 ∧ Nonempty (E ≃* ModOm0)) ∨
      (Nat.card f.ker = 2 ∧ Nonempty (E ≃* ModOm1)) ∨
      (Nat.card f.ker = 4 ∧ Nonempty (E ≃* ModOm2)) := by
  obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT hQ
  have hQ' : LieModel ModOm0 .POmegaPlus 4 2 1 := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hQ
  let q : E →* ModOm0 := e.toMonoidHom.comp f
  have hq : Function.Surjective q := e.surjective.comp hf
  have hqk : q.ker = f.ker := OmegaEight.Cover.ker_comp_mulEquiv f e
  have hqc : q.ker ≤ Subgroup.center E := hqk ▸ hc
  obtain ⟨hUfin, hUle0⟩ := OmegaEight.Cover.card_hopfCover_le
  have hUle : Nat.card (HopfCover ModOm0) ≤ 4 * Nat.card ModOm0 := hUle0
  have hlam : Function.Surjective (hopfLift q hq hqc) := hopfLift_surjective q hq hqc
  have hEU : Nat.card E ≤ Nat.card (HopfCover ModOm0) := Nat.card_le_card_of_surjective _ hlam
  have hcardE : Nat.card f.ker * Nat.card Q = Nat.card E :=
    Subgroup.card_ker_mul_card_of_surjective hf
  have hcardQ : Nat.card Q = Nat.card ModOm0 := Nat.card_congr e.toEquiv
  have hQpos : 0 < Nat.card ModOm0 := Nat.card_pos
  have hle : Nat.card f.ker ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 4 * Nat.card ModOm0 < Nat.card f.ker * Nat.card Q := by
      rw [hcardQ]; exact Nat.mul_lt_mul_of_pos_right hlt hQpos
    omega
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hcase : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 ∨ Nat.card f.ker = 4 := by
    have hn2 : n ≤ 2 := by
      by_contra hn3
      push Not at hn3
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      omega
    interval_cases n <;> simp_all
  have hperf : commutator E = ⊤ := Group.IsPerfect.commutator_eq_top
  rcases hcase with h1 | h1 | h1
  · left
    refine ⟨h1, ⟨MulEquiv.ofBijective q ⟨?_, hq⟩⟩⟩
    rw [← MonoidHom.ker_eq_bot_iff, hqk]
    exact Subgroup.eq_bot_of_card_eq _ h1
  · right; left
    refine ⟨h1, ?_⟩
    have hQc : Subgroup.center ModOm0 = ⊥ := OmegaEight.center_omegaT
    have hcen : Subgroup.center E = f.ker :=
      center_eq_ker_of_centerless q hq hqc hQc |>.trans hqk
    have hX : LieModel (E ⧸ Subgroup.center E) .POmegaPlus 4 2 1 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hcen).trans
          (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm hQ
    obtain ⟨θ, -⟩ := OmegaEight.Weyl.exists_mulEquiv_wPlus E hperf (by rw [hcen]; exact h1) hX
    exact ⟨θ⟩
  · right; right
    refine ⟨h1, ?_⟩
    have hEeq : Nat.card E = 4 * Nat.card ModOm0 := by rw [← hcardE, h1, hcardQ]
    have hb : Function.Bijective (hopfLift q hq hqc) := by
      rw [Nat.bijective_iff_surjective_and_card]
      refine ⟨hlam, ?_⟩
      omega
    exact ⟨(MulEquiv.ofBijective _ hb).symm⟩

end Classify

section Cases

variable {G : Type} [Group G] [Finite G]

theorem isPerfect_of_commutator_eq {X : Subgroup G} (h : ⁅X, X⁆ = X) : Group.IsPerfect ↥X := by
  refine ⟨?_⟩
  apply Subgroup.map_injective X.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  exact h

theorem quasiE4_cases
    {X : Subgroup G} (hQ : QuasiE4 X) :
    (Nonempty (↥X ≃* ModSp0) ∧ (centerSet X).ncard = 1) ∨
      (Nonempty (↥X ≃* ModSp1) ∧ (centerSet X).ncard = 2) ∨
      (Nonempty (↥X ≃* ModOm0) ∧ (centerSet X).ncard = 1) ∨
      (Nonempty (↥X ≃* ModOm1) ∧ (centerSet X).ncard = 2) ∨
      (Nonempty (↥X ≃* ModOm2) ∧ (centerSet X).ncard = 4) := by
  obtain ⟨hperf, Q, _, f, hf, h2, hc, hQ⟩ := hQ
  have : Group.IsPerfect ↥X := isPerfect_of_commutator_eq hperf
  have hQc : Subgroup.center Q = ⊥ := by
    rcases hQ with h | h
    · obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 h
      exact center_eq_bot_of_equiv e CFSG.Sporadic.Schreier.Co3.co3X36_center
    · obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT h
      exact center_eq_bot_of_equiv e OmegaEight.center_omegaT
  have hZ : (centerSet X).ncard = Nat.card f.ker := by
    rw [ncard_centerSet, center_eq_ker_of_centerless f hf hc hQc]
  rcases hQ with h | h
  · rcases classify_sp f hf hc h with ⟨h1, he⟩ | ⟨h1, he⟩
    · exact Or.inl ⟨he, hZ.trans h1⟩
    · exact Or.inr (Or.inl ⟨he, hZ.trans h1⟩)
  · rcases classify_om f hf hc h2 h with ⟨h1, he⟩ | ⟨h1, he⟩ | ⟨h1, he⟩
    · exact Or.inr (Or.inr (Or.inl ⟨he, hZ.trans h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hZ.trans h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨he, hZ.trans h1⟩)))

end Cases

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
