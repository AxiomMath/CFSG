module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylow
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionOrbit
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Rank

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem eq_zero_of_mul_bar_eq_zero {u : K} (hu : u * h.bar u = 0) : u = 0 := by
  rcases mul_eq_zero.1 hu with h0 | h0
  · exact h0
  · exact (map_eq_zero h.bar).1 h0

section Squares

variable {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
include hg

theorem sq_entries : mat (g * g) ιe₁ ιe₂ = 0 ∧ mat (g * g) ιe₂ ιz = 0 ∧
    mat (g * g) ιe₁ ιz = mat g ιe₁ ιe₂ * mat g ιe₂ ιz ∧
    mat (g * g) ιe₂ ιf₂ = mat g ιe₂ ιz * h.bar (mat g ιe₂ ιz) ∧
    mat (g * g) ιe₁ ιf₂ = mat g ιe₁ ιe₂ * mat g ιe₂ ιf₂ + mat g ιe₁ ιz * h.bar (mat g ιe₂ ιz) ∧
    mat (g * g) ιe₂ ιf₁ = mat g ιe₂ ιz * mat g ιz ιf₁ +
      mat g ιe₂ ιf₂ * h.bar (mat g ιe₁ ιe₂) := by
  have := h.charP
  obtain ⟨r1, r2, -⟩ := U_rel hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_e₁e₂ hg hg, CharTwo.add_self_eq_zero]
  · rw [mul_e₂z hg hg, CharTwo.add_self_eq_zero]
  · rw [mul_e₁z hg hg, CharTwo.add_self_eq_zero, zero_add]
  · rw [mul_e₂f₂ hg hg, CharTwo.add_self_eq_zero, zero_add, r2]
  · rw [mul_e₁f₂ hg hg, CharTwo.add_self_eq_zero, zero_add, r2]
  · rw [mul_e₂f₁ hg hg, CharTwo.add_self_eq_zero, zero_add, r1]

end Squares

section CommutatorMod

theorem mul_ZPsub_entries {z v : hypSU h 2 1} (hz : z ∈ ZPsub h) (hv : v ∈ hypUnitriangular h 2 1) :
    (∀ a b : HypIndex 2 1, fullPos a < fullPos b → (a, b) ≠ (ιe₁, ιf₁) →
      mat (z * v) a b = mat v a b) ∧
    mat (z * v) ιe₁ ιf₁ = mat z ιe₁ ιf₁ + mat v ιe₁ ιf₁ := by
  obtain ⟨hzU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hz
  refine ⟨forall_upper.2 ?_, by rw [mul_e₁f₁ hzU hv]; simp [*]⟩
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hne => absurd rfl hne, fun _ => ?_,
    fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · rw [mul_e₁e₂ hzU hv, a1, zero_add]
  · rw [mul_e₁z hzU hv, a3, a1]; ring
  · rw [mul_e₁f₂ hzU hv, a7, a1, a3]; ring
  · rw [mul_e₂z hzU hv, a5, zero_add]
  · rw [mul_e₂f₂ hzU hv, a9, a5]; ring
  · rw [mul_e₂f₁ hzU hv, a8, a5, a9]; ring
  · rw [mul_zf₂ hzU hv, a6, zero_add]
  · rw [mul_zf₁ hzU hv, a4, a6]; ring
  · rw [mul_f₂f₁ hzU hv, a2, zero_add]

theorem commutator_mem_ZPsub_iff {x y : hypSU h 2 1} (hx : x ∈ hypUnitriangular h 2 1)
    (hy : y ∈ hypUnitriangular h 2 1) :
    ⁅x, y⁆ ∈ ZPsub h ↔ ∀ a b : HypIndex 2 1, fullPos a < fullPos b → (a, b) ≠ (ιe₁, ιf₁) →
      mat (x * y) a b = mat (y * x) a b := by
  have := h.charP
  have hw := mul_mem hx hy
  have hv := mul_mem hy hx
  have hxy : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  constructor
  · intro hc a b hab hne
    rw [hxy]
    exact (mul_ZPsub_entries hc hv).1 a b hab hne
  · intro he
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := forall_upper.1 he
    set c := mat (x * y) ιe₁ ιf₁ - mat (y * x) ιe₁ ιf₁ with hcdef
    have hc : h.bar c = c := by
      obtain ⟨-, -, -, -, -, r6⟩ := U_rel hw
      obtain ⟨-, -, -, -, -, r6'⟩ := U_rel hv
      rw [e1 (by decide), e2 (by decide), e3 (by decide)] at r6
      refine bar_eq_of_add_eq_zero h ?_
      rw [hcdef, map_sub]
      linear_combination r6 - r6'
    obtain ⟨z, hz, hzc⟩ := exists_rootZP h hc
    have hzv : z * (y * x) = x * y := by
      obtain ⟨hz1, hz2⟩ := mul_ZPsub_entries hz hv
      refine eq_of_U_entries (mul_mem (ZPsub_le_U hz) hv) hw fun a b hab => ?_
      by_cases hne : (a, b) = (ιe₁, ιf₁)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hne
        rw [hz2, hzc, hcdef]
        ring
      · rw [hz1 a b hab hne, he a b hab hne]
    have : ⁅x, y⁆ = z := by
      rw [commutatorElement_def, ← hzv]
      group
    rw [this]
    exact hz

theorem commutator_mem_Vsub_iff {x y : hypSU h 2 1} (hx : x ∈ hypUnitriangular h 2 1)
    (hy : y ∈ hypUnitriangular h 2 1) :
    ⁅x, y⁆ ∈ Vsub h ↔ mat x ιe₁ ιe₂ * mat y ιe₂ ιz = mat y ιe₁ ιe₂ * mat x ιe₂ ιz := by
  have := h.charP
  have hw := mul_mem hx hy
  have hv := mul_mem hy hx
  have hxy : ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by rw [commutatorElement_def]; group
  obtain ⟨x1, x2, x3, -⟩ := mulInv_entries hw hv
  obtain ⟨r1, r2, r3, -⟩ := U_rel hv
  have h12 : mat (x * y) ιe₁ ιe₂ = mat (y * x) ιe₁ ιe₂ := by
    rw [mul_e₁e₂ hx hy, mul_e₁e₂ hy hx, add_comm]
  have h2z : mat (x * y) ιe₂ ιz = mat (y * x) ιe₂ ιz := by
    rw [mul_e₂z hx hy, mul_e₂z hy hx, add_comm]
  have hdiff : mat (x * y) ιe₁ ιz - mat (y * x) ιe₁ ιz =
      mat x ιe₁ ιe₂ * mat y ιe₂ ιz - mat y ιe₁ ιe₂ * mat x ιe₂ ιz := by
    rw [mul_e₁z hx hy, mul_e₁z hy hx]
    ring
  have hxyU : (x * y) * (y * x)⁻¹ ∈ hypUnitriangular h 2 1 := mul_mem hw (inv_mem hv)
  have e1 : mat ((x * y) * (y * x)⁻¹) ιe₁ ιe₂ = 0 := by
    rw [x1, r1, h.bar_bar, h12, CharTwo.add_self_eq_zero]
  have e3 : mat ((x * y) * (y * x)⁻¹) ιe₂ ιz = 0 := by
    rw [x3, r2, h.bar_bar, h2z, CharTwo.add_self_eq_zero]
  have e2 : mat ((x * y) * (y * x)⁻¹) ιe₁ ιz =
      mat (x * y) ιe₁ ιz - mat (y * x) ιe₁ ιz := by
    rw [x2, r3, r2, map_add, map_mul, h.bar_bar, h.bar_bar, h.bar_bar, h12]
    linear_combination (CharTwo.add_self_eq_zero (mat (y * x) ιe₁ ιz)) +
      CharTwo.add_self_eq_zero (mat (y * x) ιe₁ ιe₂ * mat (y * x) ιe₂ ιz)
  rw [hxy]
  constructor
  · intro hmem
    have := (mem_Vsub'.1 hmem).2.2.2.1
    rw [e2, hdiff] at this
    exact sub_eq_zero.1 this
  · intro hc
    have hS : (x * y) * (y * x)⁻¹ ∈ Ssub h := (mem_Ssub_iff hxyU).2 e1
    refine (mem_Vsub_iff hS).2 fun i => ?_
    fin_cases i
    · change mat ((x * y) * (y * x)⁻¹) ιe₁ ιz = 0
      rw [e2, hdiff, hc, sub_self]
    · exact e3

end CommutatorMod

@[expose] def sB₁ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₂, ιz), (ιz, ιf₂)}

theorem isPattern_sB₁ : IsPattern sB₁ := ⟨by decide, by decide, by decide⟩

@[expose] def sB₂ : Finset (HypIndex 2 1 × HypIndex 2 1) := {(ιe₂, ιz), (ιz, ιf₂)}

theorem isPattern_sB₂ : IsPattern sB₂ := ⟨by decide, by decide, by decide⟩

theorem mem_patSub_sB₁ {g : hypSU h 2 1} : g ∈ patSub h sB₁ isPattern_sB₁ ↔
    g ∈ hypUnitriangular h 2 1 ∧ mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₂ ιz = 0 ∧
      mat g ιz ιf₂ = 0 := by
  simp [mem_patSub, sB₁]

theorem mem_patSub_sB₂ {g : hypSU h 2 1} : g ∈ patSub h sB₂ isPattern_sB₂ ↔
    g ∈ hypUnitriangular h 2 1 ∧ mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 := by
  simp [mem_patSub, sB₂]

theorem exists_mul_inv_mem_A₂sub {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
    (hgz : mat g ιe₂ ιz = 0) :
    ∃ y ∈ patSub h sI₆ isPattern_sI₆, g * y⁻¹ ∈ A₂sub h := by
  have := h.charP
  obtain ⟨-, s2, -, -, s5, -⟩ := U_rel hg
  have hc : h.bar (mat g ιe₂ ιf₂) = mat g ιe₂ ιf₂ :=
    bar_eq_of_add_eq_zero h (by rw [s5, hgz, zero_mul])
  obtain ⟨y, hy, hyc⟩ := exists_rootI₆ h hc
  obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := mem_patSub_sI₆.1 hy
  obtain ⟨-, -, x3, -, x5, x6, -⟩ := mulInv_entries hg hyU
  refine ⟨y, hy, mem_A₂sub.2 ⟨mul_mem hg (inv_mem hyU), ?_, ?_, ?_⟩⟩
  · rw [x3, y6, hgz, map_zero, add_zero]
  · rw [x6, s2, hgz, y5, map_zero, add_zero]
  · rw [x5, hyc, hc, hgz, zero_mul, add_zero, CharTwo.add_self_eq_zero]

theorem Vsub_sup_A₂sub_inf_Ssub_eq : Vsub h ⊔ (A₂sub h ⊓ Ssub h) = patSub h sB₁ isPattern_sB₁ := by
  refine le_antisymm (sup_le ?_ ?_) fun g hg => ?_
  · rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide)
  · intro g ⟨hg1, hg2⟩
    obtain ⟨hgU, a1, a2, -⟩ := mem_A₂sub.1 hg1
    obtain ⟨-, b1, b2⟩ := mem_Ssub'.1 hg2
    exact mem_patSub_sB₁.2 ⟨hgU, b1, b2, a1, a2⟩
  · obtain ⟨hgU, b1, b2, b3, -⟩ := mem_patSub_sB₁.1 hg
    obtain ⟨y, hy, hx⟩ := exists_mul_inv_mem_A₂sub hgU b3
    have hyV : y ∈ Vsub h := by
      rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide) hy
    have hgS : g ∈ Ssub h := (mem_Ssub_iff hgU).2 b1
    have hxS : g * y⁻¹ ∈ Ssub h := mul_mem hgS (inv_mem (Vsub_le_Ssub hyV))
    rw [show g = g * y⁻¹ * y by group]
    exact mul_mem (mem_sup_right ⟨hx, hxS⟩) (mem_sup_left hyV)

theorem Vsub_sup_A₂sub_eq : Vsub h ⊔ A₂sub h = patSub h sB₂ isPattern_sB₂ := by
  refine le_antisymm (sup_le ?_ (patSub_mono _ _ (by decide))) fun g hg => ?_
  · rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide)
  · obtain ⟨hgU, b1, -⟩ := mem_patSub_sB₂.1 hg
    obtain ⟨y, hy, hx⟩ := exists_mul_inv_mem_A₂sub hgU b1
    have hyV : y ∈ Vsub h := by
      rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide) hy
    rw [show g = g * y⁻¹ * y by group]
    exact mul_mem (mem_sup_right hx) (mem_sup_left hyV)

theorem card_patSub_sB₁ : Nat.card (patSub h sB₁ isPattern_sB₁) = (2 ^ f) ^ 6 := by
  have hBS : patSub h sB₁ isPattern_sB₁ ≤ Ssub h := by
    rw [Ssub_eq_patSub]; exact patSub_mono _ _ (by decide)
  rw [card_eq_mul_of_coord (H := patSub h sB₁ isPattern_sB₁) (N := Vsub h)
    (by rw [Vsub_eq_patSub]; exact patSub_mono _ _ (by decide))
    (fun x => mat x ιe₁ ιz) (fun x hx y hy => mul_e₁z_of_Ssub (hBS hx) (hBS hy)) ?_ ?_,
    card_Vsub]
  · ring
  · intro x hx
    obtain ⟨hxU, b1, b2, b3, b4⟩ := mem_patSub_sB₁.1 hx
    constructor
    · intro hx0
      refine (mem_Vsub_iff (hBS hx)).2 fun i => ?_
      fin_cases i
      · exact hx0
      · exact b3
    · intro hxV
      exact (mem_Vsub_iff (hBS hx)).1 hxV 0
  · intro u
    obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u) (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g, hg, hgu, -⟩ := exists_rootI₅ h hc
    exact ⟨g, patSub_mono _ _ (by decide) hg, hgu⟩

theorem card_patSub_sB₂ : Nat.card (patSub h sB₂ isPattern_sB₂) = (2 ^ f) ^ 8 := by
  have := card_eq_mul_of_coord (H := hypUnitriangular h 2 1) (N := patSub h sB₂ isPattern_sB₂)
    (patSub_le_U _ _) (fun x => mat x ιe₂ ιz) (fun x hx y hy => mul_e₂z hx hy)
    (fun x hx => ⟨fun h0 => mem_patSub_sB₂.2 ⟨hx, h0, by rw [(U_rel hx).2.1, h0, map_zero]⟩,
      fun hx' => (mem_patSub_sB₂.1 hx').2.1⟩) (fun u => by
      obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u)
        (by rw [map_mul, h.bar_bar, mul_comm])
      obtain ⟨g, hg, hgu, -⟩ := exists_rootI₂ h hc
      exact ⟨g, patSub_le_U _ _ hg, hgu⟩)
  rw [Data.card_U] at this
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  have : (2 ^ f) ^ 8 * (2 ^ f) ^ 2 = Nat.card (patSub h sB₂ isPattern_sB₂) * (2 ^ f) ^ 2 := by
    rw [← this]; ring
  exact (Nat.eq_of_mul_eq_mul_right hpos this).symm

@[expose] def ElemAbMod {G : Type*} [Group G] (N E : Subgroup G) : Prop :=
  (∀ x ∈ E, x * x ∈ N) ∧ ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ N

section ModZP

theorem sq_mem_ZPsub {x : hypSU h 2 1} (hx : x ∈ hypUnitriangular h 2 1)
    (hx2 : x * x ∈ ZPsub h) : mat x ιe₂ ιz = 0 ∧ mat x ιe₁ ιe₂ * mat x ιe₂ ιf₂ = 0 := by
  obtain ⟨-, -, -, s4, s5, -⟩ := sq_entries hx
  obtain ⟨-, -, -, -, -, -, -, a7, -, a9⟩ := mem_ZPsub.1 hx2
  rw [a9] at s4
  have hu := eq_zero_of_mul_bar_eq_zero s4.symm
  rw [a7, hu, map_zero, mul_zero, add_zero] at s5
  exact ⟨hu, s5.symm⟩

theorem le_A₂sub_or_le_sB₁_of_elemAbMod {E : Subgroup (hypSU h 2 1)}
    (hEU : E ≤ hypUnitriangular h 2 1) (hE : ElemAbMod (ZPsub h) E) :
    E ≤ A₂sub h ∨ E ≤ patSub h sB₁ isPattern_sB₁ := by
  have := h.charP
  by_cases hA : E ≤ A₂sub h
  · exact Or.inl hA
  right
  obtain ⟨x, hxE, hxA⟩ := Set.not_subset.1 hA
  have hxU := hEU hxE
  obtain ⟨hu, hay⟩ := sq_mem_ZPsub hxU (hE.1 x hxE)
  have hzf₂ : mat x ιz ιf₂ = 0 := by rw [(U_rel hxU).2.1, hu, map_zero]
  have hy22 : mat x ιe₂ ιf₂ ≠ 0 := fun h0 => hxA (mem_A₂sub.2 ⟨hxU, hu, hzf₂, h0⟩)
  have ha : mat x ιe₁ ιe₂ = 0 := (mul_eq_zero.1 hay).resolve_right hy22
  intro y hyE
  have hyU := hEU hyE
  obtain ⟨hu', -⟩ := sq_mem_ZPsub hyU (hE.1 y hyE)
  have hc := (commutator_mem_ZPsub_iff hxU hyU).1 (hE.2 x hxE y hyE) ιe₁ ιf₂ (by decide)
    (by decide)
  rw [mul_e₁f₂ hxU hyU, mul_e₁f₂ hyU hxU, ha, hzf₂, (U_rel hyU).2.1, hu', map_zero] at hc
  have hay' : mat y ιe₁ ιe₂ * mat x ιe₂ ιf₂ = 0 := by linear_combination -hc
  have ha' := (mul_eq_zero.1 hay').resolve_right hy22
  exact mem_patSub_sB₁.2 ⟨hyU, ha', by rw [(U_rel hyU).1, ha', map_zero], hu',
    by rw [(U_rel hyU).2.1, hu', map_zero]⟩

theorem elemAbMod_ZPsub_A₂sub : ElemAbMod (ZPsub h) (A₂sub h) := by
  have := h.charP
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨hxU, a1, a2, a3⟩ := mem_A₂sub.1 hx
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sq_entries hxU
    obtain ⟨-, -, r3, -⟩ := U_rel hxU
    have hxx := mul_mem hxU hxU
    obtain ⟨-, q2, q3, -⟩ := U_rel hxx
    refine mem_ZPsub.2 ⟨hxx, s1, by rw [(U_rel hxx).1, s1, map_zero], by rw [s3, a1, mul_zero],
      by rw [q3, s3, s1, a1]; simp, s2, by rw [q2, s2, map_zero], by rw [s5, a3, a1]; simp,
      by rw [s6, a1, a3]; simp, by rw [s4, a1, zero_mul]⟩
  · obtain ⟨hxU, a1, a2, a3⟩ := mem_A₂sub.1 hx
    obtain ⟨hyU, b1, b2, b3⟩ := mem_A₂sub.1 hy
    refine (commutator_mem_ZPsub_iff hxU hyU).2 (forall_upper.2 ?_)
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hne => absurd rfl hne, fun _ => ?_,
      fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [mul_e₁e₂ hxU hyU, mul_e₁e₂ hyU hxU, add_comm]
    · rw [mul_e₁z hxU hyU, mul_e₁z hyU hxU, a1, b1]; ring
    · rw [mul_e₁f₂ hxU hyU, mul_e₁f₂ hyU hxU, a2, a3, b2, b3]; ring
    · rw [mul_e₂z hxU hyU, mul_e₂z hyU hxU, add_comm]
    · rw [mul_e₂f₂ hxU hyU, mul_e₂f₂ hyU hxU, a1, b1, a3, b3]; ring
    · rw [mul_e₂f₁ hxU hyU, mul_e₂f₁ hyU hxU, a1, b1, a3, b3]; ring
    · rw [mul_zf₂ hxU hyU, mul_zf₂ hyU hxU, add_comm]
    · rw [mul_zf₁ hxU hyU, mul_zf₁ hyU hxU, a2, b2]; ring
    · rw [mul_f₂f₁ hxU hyU, mul_f₂f₁ hyU hxU, add_comm]

theorem card_le_of_elemAbMod_ZPsub {E : Subgroup (hypSU h 2 1)}
    (hEU : E ≤ hypUnitriangular h 2 1) (hE : ElemAbMod (ZPsub h) E) :
    Nat.card E ≤ (2 ^ f) ^ 7 ∧ ((2 ^ f) ^ 7 ≤ Nat.card E → E = A₂sub h) := by
  have := h.finite
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.one_le; omega)
  have h67 : (2 ^ f) ^ 6 < (2 ^ f) ^ 7 := Nat.pow_lt_pow_right hq (by norm_num)
  rcases le_A₂sub_or_le_sB₁_of_elemAbMod hEU hE with hEA | hEA
  · have hc := (card_le_of_le hEA).trans_eq card_A₂sub
    exact ⟨hc, fun hge => eq_of_le_of_card_ge hEA (by rw [card_A₂sub]; exact hge)⟩
  · have hc := (card_le_of_le hEA).trans_eq card_patSub_sB₁
    exact ⟨hc.trans h67.le, fun hge => absurd (hge.trans hc) (not_le.2 h67)⟩

end ModZP

section ModA₁

theorem sq_mem_Vsub_iff {x : hypSU h 2 1} (hx : x ∈ hypUnitriangular h 2 1) :
    x * x ∈ Vsub h ↔ mat x ιe₁ ιe₂ * mat x ιe₂ ιz = 0 := by
  obtain ⟨s1, s2, s3, -⟩ := sq_entries hx
  have hxx := mul_mem hx hx
  have hS : x * x ∈ Ssub h := (mem_Ssub_iff hxx).2 s1
  rw [mem_Vsub_iff hS]
  constructor
  · intro h0
    rw [← s3]
    exact h0 0
  · intro h0 i
    fin_cases i
    · change mat (x * x) ιe₁ ιz = 0
      rw [s3, h0]
    · exact s2

theorem le_Ssub_or_le_sB₂_of_elemAbMod {E : Subgroup (hypSU h 2 1)}
    (hEU : E ≤ hypUnitriangular h 2 1) (hE : ElemAbMod (Vsub h) E) :
    E ≤ Ssub h ∨ E ≤ patSub h sB₂ isPattern_sB₂ := by
  by_cases hS : E ≤ Ssub h
  · exact Or.inl hS
  right
  obtain ⟨x, hxE, hxS⟩ := Set.not_subset.1 hS
  have hxU := hEU hxE
  have ha : mat x ιe₁ ιe₂ ≠ 0 := fun h0 => hxS ((mem_Ssub_iff hxU).2 h0)
  have hu : mat x ιe₂ ιz = 0 :=
    (mul_eq_zero.1 ((sq_mem_Vsub_iff hxU).1 (hE.1 x hxE))).resolve_left ha
  intro y hyE
  have hyU := hEU hyE
  have hc := (commutator_mem_Vsub_iff hxU hyU).1 (hE.2 x hxE y hyE)
  rw [hu, mul_zero] at hc
  have hu' := (mul_eq_zero.1 hc).resolve_left ha
  exact mem_patSub_sB₂.2 ⟨hyU, hu', by rw [(U_rel hyU).2.1, hu', map_zero]⟩

theorem elemAbMod_Vsub_Ssub : ElemAbMod (Vsub h) (Ssub h) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨hxU, a1, -⟩ := mem_Ssub'.1 hx
    rw [sq_mem_Vsub_iff hxU, a1, zero_mul]
  · obtain ⟨hxU, a1, -⟩ := mem_Ssub'.1 hx
    obtain ⟨hyU, b1, -⟩ := mem_Ssub'.1 hy
    rw [commutator_mem_Vsub_iff hxU hyU, a1, b1, zero_mul, zero_mul]

theorem elemAbMod_Vsub_sB₂ : ElemAbMod (Vsub h) (patSub h sB₂ isPattern_sB₂) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨hxU, a1, -⟩ := mem_patSub_sB₂.1 hx
    rw [sq_mem_Vsub_iff hxU, a1, mul_zero]
  · obtain ⟨hxU, a1, -⟩ := mem_patSub_sB₂.1 hx
    obtain ⟨hyU, b1, -⟩ := mem_patSub_sB₂.1 hy
    rw [commutator_mem_Vsub_iff hxU hyU, a1, b1, mul_zero, mul_zero]

theorem card_Ssub : Nat.card (Ssub h) = (2 ^ f) ^ 8 := by
  have hBS : patSub h sB₁ isPattern_sB₁ ≤ Ssub h := by
    rw [Ssub_eq_patSub]; exact patSub_mono _ _ (by decide)
  rw [card_eq_mul_of_coord (H := Ssub h) (N := patSub h sB₁ isPattern_sB₁) hBS
    (fun x => mat x ιe₂ ιz) (fun x hx y hy => mul_e₂z (Ssub_le_Usub hx) (Ssub_le_Usub hy))
    ?_ ?_, card_patSub_sB₁]
  · ring
  · intro x hx
    obtain ⟨hxU, a1, a2⟩ := mem_Ssub'.1 hx
    exact ⟨fun h0 => mem_patSub_sB₁.2 ⟨hxU, a1, a2, h0, by rw [(U_rel hxU).2.1, h0, map_zero]⟩,
      fun hx' => (mem_patSub_sB₁.1 hx').2.2.2.1⟩
  · intro u
    obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u) (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g, hg, hgu, -⟩ := exists_rootI₂ h hc
    exact ⟨g, patSub_I₂_le_Ssub hg, hgu⟩

theorem card_le_of_elemAbMod_Vsub {E : Subgroup (hypSU h 2 1)}
    (hEU : E ≤ hypUnitriangular h 2 1) (hE : ElemAbMod (Vsub h) E) :
    Nat.card E ≤ (2 ^ f) ^ 8 ∧
      ((2 ^ f) ^ 8 ≤ Nat.card E → E = Ssub h ∨ E = Vsub h ⊔ A₂sub h) := by
  have := h.finite
  rw [Vsub_sup_A₂sub_eq]
  rcases le_Ssub_or_le_sB₂_of_elemAbMod hEU hE with hEA | hEA
  · have hc := (card_le_of_le hEA).trans_eq card_Ssub
    exact ⟨hc, fun hge => Or.inl (eq_of_le_of_card_ge hEA (by rw [card_Ssub]; exact hge))⟩
  · have hc := (card_le_of_le hEA).trans_eq card_patSub_sB₂
    exact ⟨hc, fun hge => Or.inr (eq_of_le_of_card_ge hEA (by rw [card_patSub_sB₂]; exact hge))⟩

theorem Ssub_sup_Vsub_sup_A₂sub : Ssub h ⊔ (Vsub h ⊔ A₂sub h) = hypUnitriangular h 2 1 := by
  refine le_antisymm (sup_le Ssub_le_Usub (sup_le (Vsub_le_Ssub.trans Ssub_le_Usub) A₂sub_le_U))
    ?_
  rw [U_eq_sup_Ssub_I₁.1]
  exact sup_le le_sup_left (patSub_I₁_le_A₂sub.trans (le_sup_right.trans le_sup_right))

end ModA₁

section Centres

theorem mul_ZPsub_entries_right {z v : hypSU h 2 1} (hz : z ∈ ZPsub h)
    (hv : v ∈ hypUnitriangular h 2 1) :
    (∀ a b : HypIndex 2 1, fullPos a < fullPos b → (a, b) ≠ (ιe₁, ιf₁) →
      mat (v * z) a b = mat v a b) ∧
    mat (v * z) ιe₁ ιf₁ = mat v ιe₁ ιf₁ + mat z ιe₁ ιf₁ := by
  obtain ⟨hzU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hz
  refine ⟨forall_upper.2 ?_, by rw [mul_e₁f₁ hv hzU]; simp [*]⟩
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hne => absurd rfl hne, fun _ => ?_,
    fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · rw [mul_e₁e₂ hv hzU, a1, add_zero]
  · rw [mul_e₁z hv hzU, a3, a5]; ring
  · rw [mul_e₁f₂ hv hzU, a7, a9, a6]; ring
  · rw [mul_e₂z hv hzU, a5, add_zero]
  · rw [mul_e₂f₂ hv hzU, a9, a6]; ring
  · rw [mul_e₂f₁ hv hzU, a8, a4, a2]; ring
  · rw [mul_zf₂ hv hzU, a6, add_zero]
  · rw [mul_zf₁ hv hzU, a4, a2]; ring
  · rw [mul_f₂f₁ hv hzU, a2, add_zero]

theorem ZPsub_commute {z v : hypSU h 2 1} (hz : z ∈ ZPsub h) (hv : v ∈ hypUnitriangular h 2 1) :
    z * v = v * z := by
  obtain ⟨l1, l2⟩ := mul_ZPsub_entries hz hv
  obtain ⟨r1, r2⟩ := mul_ZPsub_entries_right hz hv
  refine eq_of_U_entries (mul_mem (ZPsub_le_U hz) hv) (mul_mem hv (ZPsub_le_U hz))
    fun a b hab => ?_
  by_cases hne : (a, b) = (ιe₁, ιf₁)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hne
    rw [l2, r2, add_comm]
  · rw [l1 a b hab hne, r1 a b hab hne]

theorem e₁f₁_mul_comm_A₂ {x y : hypSU h 2 1} (hx : x ∈ A₂sub h) (hy : y ∈ A₂sub h)
    (e : x * y = y * x) :
    mat x ιe₁ ιe₂ * h.bar (mat y ιe₁ ιf₂) + mat x ιe₁ ιz * h.bar (mat y ιe₁ ιz) +
      mat x ιe₁ ιf₂ * h.bar (mat y ιe₁ ιe₂) =
    mat y ιe₁ ιe₂ * h.bar (mat x ιe₁ ιf₂) + mat y ιe₁ ιz * h.bar (mat x ιe₁ ιz) +
      mat y ιe₁ ιf₂ * h.bar (mat x ιe₁ ιe₂) := by
  obtain ⟨hxU, a1, a2, a3⟩ := mem_A₂sub.1 hx
  obtain ⟨hyU, b1, b2, b3⟩ := mem_A₂sub.1 hy
  obtain ⟨xr1, -, xr3, xr4, -⟩ := U_rel hxU
  obtain ⟨yr1, -, yr3, yr4, -⟩ := U_rel hyU
  have := congrArg (fun g => mat g ιe₁ ιf₁) e
  simp only [mul_e₁f₁ hxU hyU, mul_e₁f₁ hyU hxU, xr1, xr3, xr4, yr1, yr3, yr4, a1, a3, b1, b3,
    map_zero, mul_zero, add_zero] at this
  linear_combination this

theorem eq_zero_of_mul_bar {c ω : K} (hω : h.bar ω ≠ ω) (e : c * h.bar ω = ω * c) : c = 0 := by
  have : c * (h.bar ω - ω) = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hω)

theorem centerIn_A₂sub : CFSG.centerIn (A₂sub h) = ZPsub h := by
  have := h.charP
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  apply le_antisymm
  · rintro z ⟨hzA, hzc⟩
    have hcomm : ∀ y ∈ A₂sub h, z * y = y * z := fun y hy => (mem_centralizer_iff.1 hzc y hy).symm
    obtain ⟨hzU, a1, a2, a3⟩ := mem_A₂sub.1 hzA
    have rootA : ∀ a : K, ∃ y ∈ A₂sub h, mat y ιe₁ ιe₂ = a ∧ mat y ιe₁ ιz = 0 ∧
        mat y ιe₁ ιf₂ = 0 := fun a => by
      obtain ⟨y, hy, hya⟩ := exists_rootI₁ h a
      obtain ⟨-, c1, -, -, -, c5, -⟩ := mem_patSub_sI₁.1 hy
      exact ⟨y, patSub_I₁_le_A₂sub hy, hya, c1, c5⟩
    have rootB : ∀ b : K, ∃ y ∈ A₂sub h, mat y ιe₁ ιe₂ = 0 ∧ mat y ιe₁ ιz = 0 ∧
        mat y ιe₁ ιf₂ = b := fun b => by
      obtain ⟨y, hy, hyb⟩ := exists_rootI₄ h b
      obtain ⟨-, c1, -, c3, -⟩ := mem_patSub_sI₄.1 hy
      exact ⟨y, Z₂Psub_le_A₂sub ((Z₂Psub_eq_patSub (h := h)).symm ▸
        patSub_mono _ _ (by decide) hy), c1, c3, hyb⟩
    have rootC : ∀ u : K, ∃ y ∈ A₂sub h, mat y ιe₁ ιe₂ = 0 ∧ mat y ιe₁ ιz = u ∧
        mat y ιe₁ ιf₂ = 0 := fun u => by
      obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u)
        (by rw [map_mul, h.bar_bar, mul_comm])
      obtain ⟨y, hy, hyu, -⟩ := exists_rootI₅ h hc
      obtain ⟨-, c1, -, -, -, c5, -⟩ := mem_patSub_sI₅.1 hy
      exact ⟨y, (patSub_I₅_le_A₂sub_inf_Ssub hy).1, c1, hyu, c5⟩
    have key : ∀ (c : K), (∀ w : K, c * h.bar w = w * h.bar c) → c = 0 := fun c hc => by
      have h1 := hc 1
      simp only [map_one, mul_one, one_mul] at h1
      exact eq_zero_of_mul_bar hω ((hc ω).trans (by rw [← h1]))
    have hα : mat z ιe₁ ιe₂ = 0 := key _ fun w => by
      obtain ⟨y, hy, y1, y2, y3⟩ := rootB w
      have := e₁f₁_mul_comm_A₂ hzA hy (hcomm y hy)
      rw [y1, y2, y3, map_zero] at this
      linear_combination this
    have hu : mat z ιe₁ ιz = 0 := key _ fun w => by
      obtain ⟨y, hy, y1, y2, y3⟩ := rootC w
      have := e₁f₁_mul_comm_A₂ hzA hy (hcomm y hy)
      rw [y1, y2, y3, hα, map_zero] at this
      linear_combination this
    have hb : mat z ιe₁ ιf₂ = 0 := key _ fun w => by
      obtain ⟨y, hy, y1, y2, y3⟩ := rootA w
      have := e₁f₁_mul_comm_A₂ hzA hy (hcomm y hy)
      rw [y1, y2, y3, hα, hu, map_zero] at this
      linear_combination this
    obtain ⟨r1, r2, r3, r4, -⟩ := U_rel hzU
    exact mem_ZPsub.2 ⟨hzU, hα, by rw [r1, hα, map_zero], hu, by rw [r3, hu, hα]; simp, a1, a2,
      hb, by rw [r4, hb, hα, hu, a3]; simp, a3⟩
  · intro z hz
    exact ⟨Z₂Psub_le_A₂sub (ZPsub_le_Z₂Psub hz), mem_centralizer_iff.2 fun y hy =>
      (ZPsub_commute hz (A₂sub_le_U hy)).symm⟩

theorem centerIn_U : CFSG.centerIn (hypUnitriangular h 2 1) = ZPsub h := by
  apply le_antisymm
  · rintro z ⟨hzU, hzc⟩
    have hzA : z ∈ A₂sub h := by
      have := h.charP
      have hc : ∀ y ∈ hypUnitriangular h 2 1, z * y = y * z :=
        fun y hy => (mem_centralizer_iff.1 hzc y hy).symm
      obtain ⟨y, hy, ha⟩ := exists_rootI₁ h 1
      obtain ⟨hyU, c1, c2, c3, c4, c5, c6, c7, c8⟩ := mem_patSub_sI₁.1 hy
      have hyr := (U_rel hyU).1
      have e1 := congrArg (fun g => mat g ιe₁ ιz) (hc y hyU)
      have e2 := congrArg (fun g => mat g ιe₁ ιf₂) (hc y hyU)
      simp only [mul_e₁z hzU hyU, mul_e₁z hyU hzU, mul_e₁f₂ hzU hyU, mul_e₁f₂ hyU hzU, ha, c1, c3,
        c4, c5, c7, mul_zero, add_zero, zero_add, one_mul] at e1 e2
      have hu : mat z ιe₂ ιz = 0 := by linear_combination -e1
      have hd : mat z ιe₂ ιf₂ = 0 := by linear_combination -e2
      exact mem_A₂sub.2 ⟨hzU, hu, by rw [(U_rel hzU).2.1, hu, map_zero], hd⟩
    rw [← centerIn_A₂sub]
    exact ⟨hzA, mem_centralizer_iff.2 fun y hy => mem_centralizer_iff.1 hzc y (A₂sub_le_U hy)⟩
  · intro z hz
    exact ⟨ZPsub_le_U hz, mem_centralizer_iff.2 fun y hy => (ZPsub_commute hz hy).symm⟩

theorem centerIn_Ssub : CFSG.centerIn (Ssub h) = Vsub h := by
  ext g
  constructor
  · rintro ⟨hgS, hgc⟩
    exact (central_Ssub_iff hgS).1 fun s hs => mem_centralizer_iff.1 hgc s hs
  · intro hg
    exact ⟨Vsub_le_Ssub hg, mem_centralizer_iff.2 fun s hs =>
      ((central_Ssub_iff (Vsub_le_Ssub hg)).2 hg s hs)⟩

theorem closure_involutions_Ssub : closure {g | g ∈ Ssub h ∧ g * g = 1} = Vsub h := by
  refine le_antisymm ((closure_le _).2 fun g hg => mem_Vsub_of_sq hg.1 hg.2) fun v hv => ?_
  exact subset_closure ⟨Vsub_le_Ssub hv, Vsub_sq hv⟩

end Centres

theorem closure_squares_Ssub : closure {g | ∃ y ∈ Ssub h, g = y * y} = Vsub h := by
  refine le_antisymm ((closure_le _).2 ?_) (squares_generate_Vsub h)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hyU, a1, -⟩ := mem_Ssub'.1 hy
  rw [SetLike.mem_coe, sq_mem_Vsub_iff hyU, a1, zero_mul]

section Ranks

theorem card_Vsub_inf_centralizer_le {x : hypSU h 2 1} (hx : x ∈ hypUnitriangular h 2 1)
    (hxS : x ∉ Ssub h) :
    Nat.card (Vsub h ⊓ centralizer ({x} : Set (hypSU h 2 1)) : Subgroup _) ≤ (2 ^ f) ^ 2 := by
  have := h.charP
  have := h.finite
  have ha : aOf x ≠ 0 := fun h0 => hxS ((mem_Ssub_iff hx).2 h0)
  set T : Set (K × K) := {d | h.bar d = d} ×ˢ {c | h.bar (aOf x) * c + aOf x * h.bar c = 0}
  have hT : T.ncard = (2 ^ f) ^ 2 := by
    rw [Set.ncard_prod, U4.ncard_fixed h, U4.ncard_trace_mul_eq_zero h ha, sq]
  have hmem : ∀ v ∈ Vsub h ⊓ centralizer ({x} : Set (hypSU h 2 1)),
      Yof v 1 1 = 0 ∧ h.bar (Yof v 0 0) = Yof v 0 0 ∧
        h.bar (aOf x) * Yof v 0 1 + aOf x * h.bar (Yof v 0 1) = 0 := by
    rintro v ⟨hvV, hvC⟩
    obtain ⟨e1, e2⟩ := commute_Vsub_entries hx hvV (mem_centralizer_singleton_iff.1 hvC).symm
    have h11 := (mul_eq_zero.1 e1).resolve_left ha
    obtain ⟨h00, -, h10⟩ := isHerm_iff.1 (herm_Yof hvV)
    rw [h11, h10, mul_zero, zero_mul, add_zero] at e2
    exact ⟨h11, h00, by linear_combination e2⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← hT]
  refine Set.ncard_le_ncard_of_injOn (fun v => (Yof v 0 0, Yof v 0 1)) (fun v hv => ?_)
    (fun v hv v' hv' e => ?_) (Set.toFinite T)
  · obtain ⟨-, h00, h01⟩ := hmem v hv
    exact ⟨h00, h01⟩
  · obtain ⟨h11, -⟩ := hmem v hv
    obtain ⟨h11', -⟩ := hmem v' hv'
    simp only [Prod.mk.injEq] at e
    exact Yof_ext hv.1 hv'.1 e.1 e.2 (by rw [h11, h11'])

theorem mem_A₂sub_inf_Ssub_of_commutator {y : hypSU h 2 1} (hy : y ∈ hypUnitriangular h 2 1)
    (hyA : y ∉ A₂sub h) {a : hypSU h 2 1} (ha : a ∈ A₂sub h) (hc : ⁅a, y⁆ ∈ ZPsub h) :
    a ∈ A₂sub h ⊓ Ssub h := by
  obtain ⟨haU, a1, a2, a3⟩ := mem_A₂sub.1 ha
  have he := (commutator_mem_ZPsub_iff haU hy).1 hc
  have e1 := he ιe₁ ιz (by decide) (by decide)
  have e2 := he ιe₁ ιf₂ (by decide) (by decide)
  rw [mul_e₁z haU hy, mul_e₁z hy haU, a1] at e1
  rw [mul_e₁f₂ haU hy, mul_e₁f₂ hy haU, a2, a3, (U_rel hy).2.1] at e2
  have e1' : mat a ιe₁ ιe₂ * mat y ιe₂ ιz = 0 := by linear_combination e1
  have hα : mat a ιe₁ ιe₂ = 0 := by
    by_cases hu : mat y ιe₂ ιz = 0
    · have hd : mat y ιe₂ ιf₂ ≠ 0 := fun h0 =>
        hyA (mem_A₂sub.2 ⟨hy, hu, by rw [(U_rel hy).2.1, hu, map_zero], h0⟩)
      rw [hu, map_zero] at e2
      have : mat a ιe₁ ιe₂ * mat y ιe₂ ιf₂ = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_right hd
    · exact (mul_eq_zero.1 e1').resolve_right hu
  exact ⟨ha, (mem_Ssub_iff haU).2 hα⟩

end Ranks

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem pull_preimage {E : Subgroup G} (hE : E ≤ d.P) :
    d.pull (hypUnitriangular h 2 1 ⊓ E.comap d.η) = E := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨u, ⟨-, hu⟩, rfl⟩
    exact hu
  · obtain ⟨u, hu, rfl⟩ := hE hx
    exact ⟨u, ⟨hu, hx⟩, rfl⟩

theorem card_preimage {E : Subgroup G} (hE : E ≤ d.P) :
    Nat.card (hypUnitriangular h 2 1 ⊓ E.comap d.η : Subgroup _) = Nat.card E := by
  rw [← d.card_pull inf_le_left, d.pull_preimage hE]

theorem elemAbMod_preimage {N : Subgroup (hypSU h 2 1)} (hN : N ≤ hypUnitriangular h 2 1)
    {E : Subgroup G} (hE : ElemAbMod (d.pull N) E) :
    ElemAbMod N (hypUnitriangular h 2 1 ⊓ E.comap d.η) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := hE.1 _ hx.2
    rw [← map_mul] at this
    exact (d.η_mem_pull_iff hN (mul_mem hx.1 hx.1)).1 this
  · have := hE.2 _ hx.2 _ hy.2
    rw [← map_commutatorElement] at this
    have hU : ⁅x, y⁆ ∈ hypUnitriangular h 2 1 := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx.1 hy.1) (inv_mem hx.1)) (inv_mem hy.1)
    exact (d.η_mem_pull_iff hN hU).1 this

theorem centerIn_pull {M : Subgroup (hypSU h 2 1)} (hM : M ≤ hypUnitriangular h 2 1) :
    CFSG.centerIn (d.pull M) = d.pull (CFSG.centerIn M) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨m, hm, rfl⟩, hc⟩
    refine ⟨m, ⟨hm, mem_centralizer_iff.2 fun m' hm' => d.η_injOn (mul_mem (hM hm') (hM hm))
      (mul_mem (hM hm) (hM hm')) ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hc _ ⟨m', hm', rfl⟩
  · rintro _ ⟨m, ⟨hm, hc⟩, rfl⟩
    refine ⟨⟨m, hm, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨m', hm', rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hc m' hm']

theorem sec2_2_modZp {E : Subgroup G} (hEP : E ≤ d.P) (hE : ElemAbMod d.Zp E) :
    (E ≤ d.A₂ ∨ E ≤ d.A₁ ⊔ (d.A₂ ⊓ d.A₃)) ∧ Nat.card E ≤ (2 ^ f) ^ 7 ∧
      ((2 ^ f) ^ 7 ≤ Nat.card E → E = d.A₂) := by
  set E' := hypUnitriangular h 2 1 ⊓ E.comap d.η
  have hE' := d.elemAbMod_preimage ZPsub_le_U hE
  have hpull := d.pull_preimage hEP
  have hcard := d.card_preimage hEP
  obtain ⟨hc1, hc2⟩ := card_le_of_elemAbMod_ZPsub inf_le_left hE'
  refine ⟨?_, hcard ▸ hc1, fun hge => ?_⟩
  · rw [← hpull]
    rcases le_A₂sub_or_le_sB₁_of_elemAbMod inf_le_left hE' with h1 | h1
    · exact Or.inl (d.pull_mono h1)
    · right
      rw [← Vsub_sup_A₂sub_inf_Ssub_eq] at h1
      refine (d.pull_mono h1).trans ?_
      rw [pull, Subgroup.map_sup, ← pull, ← pull, d.pull_inf A₂sub_le_U Ssub_le_Usub]
      rfl
  · rw [← hpull, hc2 (hcard ▸ hge)]
    rfl

theorem A₃_sup_A₁_sup_A₂ : d.A₃ ⊔ (d.A₁ ⊔ d.A₂) = d.P := by
  change d.pull (Ssub h) ⊔ (d.pull (Vsub h) ⊔ d.pull (A₂sub h)) = d.pull _
  rw [pull, pull, pull, ← Subgroup.map_sup, ← Subgroup.map_sup, Ssub_sup_Vsub_sup_A₂sub]
  rfl

theorem sec2_2_three :
    closure {g | g ∈ d.A₃ ∧ g * g = 1} = d.A₁ ∧ closure {g | ∃ y ∈ d.A₃, g = y * y} = d.A₁ ∧
      CFSG.centerIn d.A₃ = d.A₁ ∧ CFSG.centerIn d.A₂ = d.Zp ∧ CFSG.centerIn d.P = d.Zp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hset : {g | g ∈ d.A₃ ∧ g * g = 1} = d.η '' {g | g ∈ Ssub h ∧ g * g = 1} := by
      ext x
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hx2⟩
        refine ⟨u, ⟨hu, d.η_injOn (mul_mem (Ssub_le_Usub hu) (Ssub_le_Usub hu)) (one_mem _)
          (by rw [map_mul, hx2, map_one])⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hu2⟩, rfl⟩
        exact ⟨⟨u, hu, rfl⟩, by rw [← map_mul, hu2, map_one]⟩
    rw [hset, ← MonoidHom.map_closure, closure_involutions_Ssub]
    rfl
  · have hset : {g | ∃ y ∈ d.A₃, g = y * y} = d.η '' {g | ∃ y ∈ Ssub h, g = y * y} := by
      ext x
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u * u, ⟨u, hu, rfl⟩, by rw [map_mul]⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨d.η u, ⟨u, hu, rfl⟩, by rw [map_mul]⟩
    rw [hset, ← MonoidHom.map_closure, closure_squares_Ssub]
    rfl
  · rw [Data.A₃, d.centerIn_pull Ssub_le_Usub, centerIn_Ssub]
    rfl
  · rw [Data.A₂, d.centerIn_pull A₂sub_le_U, centerIn_A₂sub]
    rfl
  · rw [Data.P, d.centerIn_pull le_rfl, centerIn_U]
    rfl

theorem sec2_2_five :
    (∀ x ∈ d.P, x ∉ d.A₃ →
      Nat.card (d.A₁ ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 2) ∧
    ∀ y ∈ d.P, y ∉ d.A₂ → ∀ a ∈ d.A₂, ⁅a, y⁆ ∈ d.Zp → a ∈ d.A₂ ⊓ d.A₃ := by
  have hV : Vsub h ≤ hypUnitriangular h 2 1 := Vsub_le_Ssub.trans Ssub_le_Usub
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ hxS
    have huS : u ∉ Ssub h := fun h1 => hxS ⟨u, h1, rfl⟩
    have e : d.A₁ ⊓ centralizer ({d.η u} : Set G) =
        d.pull (Vsub h ⊓ centralizer ({u} : Set (hypSU h 2 1))) := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨⟨v, hv, rfl⟩, hc⟩
        refine ⟨v, ⟨hv, mem_centralizer_singleton_iff.2 (d.η_injOn (mul_mem (hV hv) hu)
          (mul_mem hu (hV hv)) ?_)⟩, rfl⟩
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.1 hc
      · rintro _ ⟨v, ⟨hv, hc⟩, rfl⟩
        refine ⟨⟨v, hv, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
    rw [e, d.card_pull (inf_le_left.trans hV)]
    exact card_Vsub_inf_centralizer_le hu huS
  · rintro _ ⟨y, hy, rfl⟩ hyA _ ⟨a, ha, rfl⟩ hc
    have hyA' : y ∉ A₂sub h := fun h1 => hyA ⟨y, h1, rfl⟩
    have haU := A₂sub_le_U ha
    have hU : ⁅a, y⁆ ∈ hypUnitriangular h 2 1 := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem haU hy) (inv_mem haU)) (inv_mem hy)
    rw [← map_commutatorElement] at hc
    have hc' := (d.η_mem_pull_iff ZPsub_le_U hU).1 hc
    have hm := mem_A₂sub_inf_Ssub_of_commutator hy hyA' ha hc'
    exact ⟨⟨a, hm.1, rfl⟩, ⟨a, hm.2, rfl⟩⟩

end Data

section SecondCentre

theorem mem_Z₂Psub_iff_commutator {g : hypSU h 2 1} :
    g ∈ Z₂Psub h ↔ g ∈ hypUnitriangular h 2 1 ∧
      ∀ y ∈ hypUnitriangular h 2 1, ⁅g, y⁆ ∈ ZPsub h := by
  have := h.charP
  constructor
  · intro hg
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7⟩ := mem_Z₂Psub.1 hg
    refine ⟨hgU, fun y hy => (commutator_mem_ZPsub_iff hgU hy).2 (forall_upper.2 ?_)⟩
    obtain ⟨r1, r2, r3, -⟩ := U_rel hy
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hne => absurd rfl hne, fun _ => ?_,
      fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [mul_e₁e₂ hgU hy, mul_e₁e₂ hy hgU, add_comm]
    · rw [mul_e₁z hgU hy, mul_e₁z hy hgU, a1, a5]; ring
    · rw [mul_e₁f₂ hgU hy, mul_e₁f₂ hy hgU, a1, a3, a6, a7]; ring
    · rw [mul_e₂z hgU hy, mul_e₂z hy hgU, add_comm]
    · rw [mul_e₂f₂ hgU hy, mul_e₂f₂ hy hgU, a5, a6]; ring
    · rw [mul_e₂f₁ hgU hy, mul_e₂f₁ hy hgU, a5, a7, a2, a4]; ring
    · rw [mul_zf₂ hgU hy, mul_zf₂ hy hgU, add_comm]
    · rw [mul_zf₁ hgU hy, mul_zf₁ hy hgU, a6, a2]; ring
    · rw [mul_f₂f₁ hgU hy, mul_f₂f₁ hy hgU, add_comm]
  · rintro ⟨hgU, hc⟩
    obtain ⟨y, hy, hya⟩ := exists_rootI₁ h 1
    obtain ⟨hyU, c1, c2, c3, c4, c5, c6, c7, c8⟩ := mem_patSub_sI₁.1 hy
    have hy1 := (commutator_mem_ZPsub_iff hgU hyU).1 (hc y hyU)
    have e1 := hy1 ιe₁ ιz (by decide) (by decide)
    have e2 := hy1 ιe₁ ιf₂ (by decide) (by decide)
    rw [mul_e₁z hgU hyU, mul_e₁z hyU hgU, hya, c1, c3] at e1
    rw [mul_e₁f₂ hgU hyU, mul_e₁f₂ hyU hgU, hya, c1, c4, c5, c7] at e2
    have hu : mat g ιe₂ ιz = 0 := by linear_combination -e1
    have hd : mat g ιe₂ ιf₂ = 0 := by linear_combination -e2
    obtain ⟨c, hcc⟩ := trace_surj (hK := h) (a := 1 * h.bar 1) (by simp)
    obtain ⟨y', hy', hyu, hyc⟩ := exists_rootI₂ h hcc
    obtain ⟨hyU', d1, d2, d3, d4, d5, d6, d7⟩ := mem_patSub_sI₂.1 hy'
    have hy2 := (commutator_mem_ZPsub_iff hgU hyU').1 (hc y' hyU')
    have e3 := hy2 ιe₁ ιz (by decide) (by decide)
    have e4 := hy2 ιe₂ ιf₁ (by decide) (by decide)
    rw [mul_e₁z hgU hyU', mul_e₁z hyU' hgU, hyu, d1, d3, hu] at e3
    have ha : mat g ιe₁ ιe₂ = 0 := by linear_combination e3
    obtain ⟨r1, r2, r3, -⟩ := U_rel hgU
    rw [mul_e₂f₁ hgU hyU', mul_e₂f₁ hyU' hgU, hyu, hyc, hu, hd, d2, d4, r1, r3, ha, d6] at e4
    have hw : mat g ιe₁ ιz = 0 := by
      have : h.bar (mat g ιe₁ ιz) = 0 := by
        simp only [map_zero, zero_mul, add_zero, mul_zero, zero_add, one_mul] at e4
        linear_combination -e4
      exact (map_eq_zero h.bar).1 this
    exact mem_Z₂Psub.2 ⟨hgU, ha, by rw [r1, ha, map_zero], hw, by rw [r3, hw, ha]; simp, hu,
      by rw [r2, hu, map_zero], hd⟩

end SecondCentre

end CFSG.LocalAnalysis.EvenBN.U5
