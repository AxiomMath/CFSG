module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Griess

public noncomputable section

namespace CFSG.EvenSmallLie.FFourTwo.General

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open scoped commutatorElement

section IndexTwo

variable {E : Type*} [Group E]

@[expose] def adjoinInvolution (D : Subgroup E) {x : E} (hx : x ∈ center E) (hx2 : x * x = 1) :
    Subgroup E where
  carrier := {y | y ∈ D ∨ y * x ∈ D}
  one_mem' := Or.inl D.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (D.mul_mem ha hb)
    · right
      rw [mul_assoc]
      exact D.mul_mem ha hb
    · right
      rw [mul_assoc, mem_center_iff.1 hx b, ← mul_assoc]
      exact D.mul_mem ha hb
    · left
      have e : a * b = a * x * (b * x) := by
        calc a * b = a * b * (x * x) := by rw [hx2, mul_one]
          _ = a * (b * x) * x := by group
          _ = a * (x * b) * x := by rw [mem_center_iff.1 hx b]
          _ = a * x * (b * x) := by group
      rw [e]
      exact D.mul_mem ha hb
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (D.inv_mem ha)
    · right
      have e : a⁻¹ * x = (a * x)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2, mem_center_iff.1 hx a⁻¹]
      rw [e]
      exact D.inv_mem ha

theorem mem_adjoinInvolution {D : Subgroup E} {x : E} {hx : x ∈ center E} {hx2 : x * x = 1}
    {y : E} : y ∈ adjoinInvolution D hx hx2 ↔ y ∈ D ∨ y * x ∈ D :=
  Iff.rfl

theorem exists_index_two [Finite E] {C : Subgroup E} (hC : C ≤ center E)
    (h2 : ∀ x ∈ C, x * x = 1) {ε c : E} (hε : ε ∈ C) (hcε : c ∉ zpowers ε) :
    ∃ D : Subgroup E, D ≤ C ∧ ε ∈ D ∧ c ∉ D ∧ ∀ x ∈ C, x ∈ D ∨ x * c ∈ D := by
  obtain ⟨D, -, ⟨hDC, hεD, hcD⟩, hmax⟩ :=
    Set.Finite.exists_le_maximal (s := {D : Subgroup E | D ≤ C ∧ ε ∈ D ∧ c ∉ D})
      (Set.toFinite _) (a := zpowers ε) ⟨zpowers_le.2 hε, mem_zpowers ε, hcε⟩
  refine ⟨D, hDC, hεD, hcD, fun x hx => ?_⟩
  by_contra hne
  rw [not_or] at hne
  have hD' : adjoinInvolution D (hC hx) (h2 x hx) ≤ C := fun y hy => by
    rcases mem_adjoinInvolution.1 hy with hy | hy
    · exact hDC hy
    · have := C.mul_mem (hDC hy) (C.inv_mem hx)
      rwa [mul_inv_cancel_right] at this
  have hcD' : c ∉ adjoinInvolution D (hC hx) (h2 x hx) := fun h => by
    rcases mem_adjoinInvolution.1 h with h | h
    · exact hcD h
    · exact hne.2 (by rw [← mem_center_iff.1 (hC hx) c]; exact h)
  have hle : adjoinInvolution D (hC hx) (h2 x hx) ≤ D :=
    hmax ⟨hD', mem_adjoinInvolution.2 (Or.inl hεD), hcD'⟩
      fun y hy => mem_adjoinInvolution.2 (Or.inl hy)
  exact hne.1 (hle (mem_adjoinInvolution.2 (Or.inr (by rw [h2 x hx]; exact D.one_mem))))

end IndexTwo

section QuotCover

variable {K : Type} [Field K] {E : Type*} [Group E] {η : E →* adjointGroup .F4 K}
  (hη : Function.Surjective η)

@[expose] def quotCover (hK : Nat.card K = 2) (hC : η.ker ≤ center E)
    (h2 : ∀ k ∈ η.ker, k * k = 1) (D : Subgroup E) [D.Normal] (hD : D ≤ η.ker) {c : E}
    (hc : c ∈ η.ker) (hcD : c ∉ D) (hidx : ∀ x ∈ η.ker, x ∈ D ∨ x * c ∈ D) :
    Cover K (E ⧸ D) where
  card := hK
  π := QuotientGroup.lift D η hD
  surj := fun g => by
    obtain ⟨e, rfl⟩ := hη g
    exact ⟨(e : E ⧸ D), QuotientGroup.lift_mk _ _ _⟩
  ker_le := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η.ker := by
      rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hy
      exact hy
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hC he) g']
  z := (c : E ⧸ D)
  z_ne := fun h => hcD ((QuotientGroup.eq_one_iff c).1 h)
  ker_iff := fun k => by
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective k
    rw [QuotientGroup.lift_mk]
    constructor
    · intro he
      rcases hidx e he with h | h
      · exact Or.inl ((QuotientGroup.eq_one_iff e).2 h)
      · right
        rw [QuotientGroup.eq, inv_eq_of_mul_eq_one_right (h2 e he)]
        exact h
    · rintro (h | h)
      · exact hD ((QuotientGroup.eq_one_iff e).1 h)
      · have h' := congrArg (QuotientGroup.lift D η hD) h
        rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at h'
        rw [h']
        exact hc

end QuotCover

section Lifts


variable {K : Type} [Field K] {E : Type*} [Group E] {η : E →* adjointGroup .F4 K}
  (hη : Function.Surjective η)

@[expose] def rootLift (r : Fin Tag.F4.rank → ℤ) : E :=
  Function.surjInv hη (xr r)

theorem rootLift_spec (r : Fin Tag.F4.rank → ℤ) : η (rootLift hη r) = xr r :=
  Function.surjInv_eq hη _

@[expose] def yhatE (r : Fin Tag.F4.rank → ℤ) : E :=
  haveI := Classical.propDecidable (IsRoot .F4 r)
  if h : IsRoot .F4 r then
    ⁅rootLift hη (Cover.exists_dec r h).choose,
      rootLift hη (Cover.exists_dec r h).choose_spec.choose⁆
  else 1

@[expose] def twistE (a b : Fin Tag.F4.rank → ℤ) : E :=
  (yhatE hη (a + b) * yhatE hη (a + 2 • b))⁻¹ * ⁅yhatE hη a, yhatE hη b⁆

theorem yhatE_eq {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    yhatE hη r = ⁅rootLift hη (Cover.exists_dec r hr).choose,
      rootLift hη (Cover.exists_dec r hr).choose_spec.choose⁆ := by
  rw [yhatE]
  simp only [hr, ↓reduceDIte]

end Lifts

section Twist

section Map

variable {K : Type} [Field K] {E : Type*} [Group E] {η : E →* adjointGroup .F4 K}
  (hη : Function.Surjective η)

theorem map_yhatE (hK : Nat.card K = 2) {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    η (yhatE hη r) = xr r := by
  rw [yhatE_eq hη hr, map_commutatorElement, rootLift_spec, rootLift_spec,
    (Cover.xr_commutator_of_dec hK (Cover.exists_dec r hr).choose_spec.choose_spec).2]

theorem twistE_mem_ker (hK : Nat.card K = 2) {a b : Fin Tag.F4.rank → ℤ} (h : Cover.Mixed a b) :
    twistE hη a b ∈ η.ker := by
  obtain ⟨h1, h2, h3⟩ := Cover.xr_commutator_of_mixed hK h
  rw [MonoidHom.mem_ker, twistE, map_mul, map_inv, map_mul, map_commutatorElement,
    map_yhatE hη hK h.1, map_yhatE hη hK h.2.1, map_yhatE hη hK h1, map_yhatE hη hK h2, h3,
    inv_mul_cancel]

variable {M : Type*} [Group M]

theorem yhat_eq_map (C : Cover K M) {q : E →* M} (hq : ∀ e, C.π (q e) = η e)
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) : C.yhat r = q (yhatE hη r) := by
  rw [yhatE_eq hη hr, map_commutatorElement,
    C.yhat_eq (Cover.exists_dec r hr).choose_spec.choose_spec]
  exact (C.cc_eq (by rw [hq, rootLift_spec]) (by rw [hq, rootLift_spec])).symm

theorem twist_eq_map (C : Cover K M) {q : E →* M} (hq : ∀ e, C.π (q e) = η e)
    {a b : Fin Tag.F4.rank → ℤ} (h : Cover.Mixed a b) : C.twist a b = q (twistE hη a b) := by
  obtain ⟨h1, h2, -⟩ := Cover.xr_commutator_of_mixed C.card h
  rw [Cover.twist, twistE, map_mul, map_inv, map_mul, map_commutatorElement,
    yhat_eq_map hη C hq h.1, yhat_eq_map hη C hq h.2.1, yhat_eq_map hη C hq h1,
    yhat_eq_map hη C hq h2]

theorem ker_eq_zpowers_twistE (hK : Nat.card K = 2) [Finite E] [Group.IsPerfect E]
    (hC : η.ker ≤ center E) (h2 : ∀ k ∈ η.ker, k * k = 1) {a b : Fin Tag.F4.rank → ℤ}
    (h : Cover.Mixed a b) : η.ker = zpowers (twistE hη a b) := by
  have hε := twistE_mem_ker hη hK h
  refine le_antisymm (fun c hc => ?_) (zpowers_le.2 hε)
  by_contra hcε
  obtain ⟨D, hDC, hεD, hcD, hidx⟩ := exists_index_two hC h2 hε hcε
  have : D.Normal := normal_of_le_center (hDC.trans hC)
  have : Group.IsPerfect (E ⧸ D) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective D)
  have h1 := (quotCover hη hK hC h2 D hDC hc hcD hidx).twist_eq_z h
  rw [twist_eq_map hη _ (q := QuotientGroup.mk' D) (fun _ => rfl) h] at h1
  have h3 : ((twistE hη a b : E) : E ⧸ D) = (c : E ⧸ D) := h1
  rw [(QuotientGroup.eq_one_iff _).2 hεD] at h3
  exact hcD ((QuotientGroup.eq_one_iff c).1 h3.symm)

end Map

theorem card_ker_le_two {K : Type} [Field K] (hK : Nat.card K = 2) {E : Type*} [Group E]
    [Finite E] [Group.IsPerfect E] (η : E →* adjointGroup .F4 K) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) : Nat.card η.ker ≤ 2 := by
  have hsq : ∀ k ∈ η.ker, k * k = 1 := fun k hk => by
    rw [← sq]
    exact (F4_field_two_central_two_kernel_elementary hK η hη hC h2).1 k hk
  have hm : Cover.Mixed (![1, 0, 0, 0] : Fin Tag.F4.rank → ℤ) ![0, 1, 1, 0] :=
    ⟨isRoot_of_ofFn (by decide +kernel), isRoot_of_ofFn (by decide +kernel), by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  rw [ker_eq_zpowers_twistE hη hK hC hsq hm, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact hsq _ (twistE_mem_ker hη hK hm))

end Twist

end CFSG.EvenSmallLie.FFourTwo.General
