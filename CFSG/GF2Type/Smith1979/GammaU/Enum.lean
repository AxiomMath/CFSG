
module

public import CFSG.GF2Type.Smith1979.GammaU.EnumDefs
public import CFSG.GF2Type.Smith1979.GammaU.Violation
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.GF2Type.Smith1979.GammaU.Enum

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol
open scoped commutatorElement

instance : Finite (V12 ≃ₗ[ZMod 2] V12) :=
  Finite.of_injective (fun e : V12 ≃ₗ[ZMod 2] V12 => (e : V12 → V12))
    fun _ _ h => LinearEquiv.ext (congrFun h)

@[expose] def Rep (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (x : Array ℕ) : Prop :=
  okRows x = true ∧ ∃ U ∈ N, ∀ v, U v = linOfRows x v

theorem idR_ok : okRows idR = true := by simp [okRows, idR]

theorem enumGrp_sound {gs : List (Array ℕ)} (hgs : GensOK gs) :
    ∀ x ∈ enumGrp gs, Rep (genGrp gs) x := by
  unfold enumGrp
  refine bfsClosure_inv _ _ ?_ _ _ _ _ ?_ (by simp)
  · intro f hf x hx
    obtain ⟨hok, U, hU, hUx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hgok, -, h1, h2⟩ := hgs g hg
    refine ⟨okRows_mulR hok hgok, U * eqvOf g (invR g) h1 h2, mul_mem hU (gen_mem hgs hg),
      fun v => ?_⟩
    rw [LinearEquiv.mul_apply, eqvOf_apply, hUx, linOfRows_mulR]
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨idR_ok, 1, one_mem _, fun v => (linOfRows_idR v).symm⟩

theorem mem_of_closedCheck {gs X : List (Array ℕ)} (hc : closedCheck gs X = true) {x g : Array ℕ}
    (hx : x ∈ X) (hg : g ∈ gs) : mulR x g ∈ X := by
  simp only [closedCheck, List.all_eq_true] at hc
  have h := hc x hx g hg
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  exact h

theorem complete {gs X : List (Array ℕ)} (hid : idR ∈ X) (hc : closedCheck gs X = true) :
    ∀ u ∈ genGrp gs, ∃ x ∈ X, ∀ v, u v = linOfRows x v := by
  intro u hu
  have hu' : u ∈ Submonoid.closure (GenSet gs) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hu
  refine Submonoid.closure_induction_right
    (motive := fun u _ => ∃ x ∈ X, ∀ v, u v = linOfRows x v) ?_ ?_ hu'
  · exact ⟨idR, hid, fun v => (linOfRows_idR v).symm⟩
  · rintro u - s ⟨g, hg, hs⟩ ⟨x, hx, hux⟩
    exact ⟨mulR x g, mem_of_closedCheck hc hx hg, fun v => by
      rw [LinearEquiv.mul_apply, hs, hux, linOfRows_mulR]⟩

@[expose] noncomputable def rowsOf (u : V12 ≃ₗ[ZMod 2] V12) : Array ℕ :=
  ((List.range 12).map fun j => codeOf (u (vecOf (2 ^ j)))).toArray

theorem rowsOf_size (u : V12 ≃ₗ[ZMod 2] V12) : (rowsOf u).size = 12 := by
  simp [rowsOf]

theorem rowsOf_lt (u : V12 ≃ₗ[ZMod 2] V12) : ∀ x ∈ rowsOf u, x < 4096 := by
  intro x hx
  simp only [rowsOf, List.mem_toArray, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact codeOf_lt _

theorem linOfRows_rowsOf (u : V12 ≃ₗ[ZMod 2] V12) (v : V12) : linOfRows (rowsOf u) v = u v := by
  have hf : linOfRows (rowsOf u) = (u : V12 →ₗ[ZMod 2] V12) := linMap_ext fun j => by
    rw [linOfRows_unit]
    have hj : (j : ℕ) < (rowsOf u).size := by rw [rowsOf_size]; exact j.isLt
    rw [getElem!_pos (rowsOf u) (j : ℕ) hj]
    simp only [rowsOf, List.getElem_toArray, List.getElem_map, List.getElem_range]
    exact vecOf_codeOf _
  exact LinearMap.congr_fun hf v

theorem rowsOf_eq {u : V12 ≃ₗ[ZMod 2] V12} {x : Array ℕ} (hx : okRows x = true)
    (h : ∀ v, u v = linOfRows x v) : rowsOf u = x :=
  rows_eq (rowsOf_size u) (okRows_spec hx).1 (rowsOf_lt u) (okRows_spec hx).2 fun v => by
    rw [linOfRows_rowsOf, h]

theorem card_genGrp {gs X : List (Array ℕ)} (hX : ∀ x ∈ X, Rep (genGrp gs) x) (hid : idR ∈ X)
    (hc : closedCheck gs X = true) : Nat.card (genGrp gs) = X.dedup.length := by
  have hmem : ∀ u : genGrp gs, rowsOf u ∈ X.toFinset := fun u => by
    obtain ⟨x, hx, hux⟩ := complete hid hc u u.2
    rw [List.mem_toFinset, rowsOf_eq (hX x hx).1 hux]
    exact hx
  let f : genGrp gs → X.toFinset := fun u => ⟨rowsOf u, hmem u⟩
  have hinj : Function.Injective f := fun u u' h => by
    have h' : rowsOf u = rowsOf u' := congrArg Subtype.val h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [← linOfRows_rowsOf, h', linOfRows_rowsOf]
  have hsurj : Function.Surjective f := fun ⟨x, hx⟩ => by
    obtain ⟨hok, U, hU, hUx⟩ := hX x (List.mem_toFinset.1 hx)
    exact ⟨⟨U, hU⟩, Subtype.ext (rowsOf_eq hok hUx)⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe, List.card_toFinset]

theorem commutatorElement_mul_right {G : Type*} [Group G] (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_inv_right {G : Type*} [Group G] (a b : G) :
    ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b⁻¹⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_left {G : Type*} [Group G] (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_inv_left {G : Type*} [Group G] (a b : G) :
    ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a⁻¹⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutator_le_of_gens {G : Type*} [Group G] {S : Set G} {P : Subgroup G}
    (hnorm : Subgroup.closure S ≤ Subgroup.normalizer (P : Set G)) (hcomm : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ P) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ P := by
  have hconj : ∀ g ∈ Subgroup.closure S, ∀ h ∈ P, g * h * g⁻¹ ∈ P := fun g hg h hh =>
    (Subgroup.mem_normalizer_iff.1 (hnorm hg) h).1 hh
  have step1 : ∀ a ∈ S, ∀ b ∈ Subgroup.closure S, ⁅a, b⁆ ∈ P := by
    intro a ha b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb => exact hcomm a ha b hb
    | one => rw [commutatorElement_one_right]; exact one_mem _
    | mul b c hb hc ihb ihc =>
      rw [commutatorElement_mul_right]
      exact mul_mem ihb (hconj b hb _ ihc)
    | inv b hb ihb =>
      rw [commutatorElement_inv_right]
      exact hconj _ (inv_mem hb) _ (inv_mem ihb)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  induction ha using Subgroup.closure_induction with
  | mem a ha => exact step1 a ha b hb
  | one => rw [commutatorElement_one_left]; exact one_mem _
  | mul a c ha hc iha ihc =>
    rw [commutatorElement_mul_left]
    exact mul_mem (hconj a ha _ ihc) iha
  | inv a ha iha =>
    rw [commutatorElement_inv_left]
    exact hconj _ (inv_mem ha) _ (inv_mem iha)

end CFSG.GF2Type.Smith1979.GammaU.Enum
