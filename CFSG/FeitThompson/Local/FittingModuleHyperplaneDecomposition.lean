module

public import Mathlib.GroupTheory.PGroup
public import CFSG.FeitThompson.Representations.PrimeFieldRepAlgClosedExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import CFSG.FeitThompson.Representations.CoprimeAbelianWeightDecomposition
import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p q : ℕ} {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def fixedSpace (ρ : Representation (ZMod p) K V) (L : Subgroup K) : Submodule (ZMod p) V where
  carrier := {v | ∀ x ∈ L, ρ x v = v}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb x hx; rw [map_add, ha x hx, hb x hx]
  smul_mem' := by intro c a ha x hx; rw [map_smul, ha x hx]

@[simp] lemma mem_fixedSpace {ρ : Representation (ZMod p) K V} {L : Subgroup K} {v : V} :
    v ∈ fixedSpace ρ L ↔ ∀ x ∈ L, ρ x v = v := Iff.rfl

def actionKernel (ρ : Representation (ZMod p) K V) (W : Submodule (ZMod p) V) : Subgroup K where
  carrier := {x | ∀ v ∈ W, ρ x v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have h1 : ρ a⁻¹ (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha v hv] at h1

@[simp] lemma mem_actionKernel {ρ : Representation (ZMod p) K V} {W : Submodule (ZMod p) V}
    {x : K} : x ∈ actionKernel ρ W ↔ ∀ v ∈ W, ρ x v = v := Iff.rfl

lemma fixedSpace_anti (ρ : Representation (ZMod p) K V) {L L' : Subgroup K} (h : L ≤ L') :
    fixedSpace ρ L' ≤ fixedSpace ρ L := fun _ hv x hx => hv x (h hx)

lemma fixedSpace_top (ρ : Representation (ZMod p) K V) : fixedSpace ρ ⊤ = ρ.invariants := by
  ext v
  rw [mem_fixedSpace, Representation.mem_invariants]
  exact ⟨fun h x => h x (Subgroup.mem_top x), fun h x _ => h x⟩

lemma le_actionKernel_fixedSpace (ρ : Representation (ZMod p) K V) (L : Subgroup K) :
    L ≤ actionKernel ρ (fixedSpace ρ L) := fun x hx _ hv => hv x hx

private def vectorStabilizer (ρ : Representation (ZMod p) K V) (v : V) : Subgroup K where
  carrier := {x | ρ x v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ a v = v at ha
    change ρ b v = v at hb
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change ρ a v = v at ha
    change ρ a⁻¹ v = v
    have h1 : ρ a⁻¹ (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h1

lemma fixedSpace_sup (ρ : Representation (ZMod p) K V) (L L' : Subgroup K) :
    fixedSpace ρ (L ⊔ L') = fixedSpace ρ L ⊓ fixedSpace ρ L' := by
  refine le_antisymm (le_inf (fixedSpace_anti ρ le_sup_left) (fixedSpace_anti ρ le_sup_right)) ?_
  rintro v ⟨hv, hv'⟩
  have hle : L ⊔ L' ≤ vectorStabilizer ρ v :=
    sup_le (fun x hx => hv x hx) (fun x hx => hv' x hx)
  exact fun x hx => hle hx

lemma mem_fixedSpace_zpowers {ρ : Representation (ZMod p) K V} {x : K} {v : V}
    (hxv : ρ x v = v) : v ∈ fixedSpace ρ (Subgroup.zpowers x) := by
  have hxinv : ρ x⁻¹ v = v := by
    have h1 : ρ x⁻¹ (ρ x v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [hxv] at h1
  have key : ∀ n : ℤ, ρ (x ^ n) v = v := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, map_mul, Module.End.mul_apply, hxv, ih]
    | pred k ih => rw [zpow_sub_one, map_mul, Module.End.mul_apply, hxinv, ih]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact key n

lemma sup_zpowers_eq_top_of_index_eq {L : Subgroup K} (hq : q.Prime) (hL : L.index = q) {x : K}
    (hx : x ∉ L) : L ⊔ Subgroup.zpowers x = ⊤ := by
  set M : Subgroup K := L ⊔ Subgroup.zpowers x with hM
  have hkey := Subgroup.relIndex_mul_index (le_sup_left : L ≤ M)
  rw [hL] at hkey
  have hxM : x ∈ M := (le_sup_right : Subgroup.zpowers x ≤ M) (Subgroup.mem_zpowers x)
  have hrel : L.relIndex M ≠ 1 := fun h =>
    hx (Subgroup.relIndex_eq_one.1 h hxM)
  refine Subgroup.index_eq_one.1 ?_
  rcases hq.eq_one_or_self_of_dvd M.index ⟨L.relIndex M, by rw [← hkey]; ring⟩ with h | h
  · exact h
  · exact absurd (Nat.eq_of_mul_eq_mul_right hq.pos (by rw [h] at hkey; rw [hkey, one_mul])) hrel

lemma sup_eq_top_of_index_eq {L L' : Subgroup K} (hq : q.Prime) (hL : L.index = q)
    (hL' : L'.index = q) (hne : L ≠ L') : L ⊔ L' = ⊤ := by
  have hnle : ¬ L' ≤ L := by
    intro hle
    have hk := Subgroup.relIndex_mul_index hle
    rw [hL, hL'] at hk
    have h1 : L'.relIndex L = 1 := Nat.eq_of_mul_eq_mul_right hq.pos (by rw [hk, one_mul])
    exact hne ((Subgroup.relIndex_eq_one.1 h1).antisymm hle)
  obtain ⟨x, hxL', hxL⟩ := Set.not_subset.1 hnle
  refine top_unique ?_
  rw [← sup_zpowers_eq_top_of_index_eq hq hL hxL]
  exact sup_le le_sup_left (le_sup_right.trans' (Subgroup.zpowers_le.2 hxL'))

section Averaging

variable [Finite K]

private noncomputable def sgFinset (L : Subgroup K) : Finset K := (L : Set K).toFinite.toFinset

@[simp] private lemma mem_sgFinset {L : Subgroup K} {x : K} : x ∈ sgFinset L ↔ x ∈ L := by
  simp [sgFinset]

private lemma card_sgFinset (L : Subgroup K) : (sgFinset L).card = Nat.card L := by
  rw [sgFinset, ← Set.ncard_eq_toFinset_card (L : Set K) (L : Set K).toFinite,
    ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.refl _)

noncomputable def sumOver (ρ : Representation (ZMod p) K V) (L : Subgroup K) :
    Module.End (ZMod p) V := ∑ y ∈ sgFinset L, ρ y

private lemma sumOver_apply (ρ : Representation (ZMod p) K V) (L : Subgroup K) (v : V) :
    sumOver ρ L v = ∑ y ∈ sgFinset L, ρ y v := by
  simp [sumOver, LinearMap.sum_apply]

lemma sumOver_apply_mem_fixedSpace (ρ : Representation (ZMod p) K V) (L : Subgroup K) (v : V) :
    sumOver ρ L v ∈ fixedSpace ρ L := by
  intro x hx
  rw [sumOver_apply, map_sum]
  refine Finset.sum_nbij' (i := fun y => x * y) (j := fun y => x⁻¹ * y) ?_ ?_ ?_ ?_ ?_
  · intro y hy; simp only [mem_sgFinset] at hy ⊢; exact mul_mem hx hy
  · intro y hy; simp only [mem_sgFinset] at hy ⊢; exact mul_mem (inv_mem hx) hy
  · intro y _; simp
  · intro y _; simp
  · intro y _; rw [← Module.End.mul_apply, ← map_mul]

lemma sumOver_apply_of_mem_fixedSpace {ρ : Representation (ZMod p) K V} {L : Subgroup K} {v : V}
    (hv : v ∈ fixedSpace ρ L) : sumOver ρ L v = (Nat.card L : ZMod p) • v := by
  rw [sumOver_apply, Finset.sum_congr rfl (fun y hy => hv y (mem_sgFinset.1 hy)),
    Finset.sum_const, card_sgFinset, Nat.cast_smul_eq_nsmul]

noncomputable def projFixedSpace (ρ : Representation (ZMod p) K V) (L : Subgroup K) :
    Module.End (ZMod p) V := (Nat.card L : ZMod p)⁻¹ • sumOver ρ L

lemma projFixedSpace_apply (ρ : Representation (ZMod p) K V) (L : Subgroup K) (v : V) :
    projFixedSpace ρ L v = (Nat.card L : ZMod p)⁻¹ • sumOver ρ L v := (rfl)

lemma projFixedSpace_mem (ρ : Representation (ZMod p) K V) (L : Subgroup K) (v : V) :
    projFixedSpace ρ L v ∈ fixedSpace ρ L :=
  (fixedSpace ρ L).smul_mem _ (sumOver_apply_mem_fixedSpace ρ L v)

lemma projFixedSpace_eq_self [Fact p.Prime] {ρ : Representation (ZMod p) K V} {L : Subgroup K}
    (hL : (Nat.card L : ZMod p) ≠ 0) {v : V} (hv : v ∈ fixedSpace ρ L) :
    projFixedSpace ρ L v = v := by
  rw [projFixedSpace_apply, sumOver_apply_of_mem_fixedSpace hv, smul_smul, inv_mul_cancel₀ hL,
    one_smul]

lemma projFixedSpace_eq_zero_of_sup_eq_top [IsMulCommutative K]
    {ρ : Representation (ZMod p) K V} {L L' : Subgroup K} (hsup : L ⊔ L' = ⊤)
    (hV : ρ.invariants = ⊥) {v : V} (hv : v ∈ fixedSpace ρ L') :
    projFixedSpace ρ L v = 0 := by
  have hmem' : sumOver ρ L v ∈ fixedSpace ρ L' := by
    intro x hx
    rw [sumOver_apply, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : x * y = y * x := isMulCommutative_iff.1 inferInstance x y
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hv x hx]
  have hmem : sumOver ρ L v ∈ fixedSpace ρ (L ⊔ L') :=
    (fixedSpace_sup ρ L L').ge ⟨sumOver_apply_mem_fixedSpace ρ L v, hmem'⟩
  rw [hsup, fixedSpace_top, hV, Submodule.mem_bot] at hmem
  rw [projFixedSpace_apply, hmem, smul_zero]

end Averaging

lemma fixedSpace_eq_invariants_comp_subtype (ρ : Representation (ZMod p) K V) (L : Subgroup K) :
    fixedSpace ρ L = Representation.invariants (ρ.comp L.subtype) := by
  ext v
  simp only [mem_fixedSpace, Representation.mem_invariants, MonoidHom.coe_comp,
    Function.comp_apply]
  exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

lemma baseChange_fixedSpace [Fact p.Prime] [Finite K] (F : Type*) [Field F] [Algebra (ZMod p) F]
    (ρ : Representation (ZMod p) K V) (L : Subgroup K) :
    (fixedSpace ρ L).baseChange F
      = Representation.invariants ((Representation.baseChange F ρ).comp L.subtype) := by
  rw [fixedSpace_eq_invariants_comp_subtype, ← Representation.invariants_baseChange,
    Representation.baseChange_comp]

lemma index_ker_eq_of_ne_one {F : Type*} [Field F] [Finite K] (hq : q.Prime)
    (hexp : ∀ x : K, x ^ q = 1) {χ : K →* Fˣ} (hχ : χ ≠ 1) :
    (MonoidHom.ker χ).index = q := by
  have hfin : Finite χ.range := Finite.of_surjective _ χ.rangeRestrict_surjective
  have hcyc : IsCyclic χ.range := isCyclic_subgroup_units _
  have hdvd : Monoid.exponent χ.range ∣ q := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    obtain ⟨x, hx⟩ := g.2
    have h1 : (g : Fˣ) ^ q = 1 := by rw [← hx, ← map_pow, hexp x, map_one]
    exact Subtype.ext (by exact_mod_cast h1)
  obtain ⟨x, hx⟩ : ∃ x : K, χ x ≠ 1 := by
    by_contra h
    exact hχ (MonoidHom.ext fun x => not_ne_iff.1 fun hh => h ⟨x, hh⟩)
  have hord : orderOf (⟨χ x, ⟨x, rfl⟩⟩ : χ.range) = q := by
    refine (hq.eq_one_or_self_of_dvd _ ?_).resolve_left ?_
    · exact orderOf_dvd_of_pow_eq_one
        (Subtype.ext (by push_cast; rw [← map_pow, hexp x, map_one]))
    · intro h
      exact hx (by simpa using Subtype.ext_iff.1 (orderOf_eq_one_iff.1 h))
  rw [Subgroup.index_ker, ← IsCyclic.exponent_eq_card]
  exact Nat.dvd_antisymm hdvd (hord ▸ Monoid.order_dvd_exponent _)

section Recovery

variable {ρ : Representation (ZMod p) K V} (hq : q.Prime) (hV : ρ.invariants = ⊥)

include hq hV

theorem actionKernel_fixedSpace_of_index_eq {L : Subgroup K} (hL : L.index = q)
    (hne : fixedSpace ρ L ≠ ⊥) : actionKernel ρ (fixedSpace ρ L) = L := by
  refine le_antisymm (fun x hx => ?_) (le_actionKernel_fixedSpace ρ L)
  by_contra hxL
  refine hne (le_bot_iff.1 fun v hv => ?_)
  have hzp : v ∈ fixedSpace ρ (Subgroup.zpowers x) :=
    mem_fixedSpace_zpowers (mem_actionKernel.1 hx v hv)
  have hmem : v ∈ fixedSpace ρ (L ⊔ Subgroup.zpowers x) :=
    (fixedSpace_sup ρ L _).ge ⟨hv, hzp⟩
  rwa [sup_zpowers_eq_top_of_index_eq hq hL hxL, fixedSpace_top, hV] at hmem

theorem injOn_fixedSpace_hyperplane :
    Set.InjOn (fun L : Subgroup K => fixedSpace ρ L)
      {L : Subgroup K | L.index = q ∧ fixedSpace ρ L ≠ ⊥} := by
  rintro L ⟨hL, hLne⟩ L' ⟨hL', hL'ne⟩ (h : fixedSpace ρ L = fixedSpace ρ L')
  rw [← actionKernel_fixedSpace_of_index_eq hq hV hL hLne,
    ← actionKernel_fixedSpace_of_index_eq hq hV hL' hL'ne, h]

end Recovery

section Decomposition

variable [Finite K] [IsMulCommutative K] [Fact p.Prime] {ρ : Representation (ZMod p) K V}
  (hq : q.Prime) (hqp : q ≠ p) (hK : IsPGroup q K) (hV : ρ.invariants = ⊥)

include hq hqp hK

omit [IsMulCommutative K] in
lemma natCard_ne_zero_zmod (L : Subgroup K) : (Nat.card L : ZMod p) ≠ 0 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hK.to_subgroup L)
  rw [hn]
  intro h
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ q ^ n := (ZMod.natCast_eq_zero_iff _ _).1 h
  exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd)).symm

include hV

theorem iSupIndep_fixedSpace_hyperplane :
    iSupIndep fun L : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥} =>
      fixedSpace ρ L.1 := by
  intro L
  rw [disjoint_iff, ← le_bot_iff]
  rintro v ⟨hv, hv'⟩
  have hkill : (⨆ (L' : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥}) (_ : L' ≠ L),
      fixedSpace ρ L'.1) ≤ LinearMap.ker (projFixedSpace ρ L.1) := by
    refine iSup_le fun L' => iSup_le fun hL' => fun w hw => ?_
    have hne : L.1 ≠ L'.1 := fun h => hL' (Subtype.ext h.symm)
    exact projFixedSpace_eq_zero_of_sup_eq_top
      (sup_eq_top_of_index_eq hq L.2.1 L'.2.1 hne) hV hw
  have h1 : projFixedSpace ρ L.1 v = 0 := hkill hv'
  have h2 : projFixedSpace ρ L.1 v = v :=
    projFixedSpace_eq_self (natCard_ne_zero_zmod hq hqp hK L.1) hv
  rw [Submodule.mem_bot, ← h2, h1]

variable [FiniteDimensional (ZMod p) V] (hexp : ∀ x : K, x ^ q = 1)

include hexp

theorem iSup_fixedSpace_hyperplane_eq_top :
    (⨆ L : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥}, fixedSpace ρ L.1) = ⊤ := by
  let _ : CommGroup K := IsMulCommutative.instCommGroup
  set F := AlgebraicClosure (ZMod p) with hF
  set σ := Representation.baseChange F ρ with hσ
  set W := ⨆ L : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥}, fixedSpace ρ L.1 with hW
  have hcardK : (Nat.card K : ZMod p) ≠ 0 := by
    have h := natCard_ne_zero_zmod hq hqp hK (⊤ : Subgroup K)
    rwa [Subgroup.card_top] at h
  have hcard : (Nat.card K : F) ≠ 0 :=
    Representation.natCard_ne_zero_of_baseField (G := K) F hcardK
  have htop : W.baseChange F = ⊤ := by
    refine top_unique ?_
    rw [← Representation.iSup_characterSpace_eq_top σ hcard]
    refine iSup_le fun χ => ?_
    rcases eq_or_ne (Representation.characterSpace σ χ) ⊥ with h | h
    · rw [h]; exact bot_le
    have hχ : χ ≠ 1 := by
      rintro rfl
      refine h ?_
      have hone : Representation.characterSpace σ (1 : K →* Fˣ) = σ.invariants := by
        ext v
        rw [Representation.mem_characterSpace_iff, Representation.mem_invariants]
        simp
      rw [hone, hσ, Representation.invariants_baseChange, hV, Submodule.baseChange_bot]
    have hLind : (MonoidHom.ker χ).index = q := index_ker_eq_of_ne_one hq hexp hχ
    have hle : Representation.characterSpace σ χ
        ≤ (fixedSpace ρ (MonoidHom.ker χ)).baseChange F := by
      rw [baseChange_fixedSpace]
      intro v hv
      rw [Representation.mem_invariants]
      intro x
      have h2 := (Representation.mem_characterSpace_iff (ρ := σ)).1 hv x.1
      change σ (x : K) v = v
      rw [h2, MonoidHom.mem_ker.1 x.2]
      simp
    have hne : fixedSpace ρ (MonoidHom.ker χ) ≠ ⊥ := by
      intro h0
      rw [h0, Submodule.baseChange_bot] at hle
      exact h (le_bot_iff.1 hle)
    exact hle.trans (Submodule.baseChange_mono _
      (le_iSup (fun L' : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥} => fixedSpace ρ L'.1)
        ⟨MonoidHom.ker χ, hLind, hne⟩))
  exact Submodule.baseChange_injective (htop.trans (Submodule.baseChange_top F).symm)

theorem directSum_fixedSpace_hyperplane
    [DecidableEq {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥}] :
    DirectSum.IsInternal fun L : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥} =>
      fixedSpace ρ L.1 :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_fixedSpace_hyperplane hq hqp hK hV,
      iSup_fixedSpace_hyperplane_eq_top hq hqp hK hV hexp⟩

theorem hyperplaneDecomposition
    [DecidableEq {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥}] :
    (DirectSum.IsInternal fun L : {L : Subgroup K // L.index = q ∧ fixedSpace ρ L ≠ ⊥} =>
        fixedSpace ρ L.1) ∧
      Set.InjOn (fun L : Subgroup K => fixedSpace ρ L)
        {L : Subgroup K | L.index = q ∧ fixedSpace ρ L ≠ ⊥} ∧
      ∀ L : Subgroup K, L.index = q → fixedSpace ρ L ≠ ⊥ →
        actionKernel ρ (fixedSpace ρ L) = L :=
  ⟨directSum_fixedSpace_hyperplane hq hqp hK hV hexp, injOn_fixedSpace_hyperplane hq hV,
    fun _ hL hne => actionKernel_fixedSpace_of_index_eq hq hV hL hne⟩

end Decomposition

end

end CFSG.FeitThompson

