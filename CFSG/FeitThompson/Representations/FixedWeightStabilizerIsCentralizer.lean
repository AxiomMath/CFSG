module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {L : Type*} [Group L] {M : Type*} [MulOneClass M]

def charInertia (N : Subgroup L) (lam : N →* M) : Subgroup L where
  carrier := {u | u ∈ normalizer (N : Set L) ∧
    ∀ m n : N, (m : L) = u⁻¹ * (n : L) * u → lam m = lam n}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    intro m n hmn
    have hn1 : a⁻¹ * (n : L) * a ∈ N := (mem_normalizer_iff''.mp ha (n : L)).mp n.2
    refine (hb' m ⟨a⁻¹ * (n : L) * a, hn1⟩ ?_).trans (ha' _ n rfl)
    rw [hmn]; group
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    intro m n hmn
    exact congrArg lam (Subtype.ext (by rw [hmn]; group))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    intro m n hmn
    exact (ha' n m (by rw [hmn]; group)).symm

theorem mem_charInertia {N : Subgroup L} {lam : N →* M} {u : L} :
    u ∈ charInertia N lam ↔ u ∈ normalizer (N : Set L) ∧
      ∀ m n : N, (m : L) = u⁻¹ * (n : L) * u → lam m = lam n := Iff.rfl

theorem charInertia_le_normalizer {N : Subgroup L} {lam : N →* M} :
    charInertia N lam ≤ normalizer (N : Set L) := fun _ hu => hu.1

theorem map_conj_eq_of_mem_charInertia {N : Subgroup L} {lam : N →* M} {u : L}
    (hu : u ∈ charInertia N lam) (n : N) (h : u⁻¹ * (n : L) * u ∈ N) :
    lam ⟨u⁻¹ * (n : L) * u, h⟩ = lam n :=
  hu.2 _ n rfl

theorem mem_charInertia_of_forall {N : Subgroup L} {lam : N →* M} {u : L}
    (hu : u ∈ normalizer (N : Set L))
    (h : ∀ (n : N) (hn : u⁻¹ * (n : L) * u ∈ N), lam ⟨u⁻¹ * (n : L) * u, hn⟩ = lam n) :
    u ∈ charInertia N lam := by
  refine ⟨hu, fun m n hmn => ?_⟩
  have hn : u⁻¹ * (n : L) * u ∈ N := hmn ▸ m.2
  exact (congrArg lam (Subtype.ext hmn : m = ⟨u⁻¹ * (n : L) * u, hn⟩)).trans (h n hn)

theorem centralizer_le_charInertia {N : Subgroup L} {lam : N →* M} :
    centralizer (N : Set L) ≤ charInertia N lam := by
  intro u hu
  refine ⟨centralizer_le_normalizer _ hu, fun m n hmn => congrArg lam (Subtype.ext ?_)⟩
  have h := mem_centralizer_iff.mp hu (n : L) n.2
  rw [hmn, mul_assoc, h, inv_mul_cancel_left]

theorem charInertia_one {N : Subgroup L} :
    charInertia N (1 : N →* M) = normalizer (N : Set L) := by
  ext u
  simp only [mem_charInertia, MonoidHom.one_apply, implies_true, and_true]

theorem inf_charInertia_eq_inf_centralizer {N A U Q : Subgroup L} [IsMulCommutative U]
    {lam : N →* M} (hlam : lam ≠ 1)
    (hAN : A ≤ normalizer (N : Set L))
    (hA : (A : Set L) = (U : Set L) * (Q : Set L))
    (hUnormal : (U.subgroupOf A).Normal)
    (hmin : ∀ K : Subgroup L, K ≤ N → A ≤ normalizer (K : Set L) → K = ⊥ ∨ K = N)
    (hQlam : ∀ q ∈ Q, ∀ (n : N) (hn : q⁻¹ * (n : L) * q ∈ N),
      lam ⟨q⁻¹ * (n : L) * q, hn⟩ = lam n) :
    U ⊓ charInertia N lam = U ⊓ centralizer (N : Set L) := by
  have hUA : U ≤ A := by
    intro u hu
    have : u ∈ (U : Set L) * (Q : Set L) := ⟨u, hu, 1, one_mem _, mul_one u⟩
    rwa [← hA] at this
  have hQA : Q ≤ A := by
    intro q hq
    have : q ∈ (U : Set L) * (Q : Set L) := ⟨1, one_mem _, q, hq, one_mul q⟩
    rwa [← hA] at this
  have hAU : A ≤ normalizer (U : Set L) :=
    (normal_subgroupOf_iff_le_normalizer hUA).mp hUnormal
  set V : Subgroup L := U ⊓ charInertia N lam
  have hQI : Q ≤ charInertia N lam := fun q hq =>
    mem_charInertia_of_forall (hAN (hQA hq)) (hQlam q hq)
  have hAV : A ≤ normalizer (V : Set L) := by
    rw [le_normalizer_iff]
    intro a ha v hv
    have hvU : v ∈ U := (mem_inf.mp hv).1
    have hvI : v ∈ charInertia N lam := (mem_inf.mp hv).2
    have ha' : a ∈ (U : Set L) * (Q : Set L) := by rwa [← hA]
    obtain ⟨u, hu, q, hq, rfl⟩ := ha'
    have hqv : q * v * q⁻¹ ∈ V :=
      mem_inf.mpr ⟨(le_normalizer_iff.mp hAU) q (hQA hq) v hvU,
        mul_mem (mul_mem (hQI hq) hvI) (inv_mem (hQI hq))⟩
    have huq : u * (q * v * q⁻¹) * u⁻¹ = q * v * q⁻¹ := by
      rw [setLike_mul_comm (s := U) hu (mem_inf.mp hqv).1]; group
    rw [show u * q * v * (u * q)⁻¹ = u * (q * v * q⁻¹) * u⁻¹ by group, huq]
    exact hqv
  have hDN : ⁅N, V⁆ ≤ N := by
    rw [commutator_le]
    intro n hn v hv
    have hvN : v ∈ normalizer (N : Set L) := charInertia_le_normalizer (mem_inf.mp hv).2
    have hw : v * n⁻¹ * v⁻¹ ∈ N := (mem_normalizer_iff.mp hvN n⁻¹).mp (inv_mem hn)
    rw [commutatorElement_def, show n * v * n⁻¹ * v⁻¹ = n * (v * n⁻¹ * v⁻¹) by group]
    exact mul_mem hn hw
  have hAD : A ≤ normalizer ((⁅N, V⁆ : Subgroup L) : Set L) := by
    intro a ha
    have h1 : N.map (MulAut.conj a : L →* L) = N := mem_normalizer_iff_map_conj_eq.mp (hAN ha)
    have h2 : V.map (MulAut.conj a : L →* L) = V := mem_normalizer_iff_map_conj_eq.mp (hAV ha)
    rw [mem_normalizer_iff_map_conj_eq, map_commutator, h1, h2]
  have hker : ⁅N, V⁆ ≤ (lam.ker).map N.subtype := by
    rw [commutator_le]
    intro n hn v hv
    have hvI : v ∈ charInertia N lam := (mem_inf.mp hv).2
    have hvN : v ∈ normalizer (N : Set L) := charInertia_le_normalizer hvI
    have hw : v * n⁻¹ * v⁻¹ ∈ N := (mem_normalizer_iff.mp hvN n⁻¹).mp (inv_mem hn)
    have hlw : lam ⟨v * n⁻¹ * v⁻¹, hw⟩ = lam (⟨n, hn⟩ : N)⁻¹ := by
      refine (mem_charInertia.mp (inv_mem hvI)).2 ⟨v * n⁻¹ * v⁻¹, hw⟩ (⟨n, hn⟩ : N)⁻¹ ?_
      change v * n⁻¹ * v⁻¹ = v⁻¹⁻¹ * (((⟨n, hn⟩ : N)⁻¹ : N) : L) * v⁻¹
      simp only [InvMemClass.coe_inv]
      group
    refine mem_map.mpr ⟨(⟨n, hn⟩ : N) * ⟨v * n⁻¹ * v⁻¹, hw⟩, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hlw, ← map_mul, mul_inv_cancel, map_one]
    · change n * (v * n⁻¹ * v⁻¹) = _
      rw [commutatorElement_def]
      group
  rcases hmin ⁅N, V⁆ hDN hAD with hD | hD
  · have hVc : V ≤ centralizer (N : Set L) := by
      rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact hD
    exact le_antisymm (le_inf inf_le_left hVc)
      (le_inf inf_le_left (inf_le_right.trans centralizer_le_charInertia))
  ·
    refine absurd (MonoidHom.ext fun x => ?_) hlam
    obtain ⟨y, hy, hyx⟩ := mem_map.mp (hker (by rw [hD]; exact x.2))
    rw [← (Subtype.ext hyx : y = x), MonoidHom.one_apply]
    exact hy

theorem setOf_fixes_eq_setOf_centralizes {N A U Q : Subgroup L} [IsMulCommutative U]
    {lam : N →* M} (hlam : lam ≠ 1)
    (hAN : A ≤ normalizer (N : Set L))
    (hA : (A : Set L) = (U : Set L) * (Q : Set L))
    (hUnormal : (U.subgroupOf A).Normal)
    (hmin : ∀ K : Subgroup L, K ≤ N → A ≤ normalizer (K : Set L) → K = ⊥ ∨ K = N)
    (hQlam : ∀ q ∈ Q, ∀ (n : N) (hn : q⁻¹ * (n : L) * q ∈ N),
      lam ⟨q⁻¹ * (n : L) * q, hn⟩ = lam n) :
    {u : L | u ∈ U ∧ ∀ (n : N) (hn : u⁻¹ * (n : L) * u ∈ N),
        lam ⟨u⁻¹ * (n : L) * u, hn⟩ = lam n}
      = {u : L | u ∈ U ∧ ∀ n ∈ N, u * n = n * u} := by
  have key := inf_charInertia_eq_inf_centralizer hlam hAN hA hUnormal hmin hQlam
  have hUA : U ≤ A := by
    intro u hu
    have : u ∈ (U : Set L) * (Q : Set L) := ⟨u, hu, 1, one_mem _, mul_one u⟩
    rwa [← hA] at this
  ext u
  constructor
  · rintro ⟨huU, hu⟩
    have hmem : u ∈ U ⊓ centralizer (N : Set L) := by
      rw [← key]
      exact mem_inf.mpr ⟨huU, mem_charInertia_of_forall (hAN (hUA huU)) hu⟩
    exact ⟨huU, fun n hn => (mem_centralizer_iff.mp (mem_inf.mp hmem).2 n hn).symm⟩
  · rintro ⟨huU, hu⟩
    have hmem : u ∈ U ⊓ charInertia N lam := by
      rw [key]
      exact mem_inf.mpr ⟨huU, mem_centralizer_iff.mpr fun n hn => (hu n hn).symm⟩
    exact ⟨huU, fun n hn => map_conj_eq_of_mem_charInertia (mem_inf.mp hmem).2 n hn⟩

end CFSG.FeitThompson
