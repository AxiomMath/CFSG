module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs

public section

open scoped Pointwise

namespace CFSG

variable {A B α β : Type*}

section Orbit

variable [Group A] [Group B] [MulAction A α] [MulAction B β]

noncomputable abbrev orbitMapOfStabilizerMap (e : A ≃* B) (a : α) (b : β) :
    ↥(MulAction.orbit A a) → ↥(MulAction.orbit B b) :=
  fun x => ⟨e (Classical.choose x.2) • b, MulAction.mem_orbit b _⟩

noncomputable abbrev orbitMapInvOfStabilizerMap (e : A ≃* B) (a : α) (b : β) :
    ↥(MulAction.orbit B b) → ↥(MulAction.orbit A a) :=
  fun y => ⟨e.symm (Classical.choose y.2) • a, MulAction.mem_orbit a _⟩

theorem orbitMapOfStabilizerMap_eq (e : A ≃* B) (a : α) (b : β)
    (h : (MulAction.stabilizer A a).map e.toMonoidHom = MulAction.stabilizer B b)
    {g : A} (x : ↥(MulAction.orbit A a)) (hg : g • a = (x : α)) :
    (orbitMapOfStabilizerMap e a b x : β) = e g • b := by
  have hg₀ : Classical.choose x.2 • a = (x : α) := Classical.choose_spec x.2
  have hc : Classical.choose x.2 • a = g • a := hg₀.trans hg.symm
  have hmem : (Classical.choose x.2)⁻¹ * g ∈ MulAction.stabilizer A a := by
    rw [MulAction.mem_stabilizer_iff]
    show ((Classical.choose x.2)⁻¹ * g) • a = a
    rw [mul_smul, ← hc, inv_smul_smul]
  have hmemB : e ((Classical.choose x.2)⁻¹ * g) ∈ MulAction.stabilizer B b := by
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hmem
  have hb : ((e (Classical.choose x.2))⁻¹ * e g) • b = b := by
    simpa using MulAction.mem_stabilizer_iff.mp hmemB
  have hcancel : e g • b = e (Classical.choose x.2) • b := by
    have := congrArg (fun z => (e (Classical.choose x.2)) • z) hb
    simpa [mul_smul] using this
  simpa using hcancel.symm

theorem orbitMapInv_leftInverse (e : A ≃* B) (a : α) (b : β)
    (h : (MulAction.stabilizer A a).map e.toMonoidHom = MulAction.stabilizer B b) :
    Function.LeftInverse (orbitMapInvOfStabilizerMap e a b) (orbitMapOfStabilizerMap e a b) := by
  intro x
  apply Subtype.ext
  show e.symm (Classical.choose (orbitMapOfStabilizerMap e a b x).2) • a = (x : α)
  have hg₀ : Classical.choose x.2 • a = (x : α) := Classical.choose_spec x.2
  set k := Classical.choose (orbitMapOfStabilizerMap e a b x).2 with hkdef
  have hk : k • b = e (Classical.choose x.2) • b :=
    Classical.choose_spec (orbitMapOfStabilizerMap e a b x).2
  have hmemB : k⁻¹ * e (Classical.choose x.2) ∈ MulAction.stabilizer B b := by
    rw [MulAction.mem_stabilizer_iff]
    show (k⁻¹ * e (Classical.choose x.2)) • b = b
    rw [mul_smul, ← hk, inv_smul_smul]
  have hmemA : e.symm (k⁻¹ * e (Classical.choose x.2)) ∈ MulAction.stabilizer A a := by
    have hy : k⁻¹ * e (Classical.choose x.2) ∈
        (MulAction.stabilizer A a).map e.toMonoidHom := h ▸ hmemB
    exact (Subgroup.mem_map_equiv (f := e) (K := MulAction.stabilizer A a)).mp hy
  have hfix : ((e.symm k)⁻¹ * Classical.choose x.2) • a = a := by
    simpa using MulAction.mem_stabilizer_iff.mp hmemA
  have hkey : e.symm k • a = Classical.choose x.2 • a := by
    have := congrArg (fun z => (e.symm k) • z) hfix
    simpa [mul_smul] using this.symm
  exact hkey.trans hg₀

theorem orbitMapInv_rightInverse (e : A ≃* B) (a : α) (b : β)
    (h : (MulAction.stabilizer A a).map e.toMonoidHom = MulAction.stabilizer B b) :
    Function.RightInverse (orbitMapInvOfStabilizerMap e a b) (orbitMapOfStabilizerMap e a b) := by
  intro y
  apply Subtype.ext
  show e (Classical.choose (orbitMapInvOfStabilizerMap e a b y).2) • b = (y : β)
  have hk₀ : Classical.choose y.2 • b = (y : β) := Classical.choose_spec y.2
  set k := Classical.choose (orbitMapInvOfStabilizerMap e a b y).2 with hkdef
  have hk : k • a = e.symm (Classical.choose y.2) • a :=
    Classical.choose_spec (orbitMapInvOfStabilizerMap e a b y).2
  have hmemA : k⁻¹ * e.symm (Classical.choose y.2) ∈ MulAction.stabilizer A a := by
    rw [MulAction.mem_stabilizer_iff]
    show (k⁻¹ * e.symm (Classical.choose y.2)) • a = a
    rw [mul_smul, ← hk, inv_smul_smul]
  have hmemB : e (k⁻¹ * e.symm (Classical.choose y.2)) ∈ MulAction.stabilizer B b := by
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hmemA
  have hfix : ((e k)⁻¹ * Classical.choose y.2) • b = b := by
    simpa using MulAction.mem_stabilizer_iff.mp hmemB
  have hkey : Classical.choose y.2 • b = e k • b := by
    have := congrArg (fun z => (e k) • z) hfix
    simpa [mul_smul] using this
  exact hkey.symm.trans hk₀

@[expose]
noncomputable def orbitEquivOfStabilizerMap (e : A ≃* B) (a : α) (b : β)
    (h : (MulAction.stabilizer A a).map e.toMonoidHom = MulAction.stabilizer B b) :
    ↥(MulAction.orbit A a) ≃ ↥(MulAction.orbit B b) where
  toFun := orbitMapOfStabilizerMap e a b
  invFun := orbitMapInvOfStabilizerMap e a b
  left_inv := orbitMapInv_leftInverse e a b h
  right_inv := orbitMapInv_rightInverse e a b h

theorem orbitEquivOfStabilizerMap_self (e : A ≃* B) (a : α) (b : β)
    (h : (MulAction.stabilizer A a).map e.toMonoidHom = MulAction.stabilizer B b) :
    orbitEquivOfStabilizerMap e a b h ⟨a, MulAction.mem_orbit_self a⟩ =
      ⟨b, MulAction.mem_orbit_self b⟩ := by
  apply Subtype.ext
  show e (Classical.choose ((MulAction.mem_orbit_self a) : a ∈ MulAction.orbit A a)) • b = b
  have hg : Classical.choose ((MulAction.mem_orbit_self a) : a ∈ MulAction.orbit A a) • a = a :=
    Classical.choose_spec ((MulAction.mem_orbit_self a) : a ∈ MulAction.orbit A a)
  have hmem : Classical.choose ((MulAction.mem_orbit_self a) : a ∈ MulAction.orbit A a) ∈
      MulAction.stabilizer A a := MulAction.mem_stabilizer_iff.mpr hg
  have hmemB : e (Classical.choose ((MulAction.mem_orbit_self a) : a ∈ MulAction.orbit A a)) ∈
      MulAction.stabilizer B b := by
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hmem
  exact MulAction.mem_stabilizer_iff.mp hmemB

theorem orbitEquivOfStabilizerMap_smul (e : A ≃* B) (a : α) (b : β)
    (h : (MulAction.stabilizer A a).map e.toMonoidHom = MulAction.stabilizer B b)
    (g : A) (x : ↥(MulAction.orbit A a)) :
    orbitEquivOfStabilizerMap e a b h (g • x) =
      e g • orbitEquivOfStabilizerMap e a b h x := by
  apply Subtype.ext
  have hg₀ : Classical.choose x.2 • a = (x : α) := Classical.choose_spec x.2
  have hrep : (g * Classical.choose x.2) • a = ((g • x : ↥(MulAction.orbit A a)) : α) := by
    rw [show ((g • x : ↥(MulAction.orbit A a)) : α) = g • (x : α) from rfl, mul_smul, hg₀]
  have h1 : ((orbitEquivOfStabilizerMap e a b h (g • x) : ↥(MulAction.orbit B b)) : β) =
      e (g * Classical.choose x.2) • b :=
    orbitMapOfStabilizerMap_eq e a b h (g • x) hrep
  have h2 : ((orbitEquivOfStabilizerMap e a b h x : ↥(MulAction.orbit B b)) : β) =
      e (Classical.choose x.2) • b := rfl
  change ((orbitEquivOfStabilizerMap e a b h (g • x) : ↥(MulAction.orbit B b)) : β) =
    e g • ((orbitEquivOfStabilizerMap e a b h x : ↥(MulAction.orbit B b)) : β)
  rw [h1, h2, map_mul, mul_smul]

end Orbit
section EquivariantOnOrbit

variable [Group A] [Group B] [MulAction A α] [MulAction B β]

theorem image_orbit_of_map_eq (e : A ≃* B) (Φ : α → β) {a y : α} {K : Subgroup A}
    {L : Subgroup B} (hKL : K.map e.toMonoidHom = L)
    (hΦ : ∀ (g : A) {x : α}, x ∈ MulAction.orbit A a → Φ (g • x) = e g • Φ x)
    (hinj : Set.InjOn Φ (MulAction.orbit A a)) (hy : y ∈ MulAction.orbit A a) :
    Φ '' (MulAction.orbit ↥K y) = MulAction.orbit ↥L (Φ y) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k : ↥K, k • y = x := hx
    have hkA : (k : A) • y = x := by rw [← Subgroup.smul_def]; exact hk
    have hkL : e (k : A) ∈ L := hKL ▸ Subgroup.mem_map_of_mem e.toMonoidHom k.2
    have hsmul : (⟨e (k : A), hkL⟩ : ↥L) • Φ y = Φ x := by
      rw [Subgroup.smul_def (S := L), ← hkA]
      exact (hΦ (k : A) hy).symm
    rw [← hsmul]
    exact MulAction.mem_orbit (Φ y) (⟨e (k : A), hkL⟩ : ↥L)
  · rintro ⟨l, rfl⟩
    have hkK : e.symm (l : B) ∈ K := by
      have hmem : (l : B) ∈ K.map e.toMonoidHom := hKL ▸ l.2
      exact (Subgroup.mem_map_equiv (f := e) (K := K)).mp hmem
    have hsmul : l • Φ y = Φ ((e.symm (l : B)) • y) := by
      rw [Subgroup.smul_def (S := L)]
      simpa using (hΦ (e.symm (l : B)) hy).symm
    refine ⟨(⟨e.symm (l : B), hkK⟩ : ↥K) • y, MulAction.mem_orbit y _, ?_⟩
    rw [Subgroup.smul_def (S := K)]
    exact hsmul.symm

theorem map_stabilizer_eq_of_equivariantOn [Finite α] (e : A ≃* B) (Φ : α → β) (a : α)
    (hΦ : ∀ (g : A) {x : α}, x ∈ MulAction.orbit A a → Φ (g • x) = e g • Φ x)
    (hinj : Set.InjOn Φ (MulAction.orbit A a)) (S : Set α)
    (hS : S ⊆ MulAction.orbit A a) :
    (MulAction.stabilizer A S).map e.toMonoidHom = MulAction.stabilizer B (Φ '' S) := by
  ext b
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro hb
    have hsub : b • (Φ '' S) ⊆ Φ '' S := by
      rintro y ⟨v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hv
      have hx' : (e.symm b) • x ∈ S := by
        have hmem : (e.symm b) • x ∈ (e.symm b) • S := Set.smul_mem_smul_set hx
        rwa [hb] at hmem
      exact ⟨(e.symm b) • x, hx', by simpa using (hΦ (e.symm b) (hS hx))⟩
    have heq : b • (Φ '' S) = Φ '' S := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [show b • (Φ '' S) = (fun y => b • y) '' (Φ '' S) from rfl,
        Set.ncard_image_of_injective _ (fun y z h => smul_left_cancel b h)]
    exact heq
  · intro hb
    have hsub : (e.symm b) • S ⊆ S := by
      rintro y hy
      obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
      have hmem : b • Φ x ∈ Φ '' S := by
        have hsm : b • Φ x ∈ b • (Φ '' S) := Set.smul_mem_smul_set ⟨x, hx, rfl⟩
        rwa [hb] at hsm
      obtain ⟨z, hz, hzx⟩ := hmem
      have hxorb : (e.symm b) • x ∈ MulAction.orbit A a := by
        obtain ⟨h, rfl⟩ := hS hx
        simpa [mul_smul] using MulAction.mem_orbit a (e.symm b * h)
      have hzorb : z ∈ MulAction.orbit A a := hS hz
      have heq : (e.symm b) • x = z := by
        apply hinj hxorb hzorb
        rw [show Φ ((e.symm b) • x) = b • Φ x from by simpa using hΦ (e.symm b) (hS hx), hzx]
      rwa [heq]
    have heq : (e.symm b) • S = S := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [show (e.symm b) • S = (fun y => (e.symm b) • y) '' S from rfl,
        Set.ncard_image_of_injective _ (fun y z h => smul_left_cancel (e.symm b) h)]
    exact heq

end EquivariantOnOrbit

end CFSG
