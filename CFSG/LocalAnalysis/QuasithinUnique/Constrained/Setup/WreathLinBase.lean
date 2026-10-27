module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem iSup_comm_of_pairwise {ι : Type*} (A : ι → Subgroup G)
    (hcomm : ∀ i j, ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) :
    ∀ x ∈ ⨆ i, A i, ∀ y ∈ ⨆ i, A i, x * y = y * x := by
  have h1 : ∀ i, ∀ a ∈ A i, ∀ y ∈ ⨆ i, A i, a * y = y * a := by
    intro i a ha y hy
    refine Subgroup.iSup_induction A (C := fun y => a * y = y * a) hy ?_ ?_ ?_
    · intro j y' hy'
      exact hcomm i j a ha y' hy'
    · simp
    · intro y y' hy hy'
      calc a * (y * y') = (a * y) * y' := (mul_assoc _ _ _).symm
        _ = (y * a) * y' := by rw [hy]
        _ = y * (a * y') := mul_assoc _ _ _
        _ = y * (y' * a) := by rw [hy']
        _ = y * y' * a := (mul_assoc _ _ _).symm
  intro x hx y hy
  refine Subgroup.iSup_induction A (C := fun x => x * y = y * x) hx ?_ ?_ ?_
  · intro i a ha
    exact h1 i a ha y hy
  · simp
  · intro x x' hx hx'
    calc x * x' * y = x * (x' * y) := mul_assoc _ _ _
      _ = x * (y * x') := by rw [hx']
      _ = (x * y) * x' := (mul_assoc _ _ _).symm
      _ = (y * x) * x' := by rw [hx]
      _ = y * (x * x') := mul_assoc _ _ _

theorem iSup_sq_eq_one {ι : Type*} (A : ι → Subgroup G)
    (hcomm : ∀ i j, ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (hsq : ∀ i, ∀ a ∈ A i, a * a = 1) : ∀ x ∈ ⨆ i, A i, x * x = 1 := by
  intro x hx
  refine (Subgroup.iSup_induction A
    (C := fun x => x ∈ (⨆ i, A i : Subgroup G) ∧ x * x = 1) hx ?_ ?_ ?_).2
  · intro i a ha
    exact ⟨Subgroup.mem_iSup_of_mem i ha, hsq i a ha⟩
  · exact ⟨one_mem _, by simp⟩
  · rintro x y ⟨hxm, hx⟩ ⟨hym, hy⟩
    refine ⟨mul_mem hxm hym, ?_⟩
    have hc := iSup_comm_of_pairwise A hcomm x hxm y hym
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]

theorem isPGroup_two_iSup {ι : Type*} (A : ι → Subgroup G)
    (hcomm : ∀ i j, ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (hsq : ∀ i, ∀ a ∈ A i, a * a = 1) : IsPGroup 2 ↥(⨆ i, A i) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have := iSup_sq_eq_one A hcomm hsq x x.2
  simpa [pow_two] using this

theorem eq_one_of_two_pow_of_odd_card {M : Subgroup G} (hM : Odd (Nat.card M)) {x : G}
    (hxM : x ∈ M) (h2 : ∃ n : ℕ, x ^ 2 ^ n = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := h2
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2' : orderOf x ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hxM
  have hcop : Nat.Coprime (2 ^ n) (Nat.card M) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hM)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2')

theorem two_dvd_card_of_elem {A : Subgroup G} (hel : CFSG.IsElementaryAbelian 2 ↥A)
    (hne : A ≠ ⊥) : 2 ∣ Nat.card ↥A := by
  rcases (CFSG.IsElementaryAbelian.isPGroup 2 A).card_eq_or_dvd with h1 | h1
  · exact absurd (Subgroup.card_eq_one.1 h1) hne
  · exact h1

end Group

section Acts

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V] {ι : Type*}

@[expose] def ActsAs (I : ι → Submodule k V) (x : V ≃ₗ[k] V) (σ : Equiv.Perm ι) : Prop :=
  ∀ i, ∀ v : V, x v ∈ I (σ i) ↔ v ∈ I i

theorem ActsAs.one (I : ι → Submodule k V) : ActsAs I 1 1 := fun _ _ => Iff.rfl

theorem ActsAs.mul {I : ι → Submodule k V} {x y : V ≃ₗ[k] V} {σ τ : Equiv.Perm ι}
    (hx : ActsAs I x σ) (hy : ActsAs I y τ) : ActsAs I (x * y) (σ * τ) :=
  fun i v => (hx (τ i) (y v)).trans (hy i v)

theorem ActsAs.inv {I : ι → Submodule k V} {x : V ≃ₗ[k] V} {σ : Equiv.Perm ι}
    (hx : ActsAs I x σ) : ActsAs I x⁻¹ σ⁻¹ := by
  intro i v
  have h := hx (σ⁻¹ i) (x⁻¹ v)
  have e1 : σ (σ⁻¹ i) = i := σ.apply_symm_apply i
  rw [e1, gl_apply_inv] at h
  exact h.symm

theorem ActsAs.pow {I : ι → Submodule k V} {x : V ≃ₗ[k] V} {σ : Equiv.Perm ι}
    (hx : ActsAs I x σ) (n : ℕ) : ActsAs I (x ^ n) (σ ^ n) := by
  induction n with
  | zero => simpa using ActsAs.one I
  | succ n ih => simpa [pow_succ] using ih.mul hx

theorem ActsAs.unique {I : ι → Submodule k V} (hI : Function.Injective I) {x : V ≃ₗ[k] V}
    {σ τ : Equiv.Perm ι} (hσ : ActsAs I x σ) (hτ : ActsAs I x τ) : σ = τ := by
  apply Equiv.ext
  intro i
  apply hI
  ext v
  have h1 := hσ i (x⁻¹ v)
  have h2 := hτ i (x⁻¹ v)
  rw [gl_apply_inv] at h1 h2
  exact h1.trans h2.symm

theorem map_eq_iff {x : V ≃ₗ[k] V} {U U' : Submodule k V} :
    U.map (x : V →ₗ[k] V) = U' ↔ ∀ v, x v ∈ U' ↔ v ∈ U := by
  constructor
  · intro h v
    rw [← h]
    constructor
    · intro hv
      obtain ⟨u, hu, hux⟩ := hv
      have : u = v := x.injective hux
      exact this ▸ hu
    · intro hv
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨x⁻¹ v, ?_, gl_apply_inv x v⟩
      have := h (x⁻¹ v)
      rw [gl_apply_inv] at this
      exact this.1 hv

theorem actsAs_iff_map {I : ι → Submodule k V} {x : V ≃ₗ[k] V} {σ : Equiv.Perm ι} :
    ActsAs I x σ ↔ ∀ i, (I i).map (x : V →ₗ[k] V) = I (σ i) :=
  ⟨fun h i => map_eq_iff.2 (h i), fun h i => map_eq_iff.1 (h i)⟩

theorem exists_actsAs [Finite ι] {I : ι → Submodule k V} (hI : Function.Injective I)
    {x : V ≃ₗ[k] V} (h : ∀ i, ∃ j, (I i).map (x : V →ₗ[k] V) = I j) :
    ∃ σ : Equiv.Perm ι, ActsAs I x σ := by
  choose σ hσ using h
  have hinj : Function.Injective σ := by
    intro i j hij
    apply hI
    have h1 : (I i).map (x : V →ₗ[k] V) = (I j).map (x : V →ₗ[k] V) := by
      rw [hσ i, hσ j, hij]
    ext v
    constructor
    · intro hv
      have h2 : x v ∈ (I i).map (x : V →ₗ[k] V) := ⟨v, hv, rfl⟩
      rw [h1] at h2
      obtain ⟨u, hu, hux⟩ := h2
      exact (x.injective hux) ▸ hu
    · intro hv
      have h2 : x v ∈ (I j).map (x : V →ₗ[k] V) := ⟨v, hv, rfl⟩
      rw [← h1] at h2
      obtain ⟨u, hu, hux⟩ := h2
      exact (x.injective hux) ▸ hu
  refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj), ?_⟩
  exact actsAs_iff_map.2 hσ

end Acts

end CFSG.QuasithinUnique.Setup.Wreath
