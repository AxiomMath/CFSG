module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

universe u v w

section Generic

variable {H : Type u} {E : Type v} {G : Type*} [Group H] [Group E] [Group G] {π : E →* G}

theorem eq_of_comp_eq_of_isPerfect [Group.IsPerfect H] (hcen : π.ker ≤ Subgroup.center E)
    {β₁ β₂ : H →* E} (h : π.comp β₁ = π.comp β₂) : β₁ = β₂ := by
  have hmem : ∀ x, β₁ x * (β₂ x)⁻¹ ∈ Subgroup.center E := fun x => hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply,
      mul_inv_cancel])
  let γ : H →* Subgroup.center E :=
    { toFun := fun x => ⟨β₁ x * (β₂ x)⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.1 (hmem y)
        change β₁ (x * y) * (β₂ (x * y))⁻¹ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc β₁ x * β₁ y * ((β₂ y)⁻¹ * (β₂ x)⁻¹)
            = β₁ x * ((β₁ y * (β₂ y)⁻¹) * (β₂ x)⁻¹) := by group
          _ = β₁ x * ((β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)) := by rw [← hc]
          _ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹) := by group) }
  have hγ : ∀ x, γ x = 1 := by
    intro x
    have hx : x ∈ commutator H := by
      rw [Group.IsPerfect.commutator_eq_top]
      trivial
    exact Abelianization.commutator_subset_ker γ hx
  ext x
  have := congrArg Subtype.val (hγ x)
  simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
  exact mul_inv_eq_one.1 this

open _root_.Classical in
noncomputable def perfectLift (π : E →* G) (α : H →* G) : H →* E :=
  if h : ∃ β : H →* E, π.comp β = α then h.choose else 1

theorem comp_perfectLift_of_exists {α : H →* G} (h : ∃ β : H →* E, π.comp β = α) :
    π.comp (perfectLift π α) = α := by
  classical
  rw [perfectLift, dite_eq_left h]
  exact h.choose_spec

variable [Finite H] [Finite E]

theorem exists_lift_of_forall_section
    (hsplit : ∀ (R : Type (max u v)) [Group R] [Finite R] (ρ : R →* H),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center R → IsPGroup 2 ρ.ker →
        ∃ s : H →* R, ∀ x, ρ (s x) = x)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : H →* G) : ∃ β : H →* E, π.comp β = α := by
  obtain ⟨s, hs⟩ := hsplit _ (pullbackFst α π) (pullbackFst_surjective hπ)
    (ker_pullbackFst_le_center hcen) (isPGroup_ker_pullbackFst h2)
  refine ⟨(MonoidHom.snd H E).comp ((pullback α π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : pullback α π) : H × E).1 = x := hs x
  have h2' := mem_pullback.1 (s x).2
  rw [h1] at h2'
  exact h2'.symm

variable (hsplit : ∀ (R : Type (max u v)) [Group R] [Finite R] (ρ : R →* H),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center R → IsPGroup 2 ρ.ker →
        ∃ s : H →* R, ∀ x, ρ (s x) = x)
  (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
include hsplit hπ hcen h2

theorem comp_perfectLift (α : H →* G) : π.comp (perfectLift π α) = α :=
  comp_perfectLift_of_exists (exists_lift_of_forall_section hsplit hπ hcen h2 α)

theorem map_perfectLift (α : H →* G) (x : H) : π (perfectLift π α x) = α x :=
  DFunLike.congr_fun (comp_perfectLift hsplit hπ hcen h2 α) x

omit [Finite H] [Finite E] hsplit hπ h2 in
theorem eq_perfectLift [Group.IsPerfect H] {α : H →* G} {β : H →* E} (hβ : π.comp β = α) :
    β = perfectLift π α :=
  eq_of_comp_eq_of_isPerfect hcen (hβ.trans (comp_perfectLift_of_exists ⟨β, hβ⟩).symm)

theorem existsUnique_lift_of_isPerfect [Group.IsPerfect H] (α : H →* G) :
    ∃! β : H →* E, π.comp β = α :=
  ⟨perfectLift π α, comp_perfectLift hsplit hπ hcen h2 α, fun _ hβ => eq_perfectLift hcen hβ⟩

theorem perfectLift_injective {α : H →* G} (hα : Function.Injective α) :
    Function.Injective (perfectLift π α) := by
  intro x y h
  apply hα
  rw [← map_perfectLift hsplit hπ hcen h2 α, ← map_perfectLift hsplit hπ hcen h2 α, h]

theorem perfectLift_conj [Group.IsPerfect H] (α : H →* G) (e : E) :
    (MulAut.conj e).toMonoidHom.comp (perfectLift π α) =
      perfectLift π ((MulAut.conj (π e)).toMonoidHom.comp α) := by
  apply eq_perfectLift hcen
  ext x
  simp [map_perfectLift hsplit hπ hcen h2 α x]

theorem perfectLift_comp {H' : Type*} [Group H'] [Group.IsPerfect H'] (α : H →* G)
    (β : H' →* H) : (perfectLift π α).comp β = perfectLift π (α.comp β) := by
  have h : π.comp ((perfectLift π α).comp β) = α.comp β := by
    rw [← MonoidHom.comp_assoc, comp_perfectLift hsplit hπ hcen h2 α]
  exact eq_of_comp_eq_of_isPerfect hcen (h.trans (comp_perfectLift_of_exists ⟨_, h⟩).symm)

theorem commute_perfectLift [Group.IsPerfect H] {H' : Type*} [Group H'] [Group.IsPerfect H']
    (α : H →* G) {α' : H' →* G} {β' : H' →* E} (hβ' : π.comp β' = α')
    (hαα' : ∀ x x', Commute (α x) (α' x')) (x : H) (x' : H') :
    Commute (perfectLift π α x) (β' x') := by
  have h : π.comp ((MulAut.conj (perfectLift π α x)).toMonoidHom.comp β') = α' := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, map_perfectLift hsplit hπ hcen h2 α x]
    rw [← MonoidHom.comp_apply π β', hβ', (hαα' x y).eq, mul_inv_cancel_right]
  have h' := DFunLike.congr_fun (eq_of_comp_eq_of_isPerfect hcen (h.trans hβ'.symm)) x'
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
  exact (mul_inv_eq_iff_eq_mul.1 h')

end Generic

section Extension

variable {H : Type u} {R : Type v} [Group H] [Group R] {ρ : R →* H}

theorem ker_eq_bot_of_closure_odd (hcen : ρ.ker ≤ Subgroup.center R) (h2 : IsPGroup 2 ρ.ker)
    {s : H →* R} (hs : ∀ x, ρ (s x) = x)
    (hodd : Subgroup.closure {r : R | Odd (orderOf r)} = ⊤) : ρ.ker = ⊥ := by
  have hrange : ∀ r : R, Odd (orderOf r) → r ∈ s.range := by
    intro r hr
    set c := r * (s (ρ r))⁻¹
    have hc : c ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
    have hcc : Commute c (s (ρ r)) := (Subgroup.mem_center_iff.1 (hcen hc) _).symm
    have hrc : r = c * s (ρ r) := by rw [inv_mul_cancel_right]
    have hcm : c ^ orderOf r = 1 := by
      have h1 : r ^ orderOf r = c ^ orderOf r * s (ρ r) ^ orderOf r := by
        rw [hrc, hcc.mul_pow, ← hrc]
      rw [pow_orderOf_eq_one, ← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one,
        mul_one] at h1
      exact h1.symm
    obtain ⟨k, hk⟩ := h2 ⟨c, hc⟩
    have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hc1 : c = 1 := by
      have hd1 := orderOf_dvd_of_pow_eq_one hcm
      have hd2 := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf r) (2 ^ k) := (Nat.coprime_two_right.2 hr).pow_right k
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    rw [hrc, hc1, one_mul]
    exact ⟨_, rfl⟩
  have htop : s.range = ⊤ := by
    rw [eq_top_iff, ← hodd, Subgroup.closure_le]
    exact hrange
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨x, rfl⟩ : c ∈ s.range := by rw [htop]; trivial
  rw [MonoidHom.mem_ker, hs] at hc
  rw [hc, map_one]
  exact Subgroup.one_mem _

end Extension

end CFSG.LieType.Steinberg
