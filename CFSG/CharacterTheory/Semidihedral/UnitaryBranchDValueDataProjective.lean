module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchProjective

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.Principal

variable (F : Type) [Field F]

theorem card_stabilizer_coordinateD [Finite F] (x : Omega F) :
    Nat.card (MulAction.stabilizer (coordinateD F) x) = Nat.card F * (Nat.card F - 1) := by
  classical
  have horbit : MulAction.orbit (coordinateD F) x = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := coordinateG_transitive F x y
    exact ⟨⟨g, coordinateG_le_D F g.2⟩, hg⟩
  have hidx : (MulAction.stabilizer (coordinateD F) x).index = Nat.card F + 1 := by
    have : Fintype F := Fintype.ofFinite F
    rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_option, ← Nat.card_eq_fintype_card]
  have h := Subgroup.card_mul_index (MulAction.stabilizer (coordinateD F) x)
  rw [hidx, card_coordinateD] at h
  have hq : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hsq : Nat.card F * (Nat.card F ^ 2 - 1) =
      Nat.card F * (Nat.card F - 1) * (Nat.card F + 1) := by
    have : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      zify [hq, hq2]
      ring
    rw [this, mul_assoc]
  rw [hsq] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega) h

theorem fixedPointFree_of_coprime [Finite F] {e : Equiv.Perm (Omega F)} (he : e ∈ coordinateD F)
    (he1 : e ≠ 1) (hcop : Nat.Coprime (orderOf e) (Nat.card F * (Nat.card F - 1)))
    (x : Omega F) : e x ≠ x := by
  intro hx
  have hstab : (⟨e, he⟩ : coordinateD F) ∈ MulAction.stabilizer (coordinateD F) x := hx
  have h1 : orderOf e ∣ Nat.card F * (Nat.card F - 1) := by
    rw [← card_stabilizer_coordinateD F x]
    have := orderOf_dvd_natCard (⟨⟨e, he⟩, hstab⟩ : MulAction.stabilizer (coordinateD F) x)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
  exact he1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h1))

theorem eq_one_of_three_fixed_points {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F)
    {x₁ x₂ x₃ : Omega F} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) (h1 : d x₁ = x₁)
    (h2 : d x₂ = x₂) (h3 : d x₃ = x₃) : d = 1 := by
  obtain ⟨g, hg, hg1, hg2⟩ := exists_coordinateG_infinity_zero (F := F) h12
  have hgD := coordinateG_le_D F hg
  have hai : ∀ y, g (g⁻¹ y) = y := fun y => by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hia : ∀ y, g⁻¹ (g y) = y := fun y => by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  set d' := g⁻¹ * d * g with hd'
  have hd'D : d' ∈ coordinateD F :=
    (coordinateD F).mul_mem ((coordinateD F).mul_mem ((coordinateD F).inv_mem hgD) hd) hgD
  have hfix : ∀ y, d y = y → d' (g⁻¹ y) = g⁻¹ y := by
    intro y hy
    rw [hd', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hai, hy]
  have hinf : d' none = none := by
    have := hfix x₁ h1
    rwa [← hg1, hia] at this
  have hzero : d' (some 0) = some 0 := by
    have := hfix x₂ h2
    rwa [← hg2, hia] at this
  obtain ⟨c, hc⟩ : ∃ c : F, g⁻¹ x₃ = some c ∧ c ≠ 0 := by
    cases h : g⁻¹ x₃ with
    | none =>
      exfalso
      apply h13
      rw [← hg1, ← h, hai]
    | some c =>
      refine ⟨c, rfl, ?_⟩
      rintro rfl
      apply h23
      rw [← hg2, ← h, hai]
  have h3' := hfix x₃ h3
  rw [hc.1] at h3'
  rcases eq_multiplier_or_of_preserves F hd'D (Or.inl ⟨hinf, hzero⟩) with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
  · have hμ1 : μ = 1 := by
      rw [hμ, multiplier_some, Option.some.injEq] at h3'
      apply Units.ext
      have := mul_right_cancel₀ hc.2 (h3'.trans (one_mul c).symm)
      simpa using this
    have hd'1 : d' = 1 := by
      rw [hμ, hμ1, ← multiplierHom_apply, map_one]
    have : d = g * d' * g⁻¹ := by rw [hd']; group
    rw [this, hd'1, mul_one, mul_inv_cancel]
  · exfalso
    rw [hμ, Equiv.Perm.mul_apply, inversion_none, multiplier_some, mul_zero] at hinf
    exact Option.some_ne_none _ hinf

theorem card_centralizer_le_of_fixedPointFree [Finite F] {e : Equiv.Perm (Omega F)}
    (he3 : 3 ≤ orderOf e)
    (hfree : ∀ k : ℕ, e ^ k ≠ 1 → ∀ x : Omega F, (e ^ k) x ≠ x) :
    Nat.card (Subgroup.centralizer ({e} : Set (Equiv.Perm (Omega F))) ⊓ coordinateD F :
      Subgroup (Equiv.Perm (Omega F))) ≤ Nat.card F + 1 := by
  classical
  have he1 : e ^ 1 ≠ 1 := by
    rw [pow_one]
    intro h
    rw [h, orderOf_one] at he3
    omega
  have he2 : e ^ 2 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  set Z := Subgroup.centralizer ({e} : Set (Equiv.Perm (Omega F))) ⊓ coordinateD F
  have hZfree : ∀ z ∈ Z, ∀ x : Omega F, z x = x → z = 1 := by
    intro z hz x hx
    have hze : z * e = e * z := Subgroup.mem_centralizer_singleton_iff.mp hz.1
    have hzek : ∀ k : ℕ, z ((e ^ k) x) = (e ^ k) x := by
      intro k
      have hc : z * e ^ k = e ^ k * z := (Commute.pow_right hze k).eq
      have := congrArg (fun φ : Equiv.Perm (Omega F) => φ x) hc
      simp only [Equiv.Perm.mul_apply] at this
      rw [this, hx]
    have hx1 : e x ≠ x := by simpa using hfree 1 he1 x
    have hx2 : (e ^ 2) x ≠ x := hfree 2 he2 x
    have he2x : (e ^ 2) x = e (e x) := by rw [pow_two, Equiv.Perm.mul_apply]
    have hx12 : e x ≠ (e ^ 2) x := by
      intro h
      rw [he2x] at h
      exact hx1 (e.injective h).symm
    have hz1 : z (e x) = e x := by simpa using hzek 1
    exact eq_one_of_three_fixed_points F hz.2 hx1.symm hx2.symm hx12 hx hz1 (hzek 2)
  let x₀ : Omega F := none
  have hinj : Function.Injective (fun z : Z => (z : Equiv.Perm (Omega F)) x₀) := by
    intro z₁ z₂ h
    have hmem : (z₂ : Equiv.Perm (Omega F))⁻¹ * z₁ ∈ Z := Z.mul_mem (Z.inv_mem z₂.2) z₁.2
    have hfix : ((z₂ : Equiv.Perm (Omega F))⁻¹ * z₁) x₀ = x₀ := by
      simp only at h
      rw [Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    have h1 := hZfree _ hmem x₀ hfix
    apply Subtype.ext
    exact (eq_of_inv_mul_eq_one h1).symm
  have : Fintype F := Fintype.ofFinite F
  calc Nat.card Z ≤ Nat.card (Omega F) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card F + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card]

end CFSG.Semidihedral.UnitaryBranch
