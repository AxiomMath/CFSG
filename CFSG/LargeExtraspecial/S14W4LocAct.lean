module

public import CFSG.LargeExtraspecial.S14W4LocB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup CFSG.LargeExtraspecial.S4

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure Act (T : Setting X) (R : Subgroup X) (π : T.M →* (V ≃ₗ[ZMod 2] V)) : Prop where
  R_le_M : R ≤ T.M
  conj_mem : ∀ k : T.M, ∀ r ∈ R, (k : X) * r * (k : X)⁻¹ ∈ R
  Q_le_ker : T.Q ≤ π.ker
  ker_R : ∀ r : T.M, (r : X) ∈ R → π r = 1 → r ∈ T.Q

variable {π : T.M →* (V ≃ₗ[ZMod 2] V)}

theorem mem_Q_of_π_eq_one (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    (k : T.M) (hk : ∃ n : ℕ, k ^ 2 ^ n = 1) (hπ : π k = 1) : k ∈ T.Q := by
  refine mem_Q_of_comm hcard hL k hk fun r hr => comm_of_mem_Q ?_
  have hR : ((k * r * k⁻¹ * r⁻¹ : T.M) : X) ∈ R :=
    mul_mem (A.conj_mem k r hr) (inv_mem hr)
  refine A.ker_R _ hR ?_
  simp only [map_mul, map_inv, hπ, one_mul, inv_one, mul_one, mul_inv_cancel]

@[expose] noncomputable def πbar (T : Setting X) (π : T.M →* (V ≃ₗ[ZMod 2] V))
    (hQ : T.Q ≤ π.ker) : T.Mbar →* (V ≃ₗ[ZMod 2] V) :=
  (QuotientGroup.lift T.Q π hQ).comp T.quotientEquivMbar.symm.toMonoidHom

theorem ρ_mem_Mbar (k : T.M) : T.ρ k ∈ T.Mbar := MonoidHom.mem_range.mpr ⟨k, rfl⟩

theorem πbar_ρ (hQ : T.Q ≤ π.ker) (k : T.M) : πbar T π hQ ⟨T.ρ k, ρ_mem_Mbar k⟩ = π k := by
  have e : T.quotientEquivMbar.symm ⟨T.ρ k, ρ_mem_Mbar k⟩ = (k : T.M ⧸ T.Q) :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext (T.quotientEquivMbar_mk k).symm)
  exact (congrArg (QuotientGroup.lift T.Q π hQ) e).trans (QuotientGroup.lift_mk _ hQ k)

theorem eq_one_of_πbar_eq_one (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    (x : T.Mbar) (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) (h1 : πbar T π A.Q_le_ker x = 1) : x = 1 := by
  have hk : ∃ k : T.M, T.ρ k = x := MonoidHom.mem_range.mp x.2
  cases hk with
  | intro k hkx =>
    have hxk : x = ⟨T.ρ k, ρ_mem_Mbar k⟩ := Subtype.ext hkx.symm
    subst hxk
    cases hx with
    | intro n hn =>
      have hρn : T.ρ (k ^ 2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        rw [map_pow]
        exact this
      have hQn : ((k ^ 2 ^ n : T.M) : X) ∈ T.QG :=
        (T.mem_QG_iff).mpr ⟨(k ^ 2 ^ n).2, T.mem_Q_of_ρ_eq_one hρn⟩
      have hk2 : ∃ m : ℕ, k ^ 2 ^ m = 1 := by
        refine ⟨n + 2, Subtype.ext ?_⟩
        have h4 := T.pow_four_eq_one hQn
        rw [pow_succ, pow_succ, mul_assoc, pow_mul]
        exact (by simpa using h4 : ((k : X) ^ 2 ^ n) ^ (2 * 2) = 1)
      have hkQ := mem_Q_of_π_eq_one A hcard hL k hk2 ((πbar_ρ A.Q_le_ker k).symm.trans h1)
      exact Subtype.ext (T.ρ_eq_one_of_mem_Q hkQ)

theorem card_map_πbar (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    (P : Subgroup T.Mbar) (hP : IsPGroup 2 P) :
    Nat.card (P.map (πbar T π A.Q_le_ker)) = Nat.card P := by
  set f := (πbar T π A.Q_le_ker).comp P.subtype with hf
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun x hx => ?_
    have hx2 : ∃ n : ℕ, (x : T.Mbar) ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hP x
      exact ⟨n, congrArg Subtype.val hn⟩
    exact Subtype.ext (eq_one_of_πbar_eq_one A hcard hL x hx2 hx)
  have h1 : Nat.card P = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h2 : f.range = P.map (πbar T π A.Q_le_ker) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, h2]

theorem map_πbar_le (hQ : T.Q ≤ π.ker) {B : Subgroup (V ≃ₗ[ZMod 2] V)} (hB : ∀ k, π k ∈ B)
    (P : Subgroup T.Mbar) : P.map (πbar T π hQ) ≤ B := by
  rintro _ ⟨x, -, rfl⟩
  have hk : ∃ k : T.M, T.ρ k = x := MonoidHom.mem_range.mp x.2
  obtain ⟨k, hk⟩ := hk
  have e1 : πbar T π hQ x = π k :=
    (congrArg (πbar T π hQ) (Subtype.ext hk.symm : x = ⟨T.ρ k, ρ_mem_Mbar k⟩)).trans
      (πbar_ρ hQ k)
  exact e1 ▸ hB k

theorem card_le_of_isPGroup (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    {B : Subgroup (V ≃ₗ[ZMod 2] V)} (hB : ∀ k, π k ∈ B) {e : ℕ}
    (hBe : ∀ P' : Subgroup (V ≃ₗ[ZMod 2] V), P' ≤ B → IsPGroup 2 P' → Nat.card P' ≤ 2 ^ e)
    (P : Subgroup T.Mbar) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ e :=
  card_map_πbar A hcard hL P hP ▸ hBe _ (map_πbar_le A.Q_le_ker hB P) (hP.map _)

theorem card_le_of_elemAbelian (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    {B : Subgroup (V ≃ₗ[ZMod 2] V)} (hB : ∀ k, π k ∈ B) {e : ℕ}
    (hBe : ∀ P' : Subgroup (V ≃ₗ[ZMod 2] V), P' ≤ B → (∀ x ∈ P', ∀ y ∈ P', x * y = y * x) →
      (∀ x ∈ P', x ^ 2 = 1) → Nat.card P' ≤ 2 ^ e)
    (P : Subgroup T.Mbar) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (h2 : ∀ x ∈ P, x ^ 2 = 1) : Nat.card P ≤ 2 ^ e := by
  have hP : IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by simpa using h2 x x.2)⟩
  refine card_map_πbar A hcard hL P hP ▸ hBe _ (map_πbar_le A.Q_le_ker hB P) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h2 x hx, map_one]

end CFSG.LargeExtraspecial.S14.W4Loc
