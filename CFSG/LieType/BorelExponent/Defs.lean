module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.SylowTwoEquiv

public section

namespace CFSG.LieType.BorelExponent

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.QuasithinUnique (IsSylowTwoOf)

@[expose] def lieBorelExponent : StatedLieTag → ℕ → ℕ
  | .PSU, f => 2 ^ (2 * f) - 1
  | .POmegaMinus, f => 2 ^ (2 * f) - 1
  | .twistedE6, f => 2 ^ (2 * f) - 1
  | .trialityD4, f => 2 ^ (3 * f) - 1
  | _, f => 2 ^ f - 1

@[expose] def HasBorelExponent (X : Type*) [Group X] (e : ℕ) : Prop :=
  ∀ U : Subgroup X, IsSylowTwoOf U ⊤ → ∀ x ∈ Subgroup.normalizer (U : Set X), x ^ e ∈ U

@[expose] def BorelExponentAt (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m f : ℕ), StatedLieAdmissible t m 2 f →
    CFSG.Blueprint.LieModel X t m 2 f → HasBorelExponent X (lieBorelExponent t f)

variable {X Y : Type*} [Group X] [Group Y]

theorem hasBorelExponent_of_isSylowTwoOf [Finite X] {U₀ : Subgroup X} {e : ℕ}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (h : ∀ x ∈ Subgroup.normalizer (U₀ : Set X), x ^ e ∈ U₀) :
    HasBorelExponent X e := by
  intro U hU x hx
  obtain ⟨g, -, rfl⟩ := hU₀.exists_conj hU
  have key : ∀ y : X, y ∈ U₀.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ U₀ := fun y => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hx' : g⁻¹ * x * g ∈ Subgroup.normalizer (U₀ : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro u
    have h1 := hx (g * u * g⁻¹)
    rw [key, key] at h1
    convert h1 using 2 <;> group
  rw [key]
  convert h _ hx' using 1
  have := conj_pow (a := g⁻¹) (b := x) (i := e)
  simp only [inv_inv] at this
  exact this.symm

theorem pow_mem_of_ker_eq {G T : Type*} [Group G] [Group T] {B U : Subgroup G} (φ : B →* T)
    (hker : φ.ker = U.subgroupOf B) {e : ℕ} (hT : ∀ b : B, φ b ^ e = 1) {b : G} (hb : b ∈ B) :
    b ^ e ∈ U := by
  have h : (⟨b, hb⟩ ^ e : B) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hT _
  rw [hker, Subgroup.mem_subgroupOf] at h
  simpa using h

theorem units_pi_pow_card_sub_one {ι K : Type*} [Field K] [Finite K] (u : ι → Kˣ) :
    u ^ (Nat.card K - 1) = 1 := by
  have := Fintype.ofFinite K
  funext i
  apply Units.ext
  rw [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one,
    Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ (u i).ne_zero

theorem mul_pow_mem_of_le_normalizer {G : Type*} [Group G] {U H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (U : Set G)) {e : ℕ} (hHe : ∀ h ∈ H, h ^ e = 1) {u h : G}
    (hu : u ∈ U) (hh : h ∈ H) : (u * h) ^ e ∈ U := by
  have key : ∀ n : ℕ, ∃ u' ∈ U, (u * h) ^ n = u' * h ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨u', hu', e'⟩ := ih
      refine ⟨u' * (h ^ n * u * (h ^ n)⁻¹), mul_mem hu'
        ((Subgroup.mem_normalizer_iff.1 (pow_mem (hH hh) n) u).1 hu), ?_⟩
      rw [pow_succ (u * h) n, e']
      group
  obtain ⟨u', hu', e'⟩ := key e
  rw [e', hHe h hh, mul_one]
  exact hu'

theorem hasBorelExponent_of_sylow [Finite X] (P : Sylow 2 X) {e : ℕ}
    (h : ∀ x ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), x ^ e ∈ (P : Subgroup X)) :
    HasBorelExponent X e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hasBorelExponent_of_isSylowTwoOf ⟨le_top, P.isPGroup', ?_⟩ h
  change ¬ 2 ∣ (P : Subgroup X).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact P.not_dvd_index

theorem HasBorelExponent.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X ≃* Y) {e : ℕ} (h : HasBorelExponent X e) : HasBorelExponent Y e := by
  intro U hU y hy
  have hU' : IsSylowTwoOf (U.map φ.symm.toMonoidHom) ⊤ := by
    have := hU.map_mulEquiv φ.symm
    rwa [Subgroup.map_top_of_surjective _ φ.symm.surjective] at this
  have key : ∀ z : X, z ∈ U.map φ.symm.toMonoidHom ↔ φ z ∈ U := fun z => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hy' : φ.symm y ∈ Subgroup.normalizer ((U.map φ.symm.toMonoidHom : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro z
    rw [key, key, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hy (φ z)
  have := (key _).1 (h _ hU' _ hy')
  rwa [map_pow, MulEquiv.apply_symm_apply] at this

theorem HasBorelExponent.dvd_of_orderOf_conj {e : ℕ} (h : HasBorelExponent X e)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : X}
    (hx : orderOf (MulAut.conj x) = r) (hxU : x ∈ Subgroup.normalizer (U : Set X)) : r ∣ e := by
  obtain ⟨k, hk⟩ := hU.2.1 ⟨x ^ e, h U hU x hxU⟩
  have hk' : x ^ (e * 2 ^ k) = 1 := by
    rw [pow_mul]
    exact congrArg Subtype.val hk
  have hdvd : r ∣ e * 2 ^ k := by
    rw [← hx]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hk', map_one]
  rcases hr.dvd_mul.1 hdvd with h1 | h2
  · exact h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)) hr2

end CFSG.LieType.BorelExponent

end
