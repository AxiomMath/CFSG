module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

namespace Hom

open Module

universe u

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem conjAlgEquiv_mul (g h : V ≃ₗ[ZMod 2] V) (z : Module.End (ZMod 2) V) :
    (g * h).conjAlgEquiv (ZMod 2) z = g.conjAlgEquiv (ZMod 2) (h.conjAlgEquiv (ZMod 2) z) := by
  ext v
  simp [LinearEquiv.conjAlgEquiv_apply]
  rw [LinearEquiv.mul_eq_trans, LinearEquiv.symm_trans_apply]

theorem conjAlgEquiv_one (z : Module.End (ZMod 2) V) :
    (1 : V ≃ₗ[ZMod 2] V).conjAlgEquiv (ZMod 2) z = z := by
  ext v
  simp [LinearEquiv.conjAlgEquiv_apply]
  rfl

theorem centralize_of_odd (K : Subalgebra (ZMod 2) (Module.End (ZMod 2) V)) (hK : IsField K)
    (t : ℕ) (hdim : finrank (ZMod 2) K = 2 ^ t) (g : V ≃ₗ[ZMod 2] V) (hg : Odd (orderOf g))
    (hn : ∀ z ∈ K, g.conjAlgEquiv (ZMod 2) z ∈ K) :
    ∀ z ∈ K, g.conjAlgEquiv (ZMod 2) z = z := by
  letI : Field K := hK.toField
  have : Finite (Module.End (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  haveI : Finite K := Finite.of_injective _ Subtype.val_injective
  let σ₀ : K →ₐ[ZMod 2] K :=
    ((g.conjAlgEquiv (ZMod 2)).toAlgHom.comp K.val).codRestrict K (fun z => hn z z.2)
  have hσ₀inj : Function.Injective σ₀ := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact (g.conjAlgEquiv (ZMod 2)).injective this
  let σ : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofBijective σ₀ ⟨hσ₀inj, Finite.injective_iff_surjective.mp hσ₀inj⟩
  have hσ : ∀ z : K, ((σ z : K) : Module.End (ZMod 2) V) = g.conjAlgEquiv (ZMod 2) z :=
    fun z => rfl
  have hσpow : ∀ (n : ℕ) (z : K), (((σ ^ n) z : K) : Module.End (ZMod 2) V) =
      (g ^ n).conjAlgEquiv (ZMod 2) z := by
    intro n
    induction n with
    | zero => intro z; simp [conjAlgEquiv_one]
    | succ n ih =>
      intro z
      rw [pow_succ', pow_succ', AlgEquiv.mul_apply, hσ, ih, conjAlgEquiv_mul]
  have hodd1 : σ ^ orderOf g = 1 := by
    ext z
    rw [hσpow, pow_orderOf_eq_one, conjAlgEquiv_one]
    rfl
  have hcard : Nat.card (K ≃ₐ[ZMod 2] K) = 2 ^ t := by
    rw [IsGalois.card_aut_eq_finrank (ZMod 2) K, hdim]
  have hpow2 : σ ^ (2 ^ t) = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hord : orderOf σ = 1 := by
    have h1 : orderOf σ ∣ orderOf g := orderOf_dvd_of_pow_eq_one hodd1
    have h2 : orderOf σ ∣ 2 ^ t := orderOf_dvd_of_pow_eq_one hpow2
    have hcop : Nat.Coprime (orderOf g) (2 ^ t) :=
      Nat.Coprime.pow_right t hg.coprime_two_right
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have hσ1 : σ = 1 := orderOf_eq_one_iff.mp hord
  intro z hz
  have := hσ ⟨z, hz⟩
  rw [hσ1] at this
  exact this.symm

theorem exists_normal_prime_index (G : Type u) [Group G] [Finite G] [Nontrivial G]
    [Group.IsSolvable G] : ∃ M : Subgroup G, M.Normal ∧ ∃ q : ℕ, q.Prime ∧ M.index = q := by
  have hlt : commutator G < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial G
  have hne : Nat.card (Abelianization G) ≠ 1 := by
    intro h
    have : (commutator G).index = 1 := h
    rw [Subgroup.index_eq_one] at this
    exact hlt.ne this
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  obtain ⟨H, hHi, hHn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hqd
  refine ⟨H.comap (Abelianization.of : G →* Abelianization G), Subgroup.Normal.comap hHn _, q, hq,
    ?_⟩
  have hs : Function.Surjective (Abelianization.of : G →* Abelianization G) :=
    QuotientGroup.mk'_surjective _
  rw [Subgroup.index_comap_of_surjective _ hs, hHi]

end Hom

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
