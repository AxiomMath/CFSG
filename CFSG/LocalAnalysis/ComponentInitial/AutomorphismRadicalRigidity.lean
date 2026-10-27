module

public import CFSG.GroupTheory.PCore.CharacteristicPPrimeCore

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG

theorem mulAut_mul_conj_mul_inv {C : Type*} [Group C] (α : MulAut C) (u : C) :
    α * MulAut.conj u * α⁻¹ = MulAut.conj (α u) := by
  ext c
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem automorphism_normalizer_from_pointwise_radical_rigidity {C : Type*} [Group C] [Finite C]
    (hZ : center C = ⊥) {p : ℕ} [Fact p.Prime] {U : Subgroup C} (hU : IsPGroup p U)
    {A : Subgroup (MulAut C)} (_hUA : U.map MulAut.conj ≤ A)
    (hCA : ∀ α ∈ A, (∀ u ∈ U, α u = u) → α ∈ U.map MulAut.conj)
    {K : Subgroup (MulAut C)} (hUK : U.map MulAut.conj ≤ K)
    (hKN : ∀ α ∈ K, α ∈ A ∧ U.map α.toMonoidHom = U) :
    IsCharacteristicP p K ∧ (∀ R : Subgroup K, R.Normal → ¬ p ∣ Nat.card R → R = ⊥) ∧
      pPrimeCore p K = ⊥ := by
  have : Finite (MulAut C) :=
    Finite.of_injective (fun f : MulAut C => (f : C → C)) (fun _ _ h => MulEquiv.ext (congrFun h))
  have hι : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro g hg
    rw [mem_center_iff]
    intro c
    have h1 := congrArg (fun f : MulAut C => f c) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  set U' := (U.map MulAut.conj).subgroupOf K with hU'
  have hU'n : U'.Normal := by
    constructor
    rintro ⟨_, hx⟩ ⟨u, hu, rfl⟩ ⟨k, hk⟩
    change k * MulAut.conj u * k⁻¹ ∈ U.map MulAut.conj
    rw [mulAut_mul_conj_mul_inv]
    have hku : k u ∈ U := by
      rw [← (hKN k hk).2]
      exact ⟨u, hu, rfl⟩
    exact ⟨k u, hku, rfl⟩
  have hU'p : IsPGroup p U' := by
    have h1 : IsPGroup p (U.map MulAut.conj) :=
      hU.of_equiv (U.equivMapOfInjective _ hι)
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hUK).symm
  have hU'core : U' ≤ pCore p K := le_sSup ⟨hU'n, hU'p⟩
  have hchar : IsCharacteristicP p K := by
    intro β hβ
    apply hU'core
    have hfix : ∀ u ∈ U, (β : MulAut C) u = u := by
      intro u hu
      have hmem : (⟨MulAut.conj u, hUK ⟨u, hu, rfl⟩⟩ : K) ∈ pCore p K :=
        hU'core (show (⟨MulAut.conj u, hUK ⟨u, hu, rfl⟩⟩ : K) ∈ U' from ⟨u, hu, rfl⟩)
      have h1 := congrArg Subtype.val (mem_centralizer_iff.1 hβ _ hmem)
      change MulAut.conj u * (β : MulAut C) = (β : MulAut C) * MulAut.conj u at h1
      have h2 : (β : MulAut C) * MulAut.conj u * (β : MulAut C)⁻¹ = MulAut.conj u := by
        rw [← h1, mul_inv_cancel_right]
      rw [mulAut_mul_conj_mul_inv] at h2
      exact hι h2
    exact hCA β (hKN β β.2).1 hfix
  obtain ⟨hR, hcore⟩ := characteristic_p_normal_prime_complement_trivial hchar
  exact ⟨hchar, hR, hcore⟩

end CFSG.LocalAnalysis.ComponentInitial
