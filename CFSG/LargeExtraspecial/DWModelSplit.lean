module

public import CFSG.LargeExtraspecial.DWModelHom

public section

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module Matrix CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

section Splitting

variable {H : Type*} [Group H] {V : Subgroup H} [V.Normal] [IsElementaryAbelian 2 V]

@[expose] noncomputable def Splitting.ofComplement (hC : centralizer (V : Set H) ≤ V)
    (hsurj : Function.Surjective (conjLinear V)) {K : Subgroup H} (hK : V ⊓ K = ⊥)
    (hK' : V ⊔ K = ⊤) : Splitting V :=
  have hker : ∀ h, conjLinear V h = 1 ↔ h ∈ V := fun h => by
    rw [conjLinear_eq_one_iff V hC]
    exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hh => ⟨Additive.ofMul ⟨h, hh⟩, rfl⟩⟩
  have hbij : Function.Bijective ((conjLinear V).comp K.subtype) := by
    refine ⟨fun k k' hkk' => ?_, fun f => ?_⟩
    · have h1 : conjLinear V ((k : H)⁻¹ * k') = 1 := by
        rw [map_mul, map_inv]
        exact inv_mul_eq_one.mpr hkk'
      have h2 : (k : H)⁻¹ * k' ∈ V ⊓ K := ⟨(hker _).mp h1, K.mul_mem (K.inv_mem k.2) k'.2⟩
      rw [hK, mem_bot, inv_mul_eq_one] at h2
      exact Subtype.ext h2
    · obtain ⟨h, rfl⟩ := hsurj f
      have hmem : h ∈ V ⊔ K := by rw [hK']; exact mem_top h
      obtain ⟨v, hv, k, hk, rfl⟩ := mem_sup_of_normal_left.mp hmem
      refine ⟨⟨k, hk⟩, ?_⟩
      change conjLinear V k = conjLinear V (v * k)
      rw [map_mul, (hker v).mpr hv, one_mul]
  { centralizer_le := hC
    σ := K.subtype.comp (MulEquiv.ofBijective _ hbij).symm.toMonoidHom
    conjLinear_σ := fun f => (MulEquiv.ofBijective _ hbij).apply_symm_apply f }

theorem nonempty_splitting [Finite H] (hC : centralizer (V : Set H) ≤ V)
    (hsurj : Function.Surjective (conjLinear V)) (h6 : 6 ≤ finrank (ZMod 2) (Additive V)) :
    Nonempty (Splitting V) := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  let X : NatExt H (Additive V) :=
    { ι := fun e => ((Additive.toMul e : V) : H)
      ι_add := fun _ _ => rfl
      injective := fun _ _ h => Additive.toMul.injective (Subtype.ext h)
      π := conjLinear V
      surjective := hsurj
      ker_iff := conjLinear_eq_one_iff V hC
      conj := fun g e => (coe_conjLinear_apply V g e).symm }
  have hXV : X.V = V := by
    ext g
    exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hg => ⟨Additive.ofMul ⟨g, hg⟩, rfl⟩⟩
  obtain ⟨K, hK, hK'⟩ := X.exists_complement h6
  rw [hXV] at hK hK'
  exact ⟨Splitting.ofComplement hC hsurj hK hK'⟩

end Splitting

theorem exists_basis_eq {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {m : ℕ} (hm : finrank (ZMod 2) E = m) (hm0 : 0 < m) {e : E}
    (he : e ≠ 0) : ∃ b : Basis (Fin m) (ZMod 2) E, b ⟨0, hm0⟩ = e := by
  let b₀ := Module.finBasisOfFinrankEq (ZMod 2) E hm
  obtain ⟨f, d, hfd, ht⟩ := exists_transvection_apply_eq (b₀.ne_zero ⟨0, hm0⟩) he
  exact ⟨b₀.map (LinearEquiv.transvection hfd), by rw [Basis.map_apply, ht]⟩

variable {G : Type*} [Group G]

instance normal_subgroupOf_normalizer (A : Subgroup G) :
    (A.subgroupOf (normalizer (A : Set G))).Normal :=
  normal_in_normalizer

instance isElementaryAbelian_subgroupOf_normalizer (A : Subgroup G) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.subgroupOf (normalizer (A : Set G))) :=
  IsElementaryAbelian.subgroupOf le_normalizer

theorem nonempty_centralizer_mulEquiv_subgroupOf {K : Subgroup G} {z : G} (hzK : z ∈ K)
    (hK : centralizer ({z} : Set G) ≤ K) :
    Nonempty (centralizer ({z} : Set G) ≃* centralizer ({(⟨z, hzK⟩ : K)} : Set K)) := by
  have heq : (centralizer ({(⟨z, hzK⟩ : K)} : Set K)).map K.subtype =
      centralizer ({z} : Set G) := by
    ext g
    simp only [mem_map, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact congrArg Subtype.val hk
    · intro hg
      exact ⟨⟨g, hK (mem_centralizer_singleton_iff.mpr hg)⟩, Subtype.ext hg, rfl⟩
  exact ⟨((centralizer ({(⟨z, hzK⟩ : K)} : Set K)).equivMapOfInjective K.subtype
    K.subtype_injective).trans (MulEquiv.subgroupCongr heq) |>.symm⟩

theorem nonempty_centralizer_mulEquiv_of_surjective [Finite G] (A : Subgroup G)
    [IsElementaryAbelian 2 A] {m : ℕ} (hA : Nat.card A = 2 ^ m) (h6 : 6 ≤ m)
    (hC : centralizer (A : Set G) ≤ A)
    (hsurj : Function.Surjective (conjLinear (A.subgroupOf (normalizer (A : Set G)))))
    {z : G} (hz : z ∈ A) (hz1 : z ≠ 1) (hzN : centralizer ({z} : Set G) ≤ normalizer (A : Set G)) :
    Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({cornerTransvection (N := m + 1) (by omega)} :
        Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2)))) := by
  set N := normalizer (A : Set G)
  set AN := A.subgroupOf N
  have hAN : A ≤ N := le_normalizer
  have hCN : centralizer (AN : Set N) ≤ AN := by
    intro g hg
    rw [mem_subgroupOf]
    refine hC (mem_centralizer_iff.mpr fun a ha => ?_)
    have := mem_centralizer_iff.mp hg ⟨a, hAN ha⟩
      (by rw [SetLike.mem_coe, mem_subgroupOf]; exact ha)
    exact congrArg Subtype.val this
  have : Finite (Additive AN) := inferInstanceAs (Finite AN)
  have : FiniteDimensional (ZMod 2) (Additive AN) := Module.Finite.of_finite
  have hfin : finrank (ZMod 2) (Additive AN) = m := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive AN)
    rw [Nat.card_zmod, show Nat.card (Additive AN) = Nat.card AN from rfl,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  obtain ⟨X⟩ := nonempty_splitting hCN hsurj (by omega)
  have hzAN : (⟨z, hAN hz⟩ : N) ∈ AN := hz
  have hz0 : Additive.ofMul (⟨⟨z, hAN hz⟩, hzAN⟩ : AN) ≠ 0 := by
    intro h
    exact hz1 (congrArg (fun x : AN => ((x : N) : G)) (Additive.ofMul.injective h))
  obtain ⟨b, hb⟩ := exists_basis_eq hfin (by omega) hz0
  obtain ⟨e₁⟩ := nonempty_centralizer_mulEquiv_subgroupOf (hAN hz) hzN
  obtain ⟨e₂⟩ := X.nonempty_centralizer_mulEquiv b (by omega) hzAN hb
  exact ⟨e₁.trans e₂⟩

end CFSG.LargeExtraspecial.DW
