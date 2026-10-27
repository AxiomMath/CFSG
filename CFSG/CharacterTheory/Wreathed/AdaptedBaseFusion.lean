module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionComplements

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem adapted_base_fusion_model [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    (∃ σ υ g : G, IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) σ υ g) ∧
    ∀ (σ υ g : G) (hA : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) σ υ g),
      let σ' : modelBase S e := ⟨σ, hA.left_mem⟩
      let υ' : modelBase S e := ⟨υ, hA.right_mem⟩
      let a' : modelBase S e := σ' * υ'
      ∃ α β : MulAut (modelBase S e),
        let H := Subgroup.closure {α, β}
        let E : Set (modelBase S e) := (Subgroup.zpowers a' : Set (modelBase S e)) ∪
          Subgroup.zpowers σ' ∪ Subgroup.zpowers υ'
        (α σ' = υ' ∧ α υ' = σ') ∧ (β σ' = υ' ∧ β υ' = (σ' * υ')⁻¹) ∧
        (modelBase S e).normalizerMonoidHom.range = H ∧ Nat.card H = 6 ∧
        (∃ φ : Subgroup.normalizer (modelBase S e : Set G) ⧸
            (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
              (Subgroup.normalizer (modelBase S e : Set G)) ≃* H,
          ∀ x, (φ (QuotientGroup.mk x) : MulAut (modelBase S e)) =
            (modelBase S e).normalizerMonoidHom x) ∧
        (∀ u v : modelBase S e, IsConj (u : G) (v : G) ↔ v ∈ MulAction.orbit H u) ∧
        Subgroup.zpowers a' ⊓ Subgroup.zpowers σ' = ⊥ ∧
        Subgroup.zpowers a' ⊓ Subgroup.zpowers υ' = ⊥ ∧
        Subgroup.zpowers σ' ⊓ Subgroup.zpowers υ' = ⊥ ∧
        (∀ k : ℕ, 1 ≤ k → k < 2 ^ n →
          MulAction.orbit H (a' ^ k) = {a' ^ k, (σ' ^ k)⁻¹, (υ' ^ k)⁻¹}) ∧
        Set.InjOn (fun k : ℕ => MulAction.orbit H (a' ^ k)) (Set.Ico 1 (2 ^ n)) ∧
        (∀ u : modelBase S e, u ∉ E → (MulAction.orbit H u).ncard = 6) ∧
        ((fun u => MulAction.orbit H u) '' Eᶜ).ncard = (2 ^ n - 1) * (2 ^ n - 2) / 6 ∧
        ∀ u : modelBase S e, u ∉ E →
          let D := Subgroup.centralizer {(u : G)}
          let K := CFSG.oddCore D
          (∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = modelBase S e) ∧
          Subgroup.normalizer (modelBase S e : Set G) ⊓ D =
            Subgroup.centralizer (modelBase S e : Set G) ⊓ D ∧
          (K.map D.subtype : Set G) * (modelBase S e : Set G) = D ∧
          K.map D.subtype ⊓ modelBase S e = ⊥ ∧
          K.index = (2 ^ n) ^ 2 ∧
          (∃ f : modelBase S e ≃* D ⧸ K, ∀ (y : G) (hyU : y ∈ modelBase S e) (hyD : y ∈ D),
            f ⟨y, hyU⟩ = ((⟨y, hyD⟩ : D) : D ⧸ K)) ∧
          K.Normal ∧ Odd (Nat.card K) ∧ K.IsComplement' ((modelBase S e).subgroupOf D) ∧
          ∀ K' : Subgroup D, K'.Normal → Odd (Nat.card K') →
            K'.IsComplement' ((modelBase S e).subgroupOf D) → K' = K := by
  refine ⟨exists_isAdaptedBase S e hnonab hn, ?_⟩
  intro σ υ g hA σ' υ' a'
  refine ⟨swapAut S e, hA.aut, ?_⟩
  intro H E
  have hrange := range_eq_closure hA (by omega)
  refine ⟨⟨swapAut_left hA, swapAut_right hA⟩, ⟨hA.aut_left, hA.aut_right⟩, hrange,
    card_closure hA (by omega), ?_, ?_, zpowers_mul_inf_left hA, zpowers_mul_inf_right hA,
    zpowers_left_inf_right' hA, fun k _ _ => orbit_pow_mul hA k, orbit_pow_mul_injOn hA,
    fun u hu => ncard_orbit_of_not_mem_exc hA hn hu, ncard_orbits_compl_exc hA hn, ?_⟩
  ·
    refine ⟨(QuotientGroup.quotientMulEquivOfEq
      (Subgroup.normalizerMonoidHom_ker (modelBase S e)).symm).trans
        ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange)),
      fun x => rfl⟩
  ·
    intro u v
    rw [isConj_iff_exists hA hn u v, mem_orbit_iff_exists]
  ·
    intro u hu D K
    obtain ⟨hmul, hinf, hindex, hiso, hodd, hcomp, huniq⟩ :=
      centralizer_oddCore_complement hA hn hu
    exact ⟨exists_sylow_centralizer hA hn hu, normalizer_inf_centralizer hA hn hu, hmul, hinf,
      hindex, hiso, inferInstance, hodd, hcomp, huniq⟩

theorem general_adapted_base_fusion_and_generic_centralizer_complements [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let s := wreathModelHom S e (Original.s (2 ^ n))
    let t := wreathModelHom S e (Original.t (2 ^ n))
    let w := wreathModelHom S e (Original.z (2 ^ n))
    let U := Subgroup.closure {s, t}
    let a := s * t
    (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
    ∀ (σ υ g : G) (hA : IsAdaptedBase U a w σ υ g),
      let σ' : U := ⟨σ, hA.left_mem⟩
      let υ' : U := ⟨υ, hA.right_mem⟩
      let a' : U := σ' * υ'
      ∃ α β : MulAut U,
        let H := Subgroup.closure {α, β}
        let E : Set U := (Subgroup.zpowers a' : Set U) ∪ Subgroup.zpowers σ' ∪
          Subgroup.zpowers υ'
        (α σ' = υ' ∧ α υ' = σ') ∧ (β σ' = υ' ∧ β υ' = (σ' * υ')⁻¹) ∧
        U.normalizerMonoidHom.range = H ∧ Nat.card H = 6 ∧
        (∃ φ : Subgroup.normalizer (U : Set G) ⧸
            (Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer (U : Set G)) ≃* H,
          ∀ x, (φ (QuotientGroup.mk x) : MulAut U) = U.normalizerMonoidHom x) ∧
        (∀ u v : U, IsConj (u : G) (v : G) ↔ v ∈ MulAction.orbit H u) ∧
        Subgroup.zpowers a' ⊓ Subgroup.zpowers σ' = ⊥ ∧
        Subgroup.zpowers a' ⊓ Subgroup.zpowers υ' = ⊥ ∧
        Subgroup.zpowers σ' ⊓ Subgroup.zpowers υ' = ⊥ ∧
        (∀ k : ℕ, 1 ≤ k → k < 2 ^ n →
          MulAction.orbit H (a' ^ k) = {a' ^ k, (σ' ^ k)⁻¹, (υ' ^ k)⁻¹}) ∧
        Set.InjOn (fun k : ℕ => MulAction.orbit H (a' ^ k)) (Set.Ico 1 (2 ^ n)) ∧
        (∀ u : U, u ∉ E → (MulAction.orbit H u).ncard = 6) ∧
        ((fun u => MulAction.orbit H u) '' Eᶜ).ncard = (2 ^ n - 1) * (2 ^ n - 2) / 6 ∧
        ∀ u : U, u ∉ E →
          let D := Subgroup.centralizer {(u : G)}
          let K := CFSG.oddCore D
          (∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = U) ∧
          Subgroup.normalizer (U : Set G) ⊓ D = Subgroup.centralizer (U : Set G) ⊓ D ∧
          (K.map D.subtype : Set G) * (U : Set G) = D ∧
          K.map D.subtype ⊓ U = ⊥ ∧
          K.index = (2 ^ n) ^ 2 ∧
          (∃ f : U ≃* D ⧸ K, ∀ (y : G) (hyU : y ∈ U) (hyD : y ∈ D),
            f ⟨y, hyU⟩ = ((⟨y, hyD⟩ : D) : D ⧸ K)) ∧
          K.Normal ∧ Odd (Nat.card K) ∧ K.IsComplement' (U.subgroupOf D) ∧
          ∀ K' : Subgroup D, K'.Normal → Odd (Nat.card K') →
            K'.IsComplement' (U.subgroupOf D) → K' = K := by
  intro s t w U a
  have hU : U = modelBase S e := by
    rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair]
  have ha : a = wreathModelHom S e (Original.a (2 ^ n)) := by
    rw [Original.a, map_mul]
  have hw : w = wreathModelHom S e (Original.z (2 ^ n)) := rfl
  clear_value s t w U a
  subst hU ha hw
  exact adapted_base_fusion_model hnonab n hn S e

end CFSG.Wreathed.AdaptedBaseFusion
