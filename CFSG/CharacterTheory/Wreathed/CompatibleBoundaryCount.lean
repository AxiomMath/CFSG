module

public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCountCharacters

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.TwoRankLowerBound.Helpers
open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G]

theorem compatible_centralizer_boundary_character_count [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (eb : FiniteIrreducibleCharacterBasis
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))) :
    let s := wreathModelHom S e (Original.s (2 ^ n))
    let t := wreathModelHom S e (Original.t (2 ^ n))
    let U := Subgroup.closure {s, t}
    let a := s * t
    let x := a ^ (2 ^ n / 2)
    let T := Subgroup.closure {s ^ (2 ^ n / 2), t ^ (2 ^ n / 2)}
    let N := Subgroup.centralizer {x}
    let C := Subgroup.centralizer (T : Set G)
    let C₀ := ambientOddCore C
    let Z := Subgroup.zpowers a
    let E := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))
    let N' := (commutator N).map N.subtype
    let Ξ : Set eb.index := {θ | ∃ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
      (∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G) (y : E),
        z ∈ Z → (c : G) = z * y → θt c = (eb.representation θ).character y) ∧
      ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ}
    ∀ (η : G) (hη : η ∈ Subgroup.normalizer (U : Set G)),
      orderOf (U.normalizerMonoidHom ⟨η, hη⟩) = 3 →
      ∀ qb : FiniteIrreducibleCharacterBasis (E ⧸ boundaryKernel S e η),
      let Cstar := Subgroup.closure {y : G | ∃ c ∈ C₀, y = c⁻¹ * (η⁻¹ * c * η)}
      let D := Cstar ⊔ N'
      let J := E ⊓ D
      Cstar ≤ C₀ ∧ C₀ ≤ N ∧ D ≤ N ∧ (D.subgroupOf N).Normal ∧
      (D : Set G) = (Cstar : Set G) * (N' : Set G) ∧
      boundaryKernel S e η = J.subgroupOf E ∧ (J.subgroupOf E).Normal ∧
      IsMulCommutative (E ⧸ boundaryKernel S e η) ∧
      (∃ f : qb.index ≃ Ξ, ∀ φ : qb.index,
        (eb.representation (f φ)).character =
          (qb.representation φ).character ∘ QuotientGroup.mk) ∧
      (∀ θ ∈ Ξ, (eb.representation θ).character 1 = 1 ∧
        Module.finrank ℂ (eb.representation θ).vector = 1) ∧
      Ξ.ncard = J.relIndex E := by
  intro s t U a x T N C C₀ Z E N' Ξ η hη hord qb Cstar D J
  have hU : U = modelBase S e := by
    rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair]
  clear_value U
  subst hU
  have hZ : ∀ z : G, z ∈ Z ↔ z ∈ modelCenter S e := by
    intro z
    rw [modelCenter_eq_zpowers, show wreathModelHom S e (Original.a (2 ^ n)) = a from
      map_mul _ _ _]
  set K := boundaryKernel S e η with hK
  have hmem : ∀ θ : eb.index, θ ∈ Ξ ↔ ∃ μ : E →* ℂˣ,
      (∀ y, (μ y : ℂ) = (eb.representation θ).character y) ∧ K ≤ μ.ker := by
    intro θ
    constructor
    · rintro ⟨θt, hθt, ψ, hψ⟩
      exact exists_hom_of_family S e hnonab hn hη hord _ θt
        (fun c y hcy => hθt c 1 y (Subgroup.one_mem _) (by rw [one_mul]; exact hcy)) hψ
    · rintro ⟨μ, hμχ, hμK⟩
      obtain ⟨d, hd⟩ :=
        (sylow_and_base_four_group_centralizer_structure n hn S e).centralizer_direct
      let θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ :=
        fun c => (eb.representation θ).character (d.symm c).2
      have hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G) (y : E),
          z ∈ modelCenter S e → (c : G) = z * y → θt c = (eb.representation θ).character y := by
        intro c z y hz hc
        have hdc : d.symm c = (⟨z, hz⟩, y) := by
          apply d.injective
          rw [MulEquiv.apply_symm_apply]
          apply Subtype.ext
          rw [hd]
          exact hc
        change (eb.representation θ).character (d.symm c).2 = _
        rw [hdc]
      obtain ⟨ψ, hψ⟩ := exists_family_of_hom S e hnonab hn hη hord μ hμK _ hμχ θt hθt
      exact ⟨θt, fun c z y hz hc => hθt c z y ((hZ z).mp hz) hc, ψ, hψ⟩
  have hinfl : ∀ φ : qb.index, ∃ θ : eb.index, θ ∈ Ξ ∧
      (eb.representation θ).character = (qb.representation φ).character ∘ QuotientGroup.mk := by
    intro φ
    obtain ⟨μφ, hμφ⟩ := exists_hom_of_isMulCommutative qb φ
    let μ : E →* ℂˣ := μφ.comp (QuotientGroup.mk' K)
    obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible eb
      (lineRepresentation μ) (lineRepresentation_isIrreducible μ)
    have hχ : (eb.representation θ).character = (qb.representation φ).character ∘
        QuotientGroup.mk := by
      funext y
      rw [hθ, lineRepresentation_character, Function.comp_apply, ← hμφ]
      rfl
    refine ⟨θ, (hmem θ).mpr ⟨μ, fun y => ?_, ?_⟩, hχ⟩
    · rw [hχ, Function.comp_apply, ← hμφ]
      rfl
    · intro y hy
      have hq : (QuotientGroup.mk' K) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hq, map_one]
  choose F hFΞ hFχ using hinfl
  have hFinj : Function.Injective F := by
    intro φ φ' hφ
    apply qb.distinct
    funext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (qb.representation φ).character ∘ QuotientGroup.mk =
        (qb.representation φ').character ∘ QuotientGroup.mk := by
      rw [← hFχ φ, ← hFχ φ', hφ]
    exact congrFun h1 y
  let f' : qb.index → Ξ := fun φ => ⟨F φ, hFΞ φ⟩
  have hbij : Function.Bijective f' := by
    constructor
    · intro φ φ' hφ
      exact hFinj (congrArg Subtype.val hφ)
    · rintro ⟨θ, hθ⟩
      obtain ⟨μ, hμχ, hμK⟩ := (hmem θ).mp hθ
      let μbar : E ⧸ K →* ℂˣ := QuotientGroup.lift K μ hμK
      obtain ⟨φ, hφ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible qb
        (lineRepresentation μbar) (lineRepresentation_isIrreducible μbar)
      refine ⟨φ, Subtype.ext ?_⟩
      apply eb.distinct
      change (eb.representation (F φ)).character = (eb.representation θ).character
      rw [hFχ φ, hφ]
      funext y
      rw [Function.comp_apply, lineRepresentation_character, ← hμχ]
      rfl
  have hdeg : ∀ θ ∈ Ξ, (eb.representation θ).character 1 = 1 := by
    intro θ hθ
    obtain ⟨μ, hμχ, -⟩ := (hmem θ).mp hθ
    rw [← hμχ, map_one, Units.val_one]
  refine ⟨boundaryCommutator_le S e hn hη hord, oddCore_four_le_centralizer S e,
    boundaryProduct_le S e hn hη hord, boundaryProduct_normal S e η,
    coe_boundaryProduct S e hn hη hord, rfl, boundaryKernel_normal S e η,
    boundaryKernel_quotient_isMulCommutative S e η,
    ⟨Equiv.ofBijective f' hbij, fun φ => hFχ φ⟩, fun θ hθ => ⟨hdeg θ hθ, ?_⟩, ?_⟩
  · have h := hdeg θ hθ
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact_mod_cast h
  · rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofBijective f' hbij),
      Nat.card_eq_fintype_card, card_index_of_isMulCommutative qb]
    rfl

end CFSG.Wreathed.CompatibleFamilies
