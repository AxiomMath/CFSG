module

public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem isElemAbelian_two_map {G H : Type*} [Group G] [Group H] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (f : G →* H) : CFSG.Open.IsElemAbelian 2 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem exists_ne_comm_of_commutator_eq {G : Type*} [Group G] {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) [Nontrivial J] : ∃ x y : J, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hbot : ⁅J, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hJ] at hbot
  exact (Subgroup.nontrivial_iff_ne_bot J).1 inferInstance hbot

theorem exists_four_le_eqLocus_of_derived {G : Type*} [Group G] {C J : Subgroup G}
    (hJC : J ≤ C) [Finite J] [IsSimpleGroup J] (hnc : ∃ x y : J, x * y ≠ y * x)
    {α β ψ : MulAut C}
    (hψ : (α.toMonoidHom.eqLocus (MonoidHom.id C)).map ψ.toMonoidHom =
      β.toMonoidHom.eqLocus (MonoidHom.id C))
    (hJ : ⁅β.toMonoidHom.eqLocus (MonoidHom.id C), β.toMonoidHom.eqLocus (MonoidHom.id C)⁆ =
      J.subgroupOf C) :
    ∃ A : Subgroup C, A ≤ α.toMonoidHom.eqLocus (MonoidHom.id C) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  have hZ : Odd (Nat.card (Subgroup.center J)) := by
    rw [center_eq_bot_of_isSimpleGroup hnc, Subgroup.card_bot]
    exact odd_one
  obtain ⟨A₀, hA₀, hcard₀⟩ := exists_four_group_of_two_le_pRank
    (two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hnc) hZ)
  let ι : J →* C := Subgroup.inclusion hJC
  have hι : Function.Injective ι := Subgroup.inclusion_injective hJC
  have hA₁ : A₀.map ι ≤ β.toMonoidHom.eqLocus (MonoidHom.id C) := by
    rintro _ ⟨y, -, rfl⟩
    have hy : ι y ∈ J.subgroupOf C := Subgroup.mem_subgroupOf.2 y.2
    rw [← hJ] at hy
    exact Subgroup.commutator_le_self _ hy
  refine ⟨(A₀.map ι).map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := hA₁ hx
    rw [← hψ] at hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    simpa using hz
  · exact isElemAbelian_two_map (isElemAbelian_two_map hA₀ ι) _
  · rw [Subgroup.card_map_of_injective ψ.symm.injective, Subgroup.card_map_of_injective hι,
      hcard₀]

theorem even_E6_field_involution_fixed_four_group_of_expr
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup Tag.E6 K)) (hα : α ^ 2 = 1)
    (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
    (ε : Fin (exactE Tag.E6))
    (hexpr : ∀ h : adjointGroup Tag.E6 K, (α h : ModGL Tag.E6 K) =
      (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.E6 K) * (exactQ Tag.E6 K ε)⁻¹ *
          (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹)
    (hσ : σ ≠ 1) :
    ∃ A : Subgroup (adjointGroup Tag.E6 K), A ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hσ2 : σ ^ 2 = 1 := hsq α g a σ ε hexpr hα
  obtain ⟨hfe, hσc, -⟩ := hfacts 2 f Nat.prime_two hf hK σ hσ2 hσ
  obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
  have he : 1 ≤ e := by omega
  have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
    rw [hσc, Nat.mul_div_cancel_left e two_pos]
  have hαα : α * α = 1 := by rw [← sq]; exact hα
  obtain ⟨hD0, hD1⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he K hK σ.toRingHom hσe
  obtain ⟨hJ0, hJ1⟩ := even_E6_canonical_field_graph_field_derived_fixed_subgroups he K hK σ hσe
  obtain ⟨ε, hε⟩ := ε
  have hε' : ε = 0 ∨ ε = 1 := by
    change ε < 2 at hε
    omega
  rcases hε' with rfl | rfl
  ·
    have hQ0 : exactQ Tag.E6 K ((⟨0, hε⟩ : Fin (exactE Tag.E6)) : ℕ) = 1 := pow_zero _
    obtain ⟨β, hβ, hβα⟩ := hD0 Tag.E6
    obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 α (fun u => by
      have h := hexpr u
      rw [hQ0, mul_one, inv_one, mul_one] at h
      exact h) hαα
    obtain ⟨-, hJC, hder, hfin, hsimp, -⟩ := hJ0
    have hβδ : diagramConjAut TwistTag.E6 K ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ = β :=
      MulEquiv.ext fun u => Subtype.ext ((coe_entrywiseAdjointAut _ σ u).trans (hβ u).symm)
    rw [← hβδ] at hψ
    have hperf : ⁅fixedFieldImage TwistTag.E6.tag σ, fixedFieldImage TwistTag.E6.tag σ⁆ =
        fixedFieldImage TwistTag.E6.tag σ := by
      rw [fixedFieldImage, ← Subgroup.map_commutator,
        commutator_adjointGroup_eq_of_single_edge (τ := TwistTag.E6.tag)
          (Or.inr (Or.inr (Or.inl rfl)))]
    exact exists_four_le_eqLocus_of_derived hJC (exists_ne_comm_of_commutator_eq hperf) hψ hder
  ·
    have hQ1 : exactQ Tag.E6 K ((⟨1, hε⟩ : Fin (exactE Tag.E6)) : ℕ) = diagramMap TwistTag.E6 K :=
      pow_one _
    obtain ⟨β, hβ, hβα⟩ := hD1
    obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 α (fun u => by
      have h := hexpr u
      rw [hQ1] at h
      exact h) hαα
    obtain ⟨-, hJC, hder, hfin, hsimp, -⟩ := hJ1
    have hβγδ : diagramConjAut TwistTag.E6 K ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ = β :=
      MulEquiv.ext fun u => Subtype.ext (((coe_diagramConjAut TwistTag.E6 K
        (entrywiseAdjointAut TwistTag.E6.tag σ u)).trans
          (by rw [coe_entrywiseAdjointAut])).trans (hβ u).symm)
    rw [← hβγδ] at hψ
    have hK' : Nat.card K = (2 ^ e) ^ TwistTag.E6.order := by
      rw [hK, ← pow_mul, mul_comm]
      rfl
    obtain ⟨-, ⟨x, hx, y, hy, hxy⟩, -⟩ :=
      finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two he K hK' σ.toRingHom hσe
    exact exists_four_le_eqLocus_of_derived hJC
      ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩ hψ hder

theorem even_E6_nontrivial_field_involution_fixed_four_group
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f)
    (Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)))
    (hΘ : ∀ (α : MulAut (adjointGroup Tag.E6 K)) (g : adjointGroup Tag.E6 K)
      (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE Tag.E6)),
      (∀ h : adjointGroup Tag.E6 K, (α h : ModGL Tag.E6 K) =
        (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.E6 K) * (exactQ Tag.E6 K ε)⁻¹ *
            (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹) →
      Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE Tag.E6))))
    (α : MulAut (adjointGroup Tag.E6 K)) (hα : α ^ 2 = 1) (hσ : (Θ α).1 ≠ 1) :
    ∃ A : Subgroup (adjointGroup Tag.E6 K), A ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, hexist⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist α
  rw [hΘ α g a σ ε hexpr] at hσ
  exact even_E6_field_involution_fixed_four_group_of_expr hf K hK α hα g a σ ε hexpr hσ

end CFSG.LieType.Chevalley
