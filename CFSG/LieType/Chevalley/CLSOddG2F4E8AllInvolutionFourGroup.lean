module

public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupSmallRee
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.LieType.Chevalley.OddG2F4E8AllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.LieType.Ree (ReeTag)

theorem exists_four_group_of_conj_fix {C : Type*} [Group C] {β γ ψ : MulAut C}
    (h : ∀ u, (ψ * β * ψ⁻¹) u = γ u) {A : Subgroup C} (hA : ∀ u ∈ A, γ u = u)
    (hAab : IsElementaryAbelian 2 A) (hAc : Nat.card A = 4) :
    ∃ V : Subgroup C, V ≤ fixedSubgroup β ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨A.map ψ⁻¹.toMonoidHom, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    change β (ψ⁻¹ u) = ψ⁻¹ u
    have h1 := h u
    rw [hA u hu, MulAut.mul_apply, MulAut.mul_apply] at h1
    calc β (ψ⁻¹ u) = ψ⁻¹ (ψ (β (ψ⁻¹ u))) := (MulAut.inv_apply_self C ψ _).symm
      _ = ψ⁻¹ u := by rw [h1]
  · rw [Subgroup.card_map_of_injective ψ⁻¹.injective]
    exact hAc

theorem isElementaryAbelian_of_isElemAbelian {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) : IsElementaryAbelian 2 A :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA

theorem exists_four_group_of_quadratic_field_coset
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hfe : Even f)
    (hf : 1 ≤ f) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ (f / 2))) (g : adjointGroup τ K)
    (a : Fin τ.rank → Kˣ) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ u, (β u : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hβ2 : β ^ 2 = 1) :
    ∃ V : Subgroup (adjointGroup τ K), V ≤ fixedSubgroup β ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := hfe
  have he : 1 ≤ f / 2 := by omega
  have hK' : Nat.card K = (p ^ (f / 2)) ^ 2 := by
    rw [hK, ← pow_mul]
    congr 1
    omega
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hK'
    σ.toRingHom hσ
  obtain ⟨β₀, hβ₀, hall⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hall g a
  obtain ⟨ψ, hψ, -⟩ := hconj β hβ (by rw [← sq]; exact hβ2)
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨A, hAC, hAab, hAc, hAσ, -⟩ := odd_chevalley_coordinate_fields_fixed_four_group τ hchar
  have := hAab
  refine exists_four_group_of_conj_fix (γ := β₀) (A := A.subgroupOf (adjointGroup τ K))
    (fun u => Subtype.ext ((hψ u).trans (hβ₀ u).symm)) (fun u hu => Subtype.ext ?_)
    (IsElementaryAbelian.subgroupOf hAC) ?_
  · rw [hβ₀]
    exact Units.ext (hAσ σ _ hu)
  · rw [← hAc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv

theorem exists_four_group_of_G2_exceptional_coset
    (b : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * b + 1))
    (g : adjointGroup ReeTag.G2.tag K)
    (hβ2 : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1) :
    ∃ V : Subgroup (adjointGroup ReeTag.G2.tag K),
      V ≤ fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ∧
        IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  obtain ⟨ψ, hψ⟩ := CFSG.LieType.Ree.G2_exceptional_coset_involution_conj b K hK g hβ2
  have : CharP (ZMod 3) ReeTag.G2.prime := ZMod.charP 3
  obtain ⟨-, -, -, A, -, hAΓ, hAab, hAc⟩ := small_Ree_prime_field_derived_fixed_four_group b K
    (ZMod 3) (Nat.card_zmod 3) (ZMod.castHom (dvd_refl 3) K)
  obtain ⟨-, -, -, hΓ, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_field_involution_fixed_p_components b K hK
  have hAC : A ≤ adjointGroup ReeTag.G2.tag K := fun x hx => by
    have hx' := hAΓ hx
    rw [← hΓ] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact y.2
  have hfix : ∀ u ∈ A.subgroupOf (adjointGroup ReeTag.G2.tag K),
      ReeTag.G2.finiteReeAut K b u = u := fun u hu => by
    have hx' := hAΓ hu
    rw [← hΓ] at hx'
    obtain ⟨y, hy, hyu⟩ := hx'
    have hyu' : y = u := Subtype.ext hyu
    rw [← hyu']
    exact hy
  have := isElementaryAbelian_of_isElemAbelian hAab
  refine exists_four_group_of_conj_fix (γ := ReeTag.G2.finiteReeAut K b)
    (A := A.subgroupOf (adjointGroup ReeTag.G2.tag K)) (fun u => by rw [hψ]) hfix
    (IsElementaryAbelian.subgroupOf hAC) ?_
  rw [← hAc]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv

theorem exists_four_group_G2_three
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f)
    (β : MulAut (adjointGroup ReeTag.G2.tag K)) (hβout : β ∉ inner (adjointGroup ReeTag.G2.tag K))
    (hβ2 : β ^ 2 = 1) :
    ∃ V : Subgroup (adjointGroup ReeTag.G2.tag K), V ≤ fixedSubgroup β ∧
      IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨-, hnf, -, hk, -, hEven, hOdd⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf β
  rcases hk β g k k.2 hgk hβ2 with hk0 | hkf
  · refine absurd ⟨g, ?_⟩ hβout
    rw [hgk, hk0, pow_zero, mul_one]
  · rw [hkf] at hgk
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨-, σ, -, -, hσ, -, hφσ⟩ := hEven hfe
      refine exists_four_group_of_quadratic_field_coset Nat.prime_three (by norm_num) hK hfe hf σ
        hσ g 1 β (fun u => ?_) hβ2
      rw [CFSG.LieType.Chevalley.rootDiagUnit_one, inv_one, mul_one, mul_one, hgk,
        MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hφσ]
    · obtain ⟨b, hb⟩ := hfo
      obtain ⟨-, hFb, -⟩ := hOdd b hb
      rw [hFb] at hgk
      subst hgk
      exact exists_four_group_of_G2_exceptional_coset b K (hb ▸ hK) g hβ2

theorem rootDiagAut_mem_inner_of_det_eq_one
    {τ : Tag} {K : Type} [Field K] [Finite K]
    (hdet : τ.cartan.det = 1) (a : Fin τ.rank → Kˣ) :
    rootDiagAut τ K a ∈ inner (adjointGroup τ K) := by
  have hidx := (index_range_monomialHom_dvd K τ.cartan.transpose).2
  rw [Matrix.det_transpose, hdet, Int.natAbs_one, Nat.dvd_one, Subgroup.index_eq_one] at hidx
  obtain ⟨t, ht⟩ : a ∈ (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Kˣ)
      τ.cartan.transpose).range := hidx ▸ Subgroup.mem_top a
  rw [← ht, monomialHom_transpose_cartan]
  exact rootDiagAut_cartanChar_mem_inner t

theorem _root_.CFSG.LieType.Chevalley.odd_G2_F4_E8_all_involution_fixed_four_group
    (L : Type)
    [Group L] [Finite L] [IsSimpleGroup L] (hLnab : ∃ a b : L, a * b ≠ b * a)
    (t : StatedLieTag) (ht : t = .G2 ∨ t = .F4 ∨ t = .E8) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : ChevalleyExceptionalModel L t p f) (α : MulAut L)
    (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  by_cases hin : α ∈ inner L
  · obtain ⟨g, rfl⟩ := hin
    exact exists_four_group_le_fixedSubgroup_conj hLnab g hα
  suffices H : ∀ (τ : Tag) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      (τ = .F4 ∨ τ = .G2 ∨ τ = .E8) → ∀ β : MulAut (adjointGroup τ K),
        β ∉ inner (adjointGroup τ K) → β ^ 2 = 1 →
        ∃ V : Subgroup (adjointGroup τ K), V ≤ fixedSubgroup β ∧ IsElementaryAbelian 2 V ∧
          Nat.card V = 4 by
    have key : ∃ τ : Tag, (τ = .F4 ∨ τ = .G2 ∨ τ = .E8) ∧
        UntwistedChevalleyModel L τ (p ^ f) := by
      obtain ⟨-, hm⟩ := hL
      rcases ht with rfl | rfl | rfl
      · exact ⟨.G2, Or.inr (Or.inl rfl), hm⟩
      · exact ⟨.F4, Or.inl rfl, hm⟩
      · exact ⟨.E8, Or.inr (Or.inr rfl), hm⟩
    obtain ⟨τ, hτ, hmτ⟩ := key
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hmτ
    have hβout : MulAut.congr e α ∉ inner (adjointGroup τ K) := fun h =>
      hin ((congr_mem_inner_iff e α).1 h)
    have hβ2 : MulAut.congr e α ^ 2 = 1 := by rw [← map_pow, hα, map_one]
    obtain ⟨V, hV, hVab, hVc⟩ := H τ K hK hτ _ hβout hβ2
    exact exists_four_group_le_fixedSubgroup_of_congr e α hV hVab hVc
  intro τ K _ _ hK hτ β hβout hβ2
  have hpK : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hF4G2 : (τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3)) →
      ∃ V : Subgroup (adjointGroup τ K), V ≤ fixedSubgroup β ∧ IsElementaryAbelian 2 V ∧
        Nat.card V = 4 := fun hτ' => by
    obtain ⟨hnf, Θ, hΘ, -, hker, hinv⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK τ hτ'
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf β
    have hΘβ := hΘ β g σ hgσ
    rcases hinv β hβ2 with h1 | ⟨hfe, hσ, -⟩
    · have h2 : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
      rw [hker] at h2
      exact absurd h2 hβout
    · rw [hΘβ] at hσ
      refine exists_four_group_of_quadratic_field_coset hp hp2 hK hfe hf σ hσ g 1 β
        (fun u => ?_) hβ2
      rw [hgσ u, CFSG.LieType.Chevalley.rootDiagUnit_one, inv_one, mul_one, mul_one]
  rcases hτ with rfl | rfl | rfl
  ·
    exact hF4G2 (Or.inl rfl)
  ·
    rcases eq_or_ne p 3 with rfl | hp3
    · have : CharP K ReeTag.G2.prime := hpK
      exact exists_four_group_G2_three hf K hK β hβout hβ2
    · exact hF4G2 (Or.inr ⟨rfl, hp3⟩)
  ·
    obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl)) K
    obtain ⟨g, a, σ, ε, hgaσ⟩ := hnf β
    obtain ⟨-, -, -, -, hsq, hquad⟩ :=
      ordinary_E_field_graph_quotient_and_involutions .E8 (Or.inr (Or.inr rfl)) K
    have hQ : exactQ Tag.E8 K ε = 1 := rfl
    have hβ' : ∀ u, (β u : ModGL Tag.E8 K) = (g : ModGL Tag.E8 K) * rootDiagUnit Tag.E8 a *
        Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.E8 K) * (rootDiagUnit Tag.E8 a)⁻¹ *
          (g : ModGL Tag.E8 K)⁻¹ := fun u => by
      rw [hgaσ u, hQ, inv_one, mul_one, mul_one]
    by_cases hσ1 : σ = 1
    ·
      subst hσ1
      obtain ⟨c, hc⟩ := rootDiagAut_mem_inner_of_det_eq_one det_cartan_E8 a (K := K)
      have h1 : ∀ u : adjointGroup Tag.E8 K,
          Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (u : ModGL Tag.E8 K) = u := fun u =>
        Units.ext (entrywise_id (R := K) _)
      have hβeq : β = MulAut.conj g * rootDiagAut Tag.E8 K a := MulEquiv.ext fun u =>
        Subtype.ext (by
          rw [hβ' u, h1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
            Subgroup.coe_inv, coe_rootDiagAut]
          group)
      exact (hβout ⟨g * c, by rw [map_mul, hc, hβeq]⟩).elim
    · obtain ⟨hfe, hσ, -⟩ := hquad p f hp hf hK σ (hsq β g a σ ε hgaσ hβ2) hσ1
      exact exists_four_group_of_quadratic_field_coset hp hp2 hK hfe hf σ hσ g a β hβ' hβ2

end CFSG.LieType.Chevalley.OddG2F4E8AllInvolution
