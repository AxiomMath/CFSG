module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddLinear
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalUniversalPairExclusion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LieType.Universal.Spin.Forms

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddOrthogonal

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open TauCeti.QuadraticMap (orthogonalGroup)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem commutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] def toOrth (hQ : ⇑Q = Q₀) : StatedOmega Q₀ →* orthogonalGroup Q :=
  ((toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q₀).subtype).codRestrict _ fun A => by
    have h : (A : GL ι K) ∈ ⁅orthogonalGroup Q, orthogonalGroup Q⁆.comap
        (toLinEquiv ι K).toMonoidHom := by
      rw [← statedOmega_eq_comap hQ]
      exact A.2
    exact commutator_self_le _ (Subgroup.mem_comap.1 h)

theorem coe_toOrth (hQ : ⇑Q = Q₀) (A : StatedOmega Q₀) :
    ((toOrth hQ A : orthogonalGroup Q) : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A :=
  rfl

theorem range_toOrth (hQ : ⇑Q = Q₀) :
    (toOrth hQ).range = commutator (orthogonalGroup Q) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    have h : (A : GL ι K) ∈ ⁅orthogonalGroup Q, orthogonalGroup Q⁆.comap
        (toLinEquiv ι K).toMonoidHom := by
      rw [← statedOmega_eq_comap hQ]
      exact A.2
    have h2 : ((toOrth hQ A : orthogonalGroup Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈
        (commutator (orthogonalGroup Q)).map (orthogonalGroup Q).subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact Subgroup.mem_comap.1 h
    obtain ⟨x, hx, hxe⟩ := h2
    rw [← Subtype.ext hxe]
    exact hx
  · intro hg
    have h1 : (g : (ι → K) ≃ₗ[K] (ι → K)) ∈ ⁅orthogonalGroup Q, orthogonalGroup Q⁆ := by
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨g, hg, rfl⟩
    have h2 : (toLinEquiv ι K).symm g ∈ StatedOmega Q₀ := by
      rw [statedOmega_eq_comap hQ, Subgroup.mem_comap]
      change toLinEquiv ι K ((toLinEquiv ι K).symm g) ∈ _
      rw [MulEquiv.apply_symm_apply]
      exact h1
    refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
    change toLinEquiv ι K ((toLinEquiv ι K).symm g) = g
    rw [MulEquiv.apply_symm_apply]

section Proj

variable (hQ : ⇑Q = Q₀) (Z : Subgroup (orthogonalGroup Q)) [Z.Normal]

@[expose] def toProj : StatedOmega Q₀ →* orthogonalGroup Q ⧸ Z :=
  (QuotientGroup.mk' Z).comp (toOrth hQ)

variable {hQ Z}

theorem ker_toProj
    (hZ : ∀ g : orthogonalGroup Q, g ∈ Z ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : (ι → K) ≃ₗ[K] (ι → K)) v = c • v)
    (hQne : ∃ v, Q v ≠ 0) :
    (toProj hQ Z).ker = (StatedScalars ι K).subgroupOf (StatedOmega Q₀) := by
  ext A
  rw [MonoidHom.mem_ker, toProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hZ, Subgroup.mem_subgroupOf, mem_statedScalars_iff, mem_scalars]
  simp only [coe_toOrth]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    obtain ⟨v, hv⟩ := hQne
    have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (toOrth hQ A).2 v
    rw [coe_toOrth, hc, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h2 : (c * c - 1) * Q v = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hv)

variable (hQ Z) in
@[expose] def projEmbed
    (hZ : ∀ g : orthogonalGroup Q, g ∈ Z ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : (ι → K) ≃ₗ[K] (ι → K)) v = c • v)
    (hQne : ∃ v, Q v ≠ 0) : StatedProj (StatedOmega Q₀) →* orthogonalGroup Q ⧸ Z :=
  (QuotientGroup.kerLift (toProj hQ Z)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_toProj hZ hQne).symm).toMonoidHom

theorem projEmbed_mk
    (hZ : ∀ g : orthogonalGroup Q, g ∈ Z ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : (ι → K) ≃ₗ[K] (ι → K)) v = c • v)
    (hQne : ∃ v, Q v ≠ 0) (A : StatedOmega Q₀) :
    projEmbed hQ Z hZ hQne (QuotientGroup.mk A) = toProj hQ Z A := by
  rw [projEmbed, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]

theorem projEmbed_injective
    (hZ : ∀ g : orthogonalGroup Q, g ∈ Z ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : (ι → K) ≃ₗ[K] (ι → K)) v = c • v)
    (hQne : ∃ v, Q v ≠ 0) : Function.Injective (projEmbed hQ Z hZ hQne) := by
  rw [projEmbed, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (QuotientGroup.kerLift_injective _).comp (MulEquiv.injective _)

theorem projEmbed_range_normal
    (hZ : ∀ g : orthogonalGroup Q, g ∈ Z ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : (ι → K) ≃ₗ[K] (ι → K)) v = c • v)
    (hQne : ∃ v, Q v ≠ 0) : (projEmbed hQ Z hZ hQne).range.Normal := by
  have h : (projEmbed hQ Z hZ hQne).range = (toProj hQ Z).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H A => exact ⟨A, (projEmbed_mk hZ hQne A).symm⟩
    · rintro ⟨A, rfl⟩
      exact ⟨QuotientGroup.mk A, projEmbed_mk hZ hQne A⟩
  rw [h, toProj, MonoidHom.range_comp, range_toOrth]
  have hN : (commutator (orthogonalGroup Q)).Normal := by
    rw [commutator_def]
    infer_instance
  exact hN.map _ (QuotientGroup.mk'_surjective Z)

open Subgroup CFSG.ComponentClassification in
theorem not_nonempty_equiv_of_pair_exclusion {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G))
    (hQ : ⇑Q = Q₀) (Z : Subgroup (orthogonalGroup Q)) [Z.Normal]
    (hZ : ∀ g : orthogonalGroup Q, g ∈ Z ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : (ι → K) ≃ₗ[K] (ι → K)) v = c • v)
    (hQne : ∃ v, Q v ≠ 0)
    (hpair : ¬ ∃ B₁ B₂ : Subgroup (orthogonalGroup Q ⧸ Z),
      CFSG.Assembly.IsQuasisimple B₁ ∧ CFSG.Assembly.IsQuasisimple B₂ ∧ ⁅B₁, B₂⁆ = ⊥ ∧
      (∃ V₁ : Subgroup (orthogonalGroup Q ⧸ Z), V₁ ≤ B₁ ∧ CFSG.IsElementaryAbelian 2 V₁ ∧
        Nat.card V₁ = 4) ∧
      (∃ V₂ : Subgroup (orthogonalGroup Q ⧸ Z), V₂ ≤ B₂ ∧ CFSG.IsElementaryAbelian 2 V₂ ∧
        Nat.card V₂ = 4) ∧
      (∀ t ∈ B₂, orderOf t = 2 → CFSG.Assembly.IsComponentOf B₁
        (centralizer ({t} : Set (orthogonalGroup Q ⧸ Z)))) ∧
      (∀ s ∈ B₁, orderOf s = 2 → CFSG.Assembly.IsComponentOf B₂
        (centralizer ({s} : Set (orthogonalGroup Q ⧸ Z))))) :
    ¬ Nonempty (L ⧸ center L ≃* StatedProj (StatedOmega Q₀)) := by
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  let ψ : L ⧸ center L →* orthogonalGroup Q ⧸ Z := (projEmbed hQ Z hZ hQne).comp e.toMonoidHom
  have hψ : Function.Injective ψ := by
    change Function.Injective ((projEmbed hQ Z hZ hQne).comp e.toMonoidHom)
    rw [MonoidHom.coe_comp]
    exact (projEmbed_injective hZ hQne).comp e.injective
  have hψrange : ψ.range.Normal := by
    have h : ψ.range = (projEmbed hQ Z hZ hQne).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map]
    rw [h]
    exact projEmbed_range_normal hZ hQne
  have hfour : ∀ K ∈ block J, ∃ V : Subgroup (orthogonalGroup Q ⧸ Z),
      V ≤ (centerQuotientImage L K).map ψ ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
    intro K hK
    obtain ⟨V, hVK, hVe, hVc⟩ :=
      exists_four_group_centerQuotientImage hV hK.1 ((le_blockGroup hK).trans hML) hodd
    exact ⟨V.map ψ, Subgroup.map_mono hVK, CFSG.IsElementaryAbelian.map ψ,
      by rw [Subgroup.card_map_of_injective hψ, hVc]⟩
  have hlocal : ∀ K ∈ block J, ∀ K' ∈ block J, K ≠ K' →
      ∀ t ∈ (centerQuotientImage L K').map ψ, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf ((centerQuotientImage L K).map ψ)
          (centralizer ({t} : Set (orthogonalGroup Q ⧸ Z))) := by
    intro K hK K' hK' hKK' t ht ht2
    obtain ⟨w, hw, rfl⟩ := ht
    rw [orderOf_injective ψ hψ] at ht2
    obtain ⟨t₀, ht₀K, ht₀2, rfl⟩ := exists_involution_lift_of_odd_center hodd hw ht2
    have h := (isComponentOf_map_iff hψ).2 (hloc K hK K' hK' hKK' t₀ ht₀K ht₀2).2
    rw [map_centralizer_singleton_of_injective hψ] at h
    exact isComponentOf_of_normal_inf hψrange h
  exact hpair ⟨_, _, isQuasisimple_map_of_injective hψ (hπKq K₁ hK₁).1,
    isQuasisimple_map_of_injective hψ (hπKq K₂ hK₂).1,
    by rw [← Subgroup.map_commutator, (hcomm K₁ hK₁ K₂ hK₂ hne).2, Subgroup.map_bot],
    hfour K₁ hK₁, hfour K₂ hK₂, hlocal K₁ hK₁ K₂ hK₂ hne, hlocal K₂ hK₂ K₁ hK₁ (Ne.symm hne)⟩

end Proj

theorem mem_orthSigns_iff_scalar {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (g : orthogonalGroup Q) :
    g ∈ ProjectiveOrthogonal.orthSigns Q ↔
      ∃ c : K, c * c = 1 ∧ ∀ v, (g : V ≃ₗ[K] V) v = c • v := by
  rw [ProjectiveOrthogonal.mem_orthSigns]
  constructor
  · rintro (h | h)
    · exact ⟨1, one_mul 1, fun v => by rw [h, one_smul]⟩
    · exact ⟨-1, by ring, fun v => by rw [h, neg_one_smul]⟩
  · rintro ⟨c, hc, hgc⟩
    rcases mul_self_eq_one_iff.1 hc with rfl | rfl
    · exact Or.inl fun v => by rw [hgc, one_smul]
    · exact Or.inr fun v => by rw [hgc, neg_one_smul]

open Subgroup CFSG.ComponentClassification in
theorem not_nonempty_equiv_of_form {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hQ : ⇑Q = Q₀)
    (hnd : Q.polarBilin.Nondegenerate) (hι : 5 ≤ Fintype.card ι) :
    ¬ Nonempty (L ⧸ center L ≃* StatedProj (StatedOmega Q₀)) := by
  have hd : 5 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hι
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  exact not_nonempty_equiv_of_pair_exclusion hq heven hV hJ hΔ hL hML hLH hQ
    (ProjectiveOrthogonal.orthSigns Q) mem_orthSigns_iff_scalar
    (ProjectiveOrthogonal.exists_ne_zero_of_nondegenerate hnd)
    (ProjectiveOrthogonal.odd_projective_orthogonal_commuting_universal_pair_exclusion hp hp2 hf
      hK hd hnd)

end CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddOrthogonal

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus
  coe_quadMinus nondegenerate_polarBilin_quadOdd nondegenerate_polarBilin_quadPlus
  nondegenerate_polarBilin_quadMinus_of_finite)
open EscapingNotOddOrthogonal

theorem commuting_block_odd_orthogonal_overgroup_exclusion {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ) (hp : p ≠ 2) :
    ¬ StatedClassicalModel (L ⧸ center L) t n p f := by
  rcases ht with rfl | rfl | rfl
  · rintro ⟨⟨hpp, hf, hn, -⟩, K, _, _, hK, he⟩
    have : CharP K p := finite_field_prime_power_characteristic hpp hf hK
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
    exact not_nonempty_equiv_of_form hq heven hV hJ hΔ hL hML hLH hpp hp hf hK
      (coe_quadOdd n K) (nondegenerate_polarBilin_quadOdd n K h2)
      (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega) he
  · rintro ⟨⟨hpp, hf, hn⟩, K, _, _, hK, he⟩
    exact not_nonempty_equiv_of_form hq heven hV hJ hΔ hL hML hLH hpp hp hf hK
      (coe_quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) he
  · rintro ⟨⟨hpp, hf, hn⟩, K, _, _, hK, b, c, hirr, he⟩
    exact not_nonempty_equiv_of_form hq heven hV hJ hΔ hL hML hLH hpp hp hf hK
      (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) he

end CFSG.LocalAnalysis.ComponentInitial
