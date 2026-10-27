module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
public import CFSG.Walter.Ree.Model.Fusion

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model

theorem isPGroup_center_of_mulEquiv_simple {L J : Type*} [Group L] [Group J] [IsSimpleGroup J]
    (hL : IsQuasisimple L) (E : L ≃* J) : IsPGroup 2 (center L) := by
  obtain ⟨-, hZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup
    (exists_mul_ne_of_isQuasisimple hL E)
  refine isPGroup_center_of_center_eq_bot ?_
  rw [← Subgroup.map_center_eq E.symm, hZ, Subgroup.map_bot]

theorem oddReeA6Form_holds
    :
    ∀ (J : Type) [Group J] (f : ℕ), StatedLieAdmissible .twistedG2 0 3 f →
      Blueprint.LieModel J .twistedG2 0 3 f → ∀ α : MulAut J, orderOf α = 2 →
        A6CentreForm (fixedSubgroup α) := by
  intro J _ f hadm hm α hα L hL
  suffices h : IsPGroup 2 (center L) from fun _ => h
  have hR : ReeTitsModel J .twistedG2 3 f := by
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier J 3 f hR
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hR
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  set Γ := ReeTag.G2.reeGamma K a' with hΓ
  set β := MulAut.congr E α with hβ
  have hβ2 : orderOf β = 2 :=
    (orderOf_injective (MulAut.congr E).toMonoidHom (MulAut.congr E).injective α).trans hα
  obtain ⟨-, -, -, -, hoddO, -⟩ := small_Ree_outer_three_kernel_field_complement a' ha K hK'
  have hinn : β ∈ OuterAutomorphisms.inner Γ := by
    have : Finite (OuterAutomorphisms.Outer Γ) := Nat.finite_of_card_ne_zero hoddO.pos.ne'
    have hx2 : (QuotientGroup.mk β : OuterAutomorphisms.Outer Γ) ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one β
      rw [hβ2] at h1
      rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
    have hdvd := orderOf_dvd_natCard (QuotientGroup.mk β : OuterAutomorphisms.Outer Γ)
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx2) with h | h
    · exact (QuotientGroup.eq_one_iff β).1 (orderOf_eq_one_iff.1 h)
    · rw [h] at hdvd
      exact absurd (even_iff_two_dvd.2 hdvd) (Nat.not_even_iff_odd.2 hoddO)
  obtain ⟨t₀, ht₀⟩ := hinn
  have hZ := ReeTag.center_reeGamma_G2_eq_bot (a := a') hK'
  have hcj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : x * y * x⁻¹ = y := DFunLike.congr_fun ((MonoidHom.mem_ker).1 hx) y
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have ht₂ : orderOf (t₀ : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective _ hcj t₀, ht₀]
    exact hβ2
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a' K hK' w₀ hw₀).2.2.2.2.2 t₀ t₀.2 ht₂
  set C := smallReeInvCentralizer a' K with hCdef
  have hCmap : (Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)}).map
      (MulAut.conj g).toMonoidHom = C := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
      LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgΓ),
      LocalAnalysis.ComponentInitial.map_centralizer_singleton, MulAut.conj_apply, hgt]
    rfl
  have hfixmap : (fixedSubgroup (MulAut.conj t₀)).map Γ.subtype =
      Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)} := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      have hc' : t₀ * c * t₀⁻¹ = c := hc
      have hcx : c * t₀ = t₀ * c := by
        calc c * t₀ = t₀ * c * t₀⁻¹ * t₀ := by rw [hc']
          _ = t₀ * c := by group
      exact congrArg Subtype.val hcx
    · rintro ⟨hzΓ, hz⟩
      refine ⟨⟨z, hzΓ⟩, ?_, rfl⟩
      change t₀ * ⟨z, hzΓ⟩ * t₀⁻¹ = ⟨z, hzΓ⟩
      have hcx : (⟨z, hzΓ⟩ : Γ) * t₀ = t₀ * ⟨z, hzΓ⟩ := Subtype.ext hz
      calc t₀ * ⟨z, hzΓ⟩ * t₀⁻¹ = ⟨z, hzΓ⟩ * t₀ * t₀⁻¹ := by rw [hcx]
        _ = ⟨z, hzΓ⟩ := by group
  let Ψ : fixedSubgroup α ≃* C :=
    (fixedSubgroupCongrEquiv E α).trans
      ((MulEquiv.subgroupCongr (congrArg fixedSubgroup ht₀.symm)).trans
        ((((fixedSubgroup (MulAut.conj t₀)).equivMapOfInjective Γ.subtype
          Γ.subtype_injective).trans (MulEquiv.subgroupCongr hfixmap)).trans
          (((Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)}).equivMapOfInjective
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
            (MulEquiv.subgroupCongr hCmap))))
  obtain ⟨ψ, hψC, -, -, -, -, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a' K hK' w₀ hw₀
  set h := smallReeH a' K (-1)
  rw [← hCdef] at hsup
  simp only [← hCdef] at hψC
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact hψC x
  have htC : h ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (Subgroup.zpowers (⟨h, htC⟩ : C)).subtype) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hc : c ∈ (Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N : Subgroup C) := hT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨x, hx, n, hn, rfl⟩ := hc
    refine ⟨⟨x, hx⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    change QuotientGroup.mk' N x = QuotientGroup.mk' N (x * n)
    rw [map_mul, hn1, mul_one]
  have : IsCyclic (C ⧸ N) := isCyclic_of_surjective _ hsurj
  have hsolv : Group.IsSolvable (C ⧸ N) :=
    Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK']
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr hK2) (Or.inr hK3)
  have : IsSimpleGroup ψ.range := e.symm.isSimpleGroup
  obtain ⟨eL⟩ := nonempty_component_equiv_of_normal_simple hLC hNn hsolv Ψ hL
  exact isPGroup_center_of_mulEquiv_simple hL.1 eL

theorem oddTrialityOuterA6Form_holds
    :
    ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .trialityD4 0 p f →
      Blueprint.LieModel J .trialityD4 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∉ (MulAut.conj : J →* MulAut J).range → A6CentreForm (fixedSubgroup α) := by
  intro J _ p f hp hp2 hadm hm α hα hαo L hL
  suffices h : IsPGroup 2 (center L) from fun _ => h
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  set C := graphFixedRootGroup TwistTag.D4 M σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβo : β ∉ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∉ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hex β
  have hΘβ : Θ β = δ := hΘ β g δ hgδ
  rcases hinv β hβ2 with h1 | ⟨⟨e', he'⟩, hδc⟩
  · exact absurd (hker ▸ (MonoidHom.mem_ker.mpr h1)) hβo
  have he1 : 1 ≤ e' := by omega
  have hδ : ∀ c, δ c = c ^ p ^ (3 * e') := fun c => by
    rw [← hΘβ, hδc, show 3 * f / 2 = 3 * e' by omega]
  have hr : IsPrimePow (p ^ e') := hp.isPrimePow.pow (by omega)
  have hro : Odd (p ^ e') := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hM3 : Nat.card M = (p ^ f) ^ 3 := hM
  have hM6 : Nat.card M = (p ^ e') ^ 6 := by
    rw [hM3, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hσ2 : ∀ c, σ c = c ^ ((p ^ e') ^ 2) := fun c => by
    rw [hσ, show f = e' * 2 by omega, pow_mul]
  have hδ3 : ∀ c, δ c = c ^ ((p ^ e') ^ 3) := fun c => by
    rw [hδ, ← pow_mul, mul_comm]
  have hα2 : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 := hgδ ▸ hβ2
  obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components hr hro M hM6 σ
    hσ2 δ hδ3 g hα2
  have hM6' : Nat.card M = p ^ (3 * e' * 2) := by
    rw [hM3, ← pow_mul]
    congr 1
    omega
  have hσ' : ∀ c, σ c = c ^ p ^ (e' * 2) := fun c => by
    rw [hσ, show f = e' * 2 by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, hsimple, hnab, -⟩ :=
    RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp he1
      (le_refl 2) (by norm_num : Nat.Coprime 2 3) M hM6' σ hσ' δ hδ
  have hc : MulAut.congr ψ β = fieldActor σ δ := by
    rw [show MulAut.congr ψ β = ψ * β * ψ⁻¹ from MulEquiv.ext fun _ => rfl, hgδ]
    exact hψ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      (trialityFieldImage σ δ).subgroupOf C := by
    change _ = (trialityFieldImage σ δ).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have hFc : fixedSubgroup (MulAut.congr ψ β) = (trialityFieldImage σ δ).subgroupOf C := by
    rw [hc, hF]
  let Ψ : fixedSubgroup α ≃* trialityFieldImage σ δ :=
    ((fixedSubgroupCongrEquiv e α).trans (fixedSubgroupCongrEquiv ψ β)).trans
      ((MulEquiv.subgroupCongr hFc).trans (Subgroup.subgroupOfEquivOfLe hJC))
  have : IsSimpleGroup (trialityFieldImage σ δ) := hsimple
  obtain ⟨E⟩ := nonempty_component_equiv_of_simple Ψ hL
  exact isPGroup_center_of_mulEquiv_simple hL.1 E

end CFSG.ComponentClassification.CatLeafProof
