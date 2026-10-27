module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6CaseLQuot
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6CaseLEleven
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6CaseL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6XiExclusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)
open CFSG.LocalAnalysis.ComponentInitial (index_center_eq_of_mulEquiv)


section Lambda

theorem natCard_fixSubgroup_xi_twistedE6_two {k : Type} [Field k] [Finite k] (σ : k →+* k)
    (hk : Nat.card k = 4) (hσ : ∀ c, σ c = c ^ 2)
    {η : MulAut (graphFixedRootGroup TwistTag.E6 k σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 k σ, (η h : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹)
    (hx : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 k σ) :
    Nat.card (E6Pilot.fixSubgroup
        (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 k σ) * η)) =
      (2 ^ 1) ^ 24 * (((2 ^ 1) ^ 2 - 1) * ((2 ^ 1) ^ 4 - 1) * ((2 ^ 1) ^ 6 - 1)) := by
  have hk' : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ c
  have hkG : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  have := charP_two_of_natCard_eq_two_pow hkG
  have : Finite (GaloisField 2 1) := finite_of_natCard_eq_two_pow hkG
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card le_rfl hkG hk'
  let _ : Algebra (GaloisField 2 1) k := ι.toAlgebra
  obtain ⟨ht, -, -, -, -, ⟨eJ, -, heJ, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup 1 le_rfl (GaloisField 2 1) k hkG hk' σ hσ1
  obtain ⟨htJ, hcard⟩ := natCard_fixSubgroup_of_secondGraph hsec hη hx
  rw [hcard]
  obtain ⟨c, hcC, hc⟩ := exists_conj_e6FixedToF4_highRoot_eq_yRep_t ht
  have h1 : (⟨c, hcC⟩ : adjointGroup .F4 (GaloisField 2 1)) * eJ ⟨_, htJ⟩ *
      (⟨c, hcC⟩ : adjointGroup .F4 (GaloisField 2 1))⁻¹ = yRep (GaloisField 2 1) .t := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [heJ htJ]
    exact hc
  rw [← natCard_centralizer_conj ⟨c, hcC⟩ (eJ ⟨_, htJ⟩), h1]
  exact natCard_centralizer_yRep_of_ne_tu le_rfl hkG (by decide)

theorem natCard_map_perfectCore_of_xi_twistedE6 {G : Type} [Group G] [Finite G] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {k : Type} [Field k] [Finite k]
    (σ : k →+* k) (hk : Nat.card k = 4) (hσ : ∀ c, σ c = c ^ 2) {M : Subgroup G}
    (hZM : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 k σ)
    {t : G} (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G))
    {η : MulAut (graphFixedRootGroup TwistTag.E6 k σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 k σ, (η h : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹)
    (hx : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 k σ)
    {φ : MulAut (graphFixedRootGroup TwistTag.E6 k σ)}
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η) :
    Nat.card ((perfectCore ((centralizer ({t} : Set G)).subgroupOf M)).map
        (QuotientGroup.mk' (center M))) =
      Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) := by
  have hperfA := fixSubgroup_perfect_of_conj hφ (commutator_fixSubgroup_xi_twistedE6_two σ hk hσ hη hx)
  have hmapΛ := map_perfectCore_subgroupOf_centralizer_eq hZM eM ht htM hperfA
  have hfixmap := map_eqLocus_eq_of_conj hφ
  have hfixA : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) =
      (2 ^ 1) ^ 24 * (((2 ^ 1) ^ 2 - 1) * ((2 ^ 1) ^ 4 - 1) * ((2 ^ 1) ^ 6 - 1)) := by
    rw [← card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    change Nat.card (((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus
      (MonoidHom.id _)).map φ.toMonoidHom) = _
    rw [hfixmap]
    exact natCard_fixSubgroup_xi_twistedE6_two σ hk hσ hη hx
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  rw [natCard_centralizer_yRep_of_ne_tu le_rfl hK1 (by decide), ← hfixA, ← hmapΛ,
    ← Subgroup.map_map, card_map_of_injective (f := eM.toMonoidHom) eM.injective]

end Lambda

section Aux

theorem exists_mulEquiv_of_quotEquiv {G : Type*} [Group G] [Finite G] {M G₀ Λ : Subgroup G}
    (hΛM : Λ ≤ M) (hΛG₀ : Λ ≤ G₀) (χ : M ⧸ center M ≃* G₀ ⧸ center G₀)
    (hM : Function.Injective ((QuotientGroup.mk' (center M)).comp (Subgroup.inclusion hΛM)))
    (h₀ : Function.Injective ((QuotientGroup.mk' (center G₀)).comp (Subgroup.inclusion hΛG₀)))
    (hincl : ∀ l : Λ, χ.symm (QuotientGroup.mk' (center G₀) (Subgroup.inclusion hΛG₀ l)) ∈
      ((QuotientGroup.mk' (center M)).comp (Subgroup.inclusion hΛM)).range) :
    ∃ θ : Λ ≃* Λ, ∀ l : Λ, QuotientGroup.mk' (center M) (Subgroup.inclusion hΛM (θ l)) =
      χ.symm (QuotientGroup.mk' (center G₀) (Subgroup.inclusion hΛG₀ l)) := by
  set fM := (QuotientGroup.mk' (center M)).comp (Subgroup.inclusion hΛM) with hfMdef
  set f₀ := (QuotientGroup.mk' (center G₀)).comp (Subgroup.inclusion hΛG₀) with hf₀def
  set θ₁ : Λ →* fM.range := (χ.symm.toMonoidHom.comp f₀).codRestrict fM.range hincl
    with hθ₁def
  set θ : Λ →* Λ := (MonoidHom.ofInjective hM).symm.toMonoidHom.comp θ₁ with hθdef
  have hθ : ∀ l : Λ, fM (θ l) = χ.symm (f₀ l) := by
    intro l
    change fM ((MonoidHom.ofInjective hM).symm (θ₁ l)) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    have h1 : fM (θ a) = fM (θ b) := by rw [hab]
    rw [hθ, hθ] at h1
    exact h₀ (χ.symm.injective h1)
  exact ⟨MulEquiv.ofBijective θ ⟨hθinj, Finite.injective_iff_surjective.1 hθinj⟩, hθ⟩

theorem exists_root_of_mulEquiv_inf_centralizer {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hX₀ : Nat.card X₀ = 3)
    {w : G} (hwL : w ∈ L) {κ : TwoCentral} (hκtu : κ ≠ .tu) {c₁ : adjointGroup .F4 K}
    (hc₁ : c₁ * e ⟨w, hwL⟩ * c₁⁻¹ = yRep K κ) {Λ : Subgroup G} (hΛL : Λ ≤ L)
    (hΛw : Λ ≤ centralizer ({w} : Set G))
    (hΛcard : Nat.card Λ = Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))))
    (θΛ : Λ ≃* Λ) :
    ∃ (z : Λ) (c : adjointGroup .F4 K),
      (z : G) ∈ subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom) ∧ (z : G) ≠ 1 ∧
      (c₁ * e ⟨θΛ z, hΛL (θΛ z).2⟩ * c₁⁻¹ ∈ X₀.map (MulAut.conj c).toMonoidHom ∨
        c₁ * e ⟨θΛ z, hΛL (θΛ z).2⟩ * c₁⁻¹ ∈
          (X₀.map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hΨmem : ∀ l : Λ, (MulAut.conj c₁).toMonoidHom (e.toMonoidHom (Subgroup.inclusion hΛL l)) ∈
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) := by
    intro l
    change c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹ ∈ centralizer ({yRep K κ} : Set (adjointGroup .F4 K))
    rw [mem_centralizer_singleton_iff, ← hc₁]
    have h1 : (⟨l, hΛL l.2⟩ : L) * ⟨w, hwL⟩ = ⟨w, hwL⟩ * ⟨l, hΛL l.2⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw l.2))
    have h2 : e (⟨l, hΛL l.2⟩ * ⟨w, hwL⟩) = e (⟨w, hwL⟩ * ⟨l, hΛL l.2⟩) := congrArg e h1
    rw [e.map_mul, e.map_mul] at h2
    calc c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹ * (c₁ * e ⟨w, hwL⟩ * c₁⁻¹) =
        c₁ * (e ⟨l, hΛL l.2⟩ * e ⟨w, hwL⟩) * c₁⁻¹ := by group
      _ = c₁ * (e ⟨w, hwL⟩ * e ⟨l, hΛL l.2⟩) * c₁⁻¹ := by rw [h2]
      _ = c₁ * e ⟨w, hwL⟩ * c₁⁻¹ * (c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹) := by group
  set Ψ₀ : Λ →* centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) :=
    ((MulAut.conj c₁).toMonoidHom.comp (e.toMonoidHom.comp (Subgroup.inclusion hΛL))).codRestrict
      _ hΨmem with hΨ₀def
  have hΨ₀ : ∀ l : Λ, ((Ψ₀ l : centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) :
      adjointGroup .F4 K) = c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹ := fun l => rfl
  have hΨinj : Function.Injective Ψ₀ := by
    intro a b hab
    have h1 : c₁ * e ⟨a, hΛL a.2⟩ * c₁⁻¹ = c₁ * e ⟨b, hΛL b.2⟩ * c₁⁻¹ := by
      rw [← hΨ₀, ← hΨ₀, hab]
    have h2 : e ⟨a, hΛL a.2⟩ = e ⟨b, hΛL b.2⟩ := mul_left_cancel (mul_right_cancel h1)
    have h3 := e.injective h2
    exact Subtype.ext (congrArg (fun y : L => (y : G)) h3)
  have hΨbij : Function.Bijective Ψ₀ :=
    (Nat.bijective_iff_injective_and_card Ψ₀).2 ⟨hΨinj, hΛcard⟩
  set ΨE : Λ ≃* centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) :=
    MulEquiv.ofBijective Ψ₀ hΨbij with hΨEdef
  have hXJ' : X₀ ≤ rootSL2 K rootR := by
    rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
    exact hXJ
  obtain ⟨c, hc⟩ := exists_conj_of_mulEquiv_centralizer_yRep hK hκtu hXJ' hX₀
    (ΨE.symm.trans (θΛ.trans ΨE))
  have hX₀ne : X₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hX₀
    norm_num at hX₀
  obtain ⟨⟨x₀, hx₀X⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX₀ne
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hF3 : FactF3 K := factF3
  have hx₀C : x₀ ∈ centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) := by
    obtain ⟨Q, -, hQM, -, -⟩ := hF3 κ
    rw [← hQM]
    exact mem_sup_right (rootSL2_rootR_le_levi κ (hXJ' hx₀X))
  set x₀' : centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) := ⟨x₀, hx₀C⟩ with hx₀'def
  set z : Λ := ΨE.symm x₀' with hzdef
  have hz : c₁ * e ⟨z, hΛL z.2⟩ * c₁⁻¹ = x₀ := congrArg Subtype.val (ΨE.apply_symm_apply x₀')
  have hθx : (((ΨE.symm.trans (θΛ.trans ΨE)) x₀' :
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) : adjointGroup .F4 K) =
        c₁ * e ⟨θΛ z, hΛL (θΛ z).2⟩ * c₁⁻¹ := rfl
  have hmem : (((ΨE.symm.trans (θΛ.trans ΨE)) x₀' :
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) : adjointGroup .F4 K) ∈
      ((X₀.subgroupOf (centralizer ({yRep K κ} : Set (adjointGroup .F4 K)))).map
        (ΨE.symm.trans (θΛ.trans ΨE)).toMonoidHom).map
          (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).subtype :=
    ⟨_, ⟨x₀', hx₀X, rfl⟩, rfl⟩
  rw [hθx] at hmem
  have hzX : (z : G) ∈ subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom) := by
    rw [mem_subgroupToG_iff e (hΛL z.2)]
    refine ⟨x₀, hx₀X, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hz]
    group
  have hz1 : (z : G) ≠ 1 := by
    intro h
    apply hx₀1'
    rw [← hz]
    have h1 : (⟨(z : G), hΛL z.2⟩ : L) = 1 := Subtype.ext h
    rw [h1, map_one]
    group
  refine ⟨z, c, hzX, hz1, ?_⟩
  rcases hc with hc | hc
  · left
    rw [hc] at hmem
    exact hmem
  · right
    rw [hc] at hmem
    exact hmem

end Aux

section CaseL

theorem twoTwistedE6XiCaseLInput_holds : TwoTwistedE6XiCaseLInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ6 hκ8 k _ _ σ' hk hσ' G₀ hG₀ e₀ M hM htM eM η
    hη hx φ hφ w hwM hwL hww htw hwq hwΛ hwc htwM _ htN htwN hC₀ _ hφ'
  obtain ⟨φ', hφ'⟩ := hφ'
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hK1 : Nat.card K = 2 ^ 1 := hw.card_eq
  have htC := hw.mem_centralizer
  have := finite_adjointGroup_F4 (K := K)
  have hk' : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ'.toRingHom c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ' c
  obtain ⟨-, hLG₀, -, -, hZ₀, -⟩ := twoTwistedSpan_facts hw X₀ σ' hk hσ' hG₀ e₀
  have hEG₀ : centralizerPerfectCore (subgroupToG e X₀) ≤ G₀ := hG₀ ▸ le_sup_left
  obtain ⟨g, hMg⟩ := hM
  have hZM : Odd (Nat.card (center M)) := by
    rw [hMg, E6Pilot.card_center_conjugate]
    exact hZ₀
  have hw1 : w ≠ 1 := by
    intro h1
    subst h1
    apply not_conj_eta_xi_twistedE6 le_rfl hk' hσ1 hη hx 1
    have h2 : (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom) = 1 := by
      have h3 : eM (QuotientGroup.mk' (center M) (⟨1, hwM⟩ : M)) = 1 := by
        have h4 : (⟨1, hwM⟩ : M) = 1 := rfl
        rw [h4, map_one, map_one]
      rw [hwq] at h3
      have h4 := congrArg φ h3
      rwa [MulAut.inv_apply, MulEquiv.apply_symm_apply, map_one] at h4
    rw [h2, map_one]
    group
  set ψ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom) := φ'⁻¹ * φ with hψdef
  have hψ : ψ * normalizerQuotMulAut eM ⟨t, htM⟩ * ψ⁻¹ =
      normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ := by
    calc ψ * normalizerQuotMulAut eM ⟨t, htM⟩ * ψ⁻¹ =
        φ'⁻¹ * (φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹) * φ' := by rw [hψdef]; group
      _ = φ'⁻¹ * (φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹) * φ' := by rw [hφ, hφ']
      _ = normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ := by group
  set χ : M ⧸ center M ≃* G₀ ⧸ center G₀ := eM.trans (ψ.trans e₀.symm) with hχdef
  have hχs : ∀ y, eM (χ.symm y) = ψ.symm (e₀ y) := by
    intro y
    rw [hχdef, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply]
  have hAM : ∀ y, normalizerQuotMulAut eM ⟨t, htM⟩ (ψ.symm y) =
      ψ.symm (normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ y) := by
    intro y
    rw [← hψ]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hperfA := fixSubgroup_perfect_of_conj hφ
    (commutator_fixSubgroup_xi_twistedE6_two σ'.toRingHom hk hσ' hη hx)
  have hmapPM := map_perfectCore_subgroupOf_centralizer_eq hZM eM hw.orderOf_eq htM hperfA
  have hcardPM := natCard_map_perfectCore_of_xi_twistedE6 hK σ'.toRingHom hk hσ' hZM eM
    hw.orderOf_eq htM hη hx hφ
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have hΛcL := perfectCore_inf_centralizer_le hw.standard hOut htC hw.orderOf_eq M
  have hΛcw : perfectCore (M ⊓ centralizer ({t} : Set G)) ≤ centralizer ({w} : Set G) :=
    fun c hc => mem_centralizer_singleton_iff.2 (hwc c (CFSG.Quasithin.perfectCore_le _ hc))
  have hdvdΛ : Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) ∣
      Nat.card (perfectCore (M ⊓ centralizer ({t} : Set G))) := by
    rw [← hcardPM, ← map_subtype_perfectCore_subgroupOf M t,
      card_map_of_injective M.subtype_injective]
    exact natCard_map_dvd _ _
  obtain ⟨κ, c₁, hκtu, hc₁, hΛeq, hΛcard⟩ := exists_yRep_of_le_of_dvd hK e hwL hw1 hΛcL hΛcw hdvdΛ
  have hΛperf : ⁅L ⊓ centralizer ({w} : Set G), L ⊓ centralizer ({w} : Set G)⁆ =
      L ⊓ centralizer ({w} : Set G) := by
    rw [← hΛeq]
    exact CFSG.Quasithin.perfectCore_perfect _
  have hΛtw : L ⊓ centralizer ({w} : Set G) ≤ centralizer ({t * w} : Set G) := by
    intro l hl
    have hlL : l ∈ L := (mem_inf.1 hl).1
    have hlw : l * w = w * l := mem_centralizer_singleton_iff.1 (mem_inf.1 hl).2
    rw [mem_centralizer_singleton_iff]
    have h1 : l * t = t * l := mem_centralizer_iff.1 htC l hlL
    calc l * (t * w) = (l * t) * w := by group
      _ = t * (l * w) := by rw [h1]; group
      _ = t * (w * l) := by rw [hlw]
      _ = t * w * l := by group
  set Λ : Subgroup G := L ⊓ centralizer ({w} : Set G) with hΛdef
  have hΛL : Λ ≤ L := inf_le_left
  have hΛG₀ : Λ ≤ G₀ := hΛL.trans hLG₀
  have hΛM : Λ ≤ M := hΛeq ▸ (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  set PM := perfectCore ((centralizer ({t} : Set G)).subgroupOf M) with hPMdef
  have hPMΛ : PM.map M.subtype = Λ := by
    rw [hPMdef, map_subtype_perfectCore_subgroupOf, hΛeq]
  set fM : Λ →* M ⧸ center M :=
    (QuotientGroup.mk' (center M)).comp (Subgroup.inclusion hΛM) with hfMdef
  set f₀ : Λ →* G₀ ⧸ center G₀ :=
    (QuotientGroup.mk' (center G₀)).comp (Subgroup.inclusion hΛG₀) with hf₀def
  have hfMrange : fM.range = PM.map (QuotientGroup.mk' (center M)) := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      have hl : (l : G) ∈ PM.map M.subtype := by
        rw [hPMΛ]
        exact l.2
      obtain ⟨m, hm, hml⟩ := hl
      refine ⟨m, hm, ?_⟩
      have hm' : m = Subgroup.inclusion hΛM l := Subtype.ext hml
      rw [hm']
      rfl
    · rintro ⟨m, hm, rfl⟩
      have hmΛ : (m : G) ∈ Λ := by
        rw [← hPMΛ]
        exact ⟨m, hm, rfl⟩
      exact ⟨⟨m, hmΛ⟩, rfl⟩
  have hfMinj : Function.Injective fM := by
    have hCt : Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) =
        Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) := by
      rw [natCard_centralizer_yRep_of_ne_tu le_rfl hK1 (by decide),
        natCard_centralizer_yRep_of_ne_tu le_rfl hK1 hκtu]
    have hcard : Nat.card fM.range = Nat.card Λ := by
      rw [hfMrange, hcardPM, hCt, hΛcard]
    rw [← MonoidHom.ker_eq_bot_iff]
    have h1 : Nat.card fM.ker * Nat.card fM.range = Nat.card Λ := by
      rw [← Subgroup.index_ker]
      exact Subgroup.card_mul_index _
    rw [hcard] at h1
    have h2 : Nat.card fM.ker = 1 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (one_mul _).symm)
    exact Subgroup.eq_bot_of_card_eq _ h2
  have hf₀inj : Function.Injective f₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hlc : Subgroup.inclusion hΛG₀ l ∈ center G₀ := (QuotientGroup.eq_one_iff _).1 hl
    have hlZ : (⟨l, hΛL l.2⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro y
      have h := congrArg Subtype.val ((mem_center_iff.1 hlc) ⟨y, hLG₀ y.2⟩)
      exact Subtype.ext h
    rw [hw.center_eq_bot, mem_bot] at hlZ
    rw [mem_bot]
    have h := congrArg Subtype.val hlZ
    exact Subtype.ext h
  have hA₀fix : ∀ l : Λ, normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ (e₀ (f₀ l)) = e₀ (f₀ l) := by
    intro l
    have h1 := normalizerQuotMulAut_apply e₀ ⟨t * w, htwN⟩ (Subgroup.inclusion hΛG₀ l)
    have h2 : G₀.normalizerMonoidHom ⟨t * w, htwN⟩ (Subgroup.inclusion hΛG₀ l) =
        Subgroup.inclusion hΛG₀ l := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hc : (l : G) * (t * w) = (t * w) * l := mem_centralizer_singleton_iff.1 (hΛtw l.2)
      change t * w * (l : G) * (t * w)⁻¹ = l
      rw [← hc]
      group
    rw [h2] at h1
    exact h1
  have hincl : ∀ l : Λ, (χ.symm.toMonoidHom.comp f₀) l ∈ fM.range := by
    intro l
    rw [hfMrange]
    have hfix : eM (χ.symm (f₀ l)) ∈ E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
      change normalizerQuotMulAut eM ⟨t, htM⟩ (eM (χ.symm (f₀ l))) = eM (χ.symm (f₀ l))
      rw [hχs, hAM, hA₀fix]
    rw [← hmapPM] at hfix
    obtain ⟨m, hm, hmx⟩ := hfix
    exact ⟨m, hm, eM.injective hmx⟩
  obtain ⟨θΛ, hθ⟩ := exists_mulEquiv_of_quotEquiv hΛM hΛG₀ χ hfMinj hf₀inj hincl
  obtain ⟨z, c, hzX, hz1, hmem⟩ :=
    exists_root_of_mulEquiv_inf_centralizer hK e hXJ hX₀ hwL hκtu hc₁ hΛL inf_le_right hΛcard θΛ
  set z' : Λ := θΛ z with hz'def
  have hA : centralizerPerfectCore (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)) =
      (centralizerPerfectCore (subgroupToG e X₀)).map
        (MulAut.conj ((e.symm c₁⁻¹ : L) : G)).toMonoidHom :=
    centralizerPerfectCore_subgroupToG_map_conj e X₀ c₁⁻¹
  have hAG₀ : centralizerPerfectCore (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)) ≤
      G₀ := by
    rw [hA]
    rintro _ ⟨a, ha, rfl⟩
    have hn : ((e.symm c₁⁻¹ : L) : G) ∈ G₀ := hLG₀ (e.symm c₁⁻¹).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn (hEG₀ ha)) (inv_mem hn)
  have hZG₀ : subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom) ≤ G₀ :=
    (map_subtype_le _).trans hLG₀
  have hZcard : Nat.card (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)) = 3 := by
    rw [natCard_subgroupToG, card_map_of_injective (MulAut.conj _).injective, hX₀]
  have hzpZ : zpowers (z : G) = subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom) :=
    zpowers_eq_of_mem_of_card_prime Nat.prime_three hZcard hzX hz1
  set zG₀ : G₀ := ⟨z, hΛG₀ z.2⟩ with hzG₀def
  set z'M : M := ⟨z', hΛM z'.2⟩ with hz'Mdef
  have hχz : χ.symm (QuotientGroup.mk' (center G₀) zG₀) = QuotientGroup.mk' (center M) z'M :=
    (hθ z).symm
  have hAB : ((zpowers zG₀).map (QuotientGroup.mk' (center G₀))).map χ.symm.toMonoidHom =
      (zpowers z'M).map (QuotientGroup.mk' (center M)) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact congrArg zpowers hχz
  have hidx := index_center_perfectCore_centralizer_eq χ.symm hAB
  have hzpG₀ : zpowers zG₀ =
      (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)).subgroupOf G₀ := by
    rw [← hzpZ]
    have h1 : (zpowers zG₀).map G₀.subtype = zpowers (z : G) := MonoidHom.map_zpowers _ _
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective G₀.subtype_injective _).symm
  have hcoreG₀ : perfectCore (centralizer ((zpowers zG₀ : Subgroup G₀) : Set G₀)) =
      (centralizerPerfectCore
        (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom))).subgroupOf G₀ := by
    rw [hzpG₀]
    exact perfectCore_centralizer_subgroupOf_eq hZG₀ hAG₀
  set RM := perfectCore (centralizer ((zpowers z'M : Subgroup M) : Set M)) with hRMdef
  set R : Subgroup G := RM.map M.subtype with hRdef
  have hRM : R ≤ M := map_subtype_le RM
  have hRperf : ⁅R, R⁆ = R := by
    rw [hRdef, ← map_commutator, hRMdef, CFSG.Quasithin.perfectCore_perfect]
  have hRz' : R ≤ centralizer ({(z' : G)} : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 := CFSG.Quasithin.perfectCore_le _ hr
    rw [centralizer_zpowers_coe_eq, mem_centralizer_singleton_iff] at h1
    rw [mem_centralizer_singleton_iff]
    have h2 := congrArg Subtype.val h1
    exact h2
  have hEidx : (center R).index = (center (centralizerPerfectCore (subgroupToG e X₀))).index := by
    calc (center R).index = (center RM).index :=
          (index_center_eq_of_mulEquiv (RM.equivMapOfInjective M.subtype M.subtype_injective)).symm
      _ = (center (perfectCore (centralizer ((zpowers zG₀ : Subgroup G₀) : Set G₀)))).index :=
          hidx.symm
      _ = (center (centralizerPerfectCore
            (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)))).index := by
          rw [hcoreG₀]
          exact index_center_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAG₀)
      _ = _ := by
          rw [hA]
          exact (index_center_eq_of_mulEquiv
            (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective)).symm
  have hz'1 : (z' : G) ≠ 1 := by
    intro h
    apply hz1
    have h1 : z' = 1 := Subtype.ext h
    have h2 : z = 1 := θΛ.injective (h1.trans (map_one θΛ).symm)
    rw [h2]
    rfl
  have hwz' : e ⟨w, hwL⟩ * e ⟨z', hΛL z'.2⟩ = e ⟨z', hΛL z'.2⟩ * e ⟨w, hwL⟩ := by
    have h1 : (⟨z', hΛL z'.2⟩ : L) * ⟨w, hwL⟩ = ⟨w, hwL⟩ * ⟨z', hΛL z'.2⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 z'.2).2)
    have h2 : e (⟨z', hΛL z'.2⟩ * ⟨w, hwL⟩) = e (⟨w, hwL⟩ * ⟨z', hΛL z'.2⟩) := congrArg e h1
    rw [e.map_mul, e.map_mul] at h2
    exact h2.symm
  have key : ∀ H : Subgroup (adjointGroup .F4 K), Nat.card H = 3 →
      c₁ * e ⟨z', hΛL z'.2⟩ * c₁⁻¹ ∈ H.map (MulAut.conj c).toMonoidHom →
      R ≤ centralizerPerfectCore (subgroupToG e (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom)) ∧
      ∀ x ∈ H, e ⟨w, hwL⟩ * ((c₁⁻¹ * c) * x * (c₁⁻¹ * c)⁻¹) =
        ((c₁⁻¹ * c) * x * (c₁⁻¹ * c)⁻¹) * e ⟨w, hwL⟩ := by
    intro H hH3 hzH
    have hzH' : e ⟨z', hΛL z'.2⟩ ∈ H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom := by
      obtain ⟨y, hy, hyeq⟩ := hzH
      refine ⟨y, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq ⊢
      calc (c₁⁻¹ * c) * y * (c₁⁻¹ * c)⁻¹ = c₁⁻¹ * (c * y * c⁻¹) * c₁ := by group
        _ = c₁⁻¹ * (c₁ * e ⟨z', hΛL z'.2⟩ * c₁⁻¹) * c₁ := by rw [hyeq]
        _ = e ⟨z', hΛL z'.2⟩ := by group
    have hcardH : Nat.card (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom) = 3 := by
      rw [card_map_of_injective (MulAut.conj _).injective, hH3]
    have hez'1 : e ⟨z', hΛL z'.2⟩ ≠ 1 := fun h => hz'1 (by
      have h1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val h1)
    have hzpF : zpowers (e ⟨z', hΛL z'.2⟩) = H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom :=
      zpowers_eq_of_mem_of_card_prime Nat.prime_three hcardH hzH' hez'1
    have hzG : (z' : G) ∈ subgroupToG e (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom) :=
      (mem_subgroupToG_iff e (hΛL z'.2)).2 hzH'
    have hzpG : zpowers (z' : G) = subgroupToG e (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom) :=
      zpowers_eq_of_mem_of_card_prime Nat.prime_three (by rw [natCard_subgroupToG, hcardH]) hzG
        hz'1
    refine ⟨le_centralizerPerfectCore hRperf ?_, ?_⟩
    · rw [← hzpG, centralizer_zpowers_coe_eq]
      exact hRz'
    · intro x hx
      have hwC : e ⟨w, hwL⟩ ∈ centralizer ((H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom :
          Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) := by
        rw [← hzpF, centralizer_zpowers_coe_eq, mem_centralizer_singleton_iff]
        exact hwz'
      exact (mem_centralizer_iff.1 hwC _ ⟨x, hx, rfl⟩).symm
  rcases hmem with hmem | hmem
  ·
    obtain ⟨hRE, hwX⟩ := key X₀ hX₀ hmem
    have hNidx : (center (centralizerPerfectCore (subgroupToG e
        (X₀.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom)))).index =
        (center (centralizerPerfectCore (subgroupToG e X₀))).index := by
      rw [centralizerPerfectCore_subgroupToG_map_conj]
      exact (index_center_eq_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective)).symm
    have hRN := eq_of_le_of_index_center_le_of_perfect hRE (commutator_centralizerPerfectCore _)
      (le_of_eq (by rw [hNidx, hEidx]))
    have hEM : (centralizerPerfectCore (subgroupToG e X₀)).map
        (MulAut.conj ((e.symm (c₁⁻¹ * c) : L) : G)).toMonoidHom ≤ M := by
      rw [← centralizerPerfectCore_subgroupToG_map_conj, ← hRN]
      exact hRM
    exact hw1 (eq_one_of_le_map_conj_of_commute hK e htC hXJ hcyc hX₀ (c₁⁻¹ * c) hEM hwL hww
      hwc hwX)
  ·
    have hφX₀ : Nat.card (X₀.map (graphAutF4 K).toMonoidHom) = 3 := by
      rw [card_map_of_injective (f := (graphAutF4 K).toMonoidHom) (graphAutF4 K).injective, hX₀]
    obtain ⟨hRE, -⟩ := key _ hφX₀ hmem
    have h11 : 11 ∣ (center (centralizerPerfectCore (subgroupToG e X₀))).index := by
      have h := eleven_mul_card_center_dvd_of_twoKindAt_unitary6 hκ6
      rw [← Subgroup.card_mul_index (center (centralizerPerfectCore (subgroupToG e X₀))),
        mul_comm 11] at h
      exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h
    apply not_eleven_dvd_card_centralizerPerfectCore_omegaPlus8 hw (e.trans (graphAutF4 K).symm)
      hXJ hcyc hX₀ hκ8
    rw [subgroupToG_trans_symm_eq_map,
      ← natCard_centralizerPerfectCore_subgroupToG_map_conj e _ (c₁⁻¹ * c)]
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hRE)
    rw [← hEidx] at h11
    exact h11.trans (Subgroup.index_dvd_card _)

end CaseL

end CFSG.SeitzReduction.F4Pilot
