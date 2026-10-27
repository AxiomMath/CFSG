module

public import CFSG.GH74.GLS.NT44.ActualCoverModel
public import CFSG.GH74.GLS.Classes
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.LieType.Multipliers
open CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts

private theorem sigmaS_coe :
    ∀ c : L34.Cover,
      ((sigmaS c : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) = L34Facts.sigma c := by
  intro c
  simp only [sigmaS, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict]

theorem modelStructure :
    CFSG.GH74.GLS.NT44.fullTwoCoverKernel = Subgroup.zpowers L34Facts.z₃ ∧
      Nat.card ↥CFSG.GH74.GLS.NT44.fullTwoCoverKernel = 3 ∧
      CFSG.GH74.GLS.NT44.fullTwoCoverKernel ≤ L34Facts.sigma.ker ∧
      CFSG.GH74.GLS.NT44.quotientMk.ker = CFSG.GH74.GLS.NT44.fullTwoCoverKernel ∧
      Function.Surjective CFSG.GH74.GLS.NT44.quotientMk ∧
      Function.Surjective CFSG.GH74.GLS.NT44.fullTwoCoverToS ∧
      CFSG.GH74.GLS.NT44.fullTwoCoverToS.ker = (L34Facts.sigma.ker).map CFSG.GH74.GLS.NT44.quotientMk ∧
      CFSG.GH74.GLS.NT44.fullTwoCoverToS.ker = Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover ∧
      Nat.card ↥CFSG.GH74.GLS.NT44.fullTwoCoverToS.ker = 16 ∧
      commutator CFSG.GH74.GLS.NT44.FullTwoCover = ⊤ ∧
      Finite CFSG.GH74.GLS.NT44.FullTwoCover ∧
      Nat.card CFSG.GH74.GLS.NT44.FullTwoCover = 322560 ∧
      Nonempty (Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover ≃*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
 := by
  have hsigmaS_subtype :
      (Subgroup.subtype CFSG.ComponentClassification.PSL3Four.S).comp sigmaS =
        L34Facts.sigma := by
    apply MonoidHom.ext
    intro c
    exact sigmaS_coe c
  have hkerS : L34Facts.sigma.ker = sigmaS.ker := by
    rw [← hsigmaS_subtype]
    exact MonoidHom.ker_comp_of_injective sigmaS
      (Subgroup.subtype CFSG.ComponentClassification.PSL3Four.S) Subtype.coe_injective
  have hqker : quotientMk.ker = fullTwoCoverKernel := by
    simpa only [quotientMk] using QuotientGroup.ker_mk' fullTwoCoverKernel
  have hqsurj : Function.Surjective quotientMk := by
    simpa only [quotientMk] using QuotientGroup.mk'_surjective fullTwoCoverKernel
  have hz3_eq_zHom : L34Facts.z₃ =
      L34Facts.zHom (1, (1, Multiplicative.ofAdd 1)) := by
    rw [L34Facts.zHom_apply]
    have h1 : (1 : ZMod 3).val = 1 := ZMod.val_one'' (by norm_num)
    simp only [toAdd_ofAdd, toAdd_one, ZMod.val_zero, h1, pow_zero, pow_one, one_mul]
  have hz3_ne_one : L34Facts.z₃ ≠ 1 := by
    intro h
    have h' : L34Facts.zHom (1, (1, Multiplicative.ofAdd 1)) = 1 := by
      rw [← hz3_eq_zHom]
      exact h
    have hd : (1, (1, Multiplicative.ofAdd 1)) =
        (1 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ×
          Multiplicative (ZMod 3)) := by
      apply L34Facts.zHom_injective
      simpa using h'
    have hzero : (1 : ZMod 3) = 0 := by
      simpa using congrArg (fun x : Multiplicative (ZMod 4) ×
        Multiplicative (ZMod 4) × Multiplicative (ZMod 3) => x.2.2.toAdd) hd
    exact (by decide : (1 : ZMod 3) ≠ 0) hzero
  have hz_order : orderOf L34Facts.z₃ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime L34Facts.z₃_pow hz3_ne_one
  have hC : fullTwoCoverKernel = Subgroup.zpowers L34Facts.z₃ := by
    rw [fullTwoCoverKernel]
    have : (Subgroup.zpowers L34Facts.z₃).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 L34Facts.z₃_mem_center)
    refine le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_
    · rw [Set.singleton_subset_iff]
      exact Subgroup.mem_zpowers L34Facts.z₃
    · exact Subgroup.zpowers_le.2 (Subgroup.subset_normalClosure rfl)
  have hC_card : Nat.card ↥fullTwoCoverKernel = 3 := by
    rw [hC, Nat.card_zpowers, hz_order]
  have hC_le_sigma_ker : fullTwoCoverKernel ≤ L34Facts.sigma.ker := by
    intro c hc
    have hcS : sigmaS c = 1 := MonoidHom.mem_ker.mp (normalClosure_z₃_le_sigmaS_ker hc)
    rw [MonoidHom.mem_ker]
    rw [← sigmaS_coe c]
    simpa using congrArg Subtype.val hcS
  have hker_card : Nat.card ↥L34Facts.sigma.ker = 48 := by
    rw [← L34Facts.range_zHom]
    rw [← Nat.card_congr (MonoidHom.ofInjective L34Facts.zHom_injective).toEquiv]
    simp
  have hcover_card : Nat.card L34.Cover = 967680 := by
    have h := Subgroup.card_ker_mul_card_range L34Facts.sigma
    rw [L34Facts.range_sigma, CFSG.ComponentClassification.PSL3Four.card_S,
      hker_card] at h
    omega
  have hF_card : Nat.card FullTwoCover = 322560 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup fullTwoCoverKernel
    change Nat.card L34.Cover =
      Nat.card FullTwoCover * Nat.card ↥fullTwoCoverKernel at h
    rw [hcover_card, hC_card] at h
    omega
  have hsigSurj : Function.Surjective sigmaS := by
    intro s
    have hs : (s : Equiv.Perm (Fin 42)) ∈ L34Facts.sigma.range := by
      rw [L34Facts.range_sigma]
      exact s.2
    obtain ⟨c, hc⟩ := hs
    exact ⟨c, Subtype.ext (by rw [sigmaS_coe, hc])⟩
  have hpisurj : Function.Surjective fullTwoCoverToS := by
    intro s
    obtain ⟨c, hc⟩ := hsigSurj s
    exact ⟨quotientMk c,
      by rw [← MonoidHom.comp_apply, fullTwoCoverToS_comp_quotientMk, hc]⟩
  have hpi_ker : fullTwoCoverToS.ker = (L34Facts.sigma.ker).map quotientMk := by
    rw [hkerS]
    simpa only [fullTwoCoverToS, quotientMk] using
      (QuotientGroup.ker_lift fullTwoCoverKernel sigmaS normalClosure_z₃_le_sigmaS_ker)
  have hker_le_center : fullTwoCoverToS.ker ≤ Subgroup.center FullTwoCover := by
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective fullTwoCoverKernel x
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective fullTwoCoverKernel y
    rw [← map_mul, ← map_mul]
    congr 1
    have hu : u ∈ L34Facts.sigma.ker := by
      rw [MonoidHom.mem_ker]
      have hx' : fullTwoCoverToS (quotientMk u) = 1 := MonoidHom.mem_ker.mp hx
      have hsig : sigmaS u = 1 := by
        rw [← fullTwoCoverToS_comp_quotientMk, MonoidHom.comp_apply]
        exact hx'
      rw [← sigmaS_coe u]
      simpa using congrArg Subtype.val hsig
    exact Subgroup.mem_center_iff.mp (L34Facts.ker_sigma_le_center hu) v
  have hcenter_le_ker : Subgroup.center FullTwoCover ≤ fullTwoCoverToS.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hcent : ((fullTwoCoverToS x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈
        Subgroup.centralizer (CFSG.ComponentClassification.PSL3Four.S :
          Set (Equiv.Perm (Fin 42))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨y, hy⟩ := hsigSurj (⟨s, hs⟩ : CFSG.ComponentClassification.PSL3Four.S)
      have hcommF : quotientMk y * x = x * quotientMk y :=
        Subgroup.mem_center_iff.mp hx (quotientMk y)
      have hcommS : fullTwoCoverToS (quotientMk y) * fullTwoCoverToS x =
          fullTwoCoverToS x * fullTwoCoverToS (quotientMk y) := by
        rw [← map_mul, ← map_mul]
        exact congrArg fullTwoCoverToS hcommF
      have hpiy : fullTwoCoverToS (quotientMk y) = sigmaS y := by
        rw [← MonoidHom.comp_apply, fullTwoCoverToS_comp_quotientMk]
      have hcommPerm := congrArg Subtype.val hcommS
      simpa [hpiy, hy] using hcommPerm
    have hR : ((fullTwoCoverToS x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈ CFSG.ComponentClassification.PSL3Four.R :=
      CFSG.ComponentClassification.PSL3Four.S_le_R (fullTwoCoverToS x).2
    have hmem : ((fullTwoCoverToS x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈
        (Subgroup.centralizer (CFSG.ComponentClassification.PSL3Four.S :
          Set (Equiv.Perm (Fin 42))) ⊓
          CFSG.ComponentClassification.PSL3Four.R :
            Subgroup (Equiv.Perm (Fin 42))) := ⟨hcent, hR⟩
    have hbot : ((fullTwoCoverToS x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 42))) := by
      rwa [← CFSG.ComponentClassification.PSL3Four.centralizer_S_inf_R]
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using hbot)
  have hker_center : fullTwoCoverToS.ker = Subgroup.center FullTwoCover :=
    le_antisymm hker_le_center hcenter_le_ker
  have hcard_pi : Nat.card ↥fullTwoCoverToS.ker = 16 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hpisurj
    rw [hF_card, CFSG.ComponentClassification.PSL3Four.card_S] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 20160) (h.trans (by norm_num))
  have hcomm : commutator FullTwoCover = ⊤ := by
    have : Group.IsPerfect L34.Cover := ⟨L34.commutator_cover⟩
    have : Group.IsPerfect FullTwoCover := inferInstance
    exact Group.IsPerfect.commutator_eq_top
  have hfin : Finite FullTwoCover := Finite.of_surjective quotientMk hqsurj
  have hz3mk : quotientMk L34Facts.z₃ = 1 := by
    rw [← MonoidHom.mem_ker, hqker]
    exact Subgroup.subset_normalClosure rfl
  have hcentral_mk : ∀ u : L34.Cover, u ∈ Subgroup.center L34.Cover →
      quotientMk u ∈ Subgroup.center FullTwoCover := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective fullTwoCoverKernel y
    dsimp only [quotientMk]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hu v
  let ι : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 3)) :=
    MonoidHom.mk' (fun x => (x.1, (x.2, 1))) (by
      intro x y
      ext <;> simp)
  let ψ : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →* FullTwoCover :=
    quotientMk.comp (L34Facts.zHom.comp ι)
  have hψ_mem : ∀ x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
      ψ x ∈ Subgroup.center FullTwoCover := by
    intro x
    dsimp only [ψ, ι]
    apply hcentral_mk
    change L34Facts.zHom (x.1, (x.2, 1)) ∈ Subgroup.center L34.Cover
    rw [L34Facts.zHom_apply]
    simp only [toAdd_one, ZMod.val_zero, pow_zero, mul_one]
    exact mul_mem (Subgroup.pow_mem _ L34Facts.z₁_mem_center _)
      (Subgroup.pow_mem _ L34Facts.z₂_mem_center _)
  let φ : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      Subgroup.center FullTwoCover :=
    ψ.codRestrict (Subgroup.center FullTwoCover) hψ_mem
  have hsurjφ : Function.Surjective φ := by
    intro y
    have hyker : (y : FullTwoCover) ∈ fullTwoCoverToS.ker := by
      rw [hker_center]
      exact y.2
    have hpiy : fullTwoCoverToS (y : FullTwoCover) = 1 := MonoidHom.mem_ker.mp hyker
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective fullTwoCoverKernel (y : FullTwoCover)
    have hu_sigma : u ∈ L34Facts.sigma.ker := by
      rw [MonoidHom.mem_ker]
      have hsig : sigmaS u = 1 := by
        rw [← fullTwoCoverToS_comp_quotientMk, MonoidHom.comp_apply]
        dsimp only [quotientMk]
        rw [hu]
        exact hpiy
      rw [← sigmaS_coe u]
      simpa using congrArg Subtype.val hsig
    rw [← L34Facts.range_zHom] at hu_sigma
    obtain ⟨d, rfl⟩ := hu_sigma
    refine ⟨(d.1, d.2.1), ?_⟩
    apply Subtype.ext
    change ψ (d.1, d.2.1) = (y : FullTwoCover)
    rw [← hu]
    show quotientMk (L34Facts.zHom (d.1, (d.2.1, 1))) =
      quotientMk (L34Facts.zHom d)
    have hdecomp : L34Facts.zHom d =
        L34Facts.zHom (d.1, (d.2.1, 1)) * L34Facts.z₃ ^ d.2.2.toAdd.val := by
      rw [L34Facts.zHom_apply, L34Facts.zHom_apply]
      simp only [toAdd_one, ZMod.val_zero, pow_zero, mul_one, mul_assoc]
    simp only [hdecomp, map_mul, map_pow, hz3mk, one_pow, mul_one]
  have hcard_dom : Nat.card
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
    rw [Nat.card_prod]
    simp
  have hcard_cod : Nat.card ↥(Subgroup.center FullTwoCover) = 16 := by
    rw [← hker_center, hcard_pi]
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_surjective_and_card φ).mpr
      ⟨hsurjφ, hcard_dom.trans hcard_cod.symm⟩
  have hcenter_equiv : Nonempty (Subgroup.center FullTwoCover ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
    ⟨(MulEquiv.ofBijective φ hbij).symm⟩
  exact ⟨hC, hC_card, hC_le_sigma_ker, hqker, hqsurj, hpisurj, hpi_ker,
    hker_center, hcard_pi, hcomm, hfin, hF_card, hcenter_equiv⟩

theorem actualCoverEquiv :
∀
    (Q : Type) [Group Q] [Finite Q], commutator Q = ⊤ →
    ∀ (q : Q →* CFSG.ComponentClassification.PSL3Four.S),
      Function.Surjective q → q.ker ≤ Subgroup.center Q →
      Nat.card ↥q.ker = 16 →
      ∃ (lambda : L34.Cover →* Q) (e : CFSG.GH74.GLS.NT44.FullTwoCover ≃* Q),
        q.comp lambda = CFSG.GH74.GLS.NT44.sigmaS ∧
          Function.Surjective lambda ∧
          lambda = e.toMonoidHom.comp CFSG.GH74.GLS.NT44.quotientMk ∧
          q.comp e.toMonoidHom = CFSG.GH74.GLS.NT44.fullTwoCoverToS ∧
          lambda.ker = CFSG.GH74.GLS.NT44.fullTwoCoverKernel ∧
          (L34Facts.sigma.ker).map lambda = q.ker ∧
          q.ker = Subgroup.center Q ∧
          (∀ e' : CFSG.GH74.GLS.NT44.FullTwoCover ≃* Q,
            q.comp e'.toMonoidHom = CFSG.GH74.GLS.NT44.fullTwoCoverToS → e' = e)
 := by
  intro Q _ _ hQ q hqsurj hqker hqcard
  let qtilde : Q →* Equiv.Perm (Fin 42) :=
    (Subgroup.subtype CFSG.ComponentClassification.PSL3Four.S).comp q
  have hqtilde_ker : qtilde.ker = q.ker := by
    dsimp only [qtilde]
    exact MonoidHom.ker_comp_of_injective q
      (Subgroup.subtype CFSG.ComponentClassification.PSL3Four.S) Subtype.coe_injective
  have hqr : ∀ e, qtilde e ∈ CFSG.ComponentClassification.PSL3Four.S :=
    fun e => (q e).2
  have hqS : ∀ s ∈ CFSG.ComponentClassification.PSL3Four.S, ∃ e, qtilde e = s := by
    intro s hs
    obtain ⟨e, he⟩ := hqsurj (⟨s, hs⟩ : CFSG.ComponentClassification.PSL3Four.S)
    exact ⟨e, congrArg Subtype.val he⟩
  have hCq : qtilde.ker ≤ Subgroup.center Q := by
    rw [hqtilde_ker]
    exact hqker
  obtain ⟨lambda, hlambda, hlambda_surj⟩ :=
    L34Facts.exists_lam hQ qtilde hqr hqS hCq
  have hq_lambda : q.comp lambda = sigmaS := by
    apply MonoidHom.ext
    intro c
    apply Subtype.ext
    have h1 := congrArg (fun f => f c) hlambda
    simpa [qtilde, MonoidHom.comp_apply, sigmaS_coe c] using h1
  have h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1 := by
    intro e he he3
    have hdiv16 : orderOf e ∣ 16 := by
      rw [← hqcard]
      exact Subgroup.orderOf_dvd_natCard q.ker he
    have hdiv3 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one he3
    have hcop : Nat.Coprime 16 3 := by norm_num
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdiv16 hdiv3)
  have h3' : ∀ e ∈ qtilde.ker, e ^ 3 = 1 → e = 1 := by
    intro e he he3
    exact h3 e (by simpa only [hqtilde_ker] using he) he3
  have hlam_z3 : lambda L34Facts.z₃ = 1 := L34Facts.lam_z₃ hlambda h3'
  have hClam : fullTwoCoverKernel ≤ lambda.ker := by
    have : lambda.ker.Normal := MonoidHom.normal_ker lambda
    change Subgroup.normalClosure ({L34Facts.z₃} : Set L34.Cover) ≤ lambda.ker
    refine Subgroup.normalClosure_le_normal ?_
    rw [Set.singleton_subset_iff]
    exact MonoidHom.mem_ker.mpr hlam_z3
  let f : FullTwoCover →* Q :=
    QuotientGroup.lift fullTwoCoverKernel lambda hClam
  have hf_comp : f.comp quotientMk = lambda := by
    simpa only [f, quotientMk] using
      (QuotientGroup.lift_comp_mk' fullTwoCoverKernel lambda hClam)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hlambda_surj y
    exact ⟨quotientMk c, by rw [← MonoidHom.comp_apply, hf_comp]⟩
  have hquotker : quotientMk.ker = fullTwoCoverKernel := by
    simpa only [quotientMk] using QuotientGroup.ker_mk' fullTwoCoverKernel
  have hqf : q.comp f = fullTwoCoverToS := by
    apply MonoidHom.ext
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective fullTwoCoverKernel x
    have h1 : f (quotientMk c) = lambda c := by
      rw [← MonoidHom.comp_apply, hf_comp]
    have h2 : fullTwoCoverToS (quotientMk c) = sigmaS c := by
      rw [← MonoidHom.comp_apply, fullTwoCoverToS_comp_quotientMk]
    dsimp only [quotientMk] at h1 h2 ⊢
    rw [MonoidHom.comp_apply]
    rw [h1, h2, ← MonoidHom.comp_apply, hq_lambda]
  have hcardQ : Nat.card Q = 322560 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hqsurj
    rw [hqcard, CFSG.ComponentClassification.PSL3Four.card_S] at h
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, hcommF, _, hF_card, _⟩ :=
    CFSG.GH74.GLS.NT44.modelStructure
  have hfinj : Function.Injective f := by
    have h := Subgroup.card_ker_mul_card_of_surjective hf_surj
    rw [hF_card, hcardQ] at h
    have hk : Nat.card ↥f.ker = 1 := by
      have : Nonempty Q := ⟨1⟩
      have hpos : 0 < Nat.card Q := Nat.card_pos
      omega
    have hbot : f.ker = ⊥ := Subgroup.eq_bot_of_card_eq f.ker hk
    exact (MonoidHom.ker_eq_bot_iff f).mp hbot
  let e : FullTwoCover ≃* Q := MulEquiv.ofBijective f ⟨hfinj, hf_surj⟩
  have he : e.toMonoidHom = f := by
    apply MonoidHom.ext
    intro x
    exact MulEquiv.ofBijective_apply f ⟨hfinj, hf_surj⟩ x
  have hlambda_eq : lambda = e.toMonoidHom.comp quotientMk := by
    rw [he]
    exact hf_comp.symm
  have hlambda_ker : lambda.ker = fullTwoCoverKernel := by
    rw [hlambda_eq]
    simp only [MulEquiv.toMonoidHom_eq_coe]
    rw [MonoidHom.ker_mulEquiv_comp quotientMk e, hquotker]
  have hqe : q.comp e.toMonoidHom = fullTwoCoverToS := by
    rw [he]
    exact hqf
  have hmap_ker : (L34Facts.sigma.ker).map lambda = q.ker := by
    apply le_antisymm
    · rintro y ⟨c, hc, rfl⟩
      rw [MonoidHom.mem_ker]
      have hcS : sigmaS c = 1 := by
        apply Subtype.ext
        rw [sigmaS_coe c]
        simpa using MonoidHom.mem_ker.mp hc
      rw [← MonoidHom.comp_apply, hq_lambda]
      exact hcS
    · intro y hy
      have hyq : y ∈ qtilde.ker := by simpa only [hqtilde_ker] using hy
      obtain ⟨c, hc, hlc⟩ := L34Facts.exists_ker_preimage hlambda hlambda_surj hyq
      exact Subgroup.mem_map.mpr ⟨c, hc, hlc⟩
  have hqker_center : q.ker = Subgroup.center Q := by
    apply le_antisymm hqker
    intro x hx
    rw [MonoidHom.mem_ker]
    have hcent : ((q x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈
        Subgroup.centralizer (CFSG.ComponentClassification.PSL3Four.S :
          Set (Equiv.Perm (Fin 42))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨y, hy⟩ := hqsurj (⟨s, hs⟩ : CFSG.ComponentClassification.PSL3Four.S)
      have hcommS : q y * q x = q x * q y := by
        rw [← map_mul, ← map_mul]
        exact congrArg q (Subgroup.mem_center_iff.mp hx y)
      have hcommPerm := congrArg Subtype.val hcommS
      simpa [hy] using hcommPerm
    have hR : ((q x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈ CFSG.ComponentClassification.PSL3Four.R :=
      CFSG.ComponentClassification.PSL3Four.S_le_R (q x).2
    have hmem : ((q x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈
        (Subgroup.centralizer (CFSG.ComponentClassification.PSL3Four.S :
          Set (Equiv.Perm (Fin 42))) ⊓
          CFSG.ComponentClassification.PSL3Four.R :
            Subgroup (Equiv.Perm (Fin 42))) := ⟨hcent, hR⟩
    have hbot : ((q x : CFSG.ComponentClassification.PSL3Four.S) :
        Equiv.Perm (Fin 42)) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 42))) := by
      rwa [← CFSG.ComponentClassification.PSL3Four.centralizer_S_inf_R]
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using hbot)
  have huniq : ∀ e' : FullTwoCover ≃* Q,
      q.comp e'.toMonoidHom = fullTwoCoverToS → e' = e := by
    intro e' he'
    have hhom : e'.toMonoidHom = e.toMonoidHom :=
      L34Facts.hom_ext_of_central hcommF q hqker (by rw [he', hqe])
    apply MulEquiv.ext
    intro x
    exact congrArg (fun g : FullTwoCover →* Q => g x) hhom
  exact ⟨lambda, e, hq_lambda, hlambda_surj, hlambda_eq, hqe, hlambda_ker,
    hmap_ker, hqker_center, huniq⟩

theorem actualCoverOfL34 :
∀
    (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
    CFSG.GH74.GLS.IsL34Quotient Q →
    Nat.card ↥(Subgroup.center Q) = 16 →
    ∃ (b : Q ⧸ Subgroup.center Q ≃* CFSG.ComponentClassification.PSL3Four.S)
      (lambda : L34.Cover →* Q) (e : CFSG.GH74.GLS.NT44.FullTwoCover ≃* Q),
      let q : Q →* CFSG.ComponentClassification.PSL3Four.S :=
        b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
      q.comp lambda = CFSG.GH74.GLS.NT44.sigmaS ∧
        Function.Surjective q ∧
        Function.Surjective lambda ∧
        lambda = e.toMonoidHom.comp CFSG.GH74.GLS.NT44.quotientMk ∧
        q.comp e.toMonoidHom = CFSG.GH74.GLS.NT44.fullTwoCoverToS ∧
        lambda.ker = CFSG.GH74.GLS.NT44.fullTwoCoverKernel ∧
        (L34Facts.sigma.ker).map lambda = q.ker ∧
        q.ker = Subgroup.center Q ∧
        (∀ e' : CFSG.GH74.GLS.NT44.FullTwoCover ≃* Q,
          q.comp e'.toMonoidHom = CFSG.GH74.GLS.NT44.fullTwoCoverToS → e' = e)
 := by
  intro Q instGroup instFinite hQ hL hZ
  have : Group.IsPerfect Q := hQ.1
  have hcomm : commutator Q = ⊤ := Group.IsPerfect.commutator_eq_top
  have hclass : CFSG.Open.StatedClassicalModel
      (Q ⧸ Subgroup.center Q) .PSL 3 2 2 := by
    change CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 3 2 2 at hL
    rcases hL with ⟨-, hclass⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hclass
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨b⟩ :=
    CFSG.ComponentClassification.PSL3Four.nonempty_equiv_of_stated
      (Q ⧸ Subgroup.center Q) hclass
  let q : Q →* CFSG.ComponentClassification.PSL3Four.S :=
    b.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hqsurj : Function.Surjective q := by
    dsimp only [q]
    exact b.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center Q))
  have hqker : q.ker = Subgroup.center Q := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective, QuotientGroup.ker_mk']
  have hqcard : Nat.card ↥q.ker = 16 := by rw [hqker, hZ]
  obtain ⟨lambda, e, hcomp, hsurj_lam, hlam_eq, hqe, hlamker, hmap, hcenter, huniq⟩ :=
    @CFSG.GH74.GLS.NT44.actualCoverEquiv Q
      instGroup instFinite hcomm q hqsurj
      (by rw [hqker]) hqcard
  refine ⟨b, lambda, e, ?_⟩
  dsimp only
  exact ⟨hcomp, hqsurj, hsurj_lam, hlam_eq, hqe, hlamker, hmap, hcenter, huniq⟩

end CFSG.GH74.GLS.NT44
