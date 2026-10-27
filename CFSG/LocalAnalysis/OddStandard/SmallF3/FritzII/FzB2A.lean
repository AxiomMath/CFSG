module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fzbs_card_FzZ2xSigma4 : Nat.card FzZ2xSigma4 = 48 := by
  rw [Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, ZMod.card]

private lemma fzbs_ctxW_isPGroup (h : Ctx0 t L S x₁ x₂ lam rho) :
    IsPGroup 2 (ctxW t x₁ x₂) := by
  obtain ⟨m, hm⟩ := (S4A.twoCore_isPGroup (G := G) t).exists_card_eq
  apply IsPGroup.of_card (n := m + 4)
  rw [S4A.pt_card_W h, hm, pow_add]
  ring

private theorem fzbs_pCore_eq_comap {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hF : FzF t x₁ x₂ f) :
    CFSG.pCore 2 ↥(fzN2 t x₁ x₂) = fzlK8.comap f := by
  have hle : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hker2 : IsPGroup 2 f.ker := by
    rw [hF.ker]
    exact (fzbs_ctxW_isPGroup h.toCtx0).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hK8_2 : IsPGroup 2 fzlK8 := by
    apply IsPGroup.of_card (n := 3)
    rw [fzl_card_K8]
    norm_num
  have hcomap2 : IsPGroup 2 (fzlK8.comap f) := hK8_2.comap_of_ker_isPGroup f hker2
  apply le_antisymm
  · rw [← Subgroup.map_le_iff_le_comap]
    have hle : (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)).map f ≤ CFSG.pCore 2 FzZ2xSigma4 :=
      le_sSup (show (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)).map f ∈
          {K : Subgroup FzZ2xSigma4 | K.Normal ∧ IsPGroup 2 K} from
        ⟨(CFSG.pCore_normal (p := 2) (G := ↥(fzN2 t x₁ x₂))).map f hF.surj,
          (CFSG.pCore_isPGroup (p := 2) (G := ↥(fzN2 t x₁ x₂))).map f⟩)
    rwa [fzl_pCore_eq] at hle
  · exact le_sSup (show fzlK8.comap f ∈
        {K : Subgroup ↥(fzN2 t x₁ x₂) | K.Normal ∧ IsPGroup 2 K} from
      ⟨fzl_K8_normal.comap f, hcomap2⟩)

theorem fzbs_card_N2 (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    Nat.card (fzN2 t x₁ x₂) = 3072 := by
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hWker : Nat.card f.ker = 64 := by
    rw [hF.ker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_N2).toEquiv]
    rw [S4A.pt_card_W h.toCtx0, hK]
    norm_num
  have hcard := Subgroup.card_ker_mul_card_of_surjective hF.surj
  rw [hWker, fzbs_card_FzZ2xSigma4] at hcard
  omega

theorem fzbs_R_mem_iff (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) :
    ∀ g : G, g ∈ fzR t x₁ x₂ ↔ ∃ hg : g ∈ fzN2 t x₁ x₂, f ⟨g, hg⟩ ∈ fzlK8 := by
  have hC_eq := fzbs_pCore_eq_comap h hF
  intro g
  constructor
  · intro hg
    rw [fzR, CFSG.Open.pCoreOf, Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    refine ⟨x.2, ?_⟩
    have hx' : x ∈ fzlK8.comap f := by rwa [← hC_eq]
    exact Subgroup.mem_comap.mp hx'
  · rintro ⟨hg, hfg⟩
    rw [fzR, CFSG.Open.pCoreOf, Subgroup.mem_map]
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [hC_eq]
    exact Subgroup.mem_comap.mpr hfg

theorem fzbs_card_R (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    Nat.card (fzR t x₁ x₂) = 2 ^ 9 := by
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hWker : Nat.card f.ker = 64 := by
    rw [hF.ker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_N2).toEquiv]
    rw [S4A.pt_card_W h.toCtx0, hK]
    norm_num
  have hcomap_card : Nat.card (fzlK8.comap f) = 2 ^ 9 := by
    have h := fzl_card_comap f hF.surj fzlK8
    rw [h, hWker, fzl_card_K8]
    norm_num
  have hC_eq : CFSG.pCore 2 ↥(fzN2 t x₁ x₂) = fzlK8.comap f := fzbs_pCore_eq_comap h hF
  have hRcard : Nat.card (fzR t x₁ x₂) = Nat.card (CFSG.pCore 2 ↥(fzN2 t x₁ x₂)) := by
    unfold fzR CFSG.Open.pCoreOf
    exact Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥(fzN2 t x₁ x₂))
      (f := (fzN2 t x₁ x₂).subtype) (fzN2 t x₁ x₂).subtype_injective
  rw [hRcard, hC_eq, hcomap_card]

theorem fzbs_card_T2 (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) {T₂ : Subgroup G}
    (hT : IsFzT2 t x₁ x₂ S T₂) : Nat.card T₂ = 2 ^ 10 := by
  have hN2card : Nat.card (fzN2 t x₁ x₂) = 2 ^ 10 * 3 := by
    rw [fzbs_card_N2 h hK hF]
    norm_num
  have hrel : T₂.relIndex (fzN2 t x₁ x₂) * Nat.card T₂ = Nat.card (fzN2 t x₁ x₂) := by
    have h := Subgroup.relIndex_mul_card (H := T₂) (K := fzN2 t x₁ x₂)
    rwa [inf_eq_left.mpr hT.le_N2] at h
  have hodd : Odd (T₂.relIndex (fzN2 t x₁ x₂)) :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hT.odd_relIndex)
  have hcop_r : Nat.Coprime 2 (T₂.relIndex (fzN2 t x₁ x₂)) :=
    Nat.coprime_two_left.mpr hodd
  obtain ⟨k, hk⟩ := hT.isPGroup.exists_card_eq
  have hR : T₂.relIndex (fzN2 t x₁ x₂) * 2 ^ k = 2 ^ 10 * 3 := by
    rw [← hk, hrel, hN2card]
  have hk_le : k ≤ 10 := by
    have hdvd : 2 ^ k ∣ 2 ^ 10 * 3 := by
      rw [← hR]
      exact dvd_mul_left _ _
    have hcop3 : Nat.Coprime (2 ^ k) 3 := (by decide : Nat.Coprime 2 3).pow_left k
    have hdvd' : 2 ^ k ∣ 2 ^ 10 := hcop3.dvd_of_dvd_mul_right hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd'
  have hk_ge : 10 ≤ k := by
    have hdvd : 2 ^ 10 ∣ 2 ^ k := by
      have hdvd' : 2 ^ 10 ∣ 2 ^ k * T₂.relIndex (fzN2 t x₁ x₂) := by
        rw [mul_comm, hR]
        exact dvd_mul_right _ _
      exact (hcop_r.pow_left 10).dvd_of_dvd_mul_right hdvd'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  rw [hk, le_antisymm hk_le hk_ge]

private lemma fzbs_f_eq_one_of_mem_W {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) {w : G} (hw : w ∈ fzN2 t x₁ x₂) (hwW : w ∈ ctxW t x₁ x₂) :
    f ⟨w, hw⟩ = 1 := by
  rw [← MonoidHom.mem_ker, hF.ker, Subgroup.mem_subgroupOf]
  exact hwW

private lemma fzbs_baseGrp_le_L (h : Ctx t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ L := by
  have h1 : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    rw [baseGrp, wreathGrp]
    exact Subgroup.closure_mono (by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      tauto)
  exact h1.trans (by rw [← h.inf_eq]; exact inf_le_right)

theorem fzbs_f_rho (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) (hr : rho ∈ fzN2 t x₁ x₂) :
    f ⟨rho, hr⟩ ^ 3 = 1 ∧ f ⟨rho, hr⟩ ≠ 1 := by
  have hrho := fzl_rho_Z h
  constructor
  · have h3 : (⟨rho, hr⟩ : ↥(fzN2 t x₁ x₂)) ^ 3 = 1 := by
      ext
      simpa using hrho.2.2.1
    rw [← map_pow, h3, map_one]
  · intro h1
    have hrhoW : rho ∈ ctxW t x₁ x₂ := (fzl_W_mem_iff hF rho).2 ⟨hr, h1⟩
    have hzZ : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hzW : x₁ ^ 2 ∈ ctxW t x₁ x₂ := fzl_Z_le_W h hzZ
    haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
    have hcomm : rho * x₁ ^ 2 = x₁ ^ 2 * rho :=
      congrArg Subtype.val
        (mul_comm' (⟨rho, hrhoW⟩ : ctxW t x₁ x₂) ⟨x₁ ^ 2, hzW⟩)
    exact hrho.2.2.2 (x₁ ^ 2) hzZ (fzl_z1_ne_z2 h).2.1 (by rw [hcomm]; group)

theorem fzbs_f_lam (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) (hr : rho ∈ fzN2 t x₁ x₂) (hl : lam ∈ fzN2 t x₁ x₂) :
    f ⟨lam, hl⟩ ^ 2 = 1 ∧ f ⟨lam, hl⟩ * f ⟨rho, hr⟩ * (f ⟨lam, hl⟩)⁻¹ = (f ⟨rho, hr⟩)⁻¹ := by
  have hlam := fzl_lam_Z h
  have hlr := fzl_lam_rho h
  constructor
  · have h2 : (⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) ^ 2 = 1 := by
      ext
      simpa using hlam.2.2.1
    rw [← map_pow, h2, map_one]
  · have hkey : (⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩ * ⟨lam, hl⟩⁻¹ = ⟨rho, hr⟩⁻¹ := by
      ext
      simpa using hlr.1
    calc f ⟨lam, hl⟩ * f ⟨rho, hr⟩ * (f ⟨lam, hl⟩)⁻¹
        = f ((⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩ * ⟨lam, hl⟩⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = f (⟨rho, hr⟩⁻¹) := by rw [hkey]
      _ = (f ⟨rho, hr⟩)⁻¹ := map_inv f ⟨rho, hr⟩

theorem fzbs_f_tau (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) (hr : rho ∈ fzN2 t x₁ x₂) (ht : tau ∈ fzN2 t x₁ x₂) :
    f ⟨tau, ht⟩ = fzlKappa := by
  have hfr := fzbs_f_rho h hF hr
  have htau2W : tau ^ 2 ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left h.tau_sq_mem
  have htau2N2 : tau ^ 2 ∈ fzN2 t x₁ x₂ :=
    (Subgroup.le_normalizer : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂) htau2W
  have hc2 : f ⟨tau, ht⟩ ^ 2 = 1 := by
    have h2 : (⟨tau, ht⟩ : ↥(fzN2 t x₁ x₂)) ^ 2 = ⟨tau ^ 2, htau2N2⟩ := by
      ext
      rfl
    rw [← map_pow, h2]
    exact fzbs_f_eq_one_of_mem_W hF htau2N2 htau2W
  have hc1 : f ⟨tau, ht⟩ ≠ 1 := by
    intro h1
    have htauW : tau ∈ ctxW t x₁ x₂ := (fzl_W_mem_iff hF tau).2 ⟨ht, h1⟩
    have hWle : ctxW t x₁ x₂ ≤ twoCore t ⊔ L :=
      sup_le le_sup_left ((fzbs_baseGrp_le_L h).trans le_sup_right)
    exact h.tau_not_mem (hWle htauW)
  have hca : f ⟨tau, ht⟩ * f ⟨rho, hr⟩ = f ⟨rho, hr⟩ * f ⟨tau, ht⟩ := by
    have h1 : (⟨tau, ht⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩ =
        ⟨rho, hr⟩ * ⟨tau, ht⟩ := by
      ext
      simpa using h.tau_rho
    calc f ⟨tau, ht⟩ * f ⟨rho, hr⟩
        = f ((⟨tau, ht⟩ : ↥(fzN2 t x₁ x₂)) * ⟨rho, hr⟩) := by rw [map_mul]
      _ = f (⟨rho, hr⟩ * ⟨tau, ht⟩) := by rw [h1]
      _ = f ⟨rho, hr⟩ * f ⟨tau, ht⟩ := by rw [map_mul]
  exact fzl_tau_image (f ⟨rho, hr⟩) (f ⟨tau, ht⟩) hfr.1 hfr.2 hc2 hc1 hca

theorem fzbs_tau_R (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) : tau ∈ fzR t x₁ x₂ := by
  have htn2 : tau ∈ fzN2 t x₁ x₂ := fz_S_le_N2 h h.tau_mem
  refine (fzbs_R_mem_iff h hF tau).mpr ⟨htn2, ?_⟩
  rw [fzbs_f_tau h hF (fzl_rho_Z h).1 htn2]
  exact fzl_kappa_facts.1

theorem fzbs_lam_not_R (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) : lam ∉ fzR t x₁ x₂ := by
  intro hlamR
  obtain ⟨hlamN2, hflamK8⟩ := (fzbs_R_mem_iff h hF lam).mp hlamR
  have hrhoN2 : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
  have hfr := fzbs_f_rho h hF hrhoN2
  have hfl := fzbs_f_lam h hF hrhoN2 hlamN2
  obtain ⟨v, hvK4, hvne⟩ := fzl_lam_image (f ⟨rho, hrhoN2⟩) (f ⟨lam, hlamN2⟩)
    hfr.1 hfr.2 hfl.1 hfl.2
  refine hvne (by
    have hcomm : f ⟨lam, hlamN2⟩ * v = v * f ⟨lam, hlamN2⟩ :=
      fzl_K8_comm _ hflamK8 _ (fzl_K4_le_K8 hvK4)
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm)

theorem fzbs_R_comm (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) : ∀ r ∈ fzR t x₁ x₂, ∀ r' ∈ fzR t x₁ x₂, ⁅r, r'⁆ ∈ ctxW t x₁ x₂ := by
  intro r hr r' hr'
  obtain ⟨hrN2, hfrK8⟩ := (fzbs_R_mem_iff h hF r).mp hr
  obtain ⟨hr'N2, hfr'K8⟩ := (fzbs_R_mem_iff h hF r').mp hr'
  have hcommN2 : ⁅r, r'⁆ ∈ fzN2 t x₁ x₂ := by
    rw [commutatorElement_def]
    exact (fzN2 t x₁ x₂).mul_mem
      ((fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem hrN2 hr'N2)
        ((fzN2 t x₁ x₂).inv_mem hrN2))
      ((fzN2 t x₁ x₂).inv_mem hr'N2)
  refine (fzl_W_mem_iff hF ⁅r, r'⁆).mpr ⟨hcommN2, ?_⟩
  have hsub : (⟨⁅r, r'⁆, hcommN2⟩ : ↥(fzN2 t x₁ x₂)) =
      ⁅(⟨r, hrN2⟩ : ↥(fzN2 t x₁ x₂)), ⟨r', hr'N2⟩⁆ := by
    apply Subtype.ext
    rfl
  rw [hsub, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (fzl_K8_comm _ hfrK8 _ hfr'K8)

theorem fzbs_R_sq (h : Ctx t L S x₁ x₂ lam rho tau) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4}
    (hF : FzF t x₁ x₂ f) : ∀ r ∈ fzR t x₁ x₂, r ^ 2 ∈ ctxW t x₁ x₂ := by
  intro r hr
  obtain ⟨hrN2, hfrK8⟩ := (fzbs_R_mem_iff h hF r).mp hr
  have hsqN2 : r ^ 2 ∈ fzN2 t x₁ x₂ := (fzN2 t x₁ x₂).pow_mem hrN2 2
  refine (fzl_W_mem_iff hF (r ^ 2)).mpr ⟨hsqN2, ?_⟩
  have hsub : (⟨r ^ 2, hsqN2⟩ : ↥(fzN2 t x₁ x₂)) =
      (⟨r, hrN2⟩ : ↥(fzN2 t x₁ x₂)) ^ 2 := by
    apply Subtype.ext
    rfl
  rw [hsub, map_pow, fzl_K8_sq (f ⟨r, hrN2⟩) hfrK8]

theorem fzbs_T2_cases (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) {T₂ : Subgroup G}
    (hT : IsFzT2 t x₁ x₂ S T₂) : ∀ g ∈ T₂, g ∈ fzR t x₁ x₂ ∨ lam * g ∈ fzR t x₁ x₂ := by
  have hlamS : lam ∈ S := by
    have hl : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at hl
    exact hl.1
  have hcard : Nat.card T₂ = 2 * Nat.card (fzR t x₁ x₂) := by
    rw [fzbs_card_T2 h hK hF hT, fzbs_card_R h hK hF]
    norm_num
  have hcos := fzl_index_two_cosets (fzl_R_le_T hT) hcard (hT.S_le hlamS) (fzbs_lam_not_R h hF)
  have hlinv : lam⁻¹ = lam := by
    have hll : lam * lam = 1 := by rw [← pow_two]; exact (fzl_lam_Z h).2.2.1
    exact inv_eq_of_mul_eq_one_right hll
  intro g hg
  rcases hcos g hg with hgR | hgR
  · exact Or.inl hgR
  · exact Or.inr (by rwa [hlinv] at hgR)

end CFSG.OddStandard.SmallF3.FritzII
