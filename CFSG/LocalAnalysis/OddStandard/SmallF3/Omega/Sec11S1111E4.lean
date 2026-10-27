module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Th
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Dg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L116

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_X_E4 [Finite G] (hp : Asc82Pre11) (h111N : Asc82Lemma111N) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hR : IsSylow2Of R (centralizer ({z} : Set G))) (hsc : IsStrClosedModZ t z R) :
    ∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧ IsDihSd P := by
  obtain ⟨ht2, hz2, ht1, hz1, hne, htz⟩ := sec10D_basic hp.basic hctx.toSec10Ctx
  have hdec : ∀ h ∈ centralizer ({z} : Set G), ∃ o ∈ oddCoreIn (centralizer ({z} : Set G)),
      ∃ c ∈ hatCent t z, h = o * c :=
    sec10D_decomp hR (sec11_t_mem_R hp hctx) (sec11_z_mem_R hp hctx) hsc ht2 hz2 htz ht1 hz1 hne
  have htH : t ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr htz
  have hzH : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hVH : (zpowers t ⊔ zpowers z : Subgroup G) ≤ centralizer ({z} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr htH) (Subgroup.zpowers_le.mpr hzH)
  have hXH : secXH t z ≤ centralizer ({z} : Set G) := by
    simp only [secXH]
    refine (Subgroup.closure_le (centralizer ({z} : Set G))).mpr ?_
    rintro y ⟨h, hhH, rfl⟩
    exact (centralizer ({z} : Set G)).mul_mem
      ((centralizer ({z} : Set G)).mul_mem ((centralizer ({z} : Set G)).inv_mem hhH) htH) hhH
  have htX : t ∈ secXH t z := by
    simp only [secXH]
    exact Subgroup.subset_closure ⟨1, by simp, by simp⟩
  have htzX : t * z ∈ secXH t z := by
    have htzTheta : t * z ∈ secTheta t z R := sec11_tz_mem_Theta hp h111N hctx
    simp only [secTheta, Set.mem_setOf_eq] at htzTheta
    obtain ⟨-, h, hhH, hheq⟩ := htzTheta
    simp only [secXH]
    exact Subgroup.subset_closure ⟨h, hhH, hheq⟩
  have hzX : z ∈ secXH t z := by
    convert (secXH t z).mul_mem htX htzX using 1
    exact ((sec11_klein_mul ht2 hz2 htz).1).symm
  have hVX : (zpowers t ⊔ zpowers z : Subgroup G) ≤ secXH t z :=
    sup_le (Subgroup.zpowers_le.mpr htX) (Subgroup.zpowers_le.mpr hzX)
  have hXO : secXH t z ≤ (zpowers t ⊔ zpowers z) ⊔ oddCoreIn (centralizer ({z} : Set G)) := by
    simp only [secXH]
    refine (Subgroup.closure_le ((zpowers t ⊔ zpowers z) ⊔
      oddCoreIn (centralizer ({z} : Set G)))).mpr ?_
    rintro y ⟨h, hhH, rfl⟩
    have hhH' : h⁻¹ ∈ centralizer ({z} : Set G) := (centralizer ({z} : Set G)).inv_mem hhH
    obtain ⟨o, ho, c, hc, hdec'⟩ := hdec h⁻¹ hhH'
    have hh_eq : h = c⁻¹ * o⁻¹ := by
      have hinv := congrArg Inv.inv hdec'
      simpa [mul_inv_rev] using hinv
    have hconj : h⁻¹ * t * h = o * (c * t * c⁻¹) * o⁻¹ := by
      rw [hdec', hh_eq]; group
    rw [hconj]
    have hvV : c * t * c⁻¹ ∈ (zpowers t ⊔ zpowers z : Subgroup G) := by
      rcases sec11_hatCent_conj ht2 hz2 htz ht1 hne hc with hv | hv
      · rw [hv]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
      · rw [hv]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    have hvH : c * t * c⁻¹ ∈ centralizer ({z} : Set G) := hVH hvV
    have hOv : o * (c * t * c⁻¹ * o⁻¹ * (c * t * c⁻¹)⁻¹) ∈
        oddCoreIn (centralizer ({z} : Set G)) :=
      (oddCoreIn (centralizer ({z} : Set G))).mul_mem ho
        (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn
          (X := centralizer ({z} : Set G)) hvH
          ((oddCoreIn (centralizer ({z} : Set G))).inv_mem ho))
    rw [show o * (c * t * c⁻¹) * o⁻¹ =
      (o * (c * t * c⁻¹ * o⁻¹ * (c * t * c⁻¹)⁻¹)) * (c * t * c⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hOv) (Subgroup.mem_sup_left hvV)
  refine ⟨zpowers t ⊔ zpowers z, ?_, Or.inl (sec11_V4_isDih2 ht2 hz2 htz ht1 hz1 hne)⟩
  let N : Subgroup G := secXH t z ⊓ oddCoreIn (centralizer ({z} : Set G))
  have hNX : N ≤ secXH t z := inf_le_left
  have hNn : ∀ x ∈ secXH t z, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    obtain ⟨hnX, hnO⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr
      ⟨(secXH t z).mul_mem ((secXH t z).mul_mem hx hnX) ((secXH t z).inv_mem hx),
        CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn
          (X := centralizer ({z} : Set G)) (hXH hx) hnO⟩
  have hodd : Odd (Nat.card ↥N) :=
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (centralizer ({z} : Set G))).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_right : N ≤ oddCoreIn (centralizer ({z} : Set G))))
  have hsup : secXH t z = (zpowers t ⊔ zpowers z) ⊔ N := by
    refine le_antisymm ?_ (sup_le hVX hNX)
    intro x hx
    have hxVO : x ∈ (zpowers t ⊔ zpowers z) ⊔ oddCoreIn (centralizer ({z} : Set G)) := hXO hx
    have hVn : (zpowers t ⊔ zpowers z : Subgroup G) ≤
        Subgroup.normalizer (oddCoreIn (centralizer ({z} : Set G)) : Set G) :=
      hVH.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t ⊔ zpowers z)
      (oddCoreIn (centralizer ({z} : Set G))) hVn] at hxVO
    obtain ⟨v, hv, o, ho, hvo⟩ := Set.mem_mul.mp hxVO
    have hoX : o ∈ secXH t z := by
      have hoeq : o = v⁻¹ * x := by rw [← hvo]; group
      rw [hoeq]
      exact (secXH t z).mul_mem ((secXH t z).inv_mem (hVX hv)) hx
    rw [← hvo]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨hoX, ho⟩)
  have hP : IsPGroup 2 ↥(zpowers t ⊔ zpowers z) :=
    IsPGroup.of_card (n := 2) (by rw [sec11_V4_card ht2 hz2 htz ht1 hz1 hne]; norm_num)
  exact sec11_isSylow2Of_of_sup_odd hP hVX hNX hNn hodd hsup

theorem sec11_K_E4 [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hR : IsSylow2Of R (centralizer ({z} : Set G))) (hsc : IsStrClosedModZ t z R) :
    centralizer ({z} : Set G) ≤
      normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨ht2, hz2, ht1, hz1, hne, htz⟩ := sec10D_basic hp.basic hctx.toSec10Ctx
  have hK0 : Asc82Lemma10K0 := hp.r10.lK0
  have hdec : ∀ h ∈ centralizer ({z} : Set G), ∃ o ∈ oddCoreIn (centralizer ({z} : Set G)),
      ∃ c ∈ hatCent t z, h = o * c :=
    sec10D_decomp hR (sec11_t_mem_R hp hctx) (sec11_z_mem_R hp hctx) hsc ht2 hz2 htz ht1 hz1 hne
  have hCH : hatCent t z ≤ centralizer ({z} : Set G) := inf_le_left
  have hKn : ∀ c ∈ hatCent t z, ∀ x ∈ secK0 t z, c * x * c⁻¹ ∈ secK0 t z :=
    fun c hc => sec10D_hatCent_normalizes_K0 hK0 hctx.toSec10Ctx ht2 hz2 htz ht1 hne hc
  obtain ⟨hK1K0, hK2K0, -⟩ := sec10D_K0_contains hK0 hctx.toSec10Ctx
  have hOK0O : oddCoreIn (secK0 t z) ≤ oddCoreIn (centralizer ({z} : Set G)) :=
    sec11_oddCore_le_of_decomp (H := centralizer ({z} : Set G)) (C := hatCent t z)
      (K := secK0 t z) hdec hCH (sec10D_K0_le_hatCent t z) hKn
  have hOCle : oddCoreIn (centralizer ({t} : Set G)) ≤ oddCoreIn (secK0 t z) :=
    sec10D_oddC_le_oddK0 hK0 hctx.toSec10Ctx
  have hK0N : secK0 t z ≤ (K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) := by
    rw [(hK0 G t L S z K1 K2 hctx.toSec10Ctx).1]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (hOCle.trans hOK0O).trans le_sup_right
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
  have hCnN : ∀ c ∈ hatCent t z, ∀ x ∈ (K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)),
      c * x * c⁻¹ ∈ (K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) := by
    intro c hc x hx
    have hle : ((K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) ≤
        Subgroup.comap (MulAut.conj c).toMonoidHom
          ((K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G))) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro k hk
        exact hK0N (hKn c hc k (hK1K0 hk))
      · intro k hk
        exact hK0N (hKn c hc k (hK2K0 hk))
      · intro o ho
        exact Subgroup.mem_sup_right
          (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := centralizer ({z} : Set G))
            (hCH hc) ho)
    have h1 : (MulAut.conj c).toMonoidHom x ∈
        ((K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) :=
      Subgroup.mem_comap.mp (hle hx)
    change c * x * c⁻¹ ∈ (K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) at h1
    exact h1
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro h hhH x hxN
  obtain ⟨o, ho, c, hc, hho⟩ := hdec h hhH
  have hOn : oddCoreIn (centralizer ({z} : Set G)) ≤
      Subgroup.normalizer ((K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) :=
    le_sup_right.trans Subgroup.le_normalizer
  have hcy : c * x * c⁻¹ ∈ (K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) := hCnN c hc x hxN
  have hoy : o * (c * x * c⁻¹) * o⁻¹ ∈
      (K1 ⊔ K2) ⊔ oddCoreIn (centralizer ({z} : Set G)) :=
    (Subgroup.mem_normalizer_iff.mp (hOn ho) (c * x * c⁻¹)).mp hcy
  rw [show h * x * h⁻¹ = o * (c * x * c⁻¹) * o⁻¹ by rw [hho]; group]
  exact hoy

end CFSG.OddStandard.SmallF3.Omega
