module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111KBig
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Th

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11KB_X_le {t z : G} (htz : t * z = z * t) :
    secXH t z ≤ centralizer ({z} : Set G) := by
  rw [secXH, Subgroup.closure_le]
  rintro s ⟨h, hh, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh)
    (Subgroup.mem_centralizer_singleton_iff.mpr htz)) hh

theorem sec11KB_X_conj {t z h : G} (hh : h ∈ centralizer ({z} : Set G)) {x : G}
    (hx : x ∈ secXH t z) : h * x * h⁻¹ ∈ secXH t z := by
  refine Subgroup.closure_induction (p := fun x _ => h * x * h⁻¹ ∈ secXH t z) ?_ ?_ ?_ ?_ hx
  · rintro s ⟨k, hk, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨k * h⁻¹, Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hh), ?_⟩
    group
  · simp
  · intro x y _ _ hx hy
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem sec11KB_X_norm {t z h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    h ∈ normalizer ((secXH t z : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨sec11KB_X_conj hh, fun hx => ?_⟩
  have h1 := sec11KB_X_conj (t := t) (Subgroup.inv_mem _ hh) hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem asc82Step1111KBig_of (r : Asc82Res11a) (hSD : Asc82Step1111KBigSD) :
    Asc82Step1111KBig := by
  intro hp G _ _ t L S z K1 K2 T R hctx hR hD hdih h8 hPex
  obtain ⟨P, hPX, hPds⟩ := hPex
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  obtain ⟨ht2, hz2, -, hz1, -, htz⟩ := sec10D_basic hp.basic hctx'
  have hXH : secXH t z ≤ centralizer ({z} : Set G) := sec11KB_X_le htz
  have hXnorm : ∀ h ∈ centralizer ({z} : Set G),
      h ∈ normalizer ((secXH t z : Subgroup G) : Set G) := fun h hh => sec11KB_X_norm hh
  have htX : t ∈ secXH t z := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by simp⟩
  have hK0 : secK0 t z = oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2 :=
    (hp.r10.lK0 G t L S z K1 K2 hctx').1
  have hΘX : Subgroup.closure (secTheta t z R) ≤ secXH t z := by
    apply Subgroup.closure_mono
    rintro s ⟨-, h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  have hzX : z ∈ secXH t z := hΘX (sec11_z_mem_closure_Theta hp r.l111N hctx)
  have hzc : ∀ x ∈ secXH t z, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXH hx)
  have hΘ2 : IsPGroup 2 (Subgroup.closure (secTheta t z R)) :=
    hR.2.1.to_le (sec11_closure_Theta_le_R t z R)
  have hcardP : 8 ≤ Nat.card P := h8.trans (sec11KB_card_le_sylow hPX hΘ2 hΘX)
  rcases hPds with ⟨m, hm1, ⟨e⟩⟩ | ⟨n, hn, hsd⟩
  · have hm : 2 ≤ m := by
      by_contra hlt
      have hm' : m = 1 := by omega
      subst hm'
      have h4 : Nat.card P = 4 := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
        norm_num
      omega
    have hX2 := sec11KB_dih_complement hPX hm ⟨e⟩ hzX hz2 hz1 hzc
    exact sec11_KBig_core ht2 htX hXH hXnorm hK0 fun h hh hodd x hx =>
      sec11KB_hOdd hPX hX2 (sec11KB_aut_dih hm ⟨e⟩) (hXnorm h hh) hodd x hx
  · by_cases hX2 : oddCoreIn (secXH t z) ⊔ P = secXH t z
    · exact sec11_KBig_core ht2 htX hXH hXnorm hK0 fun h hh hodd x hx =>
        sec11KB_hOdd hPX hX2 (sec11KB_aut_sd hn hsd) (hXnorm h hh) hodd x hx
    · exact hSD hp G t L S z K1 K2 T R hctx hR hD hdih h8 ⟨P, hPX, ⟨n, hn, hsd⟩, hX2⟩

end CFSG.OddStandard.SmallF3.Omega
