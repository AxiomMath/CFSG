module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private lemma sec5b517_all_sup (K₁ K₂ : Subgroup G) (h : G) :
    Sec5B517All (Kfam5 K₁ K₂ h) =
      (K₁ ⊔ K₂) ⊔ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) := by
  rw [sec5b517_all_eq, sup_assoc]

theorem sec5b517_oddCore_bot (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : oddCoreIn L = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  have hΩ : IsOm6Z2 L := c.toSec5Setting.isOm6Z2
  have hxZ : x ∈ centerIn L := sec5o_oddCoreIn_le_centerIn hΩ hx
  have hxt : x ∈ zpowers t := by rw [← c.centre]; exact hxZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxt
  have hx2 : x * x = 1 := by
    rw [← hk, ← zpow_add]
    have h2 : k + k = 2 * k := by ring
    rw [h2, zpow_mul]
    have ht2 : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]
      exact c.t_mul_self
    rw [ht2, one_zpow]
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hx2)
  have hodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd; exact absurd hodd (by decide)

theorem sec5b517_h_mem (h37 : Asc82Lemma37) (h513 : Asc82Lemma513) (h514 : Asc82Lemma514)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : h ∈ normalizer (Qsub K₁ K₂ h : Set G) := by
  have hhz : h * h ∈ centralizer ({z} : Set G) := mul_mem c.h_z c.h_z
  have hcomm : (h * h)⁻¹ * t = t * (h * h)⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.mp (inv_mem c.h_sq)
  have hxd : (h * h)⁻¹ * t * (h * h) ∈
      DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) := by
    have ht : (h * h)⁻¹ * t * (h * h) = t := by rw [hcomm]; group
    rw [ht]
    exact ⟨c.involution, c.t_ne_z h37, c.t_mem_sup₃₄⟩
  have h13 := h513 G t L S z r B A K₁ K₂ h c (h * h) hhz hxd
  have hconj : CFSG.conjugate (Sec5B517All (Kfam5 K₁ K₂ h)) h =
      Sec5B517All (Kfam5 K₁ K₂ h) := by
    rw [sec5b517_all_sup]
    rw [sec5b_conjugate_sup]
    rw [sec5b_conjugate_sup K₁ K₂ h]
    have hB : CFSG.conjugate (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) h = K₁ ⊔ K₂ := by
      rw [sec5b_conjugate_sup, sec5b517_conjugate_conjugate, sec5b517_conjugate_conjugate]
      rw [← sec5b_conjugate_sup K₁ K₂ (h * h)]
      exact h13.2
    rw [hB]
    exact sup_comm _ _
  rw [sec5b517_Qsub_eq]
  exact Sec5B517Quad.mem_normalizer_of_conj (sec5b517_quad h514 c) hconj

theorem sec5b517_swap (h37 : Asc82Lemma37) (h514 : Asc82Lemma514) (h515b : Asc82Lemma515b)
    (swap : Asc82FactSwap6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ∃ c₀ ∈ normalizer (Qsub K₁ K₂ h : Set G), CFSG.conjugate K₁ c₀ = K₂ := by
  have hΩ : IsOm6Z2 L := c.toSec5Setting.isOm6Z2
  have hbot : oddCoreIn L = ⊥ := sec5b517_oddCore_bot c
  obtain ⟨c₀, hc₀, hc₀conj⟩ :=
    swap G L z K₁ K₂ hΩ hbot c.pocket₁ c.pocket₂ c.ne c.comm c.prod
  have hc₀norm : c₀ ∈ normalizer ((L ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hc₀
  have hAB : c₀ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    have htwoRes : c₀ ∈
        normalizer ((twoRes (L ⊓ centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
      sec5b513_mem_normalizer_twoRes hc₀norm
    rwa [← c.prod] at htwoRes
  have hABconj : CFSG.conjugate (K₁ ⊔ K₂) c₀ = K₁ ⊔ K₂ :=
    sec5b513_conjugate_eq_iff.mpr hAB
  have hd1mem : h⁻¹ * t * h ∈ K₁ ⊔ K₂ := c.h_t
  have hd1ord : orderOf (h⁻¹ * t * h) = 2 := by
    simpa [MulAut.conj_apply, inv_inv, c.involution] using
      MulEquiv.orderOf_eq (MulAut.conj h⁻¹) t
  have hd1z : h⁻¹ * t * h ≠ z := by
    intro hz
    have hhz : h * z * h⁻¹ = z := by
      have hcomm : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
      rw [hcomm]; group
    have h1 : h * (h⁻¹ * t * h) * h⁻¹ = h * z * h⁻¹ := by rw [hz]
    have h2 : h * (h⁻¹ * t * h) * h⁻¹ = t := by group
    rw [h2] at h1
    exact c.t_ne_z h37 (h1.trans hhz)
  obtain ⟨hd1delta, hP1⟩ := sec5b517_pair12 h514 c hd1mem hd1ord hd1z
  have hd2mem : c₀⁻¹ * (h⁻¹ * t * h) * c₀ ∈ K₁ ⊔ K₂ :=
    sec5b_mem_of_conjugate_eq' hABconj hd1mem
  have hd2ord : orderOf (c₀⁻¹ * (h⁻¹ * t * h) * c₀) = 2 := by
    simpa [MulAut.conj_apply, inv_inv, hd1ord] using
      MulEquiv.orderOf_eq (MulAut.conj c₀⁻¹) (h⁻¹ * t * h)
  have hd2z : c₀⁻¹ * (h⁻¹ * t * h) * c₀ ≠ z := by
    intro hz
    have hc₀z : c₀ * z * c₀⁻¹ = z := by
      have hcomm : c₀ * z = z * c₀ := Subgroup.mem_centralizer_singleton_iff.mp hc₀.2
      rw [hcomm]; group
    have h1 : c₀ * (c₀⁻¹ * (h⁻¹ * t * h) * c₀) * c₀⁻¹ = c₀ * z * c₀⁻¹ := by rw [hz]
    have h2 : c₀ * (c₀⁻¹ * (h⁻¹ * t * h) * c₀) * c₀⁻¹ = h⁻¹ * t * h := by group
    rw [h2] at h1
    exact hd1z (h1.trans hc₀z)
  obtain ⟨hd2delta, hP2⟩ := sec5b517_pair12 h514 c hd2mem hd2ord hd2z
  have hCD : CFSG.conjugate (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) c₀ =
      CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h :=
    sec5b517_cov h515b c hc₀.2 hd1delta hd2delta hP1 hP2
  have hconj : CFSG.conjugate (Sec5B517All (Kfam5 K₁ K₂ h)) c₀ =
      Sec5B517All (Kfam5 K₁ K₂ h) := by
    rw [sec5b517_all_sup]
    rw [sec5b_conjugate_sup, hABconj, hCD]
  refine ⟨c₀, ?_, hc₀conj⟩
  rw [sec5b517_Qsub_eq]
  exact Sec5B517Quad.mem_normalizer_of_conj (sec5b517_quad h514 c) hconj

theorem sec5b517_orbit (h37 : Asc82Lemma37) (h513 : Asc82Lemma513) (h514 : Asc82Lemma514)
    (h515b : Asc82Lemma515b) (swap : Asc82FactSwap6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ∀ P ∈ Gamma5 K₁ K₂ h, ∃ n ∈ normalizer (Qsub K₁ K₂ h : Set G), CFSG.conjugate K₁ n = P := by
  obtain ⟨c₀, hc₀, hc₀conj⟩ := sec5b517_swap h37 h514 h515b swap c
  have hh : h ∈ normalizer (Qsub K₁ K₂ h : Set G) := sec5b517_h_mem h37 h513 h514 c
  intro P hP
  simp only [Gamma5, Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with hp | hp | hp | hp
  · refine ⟨1, one_mem _, ?_⟩
    rw [hp]
    exact sec5b517_conjugate_one K₁
  · refine ⟨c₀, hc₀, ?_⟩
    rw [hp]
    exact hc₀conj
  · refine ⟨h, hh, ?_⟩
    rw [hp]
  · refine ⟨c₀ * h, mul_mem hc₀ hh, ?_⟩
    rw [hp, ← sec5b517_conjugate_conjugate K₁ c₀ h, hc₀conj]

theorem sec5b517_trans (h37 : Asc82Lemma37) (h513 : Asc82Lemma513) (h514 : Asc82Lemma514)
    (h515b : Asc82Lemma515b) (swap : Asc82FactSwap6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ∀ P ∈ Gamma5 K₁ K₂ h, ∀ P' ∈ Gamma5 K₁ K₂ h,
      ∃ n ∈ normalizer (Qsub K₁ K₂ h : Set G), CFSG.conjugate P n = P' := by
  intro P hP P' hP'
  obtain ⟨n₁, hn₁, hP₁⟩ := sec5b517_orbit h37 h513 h514 h515b swap c P hP
  obtain ⟨n₂, hn₂, hP₂⟩ := sec5b517_orbit h37 h513 h514 h515b swap c P' hP'
  refine ⟨n₁⁻¹ * n₂, mul_mem (inv_mem hn₁) hn₂, ?_⟩
  rw [← hP₁, ← hP₂, sec5b517_conjugate_conjugate,
    show n₁ * (n₁⁻¹ * n₂) = n₂ from by group]

end CFSG.OddStandard.SmallF3.Omega
