module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerOut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (minorAut antiSp antiSpEquiv
  exceptionalAut_structure)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.QuasithinUnique.Setup.X7b (aut_eq_conj_mul_pow mem_inner_iff_autCongr autCongr_pow
  autCongr_minorAut exists_frobenius_data)
open InnerOut

private theorem b2out_minorAut_pow_mem_inner_iff {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (m : ℕ) :
    minorAut F ^ m ∈ inner (antiSp F) ↔ 2 * n ∣ m := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hF
  obtain ⟨-, -, -, -, -, -, -, -, hmem, -⟩ := exceptionalAut_structure hn hFr hord hzp
  rw [← mem_inner_iff_autCongr, autCongr_pow, autCongr_minorAut]
  exact hmem m

theorem relIndex_innerPart_le_two_sp4 {K : Type} [Group K] [Finite K] (L B : Subgroup K)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* StatedSp 2 F) (hBN : B ≤ Subgroup.normalizer (L : Set K))
    (hB2 : ∀ b ∈ B, b * b = 1) : (innerPart L B).relIndex B ≤ 2 := by
  classical
  have hn1 : 1 ≤ n := by omega
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF
  let e' : ↥L ≃* antiSp F := e.trans (antiSpEquiv F).symm
  let Φ : ↥B →* MulAut (antiSp F) :=
    (MulAut.congr e').toMonoidHom.comp (conjHom L B hBN)
  let I : Subgroup (MulAut (antiSp F)) := inner (antiSp F)
  have hN : I.Normal := inner_normal (antiSp F)
  let H : Subgroup (MulAut (antiSp F)) := Φ.range
  have hker : I.comap Φ ≤ (innerPart L B).subgroupOf B := by
    intro b hb
    rw [Subgroup.mem_subgroupOf, mem_innerPart]
    have hb' : MulAut.congr e' (conjHom L B hBN b) ∈ I := hb
    obtain ⟨g, hg⟩ := hb'
    have hconj : conjHom L B hBN b = MulAut.conj (e'.symm g) := by
      have h2 : MulAut.congr e' (MulAut.conj (e'.symm g)) = MulAut.conj g := by
        rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e' (e'.symm g),
          MulEquiv.apply_symm_apply]
      have h3 : MulAut.conj (e'.symm g) = (MulAut.congr e').symm (MulAut.conj g) := by
        rw [← h2, MulEquiv.symm_apply_apply]
      rw [h3, hg, MulEquiv.symm_apply_apply]
    exact ⟨b.2, exists_conjAgree_of_mem_range L B hBN b ⟨e'.symm g, hconj.symm⟩⟩
  have hH2 : ∀ x ∈ H, x * x = 1 := by
    intro x hx
    have hx' : x ∈ Φ.range := hx
    obtain ⟨b, rfl⟩ := hx'
    have hbb : b * b = 1 := Subtype.ext (hB2 b b.2)
    rw [← map_mul, hbb, map_one]
  have hmain : ∀ x ∈ H, x ∉ I → ∃ g : antiSp F, x = MulAut.conj g * minorAut F ^ n := by
    intro x hxH hxI
    obtain ⟨g, j, hj, hxj⟩ := aut_eq_conj_mul_pow hn1 hF x
    have hx2 : x * x = 1 := hH2 x hxH
    have hcI : MulAut.conj g ∈ I := ⟨g, rfl⟩
    have hdI : minorAut F ^ j * MulAut.conj g * (minorAut F ^ j)⁻¹ ∈ I :=
      hN.conj_mem (MulAut.conj g) hcI (minorAut F ^ j)
    have hcdI : MulAut.conj g *
        (minorAut F ^ j * MulAut.conj g * (minorAut F ^ j)⁻¹) ∈ I :=
      I.mul_mem hcI hdI
    have hρ2j : minorAut F ^ (2 * j) ∈ I := by
      have h1 : x * x = MulAut.conj g * (minorAut F ^ j * MulAut.conj g *
          (minorAut F ^ j)⁻¹) * minorAut F ^ (2 * j) := by
        rw [hxj]; group
      have hprod : MulAut.conj g * (minorAut F ^ j * MulAut.conj g *
          (minorAut F ^ j)⁻¹) * minorAut F ^ (2 * j) = 1 := by
        rw [← h1]; exact hx2
      rw [mul_eq_one_iff_eq_inv'.mp hprod]
      exact I.inv_mem hcdI
    have hndvd : n ∣ j := by
      have h := (b2out_minorAut_pow_mem_inner_iff (F := F) hn1 hF (2 * j)).mp hρ2j
      exact Nat.dvd_of_mul_dvd_mul_left two_pos h
    have hj0 : j = 0 ∨ j = n := by
      obtain ⟨k, hk⟩ := hndvd
      have hk2 : k < 2 := by
        have hnk : n * k < n * 2 := by
          calc n * k = j := hk.symm
            _ < 2 * n := hj
            _ = n * 2 := by ring
        exact Nat.lt_of_mul_lt_mul_left hnk
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · left; omega
      · right; omega
    rcases hj0 with hj0 | hjn
    · exact absurd (by rw [hxj, hj0, pow_zero, mul_one]; exact hcI) hxI
    · exact ⟨g, by rw [hxj, hjn]⟩
  have hdvd : I.relIndex H ∣ 2 := by
    by_cases hHI : H ≤ I
    · rw [Subgroup.relIndex_eq_one.mpr hHI]
      exact one_dvd 2
    · have hex : ∃ a ∈ H, a ∉ I := by
        by_contra h
        exact hHI fun a ha => by
          by_contra haI
          exact h ⟨a, ha, haI⟩
      obtain ⟨a, haH, haI⟩ := hex
      obtain ⟨ga, ha⟩ := hmain a haH haI
      refine Subgroup.relIndex_dvd_two_iff.mpr ⟨a, haH, fun b hbH => ?_⟩
      by_cases hbI : b ∈ I
      · exact Or.inr hbI
      · left
        obtain ⟨gb, hb⟩ := hmain b hbH hbI
        rw [hb, ha]
        have hρ2n : minorAut F ^ n * minorAut F ^ n ∈ I := by
          have h : minorAut F ^ (2 * n) ∈ I :=
            (b2out_minorAut_pow_mem_inner_iff (F := F) hn1 hF (2 * n)).mpr (dvd_refl (2 * n))
          rwa [two_mul, pow_add] at h
        have hconjI : minorAut F ^ n * MulAut.conj ga * (minorAut F ^ n)⁻¹ ∈ I :=
          hN.conj_mem (MulAut.conj ga) ⟨ga, rfl⟩ (minorAut F ^ n)
        have h1 : MulAut.conj gb * minorAut F ^ n * (MulAut.conj ga * minorAut F ^ n) =
            MulAut.conj gb * (minorAut F ^ n * MulAut.conj ga * (minorAut F ^ n)⁻¹) *
              (minorAut F ^ n * minorAut F ^ n) := by group
        rw [h1]
        exact I.mul_mem (I.mul_mem ⟨gb, rfl⟩ hconjI) hρ2n
  have hbound : I.relIndex H ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hle : (innerPart L B).relIndex B ≤ I.relIndex H := by
    have h1 : ((innerPart L B).subgroupOf B).index ≤ (I.comap Φ).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
        (Subgroup.index_dvd_of_le hker)
    have h2 : I.relIndex H = (I.comap Φ).index := (Subgroup.index_comap I Φ).symm
    rw [h2]
    exact h1
  exact hle.trans hbound

end CFSG.LocalAnalysis.RankThreeUC.S15

end
