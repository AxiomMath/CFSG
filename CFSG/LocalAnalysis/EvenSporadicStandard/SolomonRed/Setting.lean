module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup

variable {K : Type*} [Group K]

structure Setting (K : Type*) [Group K] (z : K) (B : Subgroup K) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  le_cent : B ≤ centralizer ({z} : Set K)
  norm : ∀ d ∈ centralizer ({z} : Set K), ∀ b ∈ B, d * b * d⁻¹ ∈ B
  simple : IsSimpleGroup ↥B
  nonab : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a
  cent : ∀ d ∈ centralizer ({z} : Set K), (∀ b ∈ B, d * b = b * d) → d ∈ zpowers z
  odd : ∀ N : Subgroup K, N.Normal → Odd (Nat.card N) → N = ⊥
  center : ∀ x : K, (∀ y, y * x = x * y) → x = 1

variable {z : K} {B : Subgroup K}

namespace Setting

theorem mem_cent_iff {x : K} : x ∈ centralizer ({z} : Set K) ↔ x * z = z * x :=
  mem_centralizer_singleton_iff

theorem fixed_mem_zpowers [Finite K] (h : Setting K z B) {W : Subgroup K} [W.Normal]
    (hW : IsPGroup 2 W) : ∀ w ∈ W, z * w = w * z → w ∈ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBW : B ⊓ W = ⊥ := by
    rcases inf_eq_bot_or_le_of_simple h.simple
      (fun b _ x hx => (inferInstance : W.Normal).conj_mem x hx b) with h1 | h1
    · exact h1
    · exact absurd (hW.to_le h1) (not_isPGroup_of_simple_nonabelian h.simple h.nonab)
  intro w hw hwz
  apply h.cent w (mem_cent_iff.2 hwz.symm)
  intro b hb
  have hwb : w * b * w⁻¹ ∈ B := h.norm w (mem_cent_iff.2 hwz.symm) b hb
  have h1 : (w * b * w⁻¹) * b⁻¹ ∈ B ⊓ W := by
    refine ⟨B.mul_mem hwb (B.inv_mem hb), ?_⟩
    have : w * (b * w⁻¹ * b⁻¹) = (w * b * w⁻¹) * b⁻¹ := by group
    rw [← this]
    exact W.mul_mem hw ((inferInstance : W.Normal).conj_mem _ (W.inv_mem hw) b)
  rw [hBW, mem_bot] at h1
  calc w * b = (w * b * w⁻¹ * b⁻¹) * b * w := by group
    _ = b * w := by rw [h1]; group

theorem eq_bot_of_normal_two_group [Finite K] (h : Setting K z B) {W : Subgroup K} [W.Normal]
    (hW : IsPGroup 2 W) : W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix := h.fixed_mem_zpowers hW
  by_contra hW1
  have hnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW1
  by_cases hzW : z ∈ W
  · have hcn := hW.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center W)
    have hcz : (c : W) = ⟨z, hzW⟩ := by
      have hcomm : z * (c : W).1 = (c : W).1 * z := by
        have := Subgroup.mem_center_iff.1 c.2 ⟨z, hzW⟩
        exact congrArg Subtype.val this
      rcases (mem_zpowers_iff_of_mul_self_eq_one h.z_sq).1
        (hfix (c : W).1 (c : W).2 hcomm) with h1 | h1
      · exfalso
        apply hc1
        have h2 : (c : W) = 1 := Subtype.ext h1
        exact Subtype.ext h2
      · exact Subtype.ext h1
    have hzcen : (⟨z, hzW⟩ : W) ∈ Subgroup.center W := by rw [← hcz]; exact c.2
    have hWz : ∀ w ∈ W, w = 1 ∨ w = z := by
      intro w hw
      apply (mem_zpowers_iff_of_mul_self_eq_one h.z_sq).1
      apply hfix w hw
      have := Subgroup.mem_center_iff.1 hzcen ⟨w, hw⟩
      exact (congrArg Subtype.val this).symm
    have hzc : ∀ y : K, y * z = z * y := by
      intro y
      have hy : y * z * y⁻¹ ∈ W := (inferInstance : W.Normal).conj_mem z hzW y
      rcases hWz _ hy with h1 | h1
      · exfalso
        apply h.z_ne
        calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      · calc y * z = (y * z * y⁻¹) * y := by group
          _ = z * y := by rw [h1]
    exact h.z_ne (h.center z hzc)
  · have hfp : ∀ w ∈ W, z * w = w * z → w = 1 := by
      intro w hw hwz
      rcases (mem_zpowers_iff_of_mul_self_eq_one h.z_sq).1 (hfix w hw hwz) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hw) hzW
    have hσ : ∀ x, (MulAut.conj z) ((MulAut.conj z) x) = x := by
      intro x
      simpa [MulAut.conj_apply] using conj_conj_of_mul_self_eq_one h.z_sq x
    have hWσ : ∀ w ∈ W, (MulAut.conj z) w ∈ W := fun w hw => by
      simpa [MulAut.conj_apply] using (inferInstance : W.Normal).conj_mem w hw z
    have hfpσ : ∀ w ∈ W, (MulAut.conj z) w = w → w = 1 := fun w hw hw' =>
      hfp w hw (conj_eq_self_iff.1 (by simpa [MulAut.conj_apply] using hw'))
    have hinv := fixedPointFree_inverts (MulAut.conj z) hσ hWσ hfpσ
    have h2 : 2 ∣ Nat.card W := by
      obtain ⟨n, hn⟩ := hW.exists_card_eq
      rcases n with _ | n
      · exfalso
        have : Nat.card W = 1 := by simpa using hn
        exact hW1 (Subgroup.card_eq_one.mp this)
      · rw [hn, pow_succ]
        exact dvd_mul_left _ _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hx2 : (x : K) * (x : K) = 1 := by
      have : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rw [hx, pow_two] at this
        exact this
      exact congrArg Subtype.val this
    have hx1 : (x : K) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      omega
    have hxi : (MulAut.conj z) (x : K) = (x : K)⁻¹ := hinv x x.2
    have hxinv : (x : K)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv] at hxi
    exact hx1 (hfp x x.2 (conj_eq_self_iff.1 (by simpa [MulAut.conj_apply] using hxi)))

theorem fitting_eq_bot [Finite K] (h : Setting K z B) : CFSG.fittingSubgroup K = ⊥ := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_eq_bot.2 fun p => ?_
  have hp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
  have : Fact (Nat.Prime (p : ℕ)) := ⟨hp⟩
  by_cases h2 : (p : ℕ) = 2
  · rw [h2]
    exact h.eq_bot_of_normal_two_group (W := CFSG.pCore 2 K) CFSG.pCore_isPGroup
  · apply h.odd _ CFSG.pCore_normal
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := K)).exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two h2).pow

end Setting

end CFSG.EvenSporadicStandard.SolomonRed
