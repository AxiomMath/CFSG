module

public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open CFSG.Open CFSG.Semidihedral
open scoped commutatorElement

section Algebra

variable {P : Type*} [Group P]

theorem pow_eq_one_of_conj {x y c : P} (hc : c ∈ Subgroup.center P)
    (hy : y ^ 2 ∈ Subgroup.center P) {j : ℕ} (hyx : y * x * y⁻¹ = c * x ^ (j + 1)) :
    (c * x ^ j) ^ (j + 2) = 1 := by
  have hcx : ∀ k : ℕ, Commute c (x ^ k) := fun k => (Subgroup.mem_center_iff.mp hc (x ^ k)).symm
  have hφc : MulAut.conj y c = c := by
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]
  have hφx : MulAut.conj y x = c * x ^ (j + 1) := by rw [MulAut.conj_apply, hyx]
  have hφφ : MulAut.conj y (MulAut.conj y x) = x := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc y * (y * x * y⁻¹) * y⁻¹ = y ^ 2 * x * (y ^ 2)⁻¹ := by rw [sq]; group
      _ = x := by rw [← Subgroup.mem_center_iff.mp hy x, mul_inv_cancel_right]
  have hkey : x = c ^ (j + 2) * x ^ (j * (j + 2)) * x := by
    calc x = MulAut.conj y (MulAut.conj y x) := hφφ.symm
      _ = c * (c * x ^ (j + 1)) ^ (j + 1) := by rw [hφx, map_mul, map_pow, hφc, hφx]
      _ = c * (c ^ (j + 1) * x ^ ((j + 1) * (j + 1))) := by
        rw [(hcx (j + 1)).mul_pow, ← pow_mul]
      _ = c ^ (j + 2) * x ^ (j * (j + 2) + 1) := by
        rw [← mul_assoc, ← pow_succ']
        congr 2
        ring
      _ = c ^ (j + 2) * x ^ (j * (j + 2)) * x := by rw [pow_succ x, mul_assoc]
  rw [(hcx j).mul_pow, ← pow_mul]
  exact mul_eq_right.mp hkey.symm

theorem mem_normalizer_zpowers_of_conj_mem [Finite P] {g w : P}
    (h : g * w * g⁻¹ ∈ Subgroup.zpowers w) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers w : Set P) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
  rw [Nat.card_zpowers, Nat.card_zpowers]
  exact (MulEquiv.orderOf_eq (MulAut.conj g) w).ge

end Algebra

theorem semidihedral_central_extension {P : Type} [Group P] [Finite P] {n : ℕ} (hn : 4 ≤ n)
    (f : P →* SemidihedralGroup n) (hf : Function.Surjective f)
    (hK : f.ker ≤ Subgroup.center P) : f.ker ⊓ commutator P = ⊥ := by
  classical
  have hn3 : 3 ≤ n := by omega
  have : Finite (SemidihedralGroup n) := presentation_finite n hn3
  obtain ⟨x, hx⟩ := hf (r n)
  obtain ⟨y, hy⟩ := hf (s n)
  set N := 2 ^ (n - 2) with hN
  have hN4 : 4 ≤ N := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set j := N - 2 with hj
  have hjN : j + 2 = N := by omega
  obtain ⟨c, hcK, hyx⟩ : ∃ c ∈ f.ker, y * x * y⁻¹ = c * x ^ (j + 1) := by
    refine ⟨y * x * y⁻¹ * (x ^ (j + 1))⁻¹, ?_, by group⟩
    have hj1 : j + 1 = 2 ^ (n - 2) - 1 := by omega
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hx, hy,
      s_conj_r, hj1, mul_inv_cancel]
  have hy2K : y ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hy, s_sq]
  have hcz : ∀ g : P, g * c = c * g := Subgroup.mem_center_iff.mp (hK hcK)
  have hcx : ∀ k : ℕ, Commute c (x ^ k) := fun k => (hcz (x ^ k)).symm
  obtain ⟨v, hv⟩ : ∃ v : P, v = c * x ^ j := ⟨_, rfl⟩
  have hvN : v ^ N = 1 := by
    rw [← hjN, hv]
    exact pow_eq_one_of_conj (hK hcK) (hK hy2K) hyx
  have hyxv : ⁅y, x⁆ = v := by
    rw [commutatorElement_def, hyx, hv, pow_succ, mul_assoc, mul_inv_cancel_right]
  have hxv : x * v * x⁻¹ = v := by
    have hcomm : Commute x v := hv ▸ (Commute.mul_right (hcz x) (Commute.self_pow x j))
    rw [hcomm.eq, mul_inv_cancel_right]
  have hyv : y * v * y⁻¹ = v ^ (j + 1) := by
    have h1 : MulAut.conj y v = v ^ (j + 1) := by
      rw [hv, map_mul, map_pow, MulAut.conj_apply y c, hcz y, mul_inv_cancel_right,
        MulAut.conj_apply y x, hyx, (hcx (j + 1)).mul_pow, (hcx j).mul_pow, ← pow_mul,
        ← pow_mul, ← mul_assoc, ← pow_succ', mul_comm j]
    rw [← MulAut.conj_apply, h1]
  let S : Set P := insert x (insert y (f.ker : Set P))
  have hS : Subgroup.closure S = ⊤ := by
    have hmap : (Subgroup.closure S).map f = ⊤ := by
      rw [eq_top_iff, ← CentralQuotients.original_generators_closure n hn3, Subgroup.closure_le]
      rintro q (rfl | rfl)
      · exact ⟨x, Subgroup.subset_closure (by simp [S]), hx⟩
      · exact ⟨y, Subgroup.subset_closure (by simp [S]), hy⟩
    have hker : f.ker ≤ Subgroup.closure S := fun k hk =>
      Subgroup.subset_closure (by simp [S, hk])
    have h := Subgroup.comap_map_eq f (Subgroup.closure S)
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker] at h
    exact h.symm
  have hnorm : (Subgroup.zpowers v).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hS, Subgroup.closure_le]
    rintro g (hg | hg | hg)
    · rw [hg]
      exact AschbacherToolkit.mem_normalizer_zpowers_of_conj (Or.inl hxv)
    · rw [hg]
      have hmem : y * v * y⁻¹ ∈ Subgroup.zpowers v := by
        rw [hyv]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _
      exact mem_normalizer_zpowers_of_conj_mem hmem
    · refine AschbacherToolkit.mem_normalizer_zpowers_of_conj (Or.inl ?_)
      rw [← Subgroup.mem_center_iff.mp (hK hg) v, mul_inv_cancel_right]
  have hcentral : ∀ s t : P, s ∈ f.ker → ⁅s, t⁆ = 1 ∧ ⁅t, s⁆ = 1 := by
    intro s t hs
    have := Subgroup.mem_center_iff.mp (hK hs) t
    exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr this.symm,
      commutatorElement_eq_one_iff_mul_comm.mpr this⟩
  have hD : commutator P ≤ Subgroup.zpowers v := by
    refine AschbacherToolkit.commutator_le_of_closure_eq_top _ hS ?_
    intro s hs t ht
    rcases hs with rfl | rfl | hs
    · rcases ht with rfl | rfl | ht
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · rw [← commutatorElement_inv, hyxv]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · rw [(hcentral t s ht).2]; exact Subgroup.one_mem _
    · rcases ht with rfl | rfl | ht
      · rw [hyxv]; exact Subgroup.mem_zpowers _
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · rw [(hcentral t s ht).2]; exact Subgroup.one_mem _
    · rw [(hcentral s t hs).1]; exact Subgroup.one_mem _
  have hSD : (commutator P).map f = commutator (SemidihedralGroup n) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hf]
  have hcardSD : Nat.card (commutator (SemidihedralGroup n)) = N := by
    have h1 := Subgroup.card_mul_index (commutator (SemidihedralGroup n))
    rw [commutator_index n hn, card n hn3] at h1
    have h2 : 2 ^ n = N * 4 := by
      rw [hN, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  have hle1 : N ≤ orderOf (f v) := by
    rw [← hcardSD, ← Nat.card_zpowers, ← hSD, ← MonoidHom.map_zpowers]
    exact Subgroup.card_le_of_le (Subgroup.map_mono hD)
  have hle2 : orderOf v ≤ N := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one hvN)
  have heq : orderOf v = orderOf (f v) :=
    Nat.le_antisymm (hle2.trans hle1) (Nat.le_of_dvd (orderOf_pos v) (orderOf_map_dvd f v))
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzK, hzD⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hD hzD)
  rw [MonoidHom.mem_ker, map_zpow] at hzK
  have h1 : (orderOf (f v) : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.mpr hzK
  rw [← heq] at h1
  exact Subgroup.mem_bot.mpr (orderOf_dvd_iff_zpow_eq_one.mp h1)

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
