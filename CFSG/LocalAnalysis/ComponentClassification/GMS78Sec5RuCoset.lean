module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuInvol

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

@[expose] def tvA : Lin8 := (1, 3, 4)

@[expose] def tvB : Lin8 := (1, 2, 5)

@[expose] def tvAB : Lin8 := (1, 3, 5)

theorem tvA_mem : tvA ∈ invList := by
  decide +kernel

theorem tvB_mem : tvB ∈ invList := by
  decide +kernel

theorem tvA_ne_tvB : tvA ≠ tvB := by
  decide

theorem linComp_tvA_tvB : linComp tvA tvB = linComp tvB tvA := by
  decide

theorem linApply_tvAB (s : Fin 8) : linApply tvAB s = linApply tvA (linApply tvB s) := by
  revert s
  decide

theorem linApply_tvA_tvA (s : Fin 8) : linApply tvA (linApply tvA s) = s := by
  revert s
  decide

theorem linApply_tvB_tvB (s : Fin 8) : linApply tvB (linApply tvB s) = s := by
  revert s
  decide

theorem linApply_tv_comm (s : Fin 8) :
    linApply tvA (linApply tvB (linApply tvA (linApply tvB s))) = s := by
  revert s
  decide

theorem sq_check : ∀ p q e : Fin 8, linApply tvA p = p → (∀ s, p ≠ linApply tvA s ^^^ s) →
    linApply tvB q = q → (∀ s, q ≠ linApply tvB s ^^^ s) →
    linApply tvA (linApply tvB (p ^^^ e ^^^ q)) = p ^^^ e ^^^ q →
    (∀ s, p ^^^ e ^^^ q ≠ linApply tvA (linApply tvB s) ^^^ s) →
    linApply tvA q ^^^ q ≠ e ^^^ linApply tvB e := by
  decide +kernel

theorem conj_check : (invList.all fun r => [tvA, tvB, tvAB].all fun t =>
    glList.any fun c => all8.all fun s =>
      linApply c (linApply t s) == linApply r (linApply c s)) = true := by
  decide +kernel

theorem exists_conj_tv {r t : Lin8} (hr : r ∈ invList) (ht : t ∈ [tvA, tvB, tvAB]) :
    ∃ c ∈ glList, ∀ s, linApply c (linApply t s) = linApply r (linApply c s) := by
  have h := conj_check
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨c, hc, h'⟩ := h r hr t ht
  exact ⟨c, hc, fun s => h' s (by simp [all8])⟩

theorem mem_invList {r : Lin8} (hr : r ∈ glList) (h2 : ∀ s, linApply r (linApply r s) = s)
    (h1 : ∃ s, linApply r s ≠ s) : r ∈ invList := by
  refine List.mem_filter.mpr ⟨hr, ?_⟩
  have hne : r ≠ linId := by
    rintro rfl
    obtain ⟨s, hs⟩ := h1
    exact hs (RuSimCode.linApply_linId s)
  have hcomp : linComp r r = linId := by
    refine lin8_ext fun t => ?_
    rw [RuSimCode.linApply_linComp, h2, RuSimCode.linApply_linId]
  simp [hne, hcomp]

theorem fin8_xor_cancel_pair : ∀ a b : Fin 8, a ^^^ b ^^^ a ^^^ b = 0 := by
  decide

theorem nat_xor_cancel (a b : ℕ) : a ^^^ b ^^^ (b ^^^ a) = 0 := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b b a, Nat.xor_self, Nat.zero_xor, Nat.xor_self]

theorem nat_xor_cancel' (a b : ℕ) : a ^^^ (a ^^^ b) ^^^ b = 0 := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_self]

end RuQCode

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem inv_conj_mem {z : G} (hzN : z ∈ normalizer (R : Set G)) {b : G} (hb : b ∈ gmsA L T) :
    z⁻¹ * b * z ∈ gmsA L T := by
  simpa using hM.normA z⁻¹ (inv_mem hzN) b hb

theorem inv_mul_mul_eq {z : G} (hz2 : z ^ 2 ∈ gmsA L T) {b : G} (hb : b ∈ gmsA L T) :
    z⁻¹ * b * z = z * b * z⁻¹ := by
  have hc : z ^ 2 * b = b * z ^ 2 := hM.central _ (hM.le hz2) b hb
  calc z⁻¹ * b * z = z⁻¹ * (b * z ^ 2) * z⁻¹ := by rw [pow_two]; group
    _ = z⁻¹ * (z ^ 2 * b) * z⁻¹ := by rw [hc]
    _ = z * b * z⁻¹ := by rw [pow_two]; group

theorem act_mul_left {g u : G} (hgN : g ∈ normalizer (R : Set G)) (hu : u ∈ R) :
    (∀ b ∈ gmsA L T, u * g * b * (u * g)⁻¹ = g * b * g⁻¹) ∧
      ∀ x ∈ R, μ (u * g * x * (u * g)⁻¹) = μ (g * x * g⁻¹) := by
  have hgR : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hgN x).mp hx
  refine ⟨fun b hb => ?_, fun x hx => ?_⟩
  · have hc := hM.central u hu _ (hM.normA g hgN b hb)
    calc u * g * b * (u * g)⁻¹ = u * (g * b * g⁻¹) * u⁻¹ := by group
      _ = g * b * g⁻¹ := by rw [hc]; group
  · rw [show u * g * x * (u * g)⁻¹ = u * (g * x * g⁻¹) * u⁻¹ by group,
      hM.mul _ (mul_mem hu (hgR x hx)) _ (inv_mem hu), hM.mul _ hu _ (hgR x hx), hM.μ_inv hu,
      Nat.xor_comm (μ u), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem conj_mul_right {g e : G} (he : e ∈ gmsA L T) {b : G} (hb : b ∈ gmsA L T) :
    g * e * b * (g * e)⁻¹ = g * b * g⁻¹ := by
  have hc : e * b = b * e := hM.central e (hM.le he) b hb
  calc g * e * b * (g * e)⁻¹ = g * (e * b) * e⁻¹ * g⁻¹ := by group
    _ = g * b * g⁻¹ := by rw [hc]; group

theorem sq_mem_of_act (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    {g : G} (hgN : g ∈ normalizer (R : Set G)) {τ : Fin 8 → Fin 8}
    (hτ : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = τ (ν b)) (h2 : ∀ s, τ (τ s) = s) : g ^ 2 ∈ R := by
  rw [← hNC]
  refine mem_inf.mpr ⟨pow_mem hgN 2, mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hgb := hM.normA g hgN b hb
  have h1 : g ^ 2 * b * (g ^ 2)⁻¹ = b := by
    refine hM.eq_of_ν_eq (hM.normA _ (pow_mem hgN 2) b hb) hb ?_
    rw [show g ^ 2 * b * (g ^ 2)⁻¹ = g * (g * b * g⁻¹) * g⁻¹ by rw [pow_two]; group, hτ _ hgb,
      hτ b hb, h2]
  calc b * g ^ 2 = g ^ 2 * b * (g ^ 2)⁻¹ * g ^ 2 := by rw [h1]
    _ = g ^ 2 * b := by group

theorem exists_sq_eq_one_of_ν_sq_eq {z : G} (hzN : z ∈ normalizer (R : Set G))
    {τ : Fin 8 → Fin 8} (hτ : ∀ b ∈ gmsA L T, ν (z * b * z⁻¹) = τ (ν b))
    (hz2 : z ^ 2 ∈ gmsA L T) {s : Fin 8} (hs : ν (z ^ 2) = τ s ^^^ s) :
    ∃ e ∈ gmsA L T, (z * e) ^ 2 = 1 := by
  obtain ⟨e, he, rfl⟩ := hM.ν_surj s
  refine ⟨e, he, ?_⟩
  have hze : z * e * z⁻¹ ∈ gmsA L T := hM.normA z hzN e he
  have e1 : (z * e) ^ 2 = z ^ 2 * (z * e * z⁻¹) * e := by
    rw [← hM.inv_mul_mul_eq hz2 he, pow_two, pow_two]
    group
  rw [e1]
  apply hM.ν_inj _ (mul_mem (mul_mem hz2 hze) he)
  rw [hM.ν_mul _ (mul_mem hz2 hze) _ he, hM.ν_mul _ hz2 _ hze, hτ e he, hs]
  exact RuQCode.fin8_xor_cancel_pair _ _

theorem exists_mul_sq_mem {g : G} (hgN : g ∈ normalizer (R : Set G)) (hg2 : g ^ 2 ∈ R)
    {t : Lin8} (ht : t ∈ invList) (htR : ∀ x ∈ R, μ (g * x * g⁻¹) = maskApply (adMat t) (μ x)) :
    ∃ u ∈ R, (u * g) ^ 2 ∈ gmsA L T := by
  have hgR : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hgN x).mp hx
  have hfix : maskApply (adMat t) (μ (g ^ 2)) = μ (g ^ 2) := by
    rw [← htR _ hg2, show g * g ^ 2 * g⁻¹ = g ^ 2 by rw [pow_two]; group]
  obtain ⟨n, hn, hnm⟩ := RuQCode.exists_image_eq ht (hM.lt _ hg2) hfix
  obtain ⟨u, hu, rfl⟩ := hM.surj n hn
  refine ⟨u, hu, ?_⟩
  have e1 : (u * g) ^ 2 = u * (g * u * g⁻¹) * g ^ 2 := by
    rw [pow_two, pow_two]
    group
  have hR : u * (g * u * g⁻¹) ∈ R := mul_mem hu (hgR u hu)
  rw [e1, ← hM.ker _ (mul_mem hR hg2), hM.mul _ hR _ hg2, hM.mul _ hu _ (hgR u hu), htR u hu,
    ← hnm]
  exact RuQCode.nat_xor_cancel _ _

theorem exists_comm_mem (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    {x y : G} (hxN : x ∈ normalizer (R : Set G)) (hyN : y ∈ normalizer (R : Set G))
    (hxA : ∀ b ∈ gmsA L T, ν (x * b * x⁻¹) = linApply RuQCode.tvA (ν b))
    (hyA : ∀ b ∈ gmsA L T, ν (y * b * y⁻¹) = linApply RuQCode.tvB (ν b))
    (hxR : ∀ r ∈ R, μ (x * r * x⁻¹) = maskApply (adMat RuQCode.tvA) (μ r))
    (hyR : ∀ r ∈ R, μ (y * r * y⁻¹) = maskApply (adMat RuQCode.tvB) (μ r))
    (hx2 : x ^ 2 ∈ gmsA L T) (hy2 : y ^ 2 ∈ gmsA L T) :
    ∃ w ∈ R, x * (w * y) * x⁻¹ * (w * y)⁻¹ ∈ gmsA L T ∧ (w * y) ^ 2 ∈ gmsA L T := by
  have hxR' : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr => (mem_normalizer_iff.mp hxN r).mp hr
  have hyR' : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr => (mem_normalizer_iff.mp hyN r).mp hr
  set k := x * y * x⁻¹ * y⁻¹ with hkdef
  have hk : k ∈ R := by
    rw [← hNC]
    refine mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN),
      mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hb1 := hM.inv_conj_mem hyN hb
    have hb2 := hM.inv_conj_mem hxN hb1
    have hb3 := hM.normA y hyN _ hb2
    have h1 : k * b * k⁻¹ = b := by
      refine hM.eq_of_ν_eq (hM.normA _ (mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN))
        (inv_mem hyN)) b hb) hb ?_
      rw [show k * b * k⁻¹ = x * (y * (x⁻¹ * (y⁻¹ * b * y) * x) * y⁻¹) * x⁻¹ by rw [hkdef]; group,
        hxA _ hb3, hyA _ hb2, hM.inv_mul_mul_eq hx2 hb1, hxA _ hb1, hM.inv_mul_mul_eq hy2 hb,
        hyA _ hb, RuQCode.linApply_tv_comm]
    calc b * k = k * b * k⁻¹ * k := by rw [h1]
      _ = k * b := by group
  have hfixA : maskApply (adMat RuQCode.tvA) (μ k) = μ k := by
    have e1 : x * k * x⁻¹ * k = x ^ 2 * (y * (x ^ 2)⁻¹ * y⁻¹) := by
      rw [hkdef, pow_two]
      group
    have hmem : x * k * x⁻¹ * k ∈ gmsA L T := by
      rw [e1]
      exact mul_mem hx2 (hM.normA y hyN _ (inv_mem hx2))
    have h1 := (hM.ker _ (mul_mem (hxR' k hk) hk)).mpr hmem
    rw [hM.mul _ (hxR' k hk) _ hk, hxR k hk] at h1
    exact RuQCode.nat_eq_of_xor_eq_zero h1
  have hfixB : maskApply (adMat RuQCode.tvB) (μ k) = μ k := by
    have e1 : k * (y * k * y⁻¹) = x * y ^ 2 * x⁻¹ * (y ^ 2)⁻¹ := by
      rw [hkdef, pow_two]
      group
    have hmem : k * (y * k * y⁻¹) ∈ gmsA L T := by
      rw [e1]
      exact mul_mem (hM.normA x hxN _ hy2) (inv_mem hy2)
    have h1 := (hM.ker _ (mul_mem hk (hyR' k hk))).mpr hmem
    rw [hM.mul _ hk _ (hyR' k hk), hyR k hk] at h1
    exact (RuQCode.nat_eq_of_xor_eq_zero h1).symm
  obtain ⟨n, hn, hn₁, hn₂⟩ := RuQCode.exists_image_eq_of_commute RuQCode.tvB_mem RuQCode.tvA_mem
    (Ne.symm RuQCode.tvA_ne_tvB) RuQCode.linComp_tvA_tvB.symm (hM.lt k hk) hfixB hfixA
  obtain ⟨w, hw, rfl⟩ := hM.surj n hn
  refine ⟨w, hw, ?_, ?_⟩
  · have e1 : x * (w * y) * x⁻¹ * (w * y)⁻¹ = x * w * x⁻¹ * k * w⁻¹ := by
      rw [hkdef]
      group
    have hR : x * w * x⁻¹ * k ∈ R := mul_mem (hxR' w hw) hk
    rw [e1, ← hM.ker _ (mul_mem hR (inv_mem hw)), hM.mul _ hR _ (inv_mem hw),
      hM.mul _ (hxR' w hw) _ hk, hxR w hw, hM.μ_inv hw, ← hn₂]
    exact RuQCode.nat_xor_cancel' _ _
  · have e1 : (w * y) ^ 2 = w * (y * w * y⁻¹) * y ^ 2 := by
      rw [pow_two, pow_two]
      group
    have hR : w * (y * w * y⁻¹) ∈ R := mul_mem hw (hyR' w hw)
    rw [e1, ← hM.ker _ (mul_mem hR (hM.le hy2)), hM.mul _ hR _ (hM.le hy2),
      hM.mul _ hw _ (hyR' w hw), hyR w hw, hn₁, Nat.xor_self, Nat.zero_xor]
    exact (hM.ker _ (hM.le hy2)).mpr hy2

theorem exists_sq_eq_one_tv {x y : G} (hxN : x ∈ normalizer (R : Set G))
    (hyN : y ∈ normalizer (R : Set G))
    (hxA : ∀ b ∈ gmsA L T, ν (x * b * x⁻¹) = linApply RuQCode.tvA (ν b))
    (hyA : ∀ b ∈ gmsA L T, ν (y * b * y⁻¹) = linApply RuQCode.tvB (ν b))
    (hx2 : x ^ 2 ∈ gmsA L T) (hy2 : y ^ 2 ∈ gmsA L T) (hxy : x * y * x⁻¹ * y⁻¹ ∈ gmsA L T) :
    ∃ z ∈ normalizer (R : Set G), z ^ 2 = 1 ∧
      ∃ t ∈ [RuQCode.tvA, RuQCode.tvB, RuQCode.tvAB],
        ∀ b ∈ gmsA L T, ν (z * b * z⁻¹) = linApply t (ν b) := by
  set E := x⁻¹ * y * x * y⁻¹ with hEdef
  have hE : E ∈ gmsA L T := by
    rw [show E = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x by rw [hEdef]; group]
    exact hM.inv_conj_mem hxN (inv_mem hxy)
  have hxyN : x * y ∈ normalizer (R : Set G) := mul_mem hxN hyN
  have hxyA : ∀ b ∈ gmsA L T, ν (x * y * b * (x * y)⁻¹) = linApply RuQCode.tvAB (ν b) := by
    intro b hb
    rw [show x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ by group,
      hxA _ (hM.normA y hyN b hb), hyA b hb, RuQCode.linApply_tvAB]
  have e1 : (x * y) ^ 2 = x ^ 2 * E * y ^ 2 := by
    rw [hEdef, pow_two, pow_two, pow_two]
    group
  have hxy2 : (x * y) ^ 2 ∈ gmsA L T := by
    rw [e1]
    exact mul_mem (mul_mem hx2 hE) hy2
  have hν3 : ν ((x * y) ^ 2) = ν (x ^ 2) ^^^ ν E ^^^ ν (y ^ 2) := by
    rw [e1, hM.ν_mul _ (mul_mem hx2 hE) _ hy2, hM.ν_mul _ hx2 _ hE]
  have hp : linApply RuQCode.tvA (ν (x ^ 2)) = ν (x ^ 2) := by
    rw [← hxA _ hx2, show x * x ^ 2 * x⁻¹ = x ^ 2 by rw [pow_two]; group]
  have hq : linApply RuQCode.tvB (ν (y ^ 2)) = ν (y ^ 2) := by
    rw [← hyA _ hy2, show y * y ^ 2 * y⁻¹ = y ^ 2 by rw [pow_two]; group]
  have hs3 : linApply RuQCode.tvA (linApply RuQCode.tvB (ν (x ^ 2) ^^^ ν E ^^^ ν (y ^ 2))) =
      ν (x ^ 2) ^^^ ν E ^^^ ν (y ^ 2) := by
    rw [← hν3, ← RuQCode.linApply_tvAB, ← hxyA _ hxy2,
      show x * y * (x * y) ^ 2 * (x * y)⁻¹ = (x * y) ^ 2 by rw [pow_two]; group]
  have hrel : linApply RuQCode.tvA (ν (y ^ 2)) ^^^ ν (y ^ 2) =
      ν E ^^^ linApply RuQCode.tvB (ν E) := by
    have e2 : x⁻¹ * y ^ 2 * x * (y ^ 2)⁻¹ = E * (y * E * y⁻¹) := by
      rw [hEdef, pow_two]
      group
    have hm1 : x⁻¹ * y ^ 2 * x ∈ gmsA L T := hM.inv_conj_mem hxN hy2
    have hm2 : y * E * y⁻¹ ∈ gmsA L T := hM.normA y hyN E hE
    have h1 := congrArg ν e2
    rw [hM.ν_mul _ hm1 _ (inv_mem hy2), hM.ν_mul _ hE _ hm2, hM.inv_mul_mul_eq hx2 hy2,
      hxA _ hy2, hM.ν_inv hy2, hyA E hE] at h1
    exact h1
  by_cases h₁ : ∃ s, ν (x ^ 2) = linApply RuQCode.tvA s ^^^ s
  · obtain ⟨s, hs⟩ := h₁
    obtain ⟨e, he, h⟩ := hM.exists_sq_eq_one_of_ν_sq_eq hxN hxA hx2 hs
    refine ⟨x * e, mul_mem hxN (le_normalizer (hM.le he)), h, RuQCode.tvA, by simp,
      fun b hb => ?_⟩
    rw [hM.conj_mul_right he hb, hxA b hb]
  by_cases h₂ : ∃ s, ν (y ^ 2) = linApply RuQCode.tvB s ^^^ s
  · obtain ⟨s, hs⟩ := h₂
    obtain ⟨e, he, h⟩ := hM.exists_sq_eq_one_of_ν_sq_eq hyN hyA hy2 hs
    refine ⟨y * e, mul_mem hyN (le_normalizer (hM.le he)), h, RuQCode.tvB, by simp,
      fun b hb => ?_⟩
    rw [hM.conj_mul_right he hb, hyA b hb]
  by_cases h₃ : ∃ s, ν ((x * y) ^ 2) = linApply RuQCode.tvAB s ^^^ s
  · obtain ⟨s, hs⟩ := h₃
    obtain ⟨e, he, h⟩ := hM.exists_sq_eq_one_of_ν_sq_eq hxyN hxyA hxy2 hs
    refine ⟨x * y * e, mul_mem hxyN (le_normalizer (hM.le he)), h, RuQCode.tvAB, by simp,
      fun b hb => ?_⟩
    rw [hM.conj_mul_right he hb, hxyA b hb]
  exfalso
  refine RuQCode.sq_check _ _ _ hp (fun s hs => h₁ ⟨s, hs⟩) hq (fun s hs => h₂ ⟨s, hs⟩) hs3
    (fun s hs => h₃ ⟨s, ?_⟩) hrel
  rw [hν3, hs, RuQCode.linApply_tvAB]

variable [Finite G]

theorem exists_sq_eq_one_code
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {r : Lin8} (hr : r ∈ invList) :
    ∃ y ∈ normalizer (R : Set G), y ^ 2 = 1 ∧
      ∀ b ∈ gmsA L T, ν (y * b * y⁻¹) = linApply r (ν b) := by
  have hglA : RuQCode.tvA ∈ glList := (List.mem_filter.mp RuQCode.tvA_mem).1
  have hglB : RuQCode.tvB ∈ glList := (List.mem_filter.mp RuQCode.tvB_mem).1
  obtain ⟨x₀, hx₀N, hx₀A, hx₀R⟩ := hM.exists_code_eq hNC hidx hglA
  obtain ⟨u, hu, hux⟩ := hM.exists_mul_sq_mem hx₀N
    (hM.sq_mem_of_act hNC hx₀N hx₀A RuQCode.linApply_tvA_tvA) RuQCode.tvA_mem hx₀R
  obtain ⟨huA, huR⟩ := hM.act_mul_left hx₀N hu
  have hxN : u * x₀ ∈ normalizer (R : Set G) := mul_mem (le_normalizer hu) hx₀N
  have hxA : ∀ b ∈ gmsA L T, ν (u * x₀ * b * (u * x₀)⁻¹) = linApply RuQCode.tvA (ν b) :=
    fun b hb => by rw [huA b hb, hx₀A b hb]
  have hxR : ∀ x ∈ R, μ (u * x₀ * x * (u * x₀)⁻¹) = maskApply (adMat RuQCode.tvA) (μ x) :=
    fun x hx => by rw [huR x hx, hx₀R x hx]
  obtain ⟨y₀, hy₀N, hy₀A, hy₀R⟩ := hM.exists_code_eq hNC hidx hglB
  obtain ⟨u', hu', huy⟩ := hM.exists_mul_sq_mem hy₀N
    (hM.sq_mem_of_act hNC hy₀N hy₀A RuQCode.linApply_tvB_tvB) RuQCode.tvB_mem hy₀R
  obtain ⟨hu'A, hu'R⟩ := hM.act_mul_left hy₀N hu'
  have hy₁N : u' * y₀ ∈ normalizer (R : Set G) := mul_mem (le_normalizer hu') hy₀N
  have hy₁A : ∀ b ∈ gmsA L T, ν (u' * y₀ * b * (u' * y₀)⁻¹) = linApply RuQCode.tvB (ν b) :=
    fun b hb => by rw [hu'A b hb, hy₀A b hb]
  have hy₁R : ∀ x ∈ R, μ (u' * y₀ * x * (u' * y₀)⁻¹) = maskApply (adMat RuQCode.tvB) (μ x) :=
    fun x hx => by rw [hu'R x hx, hy₀R x hx]
  obtain ⟨w, hw, hcomm, hy2⟩ :=
    hM.exists_comm_mem hNC hxN hy₁N hxA hy₁A hxR hy₁R hux huy
  obtain ⟨hwA, -⟩ := hM.act_mul_left hy₁N hw
  have hyN : w * (u' * y₀) ∈ normalizer (R : Set G) := mul_mem (le_normalizer hw) hy₁N
  have hyA : ∀ b ∈ gmsA L T,
      ν (w * (u' * y₀) * b * (w * (u' * y₀))⁻¹) = linApply RuQCode.tvB (ν b) :=
    fun b hb => by rw [hwA b hb, hy₁A b hb]
  obtain ⟨z, hzN, hz2, t, ht, hzA⟩ :=
    hM.exists_sq_eq_one_tv hxN hyN hxA hyA hux hy2 hcomm
  obtain ⟨c, hc, hct⟩ := RuQCode.exists_conj_tv hr ht
  obtain ⟨h, hhN, hhA, -⟩ := hM.exists_code_eq hNC hidx hc
  refine ⟨h * z * h⁻¹, mul_mem (mul_mem hhN hzN) (inv_mem hhN), ?_, fun b hb => ?_⟩
  · rw [show (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ by rw [pow_two, pow_two]; group, hz2]
    group
  · have hb' := hM.inv_conj_mem hhN hb
    rw [show h * z * h⁻¹ * b * (h * z * h⁻¹)⁻¹ = h * (z * (h⁻¹ * b * h) * z⁻¹) * h⁻¹ by group,
      hhA _ (hM.normA z hzN _ hb'), hzA _ hb', hct, ← hhA _ hb',
      show h * (h⁻¹ * b * h) * h⁻¹ = b by group]

theorem exists_sq_eq_one_inv_mul_mem
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {g : G}
    (hgN : g ∈ normalizer (R : Set G)) (hgR : g ∉ R) (hg2 : g ^ 2 ∈ R) :
    ∃ y ∈ normalizer (R : Set G), y ^ 2 = 1 ∧ g⁻¹ * y ∈ R := by
  obtain ⟨r, hr, hrA, -⟩ := hM.act g hgN
  have h2 : ∀ s, linApply r (linApply r s) = s := by
    intro s
    obtain ⟨b, hb, rfl⟩ := hM.ν_surj s
    have hc : g ^ 2 * b = b * g ^ 2 := hM.central _ hg2 b hb
    rw [← hrA b hb, ← hrA _ (hM.normA g hgN b hb)]
    congr 1
    calc g * (g * b * g⁻¹) * g⁻¹ = g ^ 2 * b * (g ^ 2)⁻¹ := by rw [pow_two]; group
      _ = b * g ^ 2 * (g ^ 2)⁻¹ := by rw [hc]
      _ = b := by group
  have h1 : ∃ s, linApply r s ≠ s := by
    by_contra hno
    push Not at hno
    apply hgR
    rw [← hNC]
    refine mem_inf.mpr ⟨hgN, mem_centralizer_iff.mpr fun b hb => ?_⟩
    have h3 : g * b * g⁻¹ = b := hM.eq_of_ν_eq (hM.normA g hgN b hb) hb (by rw [hrA b hb, hno])
    calc b * g = g * b * g⁻¹ * g := by rw [h3]
      _ = g * b := by group
  obtain ⟨y, hyN, hy2, hyA⟩ :=
    hM.exists_sq_eq_one_code hNC hidx (RuQCode.mem_invList hr h2 h1)
  refine ⟨y, hyN, hy2, ?_⟩
  rw [← hNC]
  refine mem_inf.mpr ⟨mul_mem (inv_mem hgN) hyN, mem_centralizer_iff.mpr fun b hb => ?_⟩
  have heq : g * b * g⁻¹ = y * b * y⁻¹ :=
    hM.eq_of_ν_eq (hM.normA g hgN b hb) (hM.normA y hyN b hb) (by rw [hrA b hb, hyA b hb])
  calc b * (g⁻¹ * y) = g⁻¹ * (g * b * g⁻¹) * y := by group
    _ = g⁻¹ * (y * b * y⁻¹) * y := by rw [heq]
    _ = g⁻¹ * y * b := by group

theorem exists_sq_eq_one_inv_mul_mem_of_le
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {S : Subgroup G}
    (hSN : S ≤ normalizer (R : Set G)) (hRS : R ≤ S) :
    ∀ g ∈ S, g ∉ R → g ^ 2 ∈ R → ∃ y ∈ S, y ^ 2 = 1 ∧ g⁻¹ * y ∈ R := by
  intro g hg hgR hg2
  obtain ⟨y, -, hy2, hgy⟩ := hM.exists_sq_eq_one_inv_mul_mem hNC hidx (hSN hg) hgR hg2
  refine ⟨y, ?_, hy2, hgy⟩
  rw [show y = g * (g⁻¹ * y) by group]
  exact mul_mem hg (hRS hgy)

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
