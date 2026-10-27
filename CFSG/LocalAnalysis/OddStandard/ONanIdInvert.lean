module

public import CFSG.LocalAnalysis.OddStandard.ONanFusInvert

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open scoped Pointwise

namespace InvSetting

variable {K : Type} [Group K] {S C A : Subgroup K} {j : K} (H : InvSetting S C A j)

include H

theorem not_conj_mem_of [Finite K] (hA4 : Nat.card A = 4)
    (hconj : ∀ u ∈ A, ∀ R : Subgroup K, R ≤ centralizer ({u} : Set K) → IsPGroup 2 R →
      (∀ r ∈ R, r * r = 1) → ∃ c ∈ centralizer ({u} : Set K), ∀ r ∈ R, c * r * c⁻¹ ∈ S)
    (hSyl : IsSylowOf 2 S (normalizer (H.U : Set K))) (k : K) :
    k⁻¹ * j * k ∉ C := by
  intro hk
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u := k⁻¹ * j * k with hu
  have hu2 : u * u = 1 := by
    calc u * u = k⁻¹ * (j * j) * k := by rw [hu]; group
      _ = 1 := by rw [H.j2]; group
  have huA : u ∈ A := H.A_of u hk hu2
  have huC : u ∈ C := H.AC huA
  have hUk : (H.U).map (MulAut.conj k⁻¹).toMonoidHom ≤ centralizer ({u} : Set K) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxj : x * j = j * x := H.U_comm hx H.j_mem_U
    show k⁻¹ * x * k⁻¹⁻¹ * u = u * (k⁻¹ * x * k⁻¹⁻¹)
    rw [hu, inv_inv]
    calc k⁻¹ * x * k * (k⁻¹ * j * k) = k⁻¹ * (x * j) * k := by group
      _ = k⁻¹ * (j * x) * k := by rw [hxj]
      _ = k⁻¹ * j * k * (k⁻¹ * x * k) := by group
  have hR2 : ∀ r ∈ (H.U).map (MulAut.conj k⁻¹).toMonoidHom, r * r = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 := H.U_sq hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k⁻¹ * x * k⁻¹⁻¹ * (k⁻¹ * x * k⁻¹⁻¹) = k⁻¹ * (x * x) * k := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨c, hcC, hc⟩ := hconj u huA _ hUk (H.U_isPGroup.map _) hR2
  set g := k * c⁻¹ with hg
  have hgS : ∀ x ∈ H.U, g⁻¹ * x * g ∈ S := fun x hx => by
    have h1 := hc _ ⟨x, hx, rfl⟩
    have e : c * ((MulAut.conj k⁻¹).toMonoidHom x) * c⁻¹ = g⁻¹ * x * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
      group
    rwa [e] at h1
  have hgj : g⁻¹ * j * g = u := by
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.1 hcC
    calc g⁻¹ * j * g = c * (k⁻¹ * j * k) * c⁻¹ := by rw [hg]; group
      _ = u := by rw [← hu, hcu, mul_inv_cancel_right]
  have hgu : g * u * g⁻¹ = j := by rw [← hgj]; group
  have hP2 : ∀ x ∈ H.U, ∀ y ∈ H.U,
      (g⁻¹ * (x * y) * g ∈ C ↔ (g⁻¹ * x * g ∈ C ↔ g⁻¹ * y * g ∈ C)) := by
    intro x hx y hy
    rw [show g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) by group]
    exact H.mul_mem_C_iff (hgS x hx) (hgS y hy)
  have hP1 : ∀ x ∈ H.U, ∀ y ∈ H.U, (x * y ∈ C ↔ (x ∈ C ↔ y ∈ C)) := fun x hx y hy =>
    H.mul_mem_C_iff (H.U_le_S hx) (H.U_le_S hy)
  have hjP2 : g⁻¹ * j * g ∈ C := by rw [hgj]; exact huC
  obtain ⟨e2, he2A, he2⟩ : ∃ e2 ∈ A, g⁻¹ * e2 * g ∉ C := by
    by_contra hcon
    push Not at hcon
    have hle : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 : g⁻¹ * a * g ∈ C := hcon a ha
      have h2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
        calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
          _ = 1 := by rw [H.A_sq a ha]; group
      have h3 := H.A_of _ h1 h2
      simpa [MulAut.conj_apply] using h3
    have heq : A.map (MulAut.conj g⁻¹).toMonoidHom = A :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g⁻¹).injective])
    rw [← heq] at huA
    obtain ⟨a, ha, hau⟩ := huA
    have haj : a = j := by
      have h1 : g⁻¹ * a * g = g⁻¹ * j * g := by
        rw [hgj]
        simpa [MulAut.conj_apply] using hau
      have := congrArg (fun y => g * y * g⁻¹) h1
      simpa [mul_assoc] using this
    exact H.jC (haj ▸ H.AC ha)
  obtain ⟨e, heA, he1, he⟩ : ∃ e ∈ A, e ≠ 1 ∧ g⁻¹ * e * g ∈ C := by
    set D : Subgroup K := C.comap (MulAut.conj g⁻¹).toMonoidHom with hD
    have hmemD : ∀ x, x ∈ D ↔ g⁻¹ * x * g ∈ C := fun x => by
      simp [hD]
    have h2 : D.relIndex A = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨e2, he2A, fun b hb => ?_⟩
      rw [hmemD, hmemD, hP2 b (H.A_le_U hb) e2 (H.A_le_U he2A)]
      by_cases hbD : g⁻¹ * b * g ∈ C
      · simp [hbD, he2]
      · simp [hbD, he2]
    have h3 := relIndex_mul_card (H := D) (K := A)
    rw [h2, hA4] at h3
    have h5 : (D ⊓ A : Subgroup K) ≠ ⊥ := (one_lt_card_iff_ne_bot _).1 (by omega)
    obtain ⟨⟨x, hx⟩, hx1⟩ := ne_bot_iff_exists_ne_one.1 h5
    exact ⟨x, hx.2, fun h => hx1 (Subtype.ext h), (hmemD x).1 hx.1⟩
  obtain ⟨c1, hc1C, hc1⟩ := H.comm_surj e heA
  obtain ⟨c2, hc2C, hc2⟩ := H.comm_surj u huA
  have heU : e ∈ H.U := H.A_le_U heA
  have heC : e ∈ C := H.AC heA
  have hee : e * e = 1 := H.A_sq e heA
  have hej : e * j = j * e := H.jA e heA
  have ht2 : ∀ c ∈ C, c * j * c⁻¹ * j = u → ∀ y ∈ H.U,
      (g * c * g⁻¹) * y * (g * c * g⁻¹)⁻¹ = if g⁻¹ * y * g ∈ C then y else j * y := by
    intro c hc hcc y hy
    have hyS := hgS y hy
    have e1 : (g * c * g⁻¹) * y * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * y * g) * c⁻¹) * g⁻¹ := by
      group
    rw [e1]
    split_ifs with hyC
    · rw [H.conj_of_mem hc hyC]
      group
    · rw [H.conj_of_not_mem hc hyS hyC, hcc]
      calc g * (u * (g⁻¹ * y * g)) * g⁻¹ = (g * u * g⁻¹) * y := by group
        _ = j * y := by rw [hgu]
  have ht2U : ∀ c ∈ C, c * j * c⁻¹ * j = u → ∀ y ∈ H.U,
      (g * c * g⁻¹) * y * (g * c * g⁻¹)⁻¹ ∈ H.U := by
    intro c hc hcc y hy
    rw [ht2 c hc hcc y hy]
    split_ifs
    · exact hy
    · exact mul_mem H.j_mem_U hy
  have hc2' : c2⁻¹ * j * c2⁻¹⁻¹ * j = u := by
    have hjc : j * c2 * j ∈ C := H.jN c2 hc2C
    calc c2⁻¹ * j * c2⁻¹⁻¹ * j = c2⁻¹ * (j * c2 * j) := by group
      _ = (j * c2 * j) * c2⁻¹ := H.C_comm _ (inv_mem hc2C) _ hjc
      _ = (c2 * j * c2⁻¹ * j)⁻¹ := by rw [show (c2 * j * c2⁻¹ * j)⁻¹ = j⁻¹ * c2 * j⁻¹ * c2⁻¹ by
            group, H.j_inv]
      _ = u := by rw [hc2, H.inv_of_A huA]
  have hNt2 : g * c2 * g⁻¹ ∈ normalizer (H.U : Set K) := by
    refine H.mem_normalizer_U_of (ht2U c2 hc2C hc2) fun y hy => ?_
    rw [show (g * c2 * g⁻¹)⁻¹ = g * c2⁻¹ * g⁻¹ by group]
    exact ht2U c2⁻¹ (inv_mem hc2C) hc2' y hy
  have ht1 : ∀ y ∈ H.U, c1 * y * c1⁻¹ = if y ∈ C then y else e * y := by
    intro y hy
    split_ifs with hyC
    · exact H.conj_of_mem hc1C hyC
    · rw [H.conj_of_not_mem hc1C (H.U_le_S hy) hyC, hc1]
  set x0 := c1 * (g * c2 * g⁻¹) with hx0
  have hM : ∀ y : K, x0 * y * x0⁻¹ =
      c1 * ((g * c2 * g⁻¹) * y * (g * c2 * g⁻¹)⁻¹) * c1⁻¹ := fun y => by rw [hx0]; group
  have hF1 : ∀ y ∈ H.U, x0 * y * x0⁻¹ =
      if g⁻¹ * y * g ∈ C then (if y ∈ C then y else e * y)
      else (if y ∈ C then e * (j * y) else j * y) := by
    intro y hy
    rw [hM, ht2 c2 hc2C hc2 y hy]
    split_ifs with h2 h1 h1
    · rw [ht1 y hy, ite_eq_left h1]
    · rw [ht1 y hy, ite_eq_right h1]
    · rw [ht1 (j * y) (mul_mem H.j_mem_U hy), ite_eq_right]
      rw [hP1 j H.j_mem_U y hy]
      exact fun h => H.jC (h.2 h1)
    · rw [ht1 (j * y) (mul_mem H.j_mem_U hy), ite_eq_left]
      rw [hP1 j H.j_mem_U y hy]
      exact ⟨fun h => absurd h H.jC, fun h => absurd h h1⟩
  have hF2 : ∀ y ∈ H.U, x0 * (x0 * y * x0⁻¹) * x0⁻¹ =
      if g⁻¹ * y * g ∈ C then y else e * y := by
    intro y hy
    have hjy : j * y ∈ H.U := mul_mem H.j_mem_U hy
    have hey : e * y ∈ H.U := mul_mem heU hy
    by_cases h2 : g⁻¹ * y * g ∈ C <;> by_cases h1 : y ∈ C
    · rw [hF1 y hy, ite_eq_left h2, ite_eq_left h1, hF1 y hy, ite_eq_left h2, ite_eq_left h1,
        ite_eq_left h2]
    · rw [hF1 y hy, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, hF1 (e * y) hey,
        ite_eq_left ((hP2 e heU y hy).2 ⟨fun _ => h2, fun _ => he⟩),
        ite_eq_right (fun h => h1 (((hP1 e heU y hy).1 h).1 heC)), ← mul_assoc, hee, one_mul]
    · have hejy : e * (j * y) ∈ H.U := mul_mem heU hjy
      have hnP2 : ¬ g⁻¹ * (e * (j * y)) * g ∈ C := by
        rw [hP2 e heU (j * y) hjy, hP2 j H.j_mem_U y hy]
        tauto
      have hnC : e * (j * y) ∉ C := by
        rw [hP1 e heU (j * y) hjy, hP1 j H.j_mem_U y hy]
        have := H.jC
        tauto
      rw [hF1 y hy, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2, hF1 (e * (j * y)) hejy,
        ite_eq_right hnP2,
        ite_eq_right hnC]
      calc j * (e * (j * y)) = (j * e) * (j * y) := by group
        _ = e * ((j * j) * y) := by rw [← hej]; group
        _ = e * y := by rw [H.j2, one_mul]
    · have hnP2 : ¬ g⁻¹ * (j * y) * g ∈ C := by
        rw [hP2 j H.j_mem_U y hy]
        tauto
      have hC' : j * y ∈ C := by
        rw [hP1 j H.j_mem_U y hy]
        have := H.jC
        tauto
      rw [hF1 y hy, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2, hF1 (j * y) hjy,
        ite_eq_right hnP2, ite_eq_left hC',
        ← mul_assoc j j y, H.j2, one_mul]
  have hF4 : ∀ y ∈ H.U, x0 ^ 4 * y * (x0 ^ 4)⁻¹ = y := by
    intro y hy
    have e1 : x0 ^ 4 * y * (x0 ^ 4)⁻¹ =
        x0 * (x0 * (x0 * (x0 * y * x0⁻¹) * x0⁻¹) * x0⁻¹) * x0⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e1, hF2 _ (by
      rw [hF2 y hy]
      split_ifs
      · exact hy
      · exact mul_mem heU hy), hF2 y hy]
    by_cases h2 : g⁻¹ * y * g ∈ C
    · rw [ite_eq_left h2, ite_eq_left h2]
    · have hnP2 : ¬ g⁻¹ * (e * y) * g ∈ C := by
        rw [hP2 e heU y hy]
        tauto
      rw [ite_eq_right h2, ite_eq_right hnP2, ← mul_assoc, hee, one_mul]
  have hF2e : x0 ^ 2 * e2 * (x0 ^ 2)⁻¹ = e * e2 := by
    have e1 : x0 ^ 2 * e2 * (x0 ^ 2)⁻¹ = x0 * (x0 * e2 * x0⁻¹) * x0⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    rw [e1, hF2 e2 (H.A_le_U he2A), ite_eq_right he2]
  have hx0N : x0 ∈ normalizer (H.U : Set K) := mul_mem (H.C_le_normalizer_U hc1C) hNt2
  obtain ⟨T, hT⟩ := hSyl
  have hTsq : ∀ s ∈ (T : Subgroup (normalizer (H.U : Set K))),
      (H.U).normalizerMonoidHom s ^ 2 = 1 := by
    intro s hs
    have hsS : (s : K) ∈ S := by
      have h0 : (s : K) ∈ (T : Subgroup (normalizer (H.U : Set K))).map
          (normalizer (H.U : Set K)).subtype := ⟨s, hs, rfl⟩
      rwa [hT] at h0
    rw [← map_pow]
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.one_apply, normalizerMonoidHom_coe, Subgroup.coe_pow]
    have hs2 : (s : K) ^ 2 ∈ H.U := by rw [pow_two]; exact H.A_le_U (H.sq_mem_A hsS)
    rw [H.U_comm hs2 y.2, mul_inv_cancel_right]
  have hx04 : (H.U).normalizerMonoidHom ⟨x0, hx0N⟩ ^ 4 = 1 := by
    rw [← map_pow]
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.one_apply, normalizerMonoidHom_coe, Subgroup.coe_pow]
    exact hF4 y y.2
  have hx02 := sq_eq_one_of_sylow_image (H.U).normalizerMonoidHom T hTsq hx04
  have h1 := congrArg (fun φ : MulAut H.U => ((φ ⟨e2, H.A_le_U he2A⟩ : H.U) : K)) hx02
  simp only [MulAut.one_apply] at h1
  rw [← map_pow, normalizerMonoidHom_coe, Subgroup.coe_pow] at h1
  rw [hF2e] at h1
  exact he1 (by simpa using h1)


end InvSetting

end CFSG.OddStandard.ONanRec
