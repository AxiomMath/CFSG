module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma p0f_card_fourGrp (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(fourGrp x₁ x₂) = 4 :=
  hc.wreath.fourGrp_eq_omega.2.2

private lemma p0f_card_ctxN_le (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxN tau x₁ x₂) ≤ 2 ^ 3 := by
  classical
  have hV : Nat.card ↥(fourGrp x₁ x₂) = 4 := p0f_card_fourGrp hc
  have hB : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  let f : ↥(ctxN tau x₁ x₂) → ↥(fourGrp x₁ x₂) × Bool := fun n =>
    if hn : (n : G) ∈ fourGrp x₁ x₂ then (⟨(n : G), hn⟩, true)
    else (⟨tau * (n : G), (l12_N_cases hc.toCtx4 n.2).resolve_left hn⟩, false)
  have hf : Function.Injective f := by
    intro n m hnm
    by_cases hn : (n : G) ∈ fourGrp x₁ x₂
    · by_cases hm : (m : G) ∈ fourGrp x₁ x₂
      · have h2 : (n : G) = (m : G) := by
          have h := congrArg (fun z : ↥(fourGrp x₁ x₂) × Bool => (z.1 : G)) hnm
          simp only [f] at h
          rw [dif_pos hn, dif_pos hm] at h
          exact h
        exact Subtype.ext h2
      · have h2 : (true : Bool) = false := by
          have h := congrArg (fun z : ↥(fourGrp x₁ x₂) × Bool => z.2) hnm
          simp only [f] at h
          rw [dif_pos hn, dif_neg hm] at h
          exact h
        exact absurd h2 (by decide)
    · by_cases hm : (m : G) ∈ fourGrp x₁ x₂
      · have h2 : (false : Bool) = true := by
          have h := congrArg (fun z : ↥(fourGrp x₁ x₂) × Bool => z.2) hnm
          simp only [f] at h
          rw [dif_neg hn, dif_pos hm] at h
          exact h
        exact absurd h2 (by decide)
      · have h2 : tau * (n : G) = tau * (m : G) := by
          have h := congrArg (fun z : ↥(fourGrp x₁ x₂) × Bool => (z.1 : G)) hnm
          simp only [f] at h
          rw [dif_neg hn, dif_neg hm] at h
          exact h
        exact Subtype.ext (mul_left_cancel h2)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hV, hB] at hle
  norm_num at hle ⊢
  exact hle

private lemma p0f_card_ctxX_le (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxX t tau x₁ x₂) ≤ 2 ^ 4 := by
  classical
  have hN : Nat.card ↥(ctxN tau x₁ x₂) ≤ 2 ^ 3 := p0f_card_ctxN_le hc
  have hB : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  let f : ↥(ctxX t tau x₁ x₂) → ↥(ctxN tau x₁ x₂) × Bool := fun z =>
    if hz : (z : G) ∈ ctxN tau x₁ x₂ then (⟨(z : G), hz⟩, true)
    else (⟨t * (z : G), (l12_X_cases hc.toCtx4 z.2).resolve_left hz⟩, false)
  have hf : Function.Injective f := by
    intro z z' hzz
    by_cases hz : (z : G) ∈ ctxN tau x₁ x₂
    · by_cases hz' : (z' : G) ∈ ctxN tau x₁ x₂
      · have h2 : (z : G) = (z' : G) := by
          have h := congrArg (fun w : ↥(ctxN tau x₁ x₂) × Bool => (w.1 : G)) hzz
          simp only [f] at h
          rw [dif_pos hz, dif_pos hz'] at h
          exact h
        exact Subtype.ext h2
      · have h2 : (true : Bool) = false := by
          have h := congrArg (fun w : ↥(ctxN tau x₁ x₂) × Bool => w.2) hzz
          simp only [f] at h
          rw [dif_pos hz, dif_neg hz'] at h
          exact h
        exact absurd h2 (by decide)
    · by_cases hz' : (z' : G) ∈ ctxN tau x₁ x₂
      · have h2 : (false : Bool) = true := by
          have h := congrArg (fun w : ↥(ctxN tau x₁ x₂) × Bool => w.2) hzz
          simp only [f] at h
          rw [dif_neg hz, dif_pos hz'] at h
          exact h
        exact absurd h2 (by decide)
      · have h2 : t * (z : G) = t * (z' : G) := by
          have h := congrArg (fun w : ↥(ctxN tau x₁ x₂) × Bool => (w.1 : G)) hzz
          simp only [f] at h
          rw [dif_neg hz, dif_neg hz'] at h
          exact h
        exact Subtype.ext (mul_left_cancel h2)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hB] at hle
  calc Nat.card ↥(ctxX t tau x₁ x₂) ≤ Nat.card ↥(ctxN tau x₁ x₂) * 2 := hle
    _ ≤ 2 ^ 3 * 2 := Nat.mul_le_mul_right 2 hN
    _ = 2 ^ 4 := by norm_num

theorem p0_card_R_le (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxR t tau x₁ x₂) ≤ 2 ^ 8 := by
  obtain ⟨φ, hφ⟩ := p0_exists_hom hc
  have hXcard : Nat.card ↥(ctxX t tau x₁ x₂) ≤ 2 ^ 4 := p0f_card_ctxX_le hc
  have hVcard : Nat.card ↥(fourGrp x₁ x₂) = 4 := p0f_card_fourGrp hc
  have hker : Nat.card φ.ker ≤ 2 ^ 4 := by
    let ψ : φ.ker → ↥(ctxX t tau x₁ x₂) :=
      fun g => ⟨((g : ↥(ctxR t tau x₁ x₂)) : G), hφ (g : ↥(ctxR t tau x₁ x₂)) g.2⟩
    have hinj : Function.Injective ψ := by
      intro g h hgh
      have h1 : ((g : ↥(ctxR t tau x₁ x₂)) : G) = ((h : ↥(ctxR t tau x₁ x₂)) : G) :=
        congrArg (fun z : ↥(ctxX t tau x₁ x₂) => (z : G)) hgh
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    calc Nat.card φ.ker ≤ Nat.card ↥(ctxX t tau x₁ x₂) :=
          Nat.card_le_card_of_injective ψ hinj
      _ ≤ 2 ^ 4 := hXcard
  have hrange : Nat.card φ.range ≤ 2 ^ 4 := by
    have hle : Nat.card φ.range ≤ Nat.card (↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂)) :=
      Nat.card_le_card_of_injective φ.range.subtype Subtype.coe_injective
    rw [Nat.card_prod, hVcard] at hle
    norm_num at hle ⊢
    exact hle
  rw [← Subgroup.card_ker_mul_card_range φ]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 2 ^ 4 * 2 ^ 4 := Nat.mul_le_mul hker hrange
    _ = 2 ^ 8 := by norm_num

theorem p0_R_quot (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    (∀ a ∈ ctxR t tau x₁ x₂, a ^ 2 ∈ ctxX t tau x₁ x₂) ∧
      ∀ a ∈ ctxR t tau x₁ x₂, ∀ b ∈ ctxR t tau x₁ x₂,
        a * b * a⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂ := by
  obtain ⟨φ, hφ⟩ := p0_exists_hom hc
  haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := hc.wreath.fourGrp_eq_omega.2.1.1
  have hExpV : ∀ x ∈ fourGrp x₁ x₂, x ^ 2 = 1 :=
    fun x hx => (hc.wreath.fourGrp_eq_omega.2.1).2 x hx
  have hsq_prod : ∀ z : ↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂), z ^ 2 = 1 := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      simpa [Subgroup.coe_pow] using hExpV (z.1 : G) z.1.2
    · apply Subtype.ext
      simpa [Subgroup.coe_pow] using hExpV (z.2 : G) z.2.2
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · let a' : ↥(ctxR t tau x₁ x₂) := ⟨a, ha⟩
    have h1 : φ (a' ^ 2) = 1 := by
      rw [map_pow]
      exact hsq_prod (φ a')
    have hmem : ((a' ^ 2 : ↥(ctxR t tau x₁ x₂)) : G) ∈ ctxX t tau x₁ x₂ := hφ (a' ^ 2) h1
    simpa [a', Subgroup.coe_pow, pow_two] using hmem
  · let a' : ↥(ctxR t tau x₁ x₂) := ⟨a, ha⟩
    let b' : ↥(ctxR t tau x₁ x₂) := ⟨b, hb⟩
    have h1 : φ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_comm' (φ a') (φ b')]
      group
    have hmem : ((a' * b' * a'⁻¹ * b'⁻¹ : ↥(ctxR t tau x₁ x₂)) : G) ∈ ctxX t tau x₁ x₂ :=
      hφ (a' * b' * a'⁻¹ * b'⁻¹) h1
    simpa [a', b', Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem p0_coset (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a ∉ ctxR t tau x₁ x₂ →
      b ∉ ctxR t tau x₁ x₂ → a⁻¹ * b ∈ ctxR t tau x₁ x₂ := by
  intro a haO b hbO haR hbR
  have habO : a⁻¹ * b ∈ ctxO t tau x₁ x₂ := mul_mem (inv_mem haO) hbO
  rw [p0_mem_R_iff hc habO]
  have haM : a ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ haO
  have hbM : b ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hbO
  have haC : a ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    have h : a ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hc.O_eq_C]; exact haO
    exact h.2
  have hcent_ainv : ∀ v ∈ fourGrp x₁ x₂, a⁻¹ * v * a = v := by
    intro v hv
    have hv' := (Subgroup.mem_centralizer_iff.mp haC) v hv
    calc a⁻¹ * v * a = a⁻¹ * (v * a) := by group
      _ = a⁻¹ * (a * v) := by rw [hv']
      _ = v := by group
  have hconj_a : ∃ va ∈ fourGrp x₁ x₂, a * t * a⁻¹ = (t * tau) * va := by
    have hmem : a * t * a⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨a, haM, rfl⟩
    rw [hc.tM] at hmem
    rcases hmem with hmem | hmem
    · exact absurd ((p0_mem_R_iff hc haO).mpr hmem) haR
    · rw [Set.mem_smul_set] at hmem
      obtain ⟨va, hvaV, hva⟩ := hmem
      exact ⟨va, hvaV, hva.symm⟩
  obtain ⟨va, hvaV, hconj_a⟩ := hconj_a
  have hconj_b : ∃ vb ∈ fourGrp x₁ x₂, b * t * b⁻¹ = (t * tau) * vb := by
    have hmem : b * t * b⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨b, hbM, rfl⟩
    rw [hc.tM] at hmem
    rcases hmem with hmem | hmem
    · exact absurd ((p0_mem_R_iff hc hbO).mpr hmem) hbR
    · rw [Set.mem_smul_set] at hmem
      obtain ⟨vb, hvbV, hvb⟩ := hmem
      exact ⟨vb, hvbV, hvb.symm⟩
  obtain ⟨vb, hvbV, hconj_b⟩ := hconj_b
  have htau_a : ∃ w ∈ fourGrp x₁ x₂, a⁻¹ * tau * a = tau * w := by
    have hmem : a⁻¹ * tau * a ∈ tau • (fourGrp x₁ x₂ : Set G) := by
      have h := p0_tau_conj_mem hc (g := a⁻¹) (inv_mem haM)
      simpa using h
    rw [Set.mem_smul_set] at hmem
    obtain ⟨w, hwV, hw⟩ := hmem
    exact ⟨w, hwV, hw.symm⟩
  obtain ⟨w, hwV, htau_a⟩ := htau_a
  have hx : a⁻¹ * t * a = t * ((tau * w) * va)⁻¹ := by
    have e2 : a⁻¹ * ((t * tau) * va) * a = (a⁻¹ * t * a) * ((tau * w) * va) := by
      have h2 : (a⁻¹ * t * a) * (a⁻¹ * tau * a) * (a⁻¹ * va * a) =
          (a⁻¹ * t * a) * ((tau * w) * va) := by
        rw [htau_a, hcent_ainv va hvaV]
        group
      have h3 : a⁻¹ * ((t * tau) * va) * a =
          (a⁻¹ * t * a) * (a⁻¹ * tau * a) * (a⁻¹ * va * a) := by group
      rw [h3, h2]
    have e1 : t = (a⁻¹ * t * a) * ((tau * w) * va) := by
      calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
        _ = a⁻¹ * ((t * tau) * va) * a := by rw [hconj_a]
        _ = (a⁻¹ * t * a) * ((tau * w) * va) := e2
    calc a⁻¹ * t * a
        = (a⁻¹ * t * a) * ((tau * w) * va) * ((tau * w) * va)⁻¹ := by group
      _ = t * ((tau * w) * va)⁻¹ := by rw [← e1]
  have hmain : (a⁻¹ * b) * t * (a⁻¹ * b)⁻¹ = t * (va⁻¹ * vb) := by
    have e2b : a⁻¹ * ((t * tau) * vb) * a = (a⁻¹ * t * a) * ((tau * w) * vb) := by
      have h2 : (a⁻¹ * t * a) * (a⁻¹ * tau * a) * (a⁻¹ * vb * a) =
          (a⁻¹ * t * a) * ((tau * w) * vb) := by
        rw [htau_a, hcent_ainv vb hvbV]
        group
      have h3 : a⁻¹ * ((t * tau) * vb) * a =
          (a⁻¹ * t * a) * (a⁻¹ * tau * a) * (a⁻¹ * vb * a) := by group
      rw [h3, h2]
    calc (a⁻¹ * b) * t * (a⁻¹ * b)⁻¹
        = a⁻¹ * (b * t * b⁻¹) * a := by group
      _ = a⁻¹ * ((t * tau) * vb) * a := by rw [hconj_b]
      _ = (a⁻¹ * t * a) * ((tau * w) * vb) := e2b
      _ = t * ((tau * w) * va)⁻¹ * ((tau * w) * vb) := by rw [hx]
      _ = t * (va⁻¹ * vb) := by group
  rw [hmain]
  rw [Set.mem_smul_set]
  exact ⟨va⁻¹ * vb, mul_mem (inv_mem hvaV) hvbV, rfl⟩

theorem p0_card_R_ge (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    2 ^ 8 ≤ Nat.card ↥(ctxR t tau x₁ x₂) := by
  have hRO : ctxR t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := p0_R_le_O hc
  have hri : (ctxR t tau x₁ x₂).relIndex (ctxO t tau x₁ x₂) ≤ 2 := by
    by_cases hne : ctxR t tau x₁ x₂ = ctxO t tau x₁ x₂
    · rw [hne, Subgroup.relIndex_self]; norm_num
    · have hlt : ctxR t tau x₁ x₂ < ctxO t tau x₁ x₂ := lt_of_le_of_ne hRO hne
      obtain ⟨a₀, ha₀O, ha₀R⟩ := Set.exists_of_ssubset hlt
      have h2 : (ctxR t tau x₁ x₂).relIndex (ctxO t tau x₁ x₂) = 2 := by
        rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
        refine ⟨a₀, ha₀O, ha₀R, fun b hbO => ?_⟩
        by_cases hbR : b ∈ ctxR t tau x₁ x₂
        · exact Or.inr hbR
        · refine Or.inl ?_
          have hbR' : b⁻¹ ∉ ctxR t tau x₁ x₂ := fun h => hbR (by simpa using inv_mem h)
          have h := p0_coset hc b⁻¹ (inv_mem hbO) a₀ ha₀O hbR' ha₀R
          simpa using h
      rw [h2]
  have hcard : Nat.card ↥(ctxO t tau x₁ x₂) ≤ 2 * Nat.card ↥(ctxR t tau x₁ x₂) := by
    have h1 := Subgroup.relIndex_mul_card (H := ctxR t tau x₁ x₂) (K := ctxO t tau x₁ x₂)
    have hinf : ctxR t tau x₁ x₂ ⊓ ctxO t tau x₁ x₂ = ctxR t tau x₁ x₂ :=
      inf_eq_left.mpr hRO
    rw [hinf] at h1
    calc Nat.card ↥(ctxO t tau x₁ x₂)
        = (ctxR t tau x₁ x₂).relIndex (ctxO t tau x₁ x₂) * Nat.card ↥(ctxR t tau x₁ x₂) :=
          h1.symm
      _ ≤ 2 * Nat.card ↥(ctxR t tau x₁ x₂) := Nat.mul_le_mul_right _ hri
  have hstep : 2 ^ 9 ≤ 2 * Nat.card ↥(ctxR t tau x₁ x₂) := by
    rw [← hc.card_O]; exact hcard
  have hstep2 : 2 * 2 ^ 8 ≤ 2 * Nat.card ↥(ctxR t tau x₁ x₂) := by
    calc 2 * 2 ^ 8 = 2 ^ 9 := by norm_num
      _ ≤ 2 * Nat.card ↥(ctxR t tau x₁ x₂) := hstep
  exact Nat.le_of_mul_le_mul_left hstep2 (by norm_num)

theorem p0_card_R (hc : Ctx8c t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxR t tau x₁ x₂) = 2 ^ 8 :=
  le_antisymm (p0_card_R_le hc) (p0_card_R_ge hc)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
