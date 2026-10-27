module

public import CFSG.CGT.Stroth77.Extension24Square
public import CFSG.CGT.Stroth77.Extension23

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {τ : StrothTypeIndex}

section Square

variable (D : StrothTypeData B τ) (hk : ∀ i, 1 ≤ τ.k i) (hsq : ∀ x : C, (x : S) * x ∈ B)

@[expose] noncomputable def sqParityIdx4 (x : C) : Fin 3 → ZMod 2 :=
  parityTorus τ.k hk (D.ec ⟨(x : S) * x, hsq x⟩)

variable {D hk hsq}

theorem sqParityIdx4_mul (hcomm : ∀ x y : C, x * y = y * x) (x y : C) :
    sqParityIdx4 D hk hsq (x * y) = sqParityIdx4 D hk hsq x + sqParityIdx4 D hk hsq y := by
  have hxy : (⟨((x * y : C) : S) * ((x * y : C) : S), hsq (x * y)⟩ : B) =
      ⟨(x : S) * x, hsq x⟩ * ⟨(y : S) * y, hsq y⟩ := by
    apply Subtype.ext
    have h := congrArg Subtype.val (hcomm x y)
    simp only [Subgroup.coe_mul] at h ⊢
    calc (x : S) * y * ((x : S) * y) = x * ((y : S) * x) * y := by group
      _ = x * ((x : S) * y) * y := by rw [← h]
      _ = (x : S) * x * ((y : S) * y) := by group
  simp only [sqParityIdx4]
  rw [hxy, D.ec_mul, map_add]

theorem sqParityIdx4_of_mem (x : C) (hx : (x : S) ∈ B) : sqParityIdx4 D hk hsq x = 0 := by
  simp only [sqParityIdx4]
  rw [parityTorus_eq_zero_iff]
  refine ⟨D.ec ⟨x, hx⟩, ?_⟩
  have h : (⟨(x : S) * x, hsq x⟩ : B) = ⟨x, hx⟩ * ⟨x, hx⟩ := rfl
  rw [h, D.ec_mul, two_nsmul]

theorem mem_of_sqParityIdx4_eq_zero (hcomm : ∀ x y : C, x * y = y * x)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') (hBC : B ≤ C) (x : C) (h : sqParityIdx4 D hk hsq x = 0) :
    (x : S) ∈ B := by
  simp only [sqParityIdx4] at h
  rw [parityTorus_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = ⟨(x : S) * x, hsq x⟩ := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  have hσS : (σ : S) * σ = (x : S) * x := by
    simpa using congrArg Subtype.val hσ
  let σC : C := ⟨σ, hBC σ.2⟩
  let w : C := x * σC⁻¹
  have hww : (w : S) * w = 1 := by
    have hwC : w * w = 1 := by
      calc w * w = x * (σC⁻¹ * x) * σC⁻¹ := by simp only [w]; group
        _ = x * (x * σC⁻¹) * σC⁻¹ := by rw [hcomm σC⁻¹ x]
        _ = (x * x) * (σC * σC)⁻¹ := by group
        _ = 1 := by
          rw [mul_inv_eq_one]
          apply Subtype.ext
          simpa [σC] using hσS.symm
    simpa using congrArg Subtype.val hwC
  have hwB : (w : S) ∈ B := hH w (hcS w.2) hww (hC w.2)
  have hx : (x : S) = w * σ := by simp [w, σC]
  rw [hx]
  exact B.mul_mem hwB σ.2

theorem sqParityIdx4_conj {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x))
    {A : (Fin 3 → ZMod 2) → Fin 3 → ZMod 2}
    (hA : ∀ y, parityTorus τ.k hk (φ y) = A (parityTorus τ.k hk y)) (x : C) :
    sqParityIdx4 D hk hsq (conjBy hgC x) = A (sqParityIdx4 D hk hsq x) := by
  have h : (⟨((conjBy hgC x : C) : S) * (conjBy hgC x : C), hsq _⟩ : B) =
      conjBy hgB ⟨(x : S) * x, hsq x⟩ := by
    apply Subtype.ext
    simp only [conjBy_val]
    group
  simp only [sqParityIdx4]
  rw [h, hφ]
  exact hA _

theorem sqParityIdx4_of_sq_eq (hBC : B ≤ C) {x : C} {β : B} (hx : x * x = ⟨β, hBC β.2⟩) :
    sqParityIdx4 D hk hsq x = parityTorus τ.k hk (D.ec β) := by
  have h : (⟨(x : S) * x, hsq x⟩ : B) = β := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hx
  simp only [sqParityIdx4]
  rw [h]

end Square

theorem exists_sq_eq_of_sqParityIdx4 (D : StrothTypeData B τ) (hk : ∀ i, 1 ≤ τ.k i)
    (hsq : ∀ x : C, (x : S) * x ∈ B) (hBC : B ≤ C) (hcomm : ∀ x y : C, x * y = y * x)
    {x : C} {β : B} (h : sqParityIdx4 D hk hsq x = parityTorus τ.k hk (D.ec β)) :
    ∃ y : C, (x : S) * (y : S)⁻¹ ∈ B ∧ y * y = ⟨β, hBC β.2⟩ := by
  have hpar : parityTorus τ.k hk (D.ec (⟨(x : S) * x, hsq x⟩ * β⁻¹)) = 0 := by
    have h' : parityTorus τ.k hk (D.ec ⟨(x : S) * x, hsq x⟩) =
        parityTorus τ.k hk (D.ec β) := h
    rw [D.ec_mul, D.ec_inv, map_add, map_neg, h']
    exact add_neg_cancel _
  rw [parityTorus_eq_zero_iff] at hpar
  obtain ⟨z, hz⟩ := hpar
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = ⟨(x : S) * x, hsq x⟩ * β⁻¹ := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  let βC : C := ⟨β, hBC β.2⟩
  let σC : C := ⟨σ, hBC σ.2⟩
  have hσC2 : σC * σC = x * x * βC⁻¹ := by
    apply Subtype.ext
    simpa [σC, βC] using congrArg Subtype.val hσ
  refine ⟨x * σC⁻¹, ?_, ?_⟩
  · have hC' : x * (x * σC⁻¹)⁻¹ = σC := by
      rw [mul_inv_rev, inv_inv, ← mul_assoc, hcomm x σC, mul_assoc, mul_inv_cancel, mul_one]
    have : (x : S) * ((x * σC⁻¹ : C) : S)⁻¹ = σ := by
      simpa [σC] using congrArg Subtype.val hC'
    rw [this]
    exact σ.2
  · change x * σC⁻¹ * (x * σC⁻¹) = βC
    calc x * σC⁻¹ * (x * σC⁻¹) = x * (σC⁻¹ * x) * σC⁻¹ := by group
      _ = x * (x * σC⁻¹) * σC⁻¹ := by rw [hcomm σC⁻¹ x]
      _ = (x * x) * (σC * σC)⁻¹ := by group
      _ = (x * x) * (x * x * βC⁻¹)⁻¹ := by rw [hσC2]
      _ = βC := by
        rw [mul_inv_rev, inv_inv, ← mul_assoc, hcomm (x * x) βC, mul_assoc, mul_inv_cancel,
          mul_one]

theorem rhoBar300_fixed_check : ∀ v : Fin 3 → ZMod 2, (v ≠ 0 ∧ rhoBar300 v = v) →
    v = Pi.single 0 1 := by
  unfold rhoBar300
  decide

theorem sq_mem_of_relIndex_two_Idx4 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B)
    (x : C) : (x : S) * x ∈ B := by
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  by_cases hx : (x : S) ∈ B
  · exact B.mul_mem hx hx
  · have hxH : x ∉ B.subgroupOf C := fun h => hx (Subgroup.mem_subgroupOf.mp h)
    have h := (Subgroup.mul_mem_iff_of_index_two hindex (a := x) (b := x)).mpr Iff.rfl
    simpa using Subgroup.mem_subgroupOf.mp h

theorem exists_sq_eq_c_Idx4 (D : StrothTypeData B τ) (hk : ∀ i, 1 ≤ τ.k i)
    {A : (Fin 3 → ZMod 2) → Fin 3 → ZMod 2}
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = A (parityTorus τ.k hk y))
    (hAfix : ∀ v, v ≠ 0 → A v = v → v = Pi.single 0 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ∃ d : C, (d : S) ∉ B ∧ d * d = ⟨D.c, hBC D.c.2⟩ := by
  classical
  have hcomm : ∀ x y : C, x * y = y * x := comm_of_le_centralizer_of_type D hBC hC hrel
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_relIndex_two_Idx4 hBC hrel
  obtain ⟨d₀, hd₀C, hd₀B⟩ : ∃ d, d ∈ C ∧ d ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun x hx => hcon x hx : C ≤ B)
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  let P : C → Fin 3 → ZMod 2 := sqParityIdx4 D hk hsq
  have hPmul : ∀ x y, P (x * y) = P x + P y := sqParityIdx4_mul hcomm
  have hP0 : P ⟨d₀, hd₀C⟩ ≠ 0 := fun h =>
    hd₀B (mem_of_sqParityIdx4_eq_zero hcomm hC hH hcS hBC _ h)
  obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel hd₀C hd₀B D.ρ (hL D.ρ_mem_L) D.ρ_mem
  have hPρ : P (conjBy (hL D.ρ_mem_L) ⟨d₀, hd₀C⟩) = A (P ⟨d₀, hd₀C⟩) :=
    sqParityIdx4_conj (hL D.ρ_mem_L) D.ρ_mem D.ρ_conj hρpar _
  have hPβ : P (Subgroup.inclusion hBC β) = 0 := sqParityIdx4_of_mem _ β.2
  have hPfix : A (P ⟨d₀, hd₀C⟩) = P ⟨d₀, hd₀C⟩ := by
    rw [← hPρ, hβ, hPmul, hPβ, add_zero]
  have hPc : P ⟨d₀, hd₀C⟩ = parityTorus τ.k hk (D.ec D.c) := by
    rw [D.ec_c, Torus.c, parityTorus_gen]
    exact hAfix _ hP0 hPfix
  obtain ⟨d, hd₀d, hd⟩ := exists_sq_eq_of_sqParityIdx4 D hk hsq hBC hcomm hPc
  refine ⟨d, fun hdB => hd₀B ?_, hd⟩
  have h := B.mul_mem hd₀d hdB
  simpa using h

theorem exists_cocycle_index_two_of_data_Idx4 (D : StrothTypeData B τ) (hk : ∀ i, 1 ≤ τ.k i)
    {A : (Fin 3 → ZMod 2) → Fin 3 → ZMod 2}
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = A (parityTorus τ.k hk y))
    (hAfix : ∀ v, v ≠ 0 → A v = v → v = Pi.single 0 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ∃ zuv zt : Torus τ.k, 2 • zuv = τ.action.φuv Torus.c - Torus.c ∧
      2 • zt = τ.action.φt Torus.c - Torus.c ∧ zuv + τ.action.φuv zuv = 0 ∧
      zt + τ.action.φt zuv = zuv + τ.action.φuv zt := by
  classical
  have hcomm : ∀ x y : C, x * y = y * x := comm_of_le_centralizer_of_type D hBC hC hrel
  obtain ⟨d, hdB, hd⟩ := exists_sq_eq_c_Idx4 D hk hρpar hAfix hBC hC hrel hL hH hcS
  have huv := hL D.uv_mem_L
  have ht := hL D.t_mem_L
  obtain ⟨βuv, hβuv⟩ := exists_conj_eq hBC hrel d.2 hdB D.uv huv D.uv_mem
  obtain ⟨βt, hβt⟩ := exists_conj_eq hBC hrel d.2 hdB D.t ht D.t_mem
  have hd' : (⟨(d : S), d.2⟩ : C) = d := rfl
  rw [hd'] at hβuv hβt
  have hcommB : ∀ β : B, (β : S) * d = d * (β : S) := fun β =>
    Subgroup.mem_centralizer_iff.mp (hC d.2) (β : S) β.2
  have hsqrel : ∀ {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
      {β : B}, conjBy hgC d = d * Subgroup.inclusion hBC β →
      D.c * (β * β) = conjBy hgB D.c := by
    intro g hgC hgB β hβ
    apply Subtype.ext
    have hβS : g⁻¹ * (d : S) * g = d * (β : S) := by
      simpa [conjBy_val] using congrArg Subtype.val hβ
    have hdS : (d : S) * d = D.c := by simpa using congrArg Subtype.val hd
    simp only [Subgroup.coe_mul, conjBy_val]
    have hc : Commute (d : S) (β : S) := (hcommB β).symm
    calc (D.c : S) * ((β : S) * β) = (d : S) * d * ((β : S) * β) := by rw [hdS]
      _ = (d : S) * (β : S) * ((d : S) * β) := hc.mul_mul_mul_comm (d : S) (β : S)
      _ = (g⁻¹ * d * g) * (g⁻¹ * d * g) := by rw [hβS]
      _ = g⁻¹ * ((d : S) * d) * g := by group
      _ = g⁻¹ * (D.c : S) * g := by rw [hdS]
  have hconj_mul : ∀ {g : S} (hgC : g ∈ Subgroup.normalizer C)
      (hgB : g ∈ Subgroup.normalizer B) {βg : B}, conjBy hgC d = d * Subgroup.inclusion hBC βg →
      ∀ β : B, conjBy hgC (d * Subgroup.inclusion hBC β) =
        d * Subgroup.inclusion hBC (βg * conjBy hgB β) := by
    intro g hgC hgB βg hβg β
    rw [conjBy_mul, hβg]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, conjBy_val]
    group
  have huvc : ∀ x : B, D.ec (conjBy D.uv_mem x) = τ.action.φuv (D.ec x) := D.uv_conj
  have htc : ∀ x : B, D.ec (conjBy D.t_mem x) = τ.action.φt (D.ec x) := D.t_conj
  refine ⟨D.ec βuv, D.ec βt, ?_, ?_, ?_, ?_⟩
  · have h := congrArg D.ec (hsqrel huv D.uv_mem hβuv)
    rw [D.ec_mul, D.ec_mul, ← two_nsmul, huvc, D.ec_c] at h
    rw [← h]
    abel
  · have h := congrArg D.ec (hsqrel ht D.t_mem hβt)
    rw [D.ec_mul, D.ec_mul, ← two_nsmul, htc, D.ec_c] at h
    rw [← h]
    abel
  ·
    have h2 : conjBy huv (conjBy huv d) = d := conjBy_conjBy_of_sq huv D.uv_sq d
    rw [hβuv, hconj_mul huv D.uv_mem hβuv] at h2
    have h3 : Subgroup.inclusion hBC (βuv * conjBy D.uv_mem βuv) = 1 := by
      have := congrArg (fun x => d⁻¹ * x) h2
      simpa using this
    have h4 : βuv * conjBy D.uv_mem βuv = 1 :=
      Subgroup.inclusion_injective hBC (by rw [h3]; rfl)
    have h5 := congrArg D.ec h4
    rw [D.ec_mul, D.ec_one, huvc] at h5
    exact h5
  ·
    have hcomm' : conjBy ht (conjBy huv d) = conjBy huv (conjBy ht d) := by
      apply Subtype.ext
      simp only [conjBy_val]
      have h := D.uv_comm_t
      calc D.t⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.t
          = (D.uv * D.t)⁻¹ * (d : S) * (D.uv * D.t) := by group
        _ = (D.t * D.uv)⁻¹ * (d : S) * (D.t * D.uv) := by rw [h]
        _ = D.uv⁻¹ * (D.t⁻¹ * (d : S) * D.t) * D.uv := by group
    rw [hβuv, hβt, hconj_mul ht D.t_mem hβt, hconj_mul huv D.uv_mem hβuv] at hcomm'
    have h3 : Subgroup.inclusion hBC (βt * conjBy D.t_mem βuv) =
        Subgroup.inclusion hBC (βuv * conjBy D.uv_mem βt) := by
      have := congrArg (fun x => d⁻¹ * x) hcomm'
      simpa using this
    have h4 := congrArg D.ec (Subgroup.inclusion_injective hBC h3)
    rw [D.ec_mul, D.ec_mul, htc, huvc] at h4
    exact h4

theorem exists_cocycle_index_two_Idx4 (hB : HasStrothType B τ) (hk : ∀ i, 1 ≤ τ.k i)
    {A : (Fin 3 → ZMod 2) → Fin 3 → ZMod 2}
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = A (parityTorus τ.k hk y))
    (hAfix : ∀ v, v ≠ 0 → A v = v → v = Pi.single 0 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ∃ zuv zt : Torus τ.k, 2 • zuv = τ.action.φuv Torus.c - Torus.c ∧
      2 • zt = τ.action.φt Torus.c - Torus.c ∧ zuv + τ.action.φuv zuv = 0 ∧
      zt + τ.action.φt zuv = zuv + τ.action.φuv zt :=
  exists_cocycle_index_two_of_data_Idx4 hB.data hk hρpar hAfix hBC hC hrel hL hH hcS

theorem exists_cocycle_involution_index_two_of_data_Idx4 (D : StrothTypeData B τ)
    (hk : ∀ i, 1 ≤ τ.k i) {A : (Fin 3 → ZMod 2) → Fin 3 → ZMod 2}
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = A (parityTorus τ.k hk y))
    (hAfix : ∀ v, v ≠ 0 → A v = v → v = Pi.single 0 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (hg2 : g * g = 1) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x)) :
    ∃ z : Torus τ.k, 2 • z = φ Torus.c - Torus.c ∧ z + φ z = 0 := by
  classical
  obtain ⟨d, hdB, hd⟩ := exists_sq_eq_c_Idx4 D hk hρpar hAfix hBC hC hrel hL hH hcS
  obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel d.2 hdB g hgC hgB
  have hd' : (⟨(d : S), d.2⟩ : C) = d := rfl
  rw [hd'] at hβ
  have hcommB : ∀ β : B, (β : S) * d = d * (β : S) := fun β =>
    Subgroup.mem_centralizer_iff.mp (hC d.2) (β : S) β.2
  refine ⟨D.ec β, ?_, ?_⟩
  · have h : D.c * (β * β) = conjBy hgB D.c := by
      apply Subtype.ext
      have hβS : g⁻¹ * (d : S) * g = d * (β : S) := by
        simpa [conjBy_val] using congrArg Subtype.val hβ
      have hdS : (d : S) * d = D.c := by simpa using congrArg Subtype.val hd
      simp only [Subgroup.coe_mul, conjBy_val]
      have hc : Commute (d : S) (β : S) := (hcommB β).symm
      calc (D.c : S) * ((β : S) * β) = (d : S) * d * ((β : S) * β) := by rw [hdS]
        _ = (d : S) * (β : S) * ((d : S) * β) := hc.mul_mul_mul_comm (d : S) (β : S)
        _ = (g⁻¹ * d * g) * (g⁻¹ * d * g) := by rw [hβS]
        _ = g⁻¹ * ((d : S) * d) * g := by group
        _ = g⁻¹ * (D.c : S) * g := by rw [hdS]
    have h2 := congrArg D.ec h
    rw [D.ec_mul, D.ec_mul, ← two_nsmul, hφ, D.ec_c] at h2
    rw [← h2]
    abel
  · have h2 : conjBy hgC (conjBy hgC d) = d := conjBy_conjBy_of_sq hgC hg2 d
    have hc : conjBy hgC (Subgroup.inclusion hBC β) = Subgroup.inclusion hBC (conjBy hgB β) :=
      Subtype.ext rfl
    rw [hβ, conjBy_mul, hβ, hc] at h2
    have h3 : Subgroup.inclusion hBC (β * conjBy hgB β) = 1 := by
      apply Subtype.ext
      have h' := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h' ⊢
      calc (β : S) * (conjBy hgB β : S) = (d : S)⁻¹ * (d * β * (conjBy hgB β : S)) := by group
        _ = (d : S)⁻¹ * d := by rw [h']
        _ = 1 := inv_mul_cancel _
    have h4 : β * conjBy hgB β = 1 := Subgroup.inclusion_injective hBC (by rw [h3]; rfl)
    have h5 := congrArg D.ec h4
    rw [D.ec_mul, D.ec_one, hφ] at h5
    exact h5

theorem exists_cocycle_involution_index_two_Idx4 (hB : HasStrothType B τ)
    (hk : ∀ i, 1 ≤ τ.k i) {A : (Fin 3 → ZMod 2) → Fin 3 → ZMod 2}
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = A (parityTorus τ.k hk y))
    (hAfix : ∀ v, v ≠ 0 → A v = v → v = Pi.single 0 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (hg2 : g * g = 1) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ x : B, hB.data.ec (conjBy hgB x) = φ (hB.data.ec x)) :
    ∃ z : Torus τ.k, 2 • z = φ Torus.c - Torus.c ∧ z + φ z = 0 :=
  exists_cocycle_involution_index_two_of_data_Idx4 hB.data hk hρpar hAfix hBC hC hrel hL hH hcS
    hgC hgB hg2 hφ

section IndexFour

variable [hN : (B.subgroupOf C).Normal]

theorem L_le_normalizer_Idx4 (D : StrothTypeData B τ) : D.L ≤ Subgroup.normalizer B := by
  rw [StrothTypeData.L, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact D.uv_mem
  · exact D.t_mem
  · exact D.u_mem
  · exact D.ρ_mem

theorem exists_index_two_of_isCyclic_Idx4 (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hcyc : IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ C₂ : Subgroup S, B ≤ C₂ ∧ C₂ ≤ C ∧ Nat.card C₂ = 2 * Nat.card B ∧
      D.L ≤ Subgroup.normalizer C₂ := by
  classical
  have hcomm : ∀ x y : C, x * y = y * x :=
    comm_of_le_centralizer_of_cyclic_quotient hBC hC hcyc
  have hcommS : ∀ x y : S, x ∈ C → y ∈ C → x * y = y * x := fun x y hx hy => by
    simpa using congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  let C₂ : Subgroup S :=
    { carrier := {x | x ∈ C ∧ x * x ∈ B}
      one_mem' := ⟨C.one_mem, by simp [B.one_mem]⟩
      mul_mem' := by
        rintro x y ⟨hxC, hxB⟩ ⟨hyC, hyB⟩
        refine ⟨C.mul_mem hxC hyC, ?_⟩
        have h : x * y * (x * y) = (x * x) * (y * y) := by
          rw [mul_assoc x y, ← mul_assoc y x, hcommS y x hyC hxC]
          group
        rw [h]
        exact B.mul_mem hxB hyB
      inv_mem' := by
        rintro x ⟨hxC, hxB⟩
        refine ⟨C.inv_mem hxC, ?_⟩
        rw [← mul_inv_rev]
        exact B.inv_mem hxB }
  have hmemC₂ : ∀ x : S, x ∈ C₂ ↔ x ∈ C ∧ x * x ∈ B := fun x => Iff.rfl
  have hBC₂ : B ≤ C₂ := fun x hx => ⟨hBC hx, B.mul_mem hx hx⟩
  have hC₂C : C₂ ≤ C := fun x hx => hx.1
  have hQcard : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  obtain ⟨q, hq⟩ := hcyc.exists_generator
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q
  have hq_order : orderOf (QuotientGroup.mk' (B.subgroupOf C) z) = 4 := by
    have htop : Subgroup.zpowers (QuotientGroup.mk' (B.subgroupOf C) z) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr hq
    rw [orderOf_eq_card_of_zpowers_eq_top htop, hQcard]
  have hmkB : ∀ x : C, QuotientGroup.mk' (B.subgroupOf C) x = 1 ↔ (x : S) ∈ B := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hz2 : ((z : S) * z) ∉ B := by
    intro h
    have h1 : QuotientGroup.mk' (B.subgroupOf C) (z * z) = 1 := (hmkB (z * z)).mpr (by simpa)
    rw [map_mul, ← pow_two] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hq_order] at this
    norm_num at this
  have hz4 : ((z : S) * z) * ((z : S) * z) ∈ B := by
    have h1 : QuotientGroup.mk' (B.subgroupOf C) (z * z * (z * z)) = 1 := by
      have e4 : QuotientGroup.mk' (B.subgroupOf C) (z * z * (z * z)) =
          (QuotientGroup.mk' (B.subgroupOf C) z) ^ 4 := by
        simp only [map_mul, pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e4, ← hq_order]
      exact pow_orderOf_eq_one _
    simpa using (hmkB _).mp h1
  have hz2C₂ : (z : S) * z ∈ C₂ := ⟨C.mul_mem z.2 z.2, hz4⟩
  have hzC₂ : (z : S) ∉ C₂ := fun h => hz2 h.2
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hne1 : Nat.card C₂ ≠ Nat.card B := by
    intro h
    have hEq : B = C₂ := Subgroup.eq_of_le_of_card_ge hBC₂ (le_of_eq h)
    rw [← hEq] at hz2C₂
    exact hz2 hz2C₂
  have hne4 : Nat.card C₂ ≠ Nat.card C := by
    intro h
    have hEq : C₂ = C := Subgroup.eq_of_le_of_card_ge hC₂C (le_of_eq h.symm)
    rw [hEq] at hzC₂
    exact hzC₂ z.2
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hBC₂
  obtain ⟨r', hr'⟩ := Subgroup.card_dvd_of_le hC₂C
  have hrr : r * r' = 4 := by
    have h : Nat.card B * (r * r') = Nat.card B * 4 := by
      rw [← mul_assoc, ← hr, ← hr', hrel, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hne1 (by rw [hr, mul_one])
  have hr'1 : r' ≠ 1 := by
    rintro rfl
    exact hne4 (by rw [hr', mul_one])
  have hr2 : r = 2 := by
    have hrle : r ≤ 4 := by
      have hr'pos : 0 < r' := Nat.pos_of_ne_zero (by rintro rfl; simp at hrr)
      calc r = r * 1 := (mul_one r).symm
        _ ≤ r * r' := Nat.mul_le_mul_left r hr'pos
        _ = 4 := hrr
    interval_cases r <;> omega
  refine ⟨C₂, hBC₂, hC₂C, by rw [hr, hr2, mul_comm], ?_⟩
  intro g hg
  have hgC := hL hg
  have hgB := L_le_normalizer_Idx4 D hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e1 := Subgroup.mem_normalizer_iff.mp hgC x
  have e2 := Subgroup.mem_normalizer_iff.mp hgB (x * x)
  have h : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  show (x ∈ C ∧ x * x ∈ B) ↔ (g * x * g⁻¹ ∈ C ∧ g * x * g⁻¹ * (g * x * g⁻¹) ∈ B)
  rw [h, ← e1, ← e2]

theorem exists_sq_eq_a_of_data_Idx4 (D : StrothTypeData B τ) (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = rhoBar300 (parityTorus τ.k hk y))
    (hfix : ∀ y : B, conjBy D.ρ_mem y = y → conjBy D.t_mem y = y → y = 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ e : C, e * e = ⟨D.a, hBC D.a.2⟩ := by
  classical
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc hfix
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  let P : C → Fin 3 → ZMod 2 := sqParityIdx4 D hk hsq
  have hPmul : ∀ x y, P (x * y) = P x + P y := sqParityIdx4_mul hcomm
  have hPB : ∀ x : C, x ∈ B.subgroupOf C → P x = 0 := fun x hx =>
    sqParityIdx4_of_mem x (Subgroup.mem_subgroupOf.mp hx)
  have hP0 : ∀ x : C, P x = 0 → x ∈ B.subgroupOf C := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (mem_of_sqParityIdx4_eq_zero hcomm hC hH hcS hBC x hx)
  have hPinv : ∀ x, P x⁻¹ = -P x := by
    intro x
    have h := hPmul x⁻¹ x
    rw [inv_mul_cancel, hPB 1 (Subgroup.one_mem _)] at h
    exact (neg_eq_of_add_eq_zero_left h.symm).symm
  obtain ⟨x₁, x₂, h1, h2, h12⟩ := exists_gens_Idx4 hcardQ hncyc
  have hrange : ∀ y : C, P y = 0 ∨ P y = P x₁ ∨ P y = P x₂ ∨ P y = P x₁ + P x₂ := by
    intro y
    have hcoset := mem_cosets_Idx4 hcardQ hexp h1 h2 h12 y
    have key : ∀ x : C, y * x⁻¹ ∈ B.subgroupOf C → P y = P x := by
      intro x hx
      have h := hPmul (y * x⁻¹) x
      rw [inv_mul_cancel_right, hPB _ hx, zero_add] at h
      exact h
    rcases hcoset with h | h | h | h
    · exact Or.inl (hPB y h)
    · exact Or.inr (Or.inl (key x₁ h))
    · exact Or.inr (Or.inr (Or.inl (key x₂ h)))
    · exact Or.inr (Or.inr (Or.inr ((key _ h).trans (hPmul x₁ x₂))))
  have hv1 : P x₁ ≠ 0 := fun h => h1 (hP0 x₁ h)
  have hv2 : P x₂ ≠ 0 := fun h => h2 (hP0 x₂ h)
  have hv12 : P x₁ ≠ P x₂ := by
    intro h
    apply h12
    apply hP0
    rw [hPmul, hPinv, h]
    exact add_neg_cancel _
  have hρ1 := hrange (conjBy (hL D.ρ_mem_L) x₁)
  have hρ2 := hrange (conjBy (hL D.ρ_mem_L) x₂)
  rw [show P (conjBy (hL D.ρ_mem_L) x₁) = rhoBar300 (P x₁) from
    sqParityIdx4_conj (hL D.ρ_mem_L) D.ρ_mem D.ρ_conj hρpar x₁] at hρ1
  rw [show P (conjBy (hL D.ρ_mem_L) x₂) = rhoBar300 (P x₂) from
    sqParityIdx4_conj (hL D.ρ_mem_L) D.ρ_mem D.ρ_conj hρpar x₂] at hρ2
  obtain ⟨y, hy⟩ : ∃ y : C, P y = Pi.single 1 1 := by
    rcases rhoBar300_check (P x₁) (P x₂) ⟨hv1, hv2, hv12, hρ1, hρ2⟩ with h | h | h
    · exact ⟨x₁, h⟩
    · exact ⟨x₂, h⟩
    · exact ⟨x₁ * x₂, (hPmul x₁ x₂).trans h⟩
  have hya : P y = parityTorus τ.k hk (D.ec D.a) := by
    rw [hy, D.ec_a, Torus.a, parityTorus_gen]
  obtain ⟨e, -, he⟩ := exists_sq_eq_of_sqParityIdx4 D hk hsq hBC hcomm hya
  exact ⟨e, he⟩

theorem exists_sq_eq_a_Idx4 (hB : HasStrothType B τ) (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = rhoBar300 (parityTorus τ.k hk y))
    (hfix : ∀ y : B, conjBy hB.data.ρ_mem y = y → conjBy hB.data.t_mem y = y → y = 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ e : C, e * e = ⟨hB.data.a, hBC hB.data.a.2⟩ :=
  exists_sq_eq_a_of_data_Idx4 hB.data hk hρpar hfix hBC hC hrel hL hH hcS hncyc

theorem exists_cocycle_index_four_of_data_Idx4 (D : StrothTypeData B τ) (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = rhoBar300 (parityTorus τ.k hk y))
    (hfix : ∀ y : B, conjBy D.ρ_mem y = y → conjBy D.t_mem y = y → y = 1)
    (huva : parityTorus τ.k hk (τ.action.φuv Torus.a) = Pi.single 1 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ z : Torus τ.k, 2 • z = τ.action.φuv Torus.a - Torus.a ∧ z + τ.action.φuv z = 0 := by
  classical
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc hfix
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  obtain ⟨e, he⟩ := exists_sq_eq_a_of_data_Idx4 D hk hρpar hfix hBC hC hrel hL hH hcS hncyc
  have huv := hL D.uv_mem_L
  have huvc : ∀ x : B, D.ec (conjBy D.uv_mem x) = τ.action.φuv (D.ec x) := D.uv_conj
  have hPe : sqParityIdx4 D hk hsq e = Pi.single 1 1 := by
    rw [sqParityIdx4_of_sq_eq hBC he, D.ec_a, Torus.a, parityTorus_gen]
  have he2 : conjBy huv e * conjBy huv e = ⟨conjBy D.uv_mem D.a, hBC (conjBy D.uv_mem D.a).2⟩ := by
    rw [← conjBy_mul, he]
    rfl
  have hPe' : sqParityIdx4 D hk hsq (conjBy huv e) = Pi.single 1 1 := by
    rw [sqParityIdx4_of_sq_eq hBC he2, huvc, D.ec_a, huva]
  have hγB : ((e⁻¹ * conjBy huv e : C) : S) ∈ B := by
    apply mem_of_sqParityIdx4_eq_zero (hk := hk) (hsq := hsq) hcomm hC hH hcS hBC
    have hPinv : sqParityIdx4 D hk hsq e⁻¹ = -sqParityIdx4 D hk hsq e := by
      have h := sqParityIdx4_mul (D := D) (hk := hk) (hsq := hsq) hcomm e⁻¹ e
      rw [inv_mul_cancel, sqParityIdx4_of_mem 1 B.one_mem] at h
      exact (neg_eq_of_add_eq_zero_left h.symm).symm
    rw [sqParityIdx4_mul hcomm, hPinv, hPe, hPe']
    exact neg_add_cancel _
  let γ : B := ⟨((e⁻¹ * conjBy huv e : C) : S), hγB⟩
  have hγ : conjBy huv e = e * Subgroup.inclusion hBC γ := by
    apply Subtype.ext
    show ((conjBy huv e : C) : S) = (e : S) * ((e⁻¹ * conjBy huv e : C) : S)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcommB : ∀ β : B, (β : S) * e = e * (β : S) := fun β =>
    Subgroup.mem_centralizer_iff.mp (hC e.2) (β : S) β.2
  refine ⟨D.ec γ, ?_, ?_⟩
  ·
    have h : D.a * (γ * γ) = conjBy D.uv_mem D.a := by
      apply Subtype.ext
      have hγS : D.uv⁻¹ * (e : S) * D.uv = e * (γ : S) := by
        simpa [conjBy_val] using congrArg Subtype.val hγ
      have heS : (e : S) * e = D.a := by simpa using congrArg Subtype.val he
      simp only [Subgroup.coe_mul, conjBy_val]
      have hc : Commute (e : S) (γ : S) := (hcommB γ).symm
      calc (D.a : S) * ((γ : S) * γ) = (e : S) * e * ((γ : S) * γ) := by rw [heS]
        _ = (e : S) * (γ : S) * ((e : S) * γ) := hc.mul_mul_mul_comm (e : S) (γ : S)
        _ = (D.uv⁻¹ * e * D.uv) * (D.uv⁻¹ * e * D.uv) := by rw [hγS]
        _ = D.uv⁻¹ * ((e : S) * e) * D.uv := by group
        _ = D.uv⁻¹ * (D.a : S) * D.uv := by rw [heS]
    have h2 := congrArg D.ec h
    rw [D.ec_mul, D.ec_mul, ← two_nsmul, huvc, D.ec_a] at h2
    rw [← h2]
    abel
  ·
    have h2 : conjBy huv (conjBy huv e) = e := conjBy_conjBy_of_sq huv D.uv_sq e
    rw [hγ, conjBy_mul, hγ] at h2
    have h3 : Subgroup.inclusion hBC (γ * conjBy D.uv_mem γ) = 1 := by
      have := congrArg (fun x => e⁻¹ * x) h2
      have hc : conjBy huv (Subgroup.inclusion hBC γ) =
          Subgroup.inclusion hBC (conjBy D.uv_mem γ) := Subtype.ext rfl
      simp only [hc] at this
      apply Subtype.ext
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, inv_mul_cancel,
        Subgroup.coe_one] at h' ⊢
      calc (γ : S) * (conjBy D.uv_mem γ : S) = (e : S)⁻¹ * (e * γ * (conjBy D.uv_mem γ : S)) := by
            group
        _ = 1 := h'
    have h4 : γ * conjBy D.uv_mem γ = 1 :=
      Subgroup.inclusion_injective hBC (by rw [h3]; rfl)
    have h5 := congrArg D.ec h4
    rw [D.ec_mul, D.ec_one, huvc] at h5
    exact h5

theorem exists_cocycle_index_four_Idx4 (hB : HasStrothType B τ) (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = rhoBar300 (parityTorus τ.k hk y))
    (hfix : ∀ y : B, conjBy hB.data.ρ_mem y = y → conjBy hB.data.t_mem y = y → y = 1)
    (huva : parityTorus τ.k hk (τ.action.φuv Torus.a) = Pi.single 1 1)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ z : Torus τ.k, 2 • z = τ.action.φuv Torus.a - Torus.a ∧ z + τ.action.φuv z = 0 :=
  exists_cocycle_index_four_of_data_Idx4 hB.data hk hρpar hfix huva hBC hC hrel hL hH hcS hncyc

end IndexFour

end CFSG.CGT.Stroth77
