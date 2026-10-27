module

public import CFSG.CGT.Stroth77.Extension24

public section

namespace CFSG.CGT.Stroth77

theorem m_t310 (m : ℕ) (hm : 2 ≤ m) : (StrothTypeIndex.t310 m hm).m = m := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t310 m hm)) 0
  simp only [Matrix.cons_val_zero] at h
  exact h.symm

theorem n_t310 (m : ℕ) (hm : 2 ≤ m) : (StrothTypeIndex.t310 m hm).n = m := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t310 m hm)) 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  exact h.symm

theorem type310_rho_apply_gens (m : ℕ) (hm : 2 ≤ m) (i j l : ℤ) :
    (Type310.action m hm).φρ (i • gen (Type310.k m) 0 + j • gen (Type310.k m) 1 +
        l • gen (Type310.k m) 2) =
      (i - 4 * l) • gen (Type310.k m) 0 + (-l) • gen (Type310.k m) 1 +
        (j - l) • gen (Type310.k m) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  have hc := Type310.rho_c m hm
  have ha := Type310.rho_a m hm
  have hb := Type310.rho_b m hm
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  rw [hc, ha, hb]
  module

theorem type310_t_apply_gens (m : ℕ) (hm : 2 ≤ m) (i j l : ℤ) :
    (Type310.action m hm).φt (i • gen (Type310.k m) 0 + j • gen (Type310.k m) 1 +
        l • gen (Type310.k m) 2) =
      (i - 4 * l) • gen (Type310.k m) 0 + (i - j - 2 * l) • gen (Type310.k m) 1 +
        (2 * 2 ^ (m - 2) * i - l) • gen (Type310.k m) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  have hc := Type310.t_c m hm
  have ha := Type310.t_a m hm
  have hb := Type310.t_b m hm
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  rw [hc, ha, hb]
  module

theorem t310_fixed_rho_t_mod (m : ℕ) (hm : 2 ≤ m) (M : ℕ) (y : Torus (Type310.k m))
    (hρ : ∃ z : Torus (Type310.k m), M • z = (Type310.action m hm).φρ y - y)
    (ht : ∃ z : Torus (Type310.k m), M • z = (Type310.action m hm).φt y - y) :
    ∃ z : Torus (Type310.k m), M • z = y := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type310.k m) y
  obtain ⟨zρ, hzρ⟩ := hρ
  obtain ⟨zt, hzt⟩ := ht
  obtain ⟨a0, a1, a2, rfl⟩ := torus_eq_zsmul_gens (Type310.k m) zρ
  obtain ⟨b0, b1, b2, rfl⟩ := torus_eq_zsmul_gens (Type310.k m) zt
  rw [type310_rho_apply_gens, nsmul_zsmul_gens] at hzρ
  rw [type310_t_apply_gens, nsmul_zsmul_gens] at hzt
  set K : ℤ := 2 ^ (m - 2) with hK
  have eρ : (i - 4 * l) • gen (Type310.k m) 0 + (-l) • gen (Type310.k m) 1 +
        (j - l) • gen (Type310.k m) 2 -
      (i • gen (Type310.k m) 0 + j • gen (Type310.k m) 1 + l • gen (Type310.k m) 2) =
      (-4 * l) • gen (Type310.k m) 0 + (-l - j) • gen (Type310.k m) 1 +
        (j - 2 * l) • gen (Type310.k m) 2 := by
    module
  have et : (i - 4 * l) • gen (Type310.k m) 0 + (i - j - 2 * l) • gen (Type310.k m) 1 +
        (2 * K * i - l) • gen (Type310.k m) 2 -
      (i • gen (Type310.k m) 0 + j • gen (Type310.k m) 1 + l • gen (Type310.k m) 2) =
      (-4 * l) • gen (Type310.k m) 0 + (i - 2 * j - 2 * l) • gen (Type310.k m) 1 +
        (2 * K * i - 2 * l) • gen (Type310.k m) 2 := by
    module
  rw [eρ] at hzρ
  rw [et] at hzt
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hzρ
  obtain ⟨-, ht1, ht2⟩ := zsmul_gens_dvd_of_eq hzt
  change (2 : ℤ) ^ m ∣ _ at hρ1 hρ2 ht1 ht2
  obtain ⟨p1, hp1⟩ := hρ1
  obtain ⟨p2, hp2⟩ := hρ2
  obtain ⟨q1, hq1⟩ := ht1
  obtain ⟨q2, hq2⟩ := ht2
  refine ⟨(b1 - 2 * a1) • gen (Type310.k m) 0 +
    (a2 + 2 * K * (b1 - 2 * a1) - b2) • gen (Type310.k m) 1 +
    (-a1 - a2 - 2 * K * (b1 - 2 * a1) + b2) • gen (Type310.k m) 2, ?_⟩
  rw [nsmul_zsmul_gens]
  apply zsmul_gens_eq_of_dvd
  · change (2 : ℤ) ^ m ∣ _
    exact ⟨q1 - 2 * p1, by linear_combination hq1 - 2 * hp1⟩
  · change (2 : ℤ) ^ m ∣ _
    exact ⟨-q2 + p2 + 2 * K * q1 - 4 * K * p1, by
      linear_combination -hq2 + hp2 + 2 * K * hq1 - 4 * K * hp1⟩
  · change (2 : ℤ) ^ m ∣ _
    exact ⟨q2 - p1 - p2 - 2 * K * q1 + 4 * K * p1, by
      linear_combination hq2 - hp1 - hp2 - 2 * K * hq1 + 4 * K * hp1⟩

theorem t310_fixed_rho_t (m : ℕ) (hm : 2 ≤ m) (y : Torus (Type310.k m))
    (hρ : (Type310.action m hm).φρ y = y) (ht : (Type310.action m hm).φt y = y) : y = 0 := by
  obtain ⟨z, hz⟩ := t310_fixed_rho_t_mod m hm 0 y ⟨0, by rw [hρ, sub_self, zero_smul]⟩
    ⟨0, by rw [ht, sub_self, zero_smul]⟩
  rw [← hz, zero_smul]

section Group

variable {S : Type*} [Group S] [Finite S] {B : Subgroup S} {m : ℕ} {hm : 2 ≤ m}

theorem ec_conjBy_ρ_mul_inv310 (D : StrothTypeData B (StrothTypeIndex.t310 m hm)) (y : B) :
    D.ec (conjBy D.ρ_mem y * y⁻¹) =
      (StrothTypeIndex.t310 m hm).action.φρ (D.ec y) - D.ec y := by
  rw [D.ec_mul, D.ec_inv, sub_eq_add_neg]
  congr 1
  exact D.ρ_conj y

theorem ec_conjBy_t_mul_inv310 (D : StrothTypeData B (StrothTypeIndex.t310 m hm)) (y : B) :
    D.ec (conjBy D.t_mem y * y⁻¹) =
      (StrothTypeIndex.t310 m hm).action.φt (D.ec y) - D.ec y := by
  rw [D.ec_mul, D.ec_inv, sub_eq_add_neg]
  congr 1
  exact D.t_conj y

theorem t310_fixed_rho_t_of_mem (D : StrothTypeData B (StrothTypeIndex.t310 m hm)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t310 m hm).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t310 m hm).action.φρ (D.ec y) from
      D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t310 m hm).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t310 m hm).action.φt (D.ec y) from
      D.t_conj y, ht]
  exact D.ec_eq_zero_iff.mp (t310_fixed_rho_t m hm (D.ec y) hρ' ht')

theorem t310_fixed_rho_t_mod_four_of_mem (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
    {y : B} (hρ : conjBy D.ρ_mem y * y⁻¹ ∈ fourB D) (ht : conjBy D.t_mem y * y⁻¹ ∈ fourB D) :
    y ∈ fourB D := by
  rw [mem_fourB_iff] at hρ ht ⊢
  rw [ec_conjBy_ρ_mul_inv310] at hρ
  rw [ec_conjBy_t_mul_inv310] at ht
  exact t310_fixed_rho_t_mod m hm 4 (D.ec y) hρ ht

theorem t310_fixed_rho_t_mod_two_of_mem (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
    {y : B}
    (hρ : ∃ z : Torus (StrothTypeIndex.t310 m hm).k, 2 • z = D.ec (conjBy D.ρ_mem y * y⁻¹))
    (ht : ∃ z : Torus (StrothTypeIndex.t310 m hm).k, 2 • z = D.ec (conjBy D.t_mem y * y⁻¹)) :
    ∃ z : Torus (StrothTypeIndex.t310 m hm).k, 2 • z = D.ec y := by
  rw [ec_conjBy_ρ_mul_inv310] at hρ
  rw [ec_conjBy_t_mul_inv310] at ht
  exact t310_fixed_rho_t_mod m hm 2 (D.ec y) hρ ht

end Group

theorem false_of_index_two_t310_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {m : ℕ} {hm : 2 ≤ m} (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  classical
  obtain ⟨d, hdC, hdB⟩ : ∃ d, d ∈ C ∧ d ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun x hx => hcon x hx : C ≤ B)
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  have hdH : (⟨d, hdC⟩ : C) ∉ B.subgroupOf C := fun h => hdB (Subgroup.mem_subgroupOf.mp h)
  have hd2H : (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ ∈ B.subgroupOf C :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr (by simp [hdH])
  have hd2B : d * d ∈ B := by
    simpa using Subgroup.mem_subgroupOf.mp hd2H
  let sB : B := ⟨d * d, hd2B⟩
  have hcommB : ∀ β : B, (β : S) * d = d * (β : S) := fun β =>
    Subgroup.mem_centralizer_iff.mp (hC hdC) (β : S) β.2
  have hfix : ∀ {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B),
      ∃ z : Torus (StrothTypeIndex.t310 m hm).k, 2 • z = D.ec (conjBy hgB sB * sB⁻¹) := by
    intro g hgC hgB
    obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel hdC hdB g hgC hgB
    have hβS : g⁻¹ * d * g = d * (β : S) := by
      simpa [conjBy_val] using congrArg Subtype.val hβ
    have hconj : conjBy hgB sB * sB⁻¹ = β * β := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjBy_val]
      change g⁻¹ * (d * d) * g * (d * d)⁻¹ = (β : S) * β
      have h1 : g⁻¹ * (d * d) * g = (g⁻¹ * d * g) * (g⁻¹ * d * g) := by group
      rw [h1, hβS]
      have h2 : d * (β : S) * (d * (β : S)) = d * d * ((β : S) * β) := by
        rw [mul_assoc d, ← mul_assoc (β : S) d, hcommB β]
        group
      rw [h2]
      have h3 : (β : S) * β * d = d * ((β : S) * β) := by
        rw [mul_assoc, hcommB β, ← mul_assoc, hcommB β, mul_assoc]
      calc d * d * ((β : S) * β) * (d * d)⁻¹
          = d * (d * ((β : S) * β)) * (d * d)⁻¹ := by group
        _ = d * ((β : S) * β * d) * (d * d)⁻¹ := by rw [h3]
        _ = d * ((β : S) * β) * d * (d * d)⁻¹ := by group
        _ = (β : S) * β * d * d * (d * d)⁻¹ := by rw [← h3]
        _ = (β : S) * β := by group
    exact ⟨D.ec β, by rw [hconj, D.ec_mul, two_nsmul]⟩
  obtain ⟨z, hz⟩ := t310_fixed_rho_t_mod_two_of_mem D (hfix (hL D.ρ_mem_L) D.ρ_mem)
    (hfix (hL D.t_mem_L) D.t_mem)
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = sB := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  have hσS : (σ : S) * σ = d * d := by
    simpa [sB] using congrArg Subtype.val hσ
  have hσC : (σ : S) ∈ C := hBC σ.2
  let w : S := d * (σ : S)⁻¹
  have hwC : w ∈ C := C.mul_mem hdC (C.inv_mem hσC)
  have hww : w * w = 1 := by
    have hcσ : (σ : S)⁻¹ * d = d * (σ : S)⁻¹ := by
      have h := hcommB σ⁻¹
      simpa using h
    calc w * w = d * ((σ : S)⁻¹ * d) * (σ : S)⁻¹ := by simp only [w]; group
      _ = d * (d * (σ : S)⁻¹) * (σ : S)⁻¹ := by rw [hcσ]
      _ = (d * d) * ((σ : S) * σ)⁻¹ := by group
      _ = 1 := by rw [hσS, mul_inv_cancel]
  have hwB : w ∈ B := hH w (hcS hwC) hww (hC hwC)
  apply hdB
  have hd : d = w * (σ : S) := by simp only [w]; group
  rw [hd]
  exact B.mul_mem hwB σ.2

theorem false_of_index_two_t310 {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {m : ℕ} {hm : 2 ≤ m} (hB : HasStrothType B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_t310_of_data hB.data hBC hC hrel hL hH hcS

section IndexFour

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem not_isCyclic_quotient_t310_of_data {m : ℕ} {hm : 2 ≤ m}
    [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ¬ IsCyclic (C ⧸ B.subgroupOf C) := by
  intro hcycQ
  classical
  have hcomm : ∀ x y : C, x * y = y * x :=
    comm_of_le_centralizer_of_cyclic_quotient hBC hC hcycQ
  let : CommGroup C := { mul_comm := hcomm }
  obtain ⟨q₀, hq₀⟩ := hcycQ.exists_generator
  obtain ⟨z, hzq⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₀
  let q : C ⧸ B.subgroupOf C := QuotientGroup.mk' (B.subgroupOf C) z
  have hQcard : Nat.card (C ⧸ B.subgroupOf C) = 4 :=
    card_quotient_four hBC hC hrel
  have hq_gen : Subgroup.zpowers q = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hqq : q = q₀ := hzq
    rw [hqq]
    exact hq₀ y
  have hq_order : orderOf q = 4 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hq_gen, hQcard]
  have hq4 : q ^ 4 = 1 := by
    rw [← hq_order]
    exact pow_orderOf_eq_one q
  have hz4H : z ^ 4 ∈ B.subgroupOf C := by
    have h : QuotientGroup.mk' (B.subgroupOf C) (z ^ 4) = 1 := by
      simpa [q, map_pow] using hq4
    exact (QuotientGroup.eq_one_iff _).mp h
  have hz4B : (z : S) ^ 4 ∈ B := by
    have := Subgroup.mem_subgroupOf.mp hz4H
    simpa using this
  have hq2 : q ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf q ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hq_order] at hdvd
    norm_num at hdvd
  have hAutSq : ∀ σ : MulAut (C ⧸ B.subgroupOf C), σ * σ = 1 := by
    intro σ
    have hcard : Nat.card (MulAut (C ⧸ B.subgroupOf C)) = 2 := by
      rw [IsCyclic.card_mulAut (C ⧸ B.subgroupOf C), hQcard]
      decide
    have h : orderOf σ ∣ 2 := by
      rw [← hcard]
      exact orderOf_dvd_natCard σ
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h
  have huvC : D.uv ∈ Subgroup.normalizer C := hL D.uv_mem_L
  have htC : D.t ∈ Subgroup.normalizer C := hL D.t_mem_L
  have hρC : D.ρ ∈ Subgroup.normalizer C := hL D.ρ_mem_L
  let Auv : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.uv huvC D.uv_mem
  let At : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.t htC D.t_mem
  let Ar : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.ρ hρC D.ρ_mem
  have hAuv_sq : Auv * Auv = 1 := by
    have h := conjByAutQuotient_pow D.uv huvC D.uv_mem 2
    simpa [pow_two, D.uv_sq, conjByAutQuotient_one] using h.symm
  have hAt_sq : At * At = 1 := by
    have h := conjByAutQuotient_pow D.t htC D.t_mem 2
    simpa [pow_two, D.t_sq, conjByAutQuotient_one] using h.symm
  have hAr_cube : Ar ^ 3 = 1 := by
    have h := conjByAutQuotient_pow D.ρ hρC D.ρ_mem 3
    have hρ3 : D.ρ * (D.ρ * D.ρ) = 1 := by
      rw [← mul_assoc]
      exact D.rho_cube
    simpa [pow_three, mul_assoc, hρ3, conjByAutQuotient_one] using h.symm
  have hcomp1 : (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC) =
      (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := by
    have h1 := conjByHom_mul D.uv D.ρ huvC hρC
    have h2 := conjByHom_mul D.ρ D.t hρC htC
    have h3 : conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) =
        conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) :=
      conjByHom_mul_eq huvC hρC hρC htC D.uv_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC)
        = conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) := h1.symm
      _ = conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) := h3
      _ = (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := h2
  have hcomp2 : (conjByHom D.ρ hρC).comp (conjByHom D.t htC) =
      (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
    have h1 := conjByHom_mul D.t D.ρ htC hρC
    have h2 := conjByHom_mul (D.ρ * D.uv) D.t (Subgroup.mul_mem _ hρC huvC) htC
    have h3 := conjByHom_mul D.ρ D.uv hρC huvC
    have h4 : conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) =
        conjByHom ((D.ρ * D.uv) * D.t) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) :=
      conjByHom_mul_eq htC hρC (Subgroup.mul_mem _ hρC huvC) htC D.t_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.t htC)
        = conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) := h1.symm
      _ = conjByHom ((D.ρ * D.uv) * D.t)
            (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) := h4
      _ = (conjByHom D.t htC).comp (conjByHom (D.ρ * D.uv)
            (Subgroup.mul_mem _ hρC huvC)) := h2
      _ = (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
            rw [h3]
  have hAr : Ar = 1 := by
    have hsq := hAutSq Ar
    calc Ar = Ar * 1 := (mul_one Ar).symm
      _ = Ar * (Ar * Ar) := by rw [hsq]
      _ = Ar * Ar * Ar := by rw [← mul_assoc]
      _ = Ar ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := hAr_cube
  have hAuv_Ar : Ar * Auv = At * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk (by simpa using DFunLike.congr_fun hcomp1 x)
  have hAt_Ar : Ar * At = At * Auv * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk
        (by simpa [MonoidHom.comp_apply] using DFunLike.congr_fun hcomp2 x)
  have hAuv_eq_At : Auv = At := by
    simpa [hAr] using hAuv_Ar
  have hAuv : Auv = 1 := by
    have h := hAt_Ar
    rw [hAr] at h
    have h' : At = At * Auv := by simpa using h
    have h'' : At * At = At * (At * Auv) := congrArg (fun x => At * x) h'
    rw [← mul_assoc] at h''
    have h''' : (1 : MulAut (C ⧸ B.subgroupOf C)) = Auv := by
      simpa [hAt_sq] using h''
    exact h'''.symm
  have hAt : At = 1 := hAuv_eq_At.symm.trans hAuv
  obtain ⟨bρ, hbρ⟩ := exists_mul_of_conjByAutQuotient_eq_one_Idx4 hcomm hρC D.ρ_mem hAr z
  obtain ⟨bt, hbt⟩ := exists_mul_of_conjByAutQuotient_eq_one_Idx4 hcomm htC D.t_mem hAt z
  have hcommρ : Commute (z : S) (bρ : S) := by
    have h := hcomm (⟨(z : S), z.2⟩ : C) ⟨(bρ : S), hBC bρ.2⟩
    exact congrArg Subtype.val h
  have hcommt : Commute (z : S) (bt : S) := by
    have h := hcomm (⟨(z : S), z.2⟩ : C) ⟨(bt : S), hBC bt.2⟩
    exact congrArg Subtype.val h
  have hρfix : conjBy D.ρ_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.ρ_mem z bρ hz4B hbρ hcommρ
  have htfix : conjBy D.t_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.t_mem z bt hz4B hbt hcommt
  have hy4 : (⟨(z : S) ^ 4, hz4B⟩ : B) ∈ fourB D :=
    t310_fixed_rho_t_mod_four_of_mem D hρfix htfix
  obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hy4
  let sC : C := ⟨s, hBC s.2⟩
  let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
  have hz4C : z ^ 4 = yC := by ext; rfl
  have hsC4 : sC ^ 4 = yC := by
    apply Subtype.ext
    simpa [sC, yC] using congrArg (fun x : B => (x : S)) hs
  let wC : C := z * sC⁻¹
  have hw4 : wC ^ 4 = 1 := by
    calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
          rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
      _ = yC * yC⁻¹ := by rw [hz4C, hsC4]
      _ = 1 := mul_inv_cancel yC
  let winv : C := wC ^ 2
  have hwinv2 : winv * winv = 1 := by
    have h : winv * winv = wC ^ 4 := by
      show (wC ^ 2) * (wC ^ 2) = wC ^ 4
      group
    rw [h, hw4]
  have hwinvS2 : (winv : S) * (winv : S) = 1 := by
    simpa using congrArg (fun x : C => (x : S)) hwinv2
  have hwinv_notB : (winv : S) ∉ B := by
    intro hmem
    have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
    have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
      (QuotientGroup.eq_one_iff winv).mpr hmemH
    have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
      have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
        (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
      rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
      simp [q]
    have hq2eq : q ^ 2 = 1 := by
      rw [← hmkw, ← map_pow]
      simpa [winv] using h1
    exact hq2 hq2eq
  exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))

theorem not_isCyclic_quotient_t310 {m : ℕ} {hm : 2 ≤ m}
    [hN : (B.subgroupOf C).Normal]
    (hB : HasStrothType B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ¬ IsCyclic (C ⧸ B.subgroupOf C) :=
  not_isCyclic_quotient_t310_of_data hB.data hBC hC hrel hL hH hcS


theorem isMulCommutative_of_relIndex_four_t310_of_data {m : ℕ} {hm : 2 ≤ m}
    [hN : (B.subgroupOf C).Normal] (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    IsMulCommutative C :=
  isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc
    fun _ hρ ht => t310_fixed_rho_t_of_mem D hρ ht

theorem isMulCommutative_of_relIndex_four_t310 {m : ℕ} {hm : 2 ≤ m}
    [hN : (B.subgroupOf C).Normal] (hB : HasStrothType B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    IsMulCommutative C :=
  isMulCommutative_of_relIndex_four_t310_of_data hB.data hBC hC hrel hL hncyc

end IndexFour

end CFSG.CGT.Stroth77
