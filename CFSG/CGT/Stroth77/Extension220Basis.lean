module

public import CFSG.CGT.Stroth77.Extension220Lifts
public import CFSG.CGT.Stroth77.Extension220IndexTwo
public import CFSG.CGT.Stroth77.Extension25Common

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type230.k s) j

public section

namespace CFSG.CGT.Stroth77

open Matrix Ext218 Ext220

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {s : ℕ} {hm : 3 ≤ s + 2}


theorem GV_succ_t131 (s : ℕ) : Type120.GV (s + 4) = 4 * Type120.GV (s + 2 + 1) + 7 := by
  have h1 := Type120.three_mul_GV (s + 4)
  have h2 := Type120.three_mul_GV (s + 2 + 1)
  rw [show s + 4 - 1 = (s + 2) + 1 by omega, pow_succ] at h1
  rw [show s + 2 + 1 - 1 = s + 2 by omega] at h2
  linarith

theorem three_mul_GV_t131 (s : ℕ) :
    3 * Type120.GV (s + 2 + 1) + 7 = 16 * ((2 : ℤ) ^ s) ^ 2 := by
  have h2 := Type120.three_mul_GV (s + 2 + 1)
  rw [show s + 2 + 1 - 1 = s + 2 by omega, pow_add, four_pow_eq_two_pow_sq s] at h2
  linarith

theorem t131_k_pos (i : Fin 3) : 1 ≤ (StrothTypeIndex.t131 (s + 2) hm).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type131.k] <;> omega

theorem parityTorus_rho_t131 (y : Torus (StrothTypeIndex.t131 (s + 2) hm).k) :
    parityTorus _ t131_k_pos ((StrothTypeIndex.t131 (s + 2) hm).action.φρ y) =
      rhoBar300 (parityTorus _ t131_k_pos y) := by
  obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t131, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [rhoBar300, h2, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem t131_fixed_rho_t (y : Torus (StrothTypeIndex.t131 (s + 2) hm).k)
    (hρ : (StrothTypeIndex.t131 (s + 2) hm).action.φρ y = y)
    (ht : (StrothTypeIndex.t131 (s + 2) hm).action.φt y = y) : y = 0 := by
  have h := Type131.data (s + 2) (by omega)
  change matAct (Type131.k (s + 2)) Type131.ρM (Type131.compat_rho h) y = y at hρ
  change matAct (Type131.k (s + 2))
      (Type131.tM (Type120.iV (s + 2 + 1)) (Type120.FV (s + 2 + 1)) (Type120.GV (s + 2 + 1))
        (2 ^ (s + 2))) (Type131.compat_t h) y = y at ht
  change @Eq (Torus (Type131.k (s + 2))) y 0
  obtain ⟨v, hv⟩ := Torus.exists_ofInt (k := Type131.k (s + 2)) y
  rw [← hv] at hρ ht ⊢
  rw [matAct_ofInt, Torus.ofInt_eq_ofInt_iff] at hρ
  have h1 := (hρ 1).dvd
  have h2 := (hρ 2).dvd
  simp [Type131.ρM, ofCols_mulVec, Type131.k] at h1 h2
  have h3 : 3 * v 2 ≡ 3 * 0 [ZMOD 2 ^ (s + 2 + 1)] := by
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
    have := dvd_add h1 h2
    convert this using 1
    ring
  have hv2 : (2 : ℤ) ^ (s + 2 + 1) ∣ v 2 := by
    have := (int_modEq_of_mul_three_pow 1 (s + 2 + 1) (a := v 2) (b := 0)
      (by rw [pow_one]; exact h3)).symm.dvd
    simpa using this
  have hv1 : (2 : ℤ) ^ (s + 2 + 1) ∣ v 1 := by
    have := dvd_sub (dvd_mul_of_dvd_right hv2 2) h2
    convert this using 1
    ring
  have hv' : Torus.ofInt (Type131.k (s + 2)) v = Torus.ofInt (Type131.k (s + 2)) ![v 0, 0, 0] := by
    rw [Torus.ofInt_eq_ofInt_iff]
    intro r
    fin_cases r
    · rfl
    · exact (Int.modEq_zero_iff_dvd.mpr (by simpa [Type131.k] using hv1))
    · exact (Int.modEq_zero_iff_dvd.mpr (by simpa [Type131.k] using hv2))
  rw [hv'] at ht ⊢
  rw [matAct_ofInt, Torus.ofInt_eq_ofInt_iff] at ht
  have h4 := (ht 1).dvd
  simp [Type131.tM, ofCols_mulVec, Type131.k] at h4
  have hv0 : (2 : ℤ) ^ (s + 2) ∣ v 0 := by
    obtain ⟨q, hq⟩ := h4
    refine ⟨q, mul_right_cancel₀ (two_ne_zero (α := ℤ)) ?_⟩
    rw [hq, pow_succ]
    ring
  rw [Torus.ofInt_eq_zero_iff]
  intro r
  fin_cases r
  · simpa [Type131.k] using hv0
  · simp
  · simp

theorem t131_fixed_rho_t_of_mem (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm))
    {y : B} (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t131 (s + 2) hm).action.φρ (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t131 (s + 2) hm).action.φρ (D.ec y)
      from D.ρ_conj y, hρ]
  have ht' : (StrothTypeIndex.t131 (s + 2) hm).action.φt (D.ec y) = D.ec y := by
    rw [← show D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t131 (s + 2) hm).action.φt (D.ec y)
      from D.t_conj y, ht]
  exact D.ec_eq_zero_iff.mp (t131_fixed_rho_t (D.ec y) hρ' ht')

theorem conjBy_ρ_a_t131 (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm)) :
    conjBy D.ρ_mem D.a = D.b := by
  apply D.ec_injective
  have h := D.ρ_conj D.a
  rw [show D.e (Additive.ofMul D.a) = Torus.a from D.ec_a,
    show (Torus.a : Torus (StrothTypeIndex.t131 (s + 2) hm).k) =
      (0 : ℤ) • gen _ 0 + (1 : ℤ) • gen _ 1 + (0 : ℤ) • gen _ 2 from gen_one_eq218,
    rho_apply_gens_t131] at h
  rw [show D.ec (conjBy D.ρ_mem D.a) = _ from h, D.ec_b]
  simp

theorem conj_ρ_sq_t131 (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e : C} (he : e * e = ⟨D.a, hBC D.a.2⟩) :
    conjBy (hL D.ρ_mem_L) e * conjBy (hL D.ρ_mem_L) e = ⟨D.b, hBC D.b.2⟩ := by
  rw [← conjBy_mul, he]
  apply Subtype.ext
  have h := congrArg Subtype.val (conjBy_ρ_a_t131 D)
  simpa [conjBy_val] using h

section Basis

variable [hN : (B.subgroupOf C).Normal]

theorem closure_c_e_conj_t131_of_data (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) :
    Subgroup.closure (Set.range ![(⟨D.c, hBC D.c.2⟩ : C), e,
      conjBy (hL D.ρ_mem_L) e]) = ⊤ := by
  classical
  let f : C := conjBy (hL D.ρ_mem_L) e
  have hf : f * f = ⟨D.b, hBC D.b.2⟩ := conj_ρ_sq_t131 D hBC hL he
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc
      (fun _ hρ ht => t131_fixed_rho_t_of_mem D hρ ht)
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  let P : C → Fin 3 → ZMod 2 := sqParityIdx4 D t131_k_pos hsq
  have hPe : P e = Pi.single 1 1 := by
    rw [show P e = _ from sqParityIdx4_of_sq_eq hBC he, D.ec_a, Torus.a, parityTorus_gen]
  have hPf : P f = Pi.single 2 1 := by
    rw [show P f = _ from sqParityIdx4_of_sq_eq hBC hf, D.ec_b, Torus.b, parityTorus_gen]
  have hPB : ∀ x : C, x ∈ B.subgroupOf C → P x = 0 := fun x hx =>
    sqParityIdx4_of_mem x (Subgroup.mem_subgroupOf.mp hx)
  have he_not : e ∉ B.subgroupOf C := fun h => by
    have := hPB e h
    rw [hPe] at this
    exact absurd (congrFun this 1) (by simp)
  have hf_not : f ∉ B.subgroupOf C := fun h => by
    have := hPB f h
    rw [hPf] at this
    exact absurd (congrFun this 2) (by simp)
  have hef_not : e * f⁻¹ ∉ B.subgroupOf C := fun h => by
    have h1 := hPB _ h
    have h2 : P (e * f⁻¹ * f) = P (e * f⁻¹) + P f := sqParityIdx4_mul hcomm _ _
    rw [inv_mul_cancel_right, h1, zero_add, hPe, hPf] at h2
    exact absurd (congrFun h2 1) (by simp)
  let K := Subgroup.closure (Set.range ![(⟨D.c, hBC D.c.2⟩ : C), e, f])
  have hcK : (⟨D.c, hBC D.c.2⟩ : C) ∈ K := Subgroup.subset_closure ⟨0, rfl⟩
  have heK : e ∈ K := Subgroup.subset_closure ⟨1, rfl⟩
  have hfK : f ∈ K := Subgroup.subset_closure ⟨2, rfl⟩
  have hBK : ∀ x : C, x ∈ B.subgroupOf C → x ∈ K := by
    intro x hx
    have hxB : (x : S) ∈ B := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨i, j, l, hijl⟩ := torus_eq_zsmul_gens _ (D.ec ⟨x, hxB⟩)
    have hβ := eq_zpow_c_a_b_Idx4 D hijl
    have hxeq : x = (⟨D.c, hBC D.c.2⟩ : C) ^ i * (e * e) ^ j * (f * f) ^ l := by
      rw [he, hf]
      apply Subtype.ext
      have h := congrArg Subtype.val hβ
      simpa using h
    rw [hxeq]
    exact K.mul_mem (K.mul_mem (K.zpow_mem hcK i) (K.zpow_mem (K.mul_mem heK heK) j))
      (K.zpow_mem (K.mul_mem hfK hfK) l)
  rw [eq_top_iff]
  intro y _
  rcases mem_cosets_Idx4 hcardQ hexp he_not hf_not hef_not y with h | h | h | h
  · exact hBK y h
  · have := K.mul_mem (hBK _ h) heK
    rw [inv_mul_cancel_right] at this
    exact this
  · have := K.mul_mem (hBK _ h) hfK
    rw [inv_mul_cancel_right] at this
    exact this
  · have := K.mul_mem (hBK _ h) (K.mul_mem heK hfK)
    rw [inv_mul_cancel_right] at this
    exact this

theorem closure_c_e_conj_t131 (hB : HasStrothType B (StrothTypeIndex.t131 (s + 2) hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨hB.data.a, hBC hB.data.a.2⟩) :
    Subgroup.closure (Set.range ![(⟨hB.data.c, hBC hB.data.c.2⟩ : C), e,
      conjBy (hL hB.data.ρ_mem_L) e]) = ⊤ :=
  closure_c_e_conj_t131_of_data hB.data hBC hC hrel hL hncyc he

theorem exists_torusBasis_t131_of_data (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) :
    ∃ E : Torus (Type230.k s) ≃+ Additive C,
      E (𝔤 s 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩ ∧ E (𝔤 s 1) = Additive.ofMul e ∧
        E (𝔤 s 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) e) := by
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc
      (fun _ hρ ht => t131_fixed_rho_t_of_mem D hρ ht)
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  let x : Fin 3 → C := ![⟨D.c, hBC D.c.2⟩, e, conjBy (hL D.ρ_mem_L) e]
  have hf := conj_ρ_sq_t131 D hBC hL he
  have hm' : (StrothTypeIndex.t131 (s + 2) hm).m = s + 2 := by
    have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t131 (s + 2) hm)) 0
    simp only [Matrix.cons_val_zero] at h
    exact h.symm
  have hn' : (StrothTypeIndex.t131 (s + 2) hm).n = s + 3 := by
    have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t131 (s + 2) hm)) 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
    exact h.symm
  have hcpow : (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ (s + 2)) = 1 := by
    apply Subtype.ext
    have h : D.c ^ (2 ^ (s + 2)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_c, hm']
    simpa using congrArg Subtype.val h
  have hapow : (⟨D.a, hBC D.a.2⟩ : C) ^ (2 ^ (s + 3)) = 1 := by
    apply Subtype.ext
    have h : D.a ^ (2 ^ (s + 3)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_a, hn']
    simpa using congrArg Subtype.val h
  have hbpow : (⟨D.b, hBC D.b.2⟩ : C) ^ (2 ^ (s + 3)) = 1 := by
    apply Subtype.ext
    have h : D.b ^ (2 ^ (s + 3)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_b, hn']
    simpa using congrArg Subtype.val h
  have hx : ∀ i, x i ^ (2 ^ Type230.k s i) = 1 := by
    intro i
    fin_cases i
    · exact hcpow
    · change e ^ (2 ^ (s + 3 + 1)) = 1
      rw [pow_succ', pow_mul, sq, he, hapow]
    · change conjBy (hL D.ρ_mem_L) e ^ (2 ^ (s + 3 + 1)) = 1
      rw [pow_succ', pow_mul, sq, hf, hbpow]
  have hgen : Subgroup.closure (Set.range x) = ⊤ :=
    closure_c_e_conj_t131_of_data D hBC hC hrel hL hncyc he
  have hcard : Nat.card (Torus (Type230.k s)) = Nat.card C := by
    rw [natCard_torus, hrel, D.card]
    change 2 ^ ((s + 2) + (s + 4) + (s + 4)) = 4 * 2 ^ ((s + 2) + (s + 3) + (s + 3))
    rw [show (s + 2) + (s + 4) + (s + 4) = 2 + ((s + 2) + (s + 3) + (s + 3)) by ring, pow_add]
    norm_num
  obtain ⟨E, hE⟩ := exists_torusEquiv_Idx4 hcomm x hx hgen hcard
  exact ⟨E, hE 0, hE 1, hE 2⟩

theorem exists_torusBasis_t131 (hB : HasStrothType B (StrothTypeIndex.t131 (s + 2) hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨hB.data.a, hBC hB.data.a.2⟩) :
    ∃ E : Torus (Type230.k s) ≃+ Additive C,
      E (𝔤 s 0) = Additive.ofMul ⟨hB.data.c, hBC hB.data.c.2⟩ ∧ E (𝔤 s 1) = Additive.ofMul e ∧
        E (𝔤 s 2) = Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) e) :=
  exists_torusBasis_t131_of_data hB.data hBC hC hrel hL hncyc he

end Basis

section Transport

variable (D : StrothTypeData B (StrothTypeIndex.t131 (s + 2) hm)) (hBC : B ≤ C)
  (hL : D.L ≤ Subgroup.normalizer C) {e : C}
  (E : Torus (Type230.k s) ≃+ Additive C)
  (hE0 : E (𝔤 s 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩) (hE1 : E (𝔤 s 1) = Additive.ofMul e)
  (hE2 : E (𝔤 s 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) e))
  (he : e * e = ⟨D.a, hBC D.a.2⟩)

include hE0 hE1 hE2 he in
theorem E_symm_incl_t131 (β : B) {i j l : ℤ}
    (h : D.ec β = i • gen (StrothTypeIndex.t131 (s + 2) hm).k 0 +
      j • gen (StrothTypeIndex.t131 (s + 2) hm).k 1 +
      l • gen (StrothTypeIndex.t131 (s + 2) hm).k 2) :
    E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C)) = i • (𝔤 s 0) + (2 * j) • (𝔤 s 1) +
        (2 * l) • (𝔤 s 2) := by
  have hf := conj_ρ_sq_t131 D hBC hL he
  have hβ := eq_zpow_c_a_b_Idx4 D h
  have hβC : (⟨β, hBC β.2⟩ : C) =
      (⟨D.c, hBC D.c.2⟩ : C) ^ i * (e * e) ^ j * (conjBy (hL D.ρ_mem_L) e *
        conjBy (hL D.ρ_mem_L) e) ^ l := by
    rw [he, hf]
    apply Subtype.ext
    simpa using congrArg Subtype.val hβ
  rw [AddEquiv.symm_apply_eq, hβC, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hE0, hE1,
    hE2, ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow, ofMul_mul, ofMul_mul,
    ← two_zsmul, ← two_zsmul, smul_smul, smul_smul, mul_comm j 2, mul_comm l 2]

include hE0 hE1 hE2 he in
theorem alpha_incl_t131 {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (β : B) {i j l : ℤ}
    (h : D.ec (conjBy hgB β) = i • gen (StrothTypeIndex.t131 (s + 2) hm).k 0 +
      j • gen (StrothTypeIndex.t131 (s + 2) hm).k 1 +
      l • gen (StrothTypeIndex.t131 (s + 2) hm).k 2) :
    conjTorusIdx4 E hgC (E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C))) =
      i • (𝔤 s 0) + (2 * j) • (𝔤 s 1) + (2 * l) • (𝔤 s 2) := by
  rw [conjTorusIdx4_apply_symm]
  have hc : conjBy hgC (⟨β, hBC β.2⟩ : C) = ⟨conjBy hgB β, hBC (conjBy hgB β).2⟩ :=
    Subtype.ext rfl
  rw [hc]
  exact E_symm_incl_t131 D hBC hL E hE0 hE1 hE2 he _ h

include hE0 hE1 hE2 he in
theorem E_symm_c_t131 : E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (𝔤 s 0) := by
  rw [E_symm_incl_t131 D hBC hL E hE0 hE1 hE2 he D.c (i := 1) (j := 0) (l := 0)
    (by rw [D.ec_c]; module)]
  module

include hE0 hE1 hE2 he in
theorem E_symm_a_t131 : E.symm (Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C)) = (2 : ℤ) • (𝔤 s 1) := by
  rw [E_symm_incl_t131 D hBC hL E hE0 hE1 hE2 he D.a (i := 0) (j := 1) (l := 0)
    (by rw [D.ec_a]; module)]
  module

include hE0 hE1 hE2 he in
theorem E_symm_b_t131 : E.symm (Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) = (2 : ℤ) • (𝔤 s 2) := by
  rw [E_symm_incl_t131 D hBC hL E hE0 hE1 hE2 he D.b (i := 0) (j := 0) (l := 1)
    (by rw [D.ec_b]; module)]
  module

include hE0 hE1 hE2 he in
theorem transport_t131 :
    conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 0) = (Type230.action (Type230.data s)).φρ (𝔤 s 0) ∧
    conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 1) = (Type230.action (Type230.data s)).φρ (𝔤 s 1) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 2) =
      (2 : ℤ) • (Type230.action (Type230.data s)).φρ (𝔤 s 2) ∧
    conjTorusIdx4 E (hL D.u_mem_L) (𝔤 s 0) = (Type230.action (Type230.data s)).φu (𝔤 s 0) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.u_mem_L) (𝔤 s 1) =
      (2 : ℤ) • (Type230.action (Type230.data s)).φu (𝔤 s 1) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.u_mem_L) (𝔤 s 2) =
      (2 : ℤ) • (Type230.action (Type230.data s)).φu (𝔤 s 2) ∧
    conjTorusIdx4 E (hL D.uv_mem_L) (𝔤 s 0) = (Type230.action (Type230.data s)).φuv (𝔤 s 0) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.uv_mem_L) (𝔤 s 1) =
      (2 : ℤ) • (Type230.action (Type230.data s)).φuv (𝔤 s 1) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.uv_mem_L) (𝔤 s 2) =
      (2 : ℤ) • (Type230.action (Type230.data s)).φuv (𝔤 s 2) := by
  have hc := E_symm_c_t131 D hBC hL E hE0 hE1 hE2 he
  have ha := E_symm_a_t131 D hBC hL E hE0 hE1 hE2 he
  have hb := E_symm_b_t131 D hBC hL E hE0 hE1 hE2 he
  have h1 : E.symm (Additive.ofMul e) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E).mpr hE1.symm
  have h2 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) e)) = (𝔤 s 2) :=
    (AddEquiv.symm_apply_eq E).mpr hE2.symm
  have hB131 := Type131.data (s + 2) (by omega)
  have hGG := GV_succ_t131 s
  have hG := three_mul_GV_t131 s
  have ec {g : S} {hgB : g ∈ Subgroup.normalizer B}
      {φ : Torus (StrothTypeIndex.t131 (s + 2) hm).k →+ Torus (StrothTypeIndex.t131 (s + 2) hm).k}
      (hφ : ∀ x : B, D.e (Additive.ofMul (conjBy hgB x)) = φ (D.e (Additive.ofMul x)))
      {x : B} {v w : Torus (StrothTypeIndex.t131 (s + 2) hm).k}
      (hx : D.ec x = v) (hw : φ v = w) : D.ec (conjBy hgB x) = w := by
    rw [← hw, ← hx]
    exact hφ x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.ρ_mem_L) D.ρ_mem D.c
      (ec D.ρ_conj D.ec_c (phiR_gen0_t131 hB131))
    rw [hc] at h
    rw [h, phiR_gen0_t230_t131 (Type230.data s) hGG hG]
  · rw [← h1, conjTorusIdx4_apply_symm, h2, h1, phiR_gen1_t230 (Type230.data s)]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.ρ_mem_L) D.ρ_mem D.b
      (ec D.ρ_conj D.ec_b (phiR_gen2_t131 hB131))
    rw [hb] at h
    rw [← map_zsmul, h, phiR_gen2_t230_t131 (Type230.data s) hGG hG]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.u_mem_L) D.u_mem D.c
      (ec D.u_conj D.ec_c (phiU_gen0_t131 hB131))
    rw [hc] at h
    rw [h, phiU_gen0_t230_t131 (Type230.data s) hGG hG]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.u_mem_L) D.u_mem D.a
      (ec D.u_conj D.ec_a (phiU_gen1_t131 hB131))
    rw [ha] at h
    rw [← map_zsmul, h, phiU_gen1_t230_t131 (Type230.data s) hGG hG]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.u_mem_L) D.u_mem D.b
      (ec D.u_conj D.ec_b (phiU_gen2_t131 hB131))
    rw [hb] at h
    rw [← map_zsmul, h, phiU_gen2_t230_t131 (Type230.data s) hGG hG]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.uv_mem_L) D.uv_mem D.c
      (ec D.uv_conj D.ec_c (phiUV_gen0_t131 hB131))
    rw [hc] at h
    rw [h, phiUV_gen0_t230_t131 (Type230.data s) hGG hG]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.uv_mem_L) D.uv_mem D.a
      (ec D.uv_conj D.ec_a (phiUV_gen1_t131 hB131))
    rw [ha] at h
    rw [← map_zsmul, h, phiUV_gen1_t230_t131 (Type230.data s) hGG hG]
  · have h := alpha_incl_t131 D hBC hL E hE0 hE1 hE2 he (hL D.uv_mem_L) D.uv_mem D.b
      (ec D.uv_conj D.ec_b (phiUV_gen2_t131 hB131))
    rw [hb] at h
    rw [← map_zsmul, h, phiUV_gen2_t230_t131 (Type230.data s) hGG hG]

end Transport

end CFSG.CGT.Stroth77
