module

public import CFSG.CGT.Stroth77.Extension24Square
public import CFSG.CGT.Stroth77.Extension24Transport
public import CFSG.CGT.Stroth77.Extension24Torus

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type100.k (s + 1)) j

local notation "𝔨" s:max j:max =>
  CFSG.CGT.Stroth77.gen
    (CFSG.CGT.Stroth77.StrothTypeIndex.k (CFSG.CGT.Stroth77.StrothTypeIndex.t300 (s + 1))) j

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {s : ℕ}

section Printed

variable (D : StrothTypeData B (StrothTypeIndex.t300 (s + 1)))

theorem ec_conj_uv_c300 : D.ec (conjBy D.uv_mem D.c) =
    (-3 : ℤ) • (𝔨 s 0) + (-1 : ℤ) • (𝔨 s 1) + (-1 : ℤ) • (𝔨 s 2) := by
  have h := D.uv_conj D.c
  rw [show D.e (Additive.ofMul D.c) = Torus.c from D.ec_c] at h
  exact h.trans (Type300.uv_c _)

theorem ec_conj_uv_a300 : D.ec (conjBy D.uv_mem D.a) =
    (4 : ℤ) • (𝔨 s 0) + (1 : ℤ) • (𝔨 s 1) + (2 : ℤ) • (𝔨 s 2) := by
  have h := D.uv_conj D.a
  rw [show D.e (Additive.ofMul D.a) = Torus.a from D.ec_a] at h
  exact h.trans (Type300.uv_a _)

theorem ec_conj_uv_b300 : D.ec (conjBy D.uv_mem D.b) =
    (4 : ℤ) • (𝔨 s 0) + (2 : ℤ) • (𝔨 s 1) + (1 : ℤ) • (𝔨 s 2) := by
  have h := D.uv_conj D.b
  rw [show D.e (Additive.ofMul D.b) = Torus.b from D.ec_b] at h
  exact h.trans (Type300.uv_b _)

theorem ec_conj_u_c300 : D.ec (conjBy D.u_mem D.c) = (1 : ℤ) • (𝔨 s 0) := by
  have h := D.u_conj D.c
  rw [show D.e (Additive.ofMul D.c) = Torus.c from D.ec_c] at h
  exact h.trans (Type300.u_c _)

theorem ec_conj_u_a300 : D.ec (conjBy D.u_mem D.a) = (1 : ℤ) • (𝔨 s 2) := by
  have h := D.u_conj D.a
  rw [show D.e (Additive.ofMul D.a) = Torus.a from D.ec_a] at h
  exact h.trans (Type300.u_a _)

theorem ec_conj_u_b300 : D.ec (conjBy D.u_mem D.b) = (1 : ℤ) • (𝔨 s 1) := by
  have h := D.u_conj D.b
  rw [show D.e (Additive.ofMul D.b) = Torus.b from D.ec_b] at h
  exact h.trans (Type300.u_b _)

theorem ec_conj_ρ_c300 : D.ec (conjBy D.ρ_mem D.c) = (1 : ℤ) • (𝔨 s 0) := by
  have h := D.ρ_conj D.c
  rw [show D.e (Additive.ofMul D.c) = Torus.c from D.ec_c] at h
  exact h.trans (Type300.rho_c _)

theorem ec_conj_ρ_a300 : D.ec (conjBy D.ρ_mem D.a) = (1 : ℤ) • (𝔨 s 2) := by
  have h := D.ρ_conj D.a
  rw [show D.e (Additive.ofMul D.a) = Torus.a from D.ec_a] at h
  exact h.trans (Type300.rho_a _)

theorem ec_conj_ρ_b300 : D.ec (conjBy D.ρ_mem D.b) =
    (-4 : ℤ) • (𝔨 s 0) + (-1 : ℤ) • (𝔨 s 1) + (-1 : ℤ) • (𝔨 s 2) := by
  have h := D.ρ_conj D.b
  rw [show D.e (Additive.ofMul D.b) = Torus.b from D.ec_b] at h
  exact h.trans (Type300.rho_b _)

theorem conjBy_ρ_a300 : conjBy D.ρ_mem D.a = D.b := by
  apply D.ec_injective
  rw [ec_conj_ρ_a300, D.ec_b, one_smul]

end Printed

theorem conj_ρ_sq300 (D : StrothTypeData B (StrothTypeIndex.t300 (s + 1))) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e : C} (he : e * e = ⟨D.a, hBC D.a.2⟩) :
    conjBy (hL D.ρ_mem_L) e * conjBy (hL D.ρ_mem_L) e = ⟨D.b, hBC D.b.2⟩ := by
  rw [← conjBy_mul, he]
  apply Subtype.ext
  have h := congrArg Subtype.val (conjBy_ρ_a300 D)
  simpa [conjBy_val] using h

section Basis

variable [hN : (B.subgroupOf C).Normal]

theorem closure_c_e_conj300_of_data (D : StrothTypeData B (StrothTypeIndex.t300 (s + 1)))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) :
    Subgroup.closure (Set.range ![(⟨D.c, hBC D.c.2⟩ : C), e,
      conjBy (hL D.ρ_mem_L) e]) = ⊤ := by
  classical
  let f : C := conjBy (hL D.ρ_mem_L) e
  have hf : f * f = ⟨D.b, hBC D.b.2⟩ := conj_ρ_sq300 D hBC hL he
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_t300_of_data D hBC hC hrel hL hncyc
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  let P : C → Fin 3 → ZMod 2 := sqParity300 D (by omega) hsq
  have hPe : P e = Pi.single 1 1 := sqParity300_of_sq_eq_a hBC he
  have hPf : P f = Pi.single 2 1 := sqParity300_of_sq_eq_b hBC hf
  have hPB : ∀ x : C, x ∈ B.subgroupOf C → P x = 0 := fun x hx =>
    sqParity300_of_mem x (Subgroup.mem_subgroupOf.mp hx)
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
    have h2 : P (e * f⁻¹ * f) = P (e * f⁻¹) + P f := sqParity300_mul hcomm _ _
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

theorem closure_c_e_conj300 (hB : HasStrothType B (StrothTypeIndex.t300 (s + 1)))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨hB.data.a, hBC hB.data.a.2⟩) :
    Subgroup.closure (Set.range ![(⟨hB.data.c, hBC hB.data.c.2⟩ : C), e,
      conjBy (hL hB.data.ρ_mem_L) e]) = ⊤ :=
  closure_c_e_conj300_of_data hB.data hBC hC hrel hL hncyc he

theorem exists_torusBasis300_of_data (D : StrothTypeData B (StrothTypeIndex.t300 (s + 1)))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) :
    ∃ E : Torus (Type100.k (s + 1)) ≃+ Additive C,
      E (𝔤 s 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩ ∧ E (𝔤 s 1) = Additive.ofMul e ∧
        E (𝔤 s 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) e) := by
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_t300_of_data D hBC hC hrel hL hncyc
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  let x : Fin 3 → C := ![⟨D.c, hBC D.c.2⟩, e, conjBy (hL D.ρ_mem_L) e]
  have hf := conj_ρ_sq300 D hBC hL he
  have hcpow : (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ (s + 1)) = 1 := by
    apply Subtype.ext
    have h : D.c ^ (2 ^ (s + 1)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_c, m_t300]
    simpa using congrArg Subtype.val h
  have hapow : (⟨D.a, hBC D.a.2⟩ : C) ^ (2 ^ (s + 1)) = 1 := by
    apply Subtype.ext
    have h : D.a ^ (2 ^ (s + 1)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_a, n_t300]
    simpa using congrArg Subtype.val h
  have hbpow : (⟨D.b, hBC D.b.2⟩ : C) ^ (2 ^ (s + 1)) = 1 := by
    apply Subtype.ext
    have h : D.b ^ (2 ^ (s + 1)) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_b, n_t300]
    simpa using congrArg Subtype.val h
  have hx : ∀ i, x i ^ (2 ^ Type100.k (s + 1) i) = 1 := by
    intro i
    fin_cases i
    · exact hcpow
    · change e ^ (2 ^ (s + 1 + 1)) = 1
      rw [pow_succ', pow_mul, sq, he, hapow]
    · change conjBy (hL D.ρ_mem_L) e ^ (2 ^ (s + 1 + 1)) = 1
      rw [pow_succ', pow_mul, sq, hf, hbpow]
  have hgen : Subgroup.closure (Set.range x) = ⊤ :=
    closure_c_e_conj300_of_data D hBC hC hrel hL hncyc he
  have hcard : Nat.card (Torus (Type100.k (s + 1))) = Nat.card C := by
    rw [card_torus_t100, hrel, D.card]
    change 2 ^ (3 * (s + 1) + 2) = 4 * 2 ^ ((s + 1) + (s + 1) + (s + 1))
    rw [show 3 * (s + 1) + 2 = 2 + ((s + 1) + (s + 1) + (s + 1)) by ring, pow_add]
    norm_num
  obtain ⟨E, hE⟩ := exists_torusEquiv_Idx4 hcomm x hx hgen hcard
  exact ⟨E, hE 0, hE 1, hE 2⟩

theorem exists_torusBasis300 (hB : HasStrothType B (StrothTypeIndex.t300 (s + 1)))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e : C}
    (he : e * e = ⟨hB.data.a, hBC hB.data.a.2⟩) :
    ∃ E : Torus (Type100.k (s + 1)) ≃+ Additive C,
      E (𝔤 s 0) = Additive.ofMul ⟨hB.data.c, hBC hB.data.c.2⟩ ∧ E (𝔤 s 1) = Additive.ofMul e ∧
        E (𝔤 s 2) = Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) e) :=
  exists_torusBasis300_of_data hB.data hBC hC hrel hL hncyc he

end Basis

section Transport

variable (D : StrothTypeData B (StrothTypeIndex.t300 (s + 1))) (hBC : B ≤ C)
  (hL : D.L ≤ Subgroup.normalizer C) {e : C}
  (E : Torus (Type100.k (s + 1)) ≃+ Additive C)
  (hE0 : E (𝔤 s 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩) (hE1 : E (𝔤 s 1) = Additive.ofMul e)
  (hE2 : E (𝔤 s 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) e))
  (he : e * e = ⟨D.a, hBC D.a.2⟩)

include hE0 hE1 hE2 he in
theorem E_symm_incl300 (β : B) {i j l : ℤ} (h : D.ec β = i • (𝔨 s 0) + j • (𝔨 s 1) + l • (𝔨 s 2)) :
    E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C)) = i • (𝔤 s 0) + (2 * j) • (𝔤 s 1) +
        (2 * l) • (𝔤 s 2) := by
  have hf := conj_ρ_sq300 D hBC hL he
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
theorem alpha_incl300 {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (β : B) {i j l : ℤ}
    (h : D.ec (conjBy hgB β) = i • (𝔨 s 0) + j • (𝔨 s 1) + l • (𝔨 s 2)) :
    conjTorusIdx4 E hgC (E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C))) =
      i • (𝔤 s 0) + (2 * j) • (𝔤 s 1) + (2 * l) • (𝔤 s 2) := by
  rw [conjTorusIdx4_apply_symm]
  have hc : conjBy hgC (⟨β, hBC β.2⟩ : C) = ⟨conjBy hgB β, hBC (conjBy hgB β).2⟩ :=
    Subtype.ext rfl
  rw [hc]
  exact E_symm_incl300 D hBC hL E hE0 hE1 hE2 he _ h

include hE0 hE1 hE2 he in
theorem E_symm_c300 : E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (𝔤 s 0) := by
  rw [E_symm_incl300 D hBC hL E hE0 hE1 hE2 he D.c (i := 1) (j := 0) (l := 0)
    (by rw [D.ec_c]; module)]
  module

include hE0 hE1 hE2 he in
theorem E_symm_a300 : E.symm (Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C)) = (2 : ℤ) • (𝔤 s 1) := by
  rw [E_symm_incl300 D hBC hL E hE0 hE1 hE2 he D.a (i := 0) (j := 1) (l := 0)
    (by rw [D.ec_a]; module)]
  module

include hE0 hE1 hE2 he in
theorem E_symm_b300 : E.symm (Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) = (2 : ℤ) • (𝔤 s 2) := by
  rw [E_symm_incl300 D hBC hL E hE0 hE1 hE2 he D.b (i := 0) (j := 0) (l := 1)
    (by rw [D.ec_b]; module)]
  module

include hE0 hE1 hE2 he in
theorem transport300 :
    conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 0) = (𝔤 s 0) ∧
    conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 1) = (𝔤 s 2) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.ρ_mem_L) (𝔤 s 2) =
      (-4 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2) ∧
    conjTorusIdx4 E (hL D.u_mem_L) (𝔤 s 0) = (𝔤 s 0) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.u_mem_L) (𝔤 s 1) = (2 : ℤ) • (𝔤 s 2) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.u_mem_L) (𝔤 s 2) = (2 : ℤ) • (𝔤 s 1) ∧
    conjTorusIdx4 E (hL D.uv_mem_L) (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) +
        (-2 : ℤ) • (𝔤 s 2) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.uv_mem_L) (𝔤 s 1) =
      (4 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) + (4 : ℤ) • (𝔤 s 2) ∧
    (2 : ℤ) • conjTorusIdx4 E (hL D.uv_mem_L) (𝔤 s 2) =
      (4 : ℤ) • (𝔤 s 0) + (4 : ℤ) • (𝔤 s 1) + (2 : ℤ) • (𝔤 s 2) := by
  have hc := E_symm_c300 D hBC hL E hE0 hE1 hE2 he
  have ha := E_symm_a300 D hBC hL E hE0 hE1 hE2 he
  have hb := E_symm_b300 D hBC hL E hE0 hE1 hE2 he
  have h1 : E.symm (Additive.ofMul e) = (𝔤 s 1) := (AddEquiv.symm_apply_eq E).mpr hE1.symm
  have h2 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) e)) = (𝔤 s 2) :=
    (AddEquiv.symm_apply_eq E).mpr hE2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.ρ_mem_L) D.ρ_mem D.c
      (i := 1) (j := 0) (l := 0)
      (by rw [ec_conj_ρ_c300]; module)
    rw [hc] at h
    rw [h]
    module
  · rw [← h1, conjTorusIdx4_apply_symm, h2]
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.ρ_mem_L) D.ρ_mem D.b
      (i := -4) (j := -1) (l := -1)
      (by rw [ec_conj_ρ_b300])
    rw [hb] at h
    rw [← map_zsmul, h]
    module
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.u_mem_L) D.u_mem D.c
      (i := 1) (j := 0) (l := 0)
      (by rw [ec_conj_u_c300]; module)
    rw [hc] at h
    rw [h]
    module
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.u_mem_L) D.u_mem D.a
      (i := 0) (j := 0) (l := 1)
      (by rw [ec_conj_u_a300]; module)
    rw [ha] at h
    rw [← map_zsmul, h]
    module
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.u_mem_L) D.u_mem D.b
      (i := 0) (j := 1) (l := 0)
      (by rw [ec_conj_u_b300]; module)
    rw [hb] at h
    rw [← map_zsmul, h]
    module
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.uv_mem_L) D.uv_mem D.c
      (i := -3) (j := -1) (l := -1)
      (by rw [ec_conj_uv_c300])
    rw [hc] at h
    rw [h]
    module
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.uv_mem_L) D.uv_mem D.a
      (i := 4) (j := 1) (l := 2)
      (by rw [ec_conj_uv_a300])
    rw [ha] at h
    rw [← map_zsmul, h]
    module
  · have h := alpha_incl300 D hBC hL E hE0 hE1 hE2 he (hL D.uv_mem_L) D.uv_mem D.b
      (i := 4) (j := 2) (l := 1)
      (by rw [ec_conj_uv_b300])
    rw [hb] at h
    rw [← map_zsmul, h]
    module

end Transport

end CFSG.CGT.Stroth77
