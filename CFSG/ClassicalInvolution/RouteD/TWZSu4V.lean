module

public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSu4

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSu4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (aSU suMat_aSU suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_inv_four twin_std_u)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_norm_one_ne (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    ∃ c : K, unitaryInvolution K p f c * c = 1 ∧ c * c ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Fintype.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hq1 : 1 ≤ p ^ f := by omega
  have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
  have e1 : (p ^ f - 1) * p ^ f + (p ^ f - 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, h1]
    ring
  have e2 : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    zify [hq1, h1]
    ring
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_mul,
      ← pow_add, e1, ← hord, pow_orderOf_eq_one, Units.val_one]
  · intro h
    rw [← Units.val_mul, ← pow_add, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one, hord] at h
    have h2 : 0 < (p ^ f - 1) + (p ^ f - 1) := by omega
    have h3 := Nat.le_of_dvd h2 h
    rw [e2] at h3
    have h4 : (p ^ f - 1) * (p ^ f + 1) ≥ (p ^ f - 1) * 6 := Nat.mul_le_mul_left _ (by omega)
    omega

theorem su4_no_commute (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hmod : (p ^ f) % 4 = 1) (w : Su K p f 4) (hw2 : suMat w * suMat w = -1)
    (hc : ∀ B : Su K p f 2, blockEmb K p f 4 2 0 (by norm_num) B * w =
      w * blockEmb K p f 4 2 0 (by norm_num) B) : False := by
  have hσσ := (isUnitaryInvolution_unitaryInvolution hK).invol
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨c, hcσ, hc2⟩ := exists_norm_one_ne hK hq
  have hab : unitaryInvolution K p f c * c + unitaryInvolution K p f 0 * 0 = 1 := by
    rw [map_zero, mul_zero, add_zero]
    exact hcσ
  have hBm : suMat (aSU K p f hab hσσ) =
      !![c, 0; -unitaryInvolution K p f 0, unitaryInvolution K p f c] := suMat_aSU hab hσσ
  have hσc : unitaryInvolution K p f c ≠ c := fun h => hc2 (by
    have := hcσ
    rw [h] at this
    exact this)
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, mul_one])
  have h := congrArg suMat (hc (aSU K p f hab hσσ))
  rw [suMat_mul, suMat_mul, suMat_blockEmb_zero, hBm] at h
  set s := unitaryInvolution K p f c with hs
  have e1 := congrFun (congrFun h 1) 0
  have e2 := congrFun (congrFun h 2) 0
  have e3 := congrFun (congrFun h 3) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e1 e2 e3
  have w10 : suMat w 1 0 = 0 := by
    have : suMat w 1 0 * (unitaryInvolution K p f c - c) = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hσc)
  have w20 : suMat w 2 0 = 0 := by
    have : suMat w 2 0 * (1 - c) = 0 := by linear_combination e2
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hc1.symm)
  have w30 : suMat w 3 0 = 0 := by
    have : suMat w 3 0 * (1 - c) = 0 := by linear_combination e3
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hc1.symm)
  set l := suMat w 0 0 with hl
  have hl2 : l * l = -1 := by
    have := congrFun (congrFun hw2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, w10, w20, w30] at this
    exact this
  have hu : conjTr (unitaryInvolution K p f) (suMat w) * suMat w = 1 := w.2.2
  have hl1 : unitaryInvolution K p f l * l = 1 := by
    have := congrFun (congrFun hu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, conjTr, w10, w20, w30] at this
    exact this
  have hl4 : l ^ 4 = 1 := by
    have : l ^ 4 = (l * l) * (l * l) := by ring
    rw [this, hl2]
    norm_num
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 4 * m + 1 := ⟨(p ^ f) / 4, by omega⟩
  have hσl : unitaryInvolution K p f l = l := by
    rw [unitaryInvolution_apply, hm, pow_succ, pow_mul, hl4, one_pow, one_mul]
  rw [hσl, hl2] at hl1
  apply h2
  linear_combination -hl1

theorem suMat_phiU_sq {A A' : Su K p f 2} (hA : suMat A * suMat A = -1)
    (hA' : suMat A' * suMat A' = -1) :
    suMat (phiU K p f (A, A')) * suMat (phiU K p f (A, A')) = -1 := by
  have e := fun i j => congrFun (congrFun hA i) j
  have e' := fun i j => congrFun (congrFun hA' i) j
  have a00 := e 0 0
  have a01 := e 0 1
  have a10 := e 1 0
  have a11 := e 1 1
  have b00 := e' 0 0
  have b01 := e' 0 1
  have b10 := e' 1 0
  have b11 := e' 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a00 a01 a10 a11 b00 b01 b10 b11
  rw [phiU_apply, suMat_mul, suMat_blockEmb_zero, suMat_blockEmb_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
      | linear_combination a00 | linear_combination a01 | linear_combination a10
      | linear_combination a11 | linear_combination b00 | linear_combination b01
      | linear_combination b10 | linear_combination b11

theorem su4_not_centralizes (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hmod : (p ^ f) % 4 = 1) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {a a' : Su K p f 4} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {S : Subgroup (Su K p f 4)}
    (hS : S ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hc : ∀ s ∈ S, (a * a') * s = s * (a * a')) : False := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hx2 : x * x = 1 := sl2_mul_self_eq_one_of_center (hi.isClassicalSL2 hK hp) hxR hxc
  have hx'2 : x' * x' = 1 := sl2_mul_self_eq_one_of_center (hi'.isClassicalSL2 hK hp) hx'R' hx'c
  have hc0 : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := (Subgroup.center (Su K p f 4)).inv_mem hsame
    simpa using this
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp ⟨i, hi⟩ ⟨i', hi'⟩ hne hxR hx2 hx1 hx'R' hx'2
    hx'1 hc0
  have hxg' : x = g * xU K p f * g⁻¹ := hxg
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := (Subgroup.center (Su K p f 4)).mul_mem hsq' hc0
    simpa [mul_assoc] using this
  have hA₁ : blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 0 (by norm_num) A *
      (xU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 0 (by norm_num) A *
        (xU K p f)⁻¹) * g⁻¹ = a * a * x⁻¹ := by
      rw [← hae, hA, hxg']
      group
    rw [e]
    exact hsq
  have hA₂ : blockEmb K p f 4 2 2 (by norm_num) A' * blockEmb K p f 4 2 2 (by norm_num) A' *
      (xU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (blockEmb K p f 4 2 2 (by norm_num) A' * blockEmb K p f 4 2 2 (by norm_num) A' *
        (xU K p f)⁻¹) * g⁻¹ = a' * a' * x⁻¹ := by
      rw [← hae', hA', hxg']
      group
    rw [e]
    exact hsq''
  have hAA := sq_neg_one_of_center_zero hK hA₁
  have hAA' := sq_neg_one_of_center_two hK hA₂
  have e2 : a * a' = g * phiU K p f (A, A') * g⁻¹ := by
    rw [phiU_apply, ← hae, ← hae', hA, hA']
    group
  obtain ⟨g', hg'⟩ := (mem_longRootSetU_iff (show 2 ≤ 4 by norm_num)).mp hS
  refine su4_no_commute hK hp hq hmod (g'⁻¹ * (a * a') * g') ?_ fun B => ?_
  · have e3 : g'⁻¹ * (a * a') * g' * (g'⁻¹ * (a * a') * g') =
        g'⁻¹ * g * (phiU K p f (A, A') * phiU K p f (A, A')) * (g'⁻¹ * g)⁻¹ := by
      rw [e2]
      group
    rw [← suMat_mul, e3,
      suMat_mul (g'⁻¹ * g * (phiU K p f (A, A') * phiU K p f (A, A'))) (g'⁻¹ * g)⁻¹,
      suMat_mul (g'⁻¹ * g) (phiU K p f (A, A') * phiU K p f (A, A')),
      suMat_mul (phiU K p f (A, A')) (phiU K p f (A, A')), suMat_phiU_sq hAA hAA',
      Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, suMat_mul_suMat_inv]
  · have hmem : g' * blockEmb K p f 4 2 0 (by norm_num) B * g'⁻¹ ∈ S := by
      rw [hg']
      exact ⟨blockEmb K p f 4 2 0 (by norm_num) B, ⟨B, rfl⟩, by simp [MulAut.conj_apply]⟩
    have h := hc _ hmem
    calc blockEmb K p f 4 2 0 (by norm_num) B * (g'⁻¹ * (a * a') * g')
        = g'⁻¹ * (g' * blockEmb K p f 4 2 0 (by norm_num) B * g'⁻¹ * (a * a')) * g' := by
          group
      _ = g'⁻¹ * ((a * a') * (g' * blockEmb K p f 4 2 0 (by norm_num) B * g'⁻¹)) * g' := by
          rw [h]
      _ = g'⁻¹ * (a * a') * g' * blockEmb K p f 4 2 0 (by norm_num) B := by group

end CFSG.ClassicalInvolution.RouteD.SCRSu4

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD.TwinY

variable {p : ℕ} [Fact p.Prime]

theorem twinMFNotCentralizing_psu4 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hmod : (p ^ e) % 4 = 1)
    {R R' : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    {x x' : (modelUniv .PSU 4 p e Fact.out).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 p e Fact.out) R R' x x')
    {a a' : (modelUniv .PSU 4 p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    {S : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    (hS : S ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D)
    (hc : ∀ s ∈ S, (a * a') * s = s * (a * a')) : False := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSU 4 p e :=
    ⟨Fact.out, he, by norm_num, fun h => by
      have : (4 : ℕ) = 3 := congrArg Prod.fst h
      omega⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  refine CFSG.ClassicalInvolution.RouteD.SCRSu4.su4_not_centralizes hK hp2 hq hmod
    ((hφ R).mp hd.mem) ((hφ R').mp hd.mem')
    (fun h => hd.ne (Subgroup.map_injective φ.injective h))
    (x := φ x) (x' := φ x') ⟨x, hd.hx, rfl⟩
    (by
      rintro _ ⟨r, hr, rfl⟩
      show φ x * φ r = φ r * φ x
      rw [← map_mul, ← map_mul, hd.cx r hr])
    (fun h => hd.nx (φ.injective (h.trans (map_one φ).symm))) ⟨x', hd.hx', rfl⟩
    (by
      rintro _ ⟨r, hr, rfl⟩
      show φ x' * φ r = φ r * φ x'
      rw [← map_mul, ← map_mul, hd.cx' r hr])
    (fun h => hd.nx' (φ.injective (h.trans (map_one φ).symm)))
    (by
      rw [← map_inv, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hd.same)
    (a := φ a) (a' := φ a') ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq)
    (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq')
    (S := S.map φ.toMonoidHom) ((hφ S).mp hS) ?_
  rintro _ ⟨s, hs, rfl⟩
  show φ a * φ a' * φ s = φ s * (φ a * φ a')
  rw [← map_mul, ← map_mul, ← map_mul, hc s hs]

end CFSG.ClassicalInvolution.RouteD.TWZ
