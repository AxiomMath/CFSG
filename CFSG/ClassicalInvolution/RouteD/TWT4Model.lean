module

public import CFSG.ClassicalInvolution.RouteD.TWZSu4V
public import CFSG.ClassicalInvolution.RouteD.TWT4Fix

public section

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_inv_four twin_std_u)
open CFSG.ClassicalInvolution.RouteD.SCRSu4 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD.TwinY

namespace CFSG.ClassicalInvolution.RouteD.TWT4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem trace_eq_zero_of_sq (A : Su K p f 2) (hA : suMat A * suMat A = -1) :
    (suMat A).trace = 0 := by
  have hdet := det_suMat A
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hA 0) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have h : (suMat A 0 0 + suMat A 1 1) ^ 2 = 0 := by
    linear_combination e00 + e11 + 2 * hdet
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h
  simpa [Matrix.trace, Fin.sum_univ_two, Matrix.diag] using this


theorem su4_twin_sq_trace (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {a a' : Su K p f 4} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    suMat (a * a') * suMat (a * a') = -1 ∧ (suMat (a * a')).trace = 0 := by
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
  have hφ := suMat_phiU_sq hAA hAA'
  have tA := trace_eq_zero_of_sq A hAA
  have tA' := trace_eq_zero_of_sq A' hAA'
  constructor
  · have e3 : (a * a') * (a * a') = g * (phiU K p f (A, A') * phiU K p f (A, A')) * g⁻¹ := by
      rw [e2]
      group
    rw [← suMat_mul, e3]
    simp only [suMat_mul, hφ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      suMat_mul_suMat_inv]
  · have e3 : suMat (a * a') = suMat g * suMat (phiU K p f (A, A')) * suMat g⁻¹ := by
      rw [e2]
      simp only [suMat_mul]
    have e4 : (suMat g * suMat (phiU K p f (A, A')) * suMat g⁻¹).trace =
        (suMat (phiU K p f (A, A'))).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, suMat_inv_mul_suMat,
        Matrix.mul_one]
    rw [e3, e4]
    rw [phiU_apply, suMat_mul, suMat_blockEmb_zero, suMat_blockEmb_two]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four, Matrix.mul_apply] at tA tA' ⊢
    linear_combination tA + tA'


section Model

variable {p : ℕ} [Fact p.Prime]


theorem twinMF_two_psu4 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) (hmod : (p ^ e) % 4 = 3)
    {R R' : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    {x x' : (modelUniv .PSU 4 p e Fact.out).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 p e Fact.out) R R' x x')
    {a a' : (modelUniv .PSU 4 p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K) :
    ∃ S₁ S₂ : Subgroup (modelUniv .PSU 4 p e Fact.out).K,
      S₁ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D ∧
      S₂ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D ∧ S₁ ≠ S₂ ∧
      (∀ s ∈ S₁, ∀ t ∈ S₂, s * t = t * s) ∧ (∀ s ∈ S₁, (a * a') * s = s * (a * a')) ∧
      (∀ s ∈ S₂, (a * a') * s = s * (a * a')) ∧
      ∀ S ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D,
        (∀ s ∈ S, (a * a') * s = s * (a * a')) → S = S₁ ∨ S = S₂ := by
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
  have hdat := su4_twin_sq_trace hK hp2
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
  obtain ⟨ι, hι2, hσι⟩ := exists_iota hK hmod
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, hcomm, hc₁, hc₂, huniq⟩ :=
    fund_centralizing_su4 hK hp2 hq hdat.1 hdat.2 hι2 hσι
  have hmapφ : ∀ L : Subgroup (Su (GaloisField p (2 * e)) p e 4),
      (L.map φ.symm.toMonoidHom).map φ.toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    ext y
    simp
  have hS₁ : L₁.map φ.symm.toMonoidHom ∈ fundamentalSubgroups .PSU
      (modelUniv .PSU 4 p e Fact.out).D := (hφ _).mpr (by rw [hmapφ]; exact hL₁)
  have hS₂ : L₂.map φ.symm.toMonoidHom ∈ fundamentalSubgroups .PSU
      (modelUniv .PSU 4 p e Fact.out).D := (hφ _).mpr (by rw [hmapφ]; exact hL₂)
  refine ⟨L₁.map φ.symm.toMonoidHom, L₂.map φ.symm.toMonoidHom, hS₁, hS₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hmapφ L₁, ← hmapφ L₂, h]
  · rintro s ⟨l₁, hl₁, rfl⟩ t ⟨l₂, hl₂, rfl⟩
    show φ.symm l₁ * φ.symm l₂ = φ.symm l₂ * φ.symm l₁
    rw [← map_mul, ← map_mul, hcomm l₁ hl₁ l₂ hl₂]
  · rintro s ⟨l₁, hl₁, rfl⟩
    show (a * a') * φ.symm l₁ = φ.symm l₁ * (a * a')
    apply φ.injective
    rw [map_mul, map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hc₁ l₁ hl₁).symm
  · rintro s ⟨l₂, hl₂, rfl⟩
    show (a * a') * φ.symm l₂ = φ.symm l₂ * (a * a')
    apply φ.injective
    rw [map_mul, map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hc₂ l₂ hl₂).symm
  · intro S hS hcS
    have hSφ := (hφ S).mp hS
    have hc' : ∀ y ∈ S.map φ.toMonoidHom, y * (φ a * φ a') = (φ a * φ a') * y := by
      rintro _ ⟨s, hs, rfl⟩
      show φ s * (φ a * φ a') = (φ a * φ a') * φ s
      rw [← map_mul, ← map_mul, ← map_mul, hcS s hs]
    rcases huniq _ hSφ hc' with h | h
    · left
      refine Subgroup.map_injective (f := φ.toMonoidHom) φ.injective ?_
      rw [h, hmapφ]
    · right
      refine Subgroup.map_injective (f := φ.toMonoidHom) φ.injective ?_
      rw [h, hmapφ]

end Model

end CFSG.ClassicalInvolution.RouteD.TWT4
