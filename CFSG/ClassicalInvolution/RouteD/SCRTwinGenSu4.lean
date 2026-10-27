module

public import CFSG.ClassicalInvolution.RouteD.SCRSu4CaseA
public import CFSG.ClassicalInvolution.RouteD.SCRSu4CaseB

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSu4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (suMat_blockEmb_zero suMat_blockEmb_two
  suMat_rootInvSU_inv_four twin_std_u)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem sl2_mul_self_eq_one_of_center {F : Type*} [Field F] {G : Type*} [Group G]
    {J : Subgroup G} {d : G} (h : CFSG.ClassicalInvolution.IsClassicalSL2 F J d) {c : G}
    (hc : c ∈ J) (hcc : ∀ r ∈ J, c * r = r * c) : c * c = 1 := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  have hz : (⟨c, hc⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro r
    exact Subtype.ext (hcc r r.2).symm
  have h1 := (CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp hz
  have h2 : e ((⟨c, hc⟩ : J) * ⟨c, hc⟩) = 1 := by
    rw [map_mul]
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp h1 with h3 | h3
    · rw [h3, mul_one]
    · rw [h3]
      exact Subtype.ext (by simp)
  have h4 : (⟨c, hc⟩ : J) * ⟨c, hc⟩ = 1 := e.injective (h2.trans (map_one e).symm)
  exact congrArg Subtype.val h4

theorem mem_center_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {g : G}
    (hg : g ∈ Subgroup.center G) : φ g ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hg ⊢
  intro h
  obtain ⟨k, rfl⟩ := φ.surjective h
  rw [← map_mul, ← map_mul, hg k]

theorem exists_sqrt_neg_one (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) :
    ∃ ι : K, ι * ι = -1 ∧
      (unitaryInvolution K p f ι = ι ∨ unitaryInvolution K p f ι = -ι) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω * ω = -1 := by
    have hsq : IsSquare (-1 : K) := by
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
      have hodd : Odd (p ^ f) := (Fact.out (p := p.Prime)).odd_of_ne_two hp |>.pow
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      ring_nf
      omega
    obtain ⟨ω, hω⟩ := hsq
    exact ⟨ω, hω.symm⟩
  have hσω2 : unitaryInvolution K p f ω * unitaryInvolution K p f ω = -1 := by
    rw [← map_mul, hω, map_neg, map_one]
  refine ⟨ω, hω, ?_⟩
  have : (unitaryInvolution K p f ω - ω) * (unitaryInvolution K p f ω + ω) = 0 := by
    linear_combination hσω2 - hω
  rcases mul_eq_zero.mp this with h | h
  · left
    linear_combination h
  · right
    linear_combination h

theorem su4_core (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (A A' : Su K p f 2) (hA : suMat A * suMat A = -1) (hA' : suMat A' * suMat A' = -1) :
    Subgroup.centralizer ({xU K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({phiU K p f (A, A')} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({xU K p f * phiU K p f (A, A')} : Set (Su K p f 4)) = ⊤ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨ι, hι, hcase⟩ := exists_sqrt_neg_one hK hp
  rcases hcase with h | h
  · exact su4_caseB hK h2 hι h A A' hA hA'
  · exact su4_caseA hK (by omega) h2 hι h A A' hA hA'

theorem sq_neg_one_of_center_zero (hK : Nat.card K = (p ^ f) ^ 2) {A : Su K p f 2}
    (h : blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 0 (by norm_num) A *
      (xU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4)) : suMat A * suMat A = -1 := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) h
  have e : suMat (blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 0 (by norm_num) A *
      (xU K p f)⁻¹) = Matrix.scalar (Fin 4) (u : K) := hu
  generalize (u : K) = c0 at e
  rw [suMat_mul, suMat_mul, suMat_blockEmb_zero, xU, suMat_rootInvSU_inv_four] at e
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  have e22 := congrFun (congrFun e 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.scalar_apply] at e00 e01 e10 e11 e22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first
    | linear_combination e22 - e00 | linear_combination e00 - e22
    | linear_combination e22 + e00 | linear_combination -e22 - e00
    | linear_combination e22 - e11 | linear_combination e11 - e22
    | linear_combination e22 + e11 | linear_combination -e22 - e11
    | linear_combination e01 | linear_combination -e01
    | linear_combination e10 | linear_combination -e10

theorem sq_neg_one_of_center_two (hK : Nat.card K = (p ^ f) ^ 2) {A : Su K p f 2}
    (h : blockEmb K p f 4 2 2 (by norm_num) A * blockEmb K p f 4 2 2 (by norm_num) A *
      (xU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4)) : suMat A * suMat A = -1 := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) h
  have e : suMat (blockEmb K p f 4 2 2 (by norm_num) A * blockEmb K p f 4 2 2 (by norm_num) A *
      (xU K p f)⁻¹) = Matrix.scalar (Fin 4) (u : K) := hu
  generalize (u : K) = c0 at e
  rw [suMat_mul, suMat_mul, suMat_blockEmb_two, xU, suMat_rootInvSU_inv_four] at e
  have e00 := congrFun (congrFun e 0) 0
  have e22 := congrFun (congrFun e 2) 2
  have e23 := congrFun (congrFun e 2) 3
  have e32 := congrFun (congrFun e 3) 2
  have e33 := congrFun (congrFun e 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.scalar_apply] at e00 e22 e23 e32 e33
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first
    | linear_combination e22 - e00 | linear_combination e00 - e22
    | linear_combination e22 + e00 | linear_combination -e22 - e00
    | linear_combination e33 - e00 | linear_combination e00 - e33
    | linear_combination e33 + e00 | linear_combination -e33 - e00
    | linear_combination e23 | linear_combination -e23
    | linear_combination e32

theorem su4_gen (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {a a' : Su K p f 4} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    Subgroup.centralizer ({x} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({a * a'} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (Su K p f 4)) = ⊤ := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hx2 : x * x = 1 := sl2_mul_self_eq_one_of_center (hi.isClassicalSL2 hK hp) hxR hxc
  have hx'2 : x' * x' = 1 := sl2_mul_self_eq_one_of_center (hi'.isClassicalSL2 hK hp) hx'R' hx'c
  have hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := (Subgroup.center (Su K p f 4)).inv_mem hsame
    simpa using this
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp ⟨i, hi⟩ ⟨i', hi'⟩ hne hxR hx2 hx1 hx'R' hx'2
    hx'1 hc
  have hxg' : x = g * xU K p f * g⁻¹ := hxg
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := (Subgroup.center (Su K p f 4)).mul_mem hsq' hc
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
  have key := su4_core hK hp hq A A' (sq_neg_one_of_center_zero hK hA₁)
    (sq_neg_one_of_center_two hK hA₂)
  have hk := CFSG.ClassicalInvolution.RouteD.SCRSL4.sup_centralizer_conj g _ _ _ key
  have e2 : a * a' = g * phiU K p f (A, A') * g⁻¹ := by
    rw [phiU_apply, ← hae, ← hae', hA, hA']
    group
  have e3 : x * (a * a') = g * (xU K p f * phiU K p f (A, A')) * g⁻¹ := by
    rw [e2, hxg']
    group
  rw [e3, e2, hxg']
  exact hk

end CFSG.ClassicalInvolution.RouteD.SCRSu4

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal

variable {p : ℕ} [Fact p.Prime]

theorem twinMFGenerationOn_psu4 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    TwinMFGenerationOn .PSU (modelUniv .PSU 4 p e Fact.out) := by
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
  intro R R' x x' hd a ha a' ha' hsq hsq' S hS
  have key := CFSG.ClassicalInvolution.RouteD.SCRSu4.su4_gen hK hp2 hq ((hφ R).mp hd.mem)
    ((hφ R').mp hd.mem') (fun h => hd.ne (Subgroup.map_injective φ.injective h))
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
  have hall := CFSG.ClassicalInvolution.RouteD.SCRSu4.sup_centralizer_of_equiv φ x (a * a')
    (x * (a * a')) (by simpa only [map_mul] using key)
  exact le_top.trans hall.symm.le

theorem twinMFGeneration_psu4 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    TwinMFGeneration p e .PSU 4 :=
  twinMFGeneration_of_on (twinMFGenerationOn_psu4 hp2 hq)

end CFSG.ClassicalInvolution.RouteD.TwinY
