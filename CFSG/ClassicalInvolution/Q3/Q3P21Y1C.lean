module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y1S
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1M
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.RouteD.SU4Pattern
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Aux

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem eq_one_or_neg_one_of_sq_det {D : Matrix (Fin 2) (Fin 2) K} (h2 : (2 : K) ≠ 0)
    (hD : D * D = 1) (hdet : D.det = 1) : D = 1 ∨ D = -1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, D = !![a, b; c, d] :=
    ⟨D 0 0, D 0 1, D 1 0, D 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have e00 := congrFun (congrFun hD 0) 0
  have e01 := congrFun (congrFun hD 0) 1
  have e10 := congrFun (congrFun hD 1) 0
  have e11 := congrFun (congrFun hD 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [det_fin_two_of] at hdet
  have hs : a + d ≠ 0 := by
    intro hs
    have hd : d = -a := by linear_combination hs
    rw [hd] at hdet
    apply h2
    linear_combination (-1 : K) * e00 - hdet
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hs
  rw [hb, hc] at e00 e11 hdet
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at e00
    simp at e00
  have had : d = a := by
    have : a * (d - a) = 0 := by linear_combination hdet - e00
    have := (mul_eq_zero.mp this).resolve_left ha0
    linear_combination this
  rcases mul_self_eq_one_iff.mp (by linear_combination e00 : a * a = 1) with h | h
  · left
    rw [had, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc]
  · right
    rw [had, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc]

theorem units_pow_eight (hK9 : Nat.card K = 9) (u : Kˣ) : u ^ 8 = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
  rw [← Nat.card_eq_fintype_card, hK9] at h
  exact Units.ext (by simpa using h)

theorem invol_of_commuting (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hqq : p ^ f = 3)
    (hq3 : p ^ f % 4 = 3) {g : Su K p f 4}
    (hc : ∀ b l : Su K p f 2,
      blockEmb K p f 4 2 0 (by norm_num) b * (g * blockEmb K p f 4 2 0 (by norm_num) l * g⁻¹) =
        (g * blockEmb K p f 4 2 0 (by norm_num) l * g⁻¹) * blockEmb K p f 4 2 0 (by norm_num) b) :
    suMat (g * rootInvSU K p f (by norm_num : 2 ≤ 4) * g⁻¹) = BD 1 (-1) := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  have hK9 : Nat.card K = 9 := by rw [hK, hqq]; norm_num
  set θ : Su K p f 2 →* Su K p f 4 :=
    (MulAut.conj g).toMonoidHom.comp (blockEmb K p f 4 2 0 (by norm_num)) with hθ
  have shape : ∀ l : Su K p f 2, ∃ (c : K) (D : Matrix (Fin 2) (Fin 2) K),
      suMat (θ l) = BD (c • 1) D := by
    intro l
    refine commutant_blockZero hK hp2 hq3 fun b => ?_
    have e := congrArg suMat (hc b l)
    exact (show blockMat 4 0 (suMat b) * suMat (θ l) = suMat (θ l) * blockMat 4 0 (suMat b)
      from e).symm
  let lam : Su K p f 2 →* K :=
    { toFun := fun l => suMat (θ l) 0 0
      map_one' := by simp
      map_mul' := fun l l' => by
        obtain ⟨c, D, hcD⟩ := shape l
        obtain ⟨c', D', hcD'⟩ := shape l'
        show suMat (θ (l * l')) 0 0 = suMat (θ l) 0 0 * suMat (θ l') 0 0
        rw [map_mul θ, suMat_mul, hcD, hcD', BD_mul]
        simp [BD_eq, mul_comm] }
  have hcube : ∀ l : Su K p f 2, (lam.toHomUnits l) ^ 3 = 1 := by
    intro l
    have := Abelianization.commutator_subset_ker lam.toHomUnits
      (su2_pow_three_mem_commutator hK hp2 hqq l)
    rwa [MonoidHom.mem_ker, map_pow] at this
  have hlam : ∀ l : Su K p f 2, suMat (θ l) 0 0 = 1 := by
    intro l
    have h3 := hcube l
    have h8 := units_pow_eight hK9 (lam.toHomUnits l)
    have h1 : lam.toHomUnits l = 1 := by
      have : (lam.toHomUnits l) ^ (Nat.gcd 3 8) = 1 := pow_gcd_eq_one.mpr ⟨h3, h8⟩
      simpa using this
    have h4 : (lam l : K) = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) h1
    exact h4
  obtain ⟨c, D, hcD⟩ := shape (negOneSU K p f)
  have hc1 : c = 1 := by
    have e := congrFun (congrFun hcD 0) 0
    rw [hlam] at e
    simpa [BD_eq] using e.symm
  rw [hc1, one_smul] at hcD
  have hi : g * rootInvSU K p f (by norm_num : 2 ≤ 4) * g⁻¹ = θ (negOneSU K p f) := rfl
  rw [hi]
  have hsq : suMat (θ (negOneSU K p f)) * suMat (θ (negOneSU K p f)) = 1 := by
    rw [← suMat_mul, ← map_mul, negOneSU_mul_self, map_one, suMat_one]
  rw [hcD, BD_mul, ← BD_one] at hsq
  have hDD : D * D = 1 := (BD_inj hsq).2
  have hdet : D.det = 1 := by
    have := (θ (negOneSU K p f)).2.1
    rw [show (((θ (negOneSU K p f)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      suMat (θ (negOneSU K p f)) from rfl, hcD, det_BD, det_one, one_mul] at this
    exact this
  rcases eq_one_or_neg_one_of_sq_det h2 hDD hdet with h | h
  · exfalso
    rw [h, BD_one] at hcD
    have h1 : θ (negOneSU K p f) = 1 := suMat_injective (by rw [hcD, suMat_one])
    have h2' : negOneSU K p f = 1 := by
      have hinj : Function.Injective θ :=
        (MulEquiv.injective (MulAut.conj g)).comp (blockEmb_injective (by norm_num))
      exact hinj (by rw [h1, map_one])
    exact negOneSU_ne_one h2 h2'
  · rw [hcD, h]


end Aux

section Main


theorem y1c : Y1cStmt := by
  intro R hR R' hR' _ hcomm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := Q3W.card_gf9
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hqq : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hq3 : (3 : ℕ) ^ 1 % 4 = 3 := by norm_num
  have h2 : (2 : GaloisField 3 (2 * 1)) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
    (by norm_num : 2 ≤ 4)).mp hR
  obtain ⟨g₂, hg₂⟩ := (mem_longRootSetU_iff (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
    (by norm_num : 2 ≤ 4)).mp hR'
  set g : Su (GaloisField 3 (2 * 1)) 3 1 4 := g₁⁻¹ * g₂ with hg
  have hmem : ∀ (h : Su (GaloisField 3 (2 * 1)) 3 1 4)
      (l : Su (GaloisField 3 (2 * 1)) 3 1 2),
      h * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * h⁻¹ ∈
        (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map
          (MulAut.conj h).toMonoidHom := fun h l =>
    Subgroup.mem_map.mpr ⟨_, ⟨l, rfl⟩, rfl⟩
  have hc : ∀ b l : Su (GaloisField 3 (2 * 1)) 3 1 2,
      blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b *
          (g * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * g⁻¹) =
        (g * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * g⁻¹) *
          blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b := by
    intro b l
    have := hcomm _ (hg₁ ▸ hmem g₁ b) _ (hg₂ ▸ hmem g₂ l)
    calc blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b *
          (g * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * g⁻¹)
        = g₁⁻¹ * ((g₁ * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b * g₁⁻¹) *
            (g₂ * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * g₂⁻¹)) * g₁ := by
          rw [hg]
          group
      _ = g₁⁻¹ * ((g₂ * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * g₂⁻¹) *
            (g₁ * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b * g₁⁻¹)) * g₁ := by
          rw [this]
      _ = (g * blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) l * g⁻¹) *
            blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b := by
          rw [hg]
          group
  have hinv := invol_of_commuting hK hp2 hqq hq3 hc
  have hR2 : (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map
      (MulAut.conj g).toMonoidHom = rootSU2Two := by
    have h1 := (show IsLongRootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)
      ((rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map
        (MulAut.conj g).toMonoidHom)
      (g * rootInvSU (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4) * g⁻¹) from
      ⟨g, rfl, rfl⟩).eq_longRootGroupSU h2
    rw [h1, hinv, rootSU2Two,
      range_blockEmb_eq_longRootGroupSU h2 (by norm_num : 2 + 2 ≤ 4)]
    congr 1
    rw [negBlock]
    exact (blockMat_two_eq_BD _).symm
  refine ⟨g₁, hg₁, ?_⟩
  rw [hg₂, ← hR2, Subgroup.map_map]
  congr 1
  ext x
  simp [hg, mul_assoc]

end Main

end CFSG.ClassicalInvolution.Q3.Q3P21
