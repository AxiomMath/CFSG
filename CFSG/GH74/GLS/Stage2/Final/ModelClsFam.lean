module

public import CFSG.GH74.GLS.Stage2.Final.ModelClasses
public import CFSG.GH74.GLS.Stage2.Final.ModelSPMain
public import CFSG.GH74.GLS.Stage2.Final.ModelMinusUni

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage2.Final.ModelSp

variable {F : Type} [Field F]

theorem clsFacts_of [Finite F] {M : ModelData F} (hG : GoodModel M) {q : ℕ} (hq : Odd q)
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) (hJ : J0 F ∈ M.H2)
    (hjj : ∃ k ∈ M.K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F)
    (hnsm : ∀ a ∈ M.U2, ∃ k ∈ M.K4, k * (swapGL F * yGL F) * k⁻¹ = swapGL F * diagGL a (-a⁻¹))
    (hrefl : ∀ a b : GL (Fin 2) F, a ∈ M.U2 → b ∈ M.U2 → a * a = 1 → b * b = 1 → a ≠ 1 → a ≠ -1 →
      b ≠ 1 → b ≠ -1 → ConjMod M (diagGL a b) (xyGL F))
    (hplus : ∀ a ∈ M.U2, ConjMod M (swapGL F * diagGL a a⁻¹) (xyGL F))
    (hnoi : ∀ l : Fˣ, sc2 l ∈ M.U2 → l * l ≠ -1) : ClsFacts M where
  refl_D := hrefl
  plus_W := hplus
  minus_D := by
    intro a b ha hb haa hbb hda hdb
    set A : ↥M.H2 := ⟨a, (M.mem_H2 a).2 ⟨ha, hda⟩⟩ with hA
    set B : ↥M.H2 := ⟨b, (M.mem_H2 b).2 ⟨hb, hdb⟩⟩ with hB
    set J : ↥M.H2 := ⟨J0 F, hJ⟩ with hJdef
    have hAA : A * A = ⟨-1, M.neg_one_mem_H2⟩ := Subtype.ext haa
    have hBB : B * B = ⟨-1, M.neg_one_mem_H2⟩ := Subtype.ext hbb
    have hJJ : J * J = ⟨-1, M.neg_one_mem_H2⟩ := Subtype.ext J0_mul_self
    obtain ⟨x, hx⟩ := ord4_conj_H2 hG hq hSL hAA hJJ
    obtain ⟨y, hy⟩ := ord4_conj_H2 hG hq hSL hBB hJJ
    have hxy : diagGL (x : GL (Fin 2) F) (y : GL (Fin 2) F) ∈ M.K4 := diagGL_mem_K4_of_H2 M x y
    have hx' : (x : GL (Fin 2) F) * a * (x : GL (Fin 2) F)⁻¹ = J0 F := congrArg Subtype.val hx
    have hy' : (y : GL (Fin 2) F) * b * (y : GL (Fin 2) F)⁻¹ = J0 F := congrArg Subtype.val hy
    have h1 : diagGL (x : GL (Fin 2) F) y * diagGL a b * (diagGL (x : GL (Fin 2) F) y)⁻¹ =
        diagGL (J0 F) (J0 F) := by
      rw [diagGL_inv, diagGL_mul, diagGL_mul, hx', hy']
    obtain ⟨k₂, hk₂, hk₂c⟩ := hjj
    exact (ConjMod.of_conj hxy h1).trans (ConjMod.of_conj hk₂ hk₂c)
  minus_W := by
    intro a ha
    obtain ⟨k, hk, hkc⟩ := hnsm a ha
    exact ConjMod.of_conj (M.K4.inv_mem hk) (by rw [← hkc]; group)
  no_scalar_i := hnoi

theorem J0_mem_H2_lin (F : Type) [Field F] : J0 F ∈ (ModelData.lin F).H2 :=
  ((ModelData.lin F).mem_H2 _).2 ⟨Subgroup.mem_top _, det_J0⟩

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg in
theorem J0_mem_U2_uni {σ : F ≃+* F} : J0 F ∈ uniGL σ 2 := by
  show conjTr σ ((J0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    ((J0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
  have hc : conjTr σ ((J0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, coe_J0]
  rw [hc, coe_J0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem J0_mem_H2_uni {p f : ℕ} [Fact p.Prime] [CharP F p] [Finite F]
    (hF : Nat.card F = (p ^ f) ^ 2) : J0 F ∈ (ModelData.uni hF).H2 :=
  ((ModelData.uni hF).mem_H2 _).2 ⟨J0_mem_U2_uni, det_J0⟩

theorem clsFacts_sp [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) :
    ClsFacts (ModelData.sp F) := by
  have hG := goodModel_sp h2 h5
  have hq : Odd (Nat.card F) := odd_card_of_two_ne_zero h2
  refine clsFacts_of hG hq (hasSL2Model_H2_sp F) (J0_mem_H2_sp F) (jj_conj_sp h2)
    (fun a ha => nsm_conj_sp a ha) ?_ ?_ ?_
  · intro a b ha hb haa hbb ha1 ham hb1 hbm
    exfalso
    have hc : a * a = sc2 (1 : Fˣ) := by rw [haa, sc2_one]
    rcases ch_sq hc with ⟨l, hl, hll⟩ | ⟨-, hd⟩
    · rcases units_sq_eq_one hll with rfl | rfl
      · exact ha1 (by rw [hl, sc2_one])
      · exact ham (by rw [hl, sc2_neg_one])
    · rw [mem_U2_sp.1 ha] at hd
      apply h2
      simp only [Units.val_one] at hd
      linear_combination hd
  · intro a ha
    obtain ⟨k, hk, hkc⟩ := ns_conj_sp a ha
    obtain ⟨k₂, hk₂, hk₂c⟩ := w_conj_sp h2
    have h1 : ConjMod (ModelData.sp F) (swapGL F * diagGL a a⁻¹) (swapGL F) :=
      ConjMod.of_conj ((ModelData.sp F).K4.inv_mem hk) (by rw [← hkc]; group)
    exact h1.trans (ConjMod.of_conj hk₂ hk₂c)
  · intro l hl hll
    have h1 := mem_U2_sp.1 hl
    rw [det_sc2] at h1
    have h3 : (l : F) * l = 1 := by simpa [sq] using h1
    have h4 : (l : F) * l = -1 := by
      have := congrArg (fun u : Fˣ => (u : F)) hll
      simpa using this
    apply h2
    linear_combination h4 - h3

theorem clsFacts_lin [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (hq4 : Nat.card F % 4 = 3) :
    ClsFacts (ModelData.lin F) := by
  have hG := goodModel_lin h2 h5
  have hq : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have hFl := luFacts_lin h2
  refine clsFacts_of hG hq (hasSL2Model_H2_lin F) (J0_mem_H2_lin F) (jj_conj_lin h2)
    (fun a _ => nsm_conj_lin h2 a) ?_ ?_ ?_
  · intro a b ha hb haa hbb ha1 ham hb1 hbm
    exact D_refl hFl ha hb haa hbb ha1 ham hb1 hbm
  · intro a ha
    exact W_one hFl ha
  · intro l _ hll
    have : Fintype F := Fintype.ofFinite F
    have hsq : IsSquare (-1 : F) := ⟨l, by
      have := congrArg (fun u : Fˣ => (u : F)) hll
      simpa using this.symm⟩
    have := FiniteField.isSquare_neg_one_iff.1 hsq
    rw [← Nat.card_eq_fintype_card] at this
    exact this hq4

theorem clsFacts_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1) :
    ClsFacts (ModelData.uni hF) := by
  have hG := goodModel_uni hF hp2 h5
  have hq : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  have hFu := luFacts_uni hF hp2
  refine clsFacts_of hG hq (hasSL2Model_H2_uni hF) (J0_mem_H2_uni hF)
    (jj_conj_uni hF hG.two_ne_zero hq4) (fun a ha => nsm_conj_uni hF hG.two_ne_zero hq4 a ha) ?_ ?_ ?_
  · intro a b ha hb haa hbb ha1 ham hb1 hbm
    exact D_refl hFu ha hb haa hbb ha1 ham hb1 hbm
  · intro a ha
    exact W_one hFu ha
  · intro l hl hll
    have hl' := (sc2_mem_uni_iff hF l).1 hl
    obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 4 * m + 2 := ⟨p ^ f / 4, by omega⟩
    have h4 : l ^ 4 = 1 := pow_four_of_sq hll
    rw [hm, pow_add, pow_mul, h4, one_pow, one_mul, sq, hll] at hl'
    have := congrArg (fun u : Fˣ => (u : F)) hl'
    simp only [Units.val_neg, Units.val_one] at this
    apply hG.two_ne_zero
    linear_combination -this

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
