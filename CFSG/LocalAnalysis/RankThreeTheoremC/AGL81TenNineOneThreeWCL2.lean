module

public import CFSG.Quasithin.Vol2.Ch11SecBK10H
public import CFSG.Adapters.LinearCatalog
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace L2

open Matrix CFSG.GorensteinWalter CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem quot_eq {A B : SL(2, F)} (h : psl2QuotientMap F A = psl2QuotientMap F B) :
    ∃ r : F, r ^ 2 = 1 ∧ (B : Matrix (Fin 2) (Fin 2) F) = r • (A : Matrix (Fin 2) (Fin 2) F) := by
  have h1 : A⁻¹ * B ∈ Subgroup.center (SL(2, F)) := QuotientGroup.eq.mp h
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  refine ⟨r, by simpa using hr, ?_⟩
  have h2 : (B : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [h2, ← hrA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem trace_unip (b : F) :
    ((sl2UpperUnipotent b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace = 2 := by
  simp [sl2UpperUnipotent, Matrix.trace_fin_two]
  norm_num

theorem trace_conjSL (G : GL (Fin 2) F) (A : SL(2, F)) :
    ((conjSL G A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      (A : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [coe_conjSL, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem map_unip (σ : F ≃+* F) (b : F) :
    SpecialLinearGroup.map σ.toRingHom (sl2UpperUnipotent b) = sl2UpperUnipotent (σ b) := by
  apply Subtype.ext
  change σ.toRingHom.mapMatrix !![1, b; 0, 1] = !![1, σ b; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

variable [CharP F 3]

theorem two_ne_zero' : (2 : F) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F 3] at h2
  norm_num at h2

theorem conj_unip_eq {G : GL (Fin 2) F} {c b : F}
    (h : psl2QuotientMap F (conjSL G (sl2UpperUnipotent c)) =
      psl2QuotientMap F (sl2UpperUnipotent b)) :
    conjSL G (sl2UpperUnipotent c) = sl2UpperUnipotent b := by
  obtain ⟨r, -, hB⟩ := quot_eq h
  have htr := congrArg Matrix.trace hB
  rw [Matrix.trace_smul, trace_conjSL, trace_unip, trace_unip, smul_eq_mul] at htr
  have hr1 : r = 1 := by
    have h0 : (r - 1) * 2 = 0 := by linear_combination -htr
    rcases mul_eq_zero.mp h0 with h | h
    · linear_combination h
    · exact absurd h two_ne_zero'
  apply Subtype.ext
  rw [hB, hr1, one_smul]

theorem cancel_right {G : GL (Fin 2) F} {X Y : Matrix (Fin 2) (Fin 2) F}
    (h : X * (G : Matrix (Fin 2) (Fin 2) F) = Y * (G : Matrix (Fin 2) (Fin 2) F)) : X = Y := by
  have := congrArg (· * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at this
  exact this

theorem conjSL_eq_of_mul {G : GL (Fin 2) F} {A Y : SL(2, F)}
    (h : (Y : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * A) : conjSL G A = Y := by
  apply Subtype.ext
  apply cancel_right (G := G)
  rw [conjSL_mul, h]

theorem inner_of_fix_unip [Finite F] (β : MulAut (PSL2 F))
    (hβ : ∀ b : F, β (psl2QuotientMap F (sl2UpperUnipotent b)) =
      psl2QuotientMap F (sl2UpperUnipotent b)) :
    ∃ g : PSL2 F, ∀ x, β x = g * x * g⁻¹ := by
  obtain ⟨G, hG⟩ := exists_rep β
  set σ := galPart β
  have hfix : ∀ b, conjSL G (sl2UpperUnipotent (σ b)) = sl2UpperUnipotent b := by
    intro b
    apply conj_unip_eq
    have := hβ b
    rw [hG, MulAut.mul_apply, psl2FieldAut_mk, map_unip, pglAction_mk] at this
    exact this
  set M := (G : Matrix (Fin 2) (Fin 2) F) with hM
  have h1 : (sl2UpperUnipotent (1 : F) : Matrix (Fin 2) (Fin 2) F) * M =
      M * sl2UpperUnipotent (1 : F) := by
    have hf := hfix 1
    simp only [map_one] at hf
    have := conjSL_mul G (sl2UpperUnipotent (1 : F))
    rw [hf] at this
    exact this
  have h10 : M 1 0 = 0 := by
    have := congrFun (congrFun h1 0) 0
    simp [sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two] at this
    exact this
  have h11 : M 1 1 = M 0 0 := by
    have := congrFun (congrFun h1 0) 1
    simp [sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, h10] at this
    linear_combination this
  have hcomm : ∀ c : F, (sl2UpperUnipotent c : Matrix (Fin 2) (Fin 2) F) * M =
      M * sl2UpperUnipotent c := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, h10, h11] <;> ring
  have hconj : ∀ c : F, conjSL G (sl2UpperUnipotent c) = sl2UpperUnipotent c :=
    fun c => conjSL_eq_of_mul (hcomm c)
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro b
    have h := hfix b
    rw [hconj] at h
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa [sl2UpperUnipotent] using this
  have hdet : M 0 0 ≠ 0 := by
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp (by rw [hM]; exact G.isUnit)
    rw [Matrix.det_fin_two, h10, h0] at hu
    simp at hu
  set c₀ := M 0 1 / M 0 0
  have hGu : M = M 0 0 • (sl2UpperUnipotent c₀ : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent, h10, h11, c₀] <;> field_simp
  refine ⟨psl2QuotientMap F (sl2UpperUnipotent c₀), fun x => ?_⟩
  obtain ⟨A, rfl⟩ := psl2QuotientMap_surjective x
  rw [hG, hσ, map_one, mul_one, pglAction_mk, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply conjSL_eq_of_mul
  rw [← hM, hGu]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.adjugate_mul, (sl2UpperUnipotent c₀).2, one_smul,
    Matrix.mul_one]

noncomputable def dmat (l : F) (hl : l ≠ 0) : SL(2, F) :=
  ⟨!![l, 0; 0, l⁻¹], by simp [Matrix.det_fin_two_of, hl]⟩

theorem dmat_conj (l : F) (hl : l ≠ 0) (b : F) :
    dmat l hl * sl2UpperUnipotent b * (dmat l hl)⁻¹ = sl2UpperUnipotent (l ^ 2 * b) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem unip_inj {x y : F} (h : psl2QuotientMap F (sl2UpperUnipotent x) =
    psl2QuotientMap F (sl2UpperUnipotent y)) : x = y := by
  obtain ⟨r, -, hB⟩ := quot_eq h
  have h00 := congrFun (congrFun hB 0) 0
  have h01 := congrFun (congrFun hB 0) 1
  simp [sl2UpperUnipotent] at h00 h01
  rw [h01, ← h00, one_mul]

theorem unip_zpow (b : F) (k : ℤ) :
    sl2UpperUnipotent b ^ k = sl2UpperUnipotent ((k : F) * b) := by
  have h := map_zpow (sl2UpperUnipotentHom F) (Multiplicative.ofAdd b) k
  simp only [sl2UpperUnipotentHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h
  rw [← h, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_eq_mul]

theorem intCast_trichotomy (k : ℤ) : (k : F) = 0 ∨ (k : F) = 1 ∨ (k : F) = -1 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hk]
  push_cast
  rw [h3, zero_mul, zero_add]
  rcases hr with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right
    have : (2 : F) = -1 := by linear_combination h3
    exact_mod_cast this

theorem exists_l [Finite F] (h9 : 9 ≤ Nat.card F) : ∃ l : F, l ≠ 0 ∧ l ^ 4 ≠ 1 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨γ, γ.ne_zero, fun h => ?_⟩
  have h4 : γ ^ 4 = 1 := Units.ext (by simpa using h)
  have hdvd := orderOf_dvd_of_pow_eq_one h4
  rw [hγ] at hdvd
  have hc : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_units]
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem center_psl2 [Finite F] (h9 : 9 ≤ Nat.card F) : Subgroup.center (PSL2 F) = ⊥ := by
  haveI : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2 F)) with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl0, hl4⟩ := exists_l h9
    have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top
      (psl2QuotientMap F (dmat l hl0))) (psl2QuotientMap F (sl2UpperUnipotent 1))
    have h1 : psl2QuotientMap F (sl2UpperUnipotent (1 : F)) =
        psl2QuotientMap F (sl2UpperUnipotent (l ^ 2 * 1)) := by
      rw [← dmat_conj l hl0, map_mul, map_mul, map_inv, ← hc]
      group
    have := unip_inj h1
    apply hl4
    have h2 : l ^ 2 = 1 := by linear_combination -this
    rw [show l ^ 4 = (l ^ 2) ^ 2 by ring, h2, one_pow]

theorem exists_equiv_psl2 {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 3 ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 3), 9 ≤ Nat.card F ∧
      Nonempty (K ≃* PSL2 F) := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  simp only at hd1
  subst hd1
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hqp ▸ inferInstance, ?_,
    ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)⟩⟩
  rw [GaloisField.card _ _ (by omega), hqp]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hqe

end L2

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
