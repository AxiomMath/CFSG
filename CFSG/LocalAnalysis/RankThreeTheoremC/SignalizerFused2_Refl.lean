module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Det

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.SectionRank.Ccomm
open scoped commutatorElement

section Determinant

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem det_eq_of_center_pow (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hZ : Nat.card (Subgroup.center G) = p) (hnc : ∃ a b : G, a * b ≠ b * a)
    (e : G ⧸ Subgroup.center G ≃* Multiplicative (Fin 2 → ZMod p)) (σ : MulAut G) (k : ℤ)
    (hσ : ∀ c ∈ Subgroup.center G, σ c = c ^ k) :
    ((elemAutEquivGL e (autQuotient (Subgroup.center G) σ) : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = (k : ZMod p) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨a, ha⟩ : ∃ a : G, e (a : G ⧸ Subgroup.center G) =
      Multiplicative.ofAdd (Pi.single 0 1) := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (Pi.single 0 1))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, hq⟩
  obtain ⟨b, hb⟩ : ∃ b : G, e (b : G ⧸ Subgroup.center G) =
      Multiplicative.ofAdd (Pi.single 1 1) := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (Pi.single 1 1))
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨b, hq⟩
  set A : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((elemAutEquivGL e (autQuotient (Subgroup.center G) σ) : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) with hA
  set c : G := ⁅a, b⁆ with hcdef
  have hcZ : c ∈ Subgroup.center G := hc a b
  have hc1 : c ≠ 1 := by
    intro hc1
    obtain ⟨u, v, huv⟩ := hnc
    apply huv
    have := commutator_coord hc e a b ha hb u v
    rw [← hcdef, hc1, one_pow, inv_one, one_pow, one_mul] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hco : orderOf c = p := by
    have hdvd : orderOf c ∣ p := by
      rw [← hZ, ← Subgroup.orderOf_mk c hcZ]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hc1
    · exact h1
  have hσa : Multiplicative.toAdd (e ((σ a : G) : G ⧸ Subgroup.center G)) =
      A.mulVec (Pi.single 0 1) := by
    rw [← autQuotient_mk, ← elemAutEquivGL_mulVec e _ (a : G ⧸ Subgroup.center G), ha]
    rfl
  have hσb : Multiplicative.toAdd (e ((σ b : G) : G ⧸ Subgroup.center G)) =
      A.mulVec (Pi.single 1 1) := by
    rw [← autQuotient_mk, ← elemAutEquivGL_mulVec e _ (b : G ⧸ Subgroup.center G), hb]
    rfl
  have key := commutator_coord hc e a b ha hb (σ a) (σ b)
  rw [hσa, hσb, ← hcdef, ← map_commutatorElement, hσ c hcZ] at key
  have h00 : A.mulVec (Pi.single 0 1) 0 = A 0 0 := by simp [Matrix.col_apply]
  have h10 : A.mulVec (Pi.single 0 1) 1 = A 1 0 := by simp [Matrix.col_apply]
  have h01 : A.mulVec (Pi.single 1 1) 0 = A 0 1 := by simp [Matrix.col_apply]
  have h11 : A.mulVec (Pi.single 1 1) 1 = A 1 1 := by simp [Matrix.col_apply]
  rw [h00, h10, h01, h11] at key
  set M : ℕ := (A 0 0).val * (A 1 1).val with hM
  set N : ℕ := (A 1 0).val * (A 0 1).val with hN
  have hzpow : c ^ ((M : ℤ) - N - k) = 1 := by
    rw [_root_.zpow_sub, _root_.zpow_sub, zpow_natCast, zpow_natCast, ← inv_pow]
    rw [key, mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hzpow
  rw [hco] at hdvd
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  push_cast at hzero
  rw [hM, hN] at hzero
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val] at hzero
  rw [Matrix.det_fin_two]
  linear_combination hzero

end Determinant

section Linear

variable {p : ℕ} [Fact p.Prime]

theorem det_eq_one_of_commute_of_fixed (A T : GL (Fin 2) (ZMod p)) (hAT : A * T = T * A)
    (hTp : T ^ p = 1) (hT1 : T ≠ 1) (v : Fin 2 → ZMod p) (hv : v ≠ 0)
    (hTv : (T : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v)
    (hAv : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  obtain ⟨g, hg⟩ := CFSG.RankThree.SubgroupLists.exists_conj_transvection T hTp hT1
  set U : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 0, 1] with hU
  set gm : Matrix (Fin 2) (Fin 2) (ZMod p) := (g : Matrix (Fin 2) (Fin 2) (ZMod p)) with hgm
  set gi : Matrix (Fin 2) (Fin 2) (ZMod p) := ((g⁻¹ : GL (Fin 2) (ZMod p)) :
    Matrix (Fin 2) (Fin 2) (ZMod p)) with hgi
  have hgg : gm * gi = 1 := by
    rw [hgm, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : gi * gm = 1 := by
    rw [hgm, hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set Am : Matrix (Fin 2) (Fin 2) (ZMod p) := (A : Matrix (Fin 2) (Fin 2) (ZMod p)) with hAm
  set Tm : Matrix (Fin 2) (Fin 2) (ZMod p) := (T : Matrix (Fin 2) (Fin 2) (ZMod p)) with hTm
  have hATm : Am * Tm = Tm * Am := by
    rw [hAm, hTm, ← Units.val_mul, ← Units.val_mul, hAT]
  have hTg : Tm * gm = gm * U := hg
  have hUg : U * gi = gi * Tm := by
    calc U * gi = gi * (gm * U) * gi := by rw [← mul_assoc, hgg', one_mul]
      _ = gi * (Tm * gm) * gi := by rw [hTg]
      _ = gi * Tm * (gm * gi) := by simp only [mul_assoc]
      _ = gi * Tm := by rw [hgg, mul_one]
  set A' : Matrix (Fin 2) (Fin 2) (ZMod p) := gi * Am * gm with hA'
  have hA'U : A' * U = U * A' := by
    calc A' * U = gi * Am * (gm * U) := by rw [hA', mul_assoc]
      _ = gi * Am * (Tm * gm) := by rw [hTg]
      _ = gi * (Am * Tm) * gm := by simp only [mul_assoc]
      _ = gi * (Tm * Am) * gm := by rw [hATm]
      _ = (gi * Tm) * Am * gm := by simp only [mul_assoc]
      _ = U * gi * Am * gm := by rw [hUg]
      _ = U * A' := by rw [hA']; simp only [mul_assoc]
  set v' : Fin 2 → ZMod p := gi *ᵥ v with hv'
  have hUv' : U *ᵥ v' = v' := by
    rw [hv', Matrix.mulVec_mulVec, hUg, ← Matrix.mulVec_mulVec, hTv]
  have hgv : gm *ᵥ v' = v := by
    rw [hv', Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hA'v' : A' *ᵥ v' = v' := by
    calc A' *ᵥ v' = (gi * Am * gm) *ᵥ v' := rfl
      _ = gi *ᵥ (Am *ᵥ (gm *ᵥ v')) := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = v' := by rw [hgv, hAv]
  have hv'1 : v' 1 = 0 := by
    have := congrFun hUv' 0
    simp [hU, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this
  have hv'0 : v' 0 ≠ 0 := by
    intro h0
    apply hv
    rw [← hgv]
    have : v' = 0 := by
      ext i
      fin_cases i
      · exact h0
      · exact hv'1
    rw [this, Matrix.mulVec_zero]
  have hA00 : A' 0 0 = 1 := by
    have := congrFun hA'v' 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv'1] at this
    exact mul_right_cancel₀ hv'0 (by rw [this, one_mul])
  have hA10 : A' 1 0 = 0 := by
    have := congrFun (congrFun hA'U 0) 0
    simp [hU, Matrix.mul_apply, Fin.sum_univ_two] at this
    exact this
  have hA11 : A' 1 1 = 1 := by
    have := congrFun (congrFun hA'U 0) 1
    simp [hU, Matrix.mul_apply, Fin.sum_univ_two] at this
    rw [← hA00]
    linear_combination -this
  have hdet : A'.det = Am.det := by
    have h1 := congrArg Matrix.det hgg'
    rw [Matrix.det_mul, Matrix.det_one] at h1
    rw [hA', Matrix.det_mul, Matrix.det_mul]
    calc Matrix.det gi * Matrix.det Am * Matrix.det gm
        = Matrix.det Am * (Matrix.det gi * Matrix.det gm) := by ring
      _ = Matrix.det Am := by rw [h1, mul_one]
  rw [← hdet, Matrix.det_fin_two, hA00, hA10, hA11]
  ring

end Linear

section Reflection

variable {E : Type*} [Group E] {p : ℕ} [Fact p.Prime]

theorem reflection_center_fixed_aut (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E)
    (hZ : Nat.card (Subgroup.center E) = p) (hnc : ∃ a b : E, a * b ≠ b * a)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) (σ τ : MulAut E) (k : ℤ)
    (hσ : ∀ c ∈ Subgroup.center E, σ c = c ^ k) (hστ : σ * τ = τ * σ) (hτp : τ ^ p = 1)
    (hτ1 : ¬ ∀ x : E, x⁻¹ * τ x ∈ Subgroup.center E) {a : E} (haz : a ∉ Subgroup.center E)
    (hτa : τ a = a) (hσa : ∃ c ∈ Subgroup.center E, σ a = a * c) : (k : ZMod p) = 1 := by
  set A : GL (Fin 2) (ZMod p) := elemAutEquivGL e (autQuotient (Subgroup.center E) σ) with hA
  set T : GL (Fin 2) (ZMod p) := elemAutEquivGL e (autQuotient (Subgroup.center E) τ) with hT
  have hAT : A * T = T * A := by
    rw [hA, hT, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hστ]
  have hTp : T ^ p = 1 := by
    rw [hT, ← map_pow, ← map_pow, hτp, map_one, map_one]
  have hT1 : T ≠ 1 := by
    intro h
    apply hτ1
    have h1 : autQuotient (Subgroup.center E) τ = 1 := by
      refine (elemAutEquivGL e).injective ?_
      rw [← hT, h, map_one]
    exact (mem_ker_autQuotient (Subgroup.center E)).mp (MonoidHom.mem_ker.mpr h1)
  set v : Fin 2 → ZMod p := Multiplicative.toAdd (e (a : E ⧸ Subgroup.center E)) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    apply haz
    have h1 : e (a : E ⧸ Subgroup.center E) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hv, h0]
      rfl
    have h2 : (a : E ⧸ Subgroup.center E) = 1 := e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hTv : (T : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v := by
    rw [hT, hv, elemAutEquivGL_mulVec, autQuotient_mk, hτa]
  have hAv : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v := by
    obtain ⟨c, hcc, hc'⟩ := hσa
    rw [hA, hv, elemAutEquivGL_mulVec, autQuotient_mk, hc']
    congr 2
    rw [QuotientGroup.eq]
    simpa using hcc
  have hdet1 := det_eq_one_of_commute_of_fixed A T hAT hTp hT1 v hv0 hTv hAv
  have hdetk := det_eq_of_center_pow hc hZ hnc e σ k hσ
  rw [← hA, hdet1] at hdetk
  exact hdetk.symm

end Reflection

end CFSG.LocalAnalysis.RankThreeTheoremC
