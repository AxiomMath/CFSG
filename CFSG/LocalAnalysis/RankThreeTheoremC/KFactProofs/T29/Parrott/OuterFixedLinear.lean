module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedBasic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SectionRank.ClassicalEven (rotMatrix rotCol)

section Rotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rotMatrix_map_ringHom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (i j : ι) :
    (rotMatrix (K := R) i j).map φ = rotMatrix (K := S) i j := by
  ext a b
  simp only [Matrix.map_apply, rotMatrix, Matrix.of_apply, rotCol]
  split_ifs <;> simp [Pi.single_apply, apply_ite φ]

theorem scalar_mulVec_eq_smul {R : Type*} [CommRing R] (c : R) (v : ι → R) :
    Matrix.scalar ι c *ᵥ v = c • v := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem rotMatrix_pow_mulVec_single_of_ne {K : Type*} [CommRing K] {i j b : ι} (hi : b ≠ i)
    (hj : b ≠ j) (m : ℕ) :
    (rotMatrix (K := K) i j ^ m) *ᵥ Pi.single b 1 = Pi.single b 1 := by
  induction m with
  | zero => rw [pow_zero, one_mulVec]
  | succ m ih =>
    rw [pow_succ, ← mulVec_mulVec, CFSG.SectionRank.ClassicalEven.rotMatrix_mulVec_of_ne hi hj, ih]

end Rotation

section PSL

variable {n : ℕ} {K : Type} [Field K]

@[expose] def slRot (i j : Fin n) : SpecialLinearGroup (Fin n) K :=
  ⟨rotMatrix i j, CFSG.SectionRank.ClassicalEven.det_rotMatrix i j⟩

theorem slRot_pow_three (i j : Fin n) : slRot (K := K) i j ^ 3 = 1 := by
  have h : ((slRot (K := K) i j ^ 3 : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact CFSG.SectionRank.ClassicalEven.rotMatrix_pow_three i j
  exact Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm)

theorem slRot_commute {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : slRot (K := K) i j * slRot k l = slRot k l * slRot i j := by
  apply Subtype.ext
  exact (CFSG.SectionRank.ClassicalEven.rotMatrix_commute hik hil hjk hjl).eq

theorem map_slRot (σ : K ≃+* K) (i j : Fin n) :
    SpecialLinearGroup.map σ.toRingHom (slRot (K := K) i j) = slRot i j := by
  apply Subtype.ext
  exact rotMatrix_map_ringHom σ.toRingHom i j

theorem fieldAut_proj_slRot (σ : K ≃+* K) (i j : Fin n) :
    fieldAut n K σ (proj n K (slRot i j)) = proj n K (slRot i j) := by
  rw [fieldAut_proj, map_slRot]

theorem mul_mem_scalars_ne {g h z : SpecialLinearGroup (Fin n) K} {a b : Fin n} (hab : a ≠ b)
    (hg : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single a 1 = Pi.single a 1)
    (hh : (h : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single a 1 = Pi.single b 1)
    (hz : z ∈ scalars n K) : g * z ≠ h := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  intro he
  have h1 := congrFun (congrArg (fun k : SpecialLinearGroup (Fin n) K =>
    (k : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single a 1) he) b
  simp only [Matrix.SpecialLinearGroup.coe_mul, hc, ← mulVec_mulVec, scalar_mulVec_eq_smul,
    mulVec_smul, hg, hh] at h1
  simp [Pi.single_apply, hab, hab.symm] at h1

theorem slRot_proj_pair (hn : 4 ≤ n) :
    proj n K (slRot ⟨0, by omega⟩ ⟨1, by omega⟩) ≠ 1 ∧
      proj n K (slRot ⟨0, by omega⟩ ⟨1, by omega⟩) ^ 3 = 1 ∧
      proj n K (slRot ⟨2, by omega⟩ ⟨3, by omega⟩) ^ 3 = 1 ∧
      proj n K (slRot ⟨0, by omega⟩ ⟨1, by omega⟩) *
          proj n K (slRot ⟨2, by omega⟩ ⟨3, by omega⟩) =
        proj n K (slRot ⟨2, by omega⟩ ⟨3, by omega⟩) *
          proj n K (slRot ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
      proj n K (slRot ⟨2, by omega⟩ ⟨3, by omega⟩) ∉
        zpowers (proj n K (slRot ⟨0, by omega⟩ ⟨1, by omega⟩)) := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set i3 : Fin n := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [i0, i2, Fin.ext_iff]
  have h21 : i2 ≠ i1 := by simp [i1, i2, Fin.ext_iff]
  have h02 : i0 ≠ i2 := h20.symm
  have h03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
  have h12 : i1 ≠ i2 := h21.symm
  have h13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  refine ⟨?_, by rw [← map_pow, slRot_pow_three, map_one], by rw [← map_pow, slRot_pow_three,
    map_one], by rw [← map_mul, slRot_commute h02 h03 h12 h13, map_mul], ?_⟩
  · intro h
    exact mul_mem_scalars_ne (g := 1) h01 (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec])
      (CFSG.SectionRank.ClassicalEven.rotMatrix_mulVec_left i0 i1) (proj_eq_one_iff.1 h)
      (one_mul _)
  · intro h
    have hfin : IsOfFinOrder (proj n K (slRot (K := K) i0 i1)) :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, by rw [← map_pow, slRot_pow_three, map_one]⟩
    obtain ⟨m, hm⟩ := (hfin.mem_powers_iff_mem_zpowers).2 h
    change proj n K (slRot i0 i1) ^ m = proj n K (slRot i2 i3) at hm
    rw [← map_pow, proj_eq_proj_iff] at hm
    refine mul_mem_scalars_ne (g := slRot i0 i1 ^ m) h23 ?_
      (CFSG.SectionRank.ClassicalEven.rotMatrix_mulVec_left i2 i3) hm (mul_inv_cancel_left _ _)
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact rotMatrix_pow_mulVec_single_of_ne h20 h21 m

theorem exists_E9_fixed_fieldAut [Finite K] (hn : 4 ≤ n) (σ : K ≃+* K) :
    ∃ E : Subgroup (projectiveSL n K), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, fieldAut n K σ e = e := by
  obtain ⟨h1, h3, h3', hc, hz⟩ := slRot_proj_pair (K := K) hn
  obtain ⟨E, hEH, hE, hE9⟩ :=
    exists_E9_le_of_pair (H := CFSG.RankThree.PartOne.CTP.fixedSubgroup (fieldAut n K σ))
      (fieldAut_proj_slRot σ _ _) (fieldAut_proj_slRot σ _ _) h1 h3 h3' hc hz
  exact ⟨E, hE, hE9, fun e he => hEH he⟩

theorem outerFixesE9_projectiveSL [Finite K] (hn : 4 ≤ n)
    (hcop : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1))) : OuterFixesE9 (projectiveSL n K) := by
  refine outerFixesE9_of_descent fun α hα3 hαo => ?_
  have hD : α ∉ linearAutGroup n K := fun hD =>
    hαo (CFSG.RankThree.PartOne.KCLinPlane.inner_of_mem_linearAut_of_pow_eq_one (by omega) hcop
      hD hα3)
  obtain ⟨σ, -, H, rfl⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (by omega) α hα3 hD
  exact ⟨conjAut n K H, fieldAut n K σ, rfl, exists_E9_fixed_fieldAut hn σ⟩

end PSL

theorem outerFixedAt_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) (hr : 3 ≤ r)
    (hcop : ¬ 3 ∣ Nat.gcd (r + 1) (q.card - 1)) : OuterFixedAt ⟨.A r q, hv⟩ := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  refine outerFixedAt_of_model fun K _ _ e => ?_
  have hF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  refine ⟨projectiveSL (r + 1) (GaloisField q.p q.exponent), inferInstance,
    outerFixesE9_projectiveSL (by omega) ?_,
    ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        (r + 1) (GaloisField q.p q.exponent))⟩⟩
  rw [hF]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
