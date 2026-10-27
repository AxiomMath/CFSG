module

public import CFSG.ClassicalInvolution.Q3.Q3URPat
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainSUs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic.CoreAssembly

section InnerDiag

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem innerDiag_three_su3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (hcen : ∀ x ∈ Subgroup.center (Su K p f (2 + 1)), ¬ 3 ∣ orderOf x)
    {Y : Type} [Group Y] (θ : Su K p f (2 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (2 + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f 2 0 A)) = θ (blockEmb2 K p f 2 0 A)) :
    ∃ w : ZMod 2, ∀ x, σ (θ x) = θ (conjSign hK (twoOneSigns w) x) := by
  classical
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    Q3NT.unitaryAutClassification_ambient_of_odd hK hp2 hf (by omega : 3 ≤ 2 + 1) θ hker σ hσ
      hstab
  have hαfix : ∀ A : Su K p f 2, α (blockEmb2 K p f 2 0 A) = blockEmb2 K p f 2 0 A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed3 hP3 hker (fun x hx => hcen x (hker hx)) hlift
      (blockEmb2 K p f 2 0) hfix) A
  set G : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K := (g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K)
    with hG
  set Gi : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K :=
    ((g⁻¹ : GL (Fin (2 + 1)) K) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne h hp2
  set c : K := ((u : Kˣ) : K) with hc
  have hcinv : (((u : Kˣ)⁻¹ : Kˣ) : K) = c⁻¹ := Units.val_inv_eq_inv_val _
  have hu2' : c⁻¹ ≠ c := by rw [← hcinv]; exact hu2
  have hrefl : ∀ M : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K,
      (RingEquiv.refl K).mapMatrix M = M := fun M => by ext a b; rfl
  rcases hφ with hid | hbar
  ·
    subst hid
    have hrel : ∀ i j : Fin (2 + 1),
        (if i.val = (0 : Fin 2).val then c else if i.val = (0 : Fin 2).val + 1 then c⁻¹ else 1) *
          G i j = G i j * (if j.val = (0 : Fin 2).val then c else
            if j.val = (0 : Fin 2).val + 1 then c⁻¹ else 1) := by
      intro i j
      have h1 := hmat (blockEmb2 K p f 2 0 (torusTwo (unitaryInvolution K p f) u))
      rw [hαfix _, coe_coe_blockEmb2_torusTwo] at h1
      have h3 := diagonal_relation (RingEquiv.refl K) G Gi hGiG _ h1.symm i j
      simpa [hcinv] using h3
    have hdiag : ∀ i j : Fin (2 + 1), i ≠ j → G i j = 0 := by
      intro i j hij
      by_contra hne
      rcases torus_entry_cases_id (0 : Fin 2) c hu1 hu2' i j (G i j) hne (hrel i j) with
        heq | ⟨h4, h5, h6, h7⟩
      · exact hij heq
      · apply hij
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        simp only [Fin.val_zero] at h4 h5 h6 h7
        omega
    obtain ⟨hd0, hconj⟩ := conj_entry_of_offdiag_zero G Gi hGGi hGiG hdiag
    have hu01 : G 0 0 = G 1 1 := by
      have h1 := hmat (blockEmb2 K p f 2 0 (weylElt K p f))
      rw [hαfix _, hrefl] at h1
      have h2' := congrFun (congrFun h1 0) 1
      rw [hconj] at h2'
      have hX := coe_coe_blockEmb2_weylElt_row (K := K) (p := p) (f := f) 2 0 0 1 rfl
      rw [ite_eq_left (show (1 : Fin (2 + 1)).val = (0 : Fin 2).val + 1 from rfl)] at hX
      rw [hX] at h2'
      have hj := hd0 1
      field_simp at h2'
      exact h2'.symm
    obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, G * G = c₂ • (1 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) := by
      refine eq_smul_one_of_commute h hp2 (by omega) (G * G) fun y hy => ?_
      have hy' : y ∈ SUid (unitaryInvolution K p f) (2 + 1) := by
        rw [SUid_eq_statedSU hK]
        exact hy
      have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
      have h2' := congrArg (fun x : Su K p f (2 + 1) =>
        ((x : GL (Fin (2 + 1)) K) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K)) h1
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2'
      rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2'
      have h3 := commute_of_double_conj (RingEquiv.refl K) (fun _ => rfl) G Gi
        (y : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) hGiG h2'.symm
      simpa [RingEquiv.mapMatrix_apply] using h3
    have hGd : G = diagonal fun i => G i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
    have hsqd : ∀ i, G i i * G i i = c₂ := fun i => by
      have := congrFun (congrFun hc₂ i) i
      rw [hGd, Matrix.diagonal_mul_diagonal] at this
      simpa using this
    obtain ⟨v, hv⟩ : ∃ v : Fin (2 + 1) → ZMod 2,
        v = fun i => if G i i = G 0 0 then 0 else 1 := ⟨_, rfl⟩
    have hvG : ∀ i, G i i = G 0 0 * signVal K (v i) := fun i => by
      by_cases hi : G i i = G 0 0
      · simp [hv, hi, signVal]
      · have hsq' : G i i * G i i = G 0 0 * G 0 0 := by rw [hsqd i, hsqd 0]
        rcases mul_self_eq_mul_self_iff.mp hsq' with h' | h'
        · exact absurd h' hi
        · simp [hv, signVal, h']
    have hv0 : v 0 = 0 := by simp [hv]
    have hv1 : v 1 = 0 := by simp [hv, hu01]
    have hvw : v = twoOneSigns (v 2) := by
      funext i
      fin_cases i
      · simpa [twoOneSigns] using hv0
      · simpa [twoOneSigns] using hv1
      · simp [twoOneSigns]
    have hs : ∀ b : ZMod 2, (signVal K b)⁻¹ = signVal K b := fun b =>
      inv_eq_of_mul_eq_one_right (signVal_mul_self _)
    have hαx : ∀ x : Su K p f (2 + 1), α x = conjSign hK v x := by
      intro x
      refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
      rw [coe_coe_conjSign_apply, hmat x, hrefl, hconj, hvG i, hvG j, mul_inv, hs]
      have hG0 := hd0 0
      field_simp
    exact ⟨v 2, fun x => by rw [← hvw, ← hlift x, hαx]⟩
  ·
    exfalso
    subst hbar
    have hcσ : (unitaryInvolution K p f) c * c = 1 := (mem_normOne _).1 u.2
    have hcσ' : (unitaryInvolution K p f) c = c⁻¹ := eq_inv_of_mul_eq_one_left hcσ
    have hrel : ∀ i j : Fin (2 + 1), G i j ≠ 0 →
        (i.val = (0 : Fin 2).val ∧ j.val = (0 : Fin 2).val + 1) ∨
        (i.val = (0 : Fin 2).val + 1 ∧ j.val = (0 : Fin 2).val) ∨
        (i.val ≠ (0 : Fin 2).val ∧ i.val ≠ (0 : Fin 2).val + 1 ∧ j.val ≠ (0 : Fin 2).val ∧
          j.val ≠ (0 : Fin 2).val + 1) := by
      intro i j hij
      have h1 := hmat (blockEmb2 K p f 2 0 (torusTwo (unitaryInvolution K p f) u))
      rw [hαfix _, coe_coe_blockEmb2_torusTwo] at h1
      have h2' := diagonal_relation (unitaryInvolution K p f) G Gi hGiG _ h1.symm i j
      exact torus_entry_cases (unitaryInvolution K p f) (0 : Fin 2) c hu1 hu2' hcσ' i j (G i j) hij
        (by simpa [hcinv] using h2')
    have row0 : ∀ j : Fin (2 + 1), G 0 j ≠ 0 → j.val = 1 := by
      intro j hj
      rcases hrel 0 j hj with ⟨-, h3⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
      · simpa using h3
      · simp at h3
      · simp at h3
    have row2 : ∀ j : Fin (2 + 1), G 2 j ≠ 0 → j.val = 2 := by
      intro j hj
      rcases hrel 2 j hj with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, -, h3, h4⟩
      · simp at h3
      · simp at h3
      · have := j.isLt
        simp at h3 h4
        omega
    have hW : G 1 0 = -G 0 1 := by
      obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K,
          X = (((blockEmb2 K p f 2 0 (weylElt K p f) : Su K p f (2 + 1)) :
            GL (Fin (2 + 1)) K) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) := ⟨_, rfl⟩
      have h1 := hmat (blockEmb2 K p f 2 0 (weylElt K p f))
      rw [hαfix _, ← hX] at h1
      have hXbar : (unitaryInvolution K p f).mapMatrix X = X := by
        have hW0 : (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map (unitaryInvolution K p f) =
            (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [CFSG.ClassicalInvolution.Phan.weylElt]
        rw [RingEquiv.mapMatrix_apply, hX]
        change (blockMat (2 + 1) 0 (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)).map (unitaryInvolution K p f) =
            blockMat (2 + 1) 0 (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K)
        refine (CFSG.ClassicalInvolution.WeakCT.map_blockMat
          (unitaryInvolution K p f : K →+* K) _).trans ?_
        exact congrArg (blockMat (2 + 1) 0) hW0
      rw [hXbar] at h1
      have h2 : X * G = G * X := by
        have : G * X = X * G := by
          simpa [Matrix.mul_assoc, hGiG] using congrArg (· * G) h1.symm
        exact this.symm
      have h3 := congrFun (congrFun h2 0) 0
      have e1 : (X * G) 0 0 = G 1 0 := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin (2 + 1))]
        · rw [hX, coe_coe_blockEmb2_weylElt_row 2 0 0 1 rfl]
          simp
        · intro k _ hk
          rw [hX, coe_coe_blockEmb2_weylElt_row 2 0 0 k rfl,
            ite_eq_right (fun h => hk (Fin.ext (by simpa using h))), zero_mul]
        · simp
      have e2 : (G * X) 0 0 = -G 0 1 := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin (2 + 1))]
        · rw [hX, coe_coe_blockEmb2_weylElt_col 2 0 1 0 rfl]
          simp
        · intro k _ hk
          rw [hX, coe_coe_blockEmb2_weylElt_col 2 0 k 0 rfl,
            ite_eq_right (fun h => hk (Fin.ext (by simpa using h))), mul_zero]
        · simp
      rw [← e1, h3, e2]
    obtain ⟨c', hc'⟩ : ∃ c' : K, G * (unitaryInvolution K p f).mapMatrix G =
        c' • (1 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) := by
      refine eq_smul_one_of_commute h hp2 (by omega)
        (G * (unitaryInvolution K p f).mapMatrix G) fun y hy => ?_
      have hy' : y ∈ SUid (unitaryInvolution K p f) (2 + 1) := by
        rw [SUid_eq_statedSU hK]
        exact hy
      have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
      have h2' := congrArg (fun x : Su K p f (2 + 1) =>
        ((x : GL (Fin (2 + 1)) K) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K)) h1
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2'
      rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2'
      exact commute_of_double_conj (unitaryInvolution K p f) (unitaryInvolution_involutive hK) G Gi
        (y : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) hGiG h2'.symm
    have hGbi : (unitaryInvolution K p f).mapMatrix G *
        (unitaryInvolution K p f).mapMatrix Gi = 1 := by
      rw [← map_mul, hGGi, map_one]
    have h4 : Gᵀ * (unitaryInvolution K p f).mapMatrix G = 1 := by
      have := congrArg Matrix.transpose hiso
      rw [transpose_mul, transpose_transpose, transpose_one] at this
      exact this
    have hGT : G = c' • Gᵀ := by
      have h5 : (G - c' • Gᵀ) * (unitaryInvolution K p f).mapMatrix G = 0 := by
        rw [Matrix.sub_mul, hc', Matrix.smul_mul, h4, sub_self]
      have h6 := congrArg (· * (unitaryInvolution K p f).mapMatrix Gi) h5
      simp only [Matrix.mul_assoc, hGbi, Matrix.mul_one, Matrix.zero_mul] at h6
      exact sub_eq_zero.mp h6
    have hGT' : ∀ i j, G i j = c' * G j i := fun i j => by
      have := congrFun (congrFun hGT i) j
      simpa using this
    have hne01 : G 0 1 ≠ 0 := by
      intro h0
      apply hdet
      refine Matrix.det_eq_zero_of_row_eq_zero (0 : Fin (2 + 1)) fun j => ?_
      by_contra hj
      have hj1 : j = 1 := Fin.ext (row0 j hj)
      rw [hj1] at hj
      exact hj h0
    have hc1 : c' = -1 := by
      have h5 := hGT' 0 1
      rw [hW] at h5
      have h6 : G 0 1 * (1 + c') = 0 := by linear_combination h5
      have h7 := (mul_eq_zero.mp h6).resolve_left hne01
      linear_combination h7
    have h22 : G 2 2 = 0 := by
      have h5 := hGT' 2 2
      rw [hc1] at h5
      have h6 : (2 : K) * G 2 2 = 0 := by linear_combination h5
      exact (mul_eq_zero.mp h6).resolve_left h2
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero (2 : Fin (2 + 1)) fun j => ?_
    by_contra hj
    have hj2 : j = 2 := Fin.ext (row2 j hj)
    rw [hj2] at hj
    exact hj h22


end InnerDiag

section Nodes

theorem LcU_node_sup_eq_top3 :
    LcU (GaloisField 3 2) 3 1 (nodePair 2 0 (by omega)) ⊔
      LcU (GaloisField 3 2) 3 1 (nodePair 2 1 (by omega)) = ⊤ := by
  have h2 := two_ne_zero_gf9
  rw [← range_blockEmb2_eq_LcU_nodePair h2 (m := 2) (a := 0) (by omega),
    ← range_blockEmb2_eq_LcU_nodePair h2 (m := 2) (a := 1) (by omega)]
  have htop := iSup_range_blockEmb2 card_gf9 (by norm_num : 3 ^ 1 ≠ 2) 2
  refine eq_top_iff.mpr ?_
  rw [← htop]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

end Nodes

end CFSG.ClassicalInvolution.Q3.Q3W
