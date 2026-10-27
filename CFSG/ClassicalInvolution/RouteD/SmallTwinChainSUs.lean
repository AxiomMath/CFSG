module

public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainAssembly
public import CFSG.ClassicalInvolution.RouteD.SmallTwinSUs
public import CFSG.ClassicalInvolution.RouteD.TypeUChain
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalInvolution.Generic.CoreAssembly

section InnerDiag

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def twoOneSigns (w : ZMod 2) (i : Fin (2 + 1)) : ZMod 2 := if i.val = 2 then w else 0

theorem innerDiag_three_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Y : Type} [Group Y] (θ : Su K p f (2 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (2 + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f 2 0 A)) = θ (blockEmb2 K p f 2 0 A)) :
    ∃ w : ZMod 2, ∀ x, σ (θ x) = θ (conjSign hK (twoOneSigns w) x) := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have := isPerfect_suTwo_of_card hK hq
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    unitaryAutClassification_ambient hK hp2 hq (by omega : 3 ≤ 2 + 1) θ hker σ hσ hstab
  have hαfix : ∀ A : Su K p f 2, α (blockEmb2 K p f 2 0 A) = blockEmb2 K p f 2 0 A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb2 K p f 2 0) hfix) A
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

section Partner

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_partner_two_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {R : Subgroup (Su K p f (2 + 1))} {i : Su K p f (2 + 1)}
    (h : IsLongRootSU2 K p f (by omega : 2 ≤ 2 + 1) R i) :
    ∃ (R' : Subgroup (Su K p f (2 + 1))) (i' : Su K p f (2 + 1)),
      IsLongRootSU2 K p f (by omega : 2 ≤ 2 + 1) R' i' ∧ Commute i i' ∧ i ≠ i' ∧
      ¬ Commutes R R' := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨g, hR, hi⟩ := h
  let T₀ : Pair (2 + 1) := nodePair 2 0 (by omega)
  let T₁ : Pair (2 + 1) := nodePair 2 1 (by omega)
  have hn : (2 : ℕ) ≤ 2 + 1 := by omega
  have hroot : rootSU2 K p f hn = LcU K p f T₀ := by
    rw [rootSU2_eq_longRootGroupSU h2, negBlock_eq_zMat (by omega : 0 + 2 ≤ 2 + 1)]
    rfl
  have hinv : rootInvSU K p f hn = zEltU K p f T₀ :=
    suMat_injective (by
      rw [suMat_rootInvSU, suMat_zEltU, negBlock_eq_zMat (by omega : 0 + 2 ≤ 2 + 1)]
      rfl)
  have hc : zEltU K p f T₀ * zEltU K p f T₁ = zEltU K p f T₁ * zEltU K p f T₀ :=
    signGroupU_comm (zEltU_mem_signGroupU T₀) (zEltU_mem_signGroupU T₁)
  have hT : T₀ ≠ T₁ := by
    intro h'
    have := (nodePair_eq_iff (m := 2) (a := 0) (b := 1) (by omega) (by omega)).mp h'
    omega
  refine ⟨(LcU K p f T₁).map (MulAut.conj g).toMonoidHom, g * zEltU K p f T₁ * g⁻¹,
    (isLongRootSU2_LcU h2 hn T₁).conj g, ?_, ?_, ?_⟩
  · rw [hi, hinv]
    show g * zEltU K p f T₀ * g⁻¹ * (g * zEltU K p f T₁ * g⁻¹) =
      g * zEltU K p f T₁ * g⁻¹ * (g * zEltU K p f T₀ * g⁻¹)
    calc g * zEltU K p f T₀ * g⁻¹ * (g * zEltU K p f T₁ * g⁻¹)
        = g * (zEltU K p f T₀ * zEltU K p f T₁) * g⁻¹ := by group
      _ = g * (zEltU K p f T₁ * zEltU K p f T₀) * g⁻¹ := by rw [hc]
      _ = g * zEltU K p f T₁ * g⁻¹ * (g * zEltU K p f T₀ * g⁻¹) := by group
  · intro h'
    rw [hi, hinv] at h'
    have h3 : zEltU K p f T₀ = zEltU K p f T₁ := by
      have := congrArg (fun y => g⁻¹ * y * g) h'
      simpa [mul_assoc] using this
    exact hT (typeU_zEltU_injective h2 h3)
  · rw [hR, hroot]
    intro hcm
    have h4 : Commutes (LcU K p f T₀) (LcU K p f T₁) := (commutes_conjSub_iff g).mp hcm
    exact not_commutes_LcU_overlap hK hp2 (by omega : 3 ≤ 2 + 1) (i := ⟨0, by omega⟩)
      (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (by simp) (by simp) (by simp) h4

theorem LcU_node_sup_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    LcU K p f (nodePair 2 0 (by omega)) ⊔ LcU K p f (nodePair 2 1 (by omega)) = ⊤ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have e₀ : (embSUid (unitaryInvolution K p f) 2).range = LcU K p f (nodePair 2 0 (by omega)) := by
    rw [embSUid_two_eq_blockEmb]
    exact range_blockEmb_two_eq_LcU h2 (by omega) rfl
  have e₁ : (embSUid (unitaryInvolution K p f) 0).range = LcU K p f (nodePair 2 1 (by omega)) := by
    rw [embSUid_zero_eq_blockEmb]
    exact range_blockEmb_two_eq_LcU h2 (by omega) rfl
  rw [← e₀, ← e₁]
  exact B12_sup_B23 hK (by omega)

end Partner

section Layer

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem UCtx.conjSub_eq_of_commute_roots (c : UCtx p f m Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    {i i' : Su (GaloisField p (2 * f)) p f (m + 1)}
    (hRi : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R i)
    (hRi' : IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ)
    (hcomm : Commute i i') {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    conjSub w L' = L' := by
  have hwY : w ∈ locLayer Ω z := le_centralizingLayer hL hw
  have hψi : c.d.ψ i = locMk Ω z ⟨w, hwY⟩ :=
    psiU_root_inv c.hp2 c.hq c.hm c.d hRi hLR (le_centralizingLayer hL) hw hw2
  have hle : conjSub i R' ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hRi'.eq_longRootGroupSU c.h2] at hy ⊢
    exact conj_mem_longRootGroupSU_of_commute (typeU_suMat_commute hcomm) hy
  have hnormR : conjSub i R' = R' := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj i).injective]
  have himg : locImg Ω z (conjSub w L') = locImg Ω z L' := by
    have h := locImg_conjSub_layer (Ω := Ω) (x := z) L' ⟨w, hwY⟩
    rw [show ((⟨w, hwY⟩ : ↥(locLayer Ω z)) : G) = w from rfl] at h
    rw [h, hLR', ← hψi]
    have h' := map_conjSub_hom c.d.ψ i R'
    rw [hnormR] at h'
    exact h'.symm
  have hmem : conjSub w L' ∈ centralizingMembers Ω {z} := by
    refine ⟨c.hΩ.conjInvariant w L' hL'.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hL'.2 ha
    have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := hL.2 hw
    have : a = w * (w⁻¹ * a * w) * w⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hwC hx') (inv_mem hwC)
  exact locImg_injOn c.hΩ c.hP1 hmem hL' himg

end Layer

section Dichotomy

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjSign_twoOneSigns_zero (hK : Nat.card K = (p ^ f) ^ 2) (x : Su K p f (2 + 1)) :
    conjSign hK (twoOneSigns 0) x = x := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [coe_coe_conjSign_apply]
  simp [twoOneSigns, signVal]

theorem conjSign_twoOneSigns_one (hK : Nat.card K = (p ^ f) ^ 2) (x : Su K p f (2 + 1)) :
    conjSign hK (twoOneSigns 1)
      (rootInvSU K p f (by omega : 2 ≤ 2 + 1) * x *
        (rootInvSU K p f (by omega : 2 ≤ 2 + 1))⁻¹) = x := by
  have hrr : rootInvSU K p f (by omega : 2 ≤ 2 + 1) * rootInvSU K p f (by omega : 2 ≤ 2 + 1) =
      1 := suMat_injective (by
    rw [suMat_mul, suMat_rootInvSU, negBlock_mul_self]
    rfl)
  have hr : (rootInvSU K p f (by omega : 2 ≤ 2 + 1))⁻¹ =
      rootInvSU K p f (by omega : 2 ≤ 2 + 1) := inv_eq_of_mul_eq_one_right hrr
  rw [hr]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [coe_coe_conjSign_apply]
  change _ * suMat (rootInvSU K p f (by omega : 2 ≤ 2 + 1) * x *
    rootInvSU K p f (by omega : 2 ≤ 2 + 1)) i j * _ = _
  rw [suMat_mul, suMat_mul, suMat_rootInvSU, negBlock_eq_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [twoOneSigns, signVal, suMat]

end Dichotomy

section LayerDich

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem UCtx.layer_dichotomy {J : Subgroup G} {w : G} (c : UCtx p f 2 Ω J w) {K : Subgroup G}
    {z : G} (hK : K ∈ centralizingMembers Ω {w}) (hKJ : K ≠ J) (hz : IsClassicalMember p f K z)
    {t : G} (ht1 : t * w * t⁻¹ = w) (ht2 : t * t = 1)
    (htK : K ≤ Subgroup.centralizer ({t} : Set G)) (htJ : conjSub t J = J) :
    (∀ N ∈ centralizingMembers Ω {w}, N ≠ J → N ≤ Subgroup.centralizer ({t} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {w}, N ≠ J →
        N ≤ Subgroup.centralizer ({t * z} : Set G)) := by
  obtain ⟨R, i, hRi, hKR, hψi⟩ := c.exists_rootData hK hKJ hz
  obtain ⟨g, hRg, hig⟩ := hRi
  let θ : Su (GaloisField p (2 * f)) p f (2 + 1) →* locQuot Ω w :=
    c.d.ψ.comp (MulAut.conj g).toMonoidHom
  have hθx : ∀ x, θ x = c.d.ψ (g * x * g⁻¹) := fun x => rfl
  have hθker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f (2 + 1)) := by
    intro x hx
    have hc := c.d.ker_le (show g * x * g⁻¹ ∈ c.d.ψ.ker from hx)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have h1 := hc (g * y * g⁻¹)
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (x * y) * g⁻¹ := by group
    have := congrArg (fun u => g⁻¹ * u * g) h2
    simpa [mul_assoc] using this
  have hψθ : ∀ r, c.d.ψ r ∈ θ.range := fun r =>
    ⟨g⁻¹ * r * g, by rw [hθx]; congr 1; group⟩
  let σ := locAut c.hΩ.conjInvariant ht1
  have hσσ : ∀ a, σ (σ a) = a := locAut_locAut c.hΩ.conjInvariant ht1 ht2
  have hlayerσ : ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → ∀ a ∈ locImg Ω w N,
      σ a ∈ c.d.ψ.range := by
    intro N hN hNJ a ha
    have h1 : σ a ∈ locImg Ω w (conjSub t N) := by
      rw [← locAut_locImg c.hΩ.conjInvariant ht1 N]
      exact ⟨a, ha, rfl⟩
    have hN' : conjSub t N ∈ centralizingMembers Ω {w} := by
      have : conjSub t N ∈ centralizingMembers Ω {t * w * t⁻¹} := by
        rw [centralizingMembers_conj c.hΩ.conjInvariant]
        exact ⟨N, hN, rfl⟩
      rwa [ht1] at this
    have hN'J : conjSub t N ≠ J := by
      intro h
      apply hNJ
      apply conjSub_injective t
      rw [h, htJ]
    obtain ⟨zN, hzN⟩ := c.hΩ.classical _ hN'.1
    obtain ⟨R'', i'', -, hR'', -⟩ := c.exists_rootData hN' hN'J hzN
    rw [hR''] at h1
    obtain ⟨r, -, hr⟩ := h1
    exact ⟨r, hr⟩
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hstabψ : ∀ x, σ (c.d.ψ x) ∈ c.d.ψ.range := by
    have hsub : ∀ (a : ℕ) (ha : a < 2), LcU (GaloisField p (2 * f)) p f (nodePair 2 a ha) ≤
        c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) := by
      intro a ha y hy
      exact hlayerσ (nd.j a) (nd.mem a ha) (nd.ne_K a ha) _
        (by rw [nd.img a ha]; exact ⟨y, hy, rfl⟩)
    have htop : c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) = ⊤ := by
      rw [eq_top_iff, ← LcU_node_sup_eq_top c.card_eq c.hp2 c.hq]
      exact sup_le (hsub 0 (by omega)) (hsub 1 (by omega))
    intro x
    have : x ∈ c.d.ψ.range.comap (σ.toMonoidHom.comp c.d.ψ) := by rw [htop]; trivial
    exact this
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x => by
    obtain ⟨r, hr⟩ := hstabψ (g * x * g⁻¹)
    rw [hθx, ← hr]
    exact hψθ r
  have hfix : ∀ A : Su (GaloisField p (2 * f)) p f 2,
      σ (θ (blockEmb2 (GaloisField p (2 * f)) p f 2 0 A)) =
        θ (blockEmb2 (GaloisField p (2 * f)) p f 2 0 A) := by
    intro A
    have hmem : θ (blockEmb2 (GaloisField p (2 * f)) p f 2 0 A) ∈ locImg Ω w K := by
      rw [hKR]
      refine ⟨g * blockEmb2 (GaloisField p (2 * f)) p f 2 0 A * g⁻¹, ?_, rfl⟩
      rw [hRg]
      exact ⟨blockEmb2 (GaloisField p (2 * f)) p f 2 0 A, ⟨A, rfl⟩, rfl⟩
    exact ((locAut_fixed_iff c.hΩ c.hP1 ht1 hK).mp htK) _ hmem
  obtain ⟨ε, hσθ⟩ := innerDiag_three_su c.card_eq c.hp2 c.hq θ hθker σ hσσ hstab hfix
  have hlocal : ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → ∀ a ∈ locImg Ω w N,
      ∃ x, a = θ x := by
    intro N hN hNJ a ha
    obtain ⟨zN, hzN⟩ := c.hΩ.classical N hN.1
    obtain ⟨R', i', -, hR', -⟩ := c.exists_rootData hN hNJ hzN
    rw [hR'] at ha
    obtain ⟨r, -, rfl⟩ := ha
    obtain ⟨x, hx⟩ := hψθ r
    exact ⟨x, hx.symm⟩
  have hε : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases hε ε with rfl | rfl
  · left
    intro N hN hNJ
    refine (locAut_fixed_iff c.hΩ c.hP1 ht1 hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    exact (hσθ x).trans (by rw [conjSign_twoOneSigns_zero])
  · right
    intro N hN hNJ
    have hzY : z ∈ locLayer Ω w := le_centralizingLayer hK hz.mem
    have hzw : z * w * z⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hK.2 hz.mem)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have htz : (t * z) * w * (t * z)⁻¹ = w := by
      calc (t * z) * w * (t * z)⁻¹ = t * (z * w * z⁻¹) * t⁻¹ := by group
        _ = w := by rw [hzw, ht1]
    refine (locAut_fixed_iff c.hΩ c.hP1 htz hN).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
    rw [locAut_mul c.hΩ.conjInvariant ht1 hzw htz, locAut_eq_conj c.hΩ.conjInvariant hzY hzw]
    have hzbar : locMk Ω w ⟨z, hzY⟩ = θ (rootInvSU (GaloisField p (2 * f)) p f c.hn) := by
      rw [hθx]
      have : g * rootInvSU (GaloisField p (2 * f)) p f c.hn * g⁻¹ = i := by rw [hig]
      rw [this]
      exact hψi.symm
    rw [hzbar, ← map_inv, ← map_mul, ← map_mul]
    show σ (θ _) = _
    rw [hσθ, conjSign_twoOneSigns_one]

end LayerDich

section Final

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem localShapeT_of_shapeU {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeU p f 2 Ω x) :
    LocalShapeT p f 1 .PSU 3 Ω x := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  refine ⟨D, by omega, i₁, ht₁, hr₁, fun i hi => ?_⟩
  have hi' : i = i₀ := by
    have h1 := i.isLt
    have h2 := i₀.isLt
    have h3 := i₁.isLt
    have h4 : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have h5 : i.val ≠ i₁.val := fun e => hi (Fin.ext e)
    exact Fin.ext (by omega)
  rw [hi']
  exact ⟨ht₀, hr₀⟩

theorem exists_uctx_member (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeU p f 2 Ω z) {J : Subgroup G} {w : G} (hJ : J ∈ Ω)
    (hw : IsClassicalMember p f J w) : Nonempty (UCtx p f 2 Ω J w) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  obtain ⟨g, hg⟩ := hsingle J hJ
  have hw' : w = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex J hJ) hw (hg ▸ hz.conj g)
  subst hw'
  have hshape' : LocalShapeU p f 2 Ω (g * z * g⁻¹) :=
    (LocalShapeT.conj hΩ.conjInvariant g (localShapeT_of_shapeU hshape)).exists_two_components
  have hP1' : LocalOddCentral Ω {g * z * g⁻¹} := localOddCentral_conj hΩ.conjInvariant g z hP1
  obtain ⟨d⟩ := LocalShapeU.nonempty_dict hp2 (m := 2) (by omega) hΩ hJ hw hshape'
  exact ⟨{ hm := le_rfl
           hp2 := hp2
           hq := hq
           hΩ := hΩ
           hex := hex
           hK := hJ
           hz := hw
           hP1 := hP1'
           d := d
           hlift := Or.inl (by omega) }⟩

theorem chainPieceSUsTwo_of_twinP1U (hP : TwinP1U p f) : ChainPieceSUsTwo p f := by
  intro G _ _ _ hnab K z S hshape
  have hp2 := S.odd
  have hq := S.five
  have hΩ := S.inClass
  have hex := S.exact
  have hsingle := single_class K
  have hK : K ∈ conjClass K := mem_conjClass_self K
  obtain ⟨c⟩ := exists_uctx_member hp2 hq hΩ hex hsingle S.cls S.p1 hshape hK S.cls
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hj₀z := nd.mem 0 (by omega)
  have hj₁z := nd.mem 1 (by omega)
  have hw₀ := nd.isCl 0 (by omega)
  have hw₁ := nd.isCl 1 (by omega)
  have hKj₀ : Commutes K (nd.j 0) := nd.commK 0 (by omega)
  have hKj₁ : Commutes K (nd.j 1) := nd.commK 1 (by omega)
  have hnc : ¬ Commutes (nd.j 0) (nd.j 1) := nd.adj 0 (by omega)
  have hinj : nd.j 0 ≠ nd.j 1 := nd.inj 0 (by omega) 1 (by omega) (by omega)
  have hlayer : ∀ N ∈ conjClass K, Commutes K N → N ≤ nd.j 0 ⊔ nd.j 1 := by
    intro N hN hKN
    have hNz : N ∈ centralizingMembers (conjClass K) {z} :=
      ⟨hN, NonClassical.le_centralizer_of_commutes hKN.symm S.cls.mem⟩
    have hNK : N ≠ K := fun h => not_commutes_self_of_isClassicalMember S.cls (h ▸ hKN)
    obtain ⟨zN, hzN⟩ := hΩ.classical N hN
    obtain ⟨R, i, hRi, hNR, -⟩ := c.exists_rootData hNz hNK hzN
    refine le_of_locImg_le hΩ c.hP1 hNz (N := nd.j 0 ⊔ nd.j 1) ?_
    rw [hNR, locImg_sup (le_centralizingLayer hj₀z) (le_centralizingLayer hj₁z),
      nd.img 0 (by omega), nd.img 1 (by omega), ← Subgroup.map_sup,
      LcU_node_sup_eq_top c.card_eq c.hp2 c.hq]
    exact Subgroup.map_mono le_top
  have hnorm : conjSub (nd.w 0) (nd.j 1) = nd.j 1 :=
    c.conjSub_eq_of_commute_roots hj₀z hj₁z
      (isLongRootSU2_LcU c.h2 c.hn (nodePair 2 0 (by omega)))
      (isLongRootSU2_LcU c.h2 c.hn (nodePair 2 1 (by omega))) (nd.img 0 (by omega))
      (nd.img 1 (by omega))
      (signGroupU_comm (zEltU_mem_signGroupU _) (zEltU_mem_signGroupU _)) hw₀.mem
      hw₀.orderOf_eq_two
  obtain ⟨c'⟩ := exists_uctx_member hp2 hq hΩ hex hsingle S.cls S.p1 hshape hj₁z.1 hw₁
  have hKw₁ : K ∈ centralizingMembers (conjClass K) {nd.w 1} :=
    ⟨hK, NonClassical.le_centralizer_of_commutes hKj₁ hw₁.mem⟩
  have hKj₁' : K ≠ nd.j 1 := (nd.ne_K 1 (by omega)).symm
  obtain ⟨R, i, hRi, hKR, -⟩ := c'.exists_rootData hKw₁ hKj₁' S.cls
  obtain ⟨R', i', hRi', hcomm', hne', hnc'⟩ := exists_partner_two_su c'.card_eq c'.hp2 hRi
  obtain ⟨β, hβ, hβJ, hβR⟩ := typeU_exists_member_of_root c'.hp2 c'.hq c'.hm c'.hΩ c'.hK c'.hz
    c'.hP1 c'.d (R := R') ⟨i', hRi'⟩
  obtain ⟨v, hv⟩ := hΩ.classical β hβ.1
  have hKβ : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β :=
    c'.stdpair_of_root hKw₁ hβ hRi hRi' hKR hβR hcomm' hne' hnc'
  have hnKβ : ¬ Commutes K β := fun h => hnc' ((c'.commutes_iff_root hKw₁ hβ hRi hKR hβR).mp h)
  have hKβne : K ≠ β := fun h =>
    hne' (c'.rootInv_eq_of_locImg_eq hRi hRi' hKR hβR (congrArg (locImg _ _) h))
  have hvK : conjSub v K = K :=
    c'.conjSub_eq_of_commute_roots hβ hKw₁ hRi' hRi hβR hKR hcomm'.symm hv.mem hv.orderOf_eq_two
  have hP1x := hP G hnab K z S hshape (nd.j 0) hj₀z (nd.ne_K 0 (by omega)) (nd.w 0) hw₀
  obtain ⟨U, hUΩ, hUc, hUp⟩ := exists_twin_chain (PairT := fun A B =>
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W A B) hnab hp2 hq hΩ S.conn hex
    S.ih hsingle hK S.cls
    (fun L hL hLK => typeU_commutes_K_of_ne c.hp2 c.hq c.hm hΩ hex hK S.cls S.p1 c.d hL hLK)
    hj₀z.1 hj₁z.1 hw₀ hw₁ (nd.ne_K 0 (by omega)) hinj hKj₀ hKj₁ hnc
    (nd.wcomm 0 (by omega) 1 (by omega)) hlayer hnorm
    (fun t ht1 ht2 htK htJ => c'.layer_dichotomy hKw₁ hKj₁' S.cls ht1 ht2 htK htJ) hP1x hβ hβJ
    hv hnKβ hKβne hvK hKβ (nd.pair 0 (by omega))
    (fun hKx hβx hMx hs h => unitary_of_chainSign_images hp2 hq hΩ hP1x hKx hβx hMx hs h)
  exact ⟨U, hUΩ, hUc, hUp⟩

end Final

end CFSG.ClassicalInvolution.RouteD
