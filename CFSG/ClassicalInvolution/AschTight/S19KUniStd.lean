module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.ClassicalInvolution.Phan.AutSU2
public import CFSG.ClassicalInvolution.AschTight.S19KMat
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem coe_blockEmb3 (A : Phan.Su K p f 2) :
    (((Phan.blockEmb K p f 3 2 0 (by norm_num) A : Phan.Su K p f 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      !![((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0,
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1, 0;
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0,
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1, 0; 0, 0, 1] := by
  rw [Phan.coe_coe_blockEmb]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Phan.blockMat_apply]

theorem trace_blockEmb3 (A : Phan.Su K p f 2) :
    (((Phan.blockEmb K p f 3 2 0 (by norm_num) A : Phan.Su K p f 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).trace =
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace + 1 := by
  rw [coe_blockEmb3, Matrix.trace_fin_three, Matrix.trace_fin_two]
  simp

theorem exists_su2Equiv (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ e₀ : SL(2, fixedSubfield K p f) ≃* Phan.Su K p f 2, ∀ A : SL(2, fixedSubfield K p f),
      (((e₀ A : Phan.Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
        (((A : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)).trace : fixedSubfield K p f) : K) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  refine ⟨(hypEquiv hζ0 hζ).trans (conjEquiv P hP), fun A => ?_⟩
  rw [MulEquiv.trans_apply, coe_conjEquiv, Units.val_mul, Units.val_mul, Matrix.trace_units_conj,
    hypEquiv_apply, coe_hypHom, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [hypMat]

variable (K p f) in
noncomputable abbrev rootU : Subgroup (Phan.Su K p f 3) :=
  Models.rootSU2 K p f (n := 3) (by norm_num)

theorem exists_stdEquivU (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ ι₀ : rootU K p f ≃* SL(2, fixedSubfield K p f), ∀ r : rootU K p f,
      ((((r : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace =
        ((((ι₀ r : SL(2, fixedSubfield K p f)) : Matrix (Fin 2) (Fin 2) _).trace :
          fixedSubfield K p f) : K) + 1 := by
  obtain ⟨e₀, he₀⟩ := exists_su2Equiv hK
  have hinj := Phan.blockEmb_injective (K := K) (p := p) (f := f) (m := 3) (k := 2) (i := 0)
    (by norm_num)
  refine ⟨(MonoidHom.ofInjective hinj).symm.trans e₀.symm, fun r => ?_⟩
  set B := (MonoidHom.ofInjective hinj).symm r
  have hr : (r : Phan.Su K p f 3) = Phan.blockEmb K p f 3 2 0 (by norm_num) B := by
    rw [← MonoidHom.ofInjective_apply hinj]
    exact congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply r).symm
  rw [hr, trace_blockEmb3]
  change _ = ((((e₀.symm B : SL(2, fixedSubfield K p f)) : Matrix (Fin 2) (Fin 2) _).trace :
    fixedSubfield K p f) : K) + 1
  rw [← he₀, MulEquiv.apply_symm_apply]

theorem isBlockScalar_of_commute_rootSU2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 2 ≤ p ^ f) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ x ∈ rootU K p f,
      M * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) :
    IsBlockScalar M := by
  have h2 : (2 : K) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := normOne (unitaryInvolution K p f))
  rw [Phan.card_normOne hK] at hu
  have hu2 : ((u : Kˣ) : K) ≠ ((u : Kˣ) : K)⁻¹ := by
    intro h
    have hu0 : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have hsq : ((u : Kˣ) : K) * ((u : Kˣ) : K) = 1 := by
      calc ((u : Kˣ) : K) * ((u : Kˣ) : K) = ((u : Kˣ) : K) * ((u : Kˣ) : K)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hu0
    have h1 : u ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_one, Units.val_one, pow_two]
      exact hsq
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hz := hM _ ⟨Models.negOneSU K p f, rfl⟩
  have hd := hM _ ⟨torusTwo (unitaryInvolution K p f) u, rfl⟩
  have hj := hM _ ⟨Phan.weylElt K p f, rfl⟩
  rw [coe_blockEmb3] at hz hd hj
  refine isBlockScalar_of_commute_unitary h2 hu2 M ?_ ?_ ?_
  · convert hz using 2 <;> simp [Models.negOneSU]
  · convert hd using 2 <;> simp [coe_torusTwo]
  · convert hj using 2 <;> simp [Phan.weylElt]

theorem isBlockScalar_of_mem_centralizerU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 2 ≤ p ^ f) {x : Phan.Su K p f 3}
    (hx : x ∈ Subgroup.centralizer (rootU K p f : Set (Phan.Su K p f 3))) :
    IsBlockScalar (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  refine isBlockScalar_of_commute_rootSU2 hK hp hq fun y hy => ?_
  have h := Subgroup.mem_centralizer_iff.mp hx y hy
  have h' := congrArg (fun z : Phan.Su K p f 3 => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Subgroup.coe_mul, Units.val_mul] at h'
  exact h'.symm

theorem coe_rootInvSU_three :
    (((Models.rootInvSU K p f (n := 3) (by norm_num) : Phan.Su K p f 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [Models.rootInvSU, coe_blockEmb3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Models.negOneSU]

theorem eq_one_of_mem_center_rootSU2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    {x : Phan.Su K p f 3} (hx : x ∈ rootU K p f) (hc : x ∈ Subgroup.center (Phan.Su K p f 3)) :
    x = 1 := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨a, ha⟩ := ModelFacts.UnitaryAut.eq_smul_one_of_commute h hp (le_refl 3)
    (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) fun y hy => by
      have hy' : y ∈ SUid (unitaryInvolution K p f) 3 := by rw [SUid_eq_statedSU hK]; exact hy
      have h1 := Subgroup.mem_center_iff.mp hc ⟨y, hy'⟩
      have h2 := congrArg (fun z : Phan.Su K p f 3 =>
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
      simp only [Subgroup.coe_mul, Units.val_mul] at h2
      exact h2.symm
  obtain ⟨A, rfl⟩ := hx
  have h22 := congrFun (congrFun ha 2) 2
  rw [coe_blockEmb3] at h22
  simp at h22
  apply Subtype.ext
  apply Units.ext
  rw [ha, ← h22, one_smul]
  rfl

theorem ringEquiv_eq_of_fixes (hK : Nat.card K = (p ^ f) ^ 2) (τ : K ≃+* K)
    (hτ : ∀ c : K, unitaryInvolution K p f c = c → τ c = c) :
    τ = RingEquiv.refl K ∨ τ = unitaryInvolution K p f := by
  set σ := unitaryInvolution K p f
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have key : ∀ c : K, τ c = c ∨ τ c = σ c := by
    intro c
    have h1 : (τ c - c) * (τ c - σ c) = 0 := by
      have e1 : σ (c + σ c) = c + σ c := by rw [map_add, hσσ, add_comm]
      have e2 : σ (c * σ c) = c * σ c := by rw [map_mul, hσσ, mul_comm]
      have h2 := hτ _ e1
      have h3 := hτ _ e2
      have h4 : c ^ 2 - (c + σ c) * c + c * σ c = 0 := by ring
      have h5 := congrArg τ h4
      rw [map_add, map_sub, map_mul, map_pow, map_zero, h2, h3] at h5
      linear_combination h5
    rcases mul_eq_zero.mp h1 with h6 | h6
    · exact Or.inl (sub_eq_zero.mp h6)
    · exact Or.inr (sub_eq_zero.mp h6)
  by_contra hcon
  push Not at hcon
  obtain ⟨hc₁, hc₂⟩ := hcon
  obtain ⟨c₁, hc₁⟩ : ∃ c, τ c ≠ c := by
    by_contra h0
    push Not at h0
    exact hc₁ (RingEquiv.ext h0)
  obtain ⟨c₂, hc₂⟩ : ∃ c, τ c ≠ σ c := by
    by_contra h0
    push Not at h0
    exact hc₂ (RingEquiv.ext h0)
  have h1 : τ c₁ = σ c₁ := (key c₁).resolve_left hc₁
  have h2 : τ c₂ = c₂ := (key c₂).resolve_right hc₂
  rcases key (c₁ + c₂) with h3 | h3
  · rw [map_add, h1, h2] at h3
    exact hc₁ (by rw [h1]; exact add_right_cancel h3)
  · rw [map_add, h1, h2, map_add] at h3
    exact hc₂ (by rw [h2]; exact add_left_cancel h3)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
