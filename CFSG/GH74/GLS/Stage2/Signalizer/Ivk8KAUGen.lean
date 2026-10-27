module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAOrth
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphTools

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.Burgoyne.PSL (vecMulVec_mul_self)
open CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

section Comp

theorem ka_all_of_components_fix {G Y : Type} [Group G] [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (π : G →* Y) (hπ : Function.Surjective π) (φ : G →* G) {α : MulAut Y}
    (hφ : ∀ g, α (π g) = π (φ g)) {S : Subgroup G} (hfix0 : ∀ g ∈ S, φ g = g)
    (hnorm : ∀ h : G, π (φ h) = π h → ∀ g ∈ S, h * g * h⁻¹ ∈ S) (hperf : ⁅S, S⁆ = S) {m : ℕ}
    (Fq : Fin m → Subgroup G) (hq : ∀ i, IsQuasisimple (Fq i)) (hle : ∀ i, Fq i ≤ S)
    (hsup : S ≤ ⨆ i, Fq i) (hFn : ∀ i, ∀ h ∈ S, ∀ g ∈ Fq i, h * g * h⁻¹ ∈ Fq i)
    (hfix : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P' : Subgroup (MulAut Y), IsPGroup p ↥P' →
      (∀ e ∈ P', e * α = α * e) → (∀ e ∈ P', ∀ r ∈ S.map π, e r = r) → IsCyclic ↥P')
    (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α :=
  ka_all_of_torus_fix_comm hinj (fixSub α) (S.map π) le_rfl (fun _ hc _ => hc)
    (ka_orth_le_fixSub π φ hφ hfix0) (ka_orth_normalizes π hπ φ hφ hnorm)
    (ka_orth_perfect_map π hperf)
    (fun _ hp _ M hML hMp hMn => ka_orth_central_of_components π Fq hq hle hsup hFn hp M hML hMp
      hMn) hfix hOut

end Comp

section UFix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ka_u_fix_matrix (hn : 1 ≤ n) (D : uU h n) (τ : K ≃+* K) (g : StatedSU n (p ^ f) K)
    (hg : (uConjAut h hn D * uFieldAut h hn τ) (projH (StatedSU n (p ^ f) K) g) =
      projH (StatedSU n (p ^ f) K) g) :
    ∃ μ : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      μ • (((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ *
        (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rw [uLift_proj h hn D τ g] at hg
  have hz := projH_eq_projH_iff.1 hg
  rw [mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have hgu : (g : GL (Fin n) K) = ((uLift h D τ g : StatedSU n (p ^ f) K) : GL (Fin n) K) *
      GeneralLinearGroup.scalar (Fin n) c := by
    have h1 : ((uLift h D τ g : StatedSU n (p ^ f) K) : GL (Fin n) K)⁻¹ * (g : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hc.symm
    rw [← h1]
    group
  refine ⟨(c : K), ?_⟩
  have h2 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hgu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h2
  have h3 := coe_uLift h D τ g
  calc ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((uLift h D τ g : StatedSU n (p ^ f) K) : GL (Fin n) K) * Matrix.scalar (Fin n) (c : K) :=
        h2
    _ = (c : K) • ((uLift h D τ g : StatedSU n (p ^ f) K) : GL (Fin n) K) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    _ = _ := by rw [h3]

theorem ka_u_sigma_fix (hn : 1 ≤ n) (D : uU h n) (τ : K ≃+* K) {v : Fin n → K}
    (hv : (fun k => h.bar (v k)) ⬝ᵥ v = 0) {η : K} (hη : h.bar η = -η) {a b : Fin n}
    (hab : (η • vecMulVec v (fun k => h.bar (v k))) a b ≠ 0)
    (hfix : ∀ g : StatedSU n (p ^ f) K, ∀ c : K, h.bar c = c →
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + c • (η • vecMulVec v (fun k => h.bar (v k))) →
      (uConjAut h hn D * uFieldAut h hn τ) (projH (StatedSU n (p ^ f) K) g) =
        projH (StatedSU n (p ^ f) K) g) :
    ∀ c, h.bar c = c → τ c = c := by
  set N : Matrix (Fin n) (Fin n) K := η • vecMulVec v (fun k => h.bar (v k)) with hN
  have hN0 : N ≠ 0 := fun e => hab (by rw [e]; rfl)
  have hVV : vecMulVec v (fun k => h.bar (v k)) * vecMulVec v (fun k => h.bar (v k)) = 0 :=
    vecMulVec_mul_self hv
  have hN2 : N * N = 0 := by
    rw [hN, Matrix.smul_mul, Matrix.mul_smul, hVV, smul_zero, smul_zero]
  have hDDi : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiD : (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hNt2 := ka_proj_conj_map_sq ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) hDiD τ N hN2
  refine fix_of_conj_family h (D := (D : GL (Fin n) K)) (τ := τ) (N := N) hab fun c hc => ?_
  obtain ⟨g, hg⟩ := exists_uTr h hv (η := c * η) (by rw [map_mul, hc, hη]; ring)
  have hgN : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + c • N := by
    rw [hg, hN, smul_smul]
  obtain ⟨μ, hμ⟩ := ka_u_fix_matrix h hn D τ g (hfix g c hc hgN)
  rw [hgN, ka_proj_conj_root _ _ hDDi τ N c] at hμ
  have hμ1 : μ = 1 := ka_proj_scalar_eq_one N _ hN0 hN2 hNt2 c (τ c) μ hμ
  rw [hμ1, one_smul] at hμ
  rw [ka_proj_conj_root _ _ hDDi τ N c]
  exact hμ.symm

end UFix

section UOut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ka_uConjAut_inner_of_det (hn : 1 ≤ n) (M : uU h n) (μ : Kˣ)
    (hμ : h.norm (μ : K) = 1)
    (hdet : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = (μ : K) ^ n) :
    uConjAut h hn M ∈ innSub (StatedProj (StatedSU n (p ^ f) K)) := by
  set Mm := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMm
  have hU : (Mm.map h.bar)ᵀ * Mm = 1 := (mem_uU h).1 M.2
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hdetG : ((μ : K)⁻¹ • Mm).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hdet, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
  have hNi : h.bar (μ : K)⁻¹ * (μ : K)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hμ, inv_one]
  have hUG : (((μ : K)⁻¹ • Mm).map h.bar)ᵀ * ((μ : K)⁻¹ • Mm) = 1 := by
    rw [show ((μ : K)⁻¹ • Mm).map h.bar = h.bar (μ : K)⁻¹ • Mm.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
  set g₀ : StatedSU n (p ^ f) K := uSUmk h _ hdetG hUG with hg₀
  have hg₀GL : (g₀ : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (M : GL (Fin n) K) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hg₀, coe_uSUmk, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rw [Units.val_inv_eq_inv_val]
  refine ⟨projH (StatedSU n (p ^ f) K) g₀, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := projH_surjective x
  rw [uConjAut_proj]
  rw [MonoidHom.coe_mk, OneHom.coe_mk]
  show projH _ g₀ * projH _ g * (projH _ g₀)⁻¹ = projH _ _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (g₀ : GL (Fin n) K) * (g : GL (Fin n) K) * (g₀ : GL (Fin n) K)⁻¹ =
    (M : GL (Fin n) K) * (g : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹
  have hs := GeneralLinearGroup.scalar_commute μ⁻¹
    ((M : GL (Fin n) K) * (g : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹)
  rw [hg₀GL]
  calc GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (M : GL (Fin n) K) * (g : GL (Fin n) K) *
        (GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (M : GL (Fin n) K))⁻¹ =
      (GeneralLinearGroup.scalar (Fin n) μ⁻¹ * ((M : GL (Fin n) K) * (g : GL (Fin n) K) *
        (M : GL (Fin n) K)⁻¹)) * (GeneralLinearGroup.scalar (Fin n) μ⁻¹)⁻¹ := by group
    _ = _ := by rw [hs, mul_inv_cancel_right]


theorem ka_outCentral_pu (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) {A : uU h n} {l : K}
    (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1)
    (hN : h.norm l = 1 ∨ h.norm l = -1)
    (x : MulAut (StatedProj (StatedSU n (p ^ f) K))) :
    ⁅x, uConjAut h (by omega) A⁆ ∈ innSub (StatedProj (StatedSU n (p ^ f) K)) := by
  obtain ⟨B, σ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq x
  have hM : ⁅uConjAut h (by omega) B * uFieldAut h (by omega) σ, uConjAut h (by omega) A⁆ =
      uConjAut h (by omega) (B * uGlAut h σ A * B⁻¹ * A⁻¹) := by
    have e := uFieldAut_mul_uConjAut h (by omega : 1 ≤ n) σ A
    have e' : uFieldAut h (by omega : 1 ≤ n) σ * uConjAut h (by omega) A *
        (uFieldAut h (by omega : 1 ≤ n) σ)⁻¹ = uConjAut h (by omega) (uGlAut h σ A) := by
      rw [e, mul_inv_cancel_right]
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← e']
    group
  rw [hM]
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hdsq : Am.det * Am.det = (l ^ n) * (l ^ n) := by
    have := congrArg Matrix.det hAA
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at this
    rw [this]
    ring
  have hdet : Am.det = l ^ n ∨ Am.det = -l ^ n := by
    rcases mul_self_eq_mul_self_iff.1 hdsq with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hNl : h.norm l ≠ 0 :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.norm_ne_zero_of_ne_zero h hl0
  have hσN : h.norm (σ l * l⁻¹) = 1 := by
    have h1 : h.norm (σ l) = h.norm l := by
      rw [UnitaryFieldData.norm, UnitaryFieldData.norm, ← map_bar h σ, ← map_mul]
      rcases hN with e | e <;> (rw [UnitaryFieldData.norm] at e; rw [e]; simp)
    have h2 : h.norm l⁻¹ = (h.norm l)⁻¹ := by
      rw [UnitaryFieldData.norm, UnitaryFieldData.norm, map_inv₀, ← mul_inv]
    rw [CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h, h1, h2, mul_inv_cancel₀ hNl]
  have hσl0 : σ l * l⁻¹ ≠ 0 := mul_ne_zero ((map_ne_zero σ).2 hl0) (inv_ne_zero hl0)
  refine ka_uConjAut_inner_of_det h (by omega) _ (Units.mk0 (σ l * l⁻¹) hσl0) hσN ?_
  rw [Units.val_mk0]
  set M : uU h n := B * uGlAut h σ A * B⁻¹ * A⁻¹ with hMdef
  have hMGL : ((M : uU h n) : GL (Fin n) K) = (B : GL (Fin n) K) *
      (uGlAut h σ A : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ * (A : GL (Fin n) K)⁻¹ := by
    simp [hMdef]
  have hdetU : GeneralLinearGroup.det ((M : uU h n) : GL (Fin n) K) =
      GeneralLinearGroup.det (uGlAut h σ A : GL (Fin n) K) *
        (GeneralLinearGroup.det (A : GL (Fin n) K))⁻¹ := by
    rw [hMGL, map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm
      (GeneralLinearGroup.det (B : GL (Fin n) K)), mul_inv_cancel, one_mul]
  have hdetK : (((M : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      σ Am.det * Am.det⁻¹ := by
    have := congrArg (fun u : Kˣ => (u : K)) hdetU
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_inv_eq_inv_val]
      at this
    rw [this, coe_uGlAut, ← hAm]
    have e := RingHom.map_det σ.toRingHom Am
    rw [RingHom.mapMatrix_apply] at e
    exact congrArg (· * Am.det⁻¹) e.symm
  rw [hdetK]
  rcases hdet with e | e
  · rw [e, map_pow, mul_pow, inv_pow, ← inv_pow]
  · rw [e, map_neg, map_pow, mul_pow, inv_pow]
    simp [mul_comm]

end UOut

section UCenter

variable {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime] {n : ℕ}

theorem ka_center_bot_pu (hK : Nat.card K = (p ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) :
    Subgroup.center (StatedProj (StatedSU n (p ^ f) K)) = ⊥ := by
  obtain ⟨-, -, hs⟩ := fam_unitary_projective_simple K p f hK n hn hnq
  have hperfS := isPerfect_statedSU hK hn hnq
  have hperf : Group.IsPerfect (StatedProj (StatedSU n (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : StatedProj (StatedSU n (p ^ f) K), a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    have : Group.IsPerfect (StatedProj (StatedSU n (p ^ f) K)) := hperf
    have : Nontrivial (StatedProj (StatedSU n (p ^ f) K)) := hs.toNontrivial
    have : IsMulCommutative (StatedProj (StatedSU n (p ^ f) K)) := ⟨⟨hcomm⟩⟩
    exact Group.IsPerfect.not_isSolvable (StatedProj (StatedSU n (p ^ f) K))
      (inferInstance : Group.IsSolvable (StatedProj (StatedSU n (p ^ f) K)))

theorem ka_conj_inj_of_center_bot {Y : Type} [Group Y] (hc : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro y z hyz
  have hz : z⁻¹ * y ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : y * g * y⁻¹ = z * g * z⁻¹ := by
      have := congrArg (fun φ : MulAut Y => φ g) hyz
      simpa [MulAut.conj_apply] using this
    calc g * (z⁻¹ * y) = z⁻¹ * (z * g * z⁻¹) * y := by group
      _ = z⁻¹ * (y * g * y⁻¹) * y := by rw [h1]
      _ = z⁻¹ * y * g := by group
  rw [hc, Subgroup.mem_bot] at hz
  calc y = z * (z⁻¹ * y) := by group
    _ = z := by rw [hz, mul_one]

theorem ka_conj_inj_pu (hK : Nat.card K = (p ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) :
    Function.Injective
      (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
        MulAut (StatedProj (StatedSU n (p ^ f) K))) :=
  ka_conj_inj_of_center_bot (ka_center_bot_pu hK hn hnq)

end UCenter

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
