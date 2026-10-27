module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uGram_one {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

abbrev uU (n : ℕ) : Subgroup (GL (Fin n) K) :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

variable {n : ℕ}

theorem mem_uU {A : GL (Fin n) K} :
    A ∈ uU h n ↔ ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * A = 1 := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]

theorem statedSU_eq_gramSU :
    StatedSU n (p ^ f) K = gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [Units.val_one]
  exact unitarySU_eq_gramSU h n

theorem statedSU_le_uU : StatedSU n (p ^ f) K ≤ uU h n := by
  intro g hg
  rw [statedSU_eq_gramSU h] at hg
  exact hg.1

theorem map_scalars_subgroupCongr (hn : 1 ≤ n) :
    ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)).map
        (MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := n))).toMonoidHom =
      normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n := by
  have e := unitaryScalars_eq h hn
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← e] at hx
    obtain ⟨c, hc, hcn, hx⟩ := hx
    exact ⟨c, hc, hcn, hx⟩
  · rintro ⟨c, hc, hcn, hg⟩
    refine ⟨(MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := n))).symm g, ?_, ?_⟩
    · rw [← e]
      exact ⟨c, hc, hcn, hg⟩
    · exact (MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := n))).apply_symm_apply g

@[expose] def uTransport (hn : 1 ≤ n) :
    StatedProj (StatedSU n (p ^ f) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := n)))
    (map_scalars_subgroupCongr h hn)

theorem uTransport_mk (hn : 1 ≤ n) (g : StatedSU n (p ^ f) K) :
    uTransport h hn (projH _ g) = ((MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := n)) g :
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem uTransport_symm_mk (hn : 1 ≤ n)
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    (uTransport h hn).symm (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      projH _ ((MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := n))).symm g) := by
  apply (uTransport h hn).injective
  rw [MulEquiv.apply_symm_apply, uTransport_mk, MulEquiv.apply_symm_apply]

@[expose] def uConjAut (hn : 1 ≤ n) : uU h n →* MulAut (StatedProj (StatedSU n (p ^ f) K)) :=
  (MulAut.congr (uTransport h hn)).symm.toMonoidHom.comp
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))

@[expose] def uFieldAut (hn : 1 ≤ n) : (K ≃+* K) →* MulAut (StatedProj (StatedSU n (p ^ f) K)) :=
  (MulAut.congr (uTransport h hn)).symm.toMonoidHom.comp (primeFormFieldHom h uGram_one)

theorem uConjSU_mem (A : uU h n) (g : StatedSU n (p ^ f) K) :
    (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ ∈ StatedSU n (p ^ f) K := by
  have hg : (g : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← statedSU_eq_gramSU h]; exact g.2
  have := conj_mem_gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A.2 hg
  rw [← statedSU_eq_gramSU h] at this
  exact this

theorem uConjAut_proj (hn : 1 ≤ n) (A : uU h n) (g : StatedSU n (p ^ f) K) :
    uConjAut h hn A (projH _ g) = projH _ ⟨_, uConjSU_mem h A g⟩ := by
  change (uTransport h hn).symm (primeFormConjAut h _ A (uTransport h hn (projH _ g))) = _
  rw [uTransport_mk, primeFormConjAut_mk, uTransport_symm_mk]
  rfl

include h in
theorem uFieldSU_mem (φ : K ≃+* K) (g : StatedSU n (p ^ f) K) :
    glAut φ (g : GL (Fin n) K) ∈ StatedSU n (p ^ f) K := by
  have hg : (g : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← statedSU_eq_gramSU h]; exact g.2
  have := glAut_mem_gramSU h uGram_one φ hg
  rw [← statedSU_eq_gramSU h] at this
  exact this

theorem uFieldAut_proj (hn : 1 ≤ n) (φ : K ≃+* K) (g : StatedSU n (p ^ f) K) :
    uFieldAut h hn φ (projH _ g) = projH _ ⟨_, uFieldSU_mem h φ g⟩ := by
  change (uTransport h hn).symm (primeFormFieldAut h uGram_one φ (uTransport h hn (projH _ g))) =
    _
  rw [uTransport_mk, primeFormFieldAut_mk, uTransport_symm_mk]
  rfl

section Aut

@[expose] def uFactor (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    MulAut (StatedProj (StatedSU n (p ^ f) K)) →* (K ≃+* K) :=
  (primeFormFieldFactor h uGram_one hn hq).comp
    (MulAut.congr (uTransport h (by omega))).toMonoidHom

theorem uFactor_apply (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) (A : uU h n) (φ : K ≃+* K) :
    uFactor h hn hq (uConjAut h (by omega) A * uFieldAut h (by omega) φ) = φ := by
  change primeFormFieldFactor h uGram_one hn hq (MulAut.congr (uTransport h (by omega))
    ((MulAut.congr (uTransport h (by omega))).symm (primeFormConjHom h _ A) *
      (MulAut.congr (uTransport h (by omega))).symm (primeFormFieldHom h uGram_one φ))) = φ
  rw [← map_mul, MulEquiv.apply_symm_apply]
  exact primeFormFieldFactor_apply h uGram_one hn hq A φ

theorem exists_uConjAut_mul_uFieldAut (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (α : MulAut (StatedProj (StatedSU n (p ^ f) K))) :
    ∃ (A : uU h n) (φ : K ≃+* K), α = uConjAut h (by omega) A * uFieldAut h (by omega) φ := by
  obtain ⟨⟨A, φ⟩, hx⟩ := primeFormPsi_surjective h uGram_one hn hq
    (MulAut.congr (uTransport h (by omega)) α)
  refine ⟨A, φ, ?_⟩
  apply (MulAut.congr (uTransport h (by omega))).injective
  rw [← hx, primeFormPsi_apply, map_mul]
  change _ = MulAut.congr (uTransport h (by omega)) ((MulAut.congr (uTransport h (by omega))).symm
    (primeFormConjHom h _ A)) * MulAut.congr (uTransport h (by omega))
      ((MulAut.congr (uTransport h (by omega))).symm (primeFormFieldHom h uGram_one φ))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem uConjAut_eq_one_iff (hn : 3 ≤ n) (A : uU h n) :
    uConjAut h (by omega) A = 1 ↔
      ∃ c : Kˣ, (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  have key := primeFormPsi_eq_one_iff h uGram_one hn ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  constructor
  · intro h1
    have h2 : primeFormConjHom h _ A = 1 := by
      have := congrArg (MulAut.congr (uTransport h (by omega))) h1
      rw [map_one] at this
      rw [← this]
      exact ((MulAut.congr (uTransport h (by omega))).apply_symm_apply _).symm
    obtain ⟨-, c, -, hc⟩ := key.1 h2
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    have hN : h.norm (c : K) = 1 := by
      have hA := (mem_uU h).1 A.2
      rw [hc, GeneralLinearGroup.coe_scalar] at hA
      have e := congrFun (congrFun hA ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.mul_apply, scalar_apply, diagonal_apply, UnitaryFieldData.norm, mul_comm]
        using e
    have h2 : primeFormConjHom h _ A = 1 := key.2 ⟨rfl, c, hN, hc⟩
    change (MulAut.congr (uTransport h (by omega))).symm (primeFormConjHom h _ A) = 1
    rw [h2, map_one]

theorem uFieldAut_eq_or_of_sq (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) {A : uU h n}
    {φ : K ≃+* K}
    (hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1) :
    φ = 1 ∨ ∀ c, φ c = h.bar c := by
  have h1 := congrArg (uFactor h hn hq) hsq
  rw [map_pow, uFactor_apply, map_one, pow_two] at h1
  exact ringEquiv_eq_refl_or_bar h h1

end Aut

@[expose] def uLift (A : uU h n) (φ : K ≃+* K) : StatedSU n (p ^ f) K →* StatedSU n (p ^ f) K where
  toFun g := ⟨_, uConjSU_mem h A ⟨_, uFieldSU_mem h φ g⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by
    change (A : GL (Fin n) K) * glAut φ ((g : GL (Fin n) K) * (g' : GL (Fin n) K)) *
        (A : GL (Fin n) K)⁻¹ =
      ((A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹) *
        ((A : GL (Fin n) K) * glAut φ (g' : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹)
    rw [map_mul]
    group)

theorem uLift_proj (hn : 1 ≤ n) (A : uU h n) (φ : K ≃+* K) (g : StatedSU n (p ^ f) K) :
    (uConjAut h hn A * uFieldAut h hn φ) (projH _ g) = projH _ (uLift h A φ g) := by
  rw [MulAut.mul_apply, uFieldAut_proj, uConjAut_proj]
  rfl

theorem coe_uLift (A : uU h n) (φ : K ≃+* K) (g : StatedSU n (p ^ f) K) :
    (((uLift h A φ g : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ *
        (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  change ((A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ :
    GL (Fin n) K).val = _
  rw [Units.val_mul, Units.val_mul, coe_glAut]

theorem uSemilinear_eq_of_fix (hn : 1 ≤ n) {A : uU h n} {φ : K ≃+* K}
    {F : Subgroup (StatedSU n (p ^ f) K)} (hF : ⁅F, F⁆ = F)
    (hfix : ∀ g ∈ F, (uConjAut h hn A * uFieldAut h hn φ) (projH _ g) = projH _ g)
    {g : StatedSU n (p ^ f) K} (hg : g ∈ F) :
    ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ *
        (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 := lift_eq_of_commutator_eq (H := StatedSU n (p ^ f) K) (uLift h A φ)
    (fun g => uLift_proj h hn A φ g) hF hfix hg
  have h2 := congrArg (fun x : StatedSU n (p ^ f) K => ((x : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) h1
  simpa only [coe_uLift] using h2

end CFSG.ComponentClassification.Burgoyne.U
