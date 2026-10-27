module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Coord

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace CaseBParts

section TIModel

open Matrix CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem su3ti_eq_one_of_fix {u : hypSU h 1 1} (hu : u ∈ hypUnitriangular h 1 1)
    {v : HypIndex 1 1 → K} (hv : v (.inr (.inr 0)) ≠ 0)
    (hfix : ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ v = v) :
    u = 1 := by
  obtain ⟨α, β, -, hM⟩ := exists_uMat_of_mem u hu
  rw [hM] at hfix
  have h1 := congrFun hfix (.inr (.inl 0))
  have h2 := congrFun hfix (.inl 0)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at h1 h2
  have hα : α = 0 := h1.resolve_right hv
  subst hα
  have hβ : β = 0 := by simpa [hv] using h2
  subst hβ
  have h3 : ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = 1 := by
    rw [hM, uMat_zero_zero]
  exact Subtype.ext (Units.ext (by simpa using h3))

theorem su3ti_hypForm_self (v : HypIndex 1 1 → K) :
    hypForm h 1 1 v v = h.bar (v (.inl 0)) * v (.inr (.inr 0)) +
      h.bar (v (.inr (.inl 0))) * v (.inr (.inl 0)) +
      h.bar (v (.inr (.inr 0))) * v (.inl 0) := by
  rw [hypForm_apply]
  simp [Fintype.sum_sum_type, add_assoc]

theorem su3ti_isotropic (x : hypSU h 1 1) :
    hypForm h 1 1 (((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K))
      (((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) = 0 := by
  have := (mem_gramSU_iff_isometry.mp x.2).1 (Pi.single (.inl 0) 1) (Pi.single (.inl 0) 1)
  rw [this, hypForm_single_inl]
  simp

theorem su3ti_z_eq_zero (x : hypSU h 1 1)
    (hf : (((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) (.inr (.inr 0)) = 0) :
    (((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) (.inr (.inl 0)) = 0 := by
  have h0 := su3ti_isotropic x
  rw [su3ti_hypForm_self, hf] at h0
  simpa using h0

theorem su3ti_eq_smul_single {v : HypIndex 1 1 → K} (hz : v (.inr (.inl 0)) = 0)
    (hf : v (.inr (.inr 0)) = 0) :
    v = v (.inl 0) • (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) := by
  funext a
  rcases a with a | a | a
  · rw [Subsingleton.elim a 0]; simp
  · rw [Subsingleton.elim a 0]; simp [hz]
  · rw [Subsingleton.elim a 0]; simp [hf]

theorem su3ti_mem_posFlag_iff {v : HypIndex 1 1 → K} :
    v ∈ posFlag 1 1 K 1 ↔ v (.inr (.inl 0)) = 0 ∧ v (.inr (.inr 0)) = 0 := by
  constructor
  · intro hv
    exact ⟨hv _ (by simp), hv _ (by simp)⟩
  · rintro ⟨hz, hf⟩ a ha
    rcases a with a | a | a
    · simp at ha
    · rw [Subsingleton.elim a 0]; exact hz
    · rw [Subsingleton.elim a 0]; exact hf

theorem su3ti_mem_borel {x : hypSU h 1 1} {c : K} (hc : c ≠ 0)
    (hx : ((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) =
      c • (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) :
    x ∈ hypBorel h 1 1 := by
  rw [mem_hypBorel]
  intro i hi1 hi2
  obtain rfl : i = 1 := le_antisymm hi2 hi1
  have hF : hypFlag h 1 1 1 = posFlag 1 1 K 1 := by
    rw [hypFlag, ite_eq_left le_rfl, isoFlag_eq_posFlag le_rfl]
  have hinv : (((x : GL (HypIndex 1 1) K)⁻¹ : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) =
      c⁻¹ • (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) := by
    have h1 : (((x : GL (HypIndex 1 1) K)⁻¹ : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (((x : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) =
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [hx, mulVec_smul] at h1
    calc _ = c⁻¹ • (c • ((((x : GL (HypIndex 1 1) K)⁻¹ : GL (HypIndex 1 1) K) :
          Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (Pi.single (.inl 0) 1 :
            HypIndex 1 1 → K))) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = _ := by rw [h1]
  rw [hF, Subgroup.smul_def]
  refine smul_eq_of_mulVec_mem ?_ ?_
  · intro v hv
    obtain ⟨hz, hf⟩ := su3ti_mem_posFlag_iff.mp hv
    rw [su3ti_eq_smul_single hz hf, mulVec_smul, hx, smul_smul, su3ti_mem_posFlag_iff]
    simp
  · intro v hv
    obtain ⟨hz, hf⟩ := su3ti_mem_posFlag_iff.mp hv
    rw [su3ti_eq_smul_single hz hf, mulVec_smul, hinv, smul_smul, su3ti_mem_posFlag_iff]
    simp

theorem su3ti_mem_borel_of_f_eq_zero (x : hypSU h 1 1)
    (hf : (((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) (.inr (.inr 0)) = 0) :
    x ∈ hypBorel h 1 1 := by
  have hz := su3ti_z_eq_zero x hf
  have hv' := su3ti_eq_smul_single hz hf
  refine su3ti_mem_borel (c := (((x : GL (HypIndex 1 1) K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (Pi.single (.inl 0) 1 :
      HypIndex 1 1 → K)) (.inl 0)) ?_ hv'
  intro h0
  have h1 : (((x : GL (HypIndex 1 1) K)⁻¹ : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (((x : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) =
      (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [hv', h0, zero_smul, mulVec_zero] at h1
  have := congrFun h1 (.inl 0)
  simp at this

theorem su3ti_unitriangular_mulVec_single {u : hypSU h 1 1} (hu : u ∈ hypUnitriangular h 1 1) :
    ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) = Pi.single (.inl 0) 1 := by
  obtain ⟨α, β, -, hM⟩ := exists_uMat_of_mem u hu
  rw [hM]
  funext a
  rcases a with a | a | a
  · rw [Subsingleton.elim a 0]; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · rw [Subsingleton.elim a 0]; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · rw [Subsingleton.elim a 0]; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem su3ti_conj_eq_one {x u' u : hypSU h 1 1} (hx : x ∉ hypBorel h 1 1)
    (hu' : u' ∈ hypUnitriangular h 1 1) (hu : u ∈ hypUnitriangular h 1 1)
    (hxu : x * u' * x⁻¹ = u) : u = 1 := by
  have hvf : (((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)) (.inr (.inr 0)) ≠ 0 :=
    fun h0 => hx (su3ti_mem_borel_of_f_eq_zero x h0)
  have h1 : ((u : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      ((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      ((x : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      ((u' : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    rw [← hxu]
    simp [mul_assoc]
  refine su3ti_eq_one_of_fix hu hvf ?_
  rw [mulVec_mulVec, h1, ← mulVec_mulVec, su3ti_unitriangular_mulVec_single hu']

end TIModel

section SylowTI

open scoped Pointwise

theorem su3ti_sylow_inf_eq_bot_of_conj {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (U : Sylow p S)
    (H : ∀ x : S, x ∉ normalizer ((U : Subgroup S) : Set S) →
      ∀ u ∈ (U : Subgroup S), ∀ u' ∈ (U : Subgroup S), x * u' * x⁻¹ = u → u = 1)
    {P Q : Sylow p S} (hPQ : P ≠ Q) : (P : Subgroup S) ⊓ Q = ⊥ := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq S U P
  obtain ⟨g', rfl⟩ := MulAction.exists_smul_eq S U Q
  by_cases hx : g⁻¹ * g' ∈ normalizer ((U : Subgroup S) : Set S)
  · exfalso
    apply hPQ
    have h1 : (g⁻¹ * g') • U = U := Sylow.smul_eq_iff_mem_normalizer.mpr hx
    calc g • U = g • ((g⁻¹ * g') • U) := by rw [h1]
      _ = g' • U := by rw [smul_smul, mul_inv_cancel_left]
  · rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
      Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨⟨s, hs, rfl⟩, s', hs', hss'⟩ := hy
    simp only [MulAut.smul_def, MulAut.conj_apply] at hss'
    have h2 : (g⁻¹ * g') * s' * (g⁻¹ * g')⁻¹ = s := by
      have : g⁻¹ * (g' * s' * g'⁻¹) * g = s := by
        rw [hss']; group
      rw [← this]; group
    have h3 := H (g⁻¹ * g') hx s hs s' hs' h2
    simp [MulAut.smul_def, h3]

end SylowTI

theorem su3SylowTI : SU3SylowTIStatement := by
  intro f K _ h hf P Q hP hQ hPQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.finite
  obtain ⟨-, ⟨U, hU⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have toSylow : ∀ P : Subgroup (hypSU h 1 1), IsSylowOf 2 P ⊤ →
      ∃ P' : Sylow 2 (hypSU h 1 1), (P' : Subgroup (hypSU h 1 1)) = P := by
    intro P hP
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP
    obtain ⟨-, hP2, hdvd⟩ := hP
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hP2.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  obtain ⟨P', rfl⟩ := toSylow P hP
  obtain ⟨Q', rfl⟩ := toSylow Q hQ
  have hne : P' ≠ Q' := fun e => hPQ (by rw [e])
  refine su3ti_sylow_inf_eq_bot_of_conj U ?_ hne
  intro x hx u hu u' hu' hxu
  rw [hU] at hu hu'
  have hxB : x ∉ hypBorel h 1 1 := by
    intro hxB
    apply hx
    have := (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).mp
      (normal_hypUnitriangular (h := h) (r := 1) le_rfl) hxB
    rwa [← hU] at this
  exact su3ti_conj_eq_one hxB hu' hu hxu

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
