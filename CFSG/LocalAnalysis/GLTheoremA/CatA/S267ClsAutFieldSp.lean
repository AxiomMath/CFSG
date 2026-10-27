module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutField
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
import CFSG.RankThree.PartOne.MB3.OddOutSymplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.OutStructure (Inn OutPChain OutPNice.toChain OutPChain.of_mulEquiv)

section Form

variable {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]

theorem toBilin'_mulVec_mulVec (J M : Matrix n n K) (w z : n → K) :
    Matrix.toBilin' J (M *ᵥ w) (M *ᵥ z) = Matrix.toBilin' (Mᵀ * J * M) w z := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← Matrix.vecMul_transpose M w,
    ← Matrix.dotProduct_mulVec w Mᵀ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem toBilin'_map (J : Matrix n n K) (σ : K ≃+* K) (hJ : J.map σ = J) (w z : n → K) :
    Matrix.toBilin' J (fun i => σ (w i)) (fun i => σ (z i)) = σ (Matrix.toBilin' J w z) := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  change _ = (σ : K →+* K) (w ⬝ᵥ J *ᵥ z)
  rw [RingHom.map_dotProduct (σ : K →+* K)]
  congr 1
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec (σ : K →+* K) J z i]
  change (J *ᵥ fun i => σ (z i)) i = ((J.map σ) *ᵥ fun i => σ (z i)) i
  rw [hJ]

end Form

section Scalars

variable {r : ℕ} {K : Type} [Field K]

theorem not_dvd_card_spScalars [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card ↥((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) := by
  refine not_dvd_card_of_sq_eq_one hp hp2 fun z => ?_
  obtain ⟨⟨z, hzS⟩, hz⟩ := z
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hz
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c = z := hc
  subst hc'
  have hc2 : c ^ 2 = 1 := (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hr c).1 hzS
  apply Subtype.ext
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) ^ 2 = 1
  rw [← map_pow, hc2, map_one]

theorem statedSp_le_isomGL : StatedSp r K ≤ Cls.isomGL (Matrix.toBilin' (formJ r K)) :=
  Cls.gramCore_le_isomGL (formJ r K)

theorem mem_statedSp_of_mem_isomGL {g : GL (Fin r ⊕ Fin r) K}
    (hg : g ∈ Cls.isomGL (Matrix.toBilin' (formJ r K))) : g ∈ StatedSp r K := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  apply (Matrix.toBilin' (n := Fin r ⊕ Fin r) (R₁ := K)).injective
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [← toBilin'_mulVec_mulVec]
  exact Cls.mem_isomGL.1 hg x y

end Scalars

section Field

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem outPChain_sp (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (h2 : (2 : K) ≠ 0)
    (e : ↥S ≃* StatedProj (StatedSp r K)) : OutPChain p ↥S := by
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_StatedSp_two_odd h2 hp
      hp2).toChain.of_mulEquiv e
  · exact (CFSG.RankThree.PartOne.OutStructure.outPNice_StatedSp_odd hr3 hp
      hp2).toChain.of_mulEquiv e

theorem exists_fieldAct_sp (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) (φ : ↥(StatedSp r K) →* Ω)
    (hφS : φ.range = S)
    (hφk : φ.ker = (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) {b : Ω}
    (hbp : b ^ p = 1) (hbN : b ∉ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∃ (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K), A ∈ gsp r K ∧ FieldAct p φ b A σ ∧
      FormRel (Matrix.toBilin' (formJ r K)) A σ := by
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set e := coverProjEquiv φ hφS hφk with he
  set β := transAut e b with hβ
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
    intro h
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1)
  have hE : spSemilinearAutGroup r K = ⊤ := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two h2).1
    · exact (automorphism_generation hr3).1
  have hβE : β ∈ spSemilinearAutGroup r K := hE ▸ Subgroup.mem_top β
  obtain ⟨-, -, -, -, -, -, -, -, hidx, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hr hK
  have hβD : β ∉ spLinearAutGroup r K := by
    intro hD
    have hcop : Nat.Coprime ((Inn (StatedProj (StatedSp r K))).relIndex
        (spLinearAutGroup r K)) p := by
      refine Nat.Coprime.coprime_dvd_left (hidx.trans (Nat.gcd_dvd_left 2 _)) ?_
      exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have hβp : β ^ p ∈ Inn (StatedProj (StatedSp r K)) := by
      rw [hβ, transAut_eq_congr, ← map_pow, ← map_pow, hbp, map_one, map_one]
      exact one_mem _
    exact hbN ((transAut_mem_inner_iff e b).1 (mem_of_pow_mem_of_coprime _ hD hβp hcop))
  have hβo : orderOf β = p := orderOf_transAut_eq e hp hbp hbN
  obtain ⟨hpf, σ, hσo, hσcard, h, hhD, hβeq⟩ := hdesc p hp β hβE hβD hβo
  obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.1 hhD
  refine ⟨A, σ, A.2, ⟨hσo, ?_, fun k => ?_⟩, ?_⟩
  ·
    rw [hσcard, hK, ← pow_mul, Nat.div_mul_cancel hpf]
  ·
    refine ⟨conjSp r K A (fieldSp r K σ (conjSp r K A⁻¹ k)), ?_, ?_⟩
    · rw [coe_conjSp, semiConj_apply]
      rfl
    · have h1 : β (QuotientGroup.mk k) =
          QuotientGroup.mk (conjSp r K A (fieldSp r K σ (conjSp r K A⁻¹ k))) := by
        rw [hβeq, MulAut.mul_apply, MulAut.mul_apply, ← map_inv]
        rfl
      have h2 := transAut_spec e b (QuotientGroup.mk k)
      rw [← hβ, h1] at h2
      exact h2
  ·
    refine ⟨(multiplier r K A)⁻¹, fun u v => ?_⟩
    have hmA := multiplier_spec A
    have hmA' := inv_transpose_formJ hmA
    rw [semiMap_apply, semiMap_apply, toBilin'_mulVec_mulVec, hmA, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, toBilin'_map _ σ (formJ_map σ),
      toBilin'_mulVec_mulVec, hmA', map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      smul_eq_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem exists_clsData_sp (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hr : 2 ≤ r) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) (e : PSimple p S ≃* StatedProj (StatedSp r K))
    {B : Subgroup Ω} (hB : IsElemAbelian p B) :
    ∃ φ : ↥(StatedSp r K) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →* ↥(StatedSp r K),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K), A ∈ gsp r K ∧ FieldAct p φ b A σ ∧
              FormRel (Matrix.toBilin' (formJ r K)) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(StatedSp r K)) : GL (Fin r ⊕ Fin r) K) = θ x) := by
  haveI : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
    intro h
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1)
  obtain ⟨φ, hφS, hφk⟩ := exists_cover_of_center_eq_bot hcore hZ e
  have hker : φ.ker ≤ Subgroup.center ↥(StatedSp r K) :=
    hφk ▸ CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hC : ¬ p ∣ Nat.card φ.ker := hφk ▸ not_dvd_card_spScalars (by omega) hp hp2
  obtain ⟨θ, hθ, hθel, hθk, hθ1⟩ := exists_inner_lift hp hB hZ φ hφS hker hC
  have hOut : OutPChain p ↥S := outPChain_sp hp hp2 hr h2 (coverProjEquiv φ hφS hφk).symm
  refine ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, ?_⟩
  rcases inner_split' hp hB hOut with h | ⟨b, hb, hbN, hBb, hbinf⟩
  · exact Or.inl h
  · right
    obtain ⟨A, σ, hA, hact, hform⟩ :=
      exists_fieldAct_sp hp hp2 hr hℓ hf hK hℓ2 φ hφS hφk (hB.2 b hb) hbN
    exact ⟨b, hb, hbN, hBb, hbinf, A, σ, hA, hact, hform, semiConj_eq_of_fieldAct hp hZ φ hφS
      hker hC hB inf_le_left θ hθ (fun x => hθel.2 _ ⟨x, rfl⟩) hb hact⟩

end Field

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
