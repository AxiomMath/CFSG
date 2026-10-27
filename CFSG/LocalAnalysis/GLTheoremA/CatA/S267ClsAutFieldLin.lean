module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutField
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.SteinbergR3ELinearFieldDescent
import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.OutStructure (Inn OutPChain OutPNice.toChain OutPChain.of_mulEquiv)

section Model

variable {n : ℕ} {K : Type} [Field K]

private noncomputable def statedProjSLEquiv (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem not_dvd_card_slScalars [Finite K] {p : ℕ} (hp : p.Prime)
    (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) :
    ¬ p ∣ Nat.card ↥((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  have hzg : z ^ Nat.gcd n (Nat.card K - 1) = 1 := by
    obtain ⟨⟨z, hzS⟩, hzZ⟩ := z
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hzZ
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin n) c = z := hc
    subst hc'
    have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hzS
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hcn : c ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    have hcq : c ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    have hcg : c ^ Nat.gcd n (Nat.card K - 1) = 1 := pow_gcd_eq_one.2 ⟨hcn, hcq⟩
    apply Subtype.ext
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ Nat.gcd n (Nat.card K - 1) = 1
    rw [← map_pow, hcg, map_one]
  have h1 := orderOf_dvd_of_pow_eq_one hzg
  rw [hz] at h1
  exact hdiag h1

private theorem mem_semilinearAutGroup_of_pow_eq_one [Finite K] (hn : 3 ≤ n)
    {γ : MulAut (projectiveSL n K)} {m : ℕ} (hm : Odd m) (hγ : γ ^ m = 1) :
    γ ∈ semilinearAutGroup n K := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL n
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  exact CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' hm
    (by rw [hγ]; exact one_mem _)

theorem statedSL_le_isomGL :
    StatedSL n K ≤ Cls.isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) := by
  rw [Cls.isomGL_zero]
  exact le_top

theorem exists_scalar_mul_mem_statedSL [Finite K] {p : ℕ} (hp : p.Prime)
    (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) {g : GL (Fin n) K} (hgp : g ^ p = 1) :
    ∃ c : Kˣ, c ^ p = 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
        Cls.isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) ∧
      Matrix.GeneralLinearGroup.scalar (Fin n) c * g ∈ StatedSL n K := by
  haveI : Fact p.Prime := ⟨hp⟩
  set d : Kˣ := (Matrix.GeneralLinearGroup.det g)⁻¹ with hd
  have hdp : d ^ p = 1 := by rw [hd, inv_pow, ← map_pow, hgp, map_one, inv_one]
  have hdetc : ∀ c : Kˣ, c ^ n = d →
      Matrix.GeneralLinearGroup.scalar (Fin n) c * g ∈ StatedSL n K := by
    intro c hc
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    rw [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Units.val_pow_eq_pow_val, hc, hd]
    change (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) *
      ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmem : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
      Cls.isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) := fun c => by
    rw [Cls.isomGL_zero]
    exact Subgroup.mem_top _
  by_cases hd1 : d = 1
  · refine ⟨1, one_pow p, hmem 1, hdetc 1 ?_⟩
    rw [one_pow, hd1]
  ·
    have hdo : orderOf d = p := orderOf_eq_prime hdp hd1
    have hpq : p ∣ Nat.card K - 1 := by
      rw [← hdo, ← Nat.card_units]
      exact orderOf_dvd_natCard d
    have hpn : ¬ p ∣ n := fun h => hdiag (Nat.dvd_gcd h hpq)
    have hcop : Nat.Coprime n p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn))
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    refine ⟨d ^ u, by rw [← pow_mul, mul_comm, pow_mul, hdp, one_pow], hmem _, hdetc _ ?_⟩
    rw [← pow_mul, mul_comm, ← pow_mod_orderOf, hdo, hu, pow_one]

end Model

section Field

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem outPChain_lin (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) (e : ↥S ≃* StatedProj (StatedSL n K)) :
    OutPChain p ↥S :=
  (CFSG.RankThree.PartOne.OutStructure.outPNice_projectiveSL hp hp2 hn hdiag).toChain.of_mulEquiv
    (e.trans (statedProjSLEquiv n K))

theorem exists_fieldAct_lin (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hpℓ : p ≠ ℓ)
    (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) (φ : ↥(StatedSL n K) →* Ω) (hφS : φ.range = S)
    (hφk : φ.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) {b : Ω}
    (hbp : b ^ p = 1) (hbN : b ∉ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
      FormRel (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) A σ := by
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  set e : projectiveSL n K ≃* ↥S := (statedProjSLEquiv n K).symm.trans (coverProjEquiv φ hφS hφk)
    with he
  set γ := transAut e b with hγ
  have hγo : orderOf γ = p := orderOf_transAut_eq e hp hbp hbN
  have hγp : γ ^ p = 1 := by rw [← hγo]; exact pow_orderOf_eq_one γ
  have hγE : γ ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_eq_one hn (hp.odd_of_ne_two hp2) hγp
  have hγD : γ ∉ linearAutGroup n K := by
    intro hD
    have hinn := CFSG.RankThree.PartOne.OutStructure.linear_D2 hp hn hdiag γ hD 1
      (by rw [pow_one, hγp]; exact one_mem _)
    exact hbN ((transAut_mem_inner_iff e b).1 hinn)
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  obtain ⟨hpf, σ, hσo, ⟨h, hhD, hγeq⟩, hσcard⟩ := hdesc p hp hpℓ γ hγE hγD hγo
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hhD
  refine ⟨A, σ, ⟨hσo, ?_, fun k => ?_⟩, ⟨1, fun u v => by simp⟩⟩
  · rw [hσcard, hK, ← pow_mul, Nat.div_mul_cancel hpf]
  ·
    set kS := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm k with hkS
    set kS' := CatalogueBHigherLinearAction.slConjugation n K A
      (SpecialLinearGroup.map σ.toRingHom
        (CatalogueBHigherLinearAction.slConjugation n K A⁻¹ kS)) with hkS'
    refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K kS', ?_, ?_⟩
    · apply Units.ext
      rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, hkS', coe_slConjugation,
        semiConj_apply, Units.val_mul, Units.val_mul, coe_glFieldAut]
      change (A : Matrix (Fin n) (Fin n) K) *
          ((CatalogueBHigherLinearAction.slConjugation n K A⁻¹ kS :
            SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
      have hkm : ((kS : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (((k : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
        rw [hkS, ← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
          MulEquiv.apply_symm_apply]
      rw [coe_slConjugation, inv_inv, Units.val_mul, Units.val_mul, hkm]
    · have h1 : γ (proj n K kS) = proj n K kS' := by
        rw [hγeq, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, conjAut_proj, fieldAut_proj,
          conjAut_proj]
      have h2 := transAut_spec e b (proj n K kS)
      rw [← hγ, h1] at h2
      have h3 : ∀ g : SpecialLinearGroup (Fin n) K, ((e (proj n K g) : ↥S) : Ω) =
          φ (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g) := fun g => rfl
      rw [h3, h3, hkS, MulEquiv.apply_symm_apply] at h2
      exact h2

theorem exists_clsData_lin (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hpℓ : p ≠ ℓ) (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (e : PSimple p S ≃* StatedProj (StatedSL n K)) {B : Subgroup Ω} (hB : IsElemAbelian p B) :
    ∃ φ : ↥(StatedSL n K) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →* ↥(StatedSL n K),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin n) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
              FormRel (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(StatedSL n K)) : GL (Fin n) K) = θ x) := by
  obtain ⟨φ, hφS, hφk⟩ := exists_cover_of_center_eq_bot hcore hZ e
  have hker : φ.ker ≤ Subgroup.center ↥(StatedSL n K) :=
    hφk ▸ CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hC : ¬ p ∣ Nat.card φ.ker := hφk ▸ not_dvd_card_slScalars hp hdiag
  obtain ⟨θ, hθ, hθel, hθk, hθ1⟩ := exists_inner_lift hp hB hZ φ hφS hker hC
  have hOut : OutPChain p ↥S := outPChain_lin hp hp2 hn hdiag (coverProjEquiv φ hφS hφk).symm
  refine ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, ?_⟩
  rcases inner_split' hp hB hOut with h | ⟨b, hb, hbN, hBb, hbinf⟩
  · exact Or.inl h
  · right
    obtain ⟨A, σ, hact, hform⟩ :=
      exists_fieldAct_lin hp hp2 hn hℓ hf hK hpℓ hdiag φ hφS hφk (hB.2 b hb) hbN
    exact ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, semiConj_eq_of_fieldAct hp hZ φ hφS
      hker hC hB inf_le_left θ hθ (fun x => hθel.2 _ ⟨x, rfl⟩) hb hact⟩

end Field

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
