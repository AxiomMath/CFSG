module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBOmega
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAIdx
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALinAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniCent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup CFSG.Open CFSG.Open.StatedAPI
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem statedProj_eq_one_iff {p : ℕ} {K : Type} [Field K] (A : ↥(StatedSL p K)) :
    (QuotientGroup.mk A : StatedProj (StatedSL p K)) = 1 ↔
      ∃ z : Kˣ, (A : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) z := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩

@[expose] noncomputable def linModel (p : ℕ) (K : Type) [Field K] [Finite K] (hn : 3 ≤ p) :
    MatModel p K (projectiveSL p K) where
  H := StatedSL p K
  𝔾 := ⊤
  norm_mem := fun g _ A hA => by
    rw [statedSL_eq_ker_det] at hA ⊢
    exact (MonoidHom.normal_ker _).conj_mem A hA g
  ι := (statedEquivL p K).toMonoidHom.comp
    (QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf (StatedSL p K)))
  c := (conjAut p K).comp (⊤ : Subgroup (GL (Fin p) K)).subtype
  det_one := fun A hA => det_of_mem_statedSL hA
  ι_surj := (statedEquivL p K).surjective.comp (QuotientGroup.mk'_surjective _)
  ι_eq_one := fun A => by
    change statedEquivL p K (QuotientGroup.mk A) = 1 ↔ _
    rw [map_eq_one_iff _ (statedEquivL p K).injective]
    exact statedProj_eq_one_iff A
  c_ι := fun g A => by
    set ϕ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL p K with hϕ
    change conjAut p K (g : GL (Fin p) K) (statedEquivL p K (QuotientGroup.mk A)) =
      statedEquivL p K (QuotientGroup.mk _)
    rw [statedEquivL_mk, statedEquivL_mk, conjAut_proj]
    congr 1
    apply ϕ.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Units.ext
    rw [hϕ, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, coe_slConjugation]
    have h1 : ((((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL p K).symm A :
        SpecialLinearGroup (Fin p) K)) : Matrix (Fin p) (Fin p) K) =
          ((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
      rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
    rw [h1]
    simp [Units.val_mul]
  c_eq_one := fun g hg => by
    obtain ⟨-, -, hker⟩ := lin_structure (K := K) hn
    have : (g : GL (Fin p) K) ∈ (conjAut p K).ker := hg
    rw [hker] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz.symm⟩


theorem linModel_range {p : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ p) :
    (linModel p K hn).c.range = linearAutGroup p K := by
  rw [linearAutGroup_eq_range]
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, trivial⟩, rfl⟩

theorem linModelHyps {p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime) (hn : 3 ≤ p)
    (hpK : p ∣ Nat.card K - 1) {ŷ : GL (Fin p) K} {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) : ModelHyps (linModel p K hn) ŷ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  refine ⟨Subgroup.mem_top _, ?_, ?_, ?_⟩
  · intro Th hTh hT2 hTne hyN
    have hdet : ∀ g ∈ Th, (g : Matrix (Fin p) (Fin p) K).det = 1 := fun g hg =>
      det_of_mem_statedSL (hTh hg)
    obtain ⟨B, hB⟩ := exists_diagData hp hp2 hT2 hTne hdet hy hω hyN
    exact ⟨B, Subgroup.mem_top _, hB⟩
  · intro Th B _ hB hyN
    obtain ⟨Q⟩ : Nonempty (Sylow p Kˣ) := inferInstance
    have h1 := not_dvd_index_normalizer hp2 hB.sep hB.diag hB.rot hyN Q hpK
    have hsurj : Function.Surjective ((⊤ : Subgroup (GL (Fin p) K)).subtype) :=
      fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
    exact (Subgroup.index_comap_of_surjective _ hsurj).symm ▸ h1
  · have hpN : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpN
    refine ⟨ζ, ?_, ?_, ?_, fun j => Subgroup.mem_top _⟩
    · have := pow_orderOf_eq_one ζ
      rwa [hζ] at this
    · intro h1
      rw [h1, orderOf_one] at hζ
      exact hp.one_lt.ne hζ
    · intro h2
      have : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hζ] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega


theorem linHyps_of_cfg {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}
    {L : Subgroup Y} [L.Normal] [Group.IsPerfect ↥L] (hcfg : LinUniCfg p P x z L)
    (hCp : IsPGroup p (centralizer (L : Set Y))) {K : Type} [Field K] [Finite K]
    (e : (↥L ⧸ center ↥L) ≃* StatedProj (StatedSL p K)) (ŷ : GL (Fin p) K) (ω : Kˣ)
    (hpK : p ∣ Nat.card K - 1) (hŷp : ŷ ^ p = GeneralLinearGroup.scalar (Fin p) ω)
    (hω : orderOf ω = p ^ (Nat.card K - 1).factorization p)
    (hact : ∀ (g h : ↥L) (A B : ↥(StatedSL p K)), x * (g : Y) * x⁻¹ = (h : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B : GL (Fin p) K) = ŷ * (A : GL (Fin p) K) * ŷ⁻¹ →
      e (QuotientGroup.mk h) = QuotientGroup.mk B) :
    ∃ (hn : 3 ≤ p) (hM : ModelHyps (linModel p K hn) ŷ),
      AutHyps (thetaP L (e.trans (statedEquivL p K))) (linModel p K hn) ∧
      thetaP L (e.trans (statedEquivL p K)) x = (linModel p K hn).c ⟨ŷ, hM.ŷ_mem⟩ := by
  have hY := hcfg.data.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ p := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  have hKcard : 1 < Nat.card K := Finite.one_lt_card
  have hωnp : ∀ b : K, b ^ p ≠ (ω : K) := by
    have ha : 1 ≤ (Nat.card K - 1).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp (by omega) hpK
    exact not_pow_of_orderOf hp ha hω (Nat.pow_succ_factorization_not_dvd (by omega) hp)
  have hŷp' : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p =
      Matrix.scalar (Fin p) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hdet := not_pow_det hp hp2 hŷp' hωnp
  have hM := linModelHyps hp hn3 hpK hŷp' hωnp
  refine ⟨hn3, hM, ?_, ?_⟩
  · set eP := e.trans (statedEquivL p K) with heP
    have hx : thetaP L eP x = conjAut p K ŷ := thetaP_eq_conjAut e ŷ hact
    obtain ⟨hDn, hab, -⟩ := lin_structure (K := K) hn3
    have hr := linModel_range (p := p) (K := K) hn3
    have hkerθ : (thetaP L eP).ker = centralizer (L : Set Y) := by
      ext y
      rw [MonoidHom.mem_ker, thetaP_eq_one_iff]
    have hker_p : IsPGroup p (thetaP L eP).ker := hkerθ ▸ hCp
    have hIle : inner (projectiveSL p K) ≤ (thetaP L eP).range := by
      rintro _ ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := eP.surjective w
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨(l : Y), thetaP_of_mem L eP l⟩
    have hdvd : (inner (projectiveSL p K)).relIndex (linearAutGroup p K) ∣ p :=
      (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := p) hp.one_lt.le).trans
        (Nat.gcd_dvd_left _ _)
    have hDS : linearAutGroup p K ≤ (thetaP L eP).range :=
      le_of_relIndex_dvd_prime hp hIle hdvd (conjAut_mem_linearAutGroup ŷ) ⟨x, hx⟩
        (conjAut_not_mem_inner hn3 ŷ hdet)
    have hperf' : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤ := hcfg.data.perf
    have hab' : ∀ a b : MulAut (projectiveSL p K), a * b * a⁻¹ * b⁻¹ ∈ linearAutGroup p K := hab
    have hDidx := not_dvd_index_comap_of_commutator hp (thetaP L eP) (linearAutGroup p K) hab'
      hperf'
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hr]
      exact hDS
    · rw [hr]
      exact hDidx
    · rw [hr]
      intro φ hφ ψ
      exact hDn.conj_mem φ hφ ψ
    · rw [hr]
      exact hab'
  · set eP := e.trans (statedEquivL p K) with heP
    exact thetaP_eq_conjAut e ŷ hact


theorem kd292CaseBSylow_lin (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y)
    (L : Subgroup Y) (hcfg : LinUniCfg p P x z L) (hzero : LinUniZero p L)
    (hmodel : LinUniModelLin p x L) (T : Subgroup Y) (hT2 : IsPGroup 2 T)
    (hxN : x ∈ normalizer (T : Set Y)) (hTL : T ⊓ L ≠ ⊥) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ normalizer (omegaOneTwo T L : Set Y) := by
  have hY := hcfg.data.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hL := hcfg.comp
  have hLu := hcfg.uniq
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hCp : IsPGroup p (centralizer (L : Set Y)) :=
    I292.centralizer_isPGroup hY.core hL hLu hzero.pCore_cyclic hzero.omega_le
  obtain ⟨K, instF, instFin, e, ŷ, ω, hpK, hŷp, hω, hact⟩ := hmodel
  obtain ⟨hn3, hM, hAut, hx⟩ := linHyps_of_cfg hcfg hCp e ŷ ω hpK hŷp hω hact
  exact exists_sylow_normalizer hp hp2 hCp (e.trans (statedEquivL p K)) (linModel p K hn3) hM
    hAut omegaOneTwo_le_left (isPGroup_omegaOneTwo hT2) (omegaOneTwo_ne_bot hT2 hTL)
    (mem_normalizer_omegaOneTwo' hxN) hx

theorem kd292CaseBConstr_lin (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y)
    (L : Subgroup Y) (hcfg : LinUniCfg p P x z L) (hzero : LinUniZero p L)
    (hmodel : LinUniModelLin p x L) (T : Subgroup Y) (hT2 : IsPGroup 2 T)
    (hxN : x ∈ normalizer (T : Set Y)) (hTL : T ⊓ L ≠ ⊥) :
    GLAPLayer p (normalizer (omegaOneTwo T L : Set Y)) = ⊥ := by
  have hY := hcfg.data.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hL := hcfg.comp
  have hLu := hcfg.uniq
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hCp : IsPGroup p (centralizer (L : Set Y)) :=
    I292.centralizer_isPGroup hY.core hL hLu hzero.pCore_cyclic hzero.omega_le
  obtain ⟨K, instF, instFin, e, ŷ, ω, hpK, hŷp, hω, hact⟩ := hmodel
  obtain ⟨hn3, hM, hAut, hx⟩ := linHyps_of_cfg hcfg hCp e ŷ ω hpK hŷp hω hact
  exact glaPLayer_normalizer hp hp2 hCp (e.trans (statedEquivL p K)) (linModel p K hn3) hM hAut
    omegaOneTwo_le_left (isPGroup_omegaOneTwo hT2) (omegaOneTwo_ne_bot hT2 hTL)
    (mem_normalizer_omegaOneTwo' hxN) hx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
