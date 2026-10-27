module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowRee
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowUnitary
import CFSG.Permutation.SylowTrivialIntersection

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding

theorem sylow_inf_eq_bot_of_mulEquiv {K G : Type*} [Group K] [Finite K] [Group G] {p : ℕ}
    (e : K ≃* G) (T : Sylow p K) {R : Subgroup G}
    (hTR : (T : Subgroup K).map e.toMonoidHom = R) (hT : (T : Subgroup K) ≠ ⊥)
    (hcount : Nat.card (Sylow p K) = Nat.card T + 1) (g : G)
    (hg : ∀ y ∈ R, g⁻¹ * y * g ∈ R → y = 1) :
    ∀ Q : Sylow p K, Q ≠ T → (T : Subgroup K) ⊓ Q = ⊥ := by
  refine (CFSG.Permutation.SylowTrivialIntersection.trivialIntersection_of_inf_eq_bot hT
    (Q₁ := e.symm g • T) ?_ hcount.le).1
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxT, hxQ⟩ := Subgroup.mem_inf.mp hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hxQ
  have h1 : e x ∈ R := by
    rw [← hTR]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hxT
  have h2 : g⁻¹ * e x * g ∈ R := by
    rw [← hTR]
    have h3 := Subgroup.mem_map_of_mem e.toMonoidHom hxQ
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply] using h3
  rw [Subgroup.mem_bot]
  exact e.injective ((hg _ h1 h2).trans (map_one e).symm)

open CFSG.UnitaryThreeRecognition.Model in
theorem kFactNineThreeNoTwoAt_unitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q) :
    KFactNineThreeNoTwoAt p (.lie d) := by
  intro X _ _ K hK ⟨eK⟩ _ T S hS hTS
  haveI : Fact p.Prime := ⟨hp⟩
  have hu : IsUnitaryIndex p d := hd
  obtain ⟨hTcard, hcount⟩ := KFactProofs.OneLieSylow.card_sylow_unitary hu ⟨eK⟩ T
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hu ⟨eK⟩)
  haveI : IsSimpleGroup (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    isSimpleGroup_psu J _ hF hfix hq
  haveI : IsSimpleGroup K := e.isSimpleGroup
  obtain ⟨R, hR⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T R
  have hTc : Nat.card T = (p ^ d.1.fieldExponent) ^ 3 := hTcard
  have hcount' : Nat.card (Sylow p K) = Nat.card T + 1 := by rw [hcount, hTc]
  have hT : (T : Subgroup K) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hTcard]
    exact one_lt_pow₀ (by omega) (by norm_num)
  have hTI := sylow_inf_eq_bot_of_mulEquiv e' T (he'.trans hR) hT hcount' (weyl J hJ)
    fun y hy hwy => by
      have h1 : ((weyl J hJ)⁻¹ * y * weyl J hJ) • pinf J hJ = pinf J hJ :=
        rootGroup_le_stabilizer J hJ hwy
      rw [mul_smul, mul_smul, weyl_smul_pinf, inv_smul_eq_iff, weyl_smul_pinf] at h1
      exact Subgroup.disjoint_def.mp (rootGroup_disjoint_stabilizer_pzero J hJ) hy h1
  refine le_centralizer_of_ti hp2 T hTI hcount' (fun a => ?_) hS hTS
  rw [hTc, ← pow_mul]
  exact pow_add_one_ne_two_pow (hp.odd_of_ne_two hp2) hp.one_lt (by omega) a

theorem kFactNineThreeNoTwoAt_ree
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ m : ℕ, d.1 = .reeG2 m) : KFactNineThreeNoTwoAt 3 (.lie d) := by
  intro X _ _ K hK ⟨eK⟩ _ T S hS hTS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdR : IsReeGTwoIndex 3 d := ⟨rfl, hd⟩
  obtain ⟨hTcard, hcount⟩ := KFactProofs.OneLieSylow.card_sylow_ree hdR ⟨eK⟩ T
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hdR ⟨eK⟩
  have hF : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  haveI : IsSimpleGroup K := by
    obtain ⟨φ⟩ := ReeModel.nonempty_derivedCentralQuotient_equiv_reeGamma ha hF
    have hm : CFSG.Blueprint.ReeTitsModel K .twistedG2 3 (2 * a + 1) :=
      ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl,
        GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hF, ⟨e.trans φ.symm⟩⟩
    exact (CFSG.LieType.Simplicity.fam_2g2_simplicity K 3 (2 * a + 1) hm).2
  obtain ⟨⟨P, hP⟩, -, hco, -⟩ := ReeModel.std_facts hF
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e T P
  obtain ⟨g, hg⟩ : ∃ g, g ∉ ReeModel.stdB a (GaloisField 3 (2 * a + 1)) := by
    by_contra h
    push Not at h
    exact hco.1 (eq_top_iff.mpr fun g _ => h g)
  have hTc : Nat.card T = (3 ^ d.1.fieldExponent) ^ 3 := hTcard
  have hcount' : Nat.card (Sylow 3 K) = Nat.card T + 1 := by rw [hcount, hTc]
  have hT : (T : Subgroup K) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hTcard]
    exact one_lt_pow₀ (one_lt_pow₀ (by norm_num) (by omega)) (by norm_num)
  have hTI := sylow_inf_eq_bot_of_mulEquiv e' T (he'.trans hP) hT hcount' g fun y hy hgy => by
    have hmem : y ∈ ReeModel.stdU a (GaloisField 3 (2 * a + 1)) ⊓
        (ReeModel.stdU a (GaloisField 3 (2 * a + 1))).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, hgy, by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩⟩
    rw [ReeModel.inf_map_conj_eq_bot hF hg, Subgroup.mem_bot] at hmem
    exact hmem
  refine le_centralizer_of_ti (by norm_num) T hTI hcount' (fun b => ?_) hS hTS
  rw [hTc, ← pow_mul]
  exact pow_add_one_ne_two_pow ⟨1, rfl⟩ (by norm_num) (by omega) b

@[expose] def KFactNineThreeNoTwoRestTwo : Prop :=
  ∀ p, p.Prime → p ≠ 2 → ∀ i, IsNineThreeIndex p i →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsCaseTwoIndex p d) →
    (¬ ∃ (n : ℕ) (hn : 5 ≤ n), i = .alternating n hn) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p = 3 ∧ ∃ m : ℕ, d.1 = .reeG2 m) →
    KFactNineThreeNoTwoAt p i

theorem kFactNineThreeNoTwoRest_of_restTwo
    (h : KFactNineThreeNoTwoRestTwo) : KFactNineThreeNoTwoRest := by
  intro p hp hp2 i hi h2 h3 h4
  by_cases h5 : ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q
  · obtain ⟨d, rfl, hd⟩ := h5
    exact kFactNineThreeNoTwoAt_unitary hp hp2 hd
  by_cases h6 : ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p = 3 ∧ ∃ m : ℕ, d.1 = .reeG2 m
  · obtain ⟨d, rfl, rfl, hd⟩ := h6
    exact kFactNineThreeNoTwoAt_ree hd
  exact h p hp hp2 i hi h2 h3 h4 h5 h6

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
