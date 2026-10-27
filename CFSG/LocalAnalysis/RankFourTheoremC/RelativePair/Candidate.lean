module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Cand

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.isRelPairCandidate {p : ℕ} (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) :
    IsRelPairCandidate p D R T (normalizer ((R ⊓ T : Subgroup G) : Set G)) := by
  have hprime := sigmaA_prime p hp
  obtain ⟨-, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hS.transitivity_data hD1 hp hd.ext hd.not_le_normalizer hR h13
  obtain ⟨hM, hDP, -, -⟩ := hd.ext.obstruction
  have hDM : D ≤ M := hDP.trans (hS.sylow_le hp hM)
  refine ⟨hd.twoLocal, sup_le inf_le_right hd.le_normalizer, ?_⟩
  exact prime_dvd_card_invariantTwoJoinIn_normalizer_inf p hprime D M R T
    (P.isPGroup'.to_le hDP) hDM hd.maxR hd.maxT hd.not_le_R hd.le_T hd.inf_eq hCD hd.maximal
    (fun T₁ hT₁ => (hglob T₁ hT₁).1)

theorem ObstructionSetting.exists_optimal {p : ℕ} (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) :
    ∃ H V : Subgroup G, IsOptimalRelPair p M D R T H V := by
  obtain ⟨V, hV⟩ := (hS.isRelPairCandidate hD1 hp hR h13 hd).exists_pair hd.le_T hd.maxT.1
    hd.maxT.2.1 hd.le_normalizer
  exact exists_isOptimalRelPair hV

theorem ObstructionSetting.pRank_eq_two (hS : ObstructionSetting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D R T H : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hH : IsRelPairCandidate p D R T H) : CFSG.Open.pRank p H = 2 := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hPM := hS.sylow_le hp hM
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hH.base_le
  have hHlocal := hH.twoLocal
  refine le_antisymm ?_ (hext.rank_eq ▸ pRank_mono p hprime.one_lt hDH)
  by_contra h3
  push Not at h3
  obtain ⟨E, hEH, hE, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨P', hEP'⟩ := (elementary_isPGroup p E hE).exists_le_sylow
  obtain ⟨M', hM', hP'M'⟩ := hS.exists_isCoreMaxLocal hp P'
  have hHM' : H ≤ M' := by
    refine le_of_three_le_pRank_inf hD1 hp hM' hHlocal
      (le_trans (show 3 ≤ CFSG.Open.pRank p H by omega) ?_)
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt _)
      ⟨E, le_inf hEH (hEP'.trans hP'M'), hE, hEc⟩
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P' M' hP'M' D
    (P.isPGroup'.to_le hDP) (hDH.trans hHM')
  set P'' : Sylow p G := ((m : G)⁻¹) • P' with hP''
  have hDP'' : D ≤ (P'' : Subgroup G) := by
    rw [hP'', sylow_coe_smul_eq_map]
    intro d hd
    refine ⟨(m : G) * d * (m : G)⁻¹, hm ⟨d, hd, rfl⟩, ?_⟩
    simp [mul_assoc]
  have hM'' : IsCoreMaxLocal p P'' M' := by
    have := hM'.smul hprime.one_lt ((m : G)⁻¹)
    have hM'm : M'.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom = M' :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem m.2))
    rwa [hM'm] at this
  have hP''M' := hS.sylow_le hp hM''
  have hiso : IsIsolatedPlane p (P'' : Subgroup G) D := by
    refine ⟨hDP'', (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hDe, hDc,
      fun E' _ hE' hDE' => ?_⟩
    have hE'' : IsElemAbelian p E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E').1 hE'
    have hE'D : E' ≤ D := fun e he =>
      hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCD
        (mem_centralizer_iff.mpr fun d hd => congrArg Subtype.val
          (hE''.1.is_comm.comm ⟨d, hDE' hd⟩ ⟨e, he⟩)) (hE''.2 e he)
    rw [← hDc]
    exact card_le_of_le hE'D
  obtain ⟨A, hAP'', hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P''
  obtain ⟨-, z'', hz''D, hz''1, hz''c, -, -⟩ := isolatedPlane_structure hprime P''.isPGroup' hiso
    hAP'' ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  obtain ⟨g, hgN, hgz⟩ := hS.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab hCD hzD hz1
    hzc hN₀M hz''D hz''1
  have hP''Mg : (P'' : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    refine (le_normalizer_zpowers_of_le_centralizer hz''c).trans ?_
    rw [hgz, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hN₀M
  have hMg := hM.smul hprime.one_lt g
  have hM'Mg : M' ≤ M.map (MulAut.conj g).toMonoidHom :=
    le_of_three_le_pRank_inf hD1 hp hMg hM'.1.1 ((hS.three_le_pRank p hp P'').trans
      (pRank_mono p hprime.one_lt (le_inf hP''M' hP''Mg)))
  have hHMg : H ≤ M.map (MulAut.conj g).toMonoidHom := by
    have hMgeq : M.map (MulAut.conj g).toMonoidHom = M' := hM'.1.2 _ hMg.1.1 hM'Mg
    rw [hMgeq]
    exact hHM'
  set X := CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
    (normalizer ((zpowers z : Subgroup G) : Set G)) with hX
  have hXall : ∀ A : Subgroup G, A ≤ M → IsPGroup 2 A → D ≤ normalizer (A : Set G) → A ≤ X := by
    intro A hAM hA2 hDA
    obtain ⟨T₁, hAT₁, hT₁⟩ := exists_invariantTwoMaximalWithin_containing D M A hAM hA2 hDA
    exact hAT₁.trans (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T₁ hT₁).le
  have hjoin : invariantTwoJoinIn D H ≤ X.map (MulAut.conj g).toMonoidHom :=
    (invariantTwoJoinIn_mono hHMg).trans ((invariantTwoJoinIn_map_le hgN).trans
      (Subgroup.map_mono (invariantTwoJoinIn_le_of_forall hXall)))
  have hdvd : p ∣ Nat.card (X.map (MulAut.conj g).toMonoidHom) :=
    hH.not_coprime.trans (Subgroup.card_dvd_of_le hjoin)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hdvd
  exact (hprime.coprime_iff_not_dvd.mp (coprime_card_pPrimeCoreIn_sup hN₀M)) hdvd

theorem ObstructionSetting.not_hasPrimeConstraint (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D R T H : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hH : IsRelPairCandidate p D R T H) :
    ¬ HasPrimeConstraint (G := H) p := by
  intro hcon
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  obtain ⟨hDab, -, -, -, -, -, -, hCD, -⟩ := hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hH.base_le
  have hcontains : ∀ x : G, x ∈ H → x ∈ centralizer (D : Set G) → orderOf x = p → x ∈ D :=
    fun x _ hxC hxo => hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCD hxC
      (by rw [← hxo]; exact pow_orderOf_eq_one x)
  have hall : ∀ A : Subgroup G, A ≤ H → IsPGroup 2 A → D ≤ normalizer (A : Set G) →
      A ≤ (primeComplementCore (G := H) p).map H.subtype := by
    intro A hAH hA2 hDA
    have hcop : p.Coprime (Nat.card A) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA2
      rw [hn]
      exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right n
    exact ambient_prime_constraint_signalizer_le_core p hprime hodd H D A hcon
      (P.isPGroup'.to_le hDP) hDH hcop hAH hDA hcontains
  have hjoin := invariantTwoJoinIn_le_of_forall hall
  have hdvd : p ∣ Nat.card ((primeComplementCore (G := H) p).map H.subtype) :=
    hH.not_coprime.trans (Subgroup.card_dvd_of_le hjoin)
  rw [card_map_of_injective H.subtype_injective] at hdvd
  exact (hprime.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) hdvd

end CFSG.LocalAnalysis.RankFourTheoremC
