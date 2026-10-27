module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Pair
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.exists_mem_normalizer_zpowers_eq (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) (hCD : centralizer (D : Set G) ≤ M) {z : G} (hzD : z ∈ D)
    (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) {d : G} (hdD : d ∈ D)
    (hd1 : d ≠ 1) :
    ∃ g ∈ normalizer (D : Set G), zpowers d = (zpowers z).map (MulAut.conj g).toMonoidHom := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hcard : ∀ y ∈ D, y ≠ 1 → Nat.card (zpowers y) = p := fun y hy hy1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hDe.2 y hy) hy1]
  by_cases hdz : d ∈ zpowers z
  · refine ⟨1, one_mem _, ?_⟩
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext
      simp
    rw [hid, Subgroup.map_id]
    exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hdz)
      (by rw [hcard z hzD hz1, hcard d hdD hd1])
  obtain ⟨g₀, hg₀N, hg₀M⟩ := IsConcreteLE.not_le_iff_exists.mp hext.obstruction.2.2.2
  have hwD : g₀ * z * g₀⁻¹ ∈ D := (mem_normalizer_iff.mp hg₀N z).mp hzD
  have hwz : g₀ * z * g₀⁻¹ ∉ zpowers z := by
    intro hw
    have hw1 : g₀ * z * g₀⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
    have heq : zpowers (g₀ * z * g₀⁻¹) = zpowers z := Subgroup.eq_of_le_of_card_ge
      (zpowers_le.mpr hw) (by rw [hcard _ hwD hw1, hcard z hzD hz1])
    apply hg₀M
    refine hN₀M (mem_normalizer_iff_map_conj_eq.mpr ?_)
    rw [MonoidHom.map_zpowers]
    exact heq
  obtain ⟨n, hnP, hnD, hnC⟩ :=
    hS.exists_mem_normalizer_not_mem_centralizer hD1 hp hext hPD hDab hCD
  have hn : ∃ k : ℕ, n ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  obtain ⟨k, hk⟩ := exists_pow_conj_zpowers_eq hDe hDc hzD hz1 hn hnD hnz hnC hwD hwz hdD hdz
  refine ⟨n ^ k * g₀, mul_mem (pow_mem hnD k) hg₀N, ?_⟩
  rw [MonoidHom.map_zpowers, ← hk]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem ObstructionSetting.pRank_normalizer_inf_eq_two (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) {R T : Subgroup G}
    (hRmax : rankTwoMaximalInvariantTwoSubgroup D R)
    (hTmax : rankTwoMaximalInvariantTwoSubgroup D T) (hRM : ¬ R ≤ M) (hTM : T ≤ M)
    (hRT : R ⊓ T ≠ ⊥) (hint : R ⊓ M = R ⊓ T)
    (hmaximal : ∀ R' T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D R' →
      rankTwoMaximalInvariantTwoSubgroup D T' → ¬ R' ≤ M → T' ≤ M →
        Nat.card (R' ⊓ T' : Subgroup G) ≤ Nat.card (R ⊓ T : Subgroup G)) :
    CFSG.Open.pRank p (normalizer ((R ⊓ T : Subgroup G) : Set G)) = 2 := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hPM := hS.sylow_le hp hM
  have hDM : D ≤ M := hDP.trans hPM
  set H := normalizer ((R ⊓ T : Subgroup G) : Set G) with hH
  obtain ⟨hHlocal, hDH⟩ := maximal_pair_intersection_normalizer_twoLocal D R T hRmax hTmax hRT
  have hescape := relative_pair_intersection_normalizer_escapes M R T hRmax.1 hRM hTM hint
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
  have hMgeq : M.map (MulAut.conj g).toMonoidHom = M' := hM'.1.2 _ hMg.1.1 hM'Mg
  have hgM : g ∉ M := by
    intro hgM
    have hMg' : M.map (MulAut.conj g).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hgM)
    rw [← hMgeq, hMg'] at hHM'
    exact hescape hHM'
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  exact not_normalizer_inf_le_map_conj_of_relativePair hprime (P.isPGroup'.to_le hDP) hDM hCD
    (coprime_card_pPrimeCoreIn_sup hN₀M)
    (hDP.trans (le_normalizer_pPrimeCoreIn_sup hPM hPN₀))
    (fun T₁ hT₁ => (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T₁ hT₁).le) hglob hRmax
    hTmax hRM hTM hmaximal hgN hgM (hHM'.trans hMgeq.symm.le)

theorem ObstructionSetting.gl83InvariantTwoContainment_of_relativePairExclusion
    (hS : ObstructionSetting G) (hD1 : TheoremD1 G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hX : GL83RelativePairExclusion G) :
    GL83InvariantTwoContainment G := by
  intro p hp P M D hext hPD _ T _
  exfalso
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, -, -, -, -, -, hCD, hglob⟩ := hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hDM : D ≤ M := hDP.trans (hS.sylow_le hp hM)
  obtain ⟨R₀, T', hR₀, hT', hR₀M, hT'M, hR₀T'⟩ := hS.exists_relative_pair hD1 hp hext hPD hR h13
  obtain ⟨R, T, hRmax, hTmax, hRM, hTM, hcard, hmaximal⟩ :=
    exists_relative_maximal_invariant_pair D M R₀ T' hR₀ hT' hR₀M hT'M
  have hRT : R ⊓ T ≠ ⊥ := by
    intro hbot
    apply hR₀T'
    refine Subgroup.eq_of_le_of_card_ge bot_le ?_ |>.symm
    simpa only [hbot, card_bot] using hcard
  have hglobalize : ∀ T₁ : Subgroup G, invariantTwoMaximalWithin D M T₁ →
      rankTwoMaximalInvariantTwoSubgroup D T₁ := fun T₁ hT₁ => (hglob T₁ hT₁).1
  have hcontains : ∀ x : G, x ∈ centralizer (D : Set G) → orderOf x = p → x ∈ D :=
    fun x hxC hxo => hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCD hxC
      (by rw [← hxo]; exact pow_orderOf_eq_one x)
  have hint := relative_maximal_pair_intersection_eq_overgroup_intersection D M R T hDM hRmax
    hTmax hRM hTM hmaximal hglobalize
  obtain ⟨hlocal, hDH⟩ := maximal_pair_intersection_normalizer_twoLocal D R T hRmax hTmax hRT
  exact hX p hp P M D hext hPD hDab R T hRmax hTmax hRM hTM hRT hint hmaximal hlocal
    (pCoreOf_normalizer_inf_eq_of_relativePair hDM hRmax hTmax hRM hTM hint hRT hmaximal
      hglobalize) hDH
    (hS.pRank_normalizer_inf_eq_two hD1 hp hext hPD hR h13 hRmax hTmax hRM hTM hRT hint
      hmaximal)
    (relative_pair_intersection_normalizer_escapes M R T hRmax.1 hRM hTM hint)
    (relative_maximal_pair_intersection_normalizer_not_prime_constrained p hprime hodd D M R T
      (P.isPGroup'.to_le hDP) hDM hRmax hTmax hRM hTM hint hCD hmaximal hglobalize hcontains)

end CFSG.LocalAnalysis.RankFourTheoremC
