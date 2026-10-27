module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityPair
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ConstrainedGlobalization
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem invariantTwoMaximalWithin_map {A K T : Subgroup G} (φ : MulAut G)
    (h : invariantTwoMaximalWithin A K T) :
    invariantTwoMaximalWithin (A.map φ.toMonoidHom) (K.map φ.toMonoidHom)
      (T.map φ.toMonoidHom) := by
  refine ⟨map_mono h.1, h.2.1.map φ.toMonoidHom, ?_, ?_⟩
  · have himage := Subgroup.map_mono (f := φ.toMonoidHom) h.2.2.1
    rwa [Subgroup.map_equiv_normalizer_eq] at himage
  · intro L hLK hL hAL hTL
    have hL' := hL.map φ.symm.toMonoidHom
    have hAL' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hAL
    rw [map_automorphism_symm_map, Subgroup.map_equiv_normalizer_eq] at hAL'
    have hLK' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hLK
    rw [map_automorphism_symm_map] at hLK'
    have hTL' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hTL
    rw [map_automorphism_symm_map] at hTL'
    have heq := h.2.2.2 (L.map φ.symm.toMonoidHom) hLK' hL' hAL' hTL'
    apply Subgroup.map_injective (f := φ.symm.toMonoidHom) φ.symm.injective
    rwa [map_automorphism_symm_map]

omit [Finite G] in
theorem sylow_coe_smul_eq_map {p : ℕ} (P : Sylow p G) (g : G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem IsCoreMaxLocal.smul {p : ℕ} (hp : 1 < p) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) (g : G) :
    IsCoreMaxLocal p (g • P) (M.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨rankThreeIsMaxTwoLocal_map hM.1 _, ?_⟩
  rw [sylow_coe_smul_eq_map, ← aschCore_map_automorphism 2 p hp]
  exact map_mono hM.2

theorem ExtremalObstruction.exists_mem_normalizer_zpowers_eq (hS : Setting G)
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
    hext.exists_mem_normalizer_not_mem_centralizer hS hD1 hp hPD hDab hCD
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

theorem not_normalizer_inf_le_map_conj_of_relativePair {p : ℕ} (hprime : p.Prime)
    {D M R T X : Subgroup G} (hDp : IsPGroup p D) (hDM : D ≤ M)
    (hCD : centralizer (D : Set G) ≤ M) (hXc : Nat.Coprime p (Nat.card X))
    (hDX : D ≤ normalizer (X : Set G))
    (hX : ∀ T₁ : Subgroup G, invariantTwoMaximalWithin D M T₁ → T₁ ≤ X)
    (hglob : ∀ T₁ : Subgroup G, invariantTwoMaximalWithin D M T₁ →
      rankTwoMaximalInvariantTwoSubgroup D T₁ ∧ normalizer (T₁ : Set G) ≤ M)
    (hRmax : rankTwoMaximalInvariantTwoSubgroup D R)
    (hTmax : rankTwoMaximalInvariantTwoSubgroup D T) (hRM : ¬ R ≤ M) (hTM : T ≤ M)
    (hmaximal : ∀ R' T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D R' →
      rankTwoMaximalInvariantTwoSubgroup D T' → ¬ R' ≤ M → T' ≤ M →
        Nat.card (R' ⊓ T' : Subgroup G) ≤ Nat.card (R ⊓ T : Subgroup G))
    {g : G} (hgN : g ∈ normalizer (D : Set G)) (hgM : g ∉ M) :
    ¬ normalizer ((R ⊓ T : Subgroup G) : Set G) ≤ M.map (MulAut.conj g).toMonoidHom := by
  intro hHM
  set H := normalizer ((R ⊓ T : Subgroup G) : Set G) with hH
  set φ := MulAut.conj g with hφ
  have hDg : D.map φ.toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hgN
  have hDg' : D.map φ.symm.toMonoidHom = D := by
    have := map_automorphism_symm_map D φ
    rwa [hDg] at this
  have hDH : D ≤ H := common_normalizer_le_normalizer_inf D R T hRmax.2.1 hTmax.2.1
  obtain ⟨T₁, hTHT₁, hT₁⟩ := exists_invariantTwoMaximalWithin_containing D H (T ⊓ H)
    inf_le_right hTmax.1.to_inf_left
    (common_normalizer_le_normalizer_inf D T H hTmax.2.1 (hDH.trans le_normalizer))
  have hT₁M : T₁ ≤ M := le_of_normalizer_inf_le_of_relativePair hRmax hTmax hRM hTM hmaximal
    hT₁.2.1 hT₁.2.2.1 hTHT₁
  have hDMg : D ≤ M.map φ.toMonoidHom := hDg ▸ map_mono hDM
  obtain ⟨Tc, hT₁Tc, hTc⟩ := exists_invariantTwoMaximalWithin_containing D (M.map φ.toMonoidHom)
    T₁ (hT₁.1.trans hHM) hT₁.2.1 hT₁.2.2.1
  have hTc' : invariantTwoMaximalWithin D M (Tc.map φ.symm.toMonoidHom) := by
    have := invariantTwoMaximalWithin_map φ.symm hTc
    rwa [hDg', map_automorphism_symm_map] at this
  obtain ⟨hTc'max, hNTc'⟩ := hglob _ hTc'
  have hTcmax : rankTwoMaximalInvariantTwoSubgroup D Tc := by
    have := rankTwoMaximalInvariantTwoSubgroup_map D _ φ hTc'max
    rw [hDg] at this
    have h2 := map_automorphism_symm_map Tc φ.symm
    rw [MulEquiv.symm_symm] at h2
    rwa [h2] at this
  have hTcM : Tc ≤ M := by
    by_contra hTcM
    have hgrow := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two T (R ⊓ T)
      hTmax.1 (inf_lt_of_rankTwoMaximal hRmax hTmax hRM hTM)
    have hle : T ⊓ H ≤ Tc ⊓ T := le_inf (hTHT₁.trans hT₁Tc) inf_le_left
    exact lt_irrefl _ ((Subgroup.card_lt_of_lt hgrow).trans_le ((card_le_of_le hle).trans
      (hmaximal Tc T hTcmax hTmax hTcM hTM)))
  have hTcM' := global_invariant_two_maximal_is_maximal_within D M Tc hTcmax hTcM
  obtain ⟨c, hcC, hc⟩ := rank_two_maximal_two_subgroups_common_signalizer_transitivity p hprime
    D _ Tc X hDp hTc'max hTcmax hXc hDX (hX _ hTc') (hX _ hTcM')
  have hcomp : (MulAut.conj c).toMonoidHom.comp φ.symm.toMonoidHom =
      (MulAut.conj (c * g⁻¹)).toMonoidHom := by
    ext x
    simp [hφ, mul_assoc]
  have hmap : Tc.map (MulAut.conj (c * g⁻¹)).toMonoidHom = Tc := by
    rw [← hcomp, ← Subgroup.map_map]
    exact hc
  have hcg : c * g⁻¹ ∈ M := (hglob Tc hTcM').2 (mem_normalizer_iff_map_conj_eq.mpr hmap)
  apply hgM
  have : g = (c * g⁻¹)⁻¹ * c := by group
  rw [this]
  exact M.mul_mem (M.inv_mem hcg) (hCD hcC)

theorem ExtremalObstruction.pRank_normalizer_inf_eq_two (hS : Setting G) (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
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
    hext.transitivity_data hS hD1 hp hPD hR h13
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hDM : D ≤ M := hDP.trans hPM
  set H := normalizer ((R ⊓ T : Subgroup G) : Set G) with hH
  obtain ⟨hHlocal, hDH⟩ := maximal_pair_intersection_normalizer_twoLocal D R T hRmax hTmax hRT
  have hescape := relative_pair_intersection_normalizer_escapes M R T hRmax.1 hRM hTM hint
  refine le_antisymm ?_ (hext.rank_eq ▸ pRank_mono p hprime.one_lt hDH)
  by_contra h3
  push Not at h3
  obtain ⟨E, hEH, hE, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨P', hEP'⟩ := (elementary_isPGroup p E hE).exists_le_sylow
  obtain ⟨M', hM', hP'M', -, -, -⟩ := exists_isCoreMaxLocal hS hp P'
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
  obtain ⟨hP''M', hP''3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM''
  have hiso : IsIsolatedPlane p (P'' : Subgroup G) D := by
    refine ⟨hDP'', (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hDe, hDc,
      fun E' _ hE' hDE' => ?_⟩
    have hE'' : IsElemAbelian p E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E').1 hE'
    have hE'D : E' ≤ D := fun e he =>
      hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD
        (mem_centralizer_iff.mpr fun d hd => congrArg Subtype.val
          (hE''.1.is_comm.comm ⟨d, hDE' hd⟩ ⟨e, he⟩)) (hE''.2 e he)
    rw [← hDc]
    exact card_le_of_le hE'D
  obtain ⟨A, hAP'', hA, hAc⟩ := pRank_attained p (P'' : Subgroup G) (by rw [hP''3]; norm_num)
  rw [hP''3] at hAc
  obtain ⟨-, z'', hz''D, hz''1, hz''c, -, -⟩ := isolatedPlane_structure hprime P''.isPGroup' hiso
    hAP'' ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  obtain ⟨g, hgN, hgz⟩ := hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCD hzD hz1
    hzc hN₀M hz''D hz''1
  have hP''Mg : (P'' : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    refine (le_normalizer_zpowers_of_le_centralizer hz''c).trans ?_
    rw [hgz, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hN₀M
  have hMg := hM.smul hprime.one_lt g
  have hM'Mg : M' ≤ M.map (MulAut.conj g).toMonoidHom := by
    refine le_of_three_le_pRank_inf hD1 hp hMg hM'.1.1 ?_
    rw [← hP''3]
    exact pRank_mono p hprime.one_lt (le_inf hP''M' hP''Mg)
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

@[expose] def GL83RelativePairExclusion (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ R T : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D R →
        rankTwoMaximalInvariantTwoSubgroup D T → ¬ R ≤ M → T ≤ M → R ⊓ T ≠ ⊥ →
        R ⊓ M = R ⊓ T →
        (∀ R' T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D R' →
          rankTwoMaximalInvariantTwoSubgroup D T' → ¬ R' ≤ M → T' ≤ M →
            Nat.card (R' ⊓ T' : Subgroup G) ≤ Nat.card (R ⊓ T : Subgroup G)) →
        IsTwoLocal (normalizer ((R ⊓ T : Subgroup G) : Set G)) →
        pCoreOf 2 (normalizer ((R ⊓ T : Subgroup G) : Set G)) = R ⊓ T →
        D ≤ normalizer ((R ⊓ T : Subgroup G) : Set G) →
        CFSG.Open.pRank p (normalizer ((R ⊓ T : Subgroup G) : Set G)) = 2 →
        ¬ normalizer ((R ⊓ T : Subgroup G) : Set G) ≤ M →
        ¬ HasPrimeConstraint (G := normalizer ((R ⊓ T : Subgroup G) : Set G)) p → False

theorem gl83InvariantTwoContainment_of_relativePairExclusion (hS : Setting G)
    (hD1 : TheoremD1 G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hX : GL83RelativePairExclusion G) : GL83InvariantTwoContainment G := by
  intro p hp P M D hext hPD _ T _
  exfalso
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, -, -, -, -, -, hCD, hglob⟩ := hext.transitivity_data hS hD1 hp hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hDM : D ≤ M := hDP.trans (sylow_le_of_isCoreMaxLocal hS hp hM).1
  obtain ⟨R₀, T', hR₀, hT', hR₀M, hT'M, hR₀T'⟩ := hext.exists_relative_pair hS hD1 hp hPD hR h13
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
    fun x hxC hxo => hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD hxC
      (by rw [← hxo]; exact pow_orderOf_eq_one x)
  have hint := relative_maximal_pair_intersection_eq_overgroup_intersection D M R T hDM hRmax
    hTmax hRM hTM hmaximal hglobalize
  obtain ⟨hlocal, hDH⟩ := maximal_pair_intersection_normalizer_twoLocal D R T hRmax hTmax hRT
  exact hX p hp P M D hext hPD hDab R T hRmax hTmax hRM hTM hRT hint hmaximal hlocal
    (pCoreOf_normalizer_inf_eq_of_relativePair hDM hRmax hTmax hRM hTM hint hRT hmaximal
      hglobalize) hDH
    (hext.pRank_normalizer_inf_eq_two hS hD1 hp hPD hR h13 hRmax hTmax hRM hTM hRT hint
      hmaximal)
    (relative_pair_intersection_normalizer_escapes M R T hRmax.1 hRM hTM hint)
    (relative_maximal_pair_intersection_normalizer_not_prime_constrained p hprime hodd D M R T
      (P.isPGroup'.to_le hDP) hDM hRmax hTmax hRM hTM hint hCD hmaximal hglobalize hcontains)

end CFSG.LocalAnalysis.RankThreeTheoremC
