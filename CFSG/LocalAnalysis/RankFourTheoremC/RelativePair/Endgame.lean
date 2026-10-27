module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Endgame
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ConstrainedGlobalization
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairTwoCore
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Candidate

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.coprime_card_invariantTwoJoinIn_left (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) : p.Coprime (Nat.card (invariantTwoJoinIn D M)) := by
  classical
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  have hXc := coprime_card_pPrimeCoreIn_sup (p := p) (M := M) hN₀M
  have hX : invariantTwoJoinIn D M ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
    refine invariantTwoJoinIn_le_of_forall fun A hAM hA2 hDA => ?_
    obtain ⟨T₁, hAT₁, hT₁⟩ := exists_invariantTwoMaximalWithin_containing D M A hAM hA2 hDA
    exact hAT₁.trans (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T₁ hT₁).le
  exact hXc.of_dvd_right (Subgroup.card_dvd_of_le hX)

theorem ObstructionSetting.exists_mem_centralizer_map_le (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) {T A : Subgroup G}
    (hT : rankTwoMaximalInvariantTwoSubgroup D T) (hTM : T ≤ M) (hAM : A ≤ M)
    (hA2 : IsPGroup 2 A) (hDA : D ≤ normalizer (A : Set G)) :
    ∃ c : G, c ∈ centralizer (D : Set G) ∧ c ∈ M ∧ A.map (MulAut.conj c).toMonoidHom ≤ T := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hPM := hS.sylow_le hp hM
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hXc := coprime_card_pPrimeCoreIn_sup (p := p) (M := M) hN₀M
  have hPX := le_normalizer_pPrimeCoreIn_sup (p := p) hPM hPN₀
  obtain ⟨A', hAA', hA'⟩ := exists_invariantTwoMaximalWithin_containing D M A hAM hA2 hDA
  have hA'S := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp A' hA'
  have hTS := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T
    (global_invariant_two_maximal_is_maximal_within D M T hT hTM)
  obtain ⟨c, -, hcC, hc⟩ := exists_mem_centralizer_conj_eq_of_isSylowOf hprime
    (P.isPGroup'.to_le hDP) (hDP.trans hPX) hXc hA'S hTS hA'.2.2.1 hT.2.1
  refine ⟨c, hcC, hCD hcC, ?_⟩
  rw [← hc]
  exact Subgroup.map_mono hAA'

theorem ObstructionSetting.card_pCoreOf_lt_of_conj (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V) {n : G}
    (hnH : n ∈ H) (hnD : n ∈ normalizer (D : Set G))
    (hjoin : p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G))
    (hVT : ∃ T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T' ∧ V < T')
    (horb : ∃ S₁ : Subgroup G, ∀ g ∈ normalizer
      ((V.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G),
      (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pCoreOf 2 H ∨
        (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = S₁) :
    Nat.card (pCoreOf 2 H) < Nat.card (R ⊓ T : Subgroup G) := by
  classical
  by_contra hge
  push Not at hge
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S₁, hS₁⟩ := horb
  have hpair := hopt.pair
  obtain ⟨hVM, hVmax⟩ := hopt.invariantTwoMaximalWithin_H hd
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hpair.cand.base_le
  obtain ⟨hM, hDP, -, -⟩ := hd.ext.obstruction
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  obtain ⟨-, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.transitivity_data hD1 hp hd.ext hd.not_le_normalizer hR h13
  set φ := MulAut.conj n with hφ
  set Vs : Subgroup G := V.map φ.toMonoidHom with hVs
  set S₀ : Subgroup G := pCoreOf 2 H with hS₀
  have hDn : D.map φ.toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hnD
  have hHn : H.map φ.toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp (le_normalizer hnH)
  have hVsmax : invariantTwoMaximalWithin D H Vs := by
    have := invariantTwoMaximalWithin_map φ hVmax
    rwa [hDn, hHn] at this
  have hS₀Vs : S₀ ≤ Vs := invariantTwoMaximalWithin_contains_normal_two_subgroup D H Vs S₀ hDH
    hVsmax (pCoreOf_le 2 H) (pCoreOf_normal 2 H) (pCoreOf_isPGroup 2 H)
  obtain ⟨T', hT'max, hVT'⟩ := hVT
  have hTsmax : rankTwoMaximalInvariantTwoSubgroup D (T'.map φ.toMonoidHom) := by
    have := rankTwoMaximalInvariantTwoSubgroup_map D T' φ hT'max
    rwa [hDn] at this
  have hVsTs : Vs < T'.map φ.toMonoidHom :=
    (Subgroup.map_lt_map_iff_of_injective φ.injective).mpr hVT'
  set Ts : Subgroup G := T'.map φ.toMonoidHom with hTs
  set T₀ : Subgroup G := Ts ⊓ normalizer (Vs : Set G) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hTsmax.1.to_inf_left
  have hDVs : D ≤ normalizer (Vs : Set G) := hVsmax.2.2.1
  have hDT₀ : D ≤ normalizer (T₀ : Set G) :=
    common_normalizer_le_normalizer_inf D Ts _ hTsmax.2.1 (hDVs.trans le_normalizer)
  have hVsT₀ : Vs < T₀ :=
    pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two Ts Vs hTsmax.1 hVsTs
  have hT₀N : T₀ ≤ normalizer (Vs : Set G) := inf_le_right
  have hHN : normalizer (S₀ : Set G) = H := hopt.normalizer_pCoreOf_eq
  have hstab : ∀ t ∈ T₀, t ∈ normalizer (S₀ : Set G) → t ∈ Vs := by
    intro t htT₀ htN
    have hDNS₀ : D ≤ normalizer ((normalizer (S₀ : Set G) : Subgroup G) : Set G) := by
      rw [hHN]
      exact hDH.trans le_normalizer
    have hB2 : IsPGroup 2 (T₀ ⊓ normalizer (S₀ : Set G) : Subgroup G) := hT₀2.to_inf_left
    have hDB : D ≤ normalizer ((T₀ ⊓ normalizer (S₀ : Set G) : Subgroup G) : Set G) :=
      common_normalizer_le_normalizer_inf D T₀ _ hDT₀ hDNS₀
    have hBH : (T₀ ⊓ normalizer (S₀ : Set G) : Subgroup G) ≤ H := hHN ▸ inf_le_right
    have hVsB : Vs ≤ (T₀ ⊓ normalizer (S₀ : Set G) : Subgroup G) :=
      le_inf hVsT₀.le (hHN ▸ hVsmax.1)
    have := hVsmax.2.2.2 _ hBH hB2 hDB hVsB
    exact this ▸ (⟨htT₀, htN⟩ : t ∈ (T₀ ⊓ normalizer (S₀ : Set G) : Subgroup G))
  obtain ⟨t₁, ht₁T₀, ht₁Vs⟩ := IsConcreteLE.exists_of_lt hVsT₀
  have ht₁N : t₁ ∈ normalizer (Vs : Set G) := hT₀N ht₁T₀
  have ht₁S₀ : t₁ ∉ normalizer (S₀ : Set G) := fun h => ht₁Vs (hstab t₁ ht₁T₀ h)
  have hS₀t₁ : S₀.map (MulAut.conj t₁).toMonoidHom = S₁ := by
    rcases hS₁ t₁ ht₁N with h | h
    · exact absurd (mem_normalizer_iff_map_conj_eq.mpr h) ht₁S₀
    · exact h
  have hcover : ∀ t ∈ T₀, t ∈ Vs ∨ t₁⁻¹ * t ∈ Vs := by
    intro t htT₀
    rcases hS₁ t (hT₀N htT₀) with h | h
    · exact Or.inl (hstab t htT₀ (mem_normalizer_iff_map_conj_eq.mpr h))
    · refine Or.inr (hstab _ (T₀.mul_mem (T₀.inv_mem ht₁T₀) htT₀) ?_)
      exact inv_mul_mem_normalizer_of_map_conj_eq (h.trans hS₀t₁.symm)
  have hDfix : ∀ d ∈ D, d * t₁ * d⁻¹ * t₁⁻¹ ∈ Vs := by
    intro d hd'
    have hu : d * t₁ * d⁻¹ ∈ T₀ := (mem_normalizer_iff.mp (hDT₀ hd') t₁).mp ht₁T₀
    have huVs : d * t₁ * d⁻¹ ∉ Vs := by
      intro h
      apply ht₁Vs
      have h2 := (mem_normalizer_iff.mp (hDVs (D.inv_mem hd')) (d * t₁ * d⁻¹)).mp h
      have e : d⁻¹ * (d * t₁ * d⁻¹) * d⁻¹⁻¹ = t₁ := by group
      rwa [e] at h2
    rcases hcover _ hu with h | h
    · exact absurd h huVs
    · have h' := (mem_normalizer_iff.mp ht₁N (t₁⁻¹ * (d * t₁ * d⁻¹))).mp h
      have e : t₁ * (t₁⁻¹ * (d * t₁ * d⁻¹)) * t₁⁻¹ = d * t₁ * d⁻¹ * t₁⁻¹ := by group
      rwa [e] at h'
  have hVsc : p.Coprime (Nat.card Vs) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVsmax.2.1
    rw [hm]
    exact ((Nat.coprime_primes hprime Nat.prime_two).mpr (sigmaA_odd p hp)).pow_right m
  obtain ⟨t, htT₀, htC, ht⟩ := exists_mem_centralizer_of_quotient_fixed hprime hDp hDT₀
    hVsT₀.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hVsT₀.le).mpr hT₀N) hDVs hVsc
    ht₁T₀ hDfix
  have htVs : t ∉ Vs := fun h => ht₁Vs (by
    have e : t₁ = t * (t⁻¹ * t₁) := by group
    rw [e]
    exact Vs.mul_mem h ht)
  have hS₀sT₀ : S₀ ⊔ zpowers t ≤ T₀ := sup_le (hS₀Vs.trans hVsT₀.le) (zpowers_le.mpr htT₀)
  have hS₀s2 : IsPGroup 2 (S₀ ⊔ zpowers t : Subgroup G) := hT₀2.to_le hS₀sT₀
  have hDS₀s : D ≤ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G) := by
    refine (le_inf ?_ ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup S₀ (zpowers t))
    · exact hHN ▸ hDH
    · intro x hx
      exact centralizer_singleton_le_normalizer_zpowers t
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC x hx))
  have hS₀sM : S₀ ⊔ zpowers t ≤ M :=
    sup_le ((hopt.pCoreOf_le_V hd).trans hVM) (zpowers_le.mpr (hCD htC))
  have hlt : Nat.card S₀ < Nat.card (S₀ ⊔ zpowers t : Subgroup G) := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => htVs (hS₀Vs ?_))
    rw [h]
    exact mem_sup_right (mem_zpowers t)
  obtain ⟨a, haC, haM, haT⟩ := hS.exists_mem_centralizer_map_le hD1 hp hd.ext
    hd.not_le_normalizer hR h13 hd.maxT hd.le_T hS₀sM hS₀s2 hDS₀s
  have hDa : D.map (MulAut.conj a).toMonoidHom = D := map_conj_eq_of_mem_centralizer_subgroup haC
  have hTss : rankTwoMaximalInvariantTwoSubgroup D (Ts.map (MulAut.conj a).toMonoidHom) := by
    have := rankTwoMaximalInvariantTwoSubgroup_map D Ts (MulAut.conj a) hTsmax
    rwa [hDa] at this
  have hsub : (S₀ ⊔ zpowers t).map (MulAut.conj a).toMonoidHom ≤
      (Ts.map (MulAut.conj a).toMonoidHom) ⊓ T :=
    le_inf (Subgroup.map_mono (hS₀sT₀.trans inf_le_left)) haT
  have hcard : Nat.card S₀ <
      Nat.card ((Ts.map (MulAut.conj a).toMonoidHom) ⊓ T : Subgroup G) := by
    have h1 := Subgroup.card_le_of_le hsub
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective] at h1
    exact lt_of_lt_of_le hlt h1
  by_cases hTssM : Ts.map (MulAut.conj a).toMonoidHom ≤ M
  ·
    have hTsM : Ts ≤ M := (conjugate_subgroup_le_iff_of_conjugator_mem Ts M a haM).mp hTssM
    have hVsM : Vs ≤ M := hVsTs.le.trans hTsM
    have hVVs : V ⊔ Vs ≤ invariantTwoJoinIn D M :=
      sup_le (le_invariantTwoJoinIn hVM hpair.maximal.2.1 hpair.maximal.2.2.1)
        (le_invariantTwoJoinIn hVsM hVsmax.2.1 hVsmax.2.2.1)
    have hcop := hS.coprime_card_invariantTwoJoinIn_left hD1 hp hd.ext hd.not_le_normalizer hR h13
    exact (hprime.coprime_iff_not_dvd.mp hcop) (hjoin.trans (Subgroup.card_dvd_of_le hVVs))
  · have hmax := hd.maximal _ T hTss hd.maxT hTssM hd.le_T
    omega

theorem ObstructionSetting.false_of_card_pCoreOf_lt (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hV : Nat.card V = 4 * Nat.card (pCoreOf 2 H))
    (hlt : Nat.card (pCoreOf 2 H) < Nat.card (R ⊓ T : Subgroup G)) : False := by
  classical
  have hpair := hopt.pair
  have hVM : V ≤ M := (hopt.invariantTwoMaximalWithin_H hd).1
  have hSlt : (R ⊓ T : Subgroup G) < relPairBase R T :=
    pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two T (R ⊓ T) hd.maxT.1
      (inf_lt_of_rankTwoMaximal hd.maxR hd.maxT hd.not_le_R hd.le_T)
  have hSV : (R ⊓ T : Subgroup G) < V := lt_of_lt_of_le hSlt hpair.base_le
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hpair.maximal.2.1
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSV.le
  have hSpos : 0 < Nat.card (R ⊓ T : Subgroup G) := Nat.card_pos
  have hlt' : Nat.card (R ⊓ T : Subgroup G) < Nat.card V := Subgroup.card_lt_of_lt hSV
  have hk4 : k < 4 := by
    by_contra h
    push Not at h
    nlinarith
  have hk1 : 1 < k := by
    by_contra h
    push Not at h
    interval_cases k <;> omega
  have hk3 : k ≠ 3 := by
    intro h
    rw [h] at hk
    have h3 : 3 ∣ 2 ^ a := ⟨Nat.card (R ⊓ T : Subgroup G), by rw [← ha, hk]; ring⟩
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hk2 : k = 2 := by omega
  have hnormal : ((R ⊓ T : Subgroup G).subgroupOf V).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have h1 := Subgroup.card_mul_index ((R ⊓ T : Subgroup G).subgroupOf V)
    have h2 : Nat.card ((R ⊓ T : Subgroup G).subgroupOf V) = Nat.card (R ⊓ T : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSV.le).toEquiv
    rw [h2, hk, hk2] at h1
    exact Nat.eq_of_mul_eq_mul_left hSpos (by linarith)
  have hVS : V ≤ normalizer ((R ⊓ T : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSV.le).mp hnormal
  have hcand := hS.isRelPairCandidate hD1 hp hR h13 hd
  have hVle : V ≤ normalizer ((R ⊓ T : Subgroup G) : Set G) ⊓ M := le_inf hVS hVM
  obtain ⟨V₀, hVV₀, hmax⟩ := exists_invariantTwoMaximalWithin_containing D
    (normalizer ((R ⊓ T : Subgroup G) : Set G) ⊓ M) V hVle hpair.maximal.2.1
    hpair.maximal.2.2.1
  have hpair₀ : IsRelPairCandidatePair p M D R T (normalizer ((R ⊓ T : Subgroup G) : Set G)) V₀ :=
    ⟨hcand, hmax, hpair.base_le.trans hVV₀⟩
  have hcardV : Nat.card V₀ = Nat.card V :=
    le_antisymm (hopt.card_le _ _ hpair₀) (Subgroup.card_le_of_le hVV₀)
  have hcore := hopt.core_le _ _ hpair₀ hcardV
  rw [hd.twoCore] at hcore
  omega

end CFSG.LocalAnalysis.RankFourTheoremC
