module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section NormalizerIntersection

variable {G : Type*} [Group G]

@[expose] def IsNormalizerIntersection (H : Subgroup G) : Prop :=
  ∃ (k : ℕ) (B : Fin k → Subgroup G), (∀ i, B i ≤ H ∧ IsPGroup 2 (B i)) ∧
    H = ⨅ i, Subgroup.normalizer (B i : Set G)

theorem iInf_normalizer_fin_cons {k : ℕ} (R : Subgroup G) (B : Fin k → Subgroup G) :
    (⨅ i : Fin (k + 1), Subgroup.normalizer (((Fin.cons R B : Fin (k + 1) → Subgroup G) i :
      Subgroup G) : Set G)) =
      Subgroup.normalizer (R : Set G) ⊓ ⨅ i : Fin k, Subgroup.normalizer (B i : Set G) := by
  apply le_antisymm
  · refine le_inf ?_ (le_iInf fun i => ?_)
    · simpa using iInf_le (fun i : Fin (k + 1) => Subgroup.normalizer
        (((Fin.cons R B : Fin (k + 1) → Subgroup G) i : Subgroup G) : Set G)) 0
    · simpa using iInf_le (fun i : Fin (k + 1) => Subgroup.normalizer
        (((Fin.cons R B : Fin (k + 1) → Subgroup G) i : Subgroup G) : Set G)) i.succ
  · refine le_iInf fun i => Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using (inf_le_right.trans (iInf_le (fun i : Fin k => Subgroup.normalizer
        (B i : Set G)) j) : Subgroup.normalizer (R : Set G) ⊓
        ⨅ i : Fin k, Subgroup.normalizer (B i : Set G) ≤ Subgroup.normalizer (B j : Set G))

theorem IsNormalizerIntersection.inf_normalizer {H : Subgroup G} (hH : IsNormalizerIntersection H)
    {R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hO : pCoreOf 2 H ≤ Subgroup.normalizer (R : Set G)) :
    IsNormalizerIntersection (H ⊓ Subgroup.normalizer (R : Set G)) := by
  obtain ⟨k, B, hB, hHeq⟩ := hH
  refine ⟨k + 1, Fin.cons R B, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact ⟨le_inf hRH Subgroup.le_normalizer, hR⟩
    · simp only [Fin.cons_succ]
      have hBj : B j ≤ pCoreOf 2 H :=
        le_pCoreOf_of_le_normalizer (hB j).1 (hHeq.le.trans (iInf_le _ j)) (hB j).2
      exact ⟨le_inf (hB j).1 (hBj.trans hO), (hB j).2⟩
  · rw [iInf_normalizer_fin_cons, inf_comm, ← hHeq]

end NormalizerIntersection

section MaximalPairs

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMaxUPair (M H U HU : Subgroup G) : Prop :=
  IsUPair M H U HU ∧
    ∀ U' HU' : Subgroup G, IsUPair M H U' HU' → U ≤ U' → HU ≤ HU' → U' = U ∧ HU' = HU

theorem exists_maximal_upair {M H U₀ HU₀ : Subgroup G} (h₀ : IsUPair M H U₀ HU₀) :
    ∃ U HU : Subgroup G, IsMaxUPair M H U HU ∧ U₀ ≤ U ∧ HU₀ ≤ HU := by
  classical
  let s : Set (Subgroup G × Subgroup G) := {p | IsUPair M H p.1 p.2 ∧ U₀ ≤ p.1 ∧ HU₀ ≤ p.2}
  have hne : s.Nonempty := ⟨(U₀, HU₀), h₀, le_rfl, le_rfl⟩
  obtain ⟨p, hp⟩ := Set.Finite.exists_maximal (Set.toFinite s) hne
  refine ⟨p.1, p.2, ⟨hp.1.1, fun U' HU' h1 h2 h3 => ?_⟩, hp.1.2.1, hp.1.2.2⟩
  have hmem : (U', HU') ∈ s := ⟨h1, hp.1.2.1.trans h2, hp.1.2.2.trans h3⟩
  have h4 := hp.2 hmem (show p ≤ (U', HU') from ⟨h2, h3⟩)
  exact ⟨le_antisymm h4.1 h2, le_antisymm h4.2 h3⟩

omit [Finite G] in
theorem IsUPair.map_conj {M H U HU : Subgroup G} (h : IsUPair M H U HU) {g : G} (hgH : g ∈ H)
    (hgM : g ∈ M) :
    IsUPair M H (U.map (MulAut.conj g).toMonoidHom) (HU.map (MulAut.conj g).toMonoidHom) := by
  have hfM : M.map (MulAut.conj g).toMonoidHom = M :=
    Unc25G2.map_conj_eq_of_mem_normalizer' (Subgroup.le_normalizer hgM)
  have hfH : H.map (MulAut.conj g).toMonoidHom = H :=
    Unc25G2.map_conj_eq_of_mem_normalizer' (Subgroup.le_normalizer hgH)
  exact ⟨h.1.map_equiv hfM, (Subgroup.map_mono h.2).trans hfH.le⟩

omit [Finite G] in
theorem map_conj_map_conj_inv (g : G) (X : Subgroup G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [Unc25G2.map_conj_conj, inv_mul_cancel, Unc25G2.map_conj_one]

omit [Finite G] in
theorem IsMaxUPair.map_conj {M H U HU : Subgroup G} (h : IsMaxUPair M H U HU) {g : G}
    (hgH : g ∈ H) (hgM : g ∈ M) :
    IsMaxUPair M H (U.map (MulAut.conj g).toMonoidHom) (HU.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨h.1.map_conj hgH hgM, fun U' HU' hp hU hHU => ?_⟩
  have hp' := hp.map_conj (H.inv_mem hgH) (M.inv_mem hgM)
  have hU' : U ≤ U'.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hU
    rwa [map_conj_map_conj_inv] at this
  have hHU' : HU ≤ HU'.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hHU
    rwa [map_conj_map_conj_inv] at this
  obtain ⟨e1, e2⟩ := h.2 _ _ hp' hU' hHU'
  have hinv : ∀ X : Subgroup G, (X.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = X := by
    intro X
    have := map_conj_map_conj_inv g⁻¹ X
    rwa [inv_inv] at this
  constructor
  · rw [← e1, hinv]
  · rw [← e2, hinv]

theorem exists_maxUPair_le_sylow {M H S U₀ HU₀ : Subgroup G} (hS : IsSylowTwoOf S (H ⊓ M))
    (h₀ : IsUPair M H U₀ HU₀) :
    ∃ U HU : Subgroup G, IsMaxUPair M H U HU ∧ U ≤ S ∧ Nat.card U₀ ≤ Nat.card U := by
  obtain ⟨U₁, HU₁, hmax, hU₁, -⟩ := exists_maximal_upair h₀
  have hU₁M : U₁ ≤ M := hmax.1.1.1.1
  have hU₁H : U₁ ≤ H := hmax.1.1.2.1.trans hmax.1.2
  have hU₁p : IsPGroup 2 U₁ := hmax.1.1.1.2.2.1
  obtain ⟨S', hUS', hS'⟩ := exists_isSylowTwoOf_of_le (le_inf hU₁H hU₁M) hU₁p
  obtain ⟨h, hh, hSS'⟩ := hS.exists_conj hS'
  have hhH : h ∈ H := (hh : h ∈ H ⊓ M).1
  have hhM : h ∈ M := (hh : h ∈ H ⊓ M).2
  refine ⟨U₁.map (MulAut.conj h⁻¹).toMonoidHom, HU₁.map (MulAut.conj h⁻¹).toMonoidHom,
    hmax.map_conj (H.inv_mem hhH) (M.inv_mem hhM), ?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hUS'
    rw [hSS', map_conj_map_conj_inv] at h1
    exact h1
  · have hinj : Function.Injective (MulAut.conj h⁻¹).toMonoidHom := (MulAut.conj h⁻¹).injective
    rw [Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_le_of_le hU₁

end MaximalPairs

section Saturation

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem upair_saturation (h : UniqueSetting G T M) {H S : Subgroup G} {z : G}
    (hT : Tuple25 T M H S z) {k : ℕ} (B : Fin k → Subgroup G)
    (hB : ∀ i, B i ≤ H ∧ IsPGroup 2 (B i)) (hH : H = ⨅ i, Subgroup.normalizer (B i : Set G))
    {U HU : Subgroup G} (hmax : IsMaxUPair M H U HU) (hUS : U ≤ S) :
    (∀ Q₁ : Subgroup G, Q₁ ≤ H → IsPGroup 2 Q₁ →
        HU ≤ Subgroup.normalizer (Q₁ : Set G) → Q₁ ≤ pCoreOf 2 HU) ∧
      pCoreOf 2 H ≤ pCoreOf 2 HU ∧ H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G) = HU ∧
      IsSylowTwoOf U HU ∧ pCoreOf 2 HU ≤ U ∧ z ∈ pCoreOf 2 HU := by
  obtain ⟨hpair, hmax'⟩ := hmax
  have hHUH : HU ≤ H := hpair.2
  have hUHU : U ≤ HU := hpair.1.2.1
  have hQHU : pCoreOf 2 HU ≤ HU := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 HU
  have hQ2 : IsPGroup 2 (pCoreOf 2 HU) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU
  have hHUN : HU ≤ Subgroup.normalizer (pCoreOf 2 HU : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU
  have hbang : ∀ Q₁ : Subgroup G, Q₁ ≤ H → IsPGroup 2 Q₁ →
      HU ≤ Subgroup.normalizer (Q₁ : Set G) → Q₁ ≤ pCoreOf 2 HU := by
    intro Q₁ hQ₁H hQ₁ hnorm
    have h3 := (hmax' U (HU ⊔ Q₁) (lemma253_two hpair hQ₁H hQ₁ hnorm) le_rfl le_sup_left).2
    have hQ₁HU : Q₁ ≤ HU := le_sup_right.trans h3.le
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q₁ HU hQ₁HU
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQ₁HU).mpr hnorm) hQ₁
  have hR₀2 : IsPGroup 2 (pCoreOf 2 H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hR₀H : pCoreOf 2 H ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hHR₀ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hO2H : pCoreOf 2 H ≤ pCoreOf 2 HU := hbang _ hR₀H hR₀2 (hHUH.trans hHR₀)
  have hchar1 : CharTwo (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) :=
    lemma253_one h B hB hH hpair hO2H
  have hHUHN : HU ≤ H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G) := le_inf hHUH hHUN
  have hQHN : pCoreOf 2 (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) = pCoreOf 2 HU := by
    refine le_antisymm ?_ ?_
    · exact hbang _ ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_left)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
        (hHUHN.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
    · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _
        (hQHU.trans hHUHN)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hQHU.trans hHUHN)).mpr inf_le_right) hQ2
  have hpair' : IsUPair M H U (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) :=
    ⟨⟨hpair.1.1, hUHU.trans hHUHN, by rw [hQHN]; exact hpair.1.2.2.1, hchar1,
      fun hM => hpair.1.2.2.2.2 (hHUHN.trans hM)⟩, inf_le_left⟩
  have hHNeq : H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G) = HU :=
    (hmax' U _ hpair' le_rfl hHUHN).2
  have hUsyl : IsSylowTwoOf U HU := by
    obtain ⟨U₁, hUU₁, hU₁⟩ := exists_isSylowTwoOf_of_le hUHU hpair.1.1.2.2.1
    have hpair₁ : IsUPair M H U₁ HU :=
      ⟨⟨hpair.1.1.of_le hU₁.isPGroup hUU₁, hU₁.le, hpair.1.2.2.1, hpair.1.2.2.2.1,
        hpair.1.2.2.2.2⟩, hHUH⟩
    have := (hmax' U₁ HU hpair₁ hUU₁ le_rfl).1
    rwa [this] at hU₁
  have hQU : pCoreOf 2 HU ≤ U := hUsyl.le_of_normalizes hQHU hHUN hQ2
  have hzT : z ∈ centerOf T := hT.z_mem
  have hST : S ≤ T := hT.lt.le
  have hzcS : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hzT.2
  have hzS : z ∈ S := hT.center_le hzT
  have hzH : z ∈ H := hT.sylow.le hzS
  have hzQc : z ∈ Subgroup.centralizer (pCoreOf 2 HU : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hQU.trans hUS)) hzcS
  have hzQ : z ∈ pCoreOf 2 HU := by
    have hzHU : z ∈ HU := by
      rw [← hHNeq]
      exact ⟨hzH, Subgroup.centralizer_le_normalizer _ hzQc⟩
    exact hpair.1.2.2.2.1 ⟨hzHU, hzQc⟩
  exact ⟨hbang, hO2H, hHNeq, hUsyl, hQU, hzQ⟩

end Saturation

section CharTwoCore

variable {G : Type*} [Group G]

theorem charTwo_of_core_le {N V : Subgroup G} (hN : CharTwo N) (hQV : pCoreOf 2 N ≤ V)
    (hVN : V ≤ N) : CharTwo V := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hN hVN hQV

end CharTwoCore

section Transfer

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem pCoreOf_le_pCoreOf_of_sylow_le {H S J : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSJ : S ≤ J) (hJH : J ≤ H) : pCoreOf 2 H ≤ pCoreOf 2 J :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ J (hS.pCoreOf_le.trans hSJ)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hS.pCoreOf_le.trans hSJ)).mpr
      (hJH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)))
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)

theorem gamma_transfer_of_witness (h : UniqueSetting G T M) {H S J U₁ HU₁ : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hSJ : S ≤ J) (hJH : J ≤ H)
    (hpair : IsWitnessPair M U₁ HU₁) (hHU : HU₁ ≤ J)
    (hmax : IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U₁) :
    (IsGammaU M H → IsGammaU M J) ∧ (IsGamma2 M H → IsGamma2 M J) := by
  have hSH : IsSylowTwoOf S H := hH.isSylowTwoOf_of_inf h hS
  have hcore : pCoreOf 2 J ≠ ⊥ := by
    intro hbot
    have h1 := pCoreOf_le_pCoreOf_of_sylow_le hSH hSJ hJH
    rw [hbot, le_bot_iff] at h1
    exact hH.isGamma.1 h1
  have hJΓ : IsGamma M J := hpair.isGamma_of_le hHU hcore
  refine ⟨fun hU => ?_, fun h2 => ?_⟩
  · have hTop : IsGammaTop M J := hpair.isGammaTop_of_le hHU hcore (hmax hU)
    exact (hH.overgroup_of_sylow_le h hS hJΓ hSJ (Or.inr ⟨hU, hTop⟩)).2.2.2.2 hU hTop
  · exact (hH.overgroup_of_sylow_le h hS hJΓ hSJ (Or.inl h2)).2.2.2.1 h2

theorem lemma253_conclusion_of_witness (h : UniqueSetting G T M) {H S : Subgroup G} {z : G}
    (ht : Tuple25 T M H S z) {K U₁ HU₁ : Subgroup G} (hK : IsComponentIn K H)
    (hKB : ¬ fusionIsBenderGroup ↥K) (hpair : IsWitnessPair M U₁ HU₁) (hHU : HU₁ ≤ K ⊔ S)
    (hmax : IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U₁) :
    IsComponentIn K H ∧ ¬ fusionIsBenderGroup ↥K ∧ IsComponentIn K (K ⊔ S) ∧
      (IsGammaU M H → IsGammaU M (K ⊔ S)) ∧ (IsGamma2 M H → IsGamma2 M (K ⊔ S)) := by
  have hJH : K ⊔ S ≤ H := sup_le hK.1 ht.le_H
  obtain ⟨h1, h2⟩ := gamma_transfer_of_witness h ht.gamma0 ht.sylow_inf le_sup_right hJH hpair
    hHU hmax
  exact ⟨hK, hKB, BenderBranch.isComponentIn_of_le hK le_sup_left hJH, h1, h2⟩

omit [Finite G] in
theorem exists_upair_with_max {M H : Subgroup G} (hH : IsGamma0 M H) :
    ∃ U₀ HU₀ : Subgroup G, IsUPair M H U₀ HU₀ ∧
      (IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U₀) := by
  by_cases hU : IsGammaU M H
  · obtain ⟨-, U₀, HU₀, hp, hle, hmax⟩ := hU.1
    exact ⟨U₀, HU₀, ⟨hp, hle⟩, fun _ => hmax⟩
  · obtain ⟨-, U₀, HU₀, hp, hle⟩ := hH.isGamma
    exact ⟨U₀, HU₀, ⟨hp, hle⟩, fun h => absurd h hU⟩

theorem exists_maxUPair_of_gamma0 {M H S : Subgroup G} (hH : IsGamma0 M H)
    (hS : IsSylowTwoOf S (H ⊓ M)) :
    ∃ U HU : Subgroup G, IsMaxUPair M H U HU ∧ U ≤ S ∧
      (IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U) := by
  obtain ⟨U₀, HU₀, h₀, hmax₀⟩ := exists_upair_with_max hH
  obtain ⟨U, HU, hmax, hUS, hcard⟩ := exists_maxUPair_le_sylow hS h₀
  exact ⟨U, HU, hmax, hUS, fun hU V hV => (hmax₀ hU V hV).trans hcard⟩

end Transfer

section Reduction

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Tuple25.of_witness_le (h : UniqueSetting G T M) {H S X U₁ HU₁ : Subgroup G} {z : G}
    (ht : Tuple25 T M H S z) (hSX : S ≤ X) (hXH : X ≤ H) (hpair : IsWitnessPair M U₁ HU₁)
    (hHU : HU₁ ≤ X)
    (hmax : IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U₁) :
    Tuple25 T M X S z := by
  have hcore : pCoreOf 2 X ≠ ⊥ := by
    intro hbot
    have h1 := pCoreOf_le_pCoreOf_of_sylow_le ht.sylow hSX hXH
    rw [hbot, le_bot_iff] at h1
    exact ht.gamma0.isGamma.1 h1
  have hXΓ : IsGamma M X := hpair.isGamma_of_le hHU hcore
  rcases ht.gamma0 with hU | h2
  · have hTop : IsGammaTop M X := hpair.isGammaTop_of_le hHU hcore (hmax hU)
    obtain ⟨h0, hS1, hS2, -, -⟩ :=
      ht.gamma0.overgroup_of_sylow_le h ht.sylow_inf hXΓ hSX (Or.inr ⟨hU, hTop⟩)
    exact ⟨h0, hS2, hS1, ht.center_le, ht.lt, ht.z_mem, ht.z_ne_one, ht.z_sq⟩
  · obtain ⟨h0, hS1, hS2, -, -⟩ :=
      ht.gamma0.overgroup_of_sylow_le h ht.sylow_inf hXΓ hSX (Or.inl h2)
    exact ⟨h0, hS2, hS1, ht.center_le, ht.lt, ht.z_mem, ht.z_ne_one, ht.z_sq⟩

theorem reduction_step (h : UniqueSetting G T M) {H S : Subgroup G} {z : G}
    (ht : Tuple25 T M H S z) (hHn : IsNormalizerIntersection H) {U HU R : Subgroup G}
    (hmaxP : IsMaxUPair M H U HU)
    (hmaxU : IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U)
    (hRH : R ≤ H) (hR2 : IsPGroup 2 R) (hSR : S ≤ Subgroup.normalizer (R : Set G))
    (hHUR : HU ≤ Subgroup.normalizer (R : Set G))
    (hOR : pCoreOf 2 H ≤ Subgroup.normalizer (R : Set G))
    (hRne : ¬ H ≤ Subgroup.normalizer (R : Set G)) :
    Tuple25 T M (H ⊓ Subgroup.normalizer (R : Set G)) S z ∧
      IsNormalizerIntersection (H ⊓ Subgroup.normalizer (R : Set G)) ∧
      (IsGammaU M H → IsGammaU M (H ⊓ Subgroup.normalizer (R : Set G))) ∧
      (IsGamma2 M H → IsGamma2 M (H ⊓ Subgroup.normalizer (R : Set G))) ∧
      Nat.card ↥(H ⊓ Subgroup.normalizer (R : Set G)) < Nat.card ↥H := by
  have hSX : S ≤ H ⊓ Subgroup.normalizer (R : Set G) := le_inf ht.le_H hSR
  have hHUX : HU ≤ H ⊓ Subgroup.normalizer (R : Set G) := le_inf hmaxP.1.2 hHUR
  obtain ⟨c1, c2⟩ := gamma_transfer_of_witness h ht.gamma0 ht.sylow_inf hSX inf_le_left
    hmaxP.1.1 hHUX hmaxU
  refine ⟨Tuple25.of_witness_le h ht hSX inf_le_left hmaxP.1.1 hHUX hmaxU,
    hHn.inf_normalizer hRH hR2 hOR, c1, c2, ?_⟩
  exact Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left
    (fun heq => hRne (inf_eq_left.mp heq)))
end Reduction

end CFSG.QuasithinUnique
