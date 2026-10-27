module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux2
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def KlingenAlt (p : ℕ) [Fact p.Prime] (K : Type) [Group K] [Finite K]
    (T : Sylow p K) : Prop :=
  ∃ E D L : Subgroup K, E ≤ (T : Subgroup K) ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
    Nat.card (Subgroup.center E) = p ∧ D ≤ E ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
    (∀ y ∈ D, y ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) →
      y ∈ (Subgroup.center E).map E.subtype) ∧
    L ≤ Subgroup.centralizer (((Subgroup.center E).map E.subtype : Subgroup K) : Set K) ∧
    (∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
      StatedSL 2 (ZMod p) ≤ (L.subgroupOf (Subgroup.normalizer (E : Set K))).map
        (centerQuotientAction E e)) ∧
    GLBWeakCore p (T : Subgroup K) ⊔ Subgroup.normalizer (D : Set K) = ⊤ ∧
    GLBWeakCore p (T : Subgroup K) ⊔ L = ⊤

@[expose] def CaseThreeKFact (p : ℕ) [Fact p.Prime] (K : Type) [Group K] [Finite K] : Prop :=
  ∀ T : Sylow p K, GLBWeakCore p (T : Subgroup K) = ⊤ ∨
    (Open.pRank p (T : Subgroup K) ≤ 2 ∧
      (Subgroup.center K = ⊥ ∨ Nat.card (T : Subgroup K) = p ^ 3)) ∨
    KlingenAlt p K T

@[expose] def KlingenTransport : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] (R : Sylow p X) (X₀ K : Subgroup X)
    (T₀ : Sylow p K), (T₀ : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K →
    GLBWeakCore p (T₀ : Subgroup K) ≤ X₀.comap K.subtype → ¬ K ≤ X₀ →
    KlingenAlt p K T₀ → HasKlingenData p R X₀

theorem klingenTransport : KlingenTransport := by
  intro X _ _ p _ R X₀ K T₀ hT₀ hW hKX₀ hkl
  obtain ⟨E, D, L, hET, hEcard, hEexp, hZE, hDE, hDel, hDcard, hDC, hLC, ⟨e, hSL⟩, hgD, hgL⟩ :=
    hkl
  have hinj := K.subtype_injective
  let φ : E ≃* E.map K.subtype := Subgroup.equivMapOfInjective E K.subtype hinj
  have hφ : ∀ u : E, ((φ u : E.map K.subtype) : X) = ((u : K) : X) := fun _ => rfl
  have hZmap : ∀ w : Subgroup.center (E.map K.subtype), ∃ z : Subgroup.center E,
      ((w : E.map K.subtype) : X) = (((z : E) : K) : X) := by
    intro w
    refine ⟨(Subgroup.centerCongr φ).symm w, ?_⟩
    have h := hφ (((Subgroup.centerCongr φ).symm w : Subgroup.center E) : E)
    rw [← h]
    congr 2
    exact (congrArg Subtype.val ((Subgroup.centerCongr φ).apply_symm_apply w)).symm
  have hKle : ∀ Y : Subgroup K, GLBWeakCore p (T₀ : Subgroup K) ⊔ Y = ⊤ →
      Y ≤ X₀.comap K.subtype → K ≤ X₀ := by
    intro Y hY hYX x hx
    have h1 : (⟨x, hx⟩ : K) ∈ GLBWeakCore p (T₀ : Subgroup K) ⊔ Y := hY ▸ Subgroup.mem_top _
    exact (sup_le hW hYX) h1
  refine ⟨E.map K.subtype, D.map K.subtype, L.map K.subtype,
    (Subgroup.map_mono hET).trans (hT₀.le.trans inf_le_left), ?_, ?_, ?_,
    Subgroup.map_mono hDE, PreuniquenessRankFour.Helpers.elementary_abelian_map p hDel K.subtype,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hEcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEexp x hx, map_one]
  · rw [← hZE]
    exact (Nat.card_congr (Subgroup.centerCongr φ).toEquiv).symm
  · rw [Subgroup.card_map_of_injective hinj, hDcard]
  · rintro _ ⟨d, hd, rfl⟩ hdR
    have hdT : d ∈ Subgroup.centralizer ((T₀ : Subgroup K) : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have htR : (t : X) ∈ (R : Subgroup X) := (hT₀.le ⟨t, ht, rfl⟩).1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hdR _ htR)
    obtain ⟨z, hz, hzd⟩ := hDC d hd hdT
    refine ⟨Subgroup.centerCongr φ ⟨z, hz⟩, Subgroup.mem_center_iff.mpr ?_, ?_⟩
    · intro g
      exact Subgroup.mem_center_iff.mp (Subgroup.centerCongr φ ⟨z, hz⟩).2 g
    · show (((Subgroup.centerCongr φ ⟨z, hz⟩ : Subgroup.center (E.map K.subtype)) :
          E.map K.subtype) : X) = (d : X)
      rw [← hzd]
      rfl
  · intro hN
    exact hKX₀ (hKle _ hgD fun x hx =>
      hN (Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hx)))
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz⟩ := hZmap ⟨w, hw⟩
    have hlz := Subgroup.mem_centralizer_iff.mp (hLC hl) ((z : E) : K) ⟨z, z.2, rfl⟩
    show ((w : E.map K.subtype) : X) * (l : X) = (l : X) * ((w : E.map K.subtype) : X)
    have hz' : ((w : E.map K.subtype) : X) = (((z : E) : K) : X) := hz
    rw [hz']
    exact congrArg Subtype.val hlz
  · intro hL
    exact hKX₀ (hKle _ hgL fun x hx => hL (Subgroup.mem_map_of_mem K.subtype hx))
  · refine ⟨_, statedSL_le_map_centerQuotientAction_of_mulEquiv φ e hSL ?_⟩
    intro g hgL' hgN
    refine ⟨(g : X), Subgroup.mem_map_of_mem K.subtype hgL',
      Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hgN), ?_⟩
    intro u v huv
    rw [hφ, hφ, huv]
    rfl

theorem isCyclic_center_of_config {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig p P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) :
    IsCyclic (Subgroup.center K) := by
  have h := hcfg.red.isCyclic_map_center hK (normal_of_forall_isComponentOf_eq hK huniq)
  let e := Subgroup.equivMapOfInjective (Subgroup.center K) K.subtype K.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem false_of_caseThreeKFact_of_red {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M H : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hred : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (hKD : ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hS2 : S2Lemma)
    (hKl : KlingenTransport) (hfact : CaseThreeKFact p K) : False := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ K := fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rbar hKn
    (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp := isPGroup_centralizer_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn hmem
  have hCR : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    IsPGroup.le_sylow_of_normal hCp Rbar
  have hRK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Rbar.isPGroup') ⟨x, hx⟩
    refine mem_sup_centralizer_of_pow hp hOut (n := n) ?_
    have h1 := pow_orderOf_eq_one
      (⟨x, hx⟩ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)))
    rw [hn] at h1
    exact congrArg Subtype.val h1
  have hnot := not_le_of_le_sup_centralizer hred hnc hCp hRK
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hS1 : Subgroup.center K = ⊥ → Open.pRank p (T₀ : Subgroup K) ≤ 2 → False := by
    intro hZ hT2
    have hC := centralizer_eq_bot_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn hmem hZ
    have h2 := pRank_le_two_of_centralizer_eq_bot T₀ hT₀ hC hRK hT2
    have h3 := hred.three_le_pRank
    omega
  rcases hfact T₀ with htop | ⟨hT2, hZ | hcard⟩ | hkl
  · exact hnot (le_of_weakCore_eq_top hred T₀ hT₀ htop)
  · exact hS1 hZ hT2
  · by_cases hZ : Subgroup.center K = ⊥
    · exact hS1 hZ hT2
    ·
      have : Group.IsPerfect K := ⟨hK.2.2.1⟩
      have hZp := isPGroup_center_of_isComponentOf hred.prime hred.core_eq_bot hK
      obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
      have hzT : (z : K) ∈ ⁅(T₀ : Subgroup K), (T₀ : Subgroup K)⁆ := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZp) z
        refine center_le_commutator_of_isPerfect T₀ z.2 ⟨k, ?_⟩
        have h1 := pow_orderOf_eq_one z
        rw [hk] at h1
        exact congrArg Subtype.val h1
      have hna : ∃ a ∈ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K),
          ∃ b ∈ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K),
            a * b ≠ b * a := by
        by_contra hall
        push Not at hall
        apply hz1
        have hcomm : ⁅(T₀ : Subgroup K), (T₀ : Subgroup K)⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hab := hall (a : _) (hT₀ ▸ Subgroup.mem_map_of_mem K.subtype ha)
            (b : _) (hT₀ ▸ Subgroup.mem_map_of_mem K.subtype hb)
          exact Subtype.ext hab.symm
        have hz' : (z : K) ∈ (⊥ : Subgroup K) := hcomm ▸ hzT
        exact Subtype.ext (Subgroup.mem_bot.mp hz')
      have hTcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 3 := by
        rw [← hT₀, Subgroup.card_map_of_injective K.subtype_injective, hcard]
      have hCcyc := isCyclic_centralizer_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot
        hKn hmem (hred.isCyclic_map_center hK hKn)
      have hCT : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤
          Subgroup.centralizer
            (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
              Subgroup (H ⧸ primeComplementCore (G := H) p)) : Set _) :=
        Subgroup.centralizer_le (fun _ hy => hy.2)
      have hΩ : ∀ c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
          c ^ p = 1 → c ∈ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) := by
        intro c hc hcp
        by_cases hc1 : c = 1
        · rw [hc1]; exact Subgroup.one_mem _
        · have hord : orderOf c = p := orderOf_eq_prime hcp hc1
          exact ⟨hCR hc, Subgroup.map_subtype_le _ (hcent c ⟨hCR hc, hc⟩ hord)⟩
      have h2 := hS2 _ p _ _ hTcard hna hCcyc hCT hΩ
      have h3 := hred.three_le_pRank.trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf_sup_centralizer hCR hRK))
      omega
  · exact hKD (hKl _ p Rbar _ K T₀ hT₀ (weakCore_le_comap hred T₀ hT₀) hnot hkl)

theorem false_of_caseThreeKFact {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig p P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (hKD : ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hS2 : S2Lemma)
    (hKl : KlingenTransport) (hfact : CaseThreeKFact p K) : False :=
  false_of_caseThreeKFact_of_red hcfg.red hK huniq hnc hcent hKD hOut hS2 hKl hfact

end CFSG.AGLEmbedding
