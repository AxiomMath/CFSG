module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Comp
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBPhase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

structure D1OneLieKZeroComp (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (P' : Sylow p G) (H₁ S : Subgroup G)
    (Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p))
    (L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) (T₁ : Sylow p L) : Prop where
  kzero : D1OneLieKZeroData p P M H R Rbar K P' H₁ S
  rbar : (Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) =
    (S.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))
  red : ReducedNongeneration p (H₁ ⧸ primeComplementCore (G := H₁) p) Rb₁
    (((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)))
  comp : IsComponentOf L ⊤
  normal : L.Normal
  le : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
    (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L
  center : Subgroup.center L = ⊥
  simple : IsSimpleGroup L
  nonabelian : ∃ a b : L, a * b ≠ b * a
  catalog : IsCatalogGroup L
  sylow : (T₁ : Subgroup L).map L.subtype =
    (Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L
  three_le_pRank : 3 ≤ Open.pRank p ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L)
  noncyclic : ¬ IsCyclic ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L :
    Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p))
  core_ne : GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤
  big : ¬ Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2
  borel_le : L ⊓ Subgroup.normalizer
      ((((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L :
        Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p))) :
        Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤
    ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))
  not_le : ¬ L ≤
    ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))
  others : ∀ L' : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L' ⊤ →
    L' ≠ L → L' ≤ ((H₁ ⊓ M).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))

namespace D1OneLieKZeroData

theorem exists_hom_center_quotient (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hL : IsComponentOf L ⊤)
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L) :
    ∃ (Y : Subgroup (L ⧸ Subgroup.center L)) (φ : Y →* K), Function.Surjective φ ∧
      p.Coprime (Nat.card φ.ker) := by
  have hd := hc.data
  have hp := hc.escape.prime
  obtain ⟨Rb₁, -, hred₁⟩ := hc.escape.reducedNongeneration
  set Jt := ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
    (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) with hJt
  obtain ⟨φ₀, hφs, hφk, -⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  have hZp : IsPGroup p (Subgroup.center L) :=
    isPGroup_center_of_isComponentOf hp hred₁.core_eq_bot hL
  set A : Subgroup L := Jt.subgroupOf L with hA
  let ι : A ≃* Jt := Subgroup.subgroupOfEquivOfLe hJL
  set ρ := (QuotientGroup.mk' (Subgroup.center L)).subgroupMap A with hρ
  set ψ : A →* K := φ₀.comp ι.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := hφs.comp ι.surjective
  have hker : ρ.ker ≤ ψ.ker := by
    intro a ha
    have haZ : (a : L) ∈ Subgroup.center L := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
      simpa [ρ] using h1
    have hmem : ((a : L) : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
        (Subgroup.center L).map L.subtype := ⟨a, haZ, rfl⟩
    have h1 := hc.eq_one_of_mem_of_normal (normal_map_center hLn) (hZp.map _) hmem
      (Subgroup.mem_subgroupOf.mp a.2)
    have ha1 : a = 1 := Subtype.ext (Subtype.ext h1)
    rw [ha1]
    exact ψ.ker.one_mem
  obtain ⟨φ, -, hφs', hφker⟩ :=
    exists_surjective_comp_eq ρ ((QuotientGroup.mk' _).subgroupMap_surjective A) ψ hψs hker
  refine ⟨A.map (QuotientGroup.mk' (Subgroup.center L)), φ, hφs', ?_⟩
  have h1 : Nat.card φ.ker ∣ Nat.card ψ.ker := by
    rw [hφker]
    exact Subgroup.card_map_dvd _ _
  have h2 : Nat.card ψ.ker ∣ Nat.card φ₀.ker := by
    rw [← Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  exact hφk.coprime_dvd_right (h1.trans h2)

theorem exists_comp_of_shape (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hT : KFactOneLieTorus) (hSch : KFactCatalogSchreier) (hcon : ¬ HasPrimeConstraint (G := H₁) p)
    (hIII : ∀ Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p), (Rb₁ : Subgroup _) =
        (S.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) →
      ReducedNongeneration p (H₁ ⧸ primeComplementCore (G := H₁) p) Rb₁
        (((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) →
      CatalogSimpleSections (H₁ ⧸ primeComplementCore (G := H₁) p) →
      ∀ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ → L.Normal →
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L →
      ¬ IsCyclic ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L :
        Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) →
      ¬ L ≤ ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) →
      (∀ c ∈ (Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓
          Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)),
        orderOf c = p → c ∈ (Subgroup.center L).map L.subtype) →
      ∀ T₁ : Sylow p L, (T₁ : Subgroup L).map L.subtype =
        (Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L →
      Subgroup.center L = ⊥ ∧ GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤) :
    ∃ (Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p))
      (L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) (T₁ : Sylow p L),
      D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁ := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  set Jt := ((nclIn H X).subgroupOf H₁).map π₁ with hJt
  set Xt := (X.subgroupOf H₁).map π₁ with hXt
  set St := (S.subgroupOf H₁).map π₁ with hSt
  obtain ⟨Rb₁, hRb₁, hred₁, hcat₁, hcomp₁, -, -, -, -⟩ :=
    hc.escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hd.cfg.glob.kProper hcon
  have hRbS : (Rb₁ : Subgroup _) = St := hRb₁
  obtain ⟨L, hL, hLn, hJL⟩ := hc.exists_component_le hSch hcon
  have : L.Normal := hLn
  have hXH₁ : X ≤ H₁ := hc.liftX_le_H₁
  have hXtJt : Xt ≤ Jt :=
    Subgroup.map_mono (Subgroup.comap_mono (le_nclIn (d1LiftX_le_H p H R K)))
  have hXtS : Xt ≤ St := Subgroup.map_mono (Subgroup.comap_mono hc.liftX_le)
  have hXtRL : Xt ≤ (Rb₁ : Subgroup _) ⊓ L := le_inf (hRbS ▸ hXtS) (hXtJt.trans hJL)
  have hnc : ¬ IsCyclic ((Rb₁ : Subgroup _) ⊓ L : Subgroup _) := fun hcyc =>
    hd.not_isCyclic_map hXH₁ (Subgroup.isCyclic_of_le hXtRL)
  have h3 : 3 ≤ Open.pRank p ((Rb₁ : Subgroup _) ⊓ L) := by
    refine le_trans ?_ (pRank_mono p hp hXtRL)
    rw [hXt, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le hXH₁]
    exact hd.three_le_pRank_d1LiftX hT
  have hNT : Subgroup.normalizer ((((Rb₁ : Subgroup _) ⊓ L : Subgroup _)) :
      Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤
      ((H₁ ⊓ M).subgroupOf H₁).map π₁ :=
    (normalizer_le_weakCore p inf_le_left (by omega)
      (h3.trans (pRank_mono p hp le_sup_left))).trans hred₁.weakCore_le
  have hLX : ¬ L ≤ ((H₁ ⊓ M).subgroupOf H₁).map π₁ :=
    not_le_of_normalizer_inf_le Rb₁ hNT hred₁.ne_top
  obtain ⟨T₁, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb₁
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  have hshape : Subgroup.center L = ⊥ ∧ GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤ ∧
      ∀ L' : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L' ⊤ → L' ≠ L →
        L' ≤ ((H₁ ⊓ M).subgroupOf H₁).map π₁ := by
    rcases hred₁.rankOne_or_center hL hnc with ⟨z, hzR, hzL, hzp, hzc, hN, hKX₀, -, hZ⟩ | hcent
    · exact ⟨hZ, hred₁.glbCore_ne_top_of_rankOne hN hKX₀ hT₁, fun L' hL' hne =>
        (le_centralizer_of_component_ne hL' hL hne).trans
          (hred₁.centralizer_le_of_rankOne hnc hzR hzL hzp hzc)⟩
    · obtain ⟨hZ, hΓ⟩ := hIII Rb₁ hRb₁ hred₁ hcat₁ L hL hLn hJL hnc hLX hcent T₁ hT₁
      exact ⟨hZ, hΓ, fun L' hL' hne => absurd (hred₁.eq_of_forall_mem_center hL hL' hcent) hne⟩
  obtain ⟨hZ, hΓ, hoth⟩ := hshape
  obtain ⟨hLs, hLnab, hLcat⟩ := simple_of_center_eq_bot hL hZ (hcomp₁ L hL).2.1
  have hbig : ¬ Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 := by
    have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hgZ : g ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun l => by
        have h1 := congrArg (fun f : MulAut L => f l) hg
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc l * g = g * l * g⁻¹ * g := by rw [h1]
          _ = g * l := by group
      rw [hZ, Subgroup.mem_bot] at hgZ
      exact hgZ
    have h1 := pRank_map_of_injective p hp (MulAut.conj : L →* MulAut L) hinj (⊤ : Subgroup L)
    have h2 : Open.pRank p ((⊤ : Subgroup L).map (MulAut.conj : L →* MulAut L)) ≤
        Open.pRank p (⊤ : Subgroup (MulAut L)) := pRank_mono p hp le_top
    have h4 : Open.pRank p (T₁ : Subgroup L) ≤ Open.pRank p (⊤ : Subgroup L) :=
      pRank_mono p hp le_top
    have h5 : Open.pRank p (T₁ : Subgroup L) = Open.pRank p ((Rb₁ : Subgroup _) ⊓ L) := by
      rw [← pRank_map_of_injective p hp L.subtype L.subtype_injective, hT₁]
    omega
  exact ⟨Rb₁, L, T₁,
    { kzero := hc, rbar := hRb₁, red := hred₁, comp := hL, normal := hLn, le := hJL,
      center := hZ, simple := hLs, nonabelian := hLnab, catalog := hLcat, sylow := hT₁,
      three_le_pRank := h3, noncyclic := hnc, core_ne := hΓ, big := hbig,
      borel_le := inf_le_right.trans hNT, not_le := hLX, others := hoth }⟩

end D1OneLieKZeroData

end CFSG.AGLEmbedding
