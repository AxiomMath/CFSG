module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)

theorem isSimpleGroup_of_equiv_S {K : Type} [Group K]
    (e : K ≃* CFSG.ComponentClassification.PSL3Four.S) : IsSimpleGroup K := by
  obtain ⟨θ, -⟩ := CFSG.ComponentClassification.PSL3Four.exact_model.2.1
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3)
      CFSG.ComponentClassification.PSL3Four.F4) :=
    BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact (e.trans (θ.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
      CFSG.ComponentClassification.PSL3Four.F4)))).isSimpleGroup

theorem isSolvable_normalizer_of_l34 (hSch : KFactCatalogSchreier)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {X : Type} [Group X] [Finite X]
    {K A : Subgroup X} (hKn : K.Normal) (hKc : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : A ≤ K) (hA9 : Nat.card A = 9) :
    Group.IsSolvable (Subgroup.normalizer (A : Set X)) := by
  have := hKn
  obtain ⟨e⟩ := he
  obtain ⟨eS⟩ := nonempty_equiv_S_of_index hd e
  have hsimple : IsSimpleGroup K := isSimpleGroup_of_equiv_S eS
  have hcardK : Nat.card K = 20160 := (Nat.card_congr eS.toEquiv).trans CFSG.ComponentClassification.PSL3Four.card_S
  have hdvd : 3 ^ 2 ∣ Nat.card K := by rw [hcardK]; norm_num
  have := hsimple
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative K := ⟨⟨hcomm⟩⟩
    have hpr : (Nat.card K).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [hcardK] at hpr
    norm_num at hpr
  have hOut : Group.IsSolvable (Outer K) := hSch K hsimple hnab ⟨TauCeti.CFSGIndex.lie d, ⟨e⟩⟩
  have hNK : Group.IsSolvable ((Subgroup.normalizer (A : Set X)).subgroupOf K) := by
    rw [Subgroup.subgroupOf_normalizer_eq hAK]
    have h1 : Nat.card (A.subgroupOf K) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
    have hcardA : Nat.card (A.subgroupOf K) = 3 ^ 2 := h1.trans (hA9.trans (by norm_num))
    exact CFSG.AGLEmbeddingD2.kFactL34NormalizerSolvable d hd K ⟨e⟩ (A.subgroupOf K) hcardA
  have hNKsolv : Group.IsSolvable ((Subgroup.normalizer (A : Set X)) ⊓ K : Subgroup X) :=
    CFSG.AGLEmbeddingD2.isSolvable_inf_of_subgroupOf hNK
  have hWsolv : Group.IsSolvable (((Subgroup.normalizer (A : Set X)) ⊓ K).subgroupOf
      (Subgroup.normalizer (A : Set X))) := by
    have e2 := Subgroup.subgroupOfEquivOfLe
      (inf_le_left : (Subgroup.normalizer (A : Set X)) ⊓ K ≤ Subgroup.normalizer (A : Set X))
    exact Group.isSolvable_of_surjective (f := e2.symm.toMonoidHom) e2.symm.surjective
  let ψ : X →* Outer K := (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal (H := K))
  have hker : ∀ x : X, ψ x = 1 → x ∈ K := by
    intro x hψ
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hψ
    have hcent : (c : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hc ⟨y, hy⟩)
      rw [MulAut.conjNormal_apply] at h1
      change (c : X) * y * (c : X)⁻¹ = x * y * x⁻¹ at h1
      calc y * ((c : X)⁻¹ * x) = (c : X)⁻¹ * ((c : X) * y * (c : X)⁻¹) * x := by group
        _ = (c : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
        _ = (c : X)⁻¹ * x * y := by group
    rw [hKc, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    exact hcent ▸ c.2
  let g : Subgroup.normalizer (A : Set X) →* Outer K :=
    ψ.comp (Subgroup.normalizer (A : Set X)).subtype
  let f : ((Subgroup.normalizer (A : Set X)) ⊓ K).subgroupOf (Subgroup.normalizer (A : Set X)) →*
      Subgroup.normalizer (A : Set X) :=
    ((Subgroup.normalizer (A : Set X)) ⊓ K).subgroupOf (Subgroup.normalizer (A : Set X)) |>.subtype
  have hle : g.ker ≤ f.range := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyK : (y : X) ∈ K := hker _ hy
    refine ⟨⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨y.2, hyK⟩)⟩, rfl⟩
  have := hOut
  have := hWsolv
  exact Group.isSolvable_of_ker_le_range f g hle

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.betaConf3_isPSolvable_of_le_inf
    {G : Type} [Group G] [Finite G]
    (hSch : KFactCatalogSchreier)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {Y : Subgroup G} (hY : Y ≤ H ⊓ M) :
    CFSG.HallHigman.IsPSolvable 3 ↥Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX₀ := hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hsolvX₀ : Group.IsSolvable (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) :
        Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hX₀]
    exact isSolvable_normalizer_of_l34 hSch hc.l34 hc.almostSimple.normal
      hc.almostSimple.centralizer_eq_bot hc.iso hc.le_K hc.almostSimple.card_A
  have : Group.IsSolvable (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) :
        Subgroup (H ⧸ primeComplementCore (G := H) 3)) := hsolvX₀
  let ι : Y →* H := Subgroup.inclusion (hY.trans inf_le_left)
  let φ : Y →* (H ⧸ primeComplementCore (G := H) 3) :=
    (QuotientGroup.mk' (primeComplementCore (G := H) 3)).comp ι
  have hrange : φ.range ≤ ((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
    rintro _ ⟨y, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hY y.2))
  have hφsolv : Group.IsSolvable φ.range := by
    have e := Subgroup.subgroupOfEquivOfLe hrange
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  refine isPSolvable_of_normal_coprime_quotient_solvable (N := φ.ker) ?_ ?_
  · have hinj : Function.Injective ι := Subgroup.inclusion_injective _
    have hle : φ.ker.map ι ≤ primeComplementCore (G := H) 3 := by
      rintro _ ⟨y, hy, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    have h1 : Nat.card (φ.ker.map ι) = Nat.card φ.ker := Subgroup.card_map_of_injective hinj
    have hdvd : Nat.card φ.ker ∣ Nat.card (primeComplementCore (G := H) 3) := by
      rw [← h1]
      exact Subgroup.card_dvd_of_le hle
    exact Nat.Coprime.coprime_dvd_right hdvd (primeComplementCore_coprime 3)
  · have e := QuotientGroup.quotientKerEquivRange φ
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem betaConf_isPSolvable_of_le_inf
    (hSch : KFactCatalogSchreier) {G : Type} [Group G] [Finite G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) {Y : Subgroup G} (hY : Y ≤ H ⊓ M) :
    CFSG.HallHigman.IsPSolvable 3 ↥Y :=
  CFSG.LocalAnalysis.RankThreeTheoremC.betaConf3_isPSolvable_of_le_inf hSch hc.toConf3 hY

theorem betaConf_isPSolvable_of_le_twoLocal
    (hSch : KFactCatalogSchreier) {G : Type} [Group G] [Finite G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : D2L34AllResidue P M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X)
    {Y : Subgroup G} (hY : Y ≤ N ⊓ M) : CFSG.HallHigman.IsPSolvable 3 ↥Y := by
  obtain ⟨N₁, E₀, hNN₁, -, hesc, hmax, -⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsidePrelim.D2L34BetaConf.exists_escape_of_not_isCyclic
      hc hstr hN hNM hXN hXM hX hXc
  obtain ⟨d₁, Rbar₁, K₁, hc₁⟩ := hAll E₀ N₁ E₀ hesc hmax
  have hY₁ : Y ≤ N₁ ⊓ M := le_inf ((hY.trans inf_le_left).trans hNN₁) (hY.trans inf_le_right)
  exact betaConf_isPSolvable_of_le_inf hSch hc₁ hY₁

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
