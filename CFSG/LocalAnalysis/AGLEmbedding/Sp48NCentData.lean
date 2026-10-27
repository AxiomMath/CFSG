module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentMSide
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NClose
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Data
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSp48
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NData

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure Sp48NCentInSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ : Subgroup Y) (z₁ z₂ σ : Y) :
    Prop where
  z₁_mem : z₁ ∈ centerOf T
  z₂_mem : z₂ ∈ centerOf T
  order₁ : orderOf z₁ = 3
  order₂ : orderOf z₂ = 3
  inf_eq_bot : Subgroup.zpowers z₁ ⊓ Subgroup.zpowers z₂ = ⊥
  σ_mem : σ ∈ Y₀
  σ_norm : σ ∈ Subgroup.normalizer (T : Set Y)
  σ₁ : σ * z₁ * σ⁻¹ ∈ Subgroup.zpowers z₂
  σ₂ : σ * z₂ * σ⁻¹ ∈ Subgroup.zpowers z₁
  outside : ∀ d ∈ centerOf T, d ∉ Subgroup.zpowers z₁ → d ∉ Subgroup.zpowers z₂ →
    ¬ Subgroup.centralizer ({d} : Set Y) ≤ Y₀
  involve : ∀ d ∈ centerOf T, d ∉ Subgroup.zpowers z₁ → d ∉ Subgroup.zpowers z₂ →
    ∃ L : Subgroup Y, L ≤ Subgroup.centralizer ({d} : Set Y) ∧ IsSimpleGroup L ∧ ⁅L, L⁆ = L ∧
      IsCaseTwoGroup 3 L ∧ ∃ x ∈ L, x ≠ 1 ∧ x ^ 3 = 1
  pRank_le : Open.pRank 3 T ≤ 3

@[expose] def KFactSp48NonsolvCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsSpFourEightIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      ¬ Group.IsSolvable Y₀ → ∃ z₁ z₂ σ : Y, Sp48NCentInSitu (T : Subgroup Y) Y₀ z₁ z₂ σ

@[expose] def StmtSp48NCentData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpFourEightIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
    ¬ Group.IsSolvable (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∃ z₁ z₂ σ : G, D1Sp48NCentData M H R z₁ z₂ σ

theorem stmtSp48NCentData_of (hSoc : StmtChevTwoSocle) (hKC : KFactSp48NonsolvCent) :
    StmtSp48NCentData := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent d hd e hns
  obtain ⟨hZ, -, ⟨eK⟩, -⟩ :=
    hSoc G 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inl ⟨rfl, hd⟩)) e
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  obtain ⟨z₁, z₂, σ, hI⟩ := hKC _ K d hd (normal_of_forall_isComponentOf_eq hK huniq) ⟨eK⟩ hC
    Rbar _ hcfg.red.three_le_pRank hcfg.red.weakCore_le hcfg.red.ne_top hns
  rw [hcfg.rbar] at hI
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hRH : R ≤ H := hcfg.ext.le_H
  have hR3 : IsPGroup 3 R := hcfg.ext.isPGroup
  have hNM : GLBPrimeCore 3 H ≤ M := hcfg.ext.primeCore_le
  set T := (R.subgroupOf H).map π with hT
  have hZmap : ((centerOf R).subgroupOf H).map π = centerOf T := map_inf_centralizer_eq hRH hR3
  have hlift : ∀ z ∈ centerOf T, ∃ a : H, (a : G) ∈ centerOf R ∧ π a = z := by
    intro z hz
    rw [← hZmap] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  have hinj : ∀ a b : H, (a : G) ∈ R → (b : G) ∈ R → π a = π b → a = b :=
    fun a b ha hb hab => eq_of_mk_primeComplementCore_eq hR3 ha hb hab
  have hzpow : ∀ (a b : H) (k : ℤ), (a : G) ∈ R → (b : G) ∈ R → (π a) ^ k = π b →
      (b : G) ∈ Subgroup.zpowers (a : G) := by
    intro a b k ha hb hk
    have hak : ((a ^ k : H) : G) ∈ R := by
      rw [Subgroup.coe_zpow]
      exact R.zpow_mem ha k
    have := hinj (a ^ k) b hak hb (by rw [map_zpow, hk])
    exact ⟨k, by rw [← this, Subgroup.coe_zpow]⟩
  have hord : ∀ a : H, (a : G) ∈ R → orderOf (π a) = orderOf (a : G) := fun a ha =>
    orderOf_mk_eq_of_isPGroup hRH hR3 ha
  obtain ⟨a₁, ha₁, rfl⟩ := hlift z₁ hI.z₁_mem
  obtain ⟨a₂, ha₂, rfl⟩ := hlift z₂ hI.z₂_mem
  obtain ⟨t, htM, htN, rfl⟩ := exists_lift_mem_normalizer_map hNM hRH hR3 hI.σ_mem hI.σ_norm
  have htR : ∀ x : H, (x : G) ∈ R → ((t * x * t⁻¹ : H) : G) ∈ R := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp htN (x : G)).mp hx
    simpa using this
  refine ⟨(a₁ : G), (a₂ : G), (t : G), ⟨ha₁, ha₂, ?_, ?_, ?_, ⟨t.2, htM⟩, htN, ?_, ?_, ?_, ?_,
    ?_⟩⟩
  · rw [← hord a₁ ha₁.1]; exact hI.order₁
  · rw [← hord a₂ ha₂.1]; exact hI.order₂
  · rw [eq_bot_iff]
    rintro g ⟨hg1, hg2⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg2
    have hb : a₁ ^ m = a₂ ^ n := Subtype.ext (by rw [Subgroup.coe_zpow, Subgroup.coe_zpow, hn])
    have hbR : ((a₁ ^ m : H) : G) ∈ R := by
      rw [Subgroup.coe_zpow]
      exact R.zpow_mem ha₁.1 m
    have hπb : π (a₁ ^ m) ∈ Subgroup.zpowers (π a₁) ⊓ Subgroup.zpowers (π a₂) :=
      ⟨⟨m, by rw [map_zpow]⟩, ⟨n, by rw [hb, map_zpow]⟩⟩
    rw [hI.inf_eq_bot, Subgroup.mem_bot] at hπb
    have h1 := hinj (a₁ ^ m) 1 hbR R.one_mem (by rw [hπb, map_one])
    rw [Subgroup.mem_bot]
    have := congrArg Subtype.val h1
    simpa using this
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hI.σ₁
    have h := hzpow a₂ (t * a₁ * t⁻¹) k ha₂.1 (htR a₁ ha₁.1) (by rw [hk, map_mul, map_mul, map_inv])
    simpa using h
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hI.σ₂
    have h := hzpow a₁ (t * a₂ * t⁻¹) k ha₁.1 (htR a₂ ha₂.1) (by rw [hk, map_mul, map_mul, map_inv])
    simpa using h
  · intro dd hdd hd1 hd2 hle
    set ê : H := ⟨dd, hRH hdd.1⟩ with hê
    have hêZ : π ê ∈ centerOf T := by
      rw [← hZmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hdd)
    have hê1 : π ê ∉ Subgroup.zpowers (π a₁) := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact hd1 (hzpow a₁ ê k ha₁.1 hdd.1 hk)
    have hê2 : π ê ∉ Subgroup.zpowers (π a₂) := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact hd2 (hzpow a₂ ê k ha₂.1 hdd.1 hk)
    obtain ⟨x, hx, hxY⟩ := Set.not_subset.mp (hI.outside _ hêZ hê1 hê2)
    have he3 : IsPGroup 3 (Subgroup.zpowers ê) :=
      (hR3.comap_subtype (K := H)).to_le
        (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hdd.1))
    obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq Nat.prime_three
      (primeComplementCore (G := H) 3) (primeComplementCore_coprime 3) he3 hx
    apply hxY
    have hgC : (g : G) ∈ Subgroup.centralizer ({dd} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have := congrArg Subtype.val hg
      simpa using this
    have hgM : (g : G) ∈ M := hle ⟨hgC, g.2⟩
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, hgM⟩, rfl⟩
  · intro dd hdd hd1 hd2
    set ê : H := ⟨dd, hRH hdd.1⟩ with hê
    have hêZ : π ê ∈ centerOf T := by
      rw [← hZmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hdd)
    have hê1 : π ê ∉ Subgroup.zpowers (π a₁) := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact hd1 (hzpow a₁ ê k ha₁.1 hdd.1 hk)
    have hê2 : π ê ∉ Subgroup.zpowers (π a₂) := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact hd2 (hzpow a₂ ê k ha₂.1 hdd.1 hk)
    obtain ⟨L, hLC, hLs, hLp, hLiso, x, hxL, hx1, hx3⟩ := hI.involve _ hêZ hê1 hê2
    have he3 : IsPGroup 3 (Subgroup.zpowers ê) :=
      (hR3.comap_subtype (K := H)).to_le
        (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hdd.1))
    set W : Subgroup G := Subgroup.centralizer ({dd} : Set G) ⊓ (L.comap π).map H.subtype
      with hW
    have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
    have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ L := by
      rintro ⟨w, -, h, hh, rfl⟩
      exact hh
    refine ⟨W, L, (π.comp (Subgroup.inclusion hWH)).codRestrict L hφ₀, inf_le_left, ?_, hLs,
      hLp, hLiso, x, hxL, hx1, hx3⟩
    intro l
    obtain ⟨g, hg, hgl⟩ := exists_mem_centralizer_mk_eq Nat.prime_three
      (primeComplementCore (G := H) 3) (primeComplementCore_coprime 3) he3 (hLC l.2)
    have hgC : (g : G) ∈ Subgroup.centralizer ({dd} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have := congrArg Subtype.val hg
      simpa using this
    have hgL : g ∈ L.comap π := by
      rw [Subgroup.mem_comap, hgl]
      exact l.2
    exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgl⟩
  · have h := hI.pRank_le
    rw [hT, pRank_map_mk_eq_pRank_map_subtype Nat.prime_three _ (primeComplementCore_coprime 3),
      Subgroup.map_subgroupOf_eq_of_le hRH] at h
    exact h

theorem d1Sp48NonsolvResidue_of_cent (hND : StmtSp48NData) (hNC : StmtSp48NCentData)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hMS : D1Sp48NCMSide) :
    D1Sp48NonsolvResidue := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e hns
  subst hp3
  obtain ⟨A, V, hD⟩ := hND G P M H R Rbar hcfg K hK huniq hcent d hd e hns
  obtain ⟨z₁, z₂, σ, hc⟩ := hNC G P M H R Rbar hcfg K hK huniq hcent d hd e hns
  exact hMS hcfg.loc hcfg.ext hD hc (hD.pCore_eq_bot h84 hD2)

theorem d1Sp48NonsolvResidue_closed_cent (hSchur : KFactChevTwoSurvivorSchur)
    (hK48 : KFactSp48Local) (hKN : KFactSp48NonsolvLocal) (hKC : KFactSp48NonsolvCent)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hCR : D1Sp48NCentResidue) :
    D1Sp48NonsolvResidue :=
  d1Sp48NonsolvResidue_of_cent
    (stmtSp48NData_of (stmtChevTwoSocle_of hSchur) (stmtSp48Surv_of hK48) hKN)
    (stmtSp48NCentData_of (stmtChevTwoSocle_of hSchur) hKC) h84 hD2 (d1Sp48NCMSide_of hCR)

end CFSG.AGLEmbedding
