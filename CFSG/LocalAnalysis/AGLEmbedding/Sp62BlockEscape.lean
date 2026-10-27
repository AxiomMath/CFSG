module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Data
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactSp62Escape : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [Fact (Nat.Prime 3)] (K : Subgroup Y)
    (d : TauCeti.ValidLieTypeIndex), IsSpSixTwoIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ CFSG.Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      ¬ HasKlingenData 3 T Y₀ →
      ∃ x ∈ (T : Subgroup Y), orderOf x = 3 ∧ ¬ Subgroup.centralizer ({x} : Set Y) ≤ Y₀ ∧
        (∃ A : Subgroup Y, A ≤ (T : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y) ∧
          IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3) ∧
        ∃ W : Subgroup Y, W ≤ Subgroup.centralizer ({x} : Set Y) ∧
          Nonempty (W ≃* alternatingGroup (Fin 6))

@[expose] def StmtSp62Escape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ¬ HasKlingenData 3 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpSixTwoIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
    ∃ x ∈ R, orderOf x = 3 ∧ ¬ Subgroup.centralizer ({x} : Set G) ⊓ H ≤ M ∧
      (∃ A : Subgroup G, A ≤ R ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsElemAbelian 3 A ∧
        Nat.card A = 3 ^ 3) ∧
      ∃ (W : Subgroup G) (φ : W →* alternatingGroup (Fin 6)),
        W ≤ Subgroup.centralizer ({x} : Set G) ⊓ H ∧ Function.Surjective φ

theorem stmtSp62Escape_of (hSoc : StmtChevTwoSocle) (hKE : KFactSp62Escape) :
    StmtSp62Escape := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  obtain ⟨hZ, -, ⟨eK⟩, -⟩ := hSoc G 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inl ⟨rfl, hd⟩) e
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  obtain ⟨xb, hxT, hx3, hxY, ⟨A, hAT, hA, hAc⟩, ⟨W₀, hW₀, ⟨eW⟩⟩⟩ :=
    hKE _ K d hd (normal_of_forall_isComponentOf_eq hK huniq) ⟨eK⟩ hC Rbar _
      hcfg.red.three_le_pRank hcfg.red.weakCore_le hcfg.red.ne_top hKD
  rw [hcfg.rbar] at hxT hAT
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hRH : R ≤ H := hcfg.ext.le_H
  have hR3 : IsPGroup 3 R := hcfg.ext.isPGroup
  obtain ⟨a, haR, rfl⟩ := hxT
  replace haR : (a : G) ∈ R := Subgroup.mem_subgroupOf.mp haR
  have hao : orderOf (a : G) = 3 := by
    rw [← orderOf_mk_eq_of_isPGroup hRH hR3 haR]; exact hx3
  have he3 : IsPGroup 3 (Subgroup.zpowers a) :=
    (hR3.comap_subtype (K := H)).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr haR))
  have hlift : ∀ y ∈ Subgroup.centralizer ({π a} : Set (H ⧸ primeComplementCore (G := H) 3)),
      ∃ g : H, (g : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) ∧ π g = y := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq Nat.prime_three
      (primeComplementCore (G := H) 3) (primeComplementCore_coprime 3) he3 hy
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have := congrArg Subtype.val hg
    simpa using this
  refine ⟨(a : G), haR, hao, ?_, ?_, ?_⟩
  ·
    intro hle
    apply hxY
    intro y hy
    obtain ⟨g, hgC, rfl⟩ := hlift y hy
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, hle ⟨hgC, g.2⟩⟩, rfl⟩
  ·
    have hAR : A ≤ (R.subgroupOf H).map π := hAT.trans inf_le_left
    obtain ⟨E₁, hE₁R, hE₁map, hE₁, hE₁c⟩ := exists_isElemAbelian_lift Nat.prime_three
      (primeComplementCore (G := H) 3) (primeComplementCore_coprime 3)
      (hR3.comap_subtype (K := H)) hA hAR
    refine ⟨E₁.map H.subtype, le_inf ?_ ?_, elementary_abelian_map 3 hE₁ _, ?_⟩
    · exact (Subgroup.map_mono hE₁R).trans (Subgroup.map_subgroupOf_eq_of_le hRH).le
    · rintro _ ⟨b, hb, rfl⟩
      have hbR : ((b : H) : G) ∈ R := Subgroup.mem_subgroupOf.mp (hE₁R hb)
      have hbA : π b ∈ A := hE₁map ▸ Subgroup.mem_map_of_mem π hb
      have hcomm : π b * π a = π a * π b :=
        Subgroup.mem_centralizer_singleton_iff.mp (hAT hbA).2
      have hba : (b : H) * a = a * b := by
        have hb1 : (((b : H) * a : H) : G) ∈ R := by
          rw [Subgroup.coe_mul]; exact R.mul_mem hbR haR
        have hb2 : ((a * (b : H) : H) : G) ∈ R := by
          rw [Subgroup.coe_mul]; exact R.mul_mem haR hbR
        exact eq_of_mk_primeComplementCore_eq (H := H) hR3 hb1 hb2
          (by rw [map_mul, map_mul, hcomm])
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := congrArg Subtype.val hba
        simpa using this)
    · rw [Subgroup.card_map_of_injective H.subtype_injective, hE₁c, hAc]
  ·
    set W : Subgroup G := Subgroup.centralizer ({(a : G)} : Set G) ⊓ (W₀.comap π).map H.subtype
      with hW
    have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
    have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ W₀ := by
      rintro ⟨w, -, h, hh, rfl⟩
      exact hh
    refine ⟨W, (eW.toMonoidHom.comp ((π.comp (Subgroup.inclusion hWH)).codRestrict W₀ hφ₀)),
      le_inf inf_le_left hWH, ?_⟩
    refine eW.surjective.comp ?_
    intro l
    obtain ⟨g, hgC, hgl⟩ := hlift l (hW₀ l.2)
    have hgL : g ∈ W₀.comap π := by
      rw [Subgroup.mem_comap, hgl]
      exact l.2
    exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgl⟩

end CFSG.AGLEmbedding
