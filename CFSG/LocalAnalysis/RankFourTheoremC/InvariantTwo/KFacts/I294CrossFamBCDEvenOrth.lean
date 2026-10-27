module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenIso
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.BCDEven

open CFSG.Open Subgroup Polynomial Module Submodule CFSG.LocalAnalysis.RankFourTheoremC
  QuadraticMap
open LinearMap (BilinForm)

section Group

variable {G₁ G₂ G : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂] [Group G] [Finite G]
  {p : ℕ} [hp : Fact p.Prime]

theorem pRank_centralizer_add_le (ι : G₁ × G₂ →* G) (hι : Function.Injective ι) (y₁ : G₁)
    (y₂ : G₂) :
    CFSG.Open.pRank p (centralizer ({y₁} : Set G₁)) +
        CFSG.Open.pRank p (centralizer ({y₂} : Set G₂)) ≤
      CFSG.Open.pRank p (centralizer ({ι (y₁, y₂)} : Set G)) := by
  have hp1 : 1 < p := hp.out.one_lt
  have h1 := pRank_top_prod_ge hp1 (A := centralizer ({y₁} : Set G₁))
    (A' := centralizer ({y₂} : Set G₂))
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h1
  let φ : centralizer ({y₁} : Set G₁) × centralizer ({y₂} : Set G₂) →* G :=
    ι.comp ((Subgroup.subtype _).prodMap (Subgroup.subtype _))
  have hφ : Function.Injective φ := by
    intro a b h
    have := hι h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst this)) (Subtype.ext (congrArg Prod.snd this))
  have h2 := CFSG.SectionRank.pRank_top_le_of_injective hp1 φ hφ
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (centralizer ({y₁} : Set G₁) ×
      centralizer ({y₂} : Set G₂))) ≤
      CFSG.Open.pRank p (centralizer ({ι (y₁, y₂)} : Set G)) := by
    refine (CFSG.SectionRank.pRank_le_map hp1 φ hφ ⊤).trans
      (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨⟨a, b⟩, -, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ha : y₁ * (a : G₁) = (a : G₁) * y₁ := by
      have := a.2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    have hb : y₂ * (b : G₂) = (b : G₂) * y₂ := by
      have := b.2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    show ι ((a : G₁), (b : G₂)) * ι (y₁, y₂) = ι (y₁, y₂) * ι ((a : G₁), (b : G₂))
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext ha.symm hb.symm
  omega

end Group

section Orth

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def resQ (Q : QuadraticForm K V) (D : Submodule K V) : QuadraticForm K D :=
  Q.comp D.subtype

theorem resQ_apply (D : Submodule K V) (x : D) : resQ Q D x = Q (x : V) := rfl

theorem polarBilin_resQ (D : Submodule K V) (x y : D) :
    polarBilin (resQ Q D) x y = polarBilin Q (x : V) (y : V) := by
  simp only [polarBilin_apply_apply, polar, resQ_apply, Submodule.coe_add]

theorem polarBilin_isRefl (Q : QuadraticForm K V) : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply, polar_comm] at h
  rwa [polarBilin_apply_apply]

theorem polarBilin_apply_of_mem_orthogonalGroup {f : V ≃ₗ[K] V}
    (hf : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x y : V) :
    polarBilin Q (f x) (f y) = polarBilin Q x y := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hf x y

theorem blockLE_mem_orth {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, polarBilin Q d c = 0) {g : D ≃ₗ[K] D}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (resQ Q D)) {g' : C ≃ₗ[K] C}
    (hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (resQ Q C)) :
    blockLE hDC g g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg hg' ⊢
  intro v
  obtain ⟨⟨d, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective v
  simp only [Submodule.coe_prodEquivOfIsCompl']
  rw [blockLE_apply, QuadraticMap.map_add Q ((g d : D) : V) ((g' c : C) : V),
    QuadraticMap.map_add Q (d : V) (c : V)]
  have h1 := hg d
  have h2 := hg' c
  rw [resQ_apply] at h1 h2
  have h3 : polar Q ((g d : D) : V) ((g' c : C) : V) = 0 := by
    rw [← polarBilin_apply_apply]
    exact hperp _ (g d).2 _ (g' c).2
  have h4 : polar Q (d : V) (c : V) = 0 := by
    rw [← polarBilin_apply_apply]
    exact hperp _ d.2 _ c.2
  rw [h1, h2, h3, h4]
  rfl

@[expose] noncomputable def blockHomO {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, polarBilin Q d c = 0) :
    TauCeti.QuadraticMap.orthogonalGroup (resQ Q D) ×
      TauCeti.QuadraticMap.orthogonalGroup (resQ Q C) →* TauCeti.QuadraticMap.orthogonalGroup Q
    where
  toFun gg := ⟨blockLE hDC gg.1 gg.2, blockLE_mem_orth hDC hperp gg.1.2 gg.2.2⟩
  map_one' := Subtype.ext (blockLE_one hDC)
  map_mul' a b := Subtype.ext (blockLE_mul hDC _ _ _ _)

theorem blockHomO_coe {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, polarBilin Q d c = 0)
    (gg : TauCeti.QuadraticMap.orthogonalGroup (resQ Q D) ×
      TauCeti.QuadraticMap.orthogonalGroup (resQ Q C)) :
    ((blockHomO hDC hperp gg : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) =
      blockLE hDC gg.1 gg.2 := rfl

theorem blockHomO_injective {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, polarBilin Q d c = 0) :
    Function.Injective (blockHomO hDC hperp) := by
  intro a b h
  have h1 := congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup Q => (x : V ≃ₗ[K] V)) h
  obtain ⟨e1, e2⟩ := blockLE_injective hDC h1
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

@[expose] noncomputable def restrictIsoO (y : TauCeti.QuadraticMap.orthogonalGroup Q)
    (W : Submodule K V) (hW : ∀ x ∈ W, (y : V ≃ₗ[K] V) x ∈ W)
    (hW' : ∀ x ∈ W, (y : V ≃ₗ[K] V)⁻¹ x ∈ W) :
    TauCeti.QuadraticMap.orthogonalGroup (resQ Q W) :=
  ⟨LinearEquiv.ofSubmodules (y : V ≃ₗ[K] V) W W
      (le_antisymm (Submodule.map_le_iff_le_comap.2 hW)
        (fun x hx => ⟨(y : V ≃ₗ[K] V)⁻¹ x, hW' x hx, (y : V ≃ₗ[K] V).apply_symm_apply x⟩)),
    by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro x
      simp only [resQ_apply, LinearEquiv.ofSubmodules_apply]
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup y.2 x⟩

theorem blockHomO_restrictIsoO {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, polarBilin Q d c = 0)
    (y : TauCeti.QuadraticMap.orthogonalGroup Q) (hD : ∀ x ∈ D, (y : V ≃ₗ[K] V) x ∈ D)
    (hD' : ∀ x ∈ D, (y : V ≃ₗ[K] V)⁻¹ x ∈ D) (hC : ∀ x ∈ C, (y : V ≃ₗ[K] V) x ∈ C)
    (hC' : ∀ x ∈ C, (y : V ≃ₗ[K] V)⁻¹ x ∈ C) :
    blockHomO hDC hperp (restrictIsoO y D hD hD', restrictIsoO y C hC hC') = y := by
  refine Subtype.ext ?_
  rw [blockHomO_coe]
  ext v
  obtain ⟨⟨d, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective v
  simp only [Submodule.coe_prodEquivOfIsCompl']
  rw [blockLE_apply, map_add]
  rfl

end Orth

end CFSG.LocalAnalysis.RankFourTheoremC.BCDEven
