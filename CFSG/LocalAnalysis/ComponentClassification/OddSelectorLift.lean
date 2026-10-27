module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {k : Type*} [Field k] {m : ℕ}

theorem inner_le_range_conjAut : inner (projectiveSL m k) ≤ (conjAut m k).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective m k x
  exact ⟨_, conjAut_toGL g⟩

theorem ker_conjAut_le_center [Finite k] (hm : 3 ≤ m) :
    (conjAut m k).ker ≤ center (GL (Fin m) k) := by
  intro A hA
  obtain ⟨c, rfl⟩ := (UnbalancedCatalog.conjAut_eq_one_iff hm A).mp hA
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem component_lift [Finite k] (hm : 3 ≤ m) {H X : Subgroup (MulAut (projectiveSL m k))}
    (hH : H ≤ inner (projectiveSL m k)) (hX : CFSG.Assembly.IsComponentOf X H) :
    CFSG.Assembly.IsComponentOf ⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆
        (H.comap (conjAut m k)) ∧
      (⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆).map (conjAut m k) = X := by
  set c := conjAut m k with hc
  set G := H.comap c with hG
  let f : G →* H := (c.comp G.subtype).codRestrict H (fun g => g.2)
  have hf : ∀ g : G, (f g : MulAut (projectiveSL m k)) = c g := fun _ => rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨A, hA⟩ := inner_le_range_conjAut (hH hy)
    refine ⟨⟨A, show c A ∈ H by rw [hA]; exact hy⟩, Subtype.ext ?_⟩
    rw [hf]
    exact hA
  have hker : f.ker ≤ center G := by
    intro g hg
    have h1 : (g : GL (Fin m) k) ∈ c.ker := by
      rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val (show f g = 1 from hg)
      rwa [hf] at this
    have h2 := ker_conjAut_le_center hm h1
    rw [mem_center_iff] at h2 ⊢
    intro h
    exact Subtype.ext (h2 h)
  have hXH := hX.1
  have hM : CFSG.IsComponent (X.subgroupOf H) :=
    (isComponentOf_iff_isComponent_subgroupOf hXH).mp hX
  have : Group.IsPerfect (X.subgroupOf H) := hM.1.1
  set D := CatalogueBCentralQuotient.derivedPreimage f (X.subgroupOf H) with hD
  have hDmap := CatalogueBCentralQuotient.derivedPreimage_map f hsurj (X.subgroupOf H)
  have hDsub := CatalogueBCentralQuotient.derivedPreimage_subnormal f (X.subgroupOf H) hM.2
  have : Group.IsPerfect D :=
    CatalogueBCentralQuotient.derivedPreimage_perfect f hsurj hker (X.subgroupOf H)
  have hDq : CFSG.IsQuasisimple D :=
    (CatalogueBCentralQuotient.quasisimple_map_iff_of_perfect f hker D).2 (by
      rw [hDmap]; exact hM.1)
  have hpre : ((X.subgroupOf H).comap f).map G.subtype = X.comap c := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hg'
    · intro hg
      refine ⟨⟨g, show c g ∈ H from hXH hg⟩, ?_, rfl⟩
      exact hg
  have hXh : D.map G.subtype = ⁅X.comap c, X.comap c⁆ := by
    rw [hD, CatalogueBCentralQuotient.derivedPreimage_eq_commutator, map_commutator, hpre]
  have hle : ⁅X.comap c, X.comap c⁆ ≤ G := by
    rw [← hXh]
    exact map_subtype_le D
  refine ⟨(isComponentOf_iff_isComponent_subgroupOf hle).mpr ?_, ?_⟩
  · rw [← hXh]
    change CFSG.IsComponent ((D.map G.subtype).comap G.subtype)
    rw [comap_map_eq_self_of_injective G.subtype_injective]
    exact ⟨hDq, hDsub⟩
  · rw [← hXh, Subgroup.map_map]
    have hcomp : c.comp G.subtype = H.subtype.comp f := by
      ext g
      rfl
    rw [hcomp, ← Subgroup.map_map, hDmap, map_subgroupOf_eq_of_le hXH]

theorem socle_images {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A} {P : Type*}
    [Group P] (φ : W ≃* P) {ρ : A →* MulAut P} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) (hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A))) :
    W.map ρ = inner P ∧
      (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a} ∧
      (W ⊓ centralizer {a}).map ρ = inner P ⊓ centralizer {ρ a} ∧
      CFSG.Assembly.IsComponentOf (L.map ρ) (inner P ⊓ centralizer {ρ a}) := by
  have hW : W.map ρ = inner P := OutcomeLocal.map_eq_range_conj φ hρW
  have hWle : inner P ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ = inner P ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  refine ⟨hW, hCAimg, hCWimg, ?_⟩
  have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
  rwa [hCWimg] at this

end CFSG.ComponentClassification.OddSelector
