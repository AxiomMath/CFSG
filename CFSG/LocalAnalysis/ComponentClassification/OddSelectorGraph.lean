module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormSimilitude
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorLift

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog

variable {k : Type*} [Field k] [Finite k] {m : ℕ}

omit [Finite k] in
theorem commute_conjAut_pureGraph_iff (B g : GL (Fin m) k) :
    Commute (conjAut m k g) (conjAut m k B * dualAut m k) ↔
      conjAut m k g * conjAut m k B =
        conjAut m k B * conjAut m k (GeneralLinearGroup.inverseTranspose g) := by
  change conjAut m k g * (conjAut m k B * dualAut m k) =
      conjAut m k B * dualAut m k * conjAut m k g ↔ _
  rw [mul_assoc (conjAut m k B), dualAut_mul_conjAut, ← mul_assoc, ← mul_assoc]
  exact mul_left_inj _

omit [Finite k] in
theorem coe_inverseTranspose_inv (g : GL (Fin m) k) :
    (((GeneralLinearGroup.inverseTranspose g)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      (g : Matrix (Fin m) (Fin m) k)ᵀ := by
  rw [← map_inv, GeneralLinearGroup.coe_inverseTranspose, inv_inv]

theorem graph_commutator_le_isometry (hm : 3 ≤ m) (B : GL (Fin m) k)
    {G : Subgroup (GL (Fin m) k)}
    (hG : G ≤ (centralizer {conjAut m k B * dualAut m k}).comap (conjAut m k)) :
    ⁅G, G⁆ ≤ CatalogueBGraphForm.isometryGroup m k B⁻¹ := by
  set T : GL (Fin m) k → GL (Fin m) k := fun g => (GeneralLinearGroup.inverseTranspose g)⁻¹
    with hT
  have hTmul : ∀ g h, T (g * h) = T h * T g := fun g h => by
    simp only [hT, map_mul, _root_.mul_inv_rev]
  have hz : ∀ g : G, (g : GL (Fin m) k) * B * T g * B⁻¹ ∈ center (GL (Fin m) k) := by
    intro g
    have hc := (commute_conjAut_pureGraph_iff B g).mp
      (mem_centralizer_singleton_iff.mp (hG g.2)).symm.symm
    have h1 : conjAut m k ((g : GL (Fin m) k) * B * T g * B⁻¹) = 1 := by
      simp only [hT, map_mul, map_inv, hc]
      group
    exact ker_conjAut_le_center hm h1
  let φ : G →* center (GL (Fin m) k) :=
    { toFun := fun g => ⟨_, hz g⟩
      map_one' := Subtype.ext (by simp [hT])
      map_mul' := fun g h => Subtype.ext (by
        have hh := mem_center_iff.mp (hz h) (g : GL (Fin m) k)
        have hh' := mem_center_iff.mp (hz h) ((g : GL (Fin m) k) * B * T g * B⁻¹)
        change (g : GL (Fin m) k) * h * B * T ((g : GL (Fin m) k) * h) * B⁻¹ =
          (g : GL (Fin m) k) * B * T g * B⁻¹ * ((h : GL (Fin m) k) * B * T h * B⁻¹)
        rw [hTmul]
        calc (g : GL (Fin m) k) * h * B * (T h * T g) * B⁻¹ =
              (g : GL (Fin m) k) * ((h : GL (Fin m) k) * B * T h * B⁻¹) *
                (B * T g * B⁻¹) := by group
          _ = (h : GL (Fin m) k) * B * T h * B⁻¹ * (g : GL (Fin m) k) *
                (B * T g * B⁻¹) := by rw [hh]
          _ = (h : GL (Fin m) k) * B * T h * B⁻¹ *
                ((g : GL (Fin m) k) * B * T g * B⁻¹) := by group
          _ = _ := hh'.symm) }
  have hker : commutator G ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [← Subgroup.map_subtype_commutator]
  rintro _ ⟨g, hg, rfl⟩
  have h1 := congrArg Subtype.val (show φ g = 1 from hker hg)
  change (g : GL (Fin m) k) * B * T g * B⁻¹ = 1 at h1
  have h2 : T g * B⁻¹ * (g : GL (Fin m) k) = B⁻¹ := by
    have h3 : (g : GL (Fin m) k) * B * T g = B := by
      calc (g : GL (Fin m) k) * B * T g = (g : GL (Fin m) k) * B * T g * B⁻¹ * B := by group
        _ = B := by rw [h1, one_mul]
    calc T g * B⁻¹ * (g : GL (Fin m) k) =
          T g * ((g : GL (Fin m) k) * B * T g)⁻¹ * (g : GL (Fin m) k) := by rw [h3]
      _ = B⁻¹ := by group
  rw [CatalogueBGraphForm.mem_isometryGroup]
  have := congrArg (fun x : GL (Fin m) k => (x : Matrix (Fin m) (Fin m) k)) h2
  simp only [Units.val_mul] at this
  rw [coe_inverseTranspose_inv] at this
  exact this

omit [Finite k] in
theorem isometryGroup_le_comap_centralizer (B : GL (Fin m) k) :
    CatalogueBGraphForm.isometryGroup m k B⁻¹ ≤
      (centralizer {conjAut m k B * dualAut m k}).comap (conjAut m k) := by
  intro g hg
  rw [mem_comap, mem_centralizer_singleton_iff]
  refine ((commute_conjAut_pureGraph_iff B g).mpr ?_).eq
  rw [CatalogueBGraphForm.mem_isometryGroup] at hg
  have hgl' : (GeneralLinearGroup.inverseTranspose g)⁻¹ * B⁻¹ * g = B⁻¹ := Units.ext (by
    simp only [Units.val_mul]
    rw [coe_inverseTranspose_inv]
    exact hg)
  have hgl : g * B * (GeneralLinearGroup.inverseTranspose g)⁻¹ = B := by
    have h1 : ((GeneralLinearGroup.inverseTranspose g)⁻¹ * B⁻¹ * g)⁻¹ = B := by
      rw [hgl', inv_inv]
    calc g * B * (GeneralLinearGroup.inverseTranspose g)⁻¹ =
          g * ((GeneralLinearGroup.inverseTranspose g)⁻¹ * B⁻¹ * g)⁻¹ *
            (GeneralLinearGroup.inverseTranspose g)⁻¹ := by rw [h1]
      _ = B := by group
  calc conjAut m k g * conjAut m k B = conjAut m k (g * B) := (map_mul _ _ _).symm
    _ = conjAut m k (B * GeneralLinearGroup.inverseTranspose g) := by
        congr 1
        calc g * B = g * B * (GeneralLinearGroup.inverseTranspose g)⁻¹ *
              GeneralLinearGroup.inverseTranspose g := by group
          _ = B * GeneralLinearGroup.inverseTranspose g := by rw [hgl]
    _ = _ := map_mul _ _ _

theorem graph_component_lift (hm : 3 ≤ m) (B : GL (Fin m) k)
    {X : Subgroup (MulAut (projectiveSL m k))}
    (hX : CFSG.Assembly.IsComponentOf X
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {conjAut m k B * dualAut m k})) :
    CFSG.Assembly.IsComponentOf ⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆
        (CatalogueBGraphForm.isometryGroup m k B⁻¹) ∧
      (⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆).map (conjAut m k) = X ∧
      ⁅X.comap (conjAut m k), X.comap (conjAut m k)⁆ ≤
        (OuterAutomorphisms.inner (projectiveSL m k)).comap (conjAut m k) := by
  set c := conjAut m k with hc
  set H := OuterAutomorphisms.inner (projectiveSL m k) ⊓
    centralizer {c B * dualAut m k} with hH
  obtain ⟨hXh, hmap⟩ := component_lift hm (H := H) inf_le_left hX
  set Xh := ⁅X.comap c, X.comap c⁆ with hXhdef
  have hGc : H.comap c ≤ (centralizer {c B * dualAut m k}).comap c := comap_mono inf_le_right
  have hXhO : Xh ≤ CatalogueBGraphForm.isometryGroup m k B⁻¹ :=
    (commutator_mono (comap_mono hX.1) (comap_mono hX.1)).trans
      (graph_commutator_le_isometry hm B hGc)
  have hXhI : Xh ≤ (OuterAutomorphisms.inner (projectiveSL m k)).comap c :=
    hXh.1.trans (comap_mono inf_le_left)
  refine ⟨?_, hmap, hXhI⟩
  have hX₁ : CFSG.Assembly.IsComponentOf Xh
      ((OuterAutomorphisms.inner (projectiveSL m k)).comap c ⊓
        CatalogueBGraphForm.isometryGroup m k B⁻¹) := by
    refine isComponentOf_of_le hXh (le_inf hXhI hXhO) ?_
    intro g hg
    exact ⟨hg.1, isometryGroup_le_comap_centralizer B hg.2⟩
  have hnormal : ((OuterAutomorphisms.inner (projectiveSL m k)).comap c).Normal :=
    (OuterAutomorphisms.inner_normal (projectiveSL m k)).comap c
  refine ⟨hX₁.1.trans inf_le_right, assembly_isSubnormal_trans hX₁.2.1
    (CFSG.Assembly.IsSubnormal.step inf_le_right ?_ (CFSG.Assembly.IsSubnormal.refl _)), hX₁.2.2⟩
  rw [inf_subgroupOf_right]
  exact hnormal.subgroupOf _

end CFSG.ComponentClassification.OddSelector
