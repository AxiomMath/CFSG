module

public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem map_centralizer_singleton_mulEquiv (e : X ≃* Y) (x : X) :
    (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg e h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1
  · intro h
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

@[expose] noncomputable def centralizerMulEquiv (e : X ≃* Y) (x : X) :
    centralizer ({x} : Set X) ≃* centralizer ({e x} : Set Y) :=
  (e.subgroupMap (centralizer ({x} : Set X))).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton_mulEquiv e x))

theorem centralizerMulEquiv_apply (e : X ≃* Y) (x : X) (c : centralizer ({x} : Set X)) :
    ((centralizerMulEquiv e x c : centralizer ({e x} : Set Y)) : Y) = e c :=
  rfl

theorem map_oddCoreOfCentralizer_mulEquiv (e : X ≃* Y) (x : X) :
    (oddCoreOfCentralizer x).map e.toMonoidHom = oddCoreOfCentralizer (e x) := by
  unfold oddCoreOfCentralizer
  rw [← pPrimeCore_map_iso 2 (centralizerMulEquiv e x), Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isPComponent_map_centralizer [Finite X] [Finite Y] (e : X ≃* Y) {b : X}
    {Y₀ : Subgroup X} (hY₀ : Y₀ ≤ centralizer ({b} : Set X))
    (hpc : IsPComponent 2 (Y₀.subgroupOf (centralizer ({b} : Set X)))) :
    IsPComponent 2 ((Y₀.map e.toMonoidHom).subgroupOf (centralizer ({e b} : Set Y))) := by
  have h := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    (centralizerMulEquiv e b)).1 _).mp hpc
  convert h using 1
  ext c
  rw [mem_subgroupOf, mem_map, mem_map]
  constructor
  · rintro ⟨y, hy, hyc⟩
    refine ⟨⟨y, hY₀ hy⟩, hy, Subtype.ext ?_⟩
    rw [MulEquiv.coe_toMonoidHom, centralizerMulEquiv_apply]
    exact hyc
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

end Transport

theorem footeCoreAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : FooteCoreAt Y) : FooteCoreAt X := by
  intro a b ha hb hab Y₀ hY₀C hY₀pc
  have ha' : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
  have hb' : orderOf (e b) = 2 := by rw [MulEquiv.orderOf_eq]; exact hb
  have hab' : e a * e b = e b * e a := by rw [← map_mul, ← map_mul, hab]
  set Y₁ := Y₀.map e.toMonoidHom with hY₁
  have hY₁C : Y₁ ≤ centralizer ({e b} : Set Y) := by
    rw [← map_centralizer_singleton_mulEquiv e b]
    exact map_mono hY₀C
  rcases h (e a) (e b) ha' hb' hab' Y₁ hY₁C (isPComponent_map_centralizer e hY₀C hY₀pc) with
    ⟨p, f, hp, hp2, hf, hL⟩ | hcomm
  · left
    obtain ⟨eZ⟩ := nonempty_quotient_fusionZStar_equiv (e.subgroupMap Y₀)
    exact ⟨p, f, hp, hp2, hf, LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL⟩
  · right
    have h1 := map_mono (f := e.symm.toMonoidHom) hcomm
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    have hOa : (oddCoreOfCentralizer (e a)).map e.symm.toMonoidHom = oddCoreOfCentralizer a := by
      rw [map_oddCoreOfCentralizer_mulEquiv e.symm (e a), MulEquiv.symm_apply_apply]
    have hOb : (oddCoreOfCentralizer (e b)).map e.symm.toMonoidHom = oddCoreOfCentralizer b := by
      rw [map_oddCoreOfCentralizer_mulEquiv e.symm (e b), MulEquiv.symm_apply_apply]
    have hCb : (centralizer ({e b} : Set Y)).map e.symm.toMonoidHom =
        centralizer ({b} : Set X) := by
      rw [map_centralizer_singleton_mulEquiv e.symm (e b), MulEquiv.symm_apply_apply]
    have hY : Y₁.map e.symm.toMonoidHom = Y₀ := by
      rw [hY₁, Subgroup.map_map]
      convert Subgroup.map_id Y₀ using 2
      ext x
      simp
    rw [map_commutator, map_commutator, Subgroup.map_inf_eq _ _ _ hinj, hOa, hCb, hY, hOb] at h1
    exact h1

theorem footeCoreHypothesis_subgroup {G : Type} [Group G] [Finite G]
    (h : FooteCoreHypothesis G) (H : Subgroup G) : FooteCoreHypothesis ↥H := fun H' =>
  footeCoreAt_of_mulEquiv (H'.equivMapOfInjective H.subtype H.subtype_injective)
    (h (H'.map H.subtype))

theorem kProper_subgroup' {G : Type} [Group G] (h : Assembly.KProper Blueprint.Catalog G)
    (H : Subgroup G) : Assembly.KProper Blueprint.Catalog ↥H :=
  LocalAnalysis.ComponentInitial.kProper_subgroup
    (fun e hY => SectionRank.catalog_of_mulEquiv e hY) h H

theorem footeFamilyType_of_mulEquiv {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (e : A ≃* B) (h : FooteFamilyType B) : FooteFamilyType A := by
  obtain ⟨eZ⟩ := nonempty_quotient_fusionZStar_equiv e
  rcases h with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact Or.inl ⟨eZ.trans e7⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL⟩

end CFSG.ComponentClassification.FooteLit
