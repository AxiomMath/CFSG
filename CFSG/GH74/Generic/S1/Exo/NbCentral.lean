module

public import CFSG.LocalAnalysis.ComponentInitial.LayerLift
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG Subgroup
open scoped commutatorElement

theorem nb_layer_map_central {X X' : Type} [Group X] [Group X'] [Finite X] (f : X →* X')
    (hf : Function.Surjective f) (hker : f.ker ≤ center X) :
    layer X' = (layer X).map f := by
  refine le_antisymm (sSup_le fun L hL => ?_) ?_
  ·
    set P := L.comap f with hP
    have hPsn : P.IsSubnormal := hL.2.comap f
    let φ : P →* L := (f.comp P.subtype).codRestrict L fun p => p.2
    have hφ : Function.Surjective φ := by
      rintro ⟨l, hl⟩
      obtain ⟨x, rfl⟩ := hf l
      exact ⟨⟨x, hl⟩, rfl⟩
    have hφker : φ.ker ≤ center P := by
      intro p hp
      have h1 : f p = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hp)
      have h2 : (p : X) ∈ center X := hker (MonoidHom.mem_ker.2 h1)
      exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 h2 g)
    have hcomp := CFSG.LocalAnalysis.ComponentInitial.isComponent_commutator_of_surjective
      hPsn hL.1 φ hφ hφker
    have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL.1.1
    have himage : ⁅P, P⁆.map f = L := by
      rw [Subgroup.map_commutator, hP, Subgroup.map_comap_eq_self_of_surjective hf, hLL]
    rw [← himage]
    exact Subgroup.map_mono (CFSG.LocalCores.component_le_layer hcomp)
  ·
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    by_cases hKf : K ≤ f.ker
    · rw [(Subgroup.map_eq_bot_iff K).mpr hKf]
      exact bot_le
    · exact CFSG.LocalCores.component_le_layer
        ⟨CFSG.LocalCores.isQuasisimple_map hK.1 f hKf, hK.2.map hf⟩

theorem nb_layer_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (layer A).map e.toMonoidHom = layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem nb_layer_comap_map {N J : Type} [Group N] [Group J] [Finite N] (f : N →* J)
    (hf : Function.Surjective f) (hker : f.ker ≤ center N) (C : Subgroup J) :
    (layer ↥C).map C.subtype = ((layer ↥(C.comap f)).map (C.comap f).subtype).map f := by
  let g : ↥(C.comap f) →* ↥C := (f.comp (C.comap f).subtype).codRestrict C fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := hf c
    exact ⟨⟨x, hc⟩, rfl⟩
  have hgker : g.ker ≤ center ↥(C.comap f) := by
    intro p hp
    have h1 : f p = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hp)
    have h2 : (p : N) ∈ center N := hker (MonoidHom.mem_ker.2 h1)
    exact Subgroup.mem_center_iff.2 fun q => Subtype.ext (Subgroup.mem_center_iff.1 h2 q)
  have hcomp : C.subtype.comp g = f.comp (C.comap f).subtype := rfl
  rw [nb_layer_map_central g hg hgker, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem nb_layer_eq_map_of_commutator_le {G : Type*} [Group G] {M : Subgroup G}
    (h : _root_.commutator G ≤ M) : layer G = (layer ↥M).map M.subtype := by
  have hMn : M.Normal := Subgroup.Normal.of_commutator_le G h
  refine le_antisymm (sSup_le fun K hK => ?_) ?_
  · have hKM : K ≤ M :=
      calc K = ⁅K, K⁆ := (Subgroup.isPerfect_iff.1 hK.1.1).symm
        _ ≤ _root_.commutator G := Subgroup.commutator_mono le_top le_top
        _ ≤ M := h
    calc K = (K.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hKM).symm
      _ ≤ (layer ↥M).map M.subtype :=
        Subgroup.map_mono (CFSG.LocalCores.component_le_layer
          (CFSG.LocalCores.component_overgroup hK hKM))
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact CFSG.LocalCores.component_le_layer
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (L.equivMapOfInjective M.subtype M.subtype_injective) hL.1,
        hL.2.trans' hMn.isSubnormal⟩

theorem nb_layer_map_subtype_eq {N : Type*} [Group N] {A B : Subgroup N} (hBA : B ≤ A)
    (hc : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ B) :
    (layer ↥A).map A.subtype = (layer ↥B).map B.subtype := by
  have hcomm : _root_.commutator ↥A ≤ B.subgroupOf A := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ h _
    exact hc g g.2 h h.2
  have h1 := nb_layer_eq_map_of_commutator_le hcomm
  let e : ↥(B.subgroupOf A) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBA
  have h3 : B.subtype.comp e.toMonoidHom = A.subtype.comp (B.subgroupOf A).subtype := rfl
  rw [← nb_layer_map_mulEquiv e, Subgroup.map_map, h3, ← Subgroup.map_map, ← h1]

theorem nb_layer_cent_map {N J : Type} [Group N] [Group J] [Finite N] (f : N →* J)
    (hf : Function.Surjective f) (hker : f.ker ≤ center N) (y : N) :
    (layer ↥(centralizer ({f y} : Set J))).map (centralizer ({f y} : Set J)).subtype =
      ((layer ↥(centralizer ({y} : Set N))).map (centralizer ({y} : Set N)).subtype).map f := by
  rw [nb_layer_comap_map f hf hker (centralizer ({f y} : Set J))]
  congr 1
  set Cs := (centralizer ({f y} : Set J)).comap f with hCs
  have hcen : ∀ g : ↥Cs, ⁅(g : N), y⁆ ∈ center N := by
    intro g
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 g.2)
  let κ : ↥Cs →* ↥(center N) := MonoidHom.mk' (fun g => ⟨⁅(g : N), y⁆, hcen g⟩) fun g h => by
    refine Subtype.ext ?_
    have h1 : ⁅(g : N) * (h : N), y⁆ = (g : N) * ⁅(h : N), y⁆ * (g : N)⁻¹ * ⁅(g : N), y⁆ := by
      simp only [commutatorElement_def]
      group
    have h2 : (g : N) * ⁅(h : N), y⁆ * (g : N)⁻¹ = ⁅(h : N), y⁆ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.1 (hcen h) g
    change ⁅(g : N) * (h : N), y⁆ = ⁅(g : N), y⁆ * ⁅(h : N), y⁆
    rw [h1, h2]
    exact (Subgroup.mem_center_iff.1 (hcen h) _).symm
  have hYC : centralizer ({y} : Set N) ≤ Cs := by
    intro x hx
    rw [hCs, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [← map_mul, ← map_mul, hx]
  refine nb_layer_map_subtype_eq hYC fun a ha b hb => ?_
  have h3 : κ ⁅(⟨a, ha⟩ : ↥Cs), (⟨b, hb⟩ : ↥Cs)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (κ ⟨b, hb⟩).2 _)
  have h4 : ⁅⁅a, b⁆, y⁆ = 1 := congrArg Subtype.val h3
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commutatorElement_eq_one_iff_mul_comm.1 h4)

theorem nb_lay_map_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (D : Subgroup A) :
    (layer ↥(D.map f)).map (D.map f).subtype = ((layer ↥D).map D.subtype).map f := by
  let e : ↥D ≃* ↥(D.map f) := D.equivMapOfInjective f hf
  have h1 : (D.map f).subtype.comp e.toMonoidHom = f.comp D.subtype := rfl
  rw [← nb_layer_map_mulEquiv e, Subgroup.map_map, Subgroup.map_map, h1]

end CFSG.GH74.Generic.S1.Exo
