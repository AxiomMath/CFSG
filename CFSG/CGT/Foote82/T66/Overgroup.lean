module

public import CFSG.CGT.Foote82.T66.Prop35
import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PGroups
public import CFSG.CGT.Foote82.T66.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem isComponentOf_of_le_of_le {Γ : Type*} [Group Γ] {L K H : Subgroup Γ}
    (hL : IsComponentOf L K) (hLH : L ≤ H) (hHK : H ≤ K) : IsComponentOf L H :=
  CFSG.Assembly.isComponentOf_iff_open.1
    ((CFSG.Assembly.isComponentOf_iff_open.2 hL).of_le_of_le hLH hHK)

theorem normalClosure_mono_left {Γ₁ Γ₂ L : Subgroup (GLV V)} (h : Γ₁ ≤ Γ₂) :
    normalClosure Γ₁ L ≤ normalClosure Γ₂ L := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact ⟨γ, h hγ, l, hl, rfl⟩

theorem normalClosure_le_self {Γ L : Subgroup (GLV V)} (hL : L ≤ Γ) : normalClosure Γ L ≤ Γ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact Γ.mul_mem (Γ.mul_mem hγ (hL hl)) (Γ.inv_mem hγ)

theorem layerIn_subgroupOf (G : Subgroup (GLV V)) :
    (layerIn G).subgroupOf G = CFSG.layer ↥G :=
  Subgroup.comap_map_eq_self_of_injective G.subtype_injective _

theorem layerIn_le (G : Subgroup (GLV V)) : layerIn G ≤ G :=
  Subgroup.map_subtype_le _

theorem isSubnormal_layerIn (G : Subgroup (GLV V)) : IsSubnormal (layerIn G) G := by
  have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
  refine .step (layerIn_le G) ?_ (.refl G)
  rw [layerIn_subgroupOf]
  infer_instance

theorem layerIn_eq_sSup (G : Subgroup (GLV V)) :
    layerIn G = sSup {Q : Subgroup (GLV V) | IsComponentOf Q G} := by
  show (CFSG.layer ↥G).map G.subtype = _
  rw [CFSG.LocalAnalysis.ComponentInitial.layer_map_subtype]
  congr 1
  ext Q
  exact CFSG.Assembly.isComponentOf_iff_open

theorem le_layerIn_of_isComponentOf {G Q : Subgroup (GLV V)} (hQ : IsComponentOf Q G) :
    Q ≤ layerIn G := by
  rw [layerIn_eq_sSup]
  exact le_sSup hQ

theorem commutator_eq_self_of_isQuasisimple {Γ : Type*} [Group Γ] {Q : Subgroup Γ}
    (hQ : CFSG.Open.IsQuasisimple ↥Q) : ⁅Q, Q⁆ = Q := by
  have : Group.IsPerfect ↥Q := ⟨hQ.1⟩
  exact Subgroup.isPerfect_iff.mp this

theorem Setup6Irr.le_layerIn_of_perfect {G S L Q : Subgroup (GLV V)} (h : Setup6Irr G S L)
    (hQG : Q ≤ G) (hQ : ⁅Q, Q⁆ = Q) : Q ≤ layerIn G := by
  have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hS : IsPGroup 2 ↥(S.subgroupOf G) :=
    IsPGroup.of_surjective h.isPGroup (Subgroup.subgroupOfEquivOfLe h.S_le).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe h.S_le).symm.surjective
  have htop : CFSG.layer ↥G ⊔ S.subgroupOf G = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h.S_le, Subgroup.map_top,
      Subgroup.range_subtype]
    exact h.eq_layerIn_sup.symm
  have hQ' : ⁅Q.subgroupOf G, Q.subgroupOf G⁆ = Q.subgroupOf G := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQG]
    exact hQ
  have hle := CFSG.EvenSporadicStandard.Induction.Junction.perfect_le_of_sup_eq_top hS htop hQ'
  calc Q = (Q.subgroupOf G).map G.subtype := (Subgroup.map_subgroupOf_eq_of_le hQG).symm
    _ ≤ layerIn G := Subgroup.map_mono hle

theorem Extremal.S_ne_bot {G S L : Subgroup (GLV V)} (h : Extremal G S L) : S ≠ ⊥ := by
  intro hS
  exact h.not_concl (Or.inl (h.setup.eq_iff_eq_bot.2 hS))

theorem Extremal.layerIn_ne {G S L : Subgroup (GLV V)} (h : Extremal G S L) : layerIn G ≠ L :=
  h.setup.layerIn_ne_of_ne_bot h.S_ne_bot

theorem Setup6Irr.layerIn_eq_of_le {G S L X : Subgroup (GLV V)} (h : Setup6Irr G S L)
    (hEX : layerIn G ≤ X) (hXG : X ≤ G) : layerIn X = layerIn G := by
  rw [layerIn_eq_sSup X, layerIn_eq_sSup G]
  congr 1
  ext Q
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hQ
    have hQE : Q ≤ layerIn G :=
      h.le_layerIn_of_perfect (hQ.1.trans hXG) (commutator_eq_self_of_isQuasisimple hQ.2.2)
    have hQE' : IsSubnormal Q (layerIn G) := by
      have := hQ.2.1.inf (layerIn G)
      rwa [inf_eq_left.2 hQE, inf_eq_right.2 hEX] at this
    exact ⟨hQE.trans (layerIn_le G), hQE'.trans (isSubnormal_layerIn G), hQ.2.2⟩
  · intro hQ
    exact isComponentOf_of_le_of_le hQ ((le_layerIn_of_isComponentOf hQ).trans hEX) hXG

theorem Extremal.eq_of_le {G S L X R : Subgroup (GLV V)} (h : Extremal G S L) (hXG : X ≤ G)
    (hEX : layerIn G ≤ X) (hR : IsPGroup 2 R) (hRX : R ≤ X)
    (hcomp : IsComponentOf L (X ⊓ Subgroup.centralizer (R : Set (GLV V))))
    (hX : X = layerIn G ⊔ R) : X = G := by
  by_contra hne
  have hlt : X < G := lt_of_le_of_ne hXG hne
  have hLX : L ≤ X := hcomp.1.trans inf_le_left
  have hgen : X = normalClosure X L ⊔ R := by
    refine le_antisymm ?_ (sup_le (normalClosure_le_self hLX) hRX)
    calc X = layerIn G ⊔ R := hX
      _ = normalClosure (layerIn G) L ⊔ R := by rw [h.setup.normalClosure_layerIn]
      _ ≤ normalClosure X L ⊔ R := sup_le_sup_right (normalClosure_mono_left hEX) R
  have hconf : Conf66 X R L :=
    { kProper := CFSG.ComponentClassification.CatalogueKProper.of_injective h.kProper
        (Subgroup.inclusion hXG) (Subgroup.inclusion_injective hXG)
      setup :=
        { S_le := hRX
          isPGroup := hR
          component := hcomp
          irrTilde := h.setup.irrTilde
          irr := h.setup.isIrr_of_layerIn_le hEX
          gen := hgen }
      fmod := h.fmod }
  have hcard : Nat.card X < Nat.card G := Subgroup.card_lt_of_lt hlt
  have hconcl := h.min V X R L hcard hconf h.faithful
  have hE : layerIn X = layerIn G := h.setup.layerIn_eq_of_le hEX hXG
  rcases hconcl with hLeq | hc | hc
  · apply h.layerIn_ne
    exact le_antisymm (hLeq ▸ hEX) h.setup.toSetup6.le_layerIn
  · exact h.not_concl (Or.inr (Or.inl (hE ▸ hc)))
  · exact h.not_concl (Or.inr (Or.inr (hE ▸ hc)))

theorem Extremal.eq_layerIn_sup_of_isComponentOf {G S L R : Subgroup (GLV V)} (h : Extremal G S L)
    (hR : IsPGroup 2 R) (hRG : R ≤ G)
    (hcomp : IsComponentOf L (G ⊓ Subgroup.centralizer (R : Set (GLV V)))) :
    G = layerIn G ⊔ R := by
  have hLE : L ≤ layerIn G := h.setup.toSetup6.le_layerIn
  have hLC : L ≤ Subgroup.centralizer (R : Set (GLV V)) := hcomp.1.trans inf_le_right
  have hX := h.eq_of_le (X := layerIn G ⊔ R) (sup_le (layerIn_le G) hRG) le_sup_left hR
    le_sup_right
    (isComponentOf_of_le_of_le hcomp (le_inf (hLE.trans le_sup_left) hLC)
      (inf_le_inf_right _ (sup_le (layerIn_le G) hRG))) rfl
  exact hX.symm

theorem Extremal.of_isComponentOf {G S L R : Subgroup (GLV V)} (h : Extremal G S L)
    (hR : IsPGroup 2 R) (hRG : R ≤ G)
    (hcomp : IsComponentOf L (G ⊓ Subgroup.centralizer (R : Set (GLV V)))) :
    Extremal G R L := by
  have hLG : L ≤ G := hcomp.1.trans inf_le_left
  have hgen : G = normalClosure G L ⊔ R := by
    refine le_antisymm ?_ (sup_le (normalClosure_le_self hLG) hRG)
    calc G = layerIn G ⊔ R := h.eq_layerIn_sup_of_isComponentOf hR hRG hcomp
      _ = normalClosure (layerIn G) L ⊔ R := by rw [h.setup.normalClosure_layerIn]
      _ ≤ normalClosure G L ⊔ R := sup_le_sup_right (normalClosure_mono_left (layerIn_le G)) R
  exact
    { kProper := h.kProper
      setup :=
        { S_le := hRG
          isPGroup := hR
          component := hcomp
          irrTilde := h.setup.irrTilde
          irr := h.setup.irr
          gen := hgen }
      fmod := h.fmod
      faithful := h.faithful
      not_concl := h.not_concl
      min := h.min
      max := h.max }

end CFSG.CGT.Foote82
