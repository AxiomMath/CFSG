module

public import CFSG.Goldschmidt.Steps.Completion

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G]

@[expose] def oddCent (t : G) : Subgroup G := oddCoreOf (centralizer ({t} : Set G))

@[expose] def oddCentSub (V : Subgroup G) : Subgroup G := oddCoreOf (centralizer (V : Set G))

@[expose] def thetaOne (V : Subgroup G) (t : G) : Subgroup G :=
  ⁅oddCent t, V⁆ ⊔ (oddCentSub V ⊓ oddCent t)

@[expose] def theta (V₁ V₂ : Subgroup G) (t : G) : Subgroup G :=
  thetaOne V₁ t ⊓ thetaOne V₂ t

@[expose] def NSet (B : Subgroup G) : Set (Subgroup G) :=
  {Y | B ≤ normalizer (Y : Set G) ∧ Odd (Nat.card Y) ∧
    ∀ t ∈ B, orderOf t = 2 → Y ⊓ centralizer ({t} : Set G) ≤ oddCent t}

@[expose] def CoreSep (S₁ S₂ : Subgroup G) : Prop :=
  ∀ t ∈ S₁ ⊔ S₂, orderOf t = 2 →
    ∀ K : Subgroup (centralizer ({t} : Set G) ⧸ goldschmidtOddCore (centralizer ({t} : Set G))),
      CFSG.IsComponent K →
      barOf (centralizer ({t} : Set G)) S₁ ≤ centralizer (K : Set _) ∨
        barOf (centralizer ({t} : Set G)) S₂ ≤ centralizer (K : Set _)

theorem coreSep_symm {S₁ S₂ : Subgroup G} (h : CoreSep S₁ S₂) : CoreSep S₂ S₁ := by
  intro t ht ht2 K hK
  exact (h t (by rwa [sup_comm]) ht2 K hK).symm

theorem oddCent_le_centralizer (t : G) : oddCent t ≤ centralizer ({t} : Set G) :=
  Subgroup.map_subtype_le _

theorem oddCentSub_le_centralizer (V : Subgroup G) :
    oddCentSub V ≤ centralizer (V : Set G) :=
  Subgroup.map_subtype_le _

theorem centralizer_le_normalizer_oddCent (t : G) :
    centralizer ({t} : Set G) ≤ normalizer ((oddCent t : Subgroup G) : Set G) :=
  Completion.le_normalizer_oddCoreOf _

theorem centralizer_le_normalizer_oddCentSub (V : Subgroup G) :
    centralizer (V : Set G) ≤ normalizer ((oddCentSub V : Subgroup G) : Set G) :=
  Completion.le_normalizer_oddCoreOf _

theorem commutator_oddCent_le {V : Subgroup G} {t : G} (hV : V ≤ centralizer ({t} : Set G)) :
    ⁅oddCent t, V⁆ ≤ oddCent t := by
  rw [commutator_le]
  intro x hx v hv
  rw [commutatorElement_def]
  have h1 := (mem_normalizer_iff.mp (centralizer_le_normalizer_oddCent t (hV hv)) x⁻¹).mp
    ((oddCent t).inv_mem hx)
  rw [mul_assoc, mul_assoc]
  exact (oddCent t).mul_mem hx (by simpa [mul_assoc] using h1)

theorem thetaOne_le_oddCent {V : Subgroup G} {t : G} (hV : V ≤ centralizer ({t} : Set G)) :
    thetaOne V t ≤ oddCent t :=
  sup_le (commutator_oddCent_le hV) inf_le_right

theorem theta_le_oddCent {V₁ V₂ : Subgroup G} {t : G}
    (hV : V₁ ≤ centralizer ({t} : Set G)) : theta V₁ V₂ t ≤ oddCent t :=
  inf_le_left.trans (thetaOne_le_oddCent hV)

end CFSG.Goldschmidt75
