module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

@[expose] def SmallCentralQuotient (Y : Type) [Group Y] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ LieModel (Y ⧸ center Y) .PSL 2 p f) ∨
    Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin 7)) ∨ LieModel (Y ⧸ center Y) .PSL 3 2 2

theorem smallCentralQuotient_of_smallSource {A : Type} [Group A] {L : Subgroup A}
    (h : SmallSource L) : SmallCentralQuotient L := by
  rcases h with ⟨p, f, hp, hp2, hf, h5, hm, -⟩ | ⟨h7, -⟩ | h34
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, hm⟩
  · exact Or.inr (Or.inl h7)
  · exact Or.inr (Or.inr h34)

theorem smallCentralQuotient_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : SmallCentralQuotient Y') : SmallCentralQuotient Y := by
  let f : Y ⧸ center Y ≃* Y' ⧸ center Y' :=
    QuotientGroup.congr (center Y) (center Y') e (Subgroup.map_center_eq e)
  rcases h with ⟨p, f', hp, hp2, hf, h5, hm⟩ | ⟨⟨e7⟩⟩ | h34
  · exact Or.inl ⟨p, f', hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv f.symm hm⟩
  · exact Or.inr (Or.inl ⟨f.trans e7⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv f.symm h34))

@[expose] def SporadicCase (s : TauCeti.SporadicName) : Prop :=
  AlmostSimpleRestricted fun Y _ => NativeSporadic.IsSporadic Y s

theorem almostSimpleRestricted_sporadicUnrestricted_of_cases
    (h : ∀ s : TauCeti.SporadicName, s ∉ restrictedSporadicNames → SporadicCase s) :
    AlmostSimpleRestricted SporadicUnrestricted := by
  intro A _ _ W _ hWs hWnab hCW hcat hW a ha L hLW hne hL hstd hs
  obtain ⟨s, hsr, hsW⟩ := hW
  exact h s hsr A W hWs hWnab hCW hcat hsW a ha L hLW hne hL hstd hs

theorem mem_of_forall_inner {A : Type*} [Group A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) (hinner : ∀ α : MulAut W, ∃ w : W, α = MulAut.conj w)
    (a : A) : a ∈ W := by
  obtain ⟨w, hw⟩ := hinner (MulAut.conjNormal a)
  have h : (w : A)⁻¹ * a ∈ centralizer (W : Set A) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut W => ((φ ⟨x, hx⟩ : W) : A)) hw
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
    calc x * ((w : A)⁻¹ * a) = (w : A)⁻¹ * ((w : A) * x * (w : A)⁻¹) * a := by group
      _ = (w : A)⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
      _ = (w : A)⁻¹ * a * x := by group
  rw [hCW, mem_bot, inv_mul_eq_one] at h
  rw [← h]
  exact w.2

theorem exists_isComponent_centralizer_of_mem {A : Type*} [Group A] {W L : Subgroup A} {a : A}
    (haW : a ∈ W) (hLW : L ≤ W) (hL : Assembly.IsComponentOf L (centralizer ({a} : Set A))) :
    ∃ B : Subgroup (centralizer ({(⟨a, haW⟩ : W)} : Set W)), IsComponent B ∧
      Nonempty (B ≃* L) := by
  set X := centralizer ({(⟨a, haW⟩ : W)} : Set W) with hX
  have hLX : Assembly.IsComponentOf L (W ⊓ centralizer ({a} : Set A)) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have hLX' : Assembly.IsComponentOf ((L.subgroupOf W).map W.subtype) (X.map W.subtype) := by
    rw [map_subgroupOf_eq_of_le hLW, hX,
      LocalAnalysis.ComponentInitial.map_subtype_centralizer_singleton]
    exact hLX
  have h1 := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff W.subtype_injective).1 hLX'
  refine ⟨(L.subgroupOf W).subgroupOf X,
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h1.1).1 h1, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe h1.1).trans (subgroupOfEquivOfLe hLW)

theorem sporadicCase_of_forall_inner_of_noSmallComponent {s : TauCeti.SporadicName}
    (hinner : ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g)
    (hcomp : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → ∀ B : Subgroup (centralizer ({t} : Set G)), IsComponent B →
        ¬ SmallCentralQuotient B) :
    SporadicCase s := by
  intro A _ _ W _ hWs hWnab hCW hcat hsW a ha L hLW hne hL hstd hs
  exfalso
  have haW : a ∈ W := mem_of_forall_inner hCW (hinner W hsW) a
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_isComponent_centralizer_of_mem haW hLW hL
  have ha' : orderOf (⟨a, haW⟩ : W) = 2 := by rw [Subgroup.orderOf_mk, ha]
  exact hcomp W hsW _ ha' B hB
    (smallCentralQuotient_of_mulEquiv eB (smallCentralQuotient_of_smallSource hs))

end CFSG.ComponentClassification.RestrictedStd
