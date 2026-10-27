module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS

section Group

variable {G : Type*} [Group G]

theorem comm_of_biSup_comm {S S' : Set (Subgroup G)}
    (h : ∀ X ∈ S, ∀ Y ∈ S', ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ x ∈ (⨆ X ∈ S, X : Subgroup G), ∀ y ∈ (⨆ Y ∈ S', Y : Subgroup G), x * y = y * x := by
  have h1 : ∀ y, (∃ Y ∈ S', y ∈ Y) → ∀ x ∈ (⨆ X ∈ S, X : Subgroup G), x * y = y * x := by
    rintro y ⟨Y, hY, hy⟩
    have : (⨆ X ∈ S, X : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) :=
      iSup₂_le fun X hX x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (h X hX Y hY x hx y hy)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  intro x hx y hy
  have : (⨆ Y ∈ S', Y : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) :=
    iSup₂_le fun Y hY y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (h1 y ⟨Y, hY, hy⟩ x hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this hy)).symm

theorem disjoint_biSup_biSup_of_comm {ℰ : Set (Subgroup G)} (hfin : ℰ.Finite)
    (hcomm : ∀ E ∈ ℰ, ∀ E' ∈ ℰ, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    (hind : ∀ E ∈ ℰ, Disjoint E (⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E'))
    {S S' : Set (Subgroup G)} (hS : S ⊆ ℰ) (hS' : S' ⊆ ℰ) (hSS' : Disjoint S S') :
    Disjoint (⨆ E ∈ S, E) (⨆ E ∈ S', E) := by
  classical
  obtain ⟨F, rfl⟩ := (hfin.subset hS).exists_finset_coe
  clear hfin
  induction F using Finset.induction_on with
  | empty => simp
  | insert E F₀ hE ih =>
    have hEℰ : E ∈ ℰ := hS (by simp)
    have hF₀ℰ : ((F₀ : Finset (Subgroup G)) : Set (Subgroup G)) ⊆ ℰ := fun X hX =>
      hS (by simp [hX])
    have hF₀S' : Disjoint ((F₀ : Finset (Subgroup G)) : Set (Subgroup G)) S' :=
      Set.disjoint_of_subset_left (by intro X hX; simp [hX]) hSS'
    have hES' : E ∉ S' := fun hE' =>
      Set.disjoint_left.1 hSS' (by simp : E ∈ ((insert E F₀ : Finset (Subgroup G)) :
        Set (Subgroup G))) hE'
    have ih' := ih hF₀ℰ hF₀S'
    rw [Finset.coe_insert, iSup_insert]
    rw [Subgroup.disjoint_def]
    intro x hx hxS'
    have hcomm' : ∀ y ∈ (⨆ X ∈ ((F₀ : Finset (Subgroup G)) : Set (Subgroup G)), X :
        Subgroup G), ∀ z ∈ E, z * y = y * z := by
      intro y hy z hz
      have := comm_of_biSup_comm (S := ({E} : Set (Subgroup G)))
        (S' := ((F₀ : Finset (Subgroup G)) : Set (Subgroup G)))
        (fun X hX Y hY x hx y hy => by
          have hXE : X = E := hX
          rw [hXE] at hx
          exact hcomm E hEℰ Y (hF₀ℰ hY) (fun h => hE (h ▸ hY)) x hx y hy) z
        (by simpa using hz) y hy
      exact this
    obtain ⟨e, he, f, hf, rfl⟩ := exists_mul_of_mem_sup' (fun z hz y hy => hcomm' y hy z hz) hx
    have hef : e ∈ (⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E' : Subgroup G) := by
      have h1 : (e * f) * f⁻¹ = e := by group
      rw [← h1]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact (iSup₂_le fun X hX => le_iSup₂_of_le (f := fun (E' : Subgroup G)
          (_ : E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}) => E') X
          ⟨hS' hX, fun h => hES' (h ▸ hX)⟩ le_rfl) hxS'
      · refine Subgroup.inv_mem _ ?_
        exact (iSup₂_le fun X hX => le_iSup₂_of_le (f := fun (E' : Subgroup G)
          (_ : E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}) => E') X
          ⟨hF₀ℰ hX, fun h => hE (h ▸ hX)⟩ le_rfl) hf
    have he1 : e = 1 := (Subgroup.disjoint_def.1 (hind E hEℰ)) he hef
    subst he1
    rw [one_mul] at hxS' ⊢
    exact (Subgroup.disjoint_def.1 ih') hf hxS'

end Group

section Module

variable {V : Type} [CommGroup V]

theorem mem_fixV_iff_le_stabilizer {X : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV X ↔ X ≤ MulAction.stabilizer (MulAut V) v :=
  CFSG.CGT.PushingUpLit.BHS.mem_fixV_iff_le

theorem mem_fixV_iSup_iff {S : Set (Subgroup (MulAut V))} {v : V} :
    v ∈ fixV (⨆ X ∈ S, X : Subgroup (MulAut V)) ↔ ∀ X ∈ S, v ∈ fixV X := by
  simp only [mem_fixV_iff_le_stabilizer, iSup_le_iff]

theorem mem_fixV_sup_iff {X Y : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV (X ⊔ Y) ↔ v ∈ fixV X ∧ v ∈ fixV Y := by
  simp only [mem_fixV_iff_le_stabilizer, sup_le_iff]

theorem fixV_sup_iSup_commV {ℰ : Set (Subgroup (MulAut V))} (hfin : ℰ.Finite)
    (hcomm : ∀ E ∈ ℰ, ∀ E' ∈ ℰ, E ≠ E' → commV E ≤ fixV E')
    (htop : ∀ E ∈ ℰ, commV E ⊔ fixV E = ⊤) :
    fixV (⨆ E ∈ ℰ, E : Subgroup (MulAut V)) ⊔ (⨆ E ∈ ℰ, commV E) = ⊤ := by
  classical
  obtain ⟨F, rfl⟩ := hfin.exists_finset_coe
  induction F using Finset.induction_on with
  | empty =>
    simp [B1.fixV_bot]
  | insert E' F₀ hE' ih =>
    have hF₀ : ((F₀ : Finset (Subgroup (MulAut V))) : Set (Subgroup (MulAut V))) ⊆
        ((insert E' F₀ : Finset (Subgroup (MulAut V))) : Set (Subgroup (MulAut V))) :=
      fun X hX => by simp [hX]
    have ih' := ih (hfin.subset hF₀)
      (fun E hE E'' hE'' hne => hcomm E (hF₀ hE) E'' (hF₀ hE'') hne)
      (fun E hE => htop E (hF₀ hE))
    have hE'mem : E' ∈ ((insert E' F₀ : Finset (Subgroup (MulAut V))) :
        Set (Subgroup (MulAut V))) := by simp
    rw [Finset.coe_insert, iSup_insert, iSup_insert]
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ fixV (⨆ X ∈ ((F₀ : Finset (Subgroup (MulAut V))) :
        Set (Subgroup (MulAut V))), X) ⊔ ⨆ X ∈ ((F₀ : Finset (Subgroup (MulAut V))) :
        Set (Subgroup (MulAut V))), commV X := by rw [ih']; trivial
    obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.1 hv
    have hc' : c ∈ commV E' ⊔ fixV E' := by rw [htop E' hE'mem]; trivial
    obtain ⟨w, hw, c', hc'E, rfl⟩ := Subgroup.mem_sup.1 hc'
    have hwfix : w ∈ fixV (⨆ X ∈ ((F₀ : Finset (Subgroup (MulAut V))) :
        Set (Subgroup (MulAut V))), X) := by
      rw [mem_fixV_iSup_iff]
      intro X hX
      exact hcomm E' hE'mem X (hF₀ hX) (fun h => hE' (h ▸ hX)) hw
    have hc'fix : c' ∈ fixV (⨆ X ∈ ((F₀ : Finset (Subgroup (MulAut V))) :
        Set (Subgroup (MulAut V))), X) := by
      have := (fixV _).mul_mem ((fixV _).inv_mem hwfix) hc
      simpa using this
    have hc'sup : c' ∈ fixV (E' ⊔ ⨆ X ∈ ((F₀ : Finset (Subgroup (MulAut V))) :
        Set (Subgroup (MulAut V))), X) := mem_fixV_sup_iff.2 ⟨hc'E, hc'fix⟩
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hw)
    · exact Subgroup.mem_sup_left hc'sup
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right hu)

end Module

end CFSG.CGT.PushingUpLit.BHS5
