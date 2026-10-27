module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLambda
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClFourNode

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique

namespace Classif

open Offender

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)}

theorem unmatched_mem_orbit_of_fourOrbit (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W)
    (hE : IsExp2 E) (h : OffenderShapeConcl E) {x : Ω} (hx : Nat.card (orbit E x) = 4) {z : Ω}
    (hz : partner hW z = z) : z ∈ orbit E x := by
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · exfalso
    have := (h.1 hf).1 x
    omega
  · rcases h.2 hf with ⟨hall2, -⟩ | ⟨⟨x₀, hx₀⟩, hall, hone, hbij⟩
    · exfalso
      have := hall2 x
      omega
    · by_contra hzx
      have hxx₀ : x ∈ orbit E x₀ := hone x₀ x hx₀ hx
      have heq : orbit E x = orbit E x₀ := orbit_eq_iff.2 hxx₀
      have hz' : z ∉ orbit E x₀ := by rw [← heq]; exact hzx
      exact fourOrbit_matched_off hW hEW hE hall hone hbij hx₀ hz' hz

end Classif

variable {G : Type} [Group G] [Finite G]

theorem card_unmatched_le_four {S L : Subgroup G} {d : ℕ} (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hS2 : IsPGroup 2 S)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ))
    {A : Subgroup G} (hAm : IsMaxElemAbelian S A) {x : Fin d}
    (hx : Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4) :
    Nat.card {z : Fin d // ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d)))} ≤ 4 := by
  classical
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  have hAJ : A ≤ thompsonJ S := le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : (A.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ :=
    Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hE : Offender.IsExp2 ((A.subgroupOf (L ⊔ S)).map θ) := by
    rintro g ⟨a, ha, rfl⟩
    have hsq : a * a = 1 := by
      apply Subtype.ext
      have := hAm.2.1.2 _ (Subgroup.mem_subgroupOf.1 ha)
      simpa [pow_two] using this
    rw [← map_mul, hsq, map_one]
  have hsub : {z : Fin d | ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d)))} ⊆
      orbit ((A.subgroupOf (L ⊔ S)).map θ) x := by
    intro z hz
    refine Classif.unmatched_mem_orbit_of_fourOrbit hP.twoGroup hEW hE (hsh A hAm) hx ?_
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (orbit ((A.subgroupOf (L ⊔ S)).map θ) x : Set (Fin d)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hx
  have h3 := Nat.card_coe_set_eq {z : Fin d | ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d)))}
  exact h3.trans_le (by omega)

open scoped Classical in
@[expose] def EightTenNodeFourOrbitFixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ A : Subgroup G, IsMaxElemAbelian S A → ∀ x : Fin m,
      Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4 →
      (∃ z : Fin m, ∀ y, z ≠ y →
        swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) →
      (Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
        5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y}) →
      (∀ p q : Fin m, IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q →
        ∀ s : ↥(L ⊔ S), (s : G) ∈ S → θ s p = p ∨ θ s p = q) →
      EightTenOutcomes X S L

theorem eightTenNodeFourOrbit_of_fixed (h : EightTenNodeFourOrbitFixed) : EightTenNodeFourOrbit := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A hAm x hx
  classical
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hunm := exists_unmatched_of_fourOrbit hA hL hSL (by omega) hNS hθS hsh hAm hx
  have hP := pre_of_theta hA'.twoRadical.isPGroup (le_sup_right : S ≤ L ⊔ S) θ hsh
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hle4 := card_unmatched_le_four θ hS2 hsh hAm hx
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
    obtain ⟨z, hz⟩ := hunm
    refine ⟨z, ?_⟩
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  have h2N := hP.two_mul_isoCount_eq hex
  have hcount : Nat.card {z : Fin m // Classif.partner hP.twoGroup z ≠ z} +
      Nat.card {z : Fin m // ∀ y, z ≠ y → swap z y ∉ W} = m := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype]
    have : (Finset.univ.filter fun z : Fin m => ∀ y, z ≠ y → swap z y ∉ W) =
        Finset.univ.filter fun z : Fin m => ¬ (Classif.partner hP.twoGroup z ≠ z) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      constructor
      · intro hz
        by_contra hne
        obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
        exact hz y hy1 hy2
      · intro hz y hy1 hy2
        have := Classif.partner_eq_of_swap_mem hP.twoGroup hy1 hy2
        rw [hz] at this
        exact hy1 this
    rw [this, Finset.card_filter_add_card_filter_not (s := Finset.univ), Finset.card_univ,
      Fintype.card_fin]
  have hN3 : 3 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} := by omega
  by_cases hfour : Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} = 4
  · exact (false_of_four_isoPairs hA hL hSL hm hNS hθS hfour).elim
  have hcnt : Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} = 3 ∨
      5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} := by omega
  by_cases hmoved : ∃ p q : Fin m, IsIsoPair W p q ∧ ∃ s : ↥(L ⊔ S), (s : G) ∈ S ∧
      θ s p ≠ p ∧ θ s p ≠ q
  · obtain ⟨p, q, hpq, s, hsS, hs1, hs2⟩ := hmoved
    exact (false_of_moved_isoPair hX hA hL hm e hNS hθS hunm hpq s hsS hs1 hs2 hcnt).elim
  · push Not at hmoved
    exact h G X S L hX hA hL m hm e hN θ hNS hθS A hAm x hx hunm hcnt fun p q hpq s hsS => by
      by_cases h1 : θ s p = p
      · exact Or.inl h1
      · exact Or.inr (hmoved p q hpq s hsS h1)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
