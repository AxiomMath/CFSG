module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClFourNode
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLambda

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.Quasithin CFSG.AGLEmbedding CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique

namespace Classif

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)}

theorem unmatched_iff_true (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W) {σ : Perm Ω}
    {c : Ω → Bool} (hB : BlockData E σ c)
    (h3 : 3 ≤ (Finset.univ.filter fun y => c y = true).card)
    (hex : ∃ z, partner hW z = z) (y : Ω) : partner hW y = y ↔ c y = true := by
  classical
  obtain ⟨h1, h2, h3', h4, h5, h6⟩ := hB
  have hωω := partner_partner hW
  have hωinj : ∀ {x y}, partner hW x = partner hW y → x = y := fun {x y} h => by
    have := congrArg (partner hW) h
    rwa [hωω, hωω] at this
  have hfalse : ∀ y, c y = false → partner hW y ≠ y := by
    intro y hy
    have hsw : swap y (σ y) ∈ E := by
      by_contra hn
      have := (h5 y).2 hn
      rw [hy] at this
      exact Bool.false_ne_true this
    rw [partner_eq_of_swap_mem hW (Ne.symm (h1 y)) (hEW hsw)]
    exact h1 y
  constructor
  · intro hy
    by_contra hcy
    exact hfalse y (by simpa using hcy) hy
  · intro hcy
    obtain ⟨z, hz⟩ := hex
    have hcz : c z = true := by
      by_contra hn
      exact hfalse z (by simpa using hn) hz
    have hσz : σ z ≠ z := h1 z
    have hdmem : ∀ y', c y' = true → y' ≠ z → y' ≠ σ z → swap z (σ z) * swap y' (σ y') ∈ E :=
      fun y' hy' hy'z hy'σz =>
        h6 (Subgroup.subset_closure ⟨z, y', hy'z, hy'σz, by rw [hy', hcz], rfl⟩)
    have hdz : ∀ y', y' ≠ z → y' ≠ σ z → (swap z (σ z) * swap y' (σ y')) z = σ z := by
      intro y' hy'z hy'σz
      have hz1 : z ≠ y' := Ne.symm hy'z
      have hz2 : z ≠ σ y' := fun h => hy'σz (by rw [h, h2])
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hz1 hz2, swap_apply_left]
    obtain ⟨y0, hy0t, hy0⟩ : ∃ y0, y0 ∈ Finset.univ.filter (fun y => c y = true) ∧
        y0 ∉ ({z, σ z} : Finset Ω) := by
      apply Finset.exists_mem_notMem_of_card_lt_card
      exact lt_of_le_of_lt Finset.card_le_two (by omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hy0t hy0
    have hA : partner hW (σ z) = σ z := by
      have hcomm := partner_comm hW (hEW (hdmem y0 hy0t hy0.1 hy0.2)) z
      rw [hdz y0 hy0.1 hy0.2, hz] at hcomm
      have hdz' : (swap z (σ z) * swap y0 (σ y0)) z = σ z := hdz y0 hy0.1 hy0.2
      rw [hdz'] at hcomm
      exact hcomm
    have hout : ∀ y', c y' = true → y' ≠ z → y' ≠ σ z → partner hW y' = y' := by
      intro y' hy' hy'z hy'σz
      by_contra hmatched
      have hd := hdmem y' hy' hy'z hy'σz
      have hcomm := partner_comm hW (hEW hd) y'
      have hσy'z : σ y' ≠ z := fun h => hy'σz (by rw [← h, h2])
      have hσy'σz : σ y' ≠ σ z := fun h => hy'z (by
        have := congrArg σ h; rwa [h2, h2] at this)
      have hdy : (swap z (σ z) * swap y' (σ y')) y' = σ y' := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hσy'z hσy'σz]
      rw [hdy] at hcomm
      have hne2 : partner hW y' ≠ z := fun h => hy'z (by
        have := congrArg (partner hW) h; rwa [hωω, hz] at this)
      have hne3 : partner hW y' ≠ σ z := fun h => hy'σz (by
        have := congrArg (partner hW) h; rwa [hωω, hA] at this)
      have hωy' : partner hW y' = σ y' := by
        by_contra hne
        have hdu : (swap z (σ z) * swap y' (σ y')) (partner hW y') = partner hW y' := by
          rw [Perm.mul_apply, swap_apply_of_ne_of_ne hmatched hne,
            swap_apply_of_ne_of_ne hne2 hne3]
        rw [hdu] at hcomm
        exact h1 y' (hωinj hcomm)
      have hsw' : swap y' (σ y') ∈ W := by
        rw [← hωy']; exact swap_partner_mem hW hmatched
      have hmem : swap z (σ z) ∈ W := by
        have := W.mul_mem (hEW hd) hsw'
        rwa [mul_assoc, swap_mul_self, mul_one] at this
      have := partner_eq_of_swap_mem hW (Ne.symm hσz) hmem
      rw [hz] at this
      exact hσz this.symm
    by_cases hyz : y = z
    · rw [hyz]; exact hz
    by_cases hyσz : y = σ z
    · rw [hyσz]; exact hA
    exact hout y hcy hyz hyσz

end Classif

variable {G : Type} [Group G] [Finite G]

theorem colourFour_shape {S L : Subgroup G} {d : ℕ} (hd : 8 < d) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hS2 : IsPGroup 2 S)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ))
    {A : Subgroup G} (hAm : IsMaxElemAbelian S A) {σ : Perm (Fin d)} {c : Fin d → Bool}
    (hB : BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c) {x : Fin d} (hx : (cls c x).card = 4)
    (hunm : ∃ z : Fin d, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d)))) :
    ∃ hP : Classif.Pre (((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
        (fun A : {A : Subgroup G // IsMaxElemAbelian S A} => (A.1.subgroupOf (L ⊔ S)).map θ),
      (∀ y, Classif.partner hP.twoGroup y = y ↔ c y = true) ∧
      ((Finset.univ.filter fun y : Fin d => c y = false).card = 4 ∨
        (Finset.univ.filter fun y : Fin d => c y = true).card = 4) := by
  classical
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  refine ⟨hP, ?_, ?_⟩
  · have hAJ : A ≤ thompsonJ S :=
      le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
    have hEW : (A.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ :=
      Subgroup.map_mono (Subgroup.comap_mono hAJ)
    have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
      obtain ⟨z, hz⟩ := hunm
      refine ⟨z, ?_⟩
      by_contra hne
      obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
      exact hz y hy1 hy2
    have htot : (Finset.univ.filter fun y : Fin d => c y = false).card +
        (Finset.univ.filter fun y : Fin d => c y = true).card = d := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d)))
        (fun y => c y = false)
      simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hcls : (cls c x).card = (Finset.univ.filter fun y : Fin d => c y = c x).card := rfl
    have h3 : 3 ≤ (Finset.univ.filter fun y : Fin d => c y = true).card := by
      cases hcx : c x
      · rw [hcls, hcx] at hx; omega
      · rw [hcls, hcx] at hx; omega
    exact fun y => Classif.unmatched_iff_true hP.twoGroup hEW hB h3 hex y
  · cases hcx : c x
    · left; have : (cls c x).card = (Finset.univ.filter fun y : Fin d => c y = c x).card := rfl
      rw [hcx] at this; omega
    · right; have : (cls c x).card = (Finset.univ.filter fun y : Fin d => c y = c x).card := rfl
      rw [hcx] at this; omega

open scoped Classical in
@[expose] def EightTenNodeColourFourTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A →
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c → ∀ x, (cls c x).card = 4 →
      (∃ z : Fin m, ∀ y, z ≠ y →
        swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) →
      Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 2 →
      (∀ y : Fin m, (∀ z, y ≠ z →
          swap y z ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ↔
        c y = true) →
      EightTenOutcomes X S L

open scoped Classical in
@[expose] def EightTenNodeColourFourLam4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A →
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c → ∀ x, (cls c x).card = 4 →
      (∃ z : Fin m, ∀ y, z ≠ y →
        swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) →
      (Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
        5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y}) →
      (∀ y : Fin m, (∀ z, y ≠ z →
          swap y z ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ↔
        c y = true) →
      (Finset.univ.filter fun y : Fin m => c y = true).card = 4 →
      (∀ p q : Fin m, IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q →
        ∀ s : ↥(L ⊔ S), (s : G) ∈ S → θ s p = p ∨ θ s p = q) →
      EightTenOutcomes X S L

theorem eightTenNodeColourFour_of_two_lam4 (h2 : EightTenNodeColourFourTwo)
    (h4 : EightTenNodeColourFourLam4) : EightTenNodeColourFour := by
  refine eightTenNodeColourFour_of_unmatched ?_
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm
  classical
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  obtain ⟨hP, hiff, hcls⟩ := colourFour_shape hm θ hS2 hsh hAm hbd hx hunm
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  have hiff' : ∀ y : Fin m, (∀ z, y ≠ z → swap y z ∉ W) ↔ c y = true := by
    intro y
    rw [← hiff y]
    constructor
    · intro h
      by_contra hne
      obtain ⟨z, hz1, hz2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
      exact h z hz1 hz2
    · intro h z hz1 hz2
      have := Classif.partner_eq_of_swap_mem hP.twoGroup hz1 hz2
      rw [h] at this
      exact hz1 this
  have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
    obtain ⟨z, hz⟩ := hunm
    refine ⟨z, ?_⟩
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  have h2N : 2 * Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} =
      Nat.card {z : Fin m // Classif.partner hP.twoGroup z ≠ z} := hP.two_mul_isoCount_eq hex
  have hMcard : Nat.card {z : Fin m // Classif.partner hP.twoGroup z ≠ z} =
      (Finset.univ.filter fun y : Fin m => c y = false).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Ne, hiff y]
    simp
  have htot : (Finset.univ.filter fun y : Fin m => c y = false).card +
      (Finset.univ.filter fun y : Fin m => c y = true).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun y => c y = false)
    simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at this
    exact this
  rcases hcls with hF | hT
  ·
    have hN2 : Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} = 2 := by omega
    exact h2 G X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hN2 hiff'
  · by_cases hfour : Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} = 4
    · exact (false_of_four_isoPairs hA hL hSL hm hNS hθS hfour).elim
    have hcnt : Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} = 3 ∨
        5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} := by omega
    by_cases hmoved : ∃ p q : Fin m, IsIsoPair W p q ∧ ∃ s : ↥(L ⊔ S), (s : G) ∈ S ∧
        θ s p ≠ p ∧ θ s p ≠ q
    · obtain ⟨p, q, hpq, s, hsS, hs1, hs2⟩ := hmoved
      exact (false_of_moved_isoPair hX hA hL hm e hNS hθS hunm hpq s hsS hs1 hs2 hcnt).elim
    · push Not at hmoved
      exact h4 G X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hcnt hiff' hT
        fun p q hpq s hsS => by
          by_cases h1 : θ s p = p
          · exact Or.inl h1
          · exact Or.inr (hmoved p q hpq s hsS h1)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
