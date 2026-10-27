module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR3
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwoAF

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.Quasithin CFSG.AGLEmbedding CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique


open scoped Classical in
theorem eightTenOutcomes_of_blockFix {G : Type} [Group G] [Finite G] {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m)
    {θ : ↥(L ⊔ S) →* Perm (Fin m)} (hNS : NaturalSectionTheta S L m θ)
    {A : Subgroup G} {σ : Perm (Fin m)} {c : Fin m → Bool} (hAm : IsMaxElemAbelian S A)
    (hbd : BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c)
    (hiff' : ∀ y : Fin m, (∀ z, y ≠ z →
        swap y z ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ↔
      c y = true)
    (hSF : ∀ s ∈ (S.subgroupOf (L ⊔ S)).map θ, ∀ y, s y = y ∨ s y = σ y)
    (hT2 : (Finset.univ.filter fun y : Fin m => c y = true).card ≠ 2) :
    EightTenOutcomes X S L := by
  classical
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  obtain ⟨π, hπ, hkerπ, hAd, hequiv, hker⟩ := hNS
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  set Sstar : Subgroup (Perm (Fin m)) := (S.subgroupOf (L ⊔ S)).map θ with hSstar
  obtain ⟨hσ1, hσ2, hg, hc, hcol, hdbl⟩ := hbd
  have hAJ : A ≤ thompsonJ S :=
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : (A.subgroupOf (L ⊔ S)).map θ ≤ W := Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hWS : W ≤ Sstar := Subgroup.map_mono (Subgroup.comap_mono
    (iSup_le fun A => iSup_le fun hA => hA.1 : thompsonJ S ≤ S))
  have hsw : ∀ y, swap y (σ y) ∉ W ↔ c y = true := by
    intro y
    constructor
    · intro h
      exact (hcol y).2 fun h' => h (hEW h')
    · intro h hmem
      exact (hiff' y).2 h (σ y) (Ne.symm (hσ1 y)) hmem
  have hsetT : (Finset.univ.filter fun y : Fin m => swap y (σ y) ∉ W) =
      Finset.univ.filter fun y : Fin m => c y = true := by
    ext y; simp [hsw y]
  have hle : W ≤ pairPres σ hσ1 hσ2 := by
    intro w hw y
    exact (hSF w (hWS hw) y)
  have hD : ∀ x y, y ≠ x → y ≠ σ x → swap x (σ x) ∉ W → swap y (σ y) ∉ W →
      swap x (σ x) * swap y (σ y) ∈ W := by
    intro x y hyx hyσ hx' hy'
    have hcx := (hsw x).1 hx'
    have hcy := (hsw y).1 hy'
    exact hEW (hdbl (Subgroup.subset_closure ⟨x, y, hyx, hyσ, hcy.trans hcx.symm, rfl⟩))
  have hN1 : (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉ W).card ≠ 2 * 1 := by
    rw [hsetT]; exact hT2
  obtain ⟨ι, i1, i2, eι, hcard, -⟩ := exists_blockEquiv σ hσ1 hσ2
  have hmn : 2 * Fintype.card ι = m := by simpa using hcard.symm
  refine Or.inr (Or.inr (Or.inl ⟨Fintype.card ι, by omega, ?_, ?_⟩))
  · refine pairActionData_of_theta_perm_of_le hA' hLs hSL hpS θ hkerP
      (fun x hx => ?_) σ hσ1 hσ2 (Fintype.card ι) (by simpa using hmn.symm) (by omega) hSF hD hN1
    obtain ⟨l, hl⟩ := hAd x hx
    exact ⟨l, hl⟩
  · have := hN.naturalSectionL
    rwa [← hmn] at this

open scoped Classical in
@[expose] def EightTenNodeColourFourTwoMove : Prop :=
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
      (∃ s : Perm (Fin m), s ∈ (S.subgroupOf (L ⊔ S)).map θ ∧ ∃ y, s y ≠ y ∧ s y ≠ σ y) →
      EightTenOutcomes X S L

theorem eightTenNodeColourFourTwo_of_move (hMove : EightTenNodeColourFourTwoMove) :
    EightTenNodeColourFourTwo := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hN2 hiff'
  classical
  by_cases hSF : ∀ s ∈ (S.subgroupOf (L ⊔ S)).map θ, ∀ y, s y = y ∨ s y = σ y
  swap
  · push Not at hSF
    obtain ⟨s, hs, y, hy1, hy2⟩ := hSF
    exact hMove G X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hN2 hiff'
      ⟨s, hs, y, hy1, hy2⟩
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  have hiffP : ∀ y, Classif.partner hP.twoGroup y = y ↔ c y = true := by
    intro y
    rw [← hiff' y]
    constructor
    · intro h z hz1 hz2
      have := Classif.partner_eq_of_swap_mem hP.twoGroup hz1 hz2
      rw [h] at this
      exact hz1 this
    · intro h
      by_contra hne
      obtain ⟨z, hz1, hz2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
      exact h z hz1 hz2
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
    rw [Ne, hiffP y]
    simp
  have htot : (Finset.univ.filter fun y : Fin m => c y = false).card +
      (Finset.univ.filter fun y : Fin m => c y = true).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun y => c y = false)
    simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hTne : (Finset.univ.filter fun y : Fin m => c y = true).card ≠ 2 := by omega
  exact eightTenOutcomes_of_blockFix hX hA hL hm e hN hNS hAm hbd hiff' hSF hTne

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
