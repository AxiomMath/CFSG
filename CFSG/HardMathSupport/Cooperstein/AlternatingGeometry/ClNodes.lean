module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClQuadNode
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenResidualSplit

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem theta_node_data {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    {θ : ↥(L ⊔ S) →* Perm (Fin m)} (hNS : NaturalSectionTheta S L m θ) :
    S ≤ Subgroup.normalizer (L : Set G) ∧ Asc81bHyp (L ⊔ S) S ∧ IsTwoPrimeComponent (L ⊔ S) L ∧
      pCoreOf 2 (L ⊔ S) ≤ S ∧ (∀ m' : ↥(L ⊔ S), θ m' = 1 ↔ (m' : G) ∈ pCoreOf 2 (L ⊔ S)) ∧
      (∀ A : Subgroup G, IsMaxElemAbelian S A →
        Offender.OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ)) := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_barM_sup_eq_one hA' hLs hSL hm e)
  have hVS : blockV S L ≤ S := Coordinator.blockV_le hA hL hSL
  have hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    Coordinator.sup_le_normalizer_blockV S L
  have hV : CFSG.Open.IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hpS : pCoreOf 2 (L ⊔ S) ≤ S := Coordinator.twoCore_sup_le hA hL hSL
  obtain ⟨π, hπ, hkerπ, hAd, hequiv, hker⟩ := hNS
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hl' : l ∈ Subgroup.normalizer (blockV S L : Set G) := hVN (Subgroup.mem_sup_left hl)
    have h1 : l * v⁻¹ * l⁻¹ ∈ blockV S L := by
      have := (Subgroup.mem_normalizer_iff.1 hl' v⁻¹).1 ((blockV S L).inv_mem hv)
      simpa [mul_assoc] using this
    simpa [commutatorElement_def, mul_assoc] using (blockV S L).mul_mem hv h1
  have hkerC := theta_eq_one_iff (by omega) hπ hequiv hUV hker
  refine ⟨hSL, hA', hLs, hpS, ?_, ?_⟩
  · intro m'
    rw [hkerC]
    constructor
    · intro h
      exact inf_centralizer_blockV_le_pCoreOf hA' hLs hSL
        (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ ⟨m'.2, h⟩
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (CFSG.HardMathSupport.Cooperstein.StructureLie.commute_of_mem_pCoreOf_blockV h hv).symm
  · intro A hAm
    exact offender_shape_of_section (Or.inr (by omega)) hπ hequiv (isElemAb2_of_isElemAbelian hV) hVS
      hUV (isElemAb2_of_isElemAbelian hAm.2.1) hAm.1 (hAm.1.trans le_sup_right)
      (fun B hBS hB => hAm.2.2 B hBS (isElemAbelian_of_isElemAb2 hB)) hker

theorem orbits_two_of_matched {X S L : Subgroup G} (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 9 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ))
    (hall : ∀ z : Fin N, ∃ y, z ≠ y ∧
      swap z y ∈ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N)))) (z : Fin N) :
    Nat.card (orbit (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) z) = 2 := by
  classical
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin N)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  have hmatch : ∀ z : Fin N, Classif.partner hP.twoGroup z ≠ z := fun z =>
    (Classif.partner_ne_iff hP.twoGroup).2 (hall z)
  let St : Classif.Setup W _ := ⟨hP, hmatch⟩
  rcases St.card_orbit z with h | h
  · exact h
  · exact (false_of_matched_quad hA hL hSL hN hNS hθS hsh hall h).elim

theorem exists_unmatched_of_fourOrbit {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 9 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ))
    {A : Subgroup G} (hAm : IsMaxElemAbelian S A) {x : Fin N}
    (hx : Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4) :
    ∃ z : Fin N, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) := by
  by_contra hcon
  push Not at hcon
  have h2 := orbits_two_of_matched hA hL hSL hN hNS hθS hsh hcon x
  have hAJ : A ≤ thompsonJ S := le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hsub : (orbit ((A.subgroupOf (L ⊔ S)).map θ) x : Set (Fin N)) ⊆
      orbit (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) x := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, Subgroup.map_mono (Subgroup.comap_mono hAJ) hg⟩, rfl⟩
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h3
  omega

theorem outcomes_of_matched_iso {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) {θ : ↥(L ⊔ S) →* Perm (Fin m)}
    (hNS : NaturalSectionTheta S L m θ) (hθS : ∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S)
    (hall : ∀ z : Fin m, ∃ y, z ≠ y ∧
      swap z y ∈ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) :
    EightTenOutcomes X S L := by
  classical
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hP := pre_of_theta hA'.twoRadical.isPGroup (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  have hmatch : ∀ z : Fin m, Classif.partner hP.twoGroup z ≠ z := fun z =>
    (Classif.partner_ne_iff hP.twoGroup).2 (hall z)
  let St : Classif.Setup W _ := ⟨hP, hmatch⟩
  have h2 := orbits_two_of_matched hA hL hSL (by omega) hNS hθS hsh hall
  have hiso : ∀ z, IsIsoPair W z (St.ω z) := fun z => St.isIsoPair_of_card_orbit_two (h2 z)
  have hσ2 : ∀ x, St.ω (St.ω x) = x := St.ωω
  obtain ⟨ι, _, _, eι, hcard, -⟩ := exists_blockEquiv St.ω (fun x => St.hmatch x) hσ2
  have hmn : Fintype.card (Fin m) = 2 * Fintype.card ι := hcard
  have hn5 : 5 ≤ Fintype.card ι := by simp at hmn; omega
  have hAltL : ∀ x ∈ alternatingGroup (Fin m),
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x := by
    obtain ⟨-, -, -, h, -, -⟩ := hNS
    exact h
  have hout : ∀ (T : Finset (Fin m)), T = Finset.univ.filter (fun x : Fin m =>
      swap x (St.ω x) ∈ W) → T = Finset.univ := by
    intro T hT
    rw [hT]
    exact Finset.filter_true_of_mem fun x _ => (hiso x).2.1
  have hPA := pairActionData_of_theta_perm hA' hLs hSL hpS θ hkerP hAltL St.ω
    (fun x => St.hmatch x) hσ2 (Fintype.card ι) hmn hn5
    (fun w hw z => (hiso z).2.2 w hw)
    (fun x y _ _ h => absurd (hiso x).2.1 h)
    (by
      have : (Finset.univ.filter fun x : Fin m => swap x (St.ω x) ∉ W) = ∅ := by
        ext x; simp [(hiso x).2.1]
      rw [this]; simp)
    (by
      have : (Finset.univ.filter fun x : Fin m => swap x (St.ω x) ∉ W) = ∅ := by
        ext x; simp [(hiso x).2.1]
      rw [this]; simp)
    (by
      have : (Finset.univ.filter fun x : Fin m => swap x (St.ω x) ∉ W) = ∅ := by
        ext x; simp [(hiso x).2.1]
      rw [this]; simp)
    (by
      have : (Finset.univ.filter fun x : Fin m => swap x (St.ω x) ∈ W) = Finset.univ :=
        hout _ rfl
      rw [this, Finset.card_univ]; simp; omega)
    (by
      have : (Finset.univ.filter fun x : Fin m => swap x (St.ω x) ∈ W) = Finset.univ :=
        hout _ rfl
      rw [this, Finset.card_univ]; simp; omega)
  refine Or.inr (Or.inr (Or.inl ⟨Fintype.card ι, hn5, hPA, ?_⟩))
  have h2n : 2 * Fintype.card ι = m := by simp at hmn; omega
  rw [h2n]
  exact hN.naturalSectionL

open scoped Classical in
@[expose] def EightTenNodeColourFourUnmatched : Prop :=
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
      EightTenOutcomes X S L

theorem eightTenNodeColourFour_of_unmatched (h : EightTenNodeColourFourUnmatched) :
    EightTenNodeColourFour := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx
  classical
  by_cases hu : ∃ z : Fin m, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))
  · exact h G X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hu
  · push Not at hu
    exact outcomes_of_matched_iso hX hA hL hm e hN hNS hθS hu

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
