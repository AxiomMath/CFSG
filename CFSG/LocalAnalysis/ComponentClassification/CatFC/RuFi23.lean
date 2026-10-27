module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Arms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrderBig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Induction.Balance (IsAltType)
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)

@[expose] def SporadicRowsFor (s : TauCeti.SporadicName) : Prop :=
  ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (S ≃* Carrier s) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      ∀ {D : Subgroup ↥(fixedSubgroup σ)}, IsComponent D →
        (σ ∈ (MulAut.conj : S →* MulAut S).range →
          SporadicInnerRow s (Nat.card (↥D ⧸ center ↥D))) ∧
        (σ ∉ (MulAut.conj : S →* MulAut S).range →
          SporadicOuterRow s (Nat.card (↥D ⧸ center ↥D)))

theorem sporOrder_eq_sporOrd (s : TauCeti.SporadicName) :
    sporOrder s = AGLEmbedding.sporOrd s := by
  cases s <;> norm_num [sporOrder, sporFactors, AGLEmbedding.sporOrd]

theorem ru_cases (s : TauCeti.SporadicName) (h : sporOrder .Ru ∣ sporOrder s) :
    s = .Ru ∨ s = .M := by
  rw [sporOrder_eq_sporOrd, sporOrder_eq_sporOrd] at h
  cases s <;> first
    | (left; rfl)
    | (right; rfl)
    | exact absurd h (by simp only [AGLEmbedding.sporOrd]; decide)

theorem fi23_cases (s : TauCeti.SporadicName) (h : sporOrder .Fi23 ∣ sporOrder s) :
    s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M := by
  rw [sporOrder_eq_sporOrd, sporOrder_eq_sporOrd] at h
  cases s <;> first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; left; rfl)
    | (right; right; right; rfl)
    | exact absurd h (by simp only [AGLEmbedding.sporOrd]; decide)

theorem ru_rows (s : TauCeti.SporadicName) (h : s = .Ru ∨ s = .M) :
    ¬ SporadicInnerRow s (sporOrder .Ru) ∧ ¬ SporadicOuterRow s (sporOrder .Ru) := by
  rw [sporOrder_eq_sporOrd]
  rcases h with rfl | rfl <;>
    simp only [SporadicInnerRow, SporadicOuterRow, AGLEmbedding.sporOrd] <;> decide

theorem fi23_rows (s : TauCeti.SporadicName)
    (h : s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M) :
    ¬ SporadicInnerRow s (sporOrder .Fi23) ∧
      (SporadicOuterRow s (sporOrder .Fi23) → s = .Fi24Prime) := by
  rw [sporOrder_eq_sporOrd]
  rcases h with rfl | rfl | rfl | rfl <;>
    simp only [SporadicInnerRow, SporadicOuterRow, AGLEmbedding.sporOrd] <;> decide

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem card_quotient_center_dvd {σ : MulAut S} (D : Subgroup ↥(fixedSubgroup σ)) :
    Nat.card (↥D ⧸ center ↥D) ∣ Nat.card S :=
  (Subgroup.card_quotient_dvd_card _).trans
    ((Subgroup.card_subgroup_dvd_card D).trans (Subgroup.card_subgroup_dvd_card _))

theorem sporadicRep_of_component
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) (hnotalt : ¬ IsAltType S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D)
    {s : TauCeti.SporadicName} (hc : Nat.card (↥D ⧸ center ↥D) = sporOrder s)
    (hne2 : ∀ {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}, StatedLieAdmissible t n 2 f →
      LieModel X t n 2 f → Nat.card X ≠ sporOrder s) :
    SporadicRep S := by
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).1 hcat with
    ⟨n, hn, hA⟩ | hodd | heven | hsp
  · exact absurd ⟨n, hn, hA⟩ hnotalt
  · exact (false_of_oddLie_fixedComponent hGLS hO hodd hσ hD hc).elim
  · exact (false_of_evenLie_fixedComponent hEI hEO hO hna heven hσ hD hc hne2).elim
  · exact hsp

theorem fixedComponent_of_oddCover {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hF : FStarSimple N) (hidx : N.index ≤ 2) {M : Subgroup H} {v : H} (hv : orderOf v = 2)
    (hMc : IsCompIn M (centralizer ({v} : Set H))) {s : TauCeti.SporadicName}
    (hodd : OddCover s M) (hcard : Nat.card (Carrier s) = sporOrder s) :
    ∃ (σ : MulAut ↥N) (D : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 ∧ IsComponent D ∧
      (v ∈ N → σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range) ∧ M ≤ N ∧
      Nat.card (↥D ⧸ center ↥D) = sporOrder s := by
  have := hF.normal
  have hMN : M ≤ N := Hyp.le_of_perfect_of_index_le_two hidx hodd.1.1
  obtain ⟨σ, D, hσ, hD, hin, ⟨e⟩⟩ := exists_fixedComponent hF hv hMc hMN
  obtain ⟨g⟩ := hodd.2.2
  refine ⟨σ, D, hσ, hD, hin, hMN, ?_⟩
  rw [Nat.card_congr ((quotientCenterEquiv e).trans g).toEquiv, hcard]

theorem catalogNoRu_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hRu : SporadicRowsFor .Ru) (hM : SporadicRowsFor .M) : Balance.CatalogNoRu := by
  intro H _ _ N hF hidx hcat hnotalt M v hv hMc hodd
  have hSimple := hF.isSimpleGroup
  have hna := hF.nonabelian
  obtain ⟨σ, D, hσ, hD, -, -, hc⟩ :=
    fixedComponent_of_oddCover hF hidx hv hMc hodd (hcard .Ru (by decide))
  have hne2 : ∀ {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ},
      StatedLieAdmissible t n 2 f → LieModel X t n 2 f → Nat.card X ≠ sporOrder .Ru := by
    intro X _ t n f hadm hX
    rw [sporOrder_eq_sporOrd]
    exact lieModel_two_card_ne_ru hO hadm hX
  obtain ⟨s, ⟨es⟩⟩ := sporadicRep_of_component hGLS hEI hEO hO hna hcat hnotalt hσ hD hc hne2
  by_cases hsM : s = .M
  · subst hsM
    obtain ⟨hin, hout⟩ := hM hSimple hna es hσ hD
    rw [hc] at hin hout
    by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
    · exact (ru_rows .M (Or.inr rfl)).1 (hin hinn)
    · exact (ru_rows .M (Or.inr rfl)).2 (hout hinn)
  · have hcs : Nat.card ↥N = sporOrder s := (Nat.card_congr es.toEquiv).trans (hcard s hsM)
    have hdvd : sporOrder .Ru ∣ sporOrder s := by
      rw [← hc, ← hcs]
      exact card_quotient_center_dvd D
    rcases ru_cases s hdvd with rfl | rfl
    · obtain ⟨hin, hout⟩ := hRu hSimple hna es hσ hD
      rw [hc] at hin hout
      by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
      · exact (ru_rows .Ru (Or.inl rfl)).1 (hin hinn)
      · exact (ru_rows .Ru (Or.inl rfl)).2 (hout hinn)
    · exact absurd rfl hsM

theorem catalogFi23Host_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hsc : Fi.V3.Fi23SelfCentralizing)
    (hFi23 : SporadicRowsFor .Fi23) (hFi24 : SporadicRowsFor .Fi24Prime)
    (hB : SporadicRowsFor .B) (hM : SporadicRowsFor .M) : Balance.CatalogFi23Host := by
  intro H _ _ N hF hidx hcat hnotalt L t ht hLc hodd
  have := hF.normal
  have hSimple := hF.isSimpleGroup
  have hna := hF.nonabelian
  obtain ⟨σ, D, hσ, hD, hinner, hLN, hc⟩ :=
    fixedComponent_of_oddCover hF hidx ht hLc hodd (hcard .Fi23 (by decide))
  have hne2 : ∀ {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ},
      StatedLieAdmissible t n 2 f → LieModel X t n 2 f → Nat.card X ≠ sporOrder .Fi23 := by
    intro X _ t n f hadm hX
    rw [sporOrder_eq_sporOrd]
    exact lieModel_two_card_ne_fi23 hO hadm hX
  obtain ⟨s, ⟨es⟩⟩ := sporadicRep_of_component hGLS hEI hEO hO hna hcat hnotalt hσ hD hc hne2
  have key : σ ∉ (MulAut.conj : ↥N →* MulAut ↥N).range ∧
      Nonempty (↥N ≃* Carrier .Fi24Prime) := by
    by_cases hsM : s = .M
    · subst hsM
      obtain ⟨hin, hout⟩ := hM hSimple hna es hσ hD
      rw [hc] at hin hout
      by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
      · exact absurd (hin hinn) (fi23_rows .M (Or.inr (Or.inr (Or.inr rfl)))).1
      · exact absurd ((fi23_rows .M (Or.inr (Or.inr (Or.inr rfl)))).2 (hout hinn)) (by decide)
    · have hcs : Nat.card ↥N = sporOrder s := (Nat.card_congr es.toEquiv).trans (hcard s hsM)
      have hdvd : sporOrder .Fi23 ∣ sporOrder s := by
        rw [← hc, ← hcs]
        exact card_quotient_center_dvd D
      rcases fi23_cases s hdvd with rfl | rfl | rfl | rfl
      · obtain ⟨hin, hout⟩ := hFi23 hSimple hna es hσ hD
        rw [hc] at hin hout
        by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
        · exact absurd (hin hinn) (fi23_rows .Fi23 (Or.inl rfl)).1
        · exact absurd ((fi23_rows .Fi23 (Or.inl rfl)).2 (hout hinn)) (by decide)
      · obtain ⟨hin, hout⟩ := hFi24 hSimple hna es hσ hD
        rw [hc] at hin hout
        by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
        · exact absurd (hin hinn) (fi23_rows .Fi24Prime (Or.inr (Or.inl rfl))).1
        · exact ⟨hinn, ⟨es⟩⟩
      · obtain ⟨hin, hout⟩ := hB hSimple hna es hσ hD
        rw [hc] at hin hout
        by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
        · exact absurd (hin hinn) (fi23_rows .B (Or.inr (Or.inr (Or.inl rfl)))).1
        · exact absurd ((fi23_rows .B (Or.inr (Or.inr (Or.inl rfl)))).2 (hout hinn)) (by decide)
      · exact absurd rfl hsM
  obtain ⟨hout, ⟨eN⟩⟩ := key
  have htN : t ∉ N := fun htN => hout (hinner htN)
  refine ⟨htN, ?_⟩
  have hZN : center ↥N = ⊥ := center_eq_bot_of_fStarSimple hF
  have hOdd : OddCover .Fi24Prime N :=
    ⟨hF.isQuasisimple, by rw [hZN, Subgroup.card_bot]; exact odd_one,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZN).trans QuotientGroup.quotientBot).trans eN⟩⟩
  have hCN : ∀ x ∈ N, (∀ k ∈ L, k * x = x * k) → x = 1 := by
    intro x hxN hxk
    have hcomm := hsc H N L hOdd hLN hodd.1 hodd.2.2 x hxN hxk
    have hxC : x ∈ centralizer (N : Set H) := mem_centralizer_iff.2 fun l hl => hcomm l hl
    rw [hF.centralizer_eq_bot, Subgroup.mem_bot] at hxC
    exact hxC
  have htC : ∀ k ∈ L, k * t = t * k := fun k hk => mem_centralizer_singleton_iff.1 (hLc.1 hk)
  have hindex : N.index = 2 := by
    have h1 : N.index ≠ 1 := fun h =>
      htN (by rw [Subgroup.index_eq_one.1 h]; exact Subgroup.mem_top t)
    have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  apply le_antisymm
  · intro x hx
    have hxk : ∀ k ∈ L, k * x = x * k := fun k hk => mem_centralizer_iff.1 hx k hk
    by_cases hxN : x ∈ N
    · rw [hCN x hxN hxk]
      exact Subgroup.one_mem _
    · have hxt : x * t ∈ N :=
        (Subgroup.mul_mem_iff_of_index_two hindex).2 (iff_of_false hxN htN)
      have h1 : x * t = 1 := hCN _ hxt fun k hk => by
        calc k * (x * t) = (k * x) * t := by group
          _ = x * (k * t) := by rw [hxk k hk]; group
          _ = x * t * k := by rw [htC k hk]; group
      have : x = t⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers t)
  · rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 htC

end CFSG.ComponentClassification.CatFC
