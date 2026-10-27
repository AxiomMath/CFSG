module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Inv
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement MatrixGroups

structure TransSection (p f : ℕ) [Fact p.Prime] {X : Type} [Group X] (Φ : Set (Subgroup X)) :
    Prop where
  hyp : HypOmegaMod p f Φ
  oddCore : classicalInvolutionOddCore X = ⊥
  gen : omegaGen Φ = ⊤
  trans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J

section Datum

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem OmegaLie.card_eq_one_of_transitive (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    (hgen : omegaGen Φ = ⊤) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hne : Φ.Nonempty) : D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨i₀, hKi₀⟩ := D.exists_comp_of_mem hK
  have hall : ∀ L ∈ Φ, L ≤ D.comp i₀ := by
    intro L hL
    obtain ⟨g, rfl⟩ := htrans K hK L hL
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := D.mem_comp_conj (g := g) (hgen ▸ Subgroup.mem_top g) (hKi₀ hx)
    simpa [mul_assoc] using this
  have hsub : ∀ j : Fin D.card, j = i₀ := by
    intro j
    by_contra hji
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    obtain ⟨z, hz⟩ := hΦ.classical _ hRΦ
    obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
    have hxj : x ∈ D.comp j := Subgroup.map_le_range _ _ hx
    exact hxy (D.comp_commute hji x hxj y (hall _ hRΦ hy))
  have hle : D.card ≤ 1 := Fin.subsingleton_iff_le_one.mp ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have hpos : 0 < D.card := i₀.pos
  omega

theorem OmegaLie.hom_surjective_of_gen (D : OmegaLie p f Φ) (hcard : D.card = 1)
    (hgen : omegaGen Φ = ⊤) (i : Fin D.card) : Function.Surjective (D.hom i) := by
  refine MonoidHom.range_eq_top.mp ?_
  have h1 : (⨆ j, D.comp j) = D.comp i :=
    le_antisymm (iSup_le fun j => by rw [D.index_eq hcard j i]) (le_iSup D.comp i)
  rw [← D.iSup_comp] at hgen
  show D.comp i = ⊤
  rw [← h1]
  exact hgen

variable [Finite X]

theorem sect_exists_datum {n : ℕ} (hn : CITBelowU p f n) (hlt : Nat.card X < n)
    (hΦ : HypOmegaMod p f Φ) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (hne : Φ.Nonempty) :
    ∃ (t : StatedLieTag) (k e : ℕ) (_ : Ih8Model p f Φ t k e), HasLieType p f Φ t k := by
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΦ.conjInvariant hΦ.classical hne hO hlt
  have hcard := D.card_eq_one_of_transitive hΦ hgen htrans hne
  let i : Fin D.card := ⟨0, by omega⟩
  have hsurj := D.hom_surjective_of_gen hcard hgen i
  exact ⟨D.tag i, D.rank i, D.exp i,
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := hsurj
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => D.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g },
    D, hcard, i, rfl, rfl⟩

theorem TransSection.exists_datum {n : ℕ} (hn : CITBelowU p f n) (hlt : Nat.card X < n)
    (h : TransSection p f Φ) (hne : Φ.Nonempty) :
    ∃ (t : StatedLieTag) (k e : ℕ) (_ : Ih8Model p f Φ t k e), HasLieType p f Φ t k :=
  sect_exists_datum hn hlt h.hyp h.oddCore h.gen h.trans hne

end Datum

section Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag}
  {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem Ih8Model.not_psl_two_sect (hp2 : p ≠ 2) (hne : Ω.Nonempty) (htop : (⊤ : Subgroup G) ∉ Ω) :
    ¬ (t = .PSL ∧ k = 2) := by
  rintro ⟨rfl, rfl⟩
  obtain ⟨R, hR⟩ := M.cls_nonempty hne
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 (by decide) (by decide) hR
  have hcard : Nat.card ↥R = Nat.card (modelUniv .PSL 2 p e Fact.out).K := by
    rw [Nat.card_congr eR.toEquiv]
    exact Nat.card_congr (Equiv.refl _)
  have := M.finite_K hp2
  have hRtop : R = ⊤ := Subgroup.eq_top_of_card_eq R hcard
  have hmap : R.map M.ψ = ⊤ := by
    rw [hRtop, Subgroup.map_top, MonoidHom.range_eq_top.mpr M.surj]
  exact htop (hmap ▸ M.map_mem hR)

variable [Finite G]

theorem Ih8Model.twin_stable_sect (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hnpsl : ¬ (t = .PSL ∧ k = 2)) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {A B : Subgroup (modelUniv t k p e Fact.out).K} (hA : A ∈ M.cls) (hB : B ∈ M.cls)
    (hAB : A ≠ B) {z : G} (hzA : IsUniqueInvolution (A.map M.ψ) z)
    (hzB : IsUniqueInvolution (B.map M.ψ) z) {S : Subgroup (modelUniv t k p e Fact.out).K}
    (hS : S ∈ M.cls) (hSA : Commutes S A) : S = B ∨ Commutes S B := by
  have hexA := M.oddCore_eq_bot hΩ hp2 hq hG2 hD4 hA
  have hpA := M.cls_perfect hp2 hD4 hq hA
  have hpB := M.cls_perfect hp2 hD4 hq hB
  have hpS := M.cls_perfect hp2 hD4 hq hS
  have hne' : A.map M.ψ ≠ B.map M.ψ := fun h =>
    hAB (ih8_eq_of_map_eq M.ψ M.ker_le_center hpA hpB h)
  obtain ⟨-, x, hx, x', hx', hψx, hψx', hx'1, hcen⟩ := ih8_twin_data hΩ M.ker_le_center hpA
    (M.map_mem hA) (M.map_mem hB) hne' hzA hzB hexA
  obtain ⟨eB⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hB
  obtain ⟨eS⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hS
  have hodd := M.natCard_galoisField_odd hp2
  have hinj := M.injOn_fund hnpsl (M.cls_sub hB)
  have hx'2 : x' * x' = 1 := by
    apply hinj (x' * x') (B.mul_mem hx' hx')
    rw [map_mul, hψx', hzB.sq]
  have hord : orderOf x' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx'2) hx'1
  have hcS : ∀ s ∈ S, x' * s = s * x' := by
    intro s hs
    have h1 : x * s = s * x := (hSA s hs x hx).symm
    have hcc : ∀ y, y * (x' * x⁻¹) = (x' * x⁻¹) * y := Subgroup.mem_center_iff.mp hcen
    have hx'c : x' = (x' * x⁻¹) * x := by group
    calc x' * s = (x' * x⁻¹) * x * s := by rw [← hx'c]
      _ = (x' * x⁻¹) * (x * s) := mul_assoc _ _ _
      _ = (x' * x⁻¹) * (s * x) := by rw [h1]
      _ = ((x' * x⁻¹) * s) * x := (mul_assoc _ _ _).symm
      _ = (s * (x' * x⁻¹)) * x := by rw [← hcc s]
      _ = s * ((x' * x⁻¹) * x) := mul_assoc _ _ _
      _ = s * x' := by rw [← hx'c]
  have hdich := ih8_stdDichotomy M.isFundTag hG2 hD4 M.admissible
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hBl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hB)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  have ho2 : orderOf (sl2Inv eS) = 2 := orderOf_sl2Inv hodd eS
  have hcomm : x' * sl2Inv eS = sl2Inv eS * x' := hcS _ (sl2Inv_mem eS)
  have hzc : ∀ y ∈ S.map M.ψ, z * y = y * z := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hψx', ← map_mul, ← map_mul, hcS s hs]
  have hz1 : z ∈ B.map M.ψ := hzB.mem
  rcases hdich.map_of_commute hp2 hq' M.ψ M.ker_le_center hBl hSl hx' (sl2Inv_mem eS) hord ho2
    hcomm with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inl (ih8_eq_of_map_eq M.ψ M.ker_le_center hpS hpB h.symm)
  · exact Or.inr (ih8_commutes_of_commutes_map M.ψ M.ker_le_center hpB h).symm
  · exact absurd (LinearBlockStandardPair.eq_one_of_centralizes
      (M.four_le_natCard_galoisField hD4 hq) hW hz1 hzc) hzB.ne_one
  · have hf : 1 ≤ e := M.admissible.2.1
    exact absurd (UnitaryBlockStandardPair.eq_one_of_centralizes
      (CFSG.LieType.Universal.card_galoisField_two_mul p e hf) hq' hW hz1 hzc) hzB.ne_one

theorem Ih8Model.modelTwinClass_two_sect (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hnpsl : ¬ (t = .PSL ∧ k = 2)) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {A B : Subgroup (modelUniv t k p e Fact.out).K} (hA : A ∈ M.cls)
    (hB : B ∈ M.cls) (hAB : A ≠ B) {z : G} (hzA : IsUniqueInvolution (A.map M.ψ) z)
    (hzB : IsUniqueInvolution (B.map M.ψ) z) : Exotic.ModelTwinClass p t k e 2 := by
  have hexA := M.oddCore_eq_bot hΩ hp2 hq hG2 hD4 hA
  have hpA := M.cls_perfect hp2 hD4 hq hA
  have hpB := M.cls_perfect hp2 hD4 hq hB
  have hne' : A.map M.ψ ≠ B.map M.ψ := fun h =>
    hAB (ih8_eq_of_map_eq M.ψ M.ker_le_center hpA hpB h)
  obtain ⟨hcomm, -⟩ := ih8_twin_data hΩ M.ker_le_center hpA (M.map_mem hA) (M.map_mem hB) hne'
    hzA hzB hexA
  refine ⟨![A, B], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact M.cls_sub hA
    · exact M.cls_sub hB
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hAB
    · exact absurd hij.symm hAB
    · rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm
    · exact hcomm.symm
    · exact absurd rfl hij
  · intro i j S hS
    have hS' := M.fund_subset_cls hne hG2 hD4 hS
    fin_cases i <;> fin_cases j
    · exact Iff.rfl
    · constructor
      · rintro (rfl | h)
        · exact Or.inr hcomm
        · exact M.twin_stable_sect hΩ hp2 hq hnpsl hG2 hD4 hA hB hAB hzA hzB hS' h
      · rintro (rfl | h)
        · exact Or.inr hcomm.symm
        · exact M.twin_stable_sect hΩ hp2 hq hnpsl hG2 hD4 hB hA hAB.symm hzB hzA hS' h
    · constructor
      · rintro (rfl | h)
        · exact Or.inr hcomm.symm
        · exact M.twin_stable_sect hΩ hp2 hq hnpsl hG2 hD4 hB hA hAB.symm hzB hzA hS' h
      · rintro (rfl | h)
        · exact Or.inr hcomm
        · exact M.twin_stable_sect hΩ hp2 hq hnpsl hG2 hD4 hA hB hAB hzA hzB hS' h
    · exact Iff.rfl

theorem Ih8Model.not_omegaNbr_of_noCommute_sect (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hnc : ∀ R ∈ M.cls, ∀ S ∈ M.cls, R ≠ S → ¬ Commutes R S) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : False := by
  obtain ⟨A, hA2, hAJ, hAN, hAnc⟩ := ih8_nbr_sylow hp2 hΩ hJ
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJ.1
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eS⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hS
  have hodd := M.natCard_galoisField_odd hp2
  have hpR := M.cls_perfect hp2 hD4 hq hR
  have hpS := M.cls_perfect hp2 hD4 hq hS
  have hRS : R ≠ S := fun h => hJ.2.1 (by rw [h])
  obtain ⟨-, -, -, -, -, -, hzcomm⟩ := ih8_nbr_model M.ψ M.ker_le_center hodd hodd hpR eR eS hA2
    hAJ hAnc hAN
  have hdich := ih8_stdDichotomy M.isFundTag hG2 hD4 M.admissible
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  rcases hdich.map_of_commute hp2 hq' M.ψ M.ker_le_center hRl hSl (sl2Inv_mem eR)
    (sl2Inv_mem eS) (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm
    with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact hRS (ih8_eq_of_map_eq M.ψ M.ker_le_center hpR hpS h)
  · exact hnc R hR S hS hRS (ih8_commutes_of_commutes_map M.ψ M.ker_le_center hpR h)
  · obtain ⟨x, hx, y, hy, hxy⟩ := hAnc
    exact hxy (LinearBlockStandardPair.comm_of_normalizes
      (M.four_le_natCard_galoisField hD4 hq) hW (hAJ hx) (hAJ hy) (hAN hx) (hAN hy))
  · obtain ⟨x, hx, y, hy, hxy⟩ := hAnc
    have hf : 1 ≤ e := M.admissible.2.1
    exact hxy (UnitaryBlockStandardPair.comm_of_normalizes
      (CFSG.LieType.Universal.card_galoisField_two_mul p e hf) hq' hW (hAJ hx) (hAJ hy)
      (hAN hx) (hAN hy))

theorem Ih8Model.not_omegaNbr_of_three_sect (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h3 : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : False := by
  have hG2 : t ≠ .G2 := by rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  refine M.not_omegaNbr_of_noCommute_sect hΩ hp2 hq hG2 hD4 ?_ hK hJ
  intro R hR S hS hRS hc
  rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have := four_le_of_commutes_psl hp2 (le_refl 3) (M.cls_sub hR) (M.cls_sub hS) hRS hc
    omega
  · have := four_le_of_commutes_psu hp2 M.admissible (M.cls_sub hR) (M.cls_sub hS) hRS hc
    omega

end Model

end CFSG.ClassicalInvolution.Asc77
