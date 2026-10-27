module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectB
public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab
public import CFSG.ClassicalInvolution.Asc77.WP3Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected

variable (p : ℕ) [Fact p.Prime]

@[expose] def TwinSquareFact : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k p e → p ≠ 2 → 5 ≤ p ^ e →
    ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) →
    ∀ R ∈ ModelFund p t k e, ∀ R' ∈ ModelFund p t k e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center (modelUniv t k p e Fact.out).K →
        (∃ c ∈ Subgroup.center (modelUniv t k p e Fact.out).K, c * c = x * x') →
        (t = .PSL ∧ k = 4 ∧ p ^ e % 4 = 1) ∨ (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 3)

variable {p}

structure TwinFrame {X : Type} [Group X] (Φ : Set (Subgroup X)) (A A' B : Subgroup X)
    (z u₁ u₂ t e : X) : Prop where
  hA : A ∈ Φ
  hA' : A' ∈ Φ
  hB : B ∈ Φ
  hne : A ≠ A'
  hzA : IsUniqueInvolution A z
  hzA' : IsUniqueInvolution A' z
  h₁ : u₁ ∈ A
  h₂ : u₂ ∈ A'
  o₁ : u₁ * u₁ = z
  o₂ : u₂ * u₂ = z
  htB : IsUniqueInvolution B t
  he : e ∈ Subgroup.center X
  he2 : e * e = 1
  he1 : e ≠ 1
  hrel : t = u₁ * u₂ * e

theorem twinFrame_tag_of_model (hTSF : TwinSquareFact p) {f : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ)
    {tg : StatedLieTag} {k ee : ℕ} (M : Ih8Model p f Φ tg k ee) (hdisc : ¬ DConnected Φ)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (h : TwinFrame Φ A A' B z u₁ u₂ τ ε) :
    (tg = .PSL ∧ k = 4 ∧ p ^ f % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ p ^ f % 4 = 3) := by
  classical
  obtain ⟨hA, hA', hB, hne, hzA, hzA', h₁, h₂, o₁, o₂, htB, he, he2, he1, hrel⟩ := h
  by_cases hG2d4 : tg = .G2 ∨ tg = .trialityD4
  · exfalso
    have hsimple : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
    · apply he1
      have := hc ▸ he
      simpa using this
    · obtain ⟨zz, hzz⟩ := hΦ.classical A hA
      obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hzz
      have hy' : y ∈ Subgroup.center X := hc ▸ Subgroup.mem_top y
      exact hxy (Subgroup.mem_center_iff.mp hy' x)
  push Not at hG2d4
  obtain ⟨hG2, hD4⟩ := hG2d4
  have hee : ee = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ ee := by rw [hee]; exact hq
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4 with hconn | hsmall
  · exact absurd (M.dConnected_of_connected hp2 hq ⟨A, hA⟩ hG2 hD4 hconn) hdisc
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RA', hRA', rfl⟩ := (M.mem_iff A').mp hA'
  obtain ⟨RB, hRB, rfl⟩ := (M.mem_iff B).mp hB
  have hpA := M.cls_perfect hp2 hD4 hq hRA
  have hpA' := M.cls_perfect hp2 hD4 hq hRA'
  have hpB := M.cls_perfect hp2 hD4 hq hRB
  have hRR : RA ≠ RA' := fun h => hne (by rw [h])
  have hexA := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hRA
  obtain ⟨hcommR, -⟩ := ih8_twin_data hΦ M.ker_le_center hpA (M.map_mem hRA)
    (M.map_mem hRA') hne hzA hzA' hexA
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    have hfin := M.finite_K hp2
    have htopR : ∀ R ∈ M.cls, R = ⊤ := by
      intro R hR
      obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 (by decide) (by decide) hR
      have hcard : Nat.card ↥R = Nat.card (modelUniv .PSL 2 p ee Fact.out).K := by
        rw [Nat.card_congr eR.toEquiv]
        exact Nat.card_congr (Equiv.refl _)
      exact Subgroup.eq_top_of_card_eq R hcard
    exact hne (by rw [htopR RA hRA, htopR RA' hRA'])
  have hmain : ((tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4) ∨ (tg = .PSU ∧ k = 4) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4)) →
      (tg = .PSL ∧ k = 4 ∧ p ^ f % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ p ^ f % 4 = 3) := by
    intro hsix
    obtain ⟨eA⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hRA
    obtain ⟨eA'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hRA'
    obtain ⟨eB⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hRB
    have hodd := M.natCard_galoisField_odd hp2
    have hinjA := M.injOn_fund hnpsl (M.cls_sub hRA)
    have hinjA' := M.injOn_fund hnpsl (M.cls_sub hRA')
    have hinjB := M.injOn_fund hnpsl (M.cls_sub hRB)
    have hxR : sl2Inv eA ∈ RA := sl2Inv_mem eA
    have hx'R : sl2Inv eA' ∈ RA' := sl2Inv_mem eA'
    have hx2 : sl2Inv eA * sl2Inv eA = 1 := sl2Inv_mul_self hodd eA
    have hx'2 : sl2Inv eA' * sl2Inv eA' = 1 := sl2Inv_mul_self hodd eA'
    have hx1 : sl2Inv eA ≠ 1 := sl2Inv_ne_one hodd eA
    have hx'1 : sl2Inv eA' ≠ 1 := sl2Inv_ne_one hodd eA'
    have hψx : M.ψ (sl2Inv eA) = z := by
      have hmem : M.ψ (sl2Inv eA) ∈ RA.map M.ψ := Subgroup.mem_map_of_mem _ hxR
      have hsq : M.ψ (sl2Inv eA) * M.ψ (sl2Inv eA) = 1 := by rw [← map_mul, hx2, map_one]
      rcases hzA.unique _ hmem hsq with h | h
      · exact absurd (hinjA _ hxR h) hx1
      · exact h
    have hψx' : M.ψ (sl2Inv eA') = z := by
      have hmem : M.ψ (sl2Inv eA') ∈ RA'.map M.ψ := Subgroup.mem_map_of_mem _ hx'R
      have hsq : M.ψ (sl2Inv eA') * M.ψ (sl2Inv eA') = 1 := by rw [← map_mul, hx'2, map_one]
      rcases hzA'.unique _ hmem hsq with h | h
      · exact absurd (hinjA' _ hx'R h) hx'1
      · exact h
    obtain ⟨a₁, ha₁, hψa₁⟩ := Subgroup.mem_map.mp h₁
    obtain ⟨a₂, ha₂, hψa₂⟩ := Subgroup.mem_map.mp h₂
    obtain ⟨b, hb, hψb⟩ := Subgroup.mem_map.mp htB.mem
    obtain ⟨c₀, hψc₀⟩ := M.surj ε
    have ha₁sq : a₁ * a₁ = sl2Inv eA := by
      have : a₁ * a₁ * (sl2Inv eA)⁻¹ = 1 := by
        apply hinjA _ (RA.mul_mem (RA.mul_mem ha₁ ha₁) (RA.inv_mem hxR))
        rw [map_mul, map_mul, map_inv, hψa₁, hψx, o₁, mul_inv_cancel]
      exact mul_inv_eq_one.mp this
    have ha₂sq : a₂ * a₂ = sl2Inv eA' := by
      have : a₂ * a₂ * (sl2Inv eA')⁻¹ = 1 := by
        apply hinjA' _ (RA'.mul_mem (RA'.mul_mem ha₂ ha₂) (RA'.inv_mem hx'R))
        rw [map_mul, map_mul, map_inv, hψa₂, hψx', o₂, mul_inv_cancel]
      exact mul_inv_eq_one.mp this
    have hbsq : b * b = 1 := by
      apply hinjB _ (RB.mul_mem hb hb)
      rw [map_mul, hψb, htB.sq]
    have hQS := ModelFacts.modelClauseZero tg k p ee Fact.out M.isFundTag M.admissible
    have hNnorm : (Subgroup.zpowers ε).Normal := ⟨fun n hn g => by
      obtain ⟨m, rfl⟩ := hn
      have hc : Commute g ε := Subgroup.mem_center_iff.mp he g
      have := (hc.zpow_right m).eq
      rw [this, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers ε) m⟩
    have hc₀ : c₀ ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K :=
      comap_le_center_of_normal_pGroup hQS.1 M.ψ M.ker_le_center
        (ExactLayer.isPGroup_zpowers_of_sq_eq_one he2)
        (show M.ψ c₀ ∈ Subgroup.zpowers ε from hψc₀ ▸ Subgroup.mem_zpowers ε)
    obtain ⟨κ, hκc, hκeq⟩ : ∃ κ ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K,
        a₁ * a₂ * c₀ = b * κ := by
      refine ⟨b⁻¹ * (a₁ * a₂ * c₀), M.ker_le_center ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψb, map_mul, map_mul, hψa₁, hψa₂, hψc₀, ← hrel,
        inv_mul_cancel]
    have hc12 : a₁ * a₂ = a₂ * a₁ := hcommR a₁ ha₁ a₂ ha₂
    have hcc : ∀ y, y * c₀ = c₀ * y := Subgroup.mem_center_iff.mp hc₀
    have hκκ : ∀ y, y * κ = κ * y := Subgroup.mem_center_iff.mp hκc
    have e1 : a₁ * a₂ * (a₁ * a₂) = (a₁ * a₁) * (a₂ * a₂) := by
      calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
        _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hc12]
        _ = (a₁ * a₁) * (a₂ * a₂) := by group
    have e2 : (a₁ * a₂ * c₀) * (a₁ * a₂ * c₀) = (a₁ * a₁) * (a₂ * a₂) * (c₀ * c₀) := by
      calc (a₁ * a₂ * c₀) * (a₁ * a₂ * c₀) = a₁ * a₂ * (c₀ * (a₁ * a₂)) * c₀ := by group
        _ = a₁ * a₂ * ((a₁ * a₂) * c₀) * c₀ := by rw [← hcc (a₁ * a₂)]
        _ = (a₁ * a₂ * (a₁ * a₂)) * (c₀ * c₀) := by group
        _ = (a₁ * a₁) * (a₂ * a₂) * (c₀ * c₀) := by rw [e1]
    have e3 : (b * κ) * (b * κ) = κ * κ := by
      calc (b * κ) * (b * κ) = b * (κ * b) * κ := by group
        _ = b * (b * κ) * κ := by rw [← hκκ b]
        _ = (b * b) * (κ * κ) := by group
        _ = κ * κ := by rw [hbsq, one_mul]
    have e4 : sl2Inv eA * sl2Inv eA' * (c₀ * c₀) = κ * κ := by
      rw [← ha₁sq, ← ha₂sq, ← e2, hκeq, e3]
    have hc₀inv : c₀⁻¹ ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K :=
      Subgroup.inv_mem _ hc₀
    have hswap : κ * c₀⁻¹ = c₀⁻¹ * κ := Subgroup.mem_center_iff.mp hc₀inv κ
    have hζ : κ * c₀⁻¹ ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K :=
      Subgroup.mul_mem _ hκc hc₀inv
    have e5 : (κ * c₀⁻¹) * (κ * c₀⁻¹) = sl2Inv eA * sl2Inv eA' := by
      calc (κ * c₀⁻¹) * (κ * c₀⁻¹) = κ * (c₀⁻¹ * κ) * c₀⁻¹ := by group
        _ = κ * (κ * c₀⁻¹) * c₀⁻¹ := by rw [← hswap]
        _ = (κ * κ) * (c₀⁻¹ * c₀⁻¹) := by group
        _ = (sl2Inv eA * sl2Inv eA' * (c₀ * c₀)) * (c₀⁻¹ * c₀⁻¹) := by rw [e4]
        _ = sl2Inv eA * sl2Inv eA' := by group
    have hxx' : sl2Inv eA * sl2Inv eA' ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K := by
      rw [← e5]; exact Subgroup.mul_mem _ hζ hζ
    have := hTSF tg k ee M.admissible hp2 hq' hsix RA (M.cls_sub hRA) RA' (M.cls_sub hRA') hRR
      hcommR _ hxR _ hx'R hx2 hx1 hx'2 hx'1 hxx' ⟨_, hζ, e5⟩
    rw [hee] at this
    exact this
  rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk2 : 2 ≤ k := M.admissible.2.2.1
    have hk' : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk' with rfl | rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hnpsl
    · exfalso
      have := four_le_of_commutes_psl hp2 (le_refl 3) (M.cls_sub hRA) (M.cls_sub hRA') hRR hcommR
      omega
    · exact hmain (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · have hk3 : 3 ≤ k := M.admissible.2.2.1
    have hk' : k = 3 ∨ k = 4 := by omega
    rcases hk' with rfl | rfl
    · exfalso
      have := four_le_of_commutes_psu hp2 M.admissible (M.cls_sub hRA) (M.cls_sub hRA') hRR hcommR
      omega
    · exact hmain (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact hmain (Or.inl ⟨rfl, rfl⟩)
  · exact hmain (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact hmain (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact hmain (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))


section Comp

variable {f : ℕ} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem OmegaLie.exists_comp_all (D : OmegaLie p f Φ)
    {A A' B : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hB : B ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hBA : B ≠ A) (hBA' : B ≠ A') (hBn : B ∉ omegaNbr Φ A) (hBn' : B ∉ omegaNbr Φ A') :
    ∃ i₀, ∀ L ∈ Φ, L ≤ D.comp i₀ := by
  obtain ⟨i₀, hAi₀⟩ := D.exists_comp_of_mem hA
  have hBi : B ≤ D.comp i₀ := by
    obtain ⟨j, hBj⟩ := D.exists_comp_of_mem hB
    by_cases hj : j = i₀
    · subst hj; exact hBj
    · exfalso; apply hBn
      refine MuTab.mem_omegaNbr_of_commutes hB hBA ?_
      intro a ha b hb
      exact D.comp_commute (Ne.symm hj) a (hAi₀ ha) b (hBj hb)
  have hA'i : A' ≤ D.comp i₀ := by
    obtain ⟨j, hA'j⟩ := D.exists_comp_of_mem hA'
    by_cases hj : j = i₀
    · subst hj; exact hA'j
    · exfalso; apply hBn'
      refine MuTab.mem_omegaNbr_of_commutes hB hBA' ?_
      intro a ha b hb
      exact D.comp_commute hj a (hA'j ha) b (hBi hb)
  refine ⟨i₀, fun L hL => ?_⟩
  obtain ⟨j, hLj⟩ := D.exists_comp_of_mem hL
  by_cases hj : j = i₀
  · subst hj; exact hLj
  · by_cases hLA : L = A
    · exact hLA ▸ hAi₀
    · have hLn : L ∈ omegaNbr Φ A :=
        MuTab.mem_omegaNbr_of_commutes hL hLA (fun a ha b hb =>
          D.comp_commute (Ne.symm hj) a (hAi₀ ha) b (hLj hb))
      exact (hnb L hL hLn) ▸ hA'i

theorem OmegaLie.card_eq_one_of_all_le (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    {i₀ : Fin D.card} (hall : ∀ L ∈ Φ, L ≤ D.comp i₀) : D.card = 1 := by
  have hsub : ∀ j : Fin D.card, j = i₀ := by
    intro j
    by_contra hji
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    obtain ⟨z, hz⟩ := hΦ.classical _ hRΦ
    obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
    have hxj : x ∈ D.comp j := Subgroup.map_le_range _ _ hx
    exact hxy (D.comp_commute hji x hxj y (hall _ hRΦ hy))
  have hle : D.card ≤ 1 :=
    Fin.subsingleton_iff_le_one.mp ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have hpos : 0 < D.card := i₀.pos
  omega

end Comp

section Wrapper

variable {f : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinFrame_tag (hTSF : TwinSquareFact p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) (hcard : D.card = 1) (hgen : omegaGen Φ = ⊤)
    (hdisc : ¬ DConnected Φ) {A A' B : Subgroup X} {z u₁ u₂ t e : X}
    (h : TwinFrame Φ A A' B z u₁ u₂ t e) (i : Fin D.card) :
    (D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ f % 4 = 1) ∨
      (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ f % 4 = 3) :=
  twinFrame_tag_of_model hTSF hp2 hq hΦ
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := D.hom_surjective_of_gen hcard hgen i
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => D.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g } hdisc h

end Wrapper

end CFSG.ClassicalInvolution.Asc77
