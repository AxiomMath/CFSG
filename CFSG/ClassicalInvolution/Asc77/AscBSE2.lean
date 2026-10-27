module

public import CFSG.ClassicalInvolution.Asc77.AscBSE1
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section
import CFSG.ClassicalInvolution.RouteD.NoG2D4Count

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.BSC.BSD
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem card_center_member_dvd_two {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : HypOmega p f Φ) {L : Subgroup X} (hL : L ∈ Φ) : Nat.card (Subgroup.center L) ∣ 2 := by
  obtain ⟨w, hw⟩ := hΦ.classical L hL
  obtain ⟨e⟩ := hw.nonempty_equiv_sl2 (hΦ.exact L hL)
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact RouteD.G2D4.card_center_sl2_dvd_two

theorem false_of_g2_of_card {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hG2 : C.D.tag b = .G2) (hcard : 3 < C.D.card) : False := by
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  obtain ⟨N, m, hinj, hN⟩ := exists_conj_twins hno hb
  obtain ⟨j₀, hj₀, -⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨c, d, hcd, hcj, hcb, hdj, hdb⟩ := exists_two_ne_of_three_lt hcard j₀ b hj₀b
  let i₀ : {j : Fin C.D.card // j ≠ b} := ⟨j₀, hj₀b⟩
  let i₁ : {j : Fin C.D.card // j ≠ b} := ⟨c, hcb⟩
  let i₂ : {j : Fin C.D.card // j ≠ b} := ⟨d, hdb⟩
  have h01 : N i₀ ≠ N i₁ := fun h => hcj (congrArg Subtype.val (hinj h)).symm
  have h02 : N i₀ ≠ N i₂ := fun h => hdj (congrArg Subtype.val (hinj h)).symm
  have h12 : N i₁ ≠ N i₂ := fun h => hcd (congrArg Subtype.val (hinj h))
  obtain ⟨h0tq, h0cl, R₀, hR₀, himg₀, -⟩ := hN i₀
  obtain ⟨h1tq, h1cl, R₁, hR₁, himg₁, -⟩ := hN i₁
  obtain ⟨h2tq, h2cl, R₂, hR₂, himg₂, -⟩ := hN i₂
  have hΦ : HypOmega p f (secFam (𝒞 K) z) := hypOmega_secFam C.hp C.hq C.hΩ C.hc2 C.hs C.D
  have hmem : ∀ M ∈ tqMembers (𝒞 K) z,
      exactCore z M ∈ centMembers (exactFamily (𝒞 K) z) z := fun M hM =>
    ⟨exactCore_mem_exactFamily hM, exactCore_le_centralizer z M⟩
  have e₀ := map_hom_eq_modOddIn C.hs C.D b (hmem _ h0tq) himg₀.symm
  have e₁ := map_hom_eq_modOddIn C.hs C.D b (hmem _ h1tq) himg₁.symm
  have e₂ := map_hom_eq_modOddIn C.hs C.D b (hmem _ h2tq) himg₂.symm
  obtain ⟨hbY, hK₀, hK₁, hne₀₁, hz₀, hz₁⟩ :=
    secFam_twin C.hp C.hq C.hΩ C.hc2 h0tq h1tq h0cl h1cl h01.symm
  obtain ⟨hbY', -, hK₂, hne₀₂, -, hz₂⟩ :=
    secFam_twin C.hp C.hq C.hΩ C.hc2 h0tq h2tq h0cl h2cl h02.symm
  obtain ⟨hbY'', -, -, hne₁₂, hz₁', hz₂'⟩ :=
    secFam_twin C.hp C.hq C.hΩ C.hc2 h1tq h2tq h1cl h2cl h12.symm
  exact RouteD.G2D4.false_of_three_commuting_sl2 C.hp (Or.inl hG2) (C.D.admissible b)
    (C.D.exp_eq b) (C.D.hom b) (A₁ := modOddIn (centralizingLayer (exactFamily (𝒞 K) z) {z})
      (exactCore z (N i₀))) (A₂ := modOddIn (centralizingLayer (exactFamily (𝒞 K) z) {z})
      (exactCore z (N i₁))) (A₃ := modOddIn (centralizingLayer (exactFamily (𝒞 K) z) {z})
      (exactCore z (N i₂)))
    (e₀ ▸ Subgroup.map_le_range _ _) (e₁ ▸ Subgroup.map_le_range _ _)
    (e₂ ▸ Subgroup.map_le_range _ _)
    (hΦ.commutes_of_twin hK₀ hK₁ hne₀₁ hz₀ hz₁) (hΦ.commutes_of_twin hK₀ hK₂ hne₀₂ hz₀ hz₂)
    (hΦ.commutes_of_twin hK₁ hK₂ hne₁₂ hz₁' hz₂')
    (natCard_member hΦ hK₀) (natCard_member hΦ hK₁) (natCard_member hΦ hK₂)
    (card_center_member_dvd_two hΦ hK₀) (card_center_member_dvd_two hΦ hK₁)

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
