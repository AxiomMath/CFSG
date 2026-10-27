module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCover

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

theorem exists_mulEquiv_orthElementary_rank_of_twistedD (hZ : OddCenterRest) {Y : Type}
    [Group Y] [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (dI : TauCeti.ValidLieTypeIndex)
    (hdI : IdxTwistedD dI.1) (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie dI).Group) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
      3 ≤ r ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        (∀ n q, dI.1 = .twistedD n q → Nat.card K = q.card ∧ n = r + 1) ∧
        Subgroup.center ↥L = ⊥ ∧
        Nonempty (↥L ≃* ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) := by
  obtain ⟨dI, hv⟩ := dI
  cases dI
  case twistedD n q =>
    have hq2 : q.p = 2 := hdI
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv
      hq2 e
    rw [hq2] at hmodel
    obtain ⟨⟨-, hf, hn⟩, K, hKf, hKfin, hK, b, c, hirr, ⟨e'⟩⟩ := hmodel
    have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rcases hZ Y L hL hodd (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hdI, ⟨e⟩⟩))) with h1 | ⟨-, ⟨e6⟩⟩
      · exact h1
      · exfalso
        have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) =
            CFSG.Open.ordTwistedD n (2 ^ q.exponent) :=
          (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .POmegaMinus) (n := n)
            ⟨⟨Nat.prime_two, hf, hn⟩, K, hKf, hKfin, hK, b, c, hirr, ⟨e'⟩⟩).2.2.2.2 rfl
        have h360 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 := by
          rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
          simp [Nat.factorial]
        have := orthMinus_sixteen_dvd hn hf
        rw [← hcard, h360] at this
        norm_num at this
    have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    refine ⟨n - 1, K, hKf, hKfin, inferInstance, b, c, by omega, hirr, fun n₁ q₁ h₁ => ?_, hbot,
      ?_⟩
    · injection h₁ with h₂ h₃
      exact ⟨by rw [← h₃, hK, TauCeti.PrimePower.card_def, hq2], by omega⟩
    exact ⟨((((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      hbot.symm)).trans e').trans (orthMinusStatedProjEquiv (by omega))).trans
        (tailOmegaEquiv (minusTailIsometry n K b c) (coe_quadMinus n K b c)
          (commutator_orthogonalGroup_quadMinus hn hirr)))⟩
  all_goals exact hdI.elim

theorem exists_orthCover_rank_of_twistedD (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) (dI : TauCeti.ValidLieTypeIndex)
    (hdI : IdxTwistedD dI.1) (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie dI).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K) (r s : ℕ)
      (d : Fin (s + 1) → ℕ) (ρ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥L),
      3 ≤ r ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ OrthCuts r d ∧
        (P.subgroupOf L).comap ρ.toMonoidHom = orthParab r (minusTailForm K b c) d ∧
        (∀ n q, dI.1 = .twistedD n q → Nat.card K = q.card ∧ n = r + 1) ∧
        Subgroup.center ↥L = ⊥ := by
  obtain ⟨r, K, hKf, hKfin, hK2, b, c, hr, hirr, hq, hZ1, ⟨φ⟩⟩ :=
    exists_mulEquiv_orthElementary_rank_of_twistedD hZ hCP.comp hCP.odd dI hdI e
  obtain ⟨ρ, s, d, hcuts, hρ⟩ := exists_comap_eq_orthParab hr hirr hCP.parab φ.symm
  exact ⟨K, hKf, hKfin, hK2, b, c, r, s, d, ρ, hr, hirr, hcuts, hρ, hq, hZ1⟩

theorem card_comap_subgroupOf_of_mulEquiv {Y : Type} [Group Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {E : Type} [Group E] (ρ : E ≃* ↥L) :
    Nat.card ↥((P.subgroupOf L).comap ρ.toMonoidHom) = Nat.card ↥P := by
  rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective ρ.symm.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv]

end CFSG.AGLEmbedding.LeviBlock
