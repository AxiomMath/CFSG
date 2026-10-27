module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

structure PinnedFacts (s : TauCeti.SporadicName) (P : ℕ → Prop) (N cardS : ℕ) : Prop where
  finite : Finite (Carrier s)
  simple : IsSimpleGroup (Carrier s)
  nonabelian : ∃ a b : Carrier s, a * b ≠ b * a
  card : Nat.card (Carrier s) = cardS
  even_card : Even cardS
  rank : ∀ (X : Type) [Group X] [Finite X], IsSporadic X s → 3 ≤ CFSG.pRank 2 X
  outTwo : OutTwo (Carrier s)
  pair : ∀ (u : Carrier s) (K : Subgroup (Carrier s)), PairShape P (Carrier s) ⊤ K u →
    Nat.card (center ↥K) = 2 ∧ Nat.card ↥K = 2 * N
  two_le : 2 ≤ N
  even_N : Even N
  lt : 2 * N < cardS
  cube : ∃ c : ℕ, c * (c ^ 2 - 1) < 2 * N ∧ 2 * N < (c + 1) * ((c + 1) ^ 2 - 1)
  ne_a7 : N ≠ 2520

variable {s : TauCeti.SporadicName} {P : ℕ → Prop} {N cardS m n : ℕ}

theorem PinnedFacts.oddCover_top (hF : PinnedFacts s P N cardS) :
    OddCover s (⊤ : Subgroup (Carrier s)) := by
  have := hF.finite
  have := hF.simple
  have hZ : center (Carrier s) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Carrier s)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hF.nonabelian
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  refine ⟨(fStarSimple_top (Carrier s) hF.nonabelian).isQuasisimple, ?_, ?_⟩
  · rw [card_center_of_mulEquiv' (Subgroup.topEquiv (G := Carrier s)), hZ, Subgroup.card_bot]
    exact odd_one
  · exact ⟨(quotientCenterEquiv' (Subgroup.topEquiv (G := Carrier s))).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem PinnedFacts.card_quotient (hF : PinnedFacts s P N cardS) {u : Carrier s}
    {K : Subgroup (Carrier s)} (h : PairShape P (Carrier s) ⊤ K u) :
    Nat.card (↥K ⧸ center ↥K) = N := by
  have hK := hF.pair u K h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K)
  rw [hK.1, hK.2] at h1
  omega

theorem PinnedFacts.hyp31Row (hF : PinnedFacts s P N cardS) (hmult : OddMultTrivial s)
    (hd : Lemma36DataQ s (PairShape P) m n) (hn : 8 ≤ n) :
    Hyp31Row (IsKPinned s P) (IsLS [s]) where
  isK_inv := isKPinned_isoInv s P
  isL_inv := fun _ _ _ _ e h => isLS_of_mulEquiv e h
  quasi_K := by
    intro X _ ⟨u, K, hQ', ⟨e⟩⟩
    have := hF.finite
    obtain ⟨-, -, -, -, hKq, -, -, hfix⟩ := hd.data (Carrier s) ⊤ K u hF.oddCover_top hQ'
    have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq,
      three_le_pRank_of_fixesElem_iso e hn hfix ?_⟩
    rw [hF.card_quotient hQ']
    exact hF.even_N
  quasi_L := by
    intro X _ hX
    obtain ⟨s', hs', hq, hodd, hsp⟩ := hX
    rcases List.mem_singleton.1 hs' with rfl
    obtain ⟨f⟩ := hsp
    have := hF.finite
    have : Finite (center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
    have : Finite (X ⧸ center X) := Finite.of_equiv _ f.symm.toEquiv
    have : Finite X := Finite.of_subgroup_quotient (center X)
    have hc : center X = ⊥ := hmult X hq hodd ⟨f⟩
    obtain ⟨e⟩ := isSporadic_of_center_eq_bot hc ⟨f⟩
    have := hF.simple
    have hev : Even (Nat.card (Carrier s')) := by rw [hF.card]; exact hF.even_card
    have hbot : CFSG.oddCore X = ⊥ :=
      oddCore_eq_bot_of_mulEquiv e.symm (oddCore_eq_bot_of_isSimpleGroup hev)
    exact ⟨hq, by rw [hc, hbot], hF.rank X ⟨e⟩⟩
  K_not_exc := by
    intro X _ ⟨u, K, hQ', ⟨e⟩⟩
    obtain ⟨c, h1, h2⟩ := hF.cube
    refine kNotExc_of_card (N := N) (c := c) ?_ h1 h2 hF.ne_a7
    rw [Nat.card_congr (quotientCenterEquiv' e).toEquiv]
    exact hF.card_quotient hQ'
  K_ne_L := by
    intro X Y _ _ hX hY
    obtain ⟨s', hs', hq, hodd, hsp⟩ := hX
    rcases List.mem_singleton.1 hs' with rfl
    obtain ⟨f⟩ := hsp
    obtain ⟨u, K, hQ', ⟨g⟩⟩ := hY
    have := hF.finite
    have : Finite (X ⧸ center X) := Finite.of_equiv _ f.symm.toEquiv
    have : IsSimpleGroup (X ⧸ center X) := hq.2.1
    have : Finite (Y ⧸ CFSG.oddCore Y) := Finite.of_equiv _ g.symm.toEquiv
    refine kNeL_of_card (cardS := cardS) (cardK := 2 * N) ?_ hF.even_card ?_ hF.lt
    · rw [Nat.card_congr f.toEquiv]; exact hF.card
    · rw [Nat.card_congr g.toEquiv]; exact (hF.pair u K hQ').2

noncomputable def stage3Row_of_pinned {Q : PairClass} (hQ : Q = PairShape P)
    (hF : PinnedFacts s P N cardS) (hmult : OddMultTrivial s) (hd : Lemma36DataQ s Q m n)
    (hn : 8 ≤ n)
    (hex : ∃ (u : Carrier s) (K : Subgroup (Carrier s)), PairShape P (Carrier s) ⊤ K u)
    (hfit : ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G), IsSporadic ↥L s → K ≤ L →
      CFSG.IsQuasisimple ↥K → CFSG.oddCore ↥K ≤ center ↥K →
        IsKPinned s P (↥K ⧸ CFSG.oddCore ↥K) → P (Nat.card ↥K)) :
    Stage3Row [s] (fun _ => Q) := by
  subst hQ
  exact
    { IsK := IsKPinned s P
      m := fun _ => m
      rec36 := fun s' hs' => by
        rcases List.mem_singleton.1 hs' with rfl
        exact Rec36.old n hd
      outTwo := fun s' hs' H _ M hM => by
        rcases List.mem_singleton.1 hs' with rfl
        obtain ⟨e⟩ := oddCover_isSporadic hF.finite hmult hM
        exact OutTwo.of_mulEquiv e.symm hF.outTwo
      hyp31Row := hF.hyp31Row hmult hd hn
      rowIsK := fun s' hs' H _ L K u hcov hQ => by
        rcases List.mem_singleton.1 hs' with rfl
        obtain ⟨e⟩ := oddCover_isSporadic hF.finite hmult hcov
        exact isKPinned_of_pair e hQ
      rowExists := fun s' hs' H _ _ L hcov => by
        rcases List.mem_singleton.1 hs' with rfl
        obtain ⟨e⟩ := oddCover_isSporadic hF.finite hmult hcov
        exact exists_pair_of_pinned e hex
      rowFit := by
        intro s' hs' H _ _ L K hcov hKL hKq hK _ _
        rcases List.mem_singleton.1 hs' with rfl
        have hK0 := hK
        obtain ⟨u', K', hQ', ⟨f⟩⟩ := hK
        have hK' := hF.pair u' K' hQ'
        have hZ2 : Nat.card (center (↥K ⧸ CFSG.oddCore ↥K)) = 2 := by
          rw [card_center_of_mulEquiv' f]; exact hK'.1
        have hnc : ¬ IsMulCommutative (↥K ⧸ CFSG.oddCore ↥K) := by
          intro hcomm
          have hall : center (↥K ⧸ CFSG.oddCore ↥K) = ⊤ := by
            refine eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun g => ?_
            exact hcomm.is_comm.comm g x
          have h1 : Nat.card (center (↥K ⧸ CFSG.oddCore ↥K)) =
              Nat.card (↥K ⧸ CFSG.oddCore ↥K) := by
            rw [hall, Subgroup.card_top]
          rw [hZ2, Nat.card_congr f.toEquiv, hK'.2] at h1
          have := hF.two_le
          omega
        have hO : CFSG.oddCore ↥K ≤ center ↥K := oddCore_le_center_of_quasisimple hKq hnc
        have : Group.IsPerfect ↥K := hKq.1
        obtain ⟨u, huc, hu2⟩ := exists_central_involution hO hZ2
        refine ⟨(u : H), hKL u.2, ?_, hKL, ?_,
          hfit H L K (oddCover_isSporadic hF.finite hmult hcov) hKL hKq hO hK0⟩
        · rw [Subgroup.orderOf_coe]; exact hu2
        · intro k hk
          exact congrArg Subtype.val (Subgroup.mem_center_iff.1 huc ⟨k, hk⟩)
      inOrTwoSylow := Or.inl fun s' hs' H _ L K u hcov hQ => by
        rcases List.mem_singleton.1 hs' with rfl
        have := oddCover_finite hF.finite hcov
        obtain ⟨-, huK, -⟩ := hd.data ↥L ⊤ (K.subgroupOf L) ⟨u, hQ.1⟩
          (oddCover_top_of_cover hcov) (pairShape_restrict hQ)
        exact huK }

end CFSG.EvenSporadicStandard.Induction
