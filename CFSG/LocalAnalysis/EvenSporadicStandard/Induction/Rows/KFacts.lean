module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCoreFree

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

theorem IsOddCentralExt.card_quotient {D X : Type} [Group D] [Group X] (h : IsOddCentralExt D X) :
    Nat.card (X ⧸ center X) = Nat.card (D ⧸ center D) := by
  obtain ⟨hq, π, hπs, hπc, -⟩ := h
  obtain ⟨e⟩ := quotientCenterEquiv_of_centralCover π hπs hπc hq.1
  exact Nat.card_congr e.toEquiv

theorem kNotExc_of_oddCentralExt {D : Type} [Group D] {N c : ℕ}
    (hD : Nat.card (D ⧸ center D) = N) (h1 : c * (c ^ 2 - 1) < 2 * N)
    (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1)) (hA7 : N ≠ 2520) (X : Type) [Group X]
    (hX : IsOddCentralExt D X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  kNotExc_of_card (hX.card_quotient.trans hD) h1 h2 hA7

theorem kNeL_of_oddCentralExt {D : Type} [Group D] {s : TauCeti.SporadicName} {cardS : ℕ}
    (hfin : Finite (Carrier s)) (hsimple : IsSimpleGroup (Carrier s))
    (hnc : ∃ a b : Carrier s, a * b ≠ b * a) (hcard : Nat.card (Carrier s) = cardS)
    (hev : Even cardS) (hlt : Nat.card (D ⧸ center D) < cardS) {X Y : Type} [Group X] [Group Y]
    (hX : IsLS [s] X) (hY : IsOddCentralExt D (Y ⧸ CFSG.oddCore Y)) :
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) := by
  rintro ⟨e⟩
  obtain ⟨s', hs', -, -, ⟨f⟩⟩ := hX
  rcases List.mem_singleton.1 hs' with rfl
  have := hfin
  have := hsimple
  have g : (Y ⧸ center Y) ≃* Carrier s' := e.symm.trans f
  have hfinY : Finite (Y ⧸ center Y) := Finite.of_equiv _ g.symm.toEquiv
  have hsimpleY : IsSimpleGroup (Y ⧸ center Y) := g.isSimpleGroup
  have hcardY : Nat.card (Y ⧸ center Y) = cardS := (Nat.card_congr g.toEquiv).trans hcard
  have hncY : ∃ a b : Y ⧸ center Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨g.symm a, g.symm b, fun h => hab (g.symm.injective (by simpa [map_mul] using h))⟩
  have hO : CFSG.oddCore Y ≤ center Y := oddCore_le_center_of_simple_quotient (hcardY ▸ hev)
  let ρ : (Y ⧸ CFSG.oddCore Y) →* (Y ⧸ center Y) :=
    QuotientGroup.map _ _ (MonoidHom.id Y) (fun x hx => hO hx)
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hρk : ρ.ker ≤ center (Y ⧸ CFSG.oddCore Y) := by
    intro w hw
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    have hyc : y ∈ center Y := (QuotientGroup.eq_one_iff y).1 hw
    refine Subgroup.mem_center_iff.2 fun g' => ?_
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g'
    show QuotientGroup.mk (g' * y) = QuotientGroup.mk (y * g')
    rw [Subgroup.mem_center_iff.1 hyc g']
  obtain ⟨hWq, π, hπs, hπk, -⟩ := hY
  obtain ⟨e₁⟩ := quotientCenterEquiv_of_centralCover ρ hρs hρk hWq.1
  obtain ⟨e₂⟩ := quotientCenterEquiv_of_centralCover π hπs hπk hWq.1
  have hZ : center (Y ⧸ center Y) = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hncY
  have h1 : Nat.card ((Y ⧸ center Y) ⧸ center (Y ⧸ center Y)) = cardS := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, hcardY]
  have h2 := Nat.card_congr e₁.toEquiv
  have h3 := Nat.card_congr e₂.toEquiv
  omega

theorem nonabelian_of_isSimpleGroup_of_not_prime {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : IsMulCommutative G := ⟨⟨fun a b => hc a b⟩⟩
  exact h ((Group.is_simple_iff_prime_card).1 inferInstance)

theorem card_quotient_center_of_isSimpleGroup {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Nat.card (G ⧸ center G) = Nat.card G := by
  have hZ : center G = ⊥ :=
    center_eq_bot_of_isSimpleGroup_nonabelian (nonabelian_of_isSimpleGroup_of_not_prime h)
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv]

end CFSG.EvenSporadicStandard.Induction
