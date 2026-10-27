module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55McLStar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55PermStep
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtOutMcL
public import CFSG.Sporadic.Recognition.McLCentralizerCert

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.McLN1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Sporadic.Recognition.LyonsSims

theorem mcl_n1_false
    {Y : Type} [Group Y] [Finite Y]
    (hY : Blueprint.NativeSporadic.IsSporadic Y .McL) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {b : MulAut Y} (hb : orderOf b = p) {R₀ : Subgroup Y} (hR₀ : IsSylowOf 2 R₀ ⊤)
    (hpg : IsPGroup p ↥(closure {c : MulAut Y | ∃ r ∈ R₀,
      c = MulAut.conj r * b * (MulAut.conj r)⁻¹})) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := id hY
  have hcard : Nat.card Y = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  have hfact : (Nat.card Y).factorization 2 = 7 := by
    rw [hcard, show (898128000 : ℕ) = 2 ^ 7 * 7016625 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_equiv_mcl e
  have hodd : Odd (orderOf b) := by
    rw [hb]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨y, hy⟩ := N1Core.inner_of_odd_order hZ (card_mulAut_of_equiv_mcl e) hodd
  obtain ⟨hy1, hyp, X, hXp, hyX, hN⟩ :=
    N1Core.n1_core hb hpg hy (N1Core.conj_injective hZ)
  have hR₀card : Nat.card ↥R₀ = 2 ^ (6 + 1) := by
    have h1 := IsSylowOf.card_eq hR₀
    rw [Subgroup.card_top, hfact] at h1
    exact h1
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hR₀card
    norm_num at hR₀card
  obtain ⟨τ, hτR, hτ2, hτc⟩ := Syl.exists_central_involution hR₀.isPGroup hR₀ne
  have hXC : X ≤ centralizer ({τ} : Set Y) :=
    WtP.mcl_central ⟨e⟩ hp2 hR₀card hτR hτ2 hτc hXp hN
  obtain ⟨-, hcen, ⟨q⟩⟩ :=
    CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ hτ2
  have hZc : Nat.card ↥(center ↥(centralizer ({τ} : Set Y))) = 2 := by
    rw [hcen, Nat.card_zpowers, Subgroup.orderOf_mk, hτ2]
  have hperm := PermStep.perm_step (n := 8) (e := 6) hp2 (Or.inl ⟨rfl, rfl⟩) hR₀card hτR hτ2 hτc
    hZc ((QuotientGroup.quotientMulEquivOfEq hcen).trans q) hXp hXC hN hyX hy1 hyp
  exact absurd hperm.1 (by norm_num)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.McLN1
