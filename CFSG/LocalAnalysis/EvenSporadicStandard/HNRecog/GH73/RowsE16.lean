module

public import CFSG.RankThree.PartOne.S11c.G2Plane
public import CFSG.CGT.T75P.A8ExclPGL
public import CFSG.ClassicalInvolution.AschTight.S19GD4Inv
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
open CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

variable {X : Type} [Group X]

private theorem a8x_isElementaryAbelian_of_sq {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 2 = 1) :
    IsElementaryAbelian 2 E := by
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact Subtype.ext (hE a a.2))
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact Subtype.ext (hE b b.2))
    have hab : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact Subtype.ext (hE (a * b) (a * b).2))
    rw [mul_inv_rev, ha, hb] at hab
    exact hab.symm
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext (hE x x.2)

theorem not_g2_of_e16
    (hE : ∃ E : Subgroup X, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) : ¬ LieModel X .G2 0 p f := by
  intro hL
  have hm : ChevalleyExceptionalModel X .G2 p f := by
    rcases hL with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact hm
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm.2
  have hodd : Odd (Nat.card K) := by
    rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨E, hE16, hEsq⟩ := hE
  let ψ : X →* ModGL .G2 K := (adjointGroup .G2 K).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  have hR : E.map ψ ≤ adjointGroup .G2 K := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE16]; norm_num)
  let eR : E ≃* E.map ψ := E.equivMapOfInjective ψ hψ
  have : Finite (E.map ψ) := Finite.of_equiv E eR.toEquiv
  have : IsElementaryAbelian 2 E := a8x_isElementaryAbelian_of_sq hEsq
  have : IsElementaryAbelian 2 (E.map ψ) := isElementaryAbelian_of_mulEquiv' eR inferInstance
  have hle := (g2_elementary_two hodd hR).1
  rw [← Nat.card_congr eR.toEquiv, hE16] at hle
  omega

theorem not_trialityD4_of_e16
    (hE : ∃ E : Subgroup X, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) : ¬ LieModel X .trialityD4 0 p f := by
  intro hL
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hL
  obtain ⟨hσ, hK, hC₀, hgF, -, hoddF⟩ := d4_model_data (p := p) hp2 hf
  obtain ⟨E, hE16, hEsq⟩ := hE
  have h2 : (2 : fixedField (sig0 p f)) ≠ 0 :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19F.two_ne_zero_of_odd hoddF
  have hle := CFSG.CGT.T75P.a8x_card_le_eight_of_chart
    (CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hoddF) (slLong _ hσ) (slLong_injective hσ)
    (tauL_mul_self hσ) (tauL_ne_one hσ hK)
    (fun x y hx hy hx1 hy1 =>
      CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf hx hy hx1 hy1)
    (fun x hx => linAct_of_centralizes_long hσ hK h2 hC₀ hgF hx)
    (fun x hx hc => eq_one_or_eq_of_centralizing_slLong hσ hK hC₀ hgF hx hc)
    (E.map φ.toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩
      show φ x * φ x = 1
      rw [← map_mul, ← sq, hEsq x hx, map_one])
  rw [← Nat.card_congr (E.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv, hE16] at hle
  omega

end CFSG.EvenSporadicStandard.HNRecog.GH73
