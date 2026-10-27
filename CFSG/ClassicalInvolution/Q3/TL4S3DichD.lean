module

public import CFSG.ClassicalInvolution.Q3.TL4S3DichC
public import CFSG.ClassicalInvolution.AschTight.S19GD4Aut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S3Dich

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19G CFSG.ClassicalInvolution.Asc77


theorem invDich_twistedD4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (heo : Odd e) {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    {L₀ : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hL₀ : IsSylow2In L₀ R) :
    InvDich ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) L₀ := by
  obtain ⟨hσ3, hK1, hC₀, hgF, hoddK, hoddF⟩ := d4_model_data hp2 he
  intro ρ hρ2 hρL
  obtain ⟨g, δ, β₀, hρg, -, hδ, hδ1⟩ := exists_field_form_d4 hp2 he ρ (n := 1)
    (by rw [pow_one, sq, hρ2])
  have hδ' : δ = 1 := by
    by_contra h
    have h3 : Odd (3 * e) := Nat.odd_mul.mpr ⟨by decide, heo⟩
    exact (Nat.not_even_iff_odd.mpr h3) (ringEquiv_sq_eq_one_facts (Fact.out : p.Prime)
      (f := 3 * e) (by omega) (GaloisField.card p (3 * e) (by omega))
      (by rwa [pow_one] at hδ) h).1
  have hρx : ∀ x, ρ x = g * x * g⁻¹ := fun x => by rw [hρg, hδ1 hδ' x]
  have hZ : Subgroup.center ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) = ⊥ :=
    CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 he
  have hg2 : g * g = 1 := by
    have hc : g * g ∈ Subgroup.center
        ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : (ρ * ρ) x = x := by rw [hρ2]; rfl
      rw [MulAut.mul_apply, hρx, hρx] at h1
      calc x * (g * g) = (g * (g * x * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = g * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hgL : ∀ y ∈ L₀, g * y = y * g := by
    intro y hy
    have h1 := hρL y hy
    rw [hρx] at h1
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h1]
  refine ⟨g, ?_, hg2, MulEquiv.ext fun x => (hρx x).trans (MulAut.conj_apply g x).symm⟩
  obtain ⟨i, g₀, hRg⟩ := exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨h, hh⟩ : ∃ h : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), h = g₀ :=
    ⟨g₀, rfl⟩
  have hR' : R = conjSub h (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    rw [hh]
    exact hRg
  subst hR'
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3] at hL₀
    obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one hoddF
    exact mem_of_centralizes_sylow hoddF hab (slLong _ hσ3) (slLong_injective hσ3)
      (fun c hc => linAct_of_centralizes_long hσ3 hK1
        (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hoddF) hC₀ hgF hc)
      (fun x hx2 hc => eq_one_or_eq_of_centralizing_slLong hσ3 hK1 hC₀ hgF hx2 hc) h hL₀ hg2 hgL
  · have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3] at hL₀
    obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one hoddK
    exact mem_of_centralizes_sylow hoddK hab (slShort _ hσ3) (slShort_injective hσ3)
      (fun c hc => linAct_of_centralizes_short hσ3 hK1
        (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hoddK) hC₀ hgF hc)
      (fun x hx2 hc => eq_one_or_eq_of_centralizing_slShort hσ3 hK1 hC₀ hgF hx2 hc) h hL₀ hg2 hgL

theorem invDich_td4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (heo : Odd e)
    {R : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D)
    {L₀ : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K} (hL₀ : IsSylow2In L₀ R) :
    InvDich (modelUniv .trialityD4 0 p e Fact.out).K L₀ :=
  invDich_twistedD4 hp2 he heo hR hL₀

end CFSG.ClassicalInvolution.Q3.TL4.S3Dich
