module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.A7Index15
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1Orbit
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.AGLEmbeddingD2.GN

theorem exists_orderOf_eq_three_of_alt_seven {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 7)) : ∃ x : G, orderOf x = 3 := by
  have h3 : 3 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.card_alternatingGroup_seven]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  exact exists_prime_orderOf_dvd_card' 3 h3

section Core

open MulAction CFSG.SectionRank.Ccomm

local notation "A₇" => alternatingGroup (Fin 7)

variable {U : Type*} [CommGroup U] [Finite U]

theorem not_forall_fixed_of_faithful (hU2 : ∀ u : U, u * u = 1) (hcard : Nat.card U = 2 ^ 4)
    (ρ : A₇ →* MulAut U) (hρ : Function.Injective ρ) {u₀ : U} (hu₀ : u₀ ≠ 1) :
    ¬ ∀ g : A₇, ρ g u₀ = u₀ := by
  intro hfix
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup A₇ := alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hu₀2 : u₀ ^ 2 = 1 := by rw [pow_two]; exact hU2 u₀
  have hord : orderOf u₀ = 2 := orderOf_eq_prime hu₀2 hu₀
  have hNcard : Nat.card (Subgroup.zpowers u₀) = 2 := by rw [Nat.card_zpowers, hord]
  have hQcard : Nat.card (U ⧸ Subgroup.zpowers u₀) = 2 ^ 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers u₀)
    rw [hcard, hNcard] at h
    omega
  have hNfix : ∀ (g : A₇) (c : U), c ∈ Subgroup.zpowers u₀ → ρ g c = c := by
    intro g c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [map_zpow, hfix g]
  have hmap : ∀ g : A₇, (Subgroup.zpowers u₀).map ((ρ g : MulAut U) : U →* U) =
      Subgroup.zpowers u₀ := by
    intro g
    refine le_antisymm ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact (hNfix g c hc).symm ▸ hc
    · intro c hc
      exact ⟨c, hc, hNfix g c hc⟩
  let ρbar : A₇ →* MulAut (U ⧸ Subgroup.zpowers u₀) :=
    { toFun := fun g => QuotientGroup.congr (Subgroup.zpowers u₀) (Subgroup.zpowers u₀) (ρ g)
        (hmap g)
      map_one' := by
        refine MulEquiv.ext fun x => ?_
        induction x using QuotientGroup.induction_on
        simp
      map_mul' := by
        intro g h
        refine MulEquiv.ext fun x => ?_
        induction x using QuotientGroup.induction_on
        simp }
  have hQ2 : ∀ q : U ⧸ Subgroup.zpowers u₀, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | _ u => rw [pow_two, ← QuotientGroup.mk_mul, hU2, QuotientGroup.mk_one]
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 2) (fun a b => mul_comm a b) hQ2 hQcard
  have hAut : Nat.card (MulAut (U ⧸ Subgroup.zpowers u₀)) = 168 := by
    rw [card_mulAut_eq_card_GL e, card_GL_zmod]
    simp [Fin.prod_univ_succ]
  have hker : ρbar.ker = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal ρbar.ker with h | h
    · exfalso
      have hinj : Function.Injective ρbar := (MonoidHom.ker_eq_bot_iff _).1 h
      have hd := Subgroup.card_dvd_of_injective ρbar hinj
      rw [CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.card_alternatingGroup_seven,
        hAut] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    · exact h
  obtain ⟨x, hx⟩ := exists_orderOf_eq_three_of_alt_seven (MulEquiv.refl A₇)
  have hx1 : ρ x = 1 := by
    refine MulEquiv.ext fun u => ?_
    have hb : ρbar x = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top x)
    have h1 : ((ρ x u : U) : U ⧸ Subgroup.zpowers u₀) = (u : U ⧸ Subgroup.zpowers u₀) := by
      have := congrArg (fun f : MulAut (U ⧸ Subgroup.zpowers u₀) =>
        f (u : U ⧸ Subgroup.zpowers u₀)) hb
      simpa [ρbar] using this
    have h2 : u⁻¹ * ρ x u ∈ Subgroup.zpowers u₀ := QuotientGroup.eq.1 h1.symm
    obtain ⟨c, hc⟩ : ∃ c : U, c = u⁻¹ * ρ x u := ⟨_, rfl⟩
    rw [← hc] at h2
    have hcu : ρ x u = u * c := by rw [hc, mul_inv_cancel_left]
    have hcfix : ρ x c = c := hNfix x c h2
    have hpow : ∀ j : ℕ, ρ (x ^ j) u = u * c ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, hcfix, hcu, pow_succ,
          mul_assoc, mul_comm c]
    have h3 : ρ (x ^ 3) u = u := by
      rw [← hx, pow_orderOf_eq_one, map_one, MulAut.one_apply]
    have hc3 : c ^ 3 = 1 := by
      have := hpow 3
      rw [h3] at this
      exact (mul_eq_left.1 this.symm)
    have hc2 : c ^ 2 = 1 := by rw [pow_two]; exact hU2 c
    have hc1 : c = 1 := by
      have : c ^ 3 = c := by rw [pow_succ, hc2, one_mul]
      rw [← this, hc3]
    rw [hcu, hc1, mul_one]
    rfl
  have hx2 : x = 1 := hρ (hx1.trans (map_one ρ).symm)
  rw [hx2, orderOf_one] at hx
  omega

theorem a7_exists_three_fixing_four (hU2 : ∀ u : U, u * u = 1) (hcard : Nat.card U = 2 ^ 4)
    (ρ : A₇ →* MulAut U) (hρ : Function.Injective ρ) (S : Subgroup A₇) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    ∃ x : A₇, orderOf x = 3 ∧ ∀ u : U, (∀ s ∈ S, ρ s u = u) → ρ x u = u := by
  classical
  let _ : MulAction A₇ U := MulAction.compHom U ρ
  have hact : ∀ (g : A₇) (u : U), g • u = ρ g u := fun _ _ => rfl
  have hX : Nat.card U = 16 := by rw [hcard]; norm_num
  have h0 : ∀ g : A₇, g • (1 : U) = 1 := fun g => by rw [hact, map_one]
  have huniq : ∀ u : U, (∀ g : A₇, g • u = u) → u = 1 := by
    intro u hu
    by_contra hne
    exact not_forall_fixed_of_faithful hU2 hcard ρ hρ hne fun g => by rw [← hact]; exact hu g
  by_cases hF : ∃ u₀ : U, u₀ ≠ 1 ∧ ∀ s ∈ S, ρ s u₀ = u₀
  · obtain ⟨u₀, hu₀, hSu₀⟩ := hF
    have h3 := three_dvd_card_stabilizer_of_card_sixteen hX (1 : U) h0 hu₀
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine ⟨(x : A₇), by rw [Subgroup.orderOf_coe]; exact hx, fun u hu => ?_⟩
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    · have heq := eq_of_fixed_of_card_sixteen hX (1 : U) h0 huniq hS hodd hu₀ hu1
        (fun s hs => by rw [hact]; exact hSu₀ s hs) (fun s hs => by rw [hact]; exact hu s hs)
      rw [← heq]
      exact mem_stabilizer_iff.1 x.2
  · push Not at hF
    obtain ⟨x, hx⟩ := exists_orderOf_eq_three_of_alt_seven (MulEquiv.refl A₇)
    refine ⟨x, hx, fun u hu => ?_⟩
    have hu1 : u = 1 := by
      by_contra hne
      obtain ⟨s, hs, hne'⟩ := hF u hne
      exact hne' (hu s hs)
    rw [hu1, map_one]

end Core

theorem kFactA7FourFixed_proved :
    ∀ (G U : Type) [Group G] [Group U] [Finite G] [Finite U], (∀ u : U, u * u = 1) →
      Nat.card U = 2 ^ 4 → ∀ (_ : G ≃* alternatingGroup (Fin 7)) (ρ : G →* MulAut U),
        Function.Injective ρ → ∀ S : Subgroup G, IsPGroup 2 S → ¬ 2 ∣ S.index →
          ∃ x : G, orderOf x = 3 ∧ ∀ u : U, (∀ s ∈ S, ρ s u = u) → ρ x u = u := by
  intro G U _ _ _ _ hU2 hcard e ρ hρ S hS hodd
  let _ : CommGroup U := { ‹Group U› with
    mul_comm := fun a b => by
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hU2 a)
      have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hU2 b)
      have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hU2 _)
      rw [mul_inv_rev, ha, hb] at hab
      exact hab.symm }
  let ρ' : alternatingGroup (Fin 7) →* MulAut U := ρ.comp e.symm.toMonoidHom
  have hρ' : Function.Injective ρ' := hρ.comp e.symm.injective
  obtain ⟨x', hx', hfix'⟩ := a7_exists_three_fixing_four hU2 hcard ρ' hρ'
    (S.map (e : G →* alternatingGroup (Fin 7))) (hS.map (e : G →* alternatingGroup (Fin 7)))
    (by rw [Subgroup.index_map_equiv]; exact hodd)
  refine ⟨e.symm x', by rw [MulEquiv.orderOf_eq]; exact hx', fun u hu => ?_⟩
  have := hfix' u (by
    rintro _ ⟨s, hs, rfl⟩
    simpa [ρ'] using hu s hs)
  simpa [ρ'] using this

theorem exists_three_fixing_four {G U : Type} [Group G] [Group U]
    [Finite G] [Finite U] (hU2 : ∀ u : U, u * u = 1) (hcard : Nat.card U = 2 ^ 4)
    (e : G ≃* alternatingGroup (Fin 7)) (ρ : G →* MulAut U) (S : Subgroup G) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    ∃ x : G, orderOf x = 3 ∧ ∀ u : U, (∀ s ∈ S, ρ s u = u) → ρ x u = u := by
  by_cases hρ : Function.Injective ρ
  · exact kFactA7FourFixed_proved G U hU2 hcard e ρ hρ S hS hodd
  · have hsimple : IsSimpleGroup G := by
      have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      exact MulEquiv.isSimpleGroup e
    have hker : ρ.ker = ⊤ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
      · exact absurd ((MonoidHom.ker_eq_bot_iff ρ).1 h) hρ
      · exact h
    obtain ⟨x, hx⟩ := exists_orderOf_eq_three_of_alt_seven e
    refine ⟨x, hx, fun u _ => ?_⟩
    have : ρ x = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top x)
    rw [this]
    rfl

end CFSG.AGLEmbeddingD2.GN
