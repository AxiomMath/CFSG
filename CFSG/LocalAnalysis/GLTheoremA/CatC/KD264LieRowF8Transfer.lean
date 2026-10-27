module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Transfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

section F8Transfer

variable {S : Type} [Group S]

theorem kd264F8_commute {A : Subgroup (MulAut S)} (hA : IsElemAbelian 3 A)
    {b c : MulAut S} (hb : b ∈ A) (hc : c ∈ A) : Commute b c :=
  congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)

theorem kd264F8_orderOf {A : Subgroup (MulAut S)} (hA : IsElemAbelian 3 A)
    {c : MulAut S} (hc : c ∈ A) (hc1 : c ≠ 1) : orderOf c = 3 :=
  orderOf_eq_prime (hA.2 c hc) hc1

theorem kd264F8_zpowers_le_normalizer {b c : MulAut S} (hbc : Commute b c) :
    Subgroup.zpowers c ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup (MulAut S)) : Set (MulAut S)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  have hfix : ∀ x ∈ Subgroup.zpowers b, c * x * c⁻¹ = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [(hbc.symm.zpow_right k).eq, mul_inv_cancel_right]
  have hfix' : ∀ x ∈ Subgroup.zpowers b, c⁻¹ * x * c = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [((hbc.symm.inv_left).zpow_right k).eq, inv_mul_cancel_right]
  intro h
  constructor
  · intro hh
    rw [hfix h hh]
    exact hh
  · intro hh
    have h1 : c⁻¹ * (c * h * c⁻¹) * c = h := by group
    have h2 : c⁻¹ * (c * h * c⁻¹) * c = c * h * c⁻¹ := hfix' _ hh
    have h3 : h = c * h * c⁻¹ := h1.symm.trans h2
    rw [h3]
    exact hh

theorem kd264F8_natCard_sup [Finite S] {A : Subgroup (MulAut S)} (hA : IsElemAbelian 3 A)
    {b c : MulAut S} (hb : b ∈ A) (hc : c ∈ A) (hc1 : c ≠ 1) (hbc : b ∉ Subgroup.zpowers c) :
    Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = 9 := by
  have hcomm : Commute b c := kd264F8_commute hA hb hc
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbc (Subgroup.one_mem _)
  have hNb : Nat.card ↥(Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, kd264F8_orderOf hA hb hb1]
  have hNc : Nat.card ↥(Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, kd264F8_orderOf hA hc hc1]
  have hcard := card_sup_mul_card_inf_of_le_normalizer (kd264F8_zpowers_le_normalizer hcomm)
  have hinf : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ Subgroup.zpowers c) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers b ⊓ Subgroup.zpowers c ≤
        Subgroup.zpowers b)
      rwa [hNb] at this
    have h3 : Nat.card ↥(Subgroup.zpowers b ⊓ Subgroup.zpowers c) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hne
      · exact h
    have heq : Subgroup.zpowers b ⊓ Subgroup.zpowers c = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hNb])
    have hbz : b ∈ Subgroup.zpowers c := by
      have hmem : b ∈ Subgroup.zpowers b ⊓ Subgroup.zpowers c := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hmem.2
    exact hbc hbz
  rw [hinf, Subgroup.card_bot, hNb, hNc] at hcard
  omega

theorem kd264F8_le_fixSubgroup_iInf {H : Subgroup S} {b c : MulAut S}
    (hb : H ≤ fixSubgroup b) (hc : H ≤ fixSubgroup c) :
    H ≤ ⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c, fixSubgroup f := by
  let T : Subgroup (MulAut S) :=
    { carrier := {g | ∀ x ∈ H, g x = x}
      mul_mem' := fun {g h} hg hh => by
        show ∀ x ∈ H, g (h x) = x
        intro x hx
        rw [hh x hx]
        exact hg x hx
      one_mem' := fun x _ => rfl
      inv_mem' := fun {g} hg => by
        show ∀ x ∈ H, g⁻¹ x = x
        intro x hx
        have h1 : g x = x := hg x hx
        calc g⁻¹ x = g⁻¹ (g x) := by rw [h1]
          _ = x := by simp }
  have hT : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ T := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · show ∀ x ∈ H, b x = x
      intro x hx
      exact mem_fixSubgroup.1 (hb hx)
    · show ∀ x ∈ H, c x = x
      intro x hx
      exact mem_fixSubgroup.1 (hc hx)
  refine le_iInf₂ fun f hf => ?_
  intro x hx
  have hfT : f ∈ T := hT hf
  exact mem_fixSubgroup.2 (hfT x hx)

theorem kd264F8_exists_good [Finite S] {A : Subgroup (MulAut S)} (hA : IsElemAbelian 3 A)
    {b c : MulAut S} (hb : b ∈ A) (hc : c ∈ A) (hc1 : c ≠ 1) (hbc : b ∉ Subgroup.zpowers c)
    {H : Subgroup S} (hHb : H ≤ fixSubgroup b) (hHc : H ≤ fixSubgroup c)
    (hsub : IsSubnormal H (⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c, fixSubgroup f))
    (hq : CFSG.Open.IsQuasisimple ↥H) (hdvd : 3 ∣ Nat.card (↥H ⧸ Subgroup.center ↥H)) :
    ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F :=
  ⟨Subgroup.zpowers b ⊔ Subgroup.zpowers c,
    sup_le (Subgroup.zpowers_le.2 hb) (Subgroup.zpowers_le.2 hc),
    kd264F8_natCard_sup hA hb hc hc1 hbc,
    isGood_three_of_quasisimple rfl (kd264F8_le_fixSubgroup_iInf hHb hHc) hsub hq hdvd⟩

end F8Transfer

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
