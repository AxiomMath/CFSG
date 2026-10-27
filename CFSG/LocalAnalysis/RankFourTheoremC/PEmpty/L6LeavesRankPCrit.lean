module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPDim
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup
open scoped commutatorElement

theorem eq_one_of_pow_coprime {M : Type*} [Monoid M] {σ : M} {a b : ℕ} (ha : σ ^ a = 1)
    (hb : σ ^ b = 1) (hab : Nat.Coprime a b) : σ = 1 := by
  have h1 : orderOf σ ∣ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf σ ∣ b := orderOf_dvd_of_pow_eq_one hb
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hab h1 h2)

open CFSG.SectionRank.Ccomm in
theorem aut_eq_one_of_frattiniAction {f p : ℕ} [Fact f.Prime] (hp : p.Prime) (hfp : f ≠ p)
    {Y : Type*} [Group Y] [Finite Y] (DE : Subgroup Y) [DE.Characteristic] (hDp : IsPGroup f DE)
    (hfix : IsPGroup f (fixingSubgroup (MulAut Y) (DE : Set Y))) (σ : MulAut Y) {m : ℕ}
    (hσ : σ ^ p ^ m = 1) (h1 : frattiniAction DE σ = 1) : σ = 1 := by
  have hcop : ∀ k : ℕ, Nat.Coprime (p ^ m) (f ^ k) := fun k =>
    Nat.Coprime.pow m k ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hfp))
  set β : MulAut DE := MulAut.characteristic DE σ with hβ
  have hβker : β ∈ (autQuotient (frattini DE)).ker := h1
  obtain ⟨a, ha⟩ := (isPGroup_ker_autQuotient_frattini hDp) ⟨β, hβker⟩
  have hβa : β ^ f ^ a = 1 := congrArg Subtype.val ha
  have hβp : β ^ p ^ m = 1 := by rw [hβ, ← map_pow, hσ, map_one]
  have hβ1 : β = 1 := eq_one_of_pow_coprime hβp hβa (hcop a)
  have hσfix : σ ∈ fixingSubgroup (MulAut Y) (DE : Set Y) := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact congrArg (fun τ : MulAut DE => ((τ ⟨x, hx⟩ : DE) : Y)) hβ1
  obtain ⟨b, hb⟩ := hfix ⟨σ, hσfix⟩
  exact eq_one_of_pow_coprime hσ (congrArg Subtype.val hb : σ ^ f ^ b = 1) (hcop b)

theorem card_commutator_map_subtype {X : Type*} [Group X] {H : Subgroup X} (K : Subgroup H) :
    Nat.card (commutator (K.map H.subtype)) = Nat.card (commutator K) := by
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  have h : (commutator K).map e.toMonoidHom = commutator (K.map H.subtype) := by
    unfold _root_.commutator
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← h]
  exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

open CFSG.SectionRank.Ccomm in
theorem exists_critical_big {f p : ℕ} (hf : f.Prime) (hp : p.Prime) (hf3 : 3 ≤ f) (hfp : f < p)
    {X : Type*} [Group X] [Finite X] {E : Subgroup X} (hE : IsPGroup f E)
    {P' : Subgroup X} (hP' : IsPGroup p P') (hPN : P' ≤ normalizer (E : Set X))
    (hfaith : ∀ g ∈ P', (∀ e ∈ E, g * e = e * g) → g = 1)
    (hnc : ¬ ∀ a ∈ P', ∀ b ∈ P', a * b = b * a) :
    ∃ D : Subgroup X, D ≤ E ∧ (∀ y ∈ normalizer (E : Set X), y ∈ normalizer (D : Set X)) ∧
      (∀ d ∈ D, d ^ f = 1) ∧ (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      f ^ (f + 1) * Nat.card (commutator D) ≤ Nat.card D := by
  haveI := Fact.mk hf
  haveI := Fact.mk hp
  have hf2 : f ≠ 2 := by omega
  have hfp' : f ≠ p := hfp.ne
  haveI : Nontrivial E := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hnc
    have h1 : ∀ a ∈ P', a = 1 := fun a ha => hfaith a ha (fun e he => by
      have : (⟨e, he⟩ : E) = 1 := Subsingleton.elim _ _
      have h2 : e = 1 := congrArg Subtype.val this
      rw [h2]
      simp)
    intro a ha b hb
    rw [h1 a ha, h1 b hb]
  obtain ⟨DE, hDEchar, hDEne, hDEcomm, hDEexp, hDEfix⟩ := odd_critical_exponent_subgroup hf2 hE
  haveI := hDEchar
  have hDp : IsPGroup f DE := hE.to_subgroup DE
  refine ⟨DE.map E.subtype, Subgroup.map_subtype_le DE, ?_, ?_, ?_, ?_⟩
  ·
    have hconj : ∀ y ∈ normalizer (E : Set X), ∀ h ∈ DE.map E.subtype,
        y * h * y⁻¹ ∈ DE.map E.subtype := by
      intro y hy h hh
      obtain ⟨d, hd, rfl⟩ := hh
      have hmap := Subgroup.characteristic_iff_map_eq.mp hDEchar (E.normalizerMonoidHom ⟨y, hy⟩)
      have hmem : (E.normalizerMonoidHom ⟨y, hy⟩) d ∈
          DE.map (E.normalizerMonoidHom ⟨y, hy⟩).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hd
      rw [hmap] at hmem
      exact ⟨_, hmem, rfl⟩
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨hconj y hy h, fun hh => ?_⟩
    have := hconj y⁻¹ (inv_mem hy) _ hh
    rwa [show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at this
  · rintro _ ⟨d, hd, rfl⟩
    have := congrArg Subtype.val (hDEexp d hd)
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    have hab : ⁅a, b⁆ ∈ ⁅DE, (⊤ : Subgroup E)⁆ := Subgroup.commutator_mem_commutator ha (mem_top b)
    have hcent := (hDEcomm hab).2
    have := (Subgroup.mem_centralizer_iff.mp hcent) c hc
    exact congrArg Subtype.val this.symm
  ·
    let ρE : P' →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
    let ρQ : P' →* MulAut (DE ⧸ frattini DE) := (frattiniAction DE).comp ρE
    have hρQ : ∀ g : P', ρQ g = 1 → g = 1 := by
      intro g hg
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP') g
      have hσ : (ρE g) ^ p ^ m = 1 := by rw [← map_pow, ← hm, pow_orderOf_eq_one, map_one]
      have hσ1 : ρE g = 1 :=
        aut_eq_one_of_frattiniAction hp hfp' DE hDp hDEfix (ρE g) hσ hg
      apply Subtype.ext
      apply hfaith g g.2
      intro e he
      have h2 : (g : X) * e * (g : X)⁻¹ = e :=
        congrArg (fun τ : MulAut E => ((τ ⟨e, he⟩ : E) : X)) hσ1
      calc (g : X) * e = ((g : X) * e * (g : X)⁻¹) * g := by group
        _ = e * g := by rw [h2]
    obtain ⟨-, hQcomm, hQpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
    have hnc' : ¬ ∀ a b : P', a * b = b * a := fun h =>
      hnc fun a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
    have hbig := card_ge_of_faithful_nonabelian hf hp hfp' (fun a b => hQcomm.is_comm.comm a b)
      hQpow hP' ρQ hρQ hnc'
    have hexpDE : ∀ x : DE, x ^ f = 1 := fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hDEexp x x.2)
    have hfc : frattini DE = commutator DE :=
      CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexpDE
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini DE)
    rw [hfc] at hcard
    rw [Subgroup.card_map_of_injective E.subtype_injective, card_commutator_map_subtype]
    rw [hfc] at hbig
    calc f ^ (f + 1) * Nat.card (commutator DE) ≤ f ^ p * Nat.card (commutator DE) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hf.pos hfp)
      _ ≤ Nat.card (DE ⧸ commutator DE) * Nat.card (commutator DE) :=
          Nat.mul_le_mul_right _ hbig
      _ = Nat.card DE := hcard.symm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
