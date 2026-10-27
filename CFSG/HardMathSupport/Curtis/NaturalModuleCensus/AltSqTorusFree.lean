module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.EvenCentre

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

theorem not_pow_three_dvd_card_alt_sq {p : ℕ} (hp : p.Prime) :
    ¬ p ^ 3 ∣ Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) := by
  intro h
  rw [Nat.card_prod] at h
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.2 hp.two_le
  have h2a := two_mul_nat_card_alternatingGroup (α := Fin p)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin p)), Fintype.card_perm,
    Fintype.card_fin] at h2a
  set a := Nat.card (alternatingGroup (Fin p)) with ha
  have h3 : p ^ 3 ∣ p.factorial * p.factorial := by
    rw [← h2a]
    exact h.trans ⟨4, by ring⟩
  have hfac : p.factorial = p * (p - 1).factorial := (Nat.mul_factorial_pred hp.pos.ne').symm
  rw [hfac] at h3
  have h3' : p ^ 2 * p ∣ p ^ 2 * ((p - 1).factorial * (p - 1).factorial) := by
    calc p ^ 2 * p = p ^ 3 := by ring
      _ ∣ p * (p - 1).factorial * (p * (p - 1).factorial) := h3
      _ = p ^ 2 * ((p - 1).factorial * (p - 1).factorial) := by ring
  have h4 : p ∣ (p - 1).factorial * (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h3'
  rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5 <;>
    · have := (hp.dvd_factorial).1 h5
      have := hp.pos
      omega

theorem false_of_pow_three_of_altSq {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {J : Subgroup Y} (hAlt : PerfectSectionsAltSq p J) {E : Subgroup Y}
    (hEPJ : E ≤ perfectJoin J) (hEel : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) :
    False := by
  obtain ⟨V₀, hV₀le, hV₀n, hV₀p, f, hf⟩ :=
    hAlt (perfectJoin J) (perfectJoin_le J) (perfectJoin_perfect J)
  let E' : Subgroup ↥(perfectJoin J) := E.subgroupOf (perfectJoin J)
  have hE' : Nat.card E' = p ^ 3 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEPJ).toEquiv
  have hinj : Function.Injective (f.comp E'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hfx : f (x : ↥(perfectJoin J)) = 1 := hx
    have hxV : (x : ↥(perfectJoin J)) ∈ V₀.subgroupOf (perfectJoin J) := by
      rw [← hf]
      exact MonoidHom.mem_ker.2 hfx
    have hxE : ((x : ↥(perfectJoin J)) : Y) ∈ E := x.2
    have hxp : ((x : ↥(perfectJoin J)) : Y) ^ p = 1 := hEel.2 _ hxE
    have hxV' : ((x : ↥(perfectJoin J)) : Y) ∈ V₀ := hxV
    have h1 : orderOf ((x : ↥(perfectJoin J)) : Y) ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have h2 : orderOf ((x : ↥(perfectJoin J)) : Y) ∣ Nat.card V₀ := by
      have := orderOf_dvd_natCard (⟨((x : ↥(perfectJoin J)) : Y), hxV'⟩ : ↥V₀)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : orderOf ((x : ↥(perfectJoin J)) : Y) ∣ Nat.gcd p (Nat.card V₀) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hV₀p] at h3
    have h4 : orderOf ((x : ↥(perfectJoin J)) : Y) = 1 := Nat.dvd_one.1 h3
    have h5 : ((x : ↥(perfectJoin J)) : Y) = 1 := orderOf_eq_one_iff.1 h4
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h5)
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  rw [hE'] at hdvd
  exact not_pow_three_dvd_card_alt_sq hp hdvd

theorem no_pow_three_of_altSq_hub {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}
    (h : CompParabE L J) (hp : p.Prime) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hH : PerfectJoinHub p (↥L ⧸ Subgroup.center ↥L)) (hAlt : PerfectSectionsAltSq p J)
    {x : Y} (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    (hE : ∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) : False := by
  obtain ⟨E, hEle, hEel, hEc⟩ := hE
  have hEJ : E ≤ J := fun y hy => hfix y (hEle hy).1 (by
    have := Subgroup.mem_centralizer_iff.1 (hEle hy).2 x (Set.mem_singleton x)
    rw [this, mul_inv_cancel_right])
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card (n := 3) hEc
  exact false_of_pow_three_of_altSq hp hAlt (pSubgroup_le_perfectJoin_of_parabolic_central h.parab hp hpZ hH hEJ hEp) hEel hEc

theorem no_pow_three_of_altSq_torusFree_classical (hGA : CFSG.Open.GriessAllModelsStatement)
    {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD) {Y : Type}
    [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ} (h : CompParabE L J) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : IsLieOfTorusFree P p (↥L ⧸ Subgroup.center ↥L))
    (hAlt : PerfectSectionsAltSq p J) {x : Y} (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    (hE : ∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) : False := by
  obtain ⟨d, hPd, ht, ⟨e⟩⟩ := hX
  obtain ⟨hd, hG2⟩ := ToralCensus.classical_index hP hPd
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.comp.2.2.1
  have hpZ := ToralCensus.not_dvd_card_center_of_index hGA d hd e hp hp5 ht
  exact no_pow_three_of_altSq_hub h hp hpZ
    (perfectJoinHub_of_classicalIndex d hd hG2 e hp hp5 ht) hAlt hfix hE

theorem no_pow_three_of_altSq_torusFree_g2 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type}
    [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ} (h : CompParabE L J) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : IsLieOfTorusFree IdxG2 p (↥L ⧸ Subgroup.center ↥L))
    (hAlt : PerfectSectionsAltSq p J) {x : Y} (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    (hE : ∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) : False := by
  obtain ⟨d, hPd, ht, ⟨e⟩⟩ := hX
  have hd : IsClassicalOrG2Index d.1 := by
    obtain ⟨d, hv⟩ := d
    cases d <;> first | exact hPd | exact hPd.elim
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.comp.2.2.1
  have hpZ := ToralCensus.not_dvd_card_center_of_index hGA d hd e hp hp5 ht
  exact no_pow_three_of_altSq_hub h hp hpZ (perfectJoinHub_of_index d hd e hp hp5 ht) hAlt
    hfix hE

theorem no_pow_three_of_small
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} {p : ℕ} (h : CompParabE L J) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hS : IsSmallTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {E : Subgroup Y} (hEL : E ≤ L)
    (hcard : Nat.card E = p ^ 3) : False := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.comp.2.2.1
  have hZ : Nat.card (Subgroup.center ↥L) ∣ 6 := card_center_dvd_six_of_small hGA hS
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
    intro hpd
    have h6 : p ∣ 6 := hpd.trans hZ
    have := Nat.le_of_dvd (by norm_num) h6
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  have hEL' : Nat.card E ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hEL
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)] at hEL'
  have hcop : Nat.Coprime (p ^ 3) (Nat.card (Subgroup.center ↥L)) :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpZ)
  have h3 : p ^ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    hcop.dvd_of_dvd_mul_right (hcard ▸ hEL')
  have hQ := (ToralCensus.card_dvd_of_small hS)
  exact ToralCensus.not_sq_dvd_smallBound hp hp5
    (((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans h3).trans (hQ.trans (by norm_num)))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
