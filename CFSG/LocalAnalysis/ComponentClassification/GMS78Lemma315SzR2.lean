module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzX

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_sq_eq_conj {U A : Subgroup G} {d : G} (f : G → G)
    (hAc : ∀ u ∈ U, ∀ b ∈ A, u * b = b * u) (hA2 : ∀ b ∈ A, b ^ 2 = 1)
    (hU2 : ∀ u ∈ U, u ^ 2 ∈ A) (hdU : d ∈ normalizer (U : Set G))
    (htr : ∀ b ∈ A, ∀ b' ∈ A, b ≠ 1 → b' ≠ 1 → ∃ k : ℕ, (d ^ k)⁻¹ * b * d ^ k = b')
    (hfA : ∀ u ∈ U, f u ∈ A) (hfmul : ∀ u ∈ U, ∀ u' ∈ U, f (u * u') = f u * f u')
    (hfker : ∀ u ∈ U, f u = 1 ↔ u ∈ A)
    (hfeq : ∀ k : ℕ, ∀ u ∈ U, f ((d ^ k)⁻¹ * u * d ^ k) = (d ^ k)⁻¹ * f u * d ^ k) :
    ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
  have hf1 : f 1 = 1 := (hfker 1 (one_mem _)).mpr (one_mem _)
  have hfinv : ∀ u ∈ U, f u⁻¹ = (f u)⁻¹ := fun u hu => by
    have := hfmul u⁻¹ (inv_mem hu) u hu
    rw [inv_mul_cancel, hf1] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hrel : ∀ u ∈ U, ∀ u' ∈ U, f u = f u' → u ^ 2 = u' ^ 2 := by
    intro u hu u' hu' he
    have hb : u⁻¹ * u' ∈ A := by
      rw [← hfker _ (mul_mem (inv_mem hu) hu'), hfmul _ (inv_mem hu) _ hu', hfinv u hu, he,
        inv_mul_cancel]
    obtain ⟨b, hbA, rfl⟩ : ∃ b ∈ A, u * b = u' := ⟨_, hb, by group⟩
    have hcomm := hAc u hu b hbA
    calc u ^ 2 = u ^ 2 * b ^ 2 := by rw [hA2 b hbA, mul_one]
      _ = u * (u * b) * b := by rw [sq, sq]; group
      _ = u * (b * u) * b := by rw [hcomm]
      _ = (u * b) ^ 2 := by rw [sq]; group
  have hsq : ∀ u ∈ U, ∀ u' ∈ U, (u * u') ^ 2 = u ^ 2 * u' ^ 2 := by
    by_cases hall : ∀ u ∈ U, u ^ 2 = 1
    · intro u hu u' hu'
      rw [hall _ (mul_mem hu hu'), hall u hu, hall u' hu', one_mul]
    push Not at hall
    obtain ⟨u₀, hu₀, hu₀2⟩ := hall
    have hu₀A : u₀ ∉ A := fun h => hu₀2 (hA2 u₀ h)
    have hb₀ : f u₀ ≠ 1 := fun h => hu₀A ((hfker u₀ hu₀).mp h)
    obtain ⟨j, hj⟩ := htr _ (hfA u₀ hu₀) _ (hU2 u₀ hu₀) hb₀ hu₀2
    have hform : ∀ u ∈ U, u ^ 2 = (d ^ j)⁻¹ * f u * d ^ j := by
      intro u hu
      by_cases huA : u ∈ A
      · rw [hA2 u huA, (hfker u hu).mpr huA]
        group
      have hfu : f u ≠ 1 := fun h => huA ((hfker u hu).mp h)
      obtain ⟨k, hk⟩ := htr _ (hfA u₀ hu₀) _ (hfA u hu) hb₀ hfu
      have hw : (d ^ k)⁻¹ * u₀ * d ^ k ∈ U := by
        have := (mem_normalizer_iff.mp (inv_mem (pow_mem hdU k)) u₀).mp hu₀
        simpa using this
      have h1 := hrel u hu _ hw (by rw [hfeq k u₀ hu₀, hk])
      rw [h1]
      have e : ((d ^ k)⁻¹ * u₀ * d ^ k) ^ 2 = (d ^ k)⁻¹ * u₀ ^ 2 * d ^ k := by rw [sq, sq]; group
      rw [e, ← hj, ← hk]
      have hc : d ^ j * d ^ k = d ^ k * d ^ j := (pow_mul_comm d j k)
      calc (d ^ k)⁻¹ * ((d ^ j)⁻¹ * f u₀ * d ^ j) * d ^ k =
          (d ^ j * d ^ k)⁻¹ * f u₀ * (d ^ j * d ^ k) := by group
        _ = (d ^ k * d ^ j)⁻¹ * f u₀ * (d ^ k * d ^ j) := by rw [hc]
        _ = (d ^ j)⁻¹ * ((d ^ k)⁻¹ * f u₀ * d ^ k) * d ^ j := by group
    intro u hu u' hu'
    rw [hform _ (mul_mem hu hu'), hform u hu, hform u' hu', hfmul u hu u' hu']
    group
  intro u hu u' hu'
  have h := hsq u hu u' hu'
  rw [sq, sq, sq] at h
  have h' : u' * u * u' = u * u' * u' := by
    have := congrArg (fun g => u⁻¹ * g) h
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
    calc u' * u * u' = u⁻¹ * u * u' * u * u' := by group
      _ = u⁻¹ * (u * u') * (u * u') := by group
      _ = u⁻¹ * (u * u * (u' * u')) := by rw [mul_assoc, h]
      _ = u * u' * u' := by group
  have := congrArg (fun g => g * u'⁻¹) h'
  simp only [mul_inv_cancel_right] at this
  exact this.symm

namespace Sec3

variable {L T R X R₂ : Subgroup G} {a : ℕ} {y d : G}

structure IsR₂ (L T R R₂ : Subgroup G) (d : G) : Prop where
  gmsA_le : gmsA L T ≤ R₂
  le_R : R₂ ≤ R
  mem_normalizer : d ∈ normalizer (R₂ : Set G)
  sup_eq : T ⊔ R₂ = R
  inf_eq : T ⊓ R₂ = gmsA L T

namespace SzR

variable (hS : SzR G L T R a y d)
include hS

omit [Finite G] hS in
theorem gmsA_le_T : gmsA L T ≤ T := inf_le_left.trans inf_le_left

theorem exists_isR₂
    (h34 : NoStronglyClosedAbelian G) : ∃ R₂, IsR₂ L T R R₂ d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have hD : Nat.Coprime 2 (Nat.card (zpowers d)) := by
    rw [Nat.card_zpowers]
    exact Nat.coprime_two_left.mpr hS.odd
  have hconj : ∀ {H : Subgroup G}, d ∈ normalizer (H : Set G) →
      ∀ g ∈ zpowers d, ∀ x ∈ H, g * x * g⁻¹ ∈ H := by
    intro H hdH g hg x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (mem_normalizer_iff.mp (zpow_mem hdH k) x).mp hx
  have hdT : d ∈ normalizer (T : Set G) := by
    rw [hS.eq_gmsW]
    exact hS.mem_normalizer_gmsW
  have hdA : d ∈ normalizer (gmsA L T : Set G) := (GMS78.mem_gmsN₁.mp hS.d_mem_gmsN₁).2.1
  obtain ⟨R₂, hAR₂, hR₂R, hdR₂, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 2) (Q := R) (Φ := gmsA L T)
      (D := zpowers d) (T := T) (gmsA_le_T.trans hS.T_le)
      (fun x hx y hy => hS.commutator_mem_gmsA_of_isX h34 hX hx hy)
      (fun x hx => hS.sq_mem_gmsA_of_mem_R h34 hX hx) hD (hconj hS.mem_normalizer)
      (hconj hdA) gmsA_le_T hS.T_le (hconj hdT)
  refine ⟨R₂, hAR₂, hR₂R, mem_normalizer_iff.mpr fun x => ⟨fun hx => hdR₂ d (mem_zpowers d) x hx,
    fun hx => ?_⟩, hsup, hinf⟩
  have := hdR₂ d⁻¹ (inv_mem (mem_zpowers d)) _ hx
  simpa [mul_assoc] using this

theorem not_mem_centralizer_of_isR₂
    (hR₂ : IsR₂ L T R R₂ d) {r : G} (hr : r ∈ R₂) (hrA : r ∉ gmsA L T) :
    r ∉ centralizer (gmsV L T : Set G) := fun hrC => hrA (by
  rw [← hR₂.inf_eq, ← hS.inf_centralizer_R]
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨hR₂.le_R hr, hrC⟩, hr⟩)

theorem exists_pow_conj_eq_gmsA {b b' : G} (hb : b ∈ gmsA L T) (hb' : b' ∈ gmsA L T)
    (hb1 : b ≠ 1) (hb'1 : b' ≠ 1) : ∃ k : ℕ, (d ^ k)⁻¹ * b * d ^ k = b' := by
  obtain ⟨k, hk⟩ := hS.torus.trans b hb b' hb' hb1 hb'1
  refine ⟨k, ?_⟩
  rw [inv_pow_conj_eq hS.mem_normalizer_gmsW hS.torus.mem_normalizer_gmsW hS.conj_eq k b
    (mem_sup_left (mem_inf.mp hb).1), hk]

theorem commutator_mul {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R) :
    r * r' * t * (r * r')⁻¹ * t⁻¹ = r * t * r⁻¹ * t⁻¹ * (r' * t * r'⁻¹ * t⁻¹) := by
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have htV : t ∈ gmsV L T := mem_sup_right ht
  have hc : r * t * r⁻¹ * t⁻¹ ∈ gmsA L T := conj_mul_inv_mem (hS.isR.le_gmsTrans hr) htV
  have hc' : r' * t * r'⁻¹ * t⁻¹ ∈ gmsA L T := conj_mul_inv_mem (hS.isR.le_gmsTrans hr') htV
  have hrc' : r * (r' * t * r'⁻¹ * t⁻¹) * r⁻¹ = r' * t * r'⁻¹ * t⁻¹ := by
    rw [commute_of_mem_gmsTrans (hS.isR.le_gmsTrans hr) hc']
    group
  have hcomm : r' * t * r'⁻¹ * t⁻¹ * (r * t * r⁻¹ * t⁻¹) =
      r * t * r⁻¹ * t⁻¹ * (r' * t * r'⁻¹ * t⁻¹) :=
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨_, mem_sup_left hc'⟩ ⟨_, mem_sup_left hc⟩)
  calc r * r' * t * (r * r')⁻¹ * t⁻¹ =
      r * (r' * t * r'⁻¹ * t⁻¹) * r⁻¹ * (r * t * r⁻¹ * t⁻¹) := by group
    _ = r * t * r⁻¹ * t⁻¹ * (r' * t * r'⁻¹ * t⁻¹) := by rw [hrc', hcomm]

theorem commutator_conj_pow {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) (k : ℕ) (r : G) :
    (d ^ k)⁻¹ * r * d ^ k * t * ((d ^ k)⁻¹ * r * d ^ k)⁻¹ * t⁻¹ =
      (d ^ k)⁻¹ * (r * t * r⁻¹ * t⁻¹) * d ^ k := by
  have h1 : Commute d t := by
    have := hS.commute_T₀ ht
    calc d * t = d * t * d⁻¹ * d := by group
      _ = t * d := by rw [this]
  have h3 : (d ^ k)⁻¹ * t * d ^ k = t := by
    rw [mul_assoc, ← (h1.pow_left k).eq]
    group
  conv_lhs => rw [← h3]
  group

theorem commutator_eq_one_iff
    (hR₂ : IsR₂ L T R R₂ d) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1)
    {r : G} (hr : r ∈ R₂) : r * t * r⁻¹ * t⁻¹ = 1 ↔ r ∈ gmsA L T := by
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have htV : t ∈ gmsV L T := mem_sup_right ht
  constructor
  · intro h1
    by_contra hrA
    have hrt : r * t = t * r := by
      calc r * t = r * t * r⁻¹ * t⁻¹ * (t * r) := by group
        _ = t * r := by rw [h1, one_mul]
    have htA := mem_gmsA_of_commute hS.lemma313 hS.facts hS.sec3 hS.foundation
      (hS.isR.le_gmsTrans (hR₂.le_R hr)) (hS.not_mem_centralizer_of_isR₂ hR₂ hr hrA) htV hrt
    have := hS.lemma313.inf_gmsA_eq_bot mem_delta_T₀
    have ht' : t ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨ht, htA⟩
    rw [this, mem_bot] at ht'
    exact ht1 ht'
  · intro hrA
    have hc : r * t = t * r :=
      congrArg Subtype.val (hVel.1.is_comm.comm ⟨r, mem_sup_left hrA⟩ ⟨t, htV⟩)
    rw [hc]
    group

theorem commute_of_isR₂
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) {r r' : G} (hr : r ∈ R₂)
    (hr' : r' ∈ R₂) : r * r' = r' * r := by
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  obtain ⟨-, hA₁sq, -⟩ := hS.facts.sylow hS.sec3
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS.sec3.T₀_ne_bot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  refine commute_of_sq_eq_conj (U := R₂) (A := gmsA L T) (d := d)
    (fun r => r * t * r⁻¹ * t⁻¹) (fun u hu b hb => ?_) hA₁sq
    (fun u hu => hS.sq_mem_gmsA_of_mem_R h34 hX (hR₂.le_R hu)) hR₂.mem_normalizer
    (fun b hb b' hb' hb1 hb'1 => hS.exists_pow_conj_eq_gmsA hb hb' hb1 hb'1)
    (fun u hu => conj_mul_inv_mem (hS.isR.le_gmsTrans (hR₂.le_R hu)) (mem_sup_right ht))
    (fun u hu u' hu' => hS.commutator_mul ht (hR₂.le_R hu) (hR₂.le_R hu'))
    (fun u hu => hS.commutator_eq_one_iff hR₂ ht ht1' hu)
    (fun k u _ => hS.commutator_conj_pow ht k u) r hr r' hr'
  exact commute_of_mem_gmsTrans (hS.isR.le_gmsTrans (hR₂.le_R hu)) hb

theorem exists_mem_R_not_mem_T :
    ∃ r ∈ R, r ∉ T := by
  obtain ⟨Q, hQ, hQT⟩ : ∃ Q ∈ gmsDelta L T, Q ≠ T ⊓ centralizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    have hsub : gmsDelta L T ⊆ {T ⊓ centralizer (L : Set G)} := fun Q hQ => hcon Q hQ
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, hS.lemma313.card_eq] at h1
    have := hS.facts.four_le
    omega
  obtain ⟨r, hr, hrQ⟩ := hS.isR.exists_conj_eq hS.facts hS.sec3 hS.trans hQ
  refine ⟨r, hr, fun hrT => hQT ?_⟩
  rw [← hrQ, (rightConjugate_eq_self_iff _ _).mpr]
  exact inv_mem (le_normalizer_of_conj_mem (fun _ ht _ hp => hS.sec3.conj_mem_T₀ ht hp) hrT)

theorem exists_mem_isR₂_not_mem_gmsA
    (hR₂ : IsR₂ L T R R₂ d) : ∃ r ∈ R₂, r ∉ gmsA L T := by
  obtain ⟨z, hz, hzT⟩ := hS.exists_mem_R_not_mem_T
  have hz' : z ∈ R₂ ⊔ T := by rw [sup_comm, hR₂.sup_eq]; exact hz
  obtain ⟨r, hr, t, ht, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hR₂.le_R.trans hS.le_normalizer_T) hz'
  exact ⟨r, hr, fun hrA => hzT (mul_mem (gmsA_le_T hrA) ht)⟩

theorem exists_commutator_eq
    (hR₂ : IsR₂ L T R R₂ d) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1)
    {b : G} (hb : b ∈ gmsA L T) : ∃ r ∈ R₂, r * t * r⁻¹ * t⁻¹ = b := by
  by_cases hb1 : b = 1
  · exact ⟨1, one_mem _, by rw [hb1]; group⟩
  obtain ⟨r₀, hr₀, hr₀A⟩ := hS.exists_mem_isR₂_not_mem_gmsA hR₂
  have hb₀ : r₀ * t * r₀⁻¹ * t⁻¹ ∈ gmsA L T :=
    conj_mul_inv_mem (hS.isR.le_gmsTrans (hR₂.le_R hr₀)) (mem_sup_right ht)
  have hb₀1 : r₀ * t * r₀⁻¹ * t⁻¹ ≠ 1 := fun h =>
    hr₀A ((hS.commutator_eq_one_iff hR₂ ht ht1 hr₀).mp h)
  obtain ⟨k, hk⟩ := hS.exists_pow_conj_eq_gmsA hb₀ hb hb₀1 hb1
  refine ⟨(d ^ k)⁻¹ * r₀ * d ^ k, ?_, by rw [hS.commutator_conj_pow ht k r₀, hk]⟩
  have := (mem_normalizer_iff.mp (inv_mem (pow_mem hR₂.mem_normalizer k)) r₀).mp hr₀
  simpa using this

theorem card_isR₂
    (hR₂ : IsR₂ L T R R₂ d) :
    Nat.card R₂ = 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
  obtain ⟨hA₁c, -, -⟩ := hS.facts.sylow hS.sec3
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS.sec3.T₀_ne_bot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hmem : ∀ r : R₂, (r : G) * t * (r : G)⁻¹ * t⁻¹ ∈ gmsA L T := fun r =>
    conj_mul_inv_mem (hS.isR.le_gmsTrans (hR₂.le_R r.2)) (mem_sup_right ht)
  let f : R₂ →* gmsA L T :=
    { toFun := fun r => ⟨_, hmem r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun r r' => Subtype.ext (by
        simp only [coe_mul]
        exact hS.commutator_mul ht (hR₂.le_R r.2) (hR₂.le_R r'.2)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨r, hr, hrb⟩ := hS.exists_commutator_eq hR₂ ht ht1' hb
    exact ⟨⟨r, hr⟩, Subtype.ext hrb⟩
  have hker : f.ker = (gmsA L T).subgroupOf R₂ := by
    ext r
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hS.commutator_eq_one_iff hR₂ ht ht1' r.2]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe hR₂.gmsA_le).toEquiv, hA₁c] at h1
  exact h1

theorem card_R
    (hR₂ : IsR₂ L T R R₂ d) : Nat.card R = 2 ^ (2 * a + 1) * Nat.card T := by
  obtain ⟨hA₁c, -, -⟩ := hS.facts.sylow hS.sec3
  have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
    (hR₂.le_R.trans hS.le_normalizer_T)
  rw [hR₂.sup_eq, hR₂.inf_eq, hA₁c, hS.card_isR₂ hR₂] at h1
  have hq : 0 < 2 ^ (2 * a + 1) := by positivity
  nlinarith [h1]

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
