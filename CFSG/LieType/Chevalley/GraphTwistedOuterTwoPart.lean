module

public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.LinearArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem ordProj_two_of_odd {n : ℕ} (hn : Odd n) : ordProj[2] n = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => by rcases hn with ⟨k, rfl⟩; omega),
    pow_zero]

theorem ordProj_two_two_mul {n : ℕ} (hn : n ≠ 0) : ordProj[2] (2 * n) = 2 * ordProj[2] n := by
  rw [Nat.ordProj_mul 2 two_ne_zero hn, Nat.Prime.factorization_self Nat.prime_two, pow_one]

theorem ordProj_two_three_mul {n : ℕ} (hn : n ≠ 0) : ordProj[2] (3 * n) = ordProj[2] n := by
  rw [Nat.ordProj_mul 2 (by norm_num) hn, ordProj_two_of_odd (by decide), one_mul]

variable {K : Type} [Field K] [Finite K]

theorem ordProj_two_card_outer_twistedE6
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ordProj[2] (Nat.card (Outer (twistedE6RootGroup K σ))) = 2 * ordProj[2] f := by
  classical
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hcardA, -⟩ := card_ringAut_and_isCyclic hp K hK'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, hsurj, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  have hle : inner (twistedE6RootGroup K σ) ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  set Φ := QuotientGroup.lift (inner (twistedE6RootGroup K σ)) Θ hle
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hle α⟩
  have hcube' : ∀ x ∈ Φ.ker, x ^ 3 = 1 := by
    intro x hx
    rw [QuotientGroup.ker_lift, hker] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  have : Finite (Outer (twistedE6RootGroup K σ)) := by
    have : Finite (MulAut (twistedE6RootGroup K σ)) := MulEquiv.finite_left
    infer_instance
  have hodd : Odd (Nat.card Φ.ker) := by
    rw [Nat.odd_iff]
    by_contra h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Φ.ker) 2 (by omega)
    have h3 : x ^ 3 = 1 := Subtype.ext (by simpa using hcube' x x.2)
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hx] at h4
    omega
  have hcard : Nat.card (Outer (twistedE6RootGroup K σ)) = Nat.card Φ.ker * (2 * f) := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj,
      Subgroup.card_top, hcardA]
  rw [hcard, Nat.ordProj_mul 2 (Nat.pos_of_ne_zero (by
      rintro h0
      rw [h0] at hodd
      exact absurd hodd (by decide))).ne' (by omega), ordProj_two_of_odd hodd, one_mul,
    ordProj_two_two_mul (by omega)]

theorem ordProj_two_card_outer_triality
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ordProj[2] (Nat.card (Outer (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) =
      ordProj[2] f := by
  classical
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  obtain ⟨Θ, hsurj, hker, hcard⟩ : ∃ Θ : MulAut C →* (K ≃+* K), Function.Surjective Θ ∧
      Θ.ker = inner C ∧ Nat.card (K ≃+* K) = 3 * f := by
    rcases eq_or_ne p 2 with rfl | hp2
    · obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcard, -⟩ :=
        even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨Θ, hsurj, hker, hcard⟩
    · obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcard, -⟩ :=
        odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
      exact ⟨Θ, hsurj, hker, hcard⟩
  have hle : inner C ≤ Θ.ker := hker.ge
  set Φ := QuotientGroup.lift (inner C) Θ hle
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hle α⟩
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  have hcardO : Nat.card (Outer C) = 3 * f := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj,
      Subgroup.card_top, hcard, hΦker, Subgroup.card_bot, one_mul]
  rw [hcardO, ordProj_two_three_mul (by omega)]

omit [Finite K] in
theorem pow_card_orbit_dvd_card_graphFixedRootGroup
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (a : Fin t.foldedTag.rank) :
    (p ^ f) ^ (t.orbit a).card ∣ Nat.card (graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨σ', hσ', -, hcardL, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  subst hσσ
  let φ : Multiplicative (orbitField t K σ'.toRingHom a) →*
      graphFixedRootGroup t K σ'.toRingHom :=
    { toFun := fun c => fixedOrbitX t K σ'.toRingHom a (Multiplicative.toAdd c)
      map_one' := Subtype.ext (by
        change ((orbitX t K σ'.toRingHom a 0 : adjointGroup t.tag K) : ModGL t.tag K) = 1
        rw [orbitX_zero]
        rfl)
      map_mul' := fun c d => Subtype.ext (by
        change ((orbitX t K σ'.toRingHom a (Multiplicative.toAdd c + Multiplicative.toAdd d) :
          adjointGroup t.tag K) : ModGL t.tag K) = _
        rw [orbitX_add]
        rfl) }
  have hφ : Function.Injective φ := fun c d h =>
    Multiplicative.toAdd.injective (fixedOrbitX_injective a h)
  rw [← hcardL a, ← Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (orbitField t K σ'.toRingHom a) ≃ _),
    Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem four_mul_ordProj_two_le_card_graphFixedRootGroup
    (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (a : Fin t.foldedTag.rank)
    (ha : (t.orbit a).card = 1) :
    4 * ordProj[2] f ≤ ordProj[2] (Nat.card (graphFixedRootGroup t K σ.toRingHom)) := by
  classical
  obtain ⟨σ', hσ', -, hcardL, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  subst hσσ
  have hL : Nat.card (orbitField t K σ'.toRingHom a) = p ^ f := by rw [hcardL a, ha, pow_one]
  have : Finite (orbitField t K σ'.toRingHom a) :=
    Nat.finite_of_card_ne_zero (by rw [hL]; exact (pow_pos hp.pos f).ne')
  obtain ⟨R, -, -, -, -, -, hrange, hle, hker, -⟩ :=
    exceptional_fixed_rank_one_central_image t K σ'.toRingHom a
  have hRle : R.range ≤ graphFixedRootGroup t K σ'.toRingHom := by
    rw [hrange]
    exact hle
  have hSL : Nat.card (SL2 (orbitField t K σ'.toRingHom a)) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [LinearFlag.card_SL_eq (n := 2) (by norm_num), hL]
    simp
  have hker2 : Nat.card R.ker ≤ 2 := by
    have key : ∀ g : R.ker, ∃ l : orbitField t K σ'.toRingHom a, (l = 1 ∨ l = -1) ∧
        ((g : SL2 (orbitField t K σ'.toRingHom a)) :
          Matrix (Fin 2) (Fin 2) (orbitField t K σ'.toRingHom a)) = l • 1 := fun g => by
      obtain ⟨l, hl, hgl⟩ := hker g g.2
      exact ⟨l, mul_self_eq_one_iff.1 (by rw [← sq]; exact hl), hgl⟩
    choose l hl hgl using key
    have hinj : Function.Injective fun g : R.ker => decide (l g = 1) := by
      intro g g' h
      have hll : l g = l g' := by
        have h' := decide_eq_decide.1 h
        rcases hl g with h1 | h1 <;> rcases hl g' with h2 | h2
        · rw [h1, h2]
        · rw [h1, h2] at h' ⊢
          exact (h'.1 rfl).symm
        · rw [h1, h2] at h' ⊢
          exact h'.2 rfl
        · rw [h1, h2]
      exact Subtype.ext (Subtype.ext (by rw [hgl, hgl, hll]))
    calc Nat.card R.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hmul : Nat.card R.ker * Nat.card R.range =
      Nat.card (SL2 (orbitField t K σ'.toRingHom a)) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hq0 : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
  have hq1 : (p ^ f) ^ 2 - 1 ≠ 0 := by
    have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  have hk0 : Nat.card R.ker ≠ 0 := fun h => by
    rw [h, zero_mul, hSL] at hmul
    exact Nat.mul_ne_zero hq0 hq1 hmul.symm
  have hr0 : Nat.card R.range ≠ 0 := fun h => by
    rw [h, mul_zero, hSL] at hmul
    exact Nat.mul_ne_zero hq0 hq1 hmul.symm
  have hqodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h8 := ((lie_order_two_adic_arithmetic).1 p f hp hp2 hf).2
  have h2part : ordProj[2] ((p ^ f) ^ 2 - 1) =
      ordProj[2] (Nat.card R.ker) * ordProj[2] (Nat.card R.range) := by
    rw [← Nat.ordProj_mul 2 hk0 hr0, hmul, hSL, Nat.ordProj_mul 2 hq0 hq1,
      ordProj_two_of_odd hqodd, one_mul]
  have hkle : ordProj[2] (Nat.card R.ker) ≤ 2 := (Nat.ordProj_le 2 hk0).trans hker2
  have hC0 : Nat.card (graphFixedRootGroup t K σ'.toRingHom) ≠ 0 := Nat.card_pos.ne'
  have hdvd := Nat.ordProj_dvd_ordProj_of_dvd hC0 (Subgroup.card_dvd_of_le hRle) 2
  have hrle := Nat.le_of_dvd (Nat.pos_of_ne_zero (by positivity)) hdvd
  have h1 : ordProj[2] (Nat.card R.ker) * ordProj[2] (Nat.card R.range) ≤
      2 * ordProj[2] (Nat.card R.range) := Nat.mul_le_mul_right _ hkle
  linarith


theorem graph_twisted_exceptional_model_outer_two_part_bound
    (T : Type) [Group T]
    (t : StatedLieTag) (p f m : ℕ) (hT : ChevalleyExceptionalModel T t p f)
    (hm : (t = .twistedE6 ∧ m = 2) ∨ (t = .trialityD4 ∧ m = 3)) :
    (t = .twistedE6 → ordProj[2] (Nat.card (Outer T)) = 2 * ordProj[2] f) ∧
    (t = .trialityD4 → ordProj[2] (Nat.card (Outer T)) = ordProj[2] f) ∧
    (p = 2 → (p ^ f) ^ m ≤ ordProj[2] (Nat.card T)) ∧
    (p ≠ 2 → 4 * ordProj[2] f ≤ ordProj[2] (Nat.card T)) ∧
    4 ≤ ordProj[2] (Nat.card T) ∧ ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) := by
  obtain ⟨⟨hp, hf, -⟩, hmod⟩ := hT
  have key : ∀ t' : TwistTag, TwistedChevalleyModel T t' (p ^ f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
        Nat.card K = (p ^ f) ^ t'.order ∧ (∀ c, σ c = c ^ (p ^ f)) ∧
        Nat.card T = Nat.card (graphFixedRootGroup t' K σ.toRingHom) ∧
        Nat.card (Outer T) = Nat.card (Outer (graphFixedRootGroup t' K σ.toRingHom)) := by
    intro t' h
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card t' hp hf h
    exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, Nat.card_congr e.toEquiv,
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv⟩
  have hf2 := ((lie_order_two_adic_arithmetic).2.2 f hf).1
  have hfpos : 1 ≤ ordProj[2] f := Nat.ordProj_pos f 2
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hmod' : TwistedChevalleyModel T .E6 (p ^ f) := hmod
    obtain ⟨K, _, _, σ, hK, hσ, hcT, hcO⟩ := key .E6 hmod'
    have ho : ordProj[2] (Nat.card (Outer T)) = 2 * ordProj[2] f := by
      rw [hcO]
      exact ordProj_two_card_outer_twistedE6 hp hf hK σ hσ
    have h2 : p = 2 → (p ^ f) ^ 2 ≤ ordProj[2] (Nat.card T) := by
      rintro rfl
      have hdvd := pow_card_orbit_dvd_card_graphFixedRootGroup .E6 hp hf hK σ hσ ⟨0, by decide⟩
      rw [show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, ← pow_mul] at hdvd
      rw [hcT, ← pow_mul]
      exact pow_le_ordProj_two Nat.card_pos.ne' hdvd
    have hodd : p ≠ 2 → 4 * ordProj[2] f ≤ ordProj[2] (Nat.card T) := by
      intro hp2
      rw [hcT]
      exact four_mul_ordProj_two_le_card_graphFixedRootGroup .E6 hp hp2 hf hK σ hσ ⟨2, by decide⟩
        (by decide)
    refine ⟨fun _ => ho, fun h => absurd h (by decide), h2, hodd, ?_⟩
    rcases eq_or_ne p 2 with rfl | hp2
    · have h := h2 rfl
      have h4 : 4 ≤ (2 ^ f) ^ 2 := by
        calc 4 = (2 ^ 1) ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hf) 2
      have hlt : 2 * ordProj[2] f < (2 ^ f) ^ 2 := by
        calc 2 * ordProj[2] f < 2 * 2 ^ f := by omega
          _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 2)
          _ = (2 ^ f) ^ 2 := (sq _).symm
      exact ⟨h4.trans h, by rw [ho]; omega⟩
    · have h := hodd hp2
      exact ⟨by omega, by rw [ho]; omega⟩
  ·
    have hmod' : TwistedChevalleyModel T .D4 (p ^ f) := hmod
    obtain ⟨K, _, _, σ, hK, hσ, hcT, hcO⟩ := key .D4 hmod'
    have ho : ordProj[2] (Nat.card (Outer T)) = ordProj[2] f := by
      rw [hcO]
      exact ordProj_two_card_outer_triality hp hf hK σ hσ
    have h2 : p = 2 → (p ^ f) ^ 3 ≤ ordProj[2] (Nat.card T) := by
      rintro rfl
      have hdvd := pow_card_orbit_dvd_card_graphFixedRootGroup .D4 hp hf hK σ hσ ⟨0, by decide⟩
      rw [show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide, ← pow_mul] at hdvd
      rw [hcT, ← pow_mul]
      exact pow_le_ordProj_two Nat.card_pos.ne' hdvd
    have hodd : p ≠ 2 → 4 * ordProj[2] f ≤ ordProj[2] (Nat.card T) := by
      intro hp2
      rw [hcT]
      exact four_mul_ordProj_two_le_card_graphFixedRootGroup .D4 hp hp2 hf hK σ hσ ⟨1, by decide⟩
        (by decide)
    refine ⟨fun h => absurd h (by decide), fun _ => ho, h2, hodd, ?_⟩
    rcases eq_or_ne p 2 with rfl | hp2
    · have h := h2 rfl
      have h4 : 4 ≤ (2 ^ f) ^ 3 := by
        calc 4 ≤ (2 ^ 1) ^ 3 := by norm_num
          _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hf) 3
      have hlt : ordProj[2] f < (2 ^ f) ^ 3 :=
        hf2.trans_le (Nat.le_self_pow (by norm_num) _)
      exact ⟨h4.trans h, by rw [ho]; omega⟩
    · have h := hodd hp2
      exact ⟨by omega, by rw [ho]; omega⟩

end CFSG.LieType.Chevalley
