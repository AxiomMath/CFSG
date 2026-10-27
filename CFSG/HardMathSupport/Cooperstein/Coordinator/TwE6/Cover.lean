module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwE6
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

theorem comm_mul_central {G : Type*} [Group G] (a b : G) {z w : G} (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  have hzc : ∀ g, z * g * z⁻¹ = g := fun g => by
    rw [← hz' g, mul_assoc, mul_inv_cancel, mul_one]
  have hwc : ∀ g, w * g * w⁻¹ = g := fun g => by
    rw [← hw' g, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * (b * w) * a⁻¹ * (b * w)⁻¹ := by rw [hzc]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hwc]


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem exists_cover_hom {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    ∃ φ : ↥(TwistedE6.fixedGroup K σ) →* L, Function.Surjective φ ∧
      ∀ x, e (QuotientGroup.mk (φ x)) = coverHom hf hK σ hσ x := by
  classical
  have : Finite ↥(TwistedE6.fixedGroup K σ) := finite_fixedGroup σ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := coverHom hf hK σ hσ with hπ
  let q : L →* ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  let E : Subgroup (↥(TwistedE6.fixedGroup K σ) × L) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst _ _)) (q.comp (MonoidHom.snd _ _))
  let πE : E →* ↥(TwistedE6.fixedGroup K σ) := (MonoidHom.fst _ _).comp E.subtype
  have hmemE : ∀ p : ↥(TwistedE6.fixedGroup K σ) × L, p ∈ E ↔ π p.1 = q p.2 := fun p => Iff.rfl
  have hπE : Function.Surjective πE := by
    intro x
    obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L)))
      (π x)
    exact ⟨⟨(x, l), (hmemE _).2 hl.symm⟩, rfl⟩
  have hker : ∀ p : E, p ∈ πE.ker ↔ p.1.1 = 1 := fun p => Iff.rfl
  have hkerZ : ∀ p : E, p ∈ πE.ker → p.1.2 ∈ Subgroup.center L := by
    intro p hp
    have h1 : q p.1.2 = 1 := by
      rw [← (hmemE p.1).1 p.2, (hker p).1 hp, map_one]
    have h2 : (QuotientGroup.mk p.1.2 : L ⧸ Subgroup.center L) = 1 := by
      have : e (QuotientGroup.mk p.1.2) = e 1 := by rw [map_one]; exact h1
      exact e.injective this
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hcen : πE.ker ≤ Subgroup.center E := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro r
    have hz := Subgroup.mem_center_iff.1 (hkerZ p hp) r.1.2
    apply Subtype.ext
    apply Prod.ext
    · show r.1.1 * p.1.1 = p.1.1 * r.1.1
      rw [(hker p).1 hp, mul_one, one_mul]
    · exact hz
  have hcard : Nat.card πE.ker = Nat.card (Subgroup.center L) := by
    refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨p.1.1.2, hkerZ p.1 p.2⟩) ⟨?_, ?_⟩)
    · intro p p' h
      have h2 : p.1.1.2 = p'.1.1.2 := congrArg Subtype.val h
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · rw [(hker p.1).1 p.2, (hker p'.1).1 p'.2]
      · exact h2
    · intro z
      refine ⟨⟨⟨(1, (z : L)), ?_⟩, ?_⟩, rfl⟩
      · rw [hmemE]
        show π 1 = q z
        rw [map_one]
        have : (QuotientGroup.mk (z : L) : L ⧸ Subgroup.center L) = 1 :=
          (QuotientGroup.eq_one_iff _).2 z.2
        show _ = e (QuotientGroup.mk (z : L))
        rw [this, map_one]
      · exact rfl
  have hcop : Nat.Coprime 2 (Nat.card πE.ker) := by
    rw [hcard]
    exact (Nat.coprime_two_left).2 hodd
  have : Finite E := inferInstance
  obtain ⟨s, hs⟩ := CentralExt.TwistedE6Closed.twistedE6_exists_section_of_coprime
    (sigma_sigma_eq hK σ hσ) hπE hcen hcop
  let φ : ↥(TwistedE6.fixedGroup K σ) →* L := (MonoidHom.snd _ _).comp (E.subtype.comp s)
  have hφ : ∀ x, π x = q (φ x) := fun x => by
    have h1 := (hmemE (s x : ↥(TwistedE6.fixedGroup K σ) × L)).1 (s x).2
    have h2 : ((s x : E) : ↥(TwistedE6.fixedGroup K σ) × L).1 = x := hs x
    rw [h2] at h1
    exact h1
  refine ⟨φ, ?_, fun x => (hφ x).symm⟩
  have hL : ∀ l : L, ∃ x, ∃ z ∈ Subgroup.center L, l = φ x * z := by
    intro l
    obtain ⟨x, hx⟩ := (isCentralCover_coverHom hf hK σ hσ).surj (q l)
    refine ⟨x, (φ x)⁻¹ * l, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 : e (QuotientGroup.mk (φ x)) = e (QuotientGroup.mk l) := by
      have := hφ x
      rw [hx] at this
      exact this.symm
    have h2 : (QuotientGroup.mk (φ x) : L ⧸ Subgroup.center L) = QuotientGroup.mk l :=
      e.injective h1
    rw [h2]; group
  intro l
  have hperf' : commutator L = ⊤ := hperf.commutator_eq_top
  have hle : commutator L ≤ φ.range := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    obtain ⟨x, z, hz, rfl⟩ := hL a
    obtain ⟨y, w, hw, rfl⟩ := hL b
    have : ⁅φ x * z, φ y * w⁆ = ⁅φ x, φ y⁆ := comm_mul_central _ _ hz hw
    rw [this, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have := hle (hperf' ▸ Subgroup.mem_top l)
  exact this

include hf hK hσ in
theorem card_ker_coverHom :
    Nat.card (coverHom hf hK σ hσ).ker = Nat.gcd 3 (2 ^ f + 1) := by
  rw [ker_coverHom hf hK σ hσ]
  exact (CentralExt.TwistedE6Closed.card_center_fixedGroup hK hσ).1

theorem ordTwistedE6_mul_gcd_le (q : ℕ) :
    CFSG.Open.ordTwistedE6 q * Nat.gcd 3 (q + 1) ≤
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) :=
  Nat.div_mul_le_self _ _

theorem prod_twistedE6_lt {q : ℕ} (hq : 2 ≤ q) :
    q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) <
      q ^ 78 := by
  have h12 : q ^ 12 - 1 ≤ q ^ 12 := Nat.sub_le _ _
  have h8 : q ^ 8 - 1 ≤ q ^ 8 := Nat.sub_le _ _
  have h6 : q ^ 6 - 1 ≤ q ^ 6 := Nat.sub_le _ _
  have h59 : (q ^ 9 + 1) * (q ^ 5 + 1) ≤ q ^ 14 + 2 * q ^ 9 := by
    have h5 : q ^ 5 + 1 ≤ q ^ 9 := by
      have : q ^ 5 * 2 ≤ q ^ 5 * q ^ 4 := Nat.mul_le_mul_left _ (by
        calc 2 ≤ q := hq
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num))
      have h1 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
      calc q ^ 5 + 1 ≤ q ^ 5 * 2 := by omega
        _ ≤ q ^ 5 * q ^ 4 := this
        _ = q ^ 9 := by rw [← pow_add]
    nlinarith [Nat.one_le_pow 9 q (by omega)]
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have key : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) ≤ (q ^ 36 * q ^ 12 * q ^ 8 * q ^ 6) * (q ^ 14 + 2 * q ^ 9) * (q ^ 2 - 1) := by
    calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
        = (q ^ 36 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) * ((q ^ 9 + 1) * (q ^ 5 + 1)) *
          (q ^ 2 - 1) := by ring
      _ ≤ (q ^ 36 * q ^ 12 * q ^ 8 * q ^ 6) * (q ^ 14 + 2 * q ^ 9) * (q ^ 2 - 1) := by
        gcongr
  refine lt_of_le_of_lt key ?_
  have e : q ^ 78 = (q ^ 36 * q ^ 12 * q ^ 8 * q ^ 6) * q ^ 16 := by
    simp only [← pow_add]
  rw [e, mul_assoc]
  refine (Nat.mul_lt_mul_left (by positivity)).2 ?_
  zify [hq2]
  have hq9 : (8 : ℤ) * (q : ℤ) ^ 11 ≤ (q : ℤ) ^ 14 := by
    have : (q : ℤ) ^ 14 = (q : ℤ) ^ 11 * (q : ℤ) ^ 3 := by ring
    rw [this]
    have h3 : (8 : ℤ) ≤ (q : ℤ) ^ 3 := by
      have : (2 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith [this]
    have : (0 : ℤ) ≤ (q : ℤ) ^ 11 := by positivity
    nlinarith
  have h9 : (0 : ℤ) < (q : ℤ) ^ 9 := by positivity
  nlinarith [h9, hq9, show (q : ℤ) ^ 11 = (q : ℤ) ^ 9 * (q : ℤ) ^ 2 by ring]

include hf hK hσ in
theorem card_fixedGroup_lt : Nat.card ↥(TwistedE6.fixedGroup K σ) < (2 ^ f) ^ 78 := by
  have : Finite ↥(TwistedE6.fixedGroup K σ) := finite_fixedGroup σ
  have hsurj : Function.Surjective (coverHom hf hK σ hσ) :=
    (isCentralCover_coverHom hf hK σ hσ).surj
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [card_ker_coverHom hf hK σ hσ,
    CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two hf hK σ hσ] at h1
  rw [← h1]
  refine lt_of_le_of_lt ?_ (prod_twistedE6_lt (q := 2 ^ f) ?_)
  · rw [mul_comm]
    exact ordTwistedE6_mul_gcd_le (2 ^ f)
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
