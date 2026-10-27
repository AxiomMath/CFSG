module

public import CFSG.Sporadic.Fi23.InvCover

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Fischer

@[expose] def InStar2 (x : J) : Prop :=
  ∃ y ∈ LocalClass D23 d, x = d * y

theorem inStar2_iff {x : J} : InStar2 x ↔ d * x ∈ LocalClass D23 d := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, d_sq, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, d_sq, one_mul]⟩

theorem star_mul_mem_star2 {x : J} (hx : x ∈ LocalClass D23 d) : InStar2 (d * x) :=
  ⟨x, hx, rfl⟩

theorem d_mul_star2_mem_star {x : J} (hx : InStar2 x) : d * x ∈ LocalClass D23 d :=
  inStar2_iff.1 hx

theorem mul_self_of_mem_star {x : J} (hx : x ∈ LocalClass D23 d) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [orderOf_of_isConj hx.1, sq] at h
  exact h

theorem star_comm_d {x : J} (hx : x ∈ LocalClass D23 d) : x * d = d * x := hx.2.2

theorem not_mem_D23_mul_pair
    {x y : J} (hx : x ∈ LocalClass D23 d)
    (hy : y ∈ LocalClass D23 x) : x * y ∉ D23 := fun h =>
  not_isConj_d_d_mul_d1 (h.trans (isConj_d_mul_d1_of_mem hx.1 hy).symm)

theorem not_mem_D23_mul_triple
    {x y : J}
    (hx : x ∈ LocalClass D23 d) (hy : y ∈ LocalClass D23 d) (hyx : y ∈ LocalClass D23 x) :
    d * x * y ∉ D23 := fun h =>
  not_isConj_d_t2 (h.trans (isConj_t2_of_mem (IsConj.refl d) hx hy hyx).symm)

theorem star_ne_d_mul_star
    {x y : J} (hx : x ∈ LocalClass D23 d)
    (hy : y ∈ LocalClass D23 x) : y ≠ d * x := by
  intro h
  have hxy : x * y = d := by
    rw [h, ← mul_assoc, star_comm_d hx, mul_assoc, mul_self_of_mem_star hx, mul_one]
  exact not_mem_D23_mul_pair hx hy (hxy ▸ IsConj.refl d)

theorem star_conj_exists
    {x y : J} (hx : x ∈ LocalClass D23 d) (hy : y ∈ LocalClass D23 d) :
    ∃ c : J, c * d = d * c ∧ c * x * c⁻¹ = y := by
  obtain ⟨c, hc⟩ := star_transitive ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨c, mem_Cd.1 c.2, ?_⟩
  have := congrArg Subtype.val hc
  rwa [starAction_val] at this

theorem c39_mem_star : c39 ∈ LocalClass D23 d := by
  refine ⟨(isConj_d_iff _).2 ⟨⟨39, by norm_num⟩, rfl⟩, fun h => ?_, c39_commute_d⟩
  have h' : conjPt 39 = conjPt 0 := by rw [conjPt_zero]; exact h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem c39_mem_star_d1 : c39 ∈ LocalClass D23 d1 := by
  refine ⟨(isConj_d_iff _).2 ⟨⟨39, by norm_num⟩, rfl⟩, fun h => ?_, c39_commute_d1⟩
  have h' : conjPt 39 = conjPt 1 := h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem exists_star_pair :
    ∃ x y : J, x ∈ LocalClass D23 d ∧ y ∈ LocalClass D23 d ∧ y ∈ LocalClass D23 x :=
  ⟨d1, c39, d1_mem_localClass, c39_mem_star, c39_mem_star_d1⟩

theorem nat_card_star : Nat.card (LocalClass D23 d) = 3510 := by
  rw [Nat.card_congr ptE.symm]
  simp

@[expose] noncomputable def twist (ε : Bool) (z : J) : J := bif ε then d * z else z

@[expose] noncomputable def starSet (ε : Bool) : Set J :=
  twist ε '' LocalClass D23 d

theorem mem_starSet_false {y : J} : y ∈ starSet false ↔ y ∈ LocalClass D23 d :=
  ⟨fun ⟨_, hz, e⟩ => e ▸ hz, fun h => ⟨y, h, rfl⟩⟩

theorem mem_starSet_true {y : J} : y ∈ starSet true ↔ InStar2 y :=
  ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

theorem twist_injective (ε : Bool) : Function.Injective (twist ε) := by
  cases ε
  · exact fun a b h => h
  · intro a b h
    exact mul_left_cancel h

theorem twist_conj (ε : Bool) {c z : J} (hc : c * d = d * c) :
    c * twist ε z * c⁻¹ = twist ε (c * z * c⁻¹) := by
  cases ε
  · rfl
  · show c * (d * z) * c⁻¹ = d * (c * z * c⁻¹)
    calc c * (d * z) * c⁻¹ = (c * d) * z * c⁻¹ := by group
      _ = (d * c) * z * c⁻¹ := by rw [hc]
      _ = d * (c * z * c⁻¹) := by group

theorem star_conj_invariant {c z : J} (hc : c * d = d * c) (hz : z ∈ LocalClass D23 d) :
    c * z * c⁻¹ ∈ LocalClass D23 d := by
  have hc' : c⁻¹ * d = d * c⁻¹ := by
    calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hc]
      _ = d * c⁻¹ := by group
  refine ⟨conj_mem_D23 c z hz.1, fun h => hz.2.1 ?_, ?_⟩
  · calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = c⁻¹ * d * c := by rw [h]
      _ = d * c⁻¹ * c := by rw [hc']
      _ = d := by group
  · calc c * z * c⁻¹ * d = c * z * (c⁻¹ * d) := by group
      _ = c * z * (d * c⁻¹) := by rw [hc']
      _ = c * (z * d) * c⁻¹ := by group
      _ = c * (d * z) * c⁻¹ := by rw [hz.2.2]
      _ = (c * d) * z * c⁻¹ := by group
      _ = (d * c) * z * c⁻¹ := by rw [hc]
      _ = d * (c * z * c⁻¹) := by group

theorem starSet_conj {ε : Bool} {c y : J} (hc : c * d = d * c) (hy : y ∈ starSet ε) :
    c * y * c⁻¹ ∈ starSet ε := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨c * z * c⁻¹, star_conj_invariant hc hz, (twist_conj ε hc).symm⟩

theorem starSet_trans {ε : Bool}
    {y y' : J} (hy : y ∈ starSet ε) (hy' : y' ∈ starSet ε) :
    ∃ c : J, c * d = d * c ∧ c * y * c⁻¹ = y' := by
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨z', hz', rfl⟩ := hy'
  obtain ⟨c, hc, hcz⟩ := star_conj_exists hz hz'
  exact ⟨c, hc, by rw [twist_conj ε hc, hcz]⟩

theorem ncard_starSet (ε : Bool) : (starSet ε).ncard = 3510 := by
  rw [starSet, Set.ncard_image_of_injective _ (twist_injective ε),
    ← Nat.card_coe_set_eq, nat_card_star]

theorem starSet_comm_d {ε : Bool} {y : J} (hy : y ∈ starSet ε) : y * d = d * y := by
  obtain ⟨z, hz, rfl⟩ := hy
  cases ε
  · exact hz.2.2
  · show d * z * d = d * (d * z)
    rw [mul_assoc, hz.2.2]

theorem twist_twist (ε : Bool) (z : J) : twist ε (twist ε z) = z := by
  cases ε
  · rfl
  · show d * (d * z) = z
    rw [← mul_assoc, d_sq, one_mul]

theorem twist_mul_twist (ε : Bool) {a b : J} (ha : a * d = d * a) :
    twist ε a * twist ε b = a * b := by
  cases ε
  · rfl
  · show d * a * (d * b) = a * b
    calc d * a * (d * b) = d * (a * d) * b := by group
      _ = d * (d * a) * b := by rw [ha]
      _ = (d * d) * a * b := by group
      _ = a * b := by rw [d_sq, one_mul]

theorem twist_mul_three (ε : Bool) {a b : J} (ha : a * d = d * a) (hb : b * d = d * b) :
    twist ε a * twist ε b * twist ε a = twist ε (a * b * a) := by
  cases ε
  · rfl
  · show d * a * (d * b) * (d * a) = d * (a * b * a)
    calc d * a * (d * b) * (d * a) = d * (a * d) * b * (d * a) := by group
      _ = d * (d * a) * b * (d * a) := by rw [ha]
      _ = (d * d) * a * b * (d * a) := by group
      _ = a * b * (d * a) := by rw [d_sq, one_mul]
      _ = a * (b * d) * a := by group
      _ = a * (d * b) * a := by rw [hb]
      _ = (a * d) * b * a := by group
      _ = (d * a) * b * a := by rw [ha]
      _ = d * (a * b * a) := by group

theorem starSet_mul_two {ε : Bool} {y₁ y₂ : J} (h₁ : y₁ ∈ starSet ε) (h₂ : y₂ ∈ starSet ε) :
    ∃ z₁ ∈ LocalClass D23 d, ∃ z₂ ∈ LocalClass D23 d, y₁ * y₂ = z₁ * z₂ := by
  obtain ⟨z₁, hz₁, rfl⟩ := h₁
  obtain ⟨z₂, hz₂, rfl⟩ := h₂
  exact ⟨z₁, hz₁, z₂, hz₂, twist_mul_twist ε hz₁.2.2⟩

end CFSG.EvenSporadicStandard.TwoFi22
