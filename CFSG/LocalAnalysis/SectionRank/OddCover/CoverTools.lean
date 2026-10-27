module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.SectionRank.OddCover

open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_mem_center {a b c : G} (h : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hb : b * c * b⁻¹ = ⁅b, c⁆ * c := by rw [commutatorElement_def]; group
  have hcomm : a * ⁅b, c⁆ = ⁅b, c⁆ * a := Subgroup.mem_center_iff.1 h a
  calc ⁅a * b, c⁆ = a * (b * c * b⁻¹) * a⁻¹ * c⁻¹ := by rw [commutatorElement_def]; group
    _ = (a * ⁅b, c⁆) * c * a⁻¹ * c⁻¹ := by rw [hb]; group
    _ = ⁅b, c⁆ * ⁅a, c⁆ := by rw [hcomm, commutatorElement_def]; group
    _ = ⁅a, c⁆ * ⁅b, c⁆ := (Subgroup.mem_center_iff.1 h _).symm

theorem commutatorElement_mul_right_of_mem_center {a b c : G} (h : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hc : ⁅c, a⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ h
  have := commutatorElement_mul_left_of_mem_center (a := b) hc
  calc ⁅a, b * c⁆ = ⁅b * c, a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (⁅b, a⁆ * ⁅c, a⁆)⁻¹ := by rw [this]
    _ = ⁅a, c⁆ * ⁅a, b⁆ := by rw [mul_inv_rev, commutatorElement_inv, commutatorElement_inv]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := (Subgroup.mem_center_iff.1 h _).symm

theorem commutatorElement_inv_inv_of_mem_center {a b : G} (h : ⁅a, b⁆ ∈ Subgroup.center G) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have hab : a * b = ⁅a, b⁆ * b * a := by rw [commutatorElement_def]; group
  have hz := Subgroup.mem_center_iff.1 h
  calc ⁅a⁻¹, b⁻¹⁆ = a⁻¹ * b⁻¹ * (a * b) := by rw [commutatorElement_def]; group
    _ = a⁻¹ * b⁻¹ * (⁅a, b⁆ * b * a) := by rw [hab]
    _ = a⁻¹ * (b⁻¹ * ⁅a, b⁆) * b * a := by group
    _ = a⁻¹ * (⁅a, b⁆ * b⁻¹) * b * a := by rw [hz b⁻¹]
    _ = (a⁻¹ * ⁅a, b⁆) * a := by group
    _ = (⁅a, b⁆ * a⁻¹) * a := by rw [hz a⁻¹]
    _ = ⁅a, b⁆ := by group

theorem sq_eq_one_of_conj_eq_inv {z s : G} (hz : z ∈ Subgroup.center G)
    (hs : s * z * s⁻¹ = z⁻¹) : z ^ 2 = 1 := by
  have h1 : s * z * s⁻¹ = z := by rw [Subgroup.mem_center_iff.1 hz s]; group
  rw [h1] at hs
  rw [sq]
  nth_rewrite 1 [hs]
  exact inv_mul_cancel z

theorem eq_one_of_sq_eq_one_of_odd {z : G} (hz : z ^ 2 = 1) (hodd : Odd (orderOf z)) :
    z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz
  have h2 : orderOf z ∣ 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · rw [h]
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)

theorem odd_orderOf_of_mem {H : Subgroup G} [Finite H] (hH : Odd (Nat.card H)) {z : G}
    (hz : z ∈ H) : Odd (orderOf z) := by
  have h : orderOf (⟨z, hz⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hH h

end Commutators

section Sylow

variable {E J : Type*} [Group E] [Group J]

theorem sylow_kernel_eq_bot_of_commute [Finite E] [Group.IsPerfect E] {p : ℕ} [Fact p.Prime]
    (π : E →* J) (hC : π.ker ≤ Subgroup.center E) (P : Sylow p E)
    (hcomm : ∀ x ∈ (P : Subgroup E), ∀ y ∈ (P : Subgroup E), x * y = y * x)
    (Cp : Sylow p π.ker) : (Cp : Subgroup π.ker) = ⊥ := by
  have hle := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction_le_derived π hC Cp P
  have hPc : IsMulCommutative (P : Subgroup E) :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  rw [commutator_eq_bot] at hle
  rw [eq_bot_iff]
  intro c hc
  have hcP : (c : E) ∈ (P : Subgroup E) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P
      ((Cp : Subgroup π.ker).map π.ker.subtype)
      ((Subgroup.map_subtype_le (Cp : Subgroup π.ker)).trans hC)
      (Cp.isPGroup'.map π.ker.subtype) (Subgroup.mem_map.2 ⟨c, hc, rfl⟩)
  have hker : (⟨(c : E), hcP⟩ : (P : Subgroup E)) ∈ (π.subgroupMap (P : Subgroup E)).ker :=
    Subtype.ext c.2
  have h1 := Subgroup.mem_bot.1 (hle hker)
  have h2 : (c : E) = 1 := congrArg Subtype.val h1
  exact Subgroup.mem_bot.2 (Subtype.ext h2)

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_forall_sylow_eq_bot (H : Subgroup G)
    (h : ∀ r : ℕ, r.Prime → ∀ [Fact r.Prime] (P : Sylow r H), (P : Subgroup H) = ⊥) : H = ⊥ := by
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r H))
  exact Sylow.ne_bot_of_dvd_card P hrd (h r hr P)

theorem isPGroup_of_forall_sylow_eq_bot {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (h : ∀ r : ℕ, r.Prime → r ≠ p → ∀ [Fact r.Prime] (P : Sylow r H), (P : Subgroup H) = ⊥) :
    IsPGroup p H := by
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card H → d = p := by
    intro d hd hdvd
    by_contra hdp
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow d H))
    exact Sylow.ne_bot_of_dvd_card P hdvd (h d hd hdp P)
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime)

end Sylow

section Lifts

variable {E J : Type*} [Group E] [Group J] {π : E →* J}

theorem eq_of_sq_eq_of_mem {C : Subgroup E} [Finite C] (hodd : Odd (Nat.card C))
    (hCZ : C ≤ Subgroup.center E) {c d : E} (hc : c ∈ C) (hd : d ∈ C) (h : c ^ 2 = d ^ 2) :
    c = d := by
  have hcd : c * d⁻¹ ∈ C := C.mul_mem hc (C.inv_mem hd)
  have hcomm : Commute c d⁻¹ := Subgroup.mem_center_iff.1 (hCZ (C.inv_mem hd)) c
  have h2 : (c * d⁻¹) ^ 2 = 1 := by
    rw [hcomm.mul_pow, h, inv_pow, mul_inv_cancel]
  have := eq_one_of_sq_eq_one_of_odd h2 (odd_orderOf_of_mem hodd hcd)
  exact mul_inv_eq_one.1 this

theorem exists_sq_eq_of_mem {C : Subgroup E} [Finite C] (hodd : Odd (Nat.card C)) {c : E}
    (hc : c ∈ C) : ∃ d ∈ C, d ^ 2 = c := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨c ^ (k + 1), C.pow_mem hc _, ?_⟩
  have h1 : c ^ Nat.card C = 1 := by
    have := pow_card_eq_one' (G := C) (x := ⟨c, hc⟩)
    exact congrArg Subtype.val this
  rw [← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, ← hk, pow_succ, h1, one_mul]

theorem existsUnique_involution_lift [Finite π.ker] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) {s : J} (hs : s ^ 2 = 1) :
    ∃! t : E, t ^ 2 = 1 ∧ π t = s := by
  obtain ⟨e, he⟩ := hπ s
  have he2 : e ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, he, hs]
  obtain ⟨d, hd, hd2⟩ := exists_sq_eq_of_mem hodd he2
  have hdc : ∀ g : E, Commute d g := fun g => (Subgroup.mem_center_iff.1 (hC hd) g).symm
  have hed2 : (e * d⁻¹) ^ 2 = 1 := by
    rw [((hdc e).symm.inv_right).mul_pow, inv_pow, hd2, mul_inv_cancel]
  refine ⟨e * d⁻¹, ⟨hed2, ?_⟩, ?_⟩
  · rw [map_mul, map_inv, he, hd, inv_one, mul_one]
  · rintro t ⟨ht2, ht⟩
    have hc : t * (e * d⁻¹)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, ht, he, hd, inv_one, mul_one,
        mul_inv_cancel]
    obtain ⟨c, hc', rfl⟩ : ∃ c ∈ π.ker, t = c * (e * d⁻¹) :=
      ⟨_, hc, by group⟩
    have hcc : ∀ g : E, Commute c g := fun g => (Subgroup.mem_center_iff.1 (hC hc') g).symm
    have h2 : c ^ 2 = 1 := by
      rw [(hcc (e * d⁻¹)).mul_pow, hed2, mul_one] at ht2
      exact ht2
    rw [eq_one_of_sq_eq_one_of_odd h2 (odd_orderOf_of_mem hodd hc'), one_mul]

theorem existsUnique_inverted_lift [Finite π.ker] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) (t : E) {x : J}
    (hx : π t * x * (π t)⁻¹ = x⁻¹) :
    ∃! y : E, π y = x ∧ t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨e, he⟩ := hπ x
  set c := e * (t * e * t⁻¹) with hcdef
  have hc : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, he, hx, mul_inv_cancel]
  obtain ⟨d, hd, hd2⟩ := exists_sq_eq_of_mem hodd hc
  have hdc : ∀ g : E, Commute d g := fun g => (Subgroup.mem_center_iff.1 (hC hd) g).symm
  have hte : t * e * t⁻¹ = e⁻¹ * c := by rw [hcdef]; group
  have htd : t * d⁻¹ * t⁻¹ = d⁻¹ := by
    rw [← ((hdc t).inv_left).eq]; group
  have hed : t * (e * d⁻¹) * t⁻¹ = (e * d⁻¹)⁻¹ := by
    calc t * (e * d⁻¹) * t⁻¹ = (t * e * t⁻¹) * (t * d⁻¹ * t⁻¹) := by group
      _ = e⁻¹ * c * d⁻¹ := by rw [hte, htd]
      _ = e⁻¹ * (d * d) * d⁻¹ := by rw [← hd2, sq]
      _ = e⁻¹ * d := by group
      _ = d * e⁻¹ := ((hdc e⁻¹)).eq.symm
      _ = (e * d⁻¹)⁻¹ := by group
  refine ⟨e * d⁻¹, ⟨?_, hed⟩, ?_⟩
  · rw [map_mul, map_inv, he, hd, inv_one, mul_one]
  · rintro y ⟨hy, hyt⟩
    have hk : y * (e * d⁻¹)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, hy, he, hd, inv_one, mul_one,
        mul_inv_cancel]
    obtain ⟨k, hk', rfl⟩ : ∃ k ∈ π.ker, y = k * (e * d⁻¹) := ⟨_, hk, by group⟩
    have hkc : ∀ g : E, Commute k g := fun g => (Subgroup.mem_center_iff.1 (hC hk') g).symm
    have htk : t * k * t⁻¹ = k := by rw [← (hkc t).eq]; group
    have h1 : t * (k * (e * d⁻¹)) * t⁻¹ = k * (e * d⁻¹)⁻¹ := by
      calc t * (k * (e * d⁻¹)) * t⁻¹ = (t * k * t⁻¹) * (t * (e * d⁻¹) * t⁻¹) := by group
        _ = k * (e * d⁻¹)⁻¹ := by rw [htk, hed]
    rw [h1] at hyt
    have h2 : k ^ 2 = 1 := by
      have h3 : k * (e * d⁻¹)⁻¹ = k⁻¹ * (e * d⁻¹)⁻¹ := by
        rw [hyt, mul_inv_rev (a := k), ← ((hkc _).inv_left).eq]
      have h4 : k = k⁻¹ := mul_right_cancel h3
      rw [sq]
      nth_rewrite 2 [h4]
      exact mul_inv_cancel k
    rw [eq_one_of_sq_eq_one_of_odd h2 (odd_orderOf_of_mem hodd hk'), one_mul]

end Lifts

end CFSG.SectionRank.OddCover
