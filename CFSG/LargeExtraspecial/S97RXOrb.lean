module

public import CFSG.LargeExtraspecial.S97RXAbs

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.CGT.Timmesfeld75

variable {Λ V : Type*} [Group Λ]

@[expose] noncomputable def zm2pow (t : Λ) (e : ZMod 2) : Λ := if e = 0 then 1 else t

omit [Group Λ] in
theorem zmod2_eq_zero_or_eq_one (e : ZMod 2) : e = 0 ∨ e = 1 := by
  fin_cases e
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem zm2pow_zero (t : Λ) : zm2pow t 0 = 1 := by simp [zm2pow]

@[simp] theorem zm2pow_one (t : Λ) : zm2pow t 1 = t := by simp [zm2pow]

theorem zm2pow_add {t : Λ} (ht : t * t = 1) (e e' : ZMod 2) :
    zm2pow t (e + e') = zm2pow t e * zm2pow t e' := by
  rcases zmod2_eq_zero_or_eq_one e with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one e' with rfl | rfl <;> simp [ht]
  rfl

theorem commute_zm2pow {t t' : Λ} (h : t * t' = t' * t) (e e' : ZMod 2) :
    Commute (zm2pow t e) (zm2pow t' e') := by
  rcases zmod2_eq_zero_or_eq_one e with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one e' with rfl | rfl <;> simp [Commute, SemiconjBy, h]

@[expose] noncomputable def word3 (t₁ t₂ t₃ : Λ) (e : ZMod 2 × ZMod 2 × ZMod 2) : Λ :=
  zm2pow t₁ e.1 * zm2pow t₂ e.2.1 * zm2pow t₃ e.2.2

theorem word3_add {t₁ t₂ t₃ : Λ} (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1) (h3 : t₃ * t₃ = 1)
    (h12 : t₁ * t₂ = t₂ * t₁) (h13 : t₁ * t₃ = t₃ * t₁) (h23 : t₂ * t₃ = t₃ * t₂)
    (e e' : ZMod 2 × ZMod 2 × ZMod 2) :
    word3 t₁ t₂ t₃ (e + e') = word3 t₁ t₂ t₃ e * word3 t₁ t₂ t₃ e' := by
  obtain ⟨a, b, c⟩ := e
  obtain ⟨a', b', c'⟩ := e'
  simp only [word3, Prod.mk_add_mk, zm2pow_add h1, zm2pow_add h2, zm2pow_add h3]
  have hCY : Commute (zm2pow t₃ c) (zm2pow t₁ a' * zm2pow t₂ b') :=
    ((commute_zm2pow h13 a' c).symm).mul_right ((commute_zm2pow h23 b' c).symm)
  rw [Commute.mul_mul_mul_comm hCY, Commute.mul_mul_mul_comm (commute_zm2pow h12 a' b).symm]

theorem word3_zero (t₁ t₂ t₃ : Λ) : word3 t₁ t₂ t₃ 0 = 1 := by
  simp [word3]

theorem word3_mem {T : Subgroup Λ} {t₁ t₂ t₃ : Λ} (h1 : t₁ ∈ T) (h2 : t₂ ∈ T) (h3 : t₃ ∈ T)
    (e : ZMod 2 × ZMod 2 × ZMod 2) : word3 t₁ t₂ t₃ e ∈ T := by
  have hz : ∀ (t : Λ) (e : ZMod 2), t ∈ T → zm2pow t e ∈ T := fun t e ht => by
    unfold zm2pow
    split_ifs
    · exact one_mem _
    · exact ht
  exact mul_mem (mul_mem (hz _ _ h1) (hz _ _ h2)) (hz _ _ h3)

theorem eq_of_mul_eq_one_of_sq {x y : Λ} (hx : x * x = 1) (h : x * y = 1) : y = x := by
  rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hx]

theorem word3_eq_one {t₁ t₂ t₃ : Λ} (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1)
    (h12 : t₁ * t₂ = t₂ * t₁) (n1 : t₁ ≠ 1) (n2 : t₂ ≠ 1) (n21 : t₂ ≠ t₁) (n3 : t₃ ≠ 1)
    (n31 : t₃ ≠ t₁) (n32 : t₃ ≠ t₂) (n312 : t₃ ≠ t₁ * t₂) {e : ZMod 2 × ZMod 2 × ZMod 2}
    (he : word3 t₁ t₂ t₃ e = 1) : e = 0 := by
  obtain ⟨a, b, c⟩ := e
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl <;>
        simp only [word3, zm2pow_zero, zm2pow_one, one_mul, mul_one] at he
  · rfl
  · exact absurd he n3
  · exact absurd he n2
  · exact absurd (eq_of_mul_eq_one_of_sq h2 he) n32
  · exact absurd he n1
  · exact absurd (eq_of_mul_eq_one_of_sq h1 he) n31
  · exact absurd (eq_of_mul_eq_one_of_sq h1 he) n21
  · have h12' : t₁ * t₂ * (t₁ * t₂) = 1 := by
      rw [mul_assoc, ← mul_assoc t₂, ← h12, mul_assoc, h2, mul_one, h1]
    exact absurd (eq_of_mul_eq_one_of_sq h12' he) n312

variable [AddCommGroup V] [Module (ZMod 2) V]

omit [Group Λ] in
theorem add_apply_eq_sub (f : V ≃ₗ[ZMod 2] V) (w : V) : w + f w = f w - w := by
  rw [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]

namespace ModCfg

variable {ρ : Λ →* (V ≃ₗ[ZMod 2] V)} {T : Subgroup Λ} {a : V} (C : ModCfg ρ T a)
include C

theorem apply_eq_iff (u : Λ) : ρ u a = a ↔ u ∈ normalizer (T : Set Λ) := by
  have := C.stab u 1
  simpa only [map_one, LinearEquiv.coe_one, id, conjSubgroup_one] using this

theorem apply_eq_of_mem {t : Λ} (ht : t ∈ T) : ρ t a = a :=
  (C.apply_eq_iff t).mpr (le_normalizer ht)

omit C in
theorem apply_apply (u y : Λ) (v : V) : ρ u (ρ y v) = ρ (u * y) v := by
  rw [map_mul, LinearEquiv.mul_apply]

theorem sum_orbit [Fintype Λ] [DecidableEq V] :
    ∑ w ∈ Finset.univ.image (fun y : Λ => ρ y a), w = 0 := by
  set Ω := Finset.univ.image (fun y : Λ => ρ y a) with hΩ
  apply C.fix0
  intro u
  rw [map_sum]
  have himg : Ω.image (ρ u) = Ω := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hw'
      exact Finset.mem_image.mpr ⟨u * y, Finset.mem_univ _, (apply_apply u y a).symm⟩
    · rw [Finset.card_image_of_injective _ (ρ u).injective]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image (fun x _ y _ h => (ρ u).injective h)]

theorem eq_one_of_fix (hSR : SRProp T) {y t : Λ} (hya : ρ y a ≠ a) (ht : t ∈ T)
    (hfix : ρ t (ρ y a) = ρ y a) : t = 1 := by
  have hne : conjSubgroup y T ≠ T := fun h => hya ((C.apply_eq_iff y).mpr
    (mem_normalizer_iff_conjSubgroup_eq.mpr h))
  have hmem : t ∈ T ⊓ normalizer (conjSubgroup y T : Set Λ) := ⟨ht, (C.stab t y).mp hfix⟩
  rw [hSR y hne] at hmem
  exact hmem

theorem apply_mem_erase [Fintype Λ] [DecidableEq V] {t : Λ} (ht : t ∈ T) {v : V}
    (hv : v ∈ (Finset.univ.image (fun y : Λ => ρ y a)).erase a) :
    ρ t v ∈ (Finset.univ.image (fun y : Λ => ρ y a)).erase a := by
  obtain ⟨hva, hv⟩ := Finset.mem_erase.mp hv
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_erase.mpr ⟨fun h => hva ?_, Finset.mem_image.mpr
    ⟨t * y, Finset.mem_univ _, (apply_apply t y a).symm⟩⟩
  have h1 := congrArg (ρ t⁻¹) h
  rwa [apply_apply, inv_mul_cancel, map_one, LinearEquiv.coe_one, id,
    C.apply_eq_of_mem (inv_mem ht)] at h1

omit C in
theorem sum_zm2pow (t : Λ) (w : V) : ∑ e : ZMod 2, ρ (zm2pow t e) w = ρ t w - w := by
  refine (Fin.sum_univ_two (fun e : ZMod 2 => ρ (zm2pow t e) w)).trans ?_
  change ρ (zm2pow t 0) w + ρ (zm2pow t 1) w = ρ t w - w
  rw [zm2pow_zero, zm2pow_one, map_one, LinearEquiv.coe_one, id, add_apply_eq_sub]

omit [AddCommGroup V] [Module (ZMod 2) V] C in
theorem exists_three [Finite Λ] (h8 : 8 ≤ Nat.card T) :
    ∃ t₁ ∈ T, ∃ t₂ ∈ T, ∃ t₃ ∈ T, t₁ ≠ 1 ∧ t₂ ≠ 1 ∧ t₂ ≠ t₁ ∧ t₃ ≠ 1 ∧ t₃ ≠ t₁ ∧
      t₃ ≠ t₂ ∧ t₃ ≠ t₁ * t₂ := by
  classical
  have := Fintype.ofFinite Λ
  set F : Finset Λ := Finset.univ.filter (fun x => x ∈ T) with hF
  have hFc : F.card = Nat.card T := by
    rw [hF, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmem : ∀ x, x ∈ F ↔ x ∈ T := fun x => by simp [hF]
  obtain ⟨t₁, ht₁F, ht₁⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {1}) (t := F)
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨t₂, ht₂F, ht₂⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {1, t₁}) (t := F)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨t₃, ht₃F, ht₃⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {1, t₁, t₂, t₁ * t₂}) (t := F) (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht₁ ht₂ ht₃
  exact ⟨t₁, (hmem _).mp ht₁F, t₂, (hmem _).mp ht₂F, t₃, (hmem _).mp ht₃F, ht₁, ht₂.1, ht₂.2,
    ht₃.1, ht₃.2.1, ht₃.2.2.1, ht₃.2.2.2⟩

theorem false_of_SR_eight [Finite Λ] [Finite V] (hSR : SRProp T) (h8 : 8 ≤ Nat.card T) :
    False := by
  classical
  have := Fintype.ofFinite Λ
  obtain ⟨t₁, h1, t₂, h2, t₃, h3, n1, n2, n21, n3, n31, n32, n312⟩ := exists_three h8
  set Ω := Finset.univ.image (fun y : Λ => ρ y a) with hΩ
  have haΩ : a ∈ Ω := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
  have hw_add := word3_add (C.sq t₁ h1) (C.sq t₂ h2) (C.sq t₃ h3) (C.comm _ h1 _ h2)
    (C.comm _ h1 _ h3) (C.comm _ h2 _ h3)
  have hN : ∀ v : V, ∑ d : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2),
      ρ (word3 t₁ t₂ t₃ (Multiplicative.toAdd d)) v = 0 := by
    intro v
    rw [Fintype.sum_equiv Multiplicative.toAdd _ (fun x => ρ (word3 t₁ t₂ t₃ x) v)
      (fun _ => rfl), Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have e1 : ∀ x y z, ρ (word3 t₁ t₂ t₃ (x, y, z)) v =
        ρ (zm2pow t₁ x) (ρ (zm2pow t₂ y) (ρ (zm2pow t₃ z) v)) := by
      intro x y z
      simp only [word3, map_mul, LinearEquiv.mul_apply]
    simp_rw [e1, ← map_sum, sum_zm2pow]
    exact C.cubic t₁ h1 t₂ h2 t₃ h3 v
  have hfree := free_orbit (D := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2))
    (fun d v => ρ (word3 t₁ t₂ t₃ (Multiplicative.toAdd d)) v)
    (fun v => by simp [word3_zero])
    (fun d e v => by simp only [toAdd_mul, hw_add, apply_apply])
    (Ω.erase a) (fun d v hv => C.apply_mem_erase (word3_mem h1 h2 h3 _) hv)
    (fun d v hv hfix => by
      obtain ⟨hva, hvΩ⟩ := Finset.mem_erase.mp hv
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hvΩ
      have h1' := C.eq_one_of_fix hSR hva (word3_mem h1 h2 h3 _) hfix
      exact toAdd_eq_zero.mp (word3_eq_one (C.sq t₁ h1) (C.sq t₂ h2) (C.comm _ h1 _ h2) n1 n2
        n21 n3 n31 n32 n312 h1'))
  have hs0 : ∑ v ∈ Ω.erase a, v = 0 := hfree.2 fun v _ => hN v
  have := Finset.add_sum_erase Ω (fun w => w) haΩ
  rw [hs0, add_zero, hΩ, C.sum_orbit] at this
  exact C.ne_zero this

theorem false_of_SR_four [Finite Λ] [Finite V] (hSR : SRProp T) (h4 : Nat.card T = 4)
    (hd : finrank (ZMod 2) V ≤ 3) : False := by
  classical
  have := Fintype.ofFinite Λ
  have := Fintype.ofFinite V
  set Ω := Finset.univ.image (fun y : Λ => ρ y a) with hΩ
  have haΩ : a ∈ Ω := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
  have hdvd := (free_orbit (D := ↥T) (fun d v => ρ (d : Λ) v) (fun v => by simp)
    (fun d e v => by simp only [Subgroup.coe_mul, apply_apply]) (Ω.erase a)
    (fun d v hv => C.apply_mem_erase d.2 hv)
    (fun d v hv hfix => by
      obtain ⟨hva, hvΩ⟩ := Finset.mem_erase.mp hv
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hvΩ
      exact Subtype.ext (C.eq_one_of_fix hSR hva d.2 hfix))).1
  rw [← Nat.card_eq_fintype_card, h4] at hdvd
  have hΩ0 : Ω ⊆ Finset.univ.erase 0 := fun w hw => by
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_erase.mpr ⟨fun h => C.ne_zero ?_, Finset.mem_univ _⟩
    exact (LinearEquiv.map_eq_zero_iff (ρ y)).mp h
  have hcV : Fintype.card V ≤ 8 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, Nat.card_eq_fintype_card] at h1
    rw [h1]
    calc 2 ^ finrank (ZMod 2) V ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hd
      _ = 8 := by norm_num
  have hΩc : Ω.card ≤ 7 := by
    have := Finset.card_le_card hΩ0
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    omega
  have hsc : (Ω.erase a).card = Ω.card - 1 := Finset.card_erase_of_mem haΩ
  have hs0 : (Ω.erase a).card ≠ 0 := by
    intro h0
    apply C.ne_zero
    refine C.fix0 a fun u => ?_
    by_contra hne
    have hmem : ρ u a ∈ Ω.erase a := Finset.mem_erase.mpr ⟨hne, Finset.mem_image.mpr
      ⟨u, Finset.mem_univ _, rfl⟩⟩
    rw [Finset.card_eq_zero.mp h0] at hmem
    exact Finset.notMem_empty _ hmem
  have h5 : Ω.card = 5 := by
    obtain ⟨c, hc⟩ := hdvd
    omega
  let _ : MulAction Λ V := MulAction.compHom V ρ
  have horb : (MulAction.orbit Λ a) = (Ω : Set V) := by
    rw [hΩ, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  have h5dvd : 5 ∣ Nat.card Λ := by
    have h1 := (MulAction.stabilizer Λ a).index_dvd_card
    rwa [MulAction.index_stabilizer, horb, Set.ncard_coe_finset, h5] at h1
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  refine false_of_orderOf_prime C.inj (p := 5) (by norm_num) (fun j hj0 hj => ?_) hc
  have hj3 : j ≤ 3 := hj.trans hd
  interval_cases j <;> decide

end ModCfg

end CFSG.LargeExtraspecial.S11
