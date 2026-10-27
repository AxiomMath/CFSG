module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

theorem card_le_fix_sq {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (α : MulAut V) (hα : α * α = 1) :
    Nat.card V ≤ Nat.card {v : V // α v = v} ^ 2 := by
  classical
  have hαα : ∀ v : V, α (α v) = v := by
    intro v
    have := congrArg (fun m : MulAut V => m v) hα
    simpa using this
  let φ : V →* V := MonoidHom.mk' (fun v => v * α v) (by
    intro a b
    simp only [map_mul]
    exact mul_mul_mul_comm a b (α a) (α b))
  have hφ : ∀ v, φ v = v * α v := fun v => rfl
  let Fx : Subgroup V := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id V)
  have hFx : ∀ v, v ∈ Fx ↔ α v = v := fun v => Iff.rfl
  have hinv : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hker : φ.ker ≤ Fx := by
    intro w hw
    rw [MonoidHom.mem_ker, hφ] at hw
    rw [hFx]
    have h : α w = w⁻¹ := (inv_eq_of_mul_eq_one_right hw).symm
    rw [h, hinv]
  have hrange : φ.range ≤ Fx := by
    rintro _ ⟨w, rfl⟩
    rw [hFx, hφ]
    simp only [map_mul, hαα]
    exact mul_comm _ _
  have hFxcard : Nat.card Fx = Nat.card {v : V // α v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hFx)
  have h1 : Nat.card V = Nat.card φ.ker * Nat.card φ.range :=
    (Subgroup.card_ker_mul_card_range φ).symm
  have h3 : Nat.card φ.range ≤ Nat.card Fx := Subgroup.card_le_of_le hrange
  have h4 : Nat.card φ.ker ≤ Nat.card Fx := Subgroup.card_le_of_le hker
  rw [h1, ← hFxcard, sq]
  exact Nat.mul_le_mul h4 h3

theorem card_fix_le_sq {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (u α : MulAut V) (hu : u * u = 1) (hαu : α * u = u * α) (B : Subgroup V)
    (hfix : ∀ e : V, u e = e ↔ e ∈ B) :
    Nat.card {v : V // α v = v} ≤ Nat.card {b : V // b ∈ B ∧ α b = b} ^ 2 := by
  classical
  let S : Subgroup V :=
    { carrier := {v | α v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : α a = a := ha
        have hb' : α b = b := hb
        change α (a * b) = a * b
        rw [map_mul, ha', hb']
      inv_mem' := by
        intro a ha
        have ha' : α a = a := ha
        change α a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  let T : Subgroup V :=
    { carrier := {b | b ∈ B ∧ α b = b}
      one_mem' := ⟨B.one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        exact ⟨B.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      inv_mem' := by
        intro a ha
        exact ⟨B.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hu2 : ∀ e : V, u (u e) = e := by
    intro e
    have := congrArg (fun m : MulAut V => m e) hu
    simpa using this
  have hαu_apply : ∀ e : V, α (u e) = u (α e) := by
    intro e
    have := congrArg (fun m : MulAut V => m e) hαu
    simpa [MulAut.mul_apply] using this
  let δ : V →* V := MonoidHom.mk' (fun e => e * (u e)⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv_rev]
    ac_rfl)
  have hδ : ∀ e, δ e = e * (u e)⁻¹ := fun e => rfl
  have hδT : ∀ e : S, δ (e : V) ∈ T := by
    intro e
    have he : α (e : V) = (e : V) := e.2
    constructor
    · rw [← hfix, hδ]
      rw [map_mul, map_inv, hu2]
      rw [inv_eq_of_mul_eq_one_right (hsq (e : V)),
        inv_eq_of_mul_eq_one_right (hsq (u (e : V)))]
      exact mul_comm _ _
    · rw [hδ, map_mul, map_inv, hαu_apply, he]
  let δS : S →* T :=
    { toFun := fun e => ⟨δ (e : V), hδT e⟩
      map_one' := Subtype.ext (map_one δ)
      map_mul' := fun a b => Subtype.ext (map_mul δ (a : V) (b : V)) }
  have hS : Nat.card S = Nat.card δS.ker * Nat.card δS.range :=
    (Subgroup.card_ker_mul_card_range δS).symm
  have hker_le : Nat.card δS.ker ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective
      (fun e : δS.ker => (⟨((e : S) : V), ?_⟩ : T)) ?_
    · have heS : α ((e : S) : V) = ((e : S) : V) := (e : S).2
      have hδ1 : δ ((e : S) : V) = 1 := by
        have h2 : (δS (e : S) : V) = ((1 : T) : V) :=
          congrArg (fun t : T => (t : V)) (MonoidHom.mem_ker.mp e.2)
        change δ ((e : S) : V) = 1 at h2
        exact h2
      have hu_eq : u ((e : S) : V) = ((e : S) : V) :=
        (eq_of_mul_inv_eq_one hδ1).symm
      exact ⟨(hfix _).mp hu_eq, heS⟩
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun t : T => (t : V)) hab))
  have hrange_le : Nat.card δS.range ≤ Nat.card T :=
    Nat.card_le_card_of_injective (fun r : δS.range => (r : T)) Subtype.val_injective
  have hmain : Nat.card S ≤ Nat.card T ^ 2 := by
    calc Nat.card S = Nat.card δS.ker * Nat.card δS.range := hS
      _ ≤ Nat.card T * Nat.card T := Nat.mul_le_mul hker_le hrange_le
      _ = Nat.card T ^ 2 := (pow_two _).symm
  exact hmain

theorem card_fix_eq_sixteen {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 8) (u α : MulAut V) (hu : u * u = 1) (hα : α * α = 1)
    (hαu : α * u = u * α) (B : Subgroup V) (hfix : ∀ e : V, u e = e ↔ e ∈ B)
    (hB4 : Nat.card {b : V // b ∈ B ∧ α b = b} = 4) :
    Nat.card {v : V // α v = v} = 16 := by
  have h1 := card_le_fix_sq hsq α hα
  have h2 := card_fix_le_sq hsq u α hu hαu B hfix
  rw [hcard] at h1
  have hge : 16 ≤ Nat.card {v : V // α v = v} := by
    by_contra hlt
    push Not at hlt
    have hle : Nat.card {v : V // α v = v} ≤ 15 := by omega
    have hpow : Nat.card {v : V // α v = v} ^ 2 ≤ 15 ^ 2 :=
      Nat.pow_le_pow_left hle 2
    norm_num at h1 hpow
    omega
  have hle : Nat.card {v : V // α v = v} ≤ 16 := by
    calc Nat.card {v : V // α v = v}
        ≤ Nat.card {b : V // b ∈ B ∧ α b = b} ^ 2 := h2
      _ = 4 ^ 2 := by rw [hB4]
      _ = 16 := by norm_num
  omega

theorem card_fix_conj {V : Type} [Group V] (h α : MulAut V) :
    Nat.card {v : V // (h * α * h⁻¹) v = v} = Nat.card {v : V // α v = v} := by
  have key : ∀ v : V, (h * α * h⁻¹) v = v ↔ α (h⁻¹ v) = h⁻¹ v := by
    intro v
    rw [MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro hv
      exact h.injective (by rw [hv, MulAut.apply_inv_self])
    · intro hv
      rw [hv, MulAut.apply_inv_self]
  exact Nat.card_congr (Equiv.subtypeEquiv (h⁻¹ : MulAut V).toEquiv key)

theorem card_le_four_of_fix_four {X : Type} [Finite X] (hX : Nat.card X = 16) {R : Type}
    [Group R] [Finite R] (ρ : R →* Equiv.Perm X) (hsq : ∀ r : R, r * r = 1)
    (hfix : ∀ r : R, r ≠ 1 → Nat.card {x : X // ρ r x = x} = 4) : Nat.card R ≤ 4 := by
  classical
  letI : MulAction R X := MulAction.compHom X ρ
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ r : R, Fintype (MulAction.fixedBy X r) :=
    fun r => Fintype.ofFinite (MulAction.fixedBy X r)
  haveI : Fintype (MulAction.orbitRel.Quotient R X) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group R X
  have hcard_fixed : ∀ r : R, Fintype.card (MulAction.fixedBy X r)
      = Nat.card {x : X // ρ r x = x} := by
    intro r
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  have hburn' : (∑ r : R, Nat.card {x : X // ρ r x = x})
      = Nat.card (MulAction.orbitRel.Quotient R X) * Nat.card R := by
    have h1 : (∑ r : R, Nat.card {x : X // ρ r x = x})
        = ∑ r : R, Fintype.card (MulAction.fixedBy X r) :=
      Finset.sum_congr rfl fun r _ => (hcard_fixed r).symm
    rw [h1, hburn]
    simp only [Nat.card_eq_fintype_card]
  have hsum : (∑ r : R, Nat.card {x : X // ρ r x = x}) = 4 * Nat.card R + 12 := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun r => Nat.card {x : X // ρ r x = x}) (Finset.mem_univ (1 : R))]
    have h1 : Nat.card {x : X // ρ (1 : R) x = x} = 16 := by
      have hall : ∀ x : X, ρ (1 : R) x = x := by
        intro x; rw [map_one]; rfl
      have e : {x : X // ρ (1 : R) x = x} ≃ X :=
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, hall x⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun x => rfl }
      rw [Nat.card_congr e, hX]
    rw [h1]
    have hrest : (∑ r ∈ Finset.univ.erase (1 : R), Nat.card {x : X // ρ r x = x})
        = (Finset.univ.erase (1 : R)).card * 4 := by
      apply Finset.sum_const_nat
      intro r hr
      rw [Finset.mem_erase] at hr
      exact hfix r hr.1
    rw [hrest, Finset.card_erase_of_mem (Finset.mem_univ (1 : R)), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    have hn : 0 < Nat.card R := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    omega
  have heq : Nat.card (MulAction.orbitRel.Quotient R X) * Nat.card R = 4 * Nat.card R + 12 := by
    rw [← hburn', hsum]
  have hdvd : Nat.card R ∣ 12 := by
    have h2 : Nat.card R ∣ 4 * Nat.card R := Nat.dvd_mul_left _ _
    have h1 : Nat.card R ∣ 4 * Nat.card R + 12 := by
      rw [← heq]; exact Nat.dvd_mul_left _ _
    exact (Nat.dvd_add_iff_right h2).mpr h1
  have h3 : ¬ 3 ∣ Nat.card R := by
    intro h3dvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    have h2 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq r)
    rw [hr] at h2
    exact absurd h2 (by norm_num)
  have hmem : Nat.card R ∈ Nat.divisors 12 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [h12] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  · omega
  · omega
  · exact absurd (by rw [h]) h3
  · omega
  · exact absurd (by rw [h]; norm_num) h3
  · exact absurd (by rw [h]; norm_num) h3

end C10

end CFSG.OddStandard.SmallF3.Omega
