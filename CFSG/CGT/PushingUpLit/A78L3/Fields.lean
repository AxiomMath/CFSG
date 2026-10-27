module

public import CFSG.CGT.PushingUpLit.A78Sp4.FieldSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.QuasithinUnique.Setup.Offender (exists_trace_eq_one)

variable {F : Type} [Field F]

theorem exists_ringEquiv_of_mul [Finite F] {f g h : F → F}
    (hh : ∀ x y, h (x + y) = h x + h y) (hinj : Function.Injective h)
    (hmul : ∀ u r, h (u * r) = f u * g r) :
    ∃ τ : F ≃+* F, (∀ u, f u = f 1 * τ u) ∧ (∀ r, g r = g 1 * τ r) ∧
      (∀ x, h x = f 1 * g 1 * τ x) ∧ f 1 ≠ 0 ∧ g 1 ≠ 0 := by
  have h0 : h 0 = 0 := by
    have := hh 0 0
    rw [add_zero] at this
    linear_combination -this
  have h1 : h 1 ≠ 0 := fun h1 => one_ne_zero (hinj (h1.trans h0.symm))
  have hk : h 1 = f 1 * g 1 := by rw [← hmul, mul_one]
  have hf1 : f 1 ≠ 0 := fun hf => h1 (by rw [hk, hf, zero_mul])
  have hg1 : g 1 ≠ 0 := fun hg => h1 (by rw [hk, hg, mul_zero])
  have hf : ∀ u, f u = h u / g 1 := fun u => by rw [← mul_one u, hmul, mul_one]; field_simp
  have hg : ∀ r, g r = h r / f 1 := fun r => by rw [← one_mul r, hmul, one_mul]; field_simp
  let τ' : F →+* F :=
    { toFun := fun x => h x / h 1
      map_one' := div_self h1
      map_mul' := fun x y => by
        rw [hmul, hf x, hg y, hk]
        field_simp
      map_zero' := by rw [h0, zero_div]
      map_add' := fun x y => by rw [hh, add_div] }
  have hτinj : Function.Injective τ' := τ'.injective
  let τ := RingEquiv.ofBijective τ' ⟨hτinj, Finite.surjective_of_injective hτinj⟩
  have hτ : ∀ x, τ x = h x / h 1 := fun x => rfl
  refine ⟨τ, fun u => ?_, fun r => ?_, fun x => ?_, hf1, hg1⟩
  · rw [hf, hτ, hk]; field_simp
  · rw [hg, hτ, hk]; field_simp
  · rw [hτ, hk]; field_simp

theorem card_fix_le [Finite F] (τ : F ≃+* F) (ν : F) :
    Nat.card {r : F // ν * τ r = r} ≤ Nat.card {c : F // τ c = c} := by
  by_cases hex : ∃ r₁ : F, r₁ ≠ 0 ∧ ν * τ r₁ = r₁
  · obtain ⟨r₁, hr₁, hfix₁⟩ := hex
    have hν : ν ≠ 0 := fun h0 => hr₁ (by rw [← hfix₁, h0, zero_mul])
    have hτr₁ : τ r₁ ≠ 0 := fun h0 => hr₁ (by rw [← hfix₁, h0, mul_zero])
    refine Nat.card_le_card_of_injective (fun r => ⟨r.1 / r₁, ?_⟩) fun r r' hrr => ?_
    · rw [map_div₀]
      have h1 : τ r.1 = r.1 / ν := by field_simp; rw [mul_comm]; exact r.2
      have h2 : τ r₁ = r₁ / ν := by field_simp; rw [mul_comm]; exact hfix₁
      rw [h1, h2]
      field_simp
    · have := congrArg Subtype.val hrr
      simp only at this
      exact Subtype.ext ((div_left_inj' hr₁).1 this)
  · push Not at hex
    have hsub : ∀ r : {r : F // ν * τ r = r}, r.1 = 0 := fun r => by
      by_contra h0
      exact hex r.1 h0 r.2
    exact Nat.card_le_card_of_injective (fun _ => (⟨0, map_zero τ⟩ : {c : F // τ c = c}))
      fun r r' _ => Subtype.ext ((hsub r).trans (hsub r').symm)

theorem exists_add_mul_eq [Finite F] [CharP F 2] (τ : F ≃+* F) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1)
    {ν : F} {s : F} (hs : ν * τ s = s) : ∃ r, r + ν * τ r = s := by
  obtain ⟨x, hx⟩ := exists_trace_eq_one τ hτ1 hτ2
  refine ⟨s * x, ?_⟩
  rw [map_mul, ← mul_assoc, hs]
  linear_combination s * hx

theorem semInv_zero {σ : F ≃+* F} {b : (Fin 2 → F) → (Fin 2 → F)} (hb : SemInv σ b) :
    b 0 = 0 := by
  have := hb.add 0 0
  rw [add_zero] at this
  exact add_eq_left.mp this.symm

theorem exists_add_semInv_eq [Finite F] [CharP F 2] {σ : F ≃+* F} {b : (Fin 2 → F) → (Fin 2 → F)}
    (hσ : ∃ c, σ c ≠ c) (hb : SemInv σ b) {w : Fin 2 → F} (hw : b w = w) :
    ∃ u, u + b u = w := by
  classical
  let φ : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun u => u + b u
      map_zero' := by rw [semInv_zero hb, add_zero]
      map_add' := fun u u' => by rw [hb.add]; abel }
  have hrange : ∀ y ∈ φ.range, y ∈ fixSet b := by
    rintro _ ⟨u, rfl⟩
    show b (u + b u) = u + b u
    rw [hb.add, hb.invol, add_comm]
  have hker : ∀ u, u ∈ φ.ker ↔ u ∈ fixSet b := by
    intro u
    rw [AddMonoidHom.mem_ker, mem_fixSet]
    show u + b u = 0 ↔ b u = u
    constructor
    · intro h
      calc b u = (u + b u) + u := by
            rw [add_comm u (b u), add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = u := by rw [h, zero_add]
    · intro h
      rw [h, CharTwo.add_self_eq_zero]
  have hfix := card_fixSet hσ hb
  have hkr := AddSubgroup.card_ker_mul_card_range φ
  have hkc : Nat.card φ.ker = Nat.card F := by
    rw [← hfix]
    exact Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hall : Nat.card (Fin 2 → F) = Nat.card F * Nat.card F := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, pow_two]
  rw [hkc, hall] at hkr
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hrc : Nat.card φ.range = Nat.card F := Nat.eq_of_mul_eq_mul_left hpos hkr
  let Fx : AddSubgroup (Fin 2 → F) :=
    { carrier := fixSet b
      zero_mem' := semInv_zero hb
      add_mem' := fun {u u'} hu hu' => by
        show b (u + u') = u + u'
        rw [hb.add, hu, hu']
      neg_mem' := fun {u} hu => by
        show b (-u) = -u
        rw [CharTwo.neg_eq]
        exact hu }
  have hle : φ.range ≤ Fx := fun y hy => hrange y hy
  have hFx : Nat.card Fx = Nat.card F := hfix
  have heq : φ.range = Fx := AddSubgroup.eq_of_le_of_card_ge hle (by rw [hFx, hrc])
  have hwF : w ∈ Fx := hw
  rw [← heq] at hwF
  obtain ⟨u, hu⟩ := hwF
  exact ⟨u, hu⟩

end CFSG.CGT.PushingUpLit.A78L3
