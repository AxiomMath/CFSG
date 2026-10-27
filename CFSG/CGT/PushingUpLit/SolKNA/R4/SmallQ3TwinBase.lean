module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallBase
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinReduce

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.TwinFr QuaternionGroup

noncomputable def q8Phi (N h : ℕ) (hh : N = h + h) : ZMod (2 * 2) →+ ZMod (2 * N) :=
  ZMod.lift (2 * 2)
    ⟨(AddMonoidHom.mulLeft (h : ZMod (2 * N))).comp (Int.castAddHom (ZMod (2 * N))), by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, Int.coe_castAddHom,
        AddMonoidHom.coe_mulLeft]
      have : (h : ZMod (2 * N)) * (((2 * 2 : ℕ) : ℤ) : ZMod (2 * N)) =
          ((2 * N : ℕ) : ZMod (2 * N)) := by
        subst hh
        push_cast
        ring
      rw [this]
      exact ZMod.natCast_self _⟩

theorem q8Phi_intCast (N h : ℕ) (hh : N = h + h) (k : ℤ) :
    q8Phi N h hh (k : ZMod (2 * 2)) = (h : ZMod (2 * N)) * (k : ZMod (2 * N)) := by
  unfold q8Phi
  rw [ZMod.lift_coe]
  rfl

theorem q8Phi_two (N h : ℕ) (hh : N = h + h) :
    q8Phi N h hh (((2 : ℕ) : ZMod (2 * 2))) = (N : ZMod (2 * N)) := by
  have : (((2 : ℕ) : ZMod (2 * 2))) = (((2 : ℤ)) : ZMod (2 * 2)) := by norm_cast
  rw [this, q8Phi_intCast]
  subst hh
  push_cast
  ring

theorem q8Phi_injective (N h : ℕ) (hh : N = h + h) (hpos : 0 < h) :
    Function.Injective (q8Phi N h hh) := by
  rw [injective_iff_map_eq_zero]
  intro i hi
  obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < 4 ∧ ((k : ℕ) : ZMod (2 * 2)) = i := by
    refine ⟨i.val, ?_, ?_⟩
    · have := ZMod.val_lt i
      simpa using this
    · exact ZMod.natCast_zmod_val i
  have h1 : q8Phi N h hh (k : ZMod (2 * 2)) = (h : ZMod (2 * N)) * (k : ZMod (2 * N)) := by
    have := q8Phi_intCast N h hh (k : ℤ)
    simpa using this
  rw [h1, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hi
  have h2 : 2 * N = 4 * h := by omega
  rw [h2] at hi
  have h3 : 4 ∣ k := by
    have := Nat.dvd_of_mul_dvd_mul_right hpos (by simpa [mul_comm] using hi)
    exact this
  have : k = 0 := by
    obtain ⟨m, rfl⟩ := h3
    omega
  subst this
  simp

noncomputable def q8ToQuat (N h : ℕ) (hh : N = h + h) : QuaternionGroup 2 →* QuaternionGroup N where
  toFun q := match q with
    | .a i => .a (q8Phi N h hh i)
    | .xa i => .xa (q8Phi N h hh i)
  map_one' := by
    show a (q8Phi N h hh 0) = 1
    rw [map_zero, one_def]
  map_mul' := by
    rintro (i | i) (j | j)
    · show a (q8Phi N h hh (i + j)) = a (q8Phi N h hh i) * a (q8Phi N h hh j)
      rw [map_add, a_mul_a]
    · show xa (q8Phi N h hh (j - i)) = a (q8Phi N h hh i) * xa (q8Phi N h hh j)
      rw [map_sub, a_mul_xa]
    · show xa (q8Phi N h hh (i + j)) = xa (q8Phi N h hh i) * a (q8Phi N h hh j)
      rw [map_add, xa_mul_a]
    · show a (q8Phi N h hh (((2 : ℕ) : ZMod (2 * 2)) + j - i)) =
        xa (q8Phi N h hh i) * xa (q8Phi N h hh j)
      rw [map_sub, map_add, q8Phi_two, xa_mul_xa]

theorem q8ToQuat_injective (N h : ℕ) (hh : N = h + h) (hpos : 0 < h) :
    Function.Injective (q8ToQuat N h hh) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) hi
  · have : a (q8Phi N h hh i) = (1 : QuaternionGroup N) := hi
    rw [one_def] at this
    have h0 := QuaternionGroup.a.inj this
    have := q8Phi_injective N h hh hpos (h0.trans (map_zero _).symm)
    rw [this, ← one_def]
  · exfalso
    have : xa (q8Phi N h hh i) = (1 : QuaternionGroup N) := hi
    rw [one_def] at this
    cases this

theorem q8ToQuat_a_two (N h : ℕ) (hh : N = h + h) :
    q8ToQuat N h hh (a 2) = a (N : ZMod (2 * N)) := by
  show a (q8Phi N h hh 2) = _
  have := q8Phi_two N h hh
  simpa using this

@[expose] def Q8Emb {Y : Type*} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ ι : QuaternionGroup 2 →* Y, Function.Injective ι ∧ (∀ q, ι q ∈ R) ∧ ι (a 2) = t

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_q8Emb {r : ℕ} (hr : 3 ≤ r) (hd : TightDatum R S t)
    (hS : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) : Q8Emb R t := by
  obtain ⟨e⟩ := hS
  obtain ⟨h, hh, hpos⟩ : ∃ h : ℕ, 2 ^ (r - 2) = h + h ∧ 0 < h :=
    ⟨2 ^ (r - 3), by rw [show r - 2 = (r - 3) + 1 by omega, pow_succ]; ring, by positivity⟩
  let ι : QuaternionGroup 2 →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp (e.symm.toMonoidHom.comp (q8ToQuat _ h hh)))
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp
      (e.symm.injective.comp (q8ToQuat_injective _ h hh hpos)))
  have hR : ∀ q, ι q ∈ R := fun q => (((e.symm (q8ToQuat _ h hh q)) : S) : R).2
  refine ⟨ι, hι, hR, hd.eq_of_orderOf_eq_two (hR _) ?_⟩
  rw [orderOf_injective ι hι]
  exact orderOf_eq_prime (by decide) (by decide)

open QuaternionGroup in
theorem exists_sq_eq_of_index_le_two_q8 (hq : Q8Emb R t) {L : Subgroup Y} (hL : L.index ≤ 2) :
    ∃ s ∈ R, s ∈ L ∧ s * s = t := by
  obtain ⟨ι, -, hR, ht⟩ := hq
  have hsq : ∀ q : QuaternionGroup 2, q * q = a 2 → ι q * ι q = t := fun q hq => by
    rw [← map_mul, hq, ht]
  have h1 := hsq (a 1) (by decide)
  have h2 := hsq (xa 0) (by decide)
  have h3 := hsq (a 1 * xa 0) (by decide)
  have hne : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show L.index = 1 ∨ L.index = 2 by omega) with h | h
  · exact ⟨ι (a 1), hR _, Subgroup.index_eq_one.1 h ▸ Subgroup.mem_top _, h1⟩
  · by_cases hi : ι (a 1) ∈ L
    · exact ⟨_, hR _, hi, h1⟩
    by_cases hj : ι (xa 0) ∈ L
    · exact ⟨_, hR _, hj, h2⟩
    refine ⟨_, hR _, ?_, h3⟩
    rw [map_mul, Subgroup.mul_mem_iff_of_index_two h]
    exact iff_of_false hi hj

theorem twinHyp_fstar_R {r : ℕ} (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hE2 : ¬ TightInO2 t) (hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)) :
    TwinHyp (genFittingFStar Y) R S t := by
  have hNc := fstarCenter_le_center_R hd hc hE2
  have hN2 := isPGroup_fstarCenter_R hc
  have htN := not_mem_fstarCenter_R hc hE2
  have htL : t ∈ genFittingFStar Y := hd.mem_genFittingFStar hc.2.2
  have hCL : ∀ y : Y, (∀ l ∈ genFittingFStar Y, y * l = l * y) → y ∈ genFittingFStar Y :=
    fun y hy => CFSG.Adapters.generalized_fitting_self_centralizing Y
      (Subgroup.mem_centralizer_iff.mpr fun l hl => (hy l hl).symm)
  refine ⟨hd, htL, ?_, hsmall, hCL, fun r hr hrc => ?_, fun z hz hzc g =>
    Subgroup.mem_center_iff.mp (hNc (mem_fstarCenter hz hzc)) g⟩
  · by_contra hcon
    push Not at hcon
    exact htN (mem_fstarCenter htL fun l hl => (hcon l hl).symm)
  · have hrN := mem_fstarCenter (hCL r hrc) hrc
    by_contra hr1
    obtain ⟨n, hn⟩ := hN2 ⟨r, hrN⟩
    have hr2 : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hr2)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
      rcases k with _ | k
      · exact absurd (orderOf_eq_one_iff.mp (by rw [hk, pow_zero])) hr1
      · omega⟩
    have h2 : orderOf (r ^ 2 ^ j) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk, pow_succ,
        Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    exact htN (hd.eq_of_orderOf_eq_two (R.pow_mem hr _) h2 ▸ (fstarCenter Y).pow_mem hrN _)

theorem isPGroup_center_fstar_R {r : ℕ} (hc : TightClsR r Y R S t) :
    IsPGroup 2 ↥(Subgroup.center ↥(genFittingFStar Y)) := fun z => by
  obtain ⟨n, hn⟩ := isPGroup_fstarCenter_R hc
    ⟨((z : ↥(genFittingFStar Y)) : Y), ⟨z, z.2, rfl⟩⟩
  exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩

end Datum

end CFSG.CGT.PushingUpLit.SolKNA.R4
