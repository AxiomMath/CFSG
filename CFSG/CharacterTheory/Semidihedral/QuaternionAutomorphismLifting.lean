module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionNormalForm

public section

namespace CFSG.Semidihedral.QuaternionAutomorphismLifting

open QuaternionGroup

theorem half_add_half (m : ℕ) : (m : ZMod (2 * m)) + m = 0 := by
  simpa only [two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)

theorem twice_eq_zero_iff (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    i + i = 0 ↔ i = 0 ∨ i = (m : ZMod (2 * m)) := by
  constructor
  · intro h
    have hd : 2 * m ∣ 2 * i.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using
        (show (2 : ZMod (2 * m)) * i = 0 by simpa only [two_mul] using h)
    obtain ⟨k, hk⟩ := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd
    have hi := ZMod.val_lt i
    have hm := NeZero.pos m
    have hklt : k < 2 := by nlinarith
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · left
      apply ZMod.val_injective
      simpa using hk
    · right
      rw [← ZMod.natCast_zmod_val i, hk, mul_one]
  · rintro (rfl | rfl)
    · simp
    · exact half_add_half m

theorem center_iff (m : ℕ) (hm : 2 ≤ m) (q : QuaternionGroup m) :
    q ∈ Subgroup.center (QuaternionGroup m) ↔ q = 1 ∨ q = a (m : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  constructor
  · intro h
    cases q with
    | a i =>
      have hc := Subgroup.mem_center_iff.mp h (xa 0)
      simp only [xa_mul_a, a_mul_xa, zero_add, zero_sub, xa.injEq] at hc
      have hi : i + i = 0 := by
        calc
          i + i = -i + i := congrArg (fun t => t + i) hc
          _ = 0 := neg_add_cancel i
      rcases (twice_eq_zero_iff m i).mp hi with rfl | rfl
      · exact Or.inl (a_zero)
      · exact Or.inr rfl
    | xa i =>
      have hc := Subgroup.mem_center_iff.mp h (a 1)
      simp only [a_mul_xa, xa_mul_a, xa.injEq] at hc
      have hone : (1 : ZMod (2 * m)) + 1 = 0 := by
        linear_combination -hc
      have hv := congrArg ZMod.val hone
      have hlt : 2 < 2 * m := by omega
      have hval : (1 : ZMod (2 * m)) + 1 = (2 : ℕ) := by norm_num
      rw [hval, ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
      omega
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · apply Subgroup.mem_center_iff.mpr
      intro q
      cases q with
      | a i => simp only [a_mul_a, add_comm]
      | xa i =>
        simp only [xa_mul_a, a_mul_xa, xa.injEq]
        have h := half_add_half m
        linear_combination h

@[expose] def reduceCoordinate (m : ℕ) : ZMod (2 * m) →+* ZMod m :=
  ZMod.castHom (dvd_mul_left m 2) (ZMod m)

@[simp] theorem reduceCoordinate_natCast (m k : ℕ) :
    reduceCoordinate m (k : ZMod (2 * m)) = (k : ZMod m) := map_natCast _ _

@[expose] def dihedralProjection (m : ℕ) : QuaternionGroup m →* DihedralGroup m where
  toFun q := match q with
    | a i => DihedralGroup.r (reduceCoordinate m i)
    | xa i => DihedralGroup.sr (reduceCoordinate m i)
  map_one' := by
    change DihedralGroup.r (reduceCoordinate m 0) = 1
    simp
  map_mul' q t := by
    cases q <;> cases t <;>
      simp [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
        QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
        DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]

@[simp] theorem dihedralProjection_a (m : ℕ) (i : ZMod (2 * m)) :
    dihedralProjection m (a i) = DihedralGroup.r (reduceCoordinate m i) := rfl

@[simp] theorem dihedralProjection_xa (m : ℕ) (i : ZMod (2 * m)) :
    dihedralProjection m (xa i) = DihedralGroup.sr (reduceCoordinate m i) := rfl

theorem dihedralProjection_surjective (m : ℕ) :
    Function.Surjective (dihedralProjection m) := by
  intro q
  cases q with
  | r i =>
    obtain ⟨j, hj⟩ := ZMod.castHom_surjective (dvd_mul_left m 2) i
    exact ⟨a j, congrArg DihedralGroup.r hj⟩
  | sr i =>
    obtain ⟨j, hj⟩ := ZMod.castHom_surjective (dvd_mul_left m 2) i
    exact ⟨xa j, congrArg DihedralGroup.sr hj⟩

theorem reduceCoordinate_eq_zero_iff (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    reduceCoordinate m i = 0 ↔ i = 0 ∨ i = (m : ZMod (2 * m)) := by
  constructor
  · intro h
    have hd : m ∣ i.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [← ZMod.natCast_zmod_val i, reduceCoordinate_natCast] at h
      exact h
    obtain ⟨k, hk⟩ := hd
    have hi := ZMod.val_lt i
    have hm := NeZero.pos m
    have hklt : k < 2 := by nlinarith
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · left
      apply ZMod.val_injective
      simpa using hk
    · right
      rw [← ZMod.natCast_zmod_val i, hk, mul_one]
  · rintro (rfl | rfl) <;> simp

theorem dihedralProjection_ker (m : ℕ) (hm : 2 ≤ m) :
    (dihedralProjection m).ker = Subgroup.center (QuaternionGroup m) := by
  let : NeZero m := ⟨by omega⟩
  ext q
  rw [MonoidHom.mem_ker, center_iff m hm]
  cases q with
  | a i =>
    simpa only [dihedralProjection_a, DihedralGroup.one_def, DihedralGroup.r.injEq,
      QuaternionGroup.one_def, QuaternionGroup.a.injEq] using reduceCoordinate_eq_zero_iff m i
  | xa i =>
    simp only [dihedralProjection_xa, DihedralGroup.one_def, QuaternionGroup.one_def,
      reduceCtorEq, false_or]

@[expose] noncomputable def centerQuotientEquivDihedral (m : ℕ) (hm : 2 ≤ m) :
    QuaternionGroup m ⧸ Subgroup.center (QuaternionGroup m) ≃* DihedralGroup m :=
  QuotientGroup.liftEquiv (Subgroup.center (QuaternionGroup m))
    (dihedralProjection_surjective m) (dihedralProjection_ker m hm).symm

@[simp] theorem centerQuotientEquivDihedral_mk (m : ℕ) (hm : 2 ≤ m)
    (q : QuaternionGroup m) :
    centerQuotientEquivDihedral m hm (QuotientGroup.mk' (Subgroup.center _) q) =
      dihedralProjection m q := QuotientGroup.liftEquiv_mk _ _ _ _

theorem centralHalf_ne_one (m : ℕ) (hm : 0 < m) :
    (a (m : ZMod (2 * m)) : QuaternionGroup m) ≠ 1 := by
  intro h
  rw [QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

theorem centralHalf_sq (m : ℕ) :
    (a (m : ZMod (2 * m)) : QuaternionGroup m) ^ 2 = 1 := by
  rw [pow_two, a_mul_a, half_add_half, a_zero]

theorem rotation_pow (m : ℕ) (i : ZMod (2 * m)) (k : ℕ) :
    (a i : QuaternionGroup m) ^ k = a (i * (k : ZMod (2 * m))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

@[expose] def coordinatePowerHom {G : Type*} [Group G] (k : ℕ) [NeZero k]
    (u : G) (hu : u ^ k = 1) : Multiplicative (ZMod k) →* G where
  toFun i := u ^ (Multiplicative.toAdd i).val
  map_one' := by simp
  map_mul' i j := by
    change u ^ (Multiplicative.toAdd i + Multiplicative.toAdd j).val =
      u ^ (Multiplicative.toAdd i).val * u ^ (Multiplicative.toAdd j).val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hu).symm

@[simp] theorem coordinatePowerHom_natCast {G : Type*} [Group G] (k : ℕ) [NeZero k]
    (u : G) (hu : u ^ k = 1) (j : ℕ) :
    coordinatePowerHom k u hu (Multiplicative.ofAdd (j : ZMod k)) = u ^ j := by
  change u ^ (j : ZMod k).val = u ^ j
  rw [ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hu).symm

theorem power_passes_outside {G : Type*} [Group G] (u v : G)
    (huv : u * v = v * u⁻¹) (k : ℕ) : u ^ k * v = v * (u ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, huv, ← mul_assoc, ih, mul_assoc, ← mul_inv_rev]
    rw [← pow_succ, ← pow_succ']

@[expose] noncomputable def relationsHom (m : ℕ) [NeZero m]
    (u v : QuaternionGroup m) (hperiod : u ^ (2 * m) = 1)
    (hsquare : v ^ 2 = u ^ m) (hinvert : u * v = v * u⁻¹) :
    QuaternionGroup m →* QuaternionGroup m :=
  CFSG.TwoRankLowerBound.Helpers.quaternionNormalFormHom m
    (coordinatePowerHom (2 * m) u hperiod) v
    (by simpa only [coordinatePowerHom_natCast] using hsquare)
    (fun i => power_passes_outside u v hinvert i.val)

@[simp] theorem relationsHom_a_one (m : ℕ) [NeZero m]
    (u v : QuaternionGroup m) (hperiod : u ^ (2 * m) = 1)
    (hsquare : v ^ 2 = u ^ m) (hinvert : u * v = v * u⁻¹) :
    relationsHom m u v hperiod hsquare hinvert (a 1) = u := by
  change coordinatePowerHom (2 * m) u hperiod (Multiplicative.ofAdd (1 : ZMod (2 * m))) = u
  simpa only [pow_one, Nat.cast_one] using coordinatePowerHom_natCast (2 * m) u hperiod 1

@[simp] theorem relationsHom_xa_zero (m : ℕ) [NeZero m]
    (u v : QuaternionGroup m) (hperiod : u ^ (2 * m) = 1)
    (hsquare : v ^ 2 = u ^ m) (hinvert : u * v = v * u⁻¹) :
    relationsHom m u v hperiod hsquare hinvert (xa 0) = v := by
  change v * coordinatePowerHom (2 * m) u hperiod 1 = v
  rw [map_one, mul_one]

@[simp] theorem relationsHom_centralHalf (m : ℕ) [NeZero m]
    (u v : QuaternionGroup m) (hperiod : u ^ (2 * m) = 1)
    (hsquare : v ^ 2 = u ^ m) (hinvert : u * v = v * u⁻¹) :
    relationsHom m u v hperiod hsquare hinvert (a (m : ZMod (2 * m))) = u ^ m := by
  exact coordinatePowerHom_natCast (2 * m) u hperiod m

theorem hom_ext {G : Type*} [Group G] (m : ℕ) [NeZero m]
    (f g : QuaternionGroup m →* G) (ha : f (a 1) = g (a 1))
    (hb : f (xa 0) = g (xa 0)) : f = g := by
  ext q
  cases q with
  | a i =>
    have heq : (a i : QuaternionGroup m) = a 1 ^ i.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val]
    rw [heq, map_pow, map_pow, ha]
  | xa i =>
    have heq : (xa i : QuaternionGroup m) = xa 0 * a 1 ^ i.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
    rw [heq, map_mul, map_mul, map_pow, map_pow, ha, hb]

theorem injective_of_projection_automorphism (m : ℕ) (hm : 2 ≤ m)
    (f : QuaternionGroup m →* QuaternionGroup m) (delta : MulAut (DihedralGroup m))
    (hprojection : ∀ q, dihedralProjection m (f q) = delta (dihedralProjection m q))
    (hhalf : f (a (m : ZMod (2 * m))) ≠ 1) : Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro q hq
  have hp : dihedralProjection m q = 1 := by
    apply delta.injective
    rw [← hprojection, hq, map_one, map_one]
  have hcenter : q ∈ Subgroup.center (QuaternionGroup m) := by
    rw [← dihedralProjection_ker m hm, MonoidHom.mem_ker]
    exact hp
  rcases (center_iff m hm q).mp hcenter with h | h
  · exact h
  · exact False.elim (hhalf (h ▸ hq))

theorem q8_relations : ∀ u v : QuaternionGroup 2,
    dihedralProjection 2 u ≠ 1 → dihedralProjection 2 v ≠ 1 →
    dihedralProjection 2 u ≠ dihedralProjection 2 v →
    u ^ 4 = 1 ∧ v ^ 2 = u ^ 2 ∧ u * v = v * u⁻¹ ∧ u ^ 2 ≠ 1 := by
  decide

theorem projection_relationsHom (m : ℕ) [NeZero m] (delta : MulAut (DihedralGroup m))
    (u v : QuaternionGroup m) (hperiod : u ^ (2 * m) = 1)
    (hsquare : v ^ 2 = u ^ m) (hinvert : u * v = v * u⁻¹)
    (hu : dihedralProjection m u = delta (DihedralGroup.r 1))
    (hv : dihedralProjection m v = delta (DihedralGroup.sr 0)) (q : QuaternionGroup m) :
    dihedralProjection m (relationsHom m u v hperiod hsquare hinvert q) =
      delta (dihedralProjection m q) := by
  have h := hom_ext m ((dihedralProjection m).comp
    (relationsHom m u v hperiod hsquare hinvert))
    (delta.toMonoidHom.comp (dihedralProjection m))
    (by
      change dihedralProjection m (relationsHom m u v hperiod hsquare hinvert (a 1)) =
        delta (dihedralProjection m (a 1))
      simpa only [relationsHom_a_one, dihedralProjection_a, map_one] using hu)
    (by
      change dihedralProjection m (relationsHom m u v hperiod hsquare hinvert (xa 0)) =
        delta (dihedralProjection m (xa 0))
      simpa only [relationsHom_xa_zero, dihedralProjection_xa, map_zero] using hv)
  exact DFunLike.congr_fun h q

theorem q8_dihedral_automorphism_lifts (delta : MulAut (DihedralGroup 2)) :
    ∃ beta : MulAut (QuaternionGroup 2), ∀ q,
      dihedralProjection 2 (beta q) = delta (dihedralProjection 2 q) := by
  classical
  obtain ⟨u, hu⟩ := dihedralProjection_surjective 2 (delta (DihedralGroup.r 1))
  obtain ⟨v, hv⟩ := dihedralProjection_surjective 2 (delta (DihedralGroup.sr 0))
  have hu1 : dihedralProjection 2 u ≠ 1 := by
    rw [hu, ← map_one delta]
    exact fun h => (by decide : (DihedralGroup.r 1 : DihedralGroup 2) ≠ 1)
      (delta.injective h)
  have hv1 : dihedralProjection 2 v ≠ 1 := by
    rw [hv, ← map_one delta]
    exact fun h => (by decide : (DihedralGroup.sr 0 : DihedralGroup 2) ≠ 1)
      (delta.injective h)
  have huv : dihedralProjection 2 u ≠ dihedralProjection 2 v := by
    rw [hu, hv]
    exact fun h => (by decide : (DihedralGroup.r 1 : DihedralGroup 2) ≠ DihedralGroup.sr 0)
      (delta.injective h)
  obtain ⟨hperiod, hsquare, hinvert, hhalf⟩ := q8_relations u v hu1 hv1 huv
  let f := relationsHom 2 u v hperiod hsquare hinvert
  have hf : ∀ q, dihedralProjection 2 (f q) = delta (dihedralProjection 2 q) :=
    projection_relationsHom 2 delta u v hperiod hsquare hinvert hu hv
  have hinj : Function.Injective f := injective_of_projection_automorphism 2 (by decide) f delta
    hf (by simpa only [f, relationsHom_centralHalf] using hhalf)
  exact ⟨MulEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

theorem dihedral_rotation_formula (m : ℕ) [NeZero m] (delta : MulAut (DihedralGroup m))
    (r : ZMod m) (hr : delta (DihedralGroup.r 1) = DihedralGroup.r r) (i : ZMod m) :
    delta (DihedralGroup.r i) = DihedralGroup.r (r * i) := by
  have heq : (DihedralGroup.r i : DihedralGroup m) = DihedralGroup.r 1 ^ i.val := by
    rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  rw [heq, map_pow, hr, DihedralGroup.r_pow, ZMod.natCast_zmod_val]

theorem dihedral_rotation_image (m : ℕ) (hm : 3 ≤ m) (delta : MulAut (DihedralGroup m)) :
    ∃ r : ZMod m, delta (DihedralGroup.r 1) = DihedralGroup.r r := by
  cases h : delta (DihedralGroup.r 1) with
  | r r => exact ⟨r, rfl⟩
  | sr s =>
    have ho := delta.orderOf_eq (DihedralGroup.r 1)
    rw [h, DihedralGroup.orderOf_sr, DihedralGroup.orderOf_r_one] at ho
    omega

theorem dihedral_reflection_image (m : ℕ) (hm : 3 ≤ m) (delta : MulAut (DihedralGroup m)) :
    ∃ s : ZMod m, delta (DihedralGroup.sr 0) = DihedralGroup.sr s := by
  let : NeZero m := ⟨by omega⟩
  cases h : delta (DihedralGroup.sr 0) with
  | r r =>
    obtain ⟨t, ht⟩ := dihedral_rotation_image m hm delta.symm
    have heq := dihedral_rotation_formula m delta.symm t ht r
    rw [← h, delta.symm_apply_apply] at heq
    cases heq
  | sr s => exact ⟨s, rfl⟩

theorem dihedral_rotation_coprime (m : ℕ) (hm : 0 < m)
    (delta : MulAut (DihedralGroup m)) (r : ZMod m)
    (hr : delta (DihedralGroup.r 1) = DihedralGroup.r r) : m.Coprime r.val := by
  let : NeZero m := ⟨by omega⟩
  have ho := delta.orderOf_eq (DihedralGroup.r 1)
  rw [hr, DihedralGroup.orderOf_r, DihedralGroup.orderOf_r_one] at ho
  exact (Nat.div_eq_self.mp ho).resolve_left (by omega)

theorem rotation_inv (m : ℕ) (i : ZMod (2 * m)) :
    (a i : QuaternionGroup m)⁻¹ = a (-i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [a_mul_a, add_neg_cancel, a_zero]

theorem odd_mul_half (m k : ℕ) (hk : Odd k) :
    (k : ZMod (2 * m)) * m = m := by
  obtain ⟨j, rfl⟩ := hk.exists_bit1
  push_cast
  have h := half_add_half m
  linear_combination (j : ZMod (2 * m)) * h

theorem higher_dihedral_automorphism_lifts (k : ℕ) (hk : 2 ≤ k)
    (delta : MulAut (DihedralGroup (2 ^ k))) :
    ∃ beta : MulAut (QuaternionGroup (2 ^ k)), ∀ q,
      dihedralProjection (2 ^ k) (beta q) = delta (dihedralProjection (2 ^ k) q) := by
  classical
  let m := 2 ^ k
  have hm : 4 ≤ m := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let : NeZero m := ⟨by omega⟩
  change MulAut (DihedralGroup m) at delta
  obtain ⟨r, hr⟩ := dihedral_rotation_image m (by omega) delta
  obtain ⟨s, hs⟩ := dihedral_reflection_image m (by omega) delta
  have hcop := dihedral_rotation_coprime m (by omega) delta r hr
  have hdiv : 2 ∣ m := by
    change 2 ∣ 2 ^ k
    simpa only [pow_one] using Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
  have hodd : Odd r.val := Nat.coprime_two_left.mp (hcop.of_dvd_left hdiv)
  let u : QuaternionGroup m := a (r.val : ZMod (2 * m))
  let v : QuaternionGroup m := xa (s.val : ZMod (2 * m))
  have hperiod : u ^ (2 * m) = 1 := by
    change a (r.val : ZMod (2 * m)) ^ (2 * m) = 1
    rw [rotation_pow, ZMod.natCast_self, mul_zero, a_zero]
  have hum : u ^ m = a (m : ZMod (2 * m)) := by
    change a (r.val : ZMod (2 * m)) ^ m = a (m : ZMod (2 * m))
    rw [rotation_pow, odd_mul_half m r.val hodd]
  have hsquare : v ^ 2 = u ^ m := by
    change xa (s.val : ZMod (2 * m)) ^ 2 = u ^ m
    rw [xa_sq, hum]
  have hinvert : u * v = v * u⁻¹ := by
    simp only [u, v, rotation_inv, a_mul_xa, xa_mul_a, sub_eq_add_neg]
  have hu : dihedralProjection m u = delta (DihedralGroup.r 1) := by
    simpa only [u, dihedralProjection_a, reduceCoordinate_natCast, ZMod.natCast_zmod_val] using hr.symm
  have hv : dihedralProjection m v = delta (DihedralGroup.sr 0) := by
    simpa only [v, dihedralProjection_xa, reduceCoordinate_natCast, ZMod.natCast_zmod_val] using hs.symm
  let f := relationsHom m u v hperiod hsquare hinvert
  have hf : ∀ q, dihedralProjection m (f q) = delta (dihedralProjection m q) :=
    projection_relationsHom m delta u v hperiod hsquare hinvert hu hv
  have hinj : Function.Injective f := injective_of_projection_automorphism m (by omega) f delta
    hf (by
      change relationsHom m u v hperiod hsquare hinvert (a (m : ZMod (2 * m))) ≠ 1
      rw [relationsHom_centralHalf, hum]
      exact centralHalf_ne_one m (by omega))
  exact ⟨MulEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

theorem dihedral_automorphism_lifts (k : ℕ) (hk : 1 ≤ k)
    (delta : MulAut (DihedralGroup (2 ^ k))) :
    ∃ beta : MulAut (QuaternionGroup (2 ^ k)), ∀ q,
      dihedralProjection (2 ^ k) (beta q) = delta (dihedralProjection (2 ^ k) q) := by
  by_cases h : k = 1
  · subst k
    exact q8_dihedral_automorphism_lifts delta
  · exact higher_dihedral_automorphism_lifts k (by omega) delta

theorem center_quotient_automorphism_lifts (n : ℕ) (hn : 3 ≤ n)
    (delta : MulAut (QuaternionGroup (2 ^ (n - 2)) ⧸
      Subgroup.center (QuaternionGroup (2 ^ (n - 2))))) :
    ∃ beta : MulAut (QuaternionGroup (2 ^ (n - 2))), ∀ q,
      QuotientGroup.mk' (Subgroup.center (QuaternionGroup (2 ^ (n - 2)))) (beta q) =
        delta (QuotientGroup.mk' (Subgroup.center (QuaternionGroup (2 ^ (n - 2)))) q) := by
  have hm : 2 ≤ 2 ^ (n - 2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ n - 2)
  let e := centerQuotientEquivDihedral (2 ^ (n - 2)) hm
  let d : MulAut (DihedralGroup (2 ^ (n - 2))) := e.symm.trans (delta.trans e)
  obtain ⟨beta, hbeta⟩ := dihedral_automorphism_lifts (n - 2) (by omega) d
  refine ⟨beta, fun q => e.injective ?_⟩
  rw [centerQuotientEquivDihedral_mk]
  rw [hbeta]
  change e (delta (e.symm (dihedralProjection (2 ^ (n - 2)) q))) =
    e (delta (QuotientGroup.mk' (Subgroup.center _) q))
  rw [← centerQuotientEquivDihedral_mk (2 ^ (n - 2)) hm q]
  rw [show e.symm (e (QuotientGroup.mk' (Subgroup.center _) q)) =
    QuotientGroup.mk' (Subgroup.center _) q from e.symm_apply_apply _]

theorem center_quotient_automorphism_lifts_of_equiv {S : Type*} [Group S]
    (n : ℕ) (hn : 3 ≤ n) (e : QuaternionGroup (2 ^ (n - 2)) ≃* S)
    (delta : MulAut (S ⧸ Subgroup.center S)) :
    ∃ beta : MulAut S, ∀ s,
      QuotientGroup.mk' (Subgroup.center S) (beta s) =
        delta (QuotientGroup.mk' (Subgroup.center S) s) := by
  let c : QuaternionGroup (2 ^ (n - 2)) ⧸ Subgroup.center _ ≃* S ⧸ Subgroup.center S :=
    QuotientGroup.congr (Subgroup.center _) (Subgroup.center S) e (Subgroup.map_center_eq e)
  let d := c.trans (delta.trans c.symm)
  obtain ⟨b, hb⟩ := center_quotient_automorphism_lifts n hn d
  refine ⟨e.symm.trans (b.trans e), fun s => ?_⟩
  change QuotientGroup.mk' (Subgroup.center S) (e (b (e.symm s))) =
    delta (QuotientGroup.mk' (Subgroup.center S) s)
  rw [← QuotientGroup.congr_mk' (Subgroup.center _) (Subgroup.center S) e
    (Subgroup.map_center_eq e)]
  change c (QuotientGroup.mk' (Subgroup.center _) (b (e.symm s))) = _
  rw [hb]
  change c (c.symm (delta (c (QuotientGroup.mk' (Subgroup.center _) (e.symm s))))) = _
  rw [c.apply_symm_apply]
  change delta (QuotientGroup.congr (Subgroup.center _) (Subgroup.center S) e
    (Subgroup.map_center_eq e) (QuotientGroup.mk' (Subgroup.center _) (e.symm s))) = _
  rw [QuotientGroup.congr_mk', e.apply_symm_apply]

theorem surjection_automorphism_lifts {S P : Type*} [Group S] [Group P]
    (n : ℕ) (hn : 3 ≤ n) (e : QuaternionGroup (2 ^ (n - 2)) ≃* S)
    (pi : S →* P) (hpi : Function.Surjective pi) (hker : pi.ker = Subgroup.center S)
    (delta : MulAut P) : ∃ beta : MulAut S, ∀ s, pi (beta s) = delta (pi s) := by
  let c : S ⧸ Subgroup.center S ≃* P :=
    QuotientGroup.liftEquiv (Subgroup.center S) hpi hker.symm
  have hc (s : S) : c (QuotientGroup.mk' (Subgroup.center S) s) = pi s :=
    QuotientGroup.liftEquiv_mk _ _ _ _
  let d := c.trans (delta.trans c.symm)
  obtain ⟨b, hb⟩ := center_quotient_automorphism_lifts_of_equiv n hn e d
  refine ⟨b, fun s => ?_⟩
  have h := congrArg c (hb s)
  change c (QuotientGroup.mk' (Subgroup.center S) (b s)) =
    c (c.symm (delta (c (QuotientGroup.mk' (Subgroup.center S) s)))) at h
  rw [c.apply_symm_apply] at h
  rw [hc, hc] at h
  exact h

theorem unique_involution (m : ℕ) (hm : 0 < m) (q : QuaternionGroup m) :
    orderOf q = 2 ↔ q = a (m : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  constructor
  · intro h
    cases q with
    | a i =>
      have hs : (a i : QuaternionGroup m) ^ 2 = 1 := by
        rw [← h]
        exact pow_orderOf_eq_one _
      rw [pow_two, a_mul_a, QuaternionGroup.one_def, a.injEq] at hs
      rcases (twice_eq_zero_iff m i).mp hs with hi | hi
      · rw [hi, a_zero, orderOf_one] at h
        omega
      · exact congrArg a hi
    | xa i =>
      rw [orderOf_xa] at h
      omega
  · rintro rfl
    exact orderOf_eq_prime (centralHalf_sq m) (centralHalf_ne_one m hm)

theorem center_card (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (Subgroup.center (QuaternionGroup m)) = 2 := by
  have hset : (Subgroup.center (QuaternionGroup m) : Set (QuaternionGroup m)) =
      {1, a (m : ZMod (2 * m))} := by
    ext q
    exact center_iff m hm q
  change Nat.card ↥(Subgroup.center (QuaternionGroup m) : Set (QuaternionGroup m)) = 2
  rw [Nat.card_coe_set_eq, hset]
  exact Set.ncard_pair (centralHalf_ne_one m (by omega)).symm

theorem automorphism_fixes_centralHalf (m : ℕ) (hm : 0 < m)
    (beta : MulAut (QuaternionGroup m)) : beta (a (m : ZMod (2 * m))) = a (m : ZMod (2 * m)) := by
  apply (unique_involution m hm _).mp
  rw [beta.orderOf_eq]
  exact (unique_involution m hm _).mpr rfl

theorem center_quotient_automorphism_lifts_int (n : ℤ) (hn : 3 ≤ n)
    (delta : MulAut (QuaternionGroup (2 ^ (n.toNat - 2)) ⧸
      Subgroup.center (QuaternionGroup (2 ^ (n.toNat - 2))))) :
    ∃ beta : MulAut (QuaternionGroup (2 ^ (n.toNat - 2))), ∀ q,
      QuotientGroup.mk' (Subgroup.center (QuaternionGroup (2 ^ (n.toNat - 2)))) (beta q) =
        delta (QuotientGroup.mk' (Subgroup.center (QuaternionGroup (2 ^ (n.toNat - 2)))) q) := by
  exact center_quotient_automorphism_lifts n.toNat (by omega) delta

end CFSG.Semidihedral.QuaternionAutomorphismLifting
