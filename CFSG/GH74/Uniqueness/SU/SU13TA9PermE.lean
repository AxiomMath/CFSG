module

public import CFSG.GH74.Uniqueness.SU.SU13TA9Perm
public import CFSG.GH74.Uniqueness.SU.SU13TA3PermE

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup

@[expose] def toP (i j k : Fin 3) : Perm (Fin 9) :=
  pa ^ (i : ℕ) * pb ^ (j : ℕ) * pc ^ (k : ℕ)

theorem apply_pow_of_commute {x c : Perm (Fin 9)} (h : Commute x c) (m : ℕ) (y : Fin 9) :
    x ((c ^ m) y) = (c ^ m) (x y) :=
  congrFun (congrArg (fun f : Perm (Fin 9) => (f : Fin 9 → Fin 9)) (h.pow_right m).eq) y

theorem exists_pow_of_commute {c x : Perm (Fin 9)} (S : Finset (Fin 9)) (b0 : Fin 9)
    (hfix : ∀ v, v ∉ S → c v = v) (hb0 : c b0 ≠ b0)
    (hS : ∀ v ∈ S, ∃ m : Fin 3, (c ^ (m : ℕ)) b0 = v) (h : Commute x c) :
    ∃ i : Fin 3, ∀ y ∈ S, x y = (c ^ (i : ℕ)) y := by
  have hxb0 : x b0 ∈ S := by
    by_contra hcon
    have h1 : c (x b0) = x b0 := hfix _ hcon
    have h2 := apply_pow_of_commute h 1 b0
    simp only [pow_one] at h2
    exact hb0 (x.injective (h2.trans h1))
  obtain ⟨i, hi⟩ := hS (x b0) hxb0
  refine ⟨i, fun y hy => ?_⟩
  obtain ⟨m, hm⟩ := hS y hy
  rw [← hm, apply_pow_of_commute h, ← hi, ← Perm.mul_apply, ← Perm.mul_apply, ← pow_add,
    ← pow_add, add_comm]

theorem toP_apply_a : ∀ i j k : Fin 3, ∀ y ∈ ({0, 1, 2} : Finset (Fin 9)),
    toP i j k y = (pa ^ (i : ℕ)) y := by decide

theorem toP_apply_b : ∀ i j k : Fin 3, ∀ y ∈ ({3, 4, 5} : Finset (Fin 9)),
    toP i j k y = (pb ^ (j : ℕ)) y := by decide

theorem toP_apply_c : ∀ i j k : Fin 3, ∀ y ∈ ({6, 7, 8} : Finset (Fin 9)),
    toP i j k y = (pc ^ (k : ℕ)) y := by decide

theorem exists_toP_of_commute {x : Perm (Fin 9)} (ha : Commute x pa) (hb : Commute x pb)
    (hc : Commute x pc) : ∃ i j k : Fin 3, x = toP i j k := by
  obtain ⟨i, hi⟩ := exists_pow_of_commute (c := pa) ({0, 1, 2} : Finset (Fin 9)) 0
    (by decide) (by decide) (by decide) ha
  obtain ⟨j, hj⟩ := exists_pow_of_commute (c := pb) ({3, 4, 5} : Finset (Fin 9)) 3
    (by decide) (by decide) (by decide) hb
  obtain ⟨k, hk⟩ := exists_pow_of_commute (c := pc) ({6, 7, 8} : Finset (Fin 9)) 6
    (by decide) (by decide) (by decide) hc
  refine ⟨i, j, k, Perm.ext fun y => ?_⟩
  have hy : y ∈ ({0, 1, 2} : Finset (Fin 9)) ∨ y ∈ ({3, 4, 5} : Finset (Fin 9)) ∨
      y ∈ ({6, 7, 8} : Finset (Fin 9)) := by
    revert y; decide
  rcases hy with hy | hy | hy
  · rw [hi y hy, toP_apply_a i j k y hy]
  · rw [hj y hy, toP_apply_b i j k y hy]
  · rw [hk y hy, toP_apply_c i j k y hy]

theorem toP_mul_pa : ∀ i j k : Fin 3, toP i j k * pa = pa * toP i j k := by decide

theorem toP_mul_pb : ∀ i j k : Fin 3, toP i j k * pb = pb * toP i j k := by decide

theorem toP_mul_pc : ∀ i j k : Fin 3, toP i j k * pc = pc * toP i j k := by decide

theorem pw_mul_toP : ∀ i j k : Fin 3, pw * toP i j k * pw⁻¹ = toP k i j := by decide

theorem toP_diag : ∀ i : Fin 3, toP i i i = (pa * pb * pc) ^ (i : ℕ) := by decide

theorem inj_a : ∀ i i' : Fin 3, (pa ^ (i : ℕ)) 0 = (pa ^ (i' : ℕ)) 0 → i = i' := by decide

theorem inj_b : ∀ j j' : Fin 3, (pb ^ (j : ℕ)) 3 = (pb ^ (j' : ℕ)) 3 → j = j' := by decide

theorem inj_c : ∀ k k' : Fin 3, (pc ^ (k : ℕ)) 6 = (pc ^ (k' : ℕ)) 6 → k = k' := by decide

theorem toP_injective {i j k i' j' k' : Fin 3} (h : toP i j k = toP i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have h0 := congrFun (congrArg (fun f : Perm (Fin 9) => (f : Fin 9 → Fin 9)) h) 0
  have h3 := congrFun (congrArg (fun f : Perm (Fin 9) => (f : Fin 9 → Fin 9)) h) 3
  have h6 := congrFun (congrArg (fun f : Perm (Fin 9) => (f : Fin 9 → Fin 9)) h) 6
  rw [toP_apply_a i j k 0 (by decide), toP_apply_a i' j' k' 0 (by decide)] at h0
  rw [toP_apply_b i j k 3 (by decide), toP_apply_b i' j' k' 3 (by decide)] at h3
  rw [toP_apply_c i j k 6 (by decide), toP_apply_c i' j' k' 6 (by decide)] at h6
  exact ⟨inj_a _ _ h0, inj_b _ _ h3, inj_c _ _ h6⟩

theorem sign_toP (i j k : Fin 3) : Perm.sign (toP i j k) = 1 := by
  rw [toP, map_mul, map_mul, map_pow, map_pow, map_pow, sign_pa, sign_pb, sign_pc]
  simp

@[expose] def toE (i j k : Fin 3) : alternatingGroup (Fin 9) :=
  ⟨toP i j k, Perm.mem_alternatingGroup.mpr (sign_toP i j k)⟩

@[expose] def Ebar : Subgroup (alternatingGroup (Fin 9)) :=
  centralizer ({ea, eb, ec} : Set (alternatingGroup (Fin 9)))

theorem mem_Ebar_iff {x : alternatingGroup (Fin 9)} :
    x ∈ Ebar ↔ Commute (x : Perm (Fin 9)) pa ∧ Commute (x : Perm (Fin 9)) pb ∧
      Commute (x : Perm (Fin 9)) pc := by
  rw [Ebar, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨(congrArg Subtype.val (hx ea (by simp))).symm, (congrArg Subtype.val (hx eb (by simp))).symm,
      (congrArg Subtype.val (hx ec (by simp))).symm⟩
  · rintro ⟨ha, hb, hc⟩ h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl
    · exact Subtype.ext ha.symm
    · exact Subtype.ext hb.symm
    · exact Subtype.ext hc.symm

theorem mem_Ebar_iff_toE {x : alternatingGroup (Fin 9)} :
    x ∈ Ebar ↔ ∃ i j k : Fin 3, x = toE i j k := by
  rw [mem_Ebar_iff]
  constructor
  · rintro ⟨ha, hb, hc⟩
    obtain ⟨i, j, k, h⟩ := exists_toP_of_commute ha hb hc
    exact ⟨i, j, k, Subtype.ext h⟩
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨(toP_mul_pa i j k : _), toP_mul_pb i j k, toP_mul_pc i j k⟩

theorem card_Ebar : Nat.card Ebar = 27 := by
  let f : Fin 3 × Fin 3 × Fin 3 → Ebar := fun p => ⟨toE p.1 p.2.1 p.2.2, mem_Ebar_iff_toE.mpr ⟨_, _, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
      have := toP_injective (congrArg (fun x : Ebar => ((x : alternatingGroup (Fin 9)) : Perm (Fin 9))) h)
      obtain ⟨h1, h2, h3⟩ := this
      exact Prod.ext h1 (Prod.ext h2 h3)
    · rintro ⟨x, hx⟩
      obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
      exact ⟨(i, j, k), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem Ebar_comm : ∀ x ∈ Ebar, ∀ y ∈ Ebar, Commute x y := by
  intro x hx y hy
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
  obtain ⟨i', j', k', rfl⟩ := mem_Ebar_iff_toE.mp hy
  refine Subtype.ext ?_
  have ha : Commute (toP i j k) pa := toP_mul_pa i j k
  have hb : Commute (toP i j k) pb := toP_mul_pb i j k
  have hc : Commute (toP i j k) pc := toP_mul_pc i j k
  exact (((ha.pow_right i').mul_right (hb.pow_right j')).mul_right (hc.pow_right k')).eq

theorem ea_mem_Ebar : ea ∈ Ebar := mem_Ebar_iff.mpr ⟨Commute.refl _, by
  exact (Subtype.ext_iff.mp (commute_ea_eb.eq)), by exact (Subtype.ext_iff.mp (commute_ea_ec.eq))⟩

theorem ec_mem_Ebar : ec ∈ Ebar := mem_Ebar_iff.mpr ⟨by
  exact (Subtype.ext_iff.mp (commute_ea_ec.symm.eq)), by exact (Subtype.ext_iff.mp (commute_eb_ec.symm.eq)),
  Commute.refl _⟩

theorem eb_mem_Ebar : eb ∈ Ebar := mem_Ebar_iff.mpr ⟨by
  exact (Subtype.ext_iff.mp (commute_ea_eb.symm.eq)), Commute.refl _, by
  exact (Subtype.ext_iff.mp (commute_eb_ec.eq))⟩

theorem centralizer_Ebar : centralizer (Ebar : Set (alternatingGroup (Fin 9))) = Ebar := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.centralizer_le (s := ({ea, eb, ec} : Set (alternatingGroup (Fin 9))))
      (t := (Ebar : Set (alternatingGroup (Fin 9)))) ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ea_mem_Ebar
    · exact eb_mem_Ebar
    · exact ec_mem_Ebar
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Ebar_comm y hy x hx).eq

@[expose] def Pst : Subgroup (alternatingGroup (Fin 9)) :=
  centralizer ({ea * eb * ec} : Set (alternatingGroup (Fin 9)))

theorem card_Pst : Nat.card Pst = 81 := card_centralizer_ea_mul_eb_mul_ec

theorem Ebar_le_Pst : Ebar ≤ Pst := by
  intro x hx
  obtain ⟨ha, hb, hc⟩ := mem_Ebar_iff.mp hx
  rw [Pst, Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (((ha.mul_right hb).mul_right hc).eq)

theorem ew_mem_Pst : ew ∈ Pst := by
  rw [Pst, Subgroup.mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  show pw * (pa * pb * pc) = pa * pb * pc * pw
  decide

theorem Ebar_inf_centralizer_ew_le :
    Ebar ⊓ centralizer ({ew} : Set (alternatingGroup (Fin 9))) ≤ zpowers (ea * eb * ec) := by
  rintro x ⟨hxE, hxw⟩
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hxE
  have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hxw)
  have hcomm : pw * toP i j k * pw⁻¹ = toP i j k := by
    have : toP i j k * pw = pw * toP i j k := hc
    rw [← this]
    group
  rw [pw_mul_toP] at hcomm
  obtain ⟨h1, h2, h3⟩ := toP_injective hcomm
  subst h1
  subst h2
  refine ⟨(k : ℤ), ?_⟩
  refine Subtype.ext ?_
  show ((ea * eb * ec : alternatingGroup (Fin 9)) ^ (k : ℤ) : alternatingGroup (Fin 9)).val = toP k k k
  rw [zpow_natCast, Subgroup.coe_pow]
  exact (toP_diag k).symm

theorem card_zpowers_g : Nat.card (zpowers (ea * eb * ec)) = 3 := by
  rw [Nat.card_zpowers]
  have h3 : (ea * eb * ec) ^ 3 = 1 := by
    rw [(commute_ea_ec.mul_left commute_eb_ec).mul_pow, (commute_ea_eb).mul_pow, ea_pow_three,
      eb_pow_three, ec_pow_three]
    simp
  have hne : ea * eb * ec ≠ 1 := fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
    revert this
    decide
  exact orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) h3 hne

theorem eq_Ebar_of_abelian_card_27 {B : Subgroup (alternatingGroup (Fin 9))} (hBP : B ≤ Pst)
    (hab : ∀ x ∈ B, ∀ y ∈ B, Commute x y) (hcard : Nat.card B = 27) : B = Ebar := by
  refine L10.eq_of_abelian_card_27 Ebar_le_Pst hBP card_Pst card_Ebar hcard Ebar_comm hab ?_
  intro S hSE hSc
  have hSle : S ≤ zpowers (ea * eb * ec) := fun b hb =>
    Ebar_inf_centralizer_ew_le ⟨hSE hb, Subgroup.mem_centralizer_singleton_iff.mpr
      (hSc b hb ew ew_mem_Pst).eq⟩
  calc Nat.card S ≤ Nat.card (zpowers (ea * eb * ec)) := Subgroup.card_le_of_le hSle
    _ = 3 := card_zpowers_g

theorem pt_mul_toP : ∀ i j k : Fin 3, pt * toP i j k * pt⁻¹ = toP j i (-k) := by decide

theorem px_mul_toP : ∀ i j k : Fin 3, px * toP i j k * px⁻¹ = toP (-j) (-i) (-k) := by decide

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
