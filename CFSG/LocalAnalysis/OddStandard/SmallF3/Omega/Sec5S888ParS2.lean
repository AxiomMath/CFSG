module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Q

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma par_s2_map_mul {K : Subgroup G} (e : ↥K ≃* SL23) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : e ⟨x * y, K.mul_mem hx hy⟩ = e ⟨x, hx⟩ * e ⟨y, hy⟩ :=
  map_mul e ⟨x, hx⟩ ⟨y, hy⟩

private lemma par_s2_iso_z_eq_neg_one (hq : Sec5B517Quad K z) {i : Fin 4}
    (e : ↥(K i) ≃* SL23) : e ⟨z, hq.z_mem i⟩ = -1 := by
  have hsq : e ⟨z, hq.z_mem i⟩ * e ⟨z, hq.z_mem i⟩ = 1 := by
    rw [← map_mul]
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) * ⟨z, hq.z_mem i⟩ = 1 :=
      Subtype.ext (by simpa using hq.z_sq)
    rw [hsub, map_one]
  rcases sl23_unique_involution _ hsq with h1 | hneg
  · exfalso
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := e.injective (by rw [h1, map_one])
    exact hq.z_ne (congrArg Subtype.val hsub)
  · exact hneg

private lemma par_s2_map_mul_z (hq : Sec5B517Quad K z) {i : Fin 4} (e : ↥(K i) ≃* SL23)
    {x : G} (hx : x ∈ K i) :
    e ⟨x * z, (K i).mul_mem hx (hq.z_mem i)⟩ = - e ⟨x, hx⟩ := by
  rw [par_s2_map_mul e hx (hq.z_mem i), par_s2_iso_z_eq_neg_one hq e, mul_neg, mul_one]

private lemma par_s2_map_conj {K : Subgroup G} (e : ↥K ≃* SL23) {k a : G} (hk : k ∈ K)
    (ha : a ∈ K) :
    e ⟨k * a * k⁻¹, K.mul_mem (K.mul_mem hk ha) (K.inv_mem hk)⟩ =
      e ⟨k, hk⟩ * e ⟨a, ha⟩ * (e ⟨k, hk⟩)⁻¹ := by
  rw [par_s2_map_mul e (K.mul_mem hk ha) (K.inv_mem hk), par_s2_map_mul e hk ha,
    show e ⟨k⁻¹, K.inv_mem hk⟩ = (e ⟨k, hk⟩)⁻¹ from map_inv e ⟨k, hk⟩]

private lemma par_s2_map_one {K : Subgroup G} (e : ↥K ≃* SL23) :
    e ⟨1, K.one_mem⟩ = 1 :=
  map_one e

private lemma par_s2_eq_iff {K : Subgroup G} (e : ↥K ≃* SL23) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : x = y ↔ e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
  ⟨fun h => congrArg e (Subtype.ext h), fun h => congrArg Subtype.val (e.injective h)⟩

private lemma par_s2_apply_symm_coe {K : Subgroup G} (e : ↥K ≃* SL23) (y : SL23) :
    e ⟨((e.symm y : ↥K) : G), (e.symm y).2⟩ = y :=
  e.apply_symm_apply y

private lemma par_s2_sq_eq_z_iff (hq : Sec5B517Quad K z) {i : Fin 4} (e : ↥(K i) ≃* SL23)
    {x : G} (hx : x ∈ K i) : x * x = z ↔ e ⟨x, hx⟩ * e ⟨x, hx⟩ = -1 := by
  rw [par_s2_eq_iff e ((K i).mul_mem hx hx) (hq.z_mem i), par_s2_map_mul e hx hx,
    par_s2_iso_z_eq_neg_one hq e]

private lemma par_s2_pow4_iff {K : Subgroup G} (e : ↥K ≃* SL23) {x : G} (hx : x ∈ K) :
    x ^ 4 = 1 ↔ (e ⟨x, hx⟩) ^ 4 = 1 := by
  constructor
  · intro h
    have hsub : (⟨x, hx⟩ : ↥K) ^ 4 = 1 := Subtype.ext (by simpa using h)
    rw [← map_pow, hsub, map_one]
  · intro h
    have hsub : (⟨x, hx⟩ : ↥K) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h, map_one]
    simpa using congrArg Subtype.val hsub

private lemma par_s2_ne_neg_of_ne (hq : Sec5B517Quad K z) {i : Fin 4} (e : ↥(K i) ≃* SL23)
    {a b : G} (ha : a ∈ K i) (hb : b ∈ K i) (hba : b ≠ a * z) :
    e ⟨b, hb⟩ ≠ - e ⟨a, ha⟩ := fun h =>
  hba ((par_s2_eq_iff e hb ((K i).mul_mem ha (hq.z_mem i))).mpr (by
    rw [par_s2_map_mul_z hq e ha]; exact h))

theorem par_exists_conj_class (hq : Sec5B517Quad K z) (i : Fin 4) {a b : G} (ha : a ∈ K i)
    (hb : b ∈ K i) (ha2 : a * a = z) (hb2 : b * b = z) :
    ∃ k ∈ K i, k * a * k⁻¹ = b ∨ k * a * k⁻¹ = b * z := by
  obtain ⟨e⟩ := hq.iso i
  have ha2' : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := (par_s2_sq_eq_z_iff hq e ha).mp ha2
  have hb2' : e ⟨b, hb⟩ * e ⟨b, hb⟩ = -1 := (par_s2_sq_eq_z_iff hq e hb).mp hb2
  obtain ⟨k', hk'⟩ := par_sl23_trans (e ⟨a, ha⟩) (e ⟨b, hb⟩) ha2' hb2'
  refine ⟨((e.symm k' : ↥(K i)) : G), (e.symm k').2, ?_⟩
  rcases hk' with hk' | hk'
  · left
    apply (par_s2_eq_iff e ((K i).mul_mem ((K i).mul_mem (e.symm k').2 ha)
      ((K i).inv_mem (e.symm k').2)) hb).mpr
    rw [par_s2_map_conj e (e.symm k').2 ha, par_s2_apply_symm_coe e k']
    exact hk'
  · right
    apply (par_s2_eq_iff e ((K i).mul_mem ((K i).mul_mem (e.symm k').2 ha)
      ((K i).inv_mem (e.symm k').2)) ((K i).mul_mem hb (hq.z_mem i))).mpr
    rw [par_s2_map_conj e (e.symm k').2 ha, par_s2_map_mul_z hq e hb,
      par_s2_apply_symm_coe e k']
    exact hk'

theorem par_conj_ne_of_not_q8 (hq : Sec5B517Quad K z) (i : Fin 4) {k a : G} (hk : k ∈ K i)
    (ha : a ∈ K i) (ha2 : a * a = z) (hk4 : k ^ 4 ≠ 1) :
    k * a * k⁻¹ ≠ a ∧ k * a * k⁻¹ ≠ a * z := by
  obtain ⟨e⟩ := hq.iso i
  have hk4' : (e ⟨k, hk⟩) ^ 4 ≠ 1 := fun h => hk4 ((par_s2_pow4_iff e hk).mpr h)
  have ha2' : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := (par_s2_sq_eq_z_iff hq e ha).mp ha2
  have hfx := par_sl23_fixfree (e ⟨k, hk⟩) (e ⟨a, ha⟩) ha2' hk4'
  constructor
  · intro h
    apply hfx.1
    rw [← par_s2_map_conj e hk ha]
    exact congrArg e (Subtype.ext h)
  · intro h
    apply hfx.2
    rw [← par_s2_map_conj e hk ha]
    exact (congrArg e (Subtype.ext h)).trans (par_s2_map_mul_z hq e ha)

theorem par_sq_not_q8 (hq : Sec5B517Quad K z) (i : Fin 4) {k : G} (hk : k ∈ K i)
    (hk4 : k ^ 4 ≠ 1) : (k * k) ^ 4 ≠ 1 := by
  obtain ⟨e⟩ := hq.iso i
  have hk4' : (e ⟨k, hk⟩) ^ 4 ≠ 1 := fun h => hk4 ((par_s2_pow4_iff e hk).mpr h)
  intro h
  apply par_sl23_sq_not_q8 (e ⟨k, hk⟩) hk4'
  rw [← par_s2_map_mul e hk hk]
  exact (par_s2_pow4_iff e ((K i).mul_mem hk hk)).mp h

theorem par_pow4_of_conj_mod (hq : Sec5B517Quad K z) (i : Fin 4) {x : G} (hx : x ∈ K i)
    (h : ∀ q ∈ K i, q ^ 4 = 1 → x * q * x⁻¹ = q ∨ x * q * x⁻¹ = q * z) : x ^ 4 = 1 := by
  obtain ⟨e⟩ := hq.iso i
  refine (par_s2_pow4_iff e hx).mpr ?_
  refine par_sl23_kernel (e ⟨x, hx⟩) ?_
  intro q' hq'4
  obtain ⟨q, rfl⟩ := e.surjective q'
  have hq4 : ((q : ↥(K i)) : G) ^ 4 = 1 :=
    (par_s2_pow4_iff e q.2).mpr hq'4
  rcases h ((q : ↥(K i)) : G) q.2 hq4 with hh | hh
  · left
    have heq : e ⟨x * ((q : ↥(K i)) : G) * x⁻¹,
        (K i).mul_mem ((K i).mul_mem hx q.2) ((K i).inv_mem hx)⟩ = e q :=
      congrArg e (Subtype.ext hh)
    rw [par_s2_map_conj e hx q.2] at heq
    exact heq
  · right
    have heq : e ⟨x * ((q : ↥(K i)) : G) * x⁻¹,
        (K i).mul_mem ((K i).mul_mem hx q.2) ((K i).inv_mem hx)⟩
        = e ⟨((q : ↥(K i)) : G) * z, (K i).mul_mem q.2 (hq.z_mem i)⟩ :=
      congrArg e (Subtype.ext hh)
    rw [par_s2_map_conj e hx q.2, par_s2_map_mul_z hq e q.2] at heq
    exact heq

theorem par_conj_q8_mod (hq : Sec5B517Quad K z) (i : Fin 4) {x q : G} (hx : x ∈ K i)
    (hq' : q ∈ K i) (hx4 : x ^ 4 = 1) (hq4 : q ^ 4 = 1) :
    x * q * x⁻¹ = q ∨ x * q * x⁻¹ = q * z := by
  obtain ⟨e⟩ := hq.iso i
  have hx4' : (e ⟨x, hx⟩) ^ 4 = 1 := (par_s2_pow4_iff e hx).mp hx4
  have hq4' : (e ⟨q, hq'⟩) ^ 4 = 1 := (par_s2_pow4_iff e hq').mp hq4
  rcases par_sl23_q8_mod (e ⟨x, hx⟩) (e ⟨q, hq'⟩) hx4' hq4' with hh | hh
  · left
    apply (par_s2_eq_iff e ((K i).mul_mem ((K i).mul_mem hx hq') ((K i).inv_mem hx)) hq').mpr
    rw [par_s2_map_conj e hx hq']
    exact hh
  · right
    apply (par_s2_eq_iff e ((K i).mul_mem ((K i).mul_mem hx hq') ((K i).inv_mem hx))
      ((K i).mul_mem hq' (hq.z_mem i))).mpr
    rw [par_s2_map_conj e hx hq', par_s2_map_mul_z hq e hq']
    exact hh

theorem par_card_sq_eq_z (hq : Sec5B517Quad K z) (i : Fin 4) :
    Nat.card {x : G // x ∈ K i ∧ x * x = z} = 6 := by
  obtain ⟨e⟩ := hq.iso i
  rw [← par_sl23_card_sq]
  let f : {x : G // x ∈ K i ∧ x * x = z} → {y : SL23 // y * y = -1} :=
    fun x => ⟨e ⟨x.1, x.2.1⟩, (par_s2_sq_eq_z_iff hq e x.2.1).mp x.2.2⟩
  let g : {y : SL23 // y * y = -1} → {x : G // x ∈ K i ∧ x * x = z} :=
    fun y => ⟨((e.symm y.1 : ↥(K i)) : G), (e.symm y.1).2,
      (par_s2_sq_eq_z_iff hq e (e.symm y.1).2).mpr (by
        rw [par_s2_apply_symm_coe e y.1]; exact y.2)⟩
  refine Nat.card_congr { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply Subtype.ext
    simp [f, g]
  · intro y
    apply Subtype.ext
    simp [f, g, par_s2_apply_symm_coe]

theorem par_mem_q8_decomp (hq : Sec5B517Quad K z) (i : Fin 4) {a b x : G} (ha : a ∈ K i)
    (hb : b ∈ K i) (ha2 : a * a = z) (hb2 : b * b = z) (hba : b ≠ a) (hba' : b ≠ a * z)
    (hx : x ∈ K i) (hx4 : x ^ 4 = 1) :
    x = 1 ∨ x = z ∨ x = a ∨ x = a * z ∨ x = b ∨ x = b * z ∨ x = a * b ∨ x = a * b * z := by
  obtain ⟨e⟩ := hq.iso i
  have ha2' : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := (par_s2_sq_eq_z_iff hq e ha).mp ha2
  have hb2' : e ⟨b, hb⟩ * e ⟨b, hb⟩ = -1 := (par_s2_sq_eq_z_iff hq e hb).mp hb2
  have hx4' : (e ⟨x, hx⟩) ^ 4 = 1 := (par_s2_pow4_iff e hx).mp hx4
  have hbne : e ⟨b, hb⟩ ≠ e ⟨a, ha⟩ := fun h => hba ((par_s2_eq_iff e hb ha).mpr h)
  have hbne' : e ⟨b, hb⟩ ≠ - e ⟨a, ha⟩ := par_s2_ne_neg_of_ne hq e ha hb hba'
  rcases par_sl23_decomp (e ⟨a, ha⟩) (e ⟨b, hb⟩) (e ⟨x, hx⟩) ha2' hb2' hbne hbne' hx4' with
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · left
    exact (par_s2_eq_iff e hx (K i).one_mem).mpr (by rw [h1, par_s2_map_one e])
  · right; left
    exact (par_s2_eq_iff e hx (hq.z_mem i)).mpr (by rw [h1, par_s2_iso_z_eq_neg_one hq e])
  · right; right; left
    exact (par_s2_eq_iff e hx ha).mpr h1
  · right; right; right; left
    exact (par_s2_eq_iff e hx ((K i).mul_mem ha (hq.z_mem i))).mpr (by
      rw [par_s2_map_mul_z hq e ha]; exact h1)
  · right; right; right; right; left
    exact (par_s2_eq_iff e hx hb).mpr h1
  · right; right; right; right; right; left
    exact (par_s2_eq_iff e hx ((K i).mul_mem hb (hq.z_mem i))).mpr (by
      rw [par_s2_map_mul_z hq e hb]; exact h1)
  · right; right; right; right; right; right; left
    exact (par_s2_eq_iff e hx ((K i).mul_mem ha hb)).mpr (by
      rw [par_s2_map_mul e ha hb]; exact h1)
  · right; right; right; right; right; right; right
    exact (par_s2_eq_iff e hx ((K i).mul_mem ((K i).mul_mem ha hb) (hq.z_mem i))).mpr (by
      rw [par_s2_map_mul_z hq e ((K i).mul_mem ha hb), par_s2_map_mul e ha hb]; exact h1)

theorem par_exists_other_sq (hq : Sec5B517Quad K z) (i : Fin 4) {a : G} (ha : a ∈ K i)
    (ha2 : a * a = z) : ∃ b ∈ K i, b * b = z ∧ b ≠ a ∧ b ≠ a * z := by
  obtain ⟨e⟩ := hq.iso i
  have ha2' : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := (par_s2_sq_eq_z_iff hq e ha).mp ha2
  obtain ⟨b', hb'sq, hb'ne, hb'ne'⟩ := par_sl23_exists_other (e ⟨a, ha⟩) ha2'
  refine ⟨((e.symm b' : ↥(K i)) : G), (e.symm b').2, ?_, ?_, ?_⟩
  · exact (par_s2_sq_eq_z_iff hq e (e.symm b').2).mpr (by
      rw [par_s2_apply_symm_coe e b']; exact hb'sq)
  · intro h
    apply hb'ne
    exact (par_s2_apply_symm_coe e b').symm.trans (congrArg e (Subtype.ext h))
  · intro h
    apply hb'ne'
    exact ((par_s2_apply_symm_coe e b').symm.trans (congrArg e (Subtype.ext h))).trans
      (par_s2_map_mul_z hq e ha)

theorem par_anticomm_sq (hq : Sec5B517Quad K z) (i : Fin 4) {a b : G} (ha : a ∈ K i)
    (hb : b ∈ K i) (ha2 : a * a = z) (hb2 : b * b = z) (hba : b ≠ a) (hba' : b ≠ a * z) :
    b * a = a * b * z := by
  obtain ⟨e⟩ := hq.iso i
  have ha2' : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := (par_s2_sq_eq_z_iff hq e ha).mp ha2
  have hb2' : e ⟨b, hb⟩ * e ⟨b, hb⟩ = -1 := (par_s2_sq_eq_z_iff hq e hb).mp hb2
  have hbne : e ⟨b, hb⟩ ≠ e ⟨a, ha⟩ := fun h => hba ((par_s2_eq_iff e hb ha).mpr h)
  have hbne' : e ⟨b, hb⟩ ≠ - e ⟨a, ha⟩ := par_s2_ne_neg_of_ne hq e ha hb hba'
  apply (par_s2_eq_iff e ((K i).mul_mem hb ha)
    ((K i).mul_mem ((K i).mul_mem ha hb) (hq.z_mem i))).mpr
  rw [par_s2_map_mul e hb ha, par_s2_map_mul_z hq e ((K i).mul_mem ha hb),
    par_s2_map_mul e ha hb]
  exact par_sl23_anticomm (e ⟨a, ha⟩) (e ⟨b, hb⟩) ha2' hb2' hbne hbne'

end CFSG.OddStandard.SmallF3.Omega
