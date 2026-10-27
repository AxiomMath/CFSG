module

public import CFSG.LargeExtraspecial.S111TWt
public import CFSG.LargeExtraspecial.S111CNorm
public import CFSG.LargeExtraspecial.S111AStar
public import CFSG.LargeExtraspecial.S111ATrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

variable (S) in
structure Ord3 (k : G) (m : S.M) : Prop where
  cube : S.ρ m ^ 3 = 1
  ne_one : S.ρ m ≠ 1
  dich : ∀ s ∈ S.Lbar k, s * S.ρ m * s⁻¹ = S.ρ m ∨ s * S.ρ m * s⁻¹ = (S.ρ m)⁻¹
  inv : ∃ s ∈ S.Lbar k, s * S.ρ m * s⁻¹ = (S.ρ m)⁻¹

namespace Ord3

variable {k : G} {m : S.M}

theorem inv_eq (W : Ord3 S k m) : (S.ρ m)⁻¹ = S.ρ m * S.ρ m := by
  have h := W.cube
  rw [pow_three] at h
  exact inv_eq_of_mul_eq_one_right h

theorem apply_apply_apply (W : Ord3 S k m) (v : S.Qt) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v := by
  rw [← coe_mul_apply, ← coe_mul_apply, ← pow_three', W.cube]
  rfl

theorem commute_of_conj_eq {s : S.O} (e : s * S.ρ m * s⁻¹ = S.ρ m) :
    s * S.ρ m = S.ρ m * s := by
  calc s * S.ρ m = s * S.ρ m * s⁻¹ * s := by group
    _ = S.ρ m * s := by rw [e]

variable (C : Cfg111 S g A) (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z)
include C hk hkz

omit hkz in
theorem map_ne (W : Ord3 S k m) :
    (S.Lbar k).map (MulAut.conj (S.ρ m)).toMonoidHom ≠ S.Lbar k := by
  have hkQ := C.inc.le_QG hk
  obtain ⟨s₀, hs₀, hs₀w⟩ := W.inv
  intro he
  have h1 : S.ρ m * s₀ * (S.ρ m)⁻¹ ∈ S.Lbar k := by rw [← he]; exact ⟨s₀, hs₀, rfl⟩
  have h2 : S.ρ m * s₀ * (S.ρ m)⁻¹ * s₀⁻¹ ∈ S.Lbar k := mul_mem h1 (inv_mem hs₀)
  have e : S.ρ m * s₀ * (S.ρ m)⁻¹ * s₀⁻¹ = S.ρ m * S.ρ m := by
    have e1 : s₀ * (S.ρ m)⁻¹ * s₀⁻¹ = S.ρ m := by
      calc s₀ * (S.ρ m)⁻¹ * s₀⁻¹ = (s₀ * S.ρ m * s₀⁻¹)⁻¹ := by group
        _ = S.ρ m := by rw [hs₀w, inv_inv]
    calc S.ρ m * s₀ * (S.ρ m)⁻¹ * s₀⁻¹ = S.ρ m * (s₀ * (S.ρ m)⁻¹ * s₀⁻¹) := by group
      _ = S.ρ m * S.ρ m := by rw [e1]
  rw [e] at h2
  have h4 := mul_self_of_mem_Lbar S hkQ h2
  apply W.ne_one
  calc S.ρ m = (S.ρ m * S.ρ m * (S.ρ m * S.ρ m)) * (S.ρ m ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, W.cube, one_mul, inv_one]

theorem exists_commute (W : Ord3 S k m) :
    ∃ t ∈ S.Lbar k, t ≠ 1 ∧ t * S.ρ m = S.ρ m * t := by
  classical
  have hkQ := C.inc.le_QG hk
  have hy : Hyp S k := C.hy.of_conj hkQ hkz
  obtain ⟨s₀, hs₀, hs₀w⟩ := W.inv
  obtain ⟨t, ht, ht1, hts⟩ : ∃ t ∈ S.Lbar k, t ≠ 1 ∧ t ≠ s₀ := by
    by_contra hcon
    push Not at hcon
    have hsub : ((S.Lbar k : Subgroup S.O) : Set S.O) ⊆ ↑({1, s₀} : Finset S.O) := by
      intro t ht
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      by_cases h1 : t = 1
      · exact Or.inl h1
      · exact Or.inr (hcon t ht h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
    have h2 : ({1, s₀} : Finset S.O).card ≤ 2 := Finset.card_le_two
    have h3 : Nat.card (S.Lbar k) ≤ 2 := h1.trans h2
    have h4 := hy.cons.card_Lbar
    have h6 := hy.hyp4.two_lt_width
    have h5 : 2 ^ 2 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases W.dich t ht with e | e
  · exact ⟨t, ht, ht1, commute_of_conj_eq e⟩
  refine ⟨s₀ * t, mul_mem hs₀ ht, fun h => hts ?_, commute_of_conj_eq ?_⟩
  · rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S hkQ hs₀)]
  · calc s₀ * t * S.ρ m * (s₀ * t)⁻¹ = s₀ * (t * S.ρ m * t⁻¹) * s₀⁻¹ := by group
      _ = (s₀ * S.ρ m * s₀⁻¹)⁻¹ := by rw [e]; group
      _ = S.ρ m := by rw [hs₀w, inv_inv]

omit C hk hkz in
theorem mem_Lbar_of_commute {t : S.O} (ht : t ∈ S.Lbar k) (htw : t * S.ρ m = S.ρ m * t) :
    t ∈ S.Lbar ((m : G) * k) := by
  rw [mem_Lbar_mul_iff]
  rwa [show (S.ρ m)⁻¹ * t * S.ρ m = t by rw [mul_assoc, htw, inv_mul_cancel_left]]

theorem mem_A (W : Ord3 S k m) : (m : G) * k * S.z * ((m : G) * k)⁻¹ ∈ A := by
  have hkQ := C.inc.le_QG hk
  obtain ⟨t, ht, ht1, htw⟩ := W.exists_commute C hk hkz
  have htm := mem_Lbar_of_commute ht htw
  have hne : S.Lbar k ⊓ S.Lbar ((m : G) * k) ≠ ⊥ := fun h0 => ht1 (by
    have hmem : t ∈ S.Lbar k ⊓ S.Lbar ((m : G) * k) := ⟨ht, htm⟩
    rw [h0] at hmem
    exact (Subgroup.mem_bot).mp hmem)
  exact C.mem_of_Lbar_inf_ne_bot hk hkz (conj_mem_QG' S m.2 hkQ) (conj_ne_z' S m.2 hkz) hne

theorem cl_ne (W : Ord3 S k m) :
    S.cl ((m : G) * k * S.z * ((m : G) * k)⁻¹) ≠ S.cl (k * S.z * k⁻¹) := fun h =>
  W.map_ne C hk (by
    rw [← Lbar_mul S m k]
    exact Lbar_eq_of_cl_eq S (C.inc.le_QG hk) hkz (conj_mem_QG' S m.2 (C.inc.le_QG hk)) h)

theorem apply_eq_of_commute (W : Ord3 S k m) {t : S.O} (ht : t ∈ S.Lbar k)
    (htw : t * S.ρ m = S.ρ m * t) {v : S.Qt} (hv : v ∈ S.clSub A) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have h1 := mem_span_cl_iff.mp (C.inc.apply_sub_mem_span hk ht hv)
  have h2 := mem_span_cl_iff.mp (C.inc.apply_sub_mem_span (W.mem_A C hk hkz)
    (mem_Lbar_of_commute ht htw) hv)
  rcases h1 with h1 | h1
  · exact sub_eq_zero.mp h1
  rcases h2 with h2 | h2
  · exact sub_eq_zero.mp h2
  exact absurd (h2.symm.trans h1) (W.cl_ne C hk hkz)

theorem map_A (W : Ord3 S k m) : A.map (MulAut.conj (m : G)).toMonoidHom = A :=
  C.map_eq_of_conj_mem m.2 hk hkz (by rw [← mul_conj_z S]; exact W.mem_A C hk hkz)

theorem apply_mem_clSub (W : Ord3 S k m) {v : S.Qt} (hv : v ∈ S.clSub A) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A :=
  ρ_apply_mem_clSub (W.map_A C hk hkz) hv

theorem eq_zero_of_fix (W : Ord3 S k m) {v : S.Qt}
    (hv : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  have hkQ := C.inc.le_QG hk
  have hy : Hyp S k := C.hy.of_conj hkQ hkz
  let U : Submodule (ZMod 2) S.Qt :=
    { carrier := {u | ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        rw [ha, hb]
      zero_mem' := by simp
      smul_mem' := fun c u hu => by
        simp only [Set.mem_ofPred_eq, map_smul] at hu ⊢
        rw [hu] }
  by_contra hv0
  have hUne : U ≠ ⊥ := fun h0 => hv0 (by
    have hvU : v ∈ U := hv
    rw [h0] at hvU
    exact (Submodule.mem_bot _).mp hvU)
  have hinv : ∀ x ∈ S.Lbar k, ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := by
    intro x hx u hu
    have hu' : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := hu
    change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u
    rcases W.dich x hx with e | e
    · rw [← coe_mul_apply, ← commute_of_conj_eq e, coe_mul_apply, hu']
    · have e1 : x * (S.ρ m)⁻¹ * x⁻¹ = S.ρ m := by
        rw [show x * (S.ρ m)⁻¹ * x⁻¹ = (x * S.ρ m * x⁻¹)⁻¹ by group, e, inv_inv]
      have e2 : S.ρ m * x = x * (S.ρ m)⁻¹ := by
        calc S.ρ m * x = x * (S.ρ m)⁻¹ * x⁻¹ * x := by rw [e1]
          _ = x * (S.ρ m)⁻¹ := by group
      have hu'' : (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
        conv_lhs => rw [← hu']
        exact inv_apply_apply_O _ _
      rw [← coe_mul_apply, e2, coe_mul_apply, hu'']
  have ha : S.cl (k * S.z * k⁻¹) ∈ U := cl_a_mem_of_invariant hy.hyp4 hUne hinv
  have ha' : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) =
      S.cl (k * S.z * k⁻¹) := ha
  rw [ρ_cl_conj_z S m hkQ] at ha'
  exact W.cl_ne C hk hkz ha'

theorem add_add_eq_zero (W : Ord3 S k m) (v : S.Qt) :
    v + ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v + ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0 := by
  apply W.eq_zero_of_fix C hk hkz
  rw [map_add, map_add, W.apply_apply_apply]
  abel

theorem mem_clSub_of_fix (W : Ord3 S k m) {v : S.Qt}
    (hv : ∀ t ∈ S.Lbar k, t * S.ρ m = S.ρ m * t → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    v ∈ S.clSub A := by
  have hkQ := C.inc.le_QG hk
  have hy : Hyp S k := C.hy.of_conj hkQ hkz
  obtain ⟨x, hx, hxw⟩ := W.inv
  have hxx : x * x = 1 := mul_self_of_mem_Lbar S hkQ hx
  have key : ∀ u : S.Qt, (∀ t ∈ S.Lbar k, t * S.ρ m = S.ρ m * t →
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) →
      u + (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) := by
    intro u hu
    rw [← hy.hyp4.fixSub_eq, mem_fixSub]
    intro s hs
    rcases W.dich s hs with e | e
    · have hsu := hu s hs (commute_of_conj_eq e)
      rw [map_add, hsu, ← coe_mul_apply, Lbar_comm S hkQ hs hx, coe_mul_apply, hsu]
    · have hxs : x * s * S.ρ m = S.ρ m * (x * s) := commute_of_conj_eq (by
        calc x * s * S.ρ m * (x * s)⁻¹ = x * (s * S.ρ m * s⁻¹) * x⁻¹ := by group
          _ = (x * S.ρ m * x⁻¹)⁻¹ := by rw [e]; group
          _ = S.ρ m := by rw [hxw, inv_inv])
      have h1 := hu _ (mul_mem hx hs) hxs
      have hsu : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) u = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
        have e2 : s = x * (x * s) := by rw [← mul_assoc, hxx, one_mul]
        rw [e2, coe_mul_apply, h1]
      have hsxu : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u := by
        rw [← coe_mul_apply, Lbar_comm S hkQ hs hx, h1]
      rw [map_add, hsu, hsxu, add_comm]
  have hwv : ∀ t ∈ S.Lbar k, t * S.ρ m = S.ρ m * t → (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro t ht htw
    rw [← coe_mul_apply, htw, coe_mul_apply, hv t ht htw]
  have hxw' : ∀ u : S.Qt, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) := by
    intro u
    have e : x * S.ρ m = S.ρ m * S.ρ m * x := by
      rw [← W.inv_eq]
      calc x * S.ρ m = x * S.ρ m * x⁻¹ * x := by group
        _ = (S.ρ m)⁻¹ * x := by rw [hxw]
    rw [← coe_mul_apply, e, coe_mul_apply, coe_mul_apply]
  have hsum : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (v + (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) + (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v +
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) + v = 0 := by
    rw [hxw', map_add, map_add]
    have h3 := W.add_add_eq_zero C hk hkz v
    calc _ = (v + ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v +
            ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) +
          (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) +
          ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) := by abel
      _ = 0 := by rw [h3, ZModModule.add_self, add_zero]
  have hdec := eq_neg_of_add_eq_zero_right hsum
  rw [neg_eq_of_add_eq_zero_right (ZModModule.add_self _)] at hdec
  rw [hdec]
  have haA : S.cl (k * S.z * k⁻¹) ∈ S.clSub A := S.cl_mem_clSub hk hkQ
  have hspan : (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) ≤ S.clSub A :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr haA
  exact add_mem (W.apply_mem_clSub C hk hkz (W.apply_mem_clSub C hk hkz (hspan (key v hv))))
    (hspan (key _ hwv))

theorem Wt_inf_le (W : Ord3 S k m) : Wt S k ⊓ Wt S ((m : G) * k) ≤ S.clSub A := by
  have hkQ := C.inc.le_QG hk
  have hmQ := conj_mem_QG' S m.2 hkQ
  intro v hv
  refine W.mem_clSub_of_fix C hk hkz fun t ht htw => ?_
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp (Submodule.mem_inf.mp hv).1
  obtain ⟨x', hx', hx'Q, hxx'⟩ := S.mem_clSub_iff.mp (Submodule.mem_inf.mp hv).2
  have h1 := mem_span_cl_iff.mp (Lbar_apply_sub_mem_span hkQ hx ht)
  have h2 := mem_span_cl_iff.mp (Lbar_apply_sub_mem_span hmQ hx' (mem_Lbar_of_commute ht htw))
  rw [hxx'] at h2
  rcases h1 with h1 | h1
  · exact sub_eq_zero.mp h1
  rcases h2 with h2 | h2
  · exact sub_eq_zero.mp h2
  exact absurd (h2.symm.trans h1) (W.cl_ne C hk hkz)

theorem apply_sub_mem_clSub (W : Ord3 S k m) {t : S.O} (ht : t ∈ S.Lbar k)
    (htw : t * S.ρ m = S.ρ m * t) {v : S.Qt} (hv : ∀ c ∈ S.clSub A, polar S.q v c = 0) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub A := by
  have hkQ := C.inc.le_QG hk
  have hy : Hyp S k := C.hy.of_conj hkQ hkz
  have hmA := W.mem_A C hk hkz
  have hy' : Hyp S ((m : G) * k) := C.hy.of_conj (C.inc.le_QG hmA) (conj_ne_z' S m.2 hkz)
  obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
  have hc : ∀ j : G, j * S.z * j⁻¹ ∈ A →
      x ∈ S.QG ⊓ centralizer ({j * S.z * j⁻¹} : Set G) := fun j hj =>
    mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr ((S.polar_cl_eq_zero_iff hxQ
      (C.inc.le_QG hj)).mp (hv _ (S.cl_mem_clSub hj (C.inc.le_QG hj))))⟩
  exact W.Wt_inf_le C hk hkz (Submodule.mem_inf.mpr ⟨hy.cons.comm_le x (hc k hk) t ht,
    hy'.cons.comm_le x (hc _ hmA) t (mem_Lbar_of_commute ht htw)⟩)

end Ord3

end CFSG.LargeExtraspecial.S11
