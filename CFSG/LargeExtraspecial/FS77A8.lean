module

public import CFSG.LargeExtraspecial.FS77A6
public import CFSG.LargeExtraspecial.FS77A7
public import CFSG.LargeExtraspecial.FS77NF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace CaseA

namespace Good

variable {D : CaseA S} (Y : D.Good)

omit [Finite G] in
theorem pow_val_mul_pow_val {x : G} (hx : x * x = 1) (c d : ZMod 2) :
    x ^ c.val * x ^ d.val = x ^ (c + d).val := by
  rcases Core.zmod2_cases c with rfl | rfl <;> rcases Core.zmod2_cases d with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 from rfl, ZMod.val_zero, pow_zero, ZMod.val_one, pow_one, hx]

theorem eq_of_pow_mul_pow (D : CaseA S) {c d c' d' : ZMod 2}
    (h : S.z ^ c.val * D.a ^ d.val = S.z ^ c'.val * D.a ^ d'.val) : c = c' ∧ d = d' := by
  have hz1 := S.z_ne_one
  have ha1 := D.a_ne_one
  have haz := D.a_ne_z
  have h1 := D.az_ne_one
  have h2 := D.az_ne_z
  have h3 := D.az_ne_a
  have hza : S.z * D.a = D.a * S.z := D.a_comm_z.symm
  rcases Core.zmod2_cases c with rfl | rfl <;> rcases Core.zmod2_cases d with rfl | rfl <;>
    rcases Core.zmod2_cases c' with rfl | rfl <;> rcases Core.zmod2_cases d' with rfl | rfl <;>
    simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, mul_one, hza] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h.symm hz1
    | exact absurd h hz1
    | exact absurd h.symm ha1
    | exact absurd h ha1
    | exact absurd h.symm haz
    | exact absurd h haz
    | exact absurd h.symm h1
    | exact absurd h h1
    | exact absurd h.symm h2
    | exact absurd h h2
    | exact absurd h.symm h3
    | exact absurd h h3

variable {e : Fin 6 → D.N} (hq : ∀ i, D.qN (e i) = orthQv6 i)
  (hB : ∀ i j, polar D.qN (e i) (e j) = orthBm6 i j)

theorem qv6_eq : qv6 = orthQv6 := by
  funext i
  fin_cases i <;> rfl

theorem Bm6_eq : Bm6 = orthBm6 := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def sLift (D : CaseA S) (e : Fin 6 → D.N) (i : Fin 6) : G :=
  (S.exists_cl ((e i : D.N) : S.Qt)).choose

theorem sLift_mem (i : Fin 6) : sLift D e i ∈ S.QG :=
  (S.exists_cl ((e i : D.N) : S.Qt)).choose_spec.1

theorem cl_sLift (i : Fin 6) : S.cl (sLift D e i) = (e i : S.Qt) :=
  (S.exists_cl ((e i : D.N) : S.Qt)).choose_spec.2

theorem z_comm_sLift (i : Fin 6) : S.z * sLift D e i = sLift D e i * S.z :=
  (S.z_comm_QG (sLift_mem i)).symm

include hq in
theorem sLift_sq (i : Fin 6) : sLift D e i * sLift D e i = S.z ^ (qv6 i).val := by
  have hqi : S.q (S.cl (sLift D e i)) = orthQv6 i := by rw [cl_sLift, ← D.qN_apply, hq]
  rw [qv6_eq, ← hqi, ← pow_two]
  rcases S.sq_eq_one_or_z (sLift_mem i) with h | h
  · rw [(S.q_cl_eq_zero_iff (sLift_mem i)).mpr h, ZMod.val_zero, pow_zero, h]
  · have h1 : (sLift D e i) ^ 2 ≠ 1 := by rw [h]; exact S.z_ne_one
    rw [(S.q_cl_eq_one_iff (sLift_mem i)).mpr h1, ZMod.val_one, pow_one, h]

include hB in
theorem sLift_comm (i j : Fin 6) :
    sLift D e i * sLift D e j = sLift D e j * sLift D e i * S.z ^ (Bm6 i j).val := by
  have hBij : polar S.q (S.cl (sLift D e i)) (S.cl (sLift D e j)) = orthBm6 i j := by
    rw [cl_sLift, cl_sLift, ← D.polar_qN, hB]
  rw [Bm6_eq, ← hBij]
  rcases S.mul_comm_or (sLift_mem i) (sLift_mem j) with h | h
  · rw [(S.polar_cl_eq_zero_iff (sLift_mem i) (sLift_mem j)).mpr h, ZMod.val_zero, pow_zero,
      mul_one, h]
  · have h1 : sLift D e i * sLift D e j ≠ sLift D e j * sLift D e i := by
      intro h'
      apply S.z_ne_one
      have h2 : S.z * (sLift D e j * sLift D e i) = sLift D e j * sLift D e i := h.symm.trans h'
      calc S.z = S.z * (sLift D e j * sLift D e i) * (sLift D e j * sLift D e i)⁻¹ := by group
        _ = 1 := by rw [h2, mul_inv_cancel]
    rw [(S.polar_cl_eq_one_iff (sLift_mem i) (sLift_mem j)).mpr h1, ZMod.val_one, pow_one, h,
      S.z_comm_QG (S.QG.mul_mem (sLift_mem j) (sLift_mem i))]

theorem sec_mem (v : V6) : sec (sLift D e) v ∈ S.QG := by
  unfold sec
  have h := fun i => S.QG.pow_mem (sLift_mem (D := D) (e := e) i)
  exact S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (h 0 _) (h 1 _))
    (h 2 _)) (h 3 _)) (h 4 _)) (h 5 _)

theorem cl_pow_val (i : Fin 6) (c : ZMod 2) :
    S.cl (sLift D e i ^ c.val) = c • ((e i : D.N) : S.Qt) := by
  rcases Core.zmod2_cases c with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, S.cl_one, zero_smul]
  · rw [ZMod.val_one, pow_one, cl_sLift, one_smul]

theorem cl_sec (v : V6) : S.cl (sec (sLift D e) v) = ((emb6 e v : D.N) : S.Qt) := by
  have h := fun i (c : ZMod 2) => S.QG.pow_mem (sLift_mem (D := D) (e := e) i) c.val
  unfold sec
  rw [S.cl_mul (S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (h 0 _) (h 1 _))
      (h 2 _)) (h 3 _)) (h 4 _)) (h 5 _),
    S.cl_mul (S.QG.mul_mem (S.QG.mul_mem (S.QG.mul_mem (h 0 _) (h 1 _)) (h 2 _)) (h 3 _))
      (h 4 _),
    S.cl_mul (S.QG.mul_mem (S.QG.mul_mem (h 0 _) (h 1 _)) (h 2 _)) (h 3 _),
    S.cl_mul (S.QG.mul_mem (h 0 _) (h 1 _)) (h 2 _), S.cl_mul (h 0 _) (h 1 _),
    cl_pow_val, cl_pow_val, cl_pow_val, cl_pow_val, cl_pow_val, cl_pow_val, emb6_apply]
  simp only [Submodule.coe_add, Submodule.coe_smul]

theorem a_comm_sLift (i : Fin 6) : D.a * sLift D e i = sLift D e i * D.a := by
  refine (S.polar_cl_eq_zero_iff D.a_mem_QG (sLift_mem i)).mp ?_
  rw [D.cl_a, cl_sLift]
  exact (D.mem_N_iff.mp (e i).2).1

theorem a_comm_sec (v : V6) : D.a * sec (sLift D e) v = sec (sLift D e) v * D.a := by
  have h : ∀ i (c : ZMod 2), Commute D.a (sLift D e i ^ c.val) := fun i c =>
    (Commute.pow_right (a_comm_sLift i) _)
  unfold sec
  exact ((((((h 0 _).mul_right (h 1 _)).mul_right (h 2 _)).mul_right (h 3 _)).mul_right
    (h 4 _)).mul_right (h 5 _))

theorem z_comm_sec (v : V6) : S.z * sec (sLift D e) v = sec (sLift D e) v * S.z :=
  (S.z_comm_QG (sec_mem v)).symm

theorem cl_a_pow (c : ZMod 2) : S.cl (D.a ^ c.val) = c • D.P.e := by
  rcases Core.zmod2_cases c with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, S.cl_one, zero_smul]
  · rw [ZMod.val_one, pow_one, D.cl_a, one_smul]

theorem a_pow_mem (c : ZMod 2) : D.a ^ c.val ∈ S.QG := S.QG.pow_mem D.a_mem_QG _

include hq hB in
theorem conj_sec (k : Fin 3) {l : D.X} (hl : D.ρN l = tEich (q := D.qN) e k) (v : V6) :
    ∃ c d : ZMod 2, (l : G) * sec (sLift D e) v * (l : G)⁻¹ =
      sec (sLift D e) (tLin k v) * S.z ^ c.val * D.a ^ d.val := by
  have hmem := sec_mem (D := D) (e := e) v
  have hconj : (l : G) * sec (sLift D e) v * (l : G)⁻¹ ∈ S.QG :=
    S.conj_mem_QG (D.X_le_M l.2) hmem
  set d := polar S.q (((D.ρX l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((emb6 e v : D.N) : S.Qt))
    D.P.f with hd
  have hcl : S.cl ((l : G) * sec (sLift D e) v * (l : G)⁻¹) =
      S.cl (sec (sLift D e) (tLin k v) * D.a ^ d.val) := by
    rw [← D.ρX_apply_cl l hmem, cl_sec, D.ρX_eq_ρN_add l, hl,
      tEich_emb6 (q := D.qN) hq hB, S.cl_mul (sec_mem _) (a_pow_mem _), cl_sec, cl_a_pow]
  rcases (S.cl_eq_cl_iff (S.QG.mul_mem (sec_mem _) (a_pow_mem _)) hconj).mp hcl.symm with h | h
  · exact ⟨0, d, by rw [h, ZMod.val_zero, pow_zero, mul_one]⟩
  · refine ⟨1, d, ?_⟩
    rw [h, ZMod.val_one, pow_one, mul_assoc, mul_assoc]
    congr 1
    exact (Commute.pow_left D.a_comm_z _).eq

@[expose] def wz (D : CaseA S) (c d : ZMod 2) : G := S.z ^ c.val * D.a ^ d.val

theorem wz_mul (D : CaseA S) (c d c' d' : ZMod 2) :
    wz D c d * wz D c' d' = wz D (c + c') (d + d') := by
  have h3 : Commute (D.a ^ d.val) (S.z ^ c'.val) :=
    Commute.pow_left (Commute.pow_right D.a_comm_z _) _
  rw [wz, wz, wz, ← pow_val_mul_pow_val S.z_mul_z, ← pow_val_mul_pow_val D.a_mul_a,
    mul_assoc, ← mul_assoc (D.a ^ d.val), h3.eq, mul_assoc, mul_assoc]

theorem wz_inj (D : CaseA S) {c d c' d' : ZMod 2} (h : wz D c d = wz D c' d') :
    c = c' ∧ d = d' :=
  eq_of_pow_mul_pow D h

theorem comm_sec_wz (u : V6) (c d : ZMod 2) :
    sec (sLift D e) u * wz D c d = wz D c d * sec (sLift D e) u :=
  ((Commute.pow_left (z_comm_sec u) _).mul_left (Commute.pow_left (a_comm_sec u) _)).eq.symm

theorem conj_wz {x : G} (hx : x ∈ D.X) (c d : ZMod 2) : x * wz D c d * x⁻¹ = wz D c d := by
  obtain ⟨hxz, hxa⟩ := D.mem_X.mp hx
  have h : Commute x (wz D c d) :=
    (Commute.pow_right hxz _).mul_right (Commute.pow_right hxa _)
  rw [h.eq, mul_inv_cancel_right]

include hq hB in
theorem sec_mul_sec' (v w : V6) :
    sec (sLift D e) v * sec (sLift D e) w = sec (sLift D e) (v + w) * wz D (beta6 v w) 0 := by
  rw [sec_mul_sec S.z_mul_z z_comm_sLift (sLift_sq hq) (sLift_comm hB) v w, wz, ZMod.val_zero,
    pow_zero, mul_one]

include hq hB in
theorem nf_mul (u u' : V6) (c d c' d' : ZMod 2) :
    (sec (sLift D e) u * wz D c d) * (sec (sLift D e) u' * wz D c' d') =
      sec (sLift D e) (u + u') * wz D (beta6 u u' + (c + c')) (0 + (d + d')) := by
  calc (sec (sLift D e) u * wz D c d) * (sec (sLift D e) u' * wz D c' d')
      = sec (sLift D e) u * (wz D c d * sec (sLift D e) u') * wz D c' d' := by
        simp only [mul_assoc]
    _ = sec (sLift D e) u * sec (sLift D e) u' * (wz D c d * wz D c' d') := by
        rw [← comm_sec_wz]
        simp only [mul_assoc]
    _ = _ := by rw [sec_mul_sec' hq hB, wz_mul, mul_assoc, wz_mul]

include hq hB Y in
theorem false_of_sextuple : False := by
  have hlift : ∀ k : Fin 3, ∃ l : D.X, Y.y * l * Y.y⁻¹ = l ∧ D.ρN l = tEich (q := D.qN) e k := by
    intro k
    obtain ⟨m, hm⟩ := D.mem_range_ρN (eichler_mem_omegaGroup D.qN_nondegenerate _ _)
    obtain ⟨l, hl1, hl2⟩ := Y.exists_lift m
    exact ⟨l, hl1, hl2.trans hm⟩
  choose l hly hlρ using hlift
  have hconj : ∀ k v, ∃ c d : ZMod 2, ((l k : D.X) : G) * sec (sLift D e) v * (l k : G)⁻¹ =
      sec (sLift D e) (tLin k v) * wz D c d := by
    intro k v
    obtain ⟨c, d, h⟩ := conj_sec hq hB k (hlρ k) v
    exact ⟨c, d, by rw [h, wz, mul_assoc]⟩
  choose F Gf hFG using hconj
  have hC1 : ∀ k v w, F k (v + w) = F k v + F k w + beta6 (tLin k v) (tLin k w) + beta6 v w := by
    intro k v w
    have h1 : ((l k : D.X) : G) * (sec (sLift D e) v * sec (sLift D e) w) * (l k : G)⁻¹ =
        (((l k : D.X) : G) * sec (sLift D e) v * (l k : G)⁻¹) *
          (((l k : D.X) : G) * sec (sLift D e) w * (l k : G)⁻¹) := by group
    have h2 : ((l k : D.X) : G) * (sec (sLift D e) (v + w) * wz D (beta6 v w) 0) *
        (l k : G)⁻¹ = (((l k : D.X) : G) * sec (sLift D e) (v + w) * (l k : G)⁻¹) *
          (((l k : D.X) : G) * wz D (beta6 v w) 0 * (l k : G)⁻¹) := by group
    rw [sec_mul_sec' hq hB, h2, conj_wz (l k).2, hFG, hFG, hFG, mul_assoc, wz_mul,
      nf_mul hq hB, ← map_add] at h1
    have h3 := (wz_inj D (mul_left_cancel h1)).1
    have h4 := CharTwo.add_self_eq_zero (beta6 v w)
    linear_combination h3 - h4
  set lX : List (Fin 3) → D.X := fun ω => (ω.map l).prod with hlX
  have hlX_cons : ∀ k ks, lX (k :: ks) = l k * lX ks := fun k ks => by
    simp only [hlX, List.map_cons, List.prod_cons]
  have hlX_nil : lX [] = 1 := by simp only [hlX, List.map_nil, List.prod_nil]
  have hly' : ∀ ω, Y.y * (lX ω : G) * Y.y⁻¹ = lX ω := by
    intro ω
    induction ω with
    | nil => rw [hlX_nil, Subgroup.coe_one, mul_one, mul_inv_cancel]
    | cons k ks ih =>
      rw [hlX_cons, Subgroup.coe_mul]
      calc Y.y * ((l k : G) * (lX ks : G)) * Y.y⁻¹
          = (Y.y * (l k : G) * Y.y⁻¹) * (Y.y * (lX ks : G) * Y.y⁻¹) := by group
        _ = (l k : G) * (lX ks : G) := by rw [hly k, ih]
  have hρ : ∀ ω, D.ρN (lX ω) = tEichProd (q := D.qN) e ω := by
    intro ω
    induction ω with
    | nil => rw [hlX_nil, map_one]; rfl
    | cons k ks ih => rw [hlX_cons, map_mul, ih, hlρ]; rfl
  have hrel : ∀ ω, (∀ v, tComp ω v = v) → lX ω = 1 := by
    intro ω hω
    refine Y.eq_of_ρN_eq (hly' ω) (by rw [Subgroup.coe_one, mul_one, mul_inv_cancel]) ?_
    rw [hρ, tEichProd_eq_one hq hB ω hω, map_one]
  have hword : ∀ ω v, ∃ d : ZMod 2, (lX ω : G) * sec (sLift D e) v * (lX ω : G)⁻¹ =
      sec (sLift D e) (tComp ω v) * wz D (wordSum F ω v) d := by
    intro ω v
    induction ω with
    | nil =>
      refine ⟨0, ?_⟩
      rw [hlX_nil, Subgroup.coe_one, one_mul, inv_one, mul_one]
      simp [tComp, wordSum, wz]
    | cons k ks ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨Gf k (tComp ks v) + d, ?_⟩
      have e1 : ((lX (k :: ks) : D.X) : G) * sec (sLift D e) v * ((lX (k :: ks) : D.X) : G)⁻¹ =
          (l k : G) * ((lX ks : G) * sec (sLift D e) v * (lX ks : G)⁻¹) * (l k : G)⁻¹ := by
        rw [hlX_cons, Subgroup.coe_mul]
        group
      have e2 : (l k : G) * (sec (sLift D e) (tComp ks v) * wz D (wordSum F ks v) d) *
          (l k : G)⁻¹ = ((l k : G) * sec (sLift D e) (tComp ks v) * (l k : G)⁻¹) *
            ((l k : G) * wz D (wordSum F ks v) d * (l k : G)⁻¹) := by group
      rw [e1, hd, e2, hFG, conj_wz (l k).2, mul_assoc, wz_mul]
      rfl
  have hzero : ∀ ω, (∀ v, tComp ω v = v) → ∀ v, wordSum F ω v = 0 := by
    intro ω hω v
    obtain ⟨d, hd⟩ := hword ω v
    rw [hrel ω hω, hω, Subgroup.coe_one, one_mul, inv_one, mul_one] at hd
    have h1 : wz D (wordSum F ω v) d = wz D 0 0 := by
      have h2 := mul_left_cancel (hd.symm.trans (mul_one _).symm)
      rw [h2, wz, ZMod.val_zero, pow_zero, pow_zero, mul_one]
    exact (wz_inj D h1).1
  exact core_obstruction F hC1 (hzero _ tComp_two_two) (hzero _ tComp_w1) (hzero _ tComp_w2)

end Good

end CaseA

end CFSG.LargeExtraspecial.FS77
