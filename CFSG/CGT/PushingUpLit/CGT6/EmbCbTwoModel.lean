module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoUniq
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} {m : ℕ}

variable [Finite V] {G T : Subgroup (MulAut V)} {t : MulAut V}
  {X₁ X₂ : Subgroup (MulAut V)} in
structure CbtRel (K : CbtCtx G T Y t m X₁ X₂) : Prop where
  v₂_fix : K.L₂.vvec ∈ fixV X₁
  zv₂_fix : K.L₂.zvec * K.L₁.vvec ∈ fixV X₁
  v₁_fix : K.L₁.vvec ∈ fixV X₂
  zv₁_fix : K.L₁.zvec * K.L₂.vvec ∈ fixV X₂
  V_eq : (commV X₁ ⊔ commV X₂) ⊔ (fixV X₁ ⊓ fixV X₂) = ⊤
  t_fix_R : ∀ r ∈ fixV X₁ ⊓ fixV X₂, t r = r

private theorem cbtm_ext {S : Set V} (hS : Subgroup.closure S = ⊤) {f g : MulAut V}
    (h : ∀ s ∈ S, f s = g s) : f = g := by
  ext v
  have hv : v ∈ Subgroup.closure S := by
    rw [hS]
    trivial
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => rw [map_one, map_one]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, map_inv, ha]

private theorem cbtm_comm {ι : Type} {ω : ι → V} {R : Subgroup V}
    (hS : Subgroup.closure (Set.range ω ∪ (R : Set V)) = ⊤) {f g : MulAut V} {σ τ : ι → ι}
    (hf : ∀ i, f (ω i) = ω (σ i)) (hg : ∀ i, g (ω i) = ω (τ i))
    (hfR : ∀ r ∈ R, f r = r) (hgR : ∀ r ∈ R, g r = r) (hστ : ∀ i, σ (τ i) = τ (σ i)) :
    f * g = g * f := by
  refine cbtm_ext hS fun s hs => ?_
  rcases hs with ⟨i, rfl⟩ | hs
  · rw [MulAut.mul_apply, MulAut.mul_apply, hg, hf, hf, hg, hστ]
  · rw [MulAut.mul_apply, MulAut.mul_apply, hgR s hs, hfR s hs, hgR s hs]

private theorem cbtm_sq (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v * v = 1 := by
  rw [← pow_two]
  exact hV v

namespace CbtLift

variable {C : CbtY Y m} {t : MulAut V} {X : Subgroup (MulAut V)} (L : CbtLift C t X)

private theorem cbtm_y_om {y : MulAut V} (hy : y ∈ Y) {u : V} (hu : y u = u)
    (s : Fin (m + 2)) :
    y (L.D.w s * u) = L.D.w ((L.D.θ ⟨y, L.hYX hy⟩ : Equiv.Perm (Fin (m + 2))) s) * u := by
  rw [map_mul, L.D.hwact y (L.hYX hy) s, hu]

private theorem cbtm_t_om {u : V} (hu : t u = u) (s : Fin (m + 2)) :
    t (L.D.w s * u) = L.D.w (swap L.D.a L.D.b s) * u := by
  rw [map_mul, L.D.htw s, hu]

private theorem cbtm_x_om {p q : Fin m} (hpq : p ≠ q) {u : V} (hu : u ∈ fixV X)
    (s : Fin (m + 2)) :
    (L.xElt hpq : MulAut V) (L.D.w s * u) =
      L.D.w ((swap (L.j p) L.D.a * swap (L.j q) L.D.b) s) * u := by
  rw [map_mul, L.xElt_w hpq s, mem_fixV.mp hu _ (L.xElt hpq).2]

private theorem cbtm_xPerm_jp {p q : Fin m} (hpq : p ≠ q) :
    (swap (L.j p) L.D.a * swap (L.j q) L.D.b) (L.j p) = L.D.a := by
  have h1 : L.j p ≠ L.j q := fun h => hpq (L.hjinj h)
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 (L.hjb p), swap_apply_left]

private theorem cbtm_xPerm_jr {p q r : Fin m} (hrp : r ≠ p) (hrq : r ≠ q) :
    (swap (L.j p) L.D.a * swap (L.j q) L.D.b) (L.j r) = L.j r := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (fun h => hrq (L.hjinj h)) (L.hjb r),
    swap_apply_of_ne_of_ne (fun h => hrp (L.hjinj h)) (L.hja r)]

end CbtLift

section Model

variable [Finite V] {G T : Subgroup (MulAut V)} {t : MulAut V}
  {X₁ X₂ : Subgroup (MulAut V)}

private abbrev CbtIdx (m : ℕ) : Type := Fin m ⊕ (Bool × Bool)

private def cbtmDelta {n : ℕ} : CbtIdx n → CbtIdx n := Sum.map id fun c => (!c.1, c.2)

private def cbtmTau {n : ℕ} : CbtIdx n → CbtIdx n := Sum.map id fun c => (c.1, !c.2)

private def cbtmNu {n : ℕ} (π : Equiv.Perm (Fin n)) : CbtIdx n → CbtIdx n := Sum.map π id

private noncomputable def cbtmOmega (K : CbtCtx G T Y t m X₁ X₂) : CbtIdx m → V
  | Sum.inl r => K.C.w r * K.L₁.vvec * K.L₂.vvec
  | Sum.inr (false, false) => K.L₁.D.w K.L₁.D.a * K.L₂.vvec
  | Sum.inr (false, true) => K.L₁.D.w K.L₁.D.b * K.L₂.vvec
  | Sum.inr (true, false) => K.L₂.D.w K.L₂.D.a * K.L₁.vvec
  | Sum.inr (true, true) => K.L₂.D.w K.L₂.D.b * K.L₁.vvec

variable (K : CbtCtx G T Y t m X₁ X₂)

private theorem cbtm_omega_c11 :
    cbtmOmega K (Sum.inr (false, false)) = K.L₁.D.w K.L₁.D.a * K.L₂.vvec := rfl

private theorem cbtm_omega_c12 :
    cbtmOmega K (Sum.inr (false, true)) = K.L₁.D.w K.L₁.D.b * K.L₂.vvec := rfl

private theorem cbtm_omega_c21 :
    cbtmOmega K (Sum.inr (true, false)) = K.L₂.D.w K.L₂.D.a * K.L₁.vvec := rfl

private theorem cbtm_omega_c22 :
    cbtmOmega K (Sum.inr (true, true)) = K.L₂.D.w K.L₂.D.b * K.L₁.vvec := rfl

private theorem cbtm_omega_inl_1 (r : Fin m) :
    cbtmOmega K (Sum.inl r) = K.L₁.D.w (K.L₁.j r) * K.L₂.vvec := by
  rw [K.L₁.w_j K.hV K.hm K.hodd r]
  rfl

private theorem cbtm_omega_inl_2 (r : Fin m) :
    cbtmOmega K (Sum.inl r) = K.L₂.D.w (K.L₂.j r) * K.L₁.vvec := by
  rw [K.L₂.w_j K.hV K.hm K.hodd r]
  exact mul_right_comm _ _ _

private theorem cbtm_v₁_eq :
    K.L₁.vvec = cbtmOmega K (Sum.inr (false, false)) * cbtmOmega K (Sum.inr (false, true)) := by
  rw [cbtm_omega_c11, cbtm_omega_c12]
  calc K.L₁.vvec = K.L₁.vvec * (K.L₂.vvec * K.L₂.vvec) := by
        rw [cbtm_sq K.hV, mul_one]
    _ = K.L₁.D.w K.L₁.D.a * K.L₂.vvec * (K.L₁.D.w K.L₁.D.b * K.L₂.vvec) := by
        unfold CbtLift.vvec
        ac_rfl

private theorem cbtm_v₂_eq :
    K.L₂.vvec = cbtmOmega K (Sum.inr (true, false)) * cbtmOmega K (Sum.inr (true, true)) := by
  rw [cbtm_omega_c21, cbtm_omega_c22]
  calc K.L₂.vvec = K.L₂.vvec * (K.L₁.vvec * K.L₁.vvec) := by
        rw [cbtm_sq K.hV, mul_one]
    _ = K.L₂.D.w K.L₂.D.a * K.L₁.vvec * (K.L₂.D.w K.L₂.D.b * K.L₁.vvec) := by
        unfold CbtLift.vvec
        ac_rfl

private theorem cbtm_c_fix₁ (hrel : CbtRel K) (b : Bool) :
    cbtmOmega K (Sum.inr (true, b)) ∈ fixV X₁ := by
  cases b
  · have h : K.L₂.D.w K.L₂.D.a = K.L₂.vvec * K.L₂.zvec := by
      unfold CbtLift.vvec CbtLift.zvec
      rw [mul_assoc, K.L₂.D.w_sq K.hV, mul_one]
    rw [cbtm_omega_c21, h, mul_assoc]
    exact mul_mem hrel.v₂_fix hrel.zv₂_fix
  · rw [cbtm_omega_c22]
    exact hrel.zv₂_fix

private theorem cbtm_c_fix₂ (hrel : CbtRel K) (b : Bool) :
    cbtmOmega K (Sum.inr (false, b)) ∈ fixV X₂ := by
  cases b
  · have h : K.L₁.D.w K.L₁.D.a = K.L₁.vvec * K.L₁.zvec := by
      unfold CbtLift.vvec CbtLift.zvec
      rw [mul_assoc, K.L₁.D.w_sq K.hV, mul_one]
    rw [cbtm_omega_c11, h, mul_assoc]
    exact mul_mem hrel.v₁_fix hrel.zv₁_fix
  · rw [cbtm_omega_c12]
    exact hrel.zv₁_fix

private theorem cbtm_om1_mem (s : Fin (m + 2)) :
    K.L₁.D.w s * K.L₂.vvec ∈ Set.range (cbtmOmega K) := by
  by_cases ha : s = K.L₁.D.a
  · subst ha
    exact ⟨Sum.inr (false, false), rfl⟩
  by_cases hb : s = K.L₁.D.b
  · subst hb
    exact ⟨Sum.inr (false, true), rfl⟩
  obtain ⟨r, hr⟩ := K.L₁.hjsurj s ha hb
  exact ⟨Sum.inl r, by rw [cbtm_omega_inl_1 K r, hr]⟩

private theorem cbtm_om2_mem (s : Fin (m + 2)) :
    K.L₂.D.w s * K.L₁.vvec ∈ Set.range (cbtmOmega K) := by
  by_cases ha : s = K.L₂.D.a
  · subst ha
    exact ⟨Sum.inr (true, false), rfl⟩
  by_cases hb : s = K.L₂.D.b
  · subst hb
    exact ⟨Sum.inr (true, true), rfl⟩
  obtain ⟨r, hr⟩ := K.L₂.hjsurj s ha hb
  exact ⟨Sum.inl r, by rw [cbtm_omega_inl_2 K r, hr]⟩

private theorem cbtm_closure (hrel : CbtRel K) :
    Subgroup.closure (Set.range (cbtmOmega K) ∪ ((fixV X₁ ⊓ fixV X₂ : Subgroup V) : Set V)) =
      ⊤ := by
  set H := Subgroup.closure
    (Set.range (cbtmOmega K) ∪ ((fixV X₁ ⊓ fixV X₂ : Subgroup V) : Set V)) with hH
  have hω : ∀ i, cbtmOmega K i ∈ H := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hR : fixV X₁ ⊓ fixV X₂ ≤ H := fun r hr => Subgroup.subset_closure (Or.inr hr)
  have hv₁ : K.L₁.vvec ∈ H := by
    rw [cbtm_v₁_eq K]
    exact mul_mem (hω _) (hω _)
  have hv₂ : K.L₂.vvec ∈ H := by
    rw [cbtm_v₂_eq K]
    exact mul_mem (hω _) (hω _)
  have hW₁ : commV X₁ ≤ H := by
    rw [← K.L₁.D.hwspan, Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    have h1 : K.L₁.D.w s * K.L₂.vvec ∈ H := by
      obtain ⟨i, hi⟩ := cbtm_om1_mem K s
      rw [← hi]
      exact hω i
    have h2 : K.L₁.D.w s = (K.L₁.D.w s * K.L₂.vvec) * K.L₂.vvec := by
      rw [mul_assoc, cbtm_sq K.hV, mul_one]
    rw [SetLike.mem_coe, h2]
    exact mul_mem h1 hv₂
  have hW₂ : commV X₂ ≤ H := by
    rw [← K.L₂.D.hwspan, Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    have h1 : K.L₂.D.w s * K.L₁.vvec ∈ H := by
      obtain ⟨i, hi⟩ := cbtm_om2_mem K s
      rw [← hi]
      exact hω i
    have h2 : K.L₂.D.w s = (K.L₂.D.w s * K.L₁.vvec) * K.L₁.vvec := by
      rw [mul_assoc, cbtm_sq K.hV, mul_one]
    rw [SetLike.mem_coe, h2]
    exact mul_mem h1 hv₁
  rw [eq_top_iff, ← hrel.V_eq]
  exact sup_le (sup_le hW₁ hW₂) hR

section Act

variable (hrel : CbtRel K) {p q : Fin m} (hpq : p ≠ q)

include hrel

private theorem cbtm_x1_p :
    (K.L₁.xElt hpq : MulAut V) (cbtmOmega K (Sum.inl p)) =
      cbtmOmega K (Sum.inr (false, false)) := by
  rw [cbtm_omega_inl_1 K p, K.L₁.cbtm_x_om hpq hrel.v₂_fix, K.L₁.cbtm_xPerm_jp hpq,
    cbtm_omega_c11]

private theorem cbtm_x1_q :
    (K.L₁.xElt hpq : MulAut V) (cbtmOmega K (Sum.inl q)) =
      cbtmOmega K (Sum.inr (false, true)) := by
  rw [cbtm_omega_inl_1 K q, K.L₁.cbtm_x_om hpq hrel.v₂_fix, K.L₁.xPerm_jq, cbtm_omega_c12]

private theorem cbtm_x1_r {r : Fin m} (hrp : r ≠ p) (hrq : r ≠ q) :
    (K.L₁.xElt hpq : MulAut V) (cbtmOmega K (Sum.inl r)) = cbtmOmega K (Sum.inl r) := by
  rw [cbtm_omega_inl_1 K r, K.L₁.cbtm_x_om hpq hrel.v₂_fix, K.L₁.cbtm_xPerm_jr hrp hrq]

private theorem cbtm_x1_ca :
    (K.L₁.xElt hpq : MulAut V) (cbtmOmega K (Sum.inr (false, false))) =
      cbtmOmega K (Sum.inl p) := by
  rw [cbtm_omega_c11, K.L₁.cbtm_x_om hpq hrel.v₂_fix, K.L₁.xPerm_a, cbtm_omega_inl_1 K p]

private theorem cbtm_x1_cb :
    (K.L₁.xElt hpq : MulAut V) (cbtmOmega K (Sum.inr (false, true))) =
      cbtmOmega K (Sum.inl q) := by
  rw [cbtm_omega_c12, K.L₁.cbtm_x_om hpq hrel.v₂_fix, K.L₁.xPerm_b hpq, cbtm_omega_inl_1 K q]

private theorem cbtm_x1_fix (b : Bool) :
    (K.L₁.xElt hpq : MulAut V) (cbtmOmega K (Sum.inr (true, b))) =
      cbtmOmega K (Sum.inr (true, b)) :=
  mem_fixV.mp (cbtm_c_fix₁ K hrel b) _ (K.L₁.xElt hpq).2

private theorem cbtm_x2_p :
    (K.L₂.xElt hpq : MulAut V) (cbtmOmega K (Sum.inl p)) =
      cbtmOmega K (Sum.inr (true, false)) := by
  rw [cbtm_omega_inl_2 K p, K.L₂.cbtm_x_om hpq hrel.v₁_fix, K.L₂.cbtm_xPerm_jp hpq,
    cbtm_omega_c21]

private theorem cbtm_x2_q :
    (K.L₂.xElt hpq : MulAut V) (cbtmOmega K (Sum.inl q)) = cbtmOmega K (Sum.inr (true, true)) := by
  rw [cbtm_omega_inl_2 K q, K.L₂.cbtm_x_om hpq hrel.v₁_fix, K.L₂.xPerm_jq, cbtm_omega_c22]

private theorem cbtm_x2_r {r : Fin m} (hrp : r ≠ p) (hrq : r ≠ q) :
    (K.L₂.xElt hpq : MulAut V) (cbtmOmega K (Sum.inl r)) = cbtmOmega K (Sum.inl r) := by
  rw [cbtm_omega_inl_2 K r, K.L₂.cbtm_x_om hpq hrel.v₁_fix, K.L₂.cbtm_xPerm_jr hrp hrq]

private theorem cbtm_x2_ca :
    (K.L₂.xElt hpq : MulAut V) (cbtmOmega K (Sum.inr (true, false))) =
      cbtmOmega K (Sum.inl p) := by
  rw [cbtm_omega_c21, K.L₂.cbtm_x_om hpq hrel.v₁_fix, K.L₂.xPerm_a, cbtm_omega_inl_2 K p]

private theorem cbtm_x2_cb :
    (K.L₂.xElt hpq : MulAut V) (cbtmOmega K (Sum.inr (true, true))) = cbtmOmega K (Sum.inl q) := by
  rw [cbtm_omega_c22, K.L₂.cbtm_x_om hpq hrel.v₁_fix, K.L₂.xPerm_b hpq, cbtm_omega_inl_2 K q]

private theorem cbtm_x2_fix (b : Bool) :
    (K.L₂.xElt hpq : MulAut V) (cbtmOmega K (Sum.inr (false, b))) =
      cbtmOmega K (Sum.inr (false, b)) :=
  mem_fixV.mp (cbtm_c_fix₂ K hrel b) _ (K.L₂.xElt hpq).2

private noncomputable def cbtmD (K : CbtCtx G T Y t m X₁ X₂) {p q : Fin m} (hpq : p ≠ q) :
    MulAut V :=
  (K.L₁.xElt hpq : MulAut V) * (K.L₂.xElt hpq : MulAut V) * (K.L₁.xElt hpq : MulAut V)

private theorem cbtm_d_inl (r : Fin m) :
    cbtmD K hpq (cbtmOmega K (Sum.inl r)) = cbtmOmega K (Sum.inl r) := by
  unfold cbtmD
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hrp : r = p
  · rw [hrp, cbtm_x1_p K hrel hpq, cbtm_x2_fix K hrel hpq false, cbtm_x1_ca K hrel hpq]
  by_cases hrq : r = q
  · rw [hrq, cbtm_x1_q K hrel hpq, cbtm_x2_fix K hrel hpq true, cbtm_x1_cb K hrel hpq]
  · rw [cbtm_x1_r K hrel hpq hrp hrq, cbtm_x2_r K hrel hpq hrp hrq, cbtm_x1_r K hrel hpq hrp hrq]

private theorem cbtm_d_c11 :
    cbtmD K hpq (cbtmOmega K (Sum.inr (false, false))) = cbtmOmega K (Sum.inr (true, false)) := by
  unfold cbtmD
  rw [MulAut.mul_apply, MulAut.mul_apply, cbtm_x1_ca K hrel hpq, cbtm_x2_p K hrel hpq,
    cbtm_x1_fix K hrel hpq false]

private theorem cbtm_d_c12 :
    cbtmD K hpq (cbtmOmega K (Sum.inr (false, true))) = cbtmOmega K (Sum.inr (true, true)) := by
  unfold cbtmD
  rw [MulAut.mul_apply, MulAut.mul_apply, cbtm_x1_cb K hrel hpq, cbtm_x2_q K hrel hpq,
    cbtm_x1_fix K hrel hpq true]

private theorem cbtm_d_c21 :
    cbtmD K hpq (cbtmOmega K (Sum.inr (true, false))) = cbtmOmega K (Sum.inr (false, false)) := by
  unfold cbtmD
  rw [MulAut.mul_apply, MulAut.mul_apply, cbtm_x1_fix K hrel hpq false, cbtm_x2_ca K hrel hpq,
    cbtm_x1_p K hrel hpq]

private theorem cbtm_d_c22 :
    cbtmD K hpq (cbtmOmega K (Sum.inr (true, true))) = cbtmOmega K (Sum.inr (false, true)) := by
  unfold cbtmD
  rw [MulAut.mul_apply, MulAut.mul_apply, cbtm_x1_fix K hrel hpq true, cbtm_x2_cb K hrel hpq,
    cbtm_x1_q K hrel hpq]

private theorem cbtm_d_act (i : CbtIdx m) :
    cbtmD K hpq (cbtmOmega K i) = cbtmOmega K (cbtmDelta i) := by
  rcases i with r | ⟨_ | _, _ | _⟩
  · exact cbtm_d_inl K hrel hpq r
  · exact cbtm_d_c11 K hrel hpq
  · exact cbtm_d_c12 K hrel hpq
  · exact cbtm_d_c21 K hrel hpq
  · exact cbtm_d_c22 K hrel hpq

omit hrel in
private theorem cbtm_d_R {r : V} (hr : r ∈ fixV X₁ ⊓ fixV X₂) : cbtmD K hpq r = r := by
  have h1 : (K.L₁.xElt hpq : MulAut V) r = r := mem_fixV.mp hr.1 _ (K.L₁.xElt hpq).2
  have h2 : (K.L₂.xElt hpq : MulAut V) r = r := mem_fixV.mp hr.2 _ (K.L₂.xElt hpq).2
  unfold cbtmD
  rw [MulAut.mul_apply, MulAut.mul_apply, h1, h2, h1]

end Act

private theorem cbtm_t_inl (r : Fin m) :
    t (cbtmOmega K (Sum.inl r)) = cbtmOmega K (Sum.inl r) := by
  rw [cbtm_omega_inl_1 K r, K.L₁.cbtm_t_om K.L₂.t_vvec,
    swap_apply_of_ne_of_ne (K.L₁.hja r) (K.L₁.hjb r)]

private theorem cbtm_t_c11 :
    t (cbtmOmega K (Sum.inr (false, false))) = cbtmOmega K (Sum.inr (false, true)) := by
  rw [cbtm_omega_c11, K.L₁.cbtm_t_om K.L₂.t_vvec, swap_apply_left, cbtm_omega_c12]

private theorem cbtm_t_c12 :
    t (cbtmOmega K (Sum.inr (false, true))) = cbtmOmega K (Sum.inr (false, false)) := by
  rw [cbtm_omega_c12, K.L₁.cbtm_t_om K.L₂.t_vvec, swap_apply_right, cbtm_omega_c11]

private theorem cbtm_t_c21 :
    t (cbtmOmega K (Sum.inr (true, false))) = cbtmOmega K (Sum.inr (true, true)) := by
  rw [cbtm_omega_c21, K.L₂.cbtm_t_om K.L₁.t_vvec, swap_apply_left, cbtm_omega_c22]

private theorem cbtm_t_c22 :
    t (cbtmOmega K (Sum.inr (true, true))) = cbtmOmega K (Sum.inr (true, false)) := by
  rw [cbtm_omega_c22, K.L₂.cbtm_t_om K.L₁.t_vvec, swap_apply_right, cbtm_omega_c21]

private theorem cbtm_t_act (i : CbtIdx m) :
    t (cbtmOmega K i) = cbtmOmega K (cbtmTau i) := by
  rcases i with r | ⟨_ | _, _ | _⟩
  · exact cbtm_t_inl K r
  · exact cbtm_t_c11 K
  · exact cbtm_t_c12 K
  · exact cbtm_t_c21 K
  · exact cbtm_t_c22 K

section ActY

variable (hrel : CbtRel K) {y : MulAut V} (hy : y ∈ Y)

include hrel hy

private theorem cbtm_y_inl (r : Fin m) :
    y (cbtmOmega K (Sum.inl r)) =
      cbtmOmega K (Sum.inl ((K.C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) r)) := by
  rw [cbtm_omega_inl_1 K r, K.L₁.cbtm_y_om hy (mem_fixV.mp hrel.v₂_fix y (K.L₁.hYX hy)),
    K.L₁.hjθ y hy r, cbtm_omega_inl_1 K]

private theorem cbtm_y_c11 :
    y (cbtmOmega K (Sum.inr (false, false))) = cbtmOmega K (Sum.inr (false, false)) := by
  rw [cbtm_omega_c11, K.L₁.cbtm_y_om hy (mem_fixV.mp hrel.v₂_fix y (K.L₁.hYX hy)),
    (K.L₁.fix_ab y hy).1]

private theorem cbtm_y_c12 :
    y (cbtmOmega K (Sum.inr (false, true))) = cbtmOmega K (Sum.inr (false, true)) := by
  rw [cbtm_omega_c12, K.L₁.cbtm_y_om hy (mem_fixV.mp hrel.v₂_fix y (K.L₁.hYX hy)),
    (K.L₁.fix_ab y hy).2]

private theorem cbtm_y_fix (b : Bool) :
    y (cbtmOmega K (Sum.inr (true, b))) = cbtmOmega K (Sum.inr (true, b)) :=
  mem_fixV.mp (cbtm_c_fix₁ K hrel b) y (K.L₁.hYX hy)

private theorem cbtm_y_act (i : CbtIdx m) :
    y (cbtmOmega K i) = cbtmOmega K (cbtmNu (K.C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) i) := by
  rcases i with r | ⟨_ | _, _ | _⟩
  · exact cbtm_y_inl K hrel hy r
  · exact cbtm_y_c11 K hrel hy
  · exact cbtm_y_c12 K hrel hy
  · exact cbtm_y_fix K hrel hy false
  · exact cbtm_y_fix K hrel hy true

end ActY

end Model

variable [Finite V] {G T : Subgroup (MulAut V)} {t : MulAut V}
  {X₁ X₂ : Subgroup (MulAut V)} in
theorem CbtCtx.false_of_rel (K : CbtCtx G T Y t m X₁ X₂) (hrel : CbtRel K) : False := by
  obtain ⟨p, q, hpq⟩ := K.exists_pair
  have hS := cbtm_closure K hrel
  have hdY : cbtmD K hpq ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact cbtm_comm hS (cbtm_y_act K hrel hz) (cbtm_d_act K hrel hpq)
      (fun r hr => mem_fixV.mp hr.1 z (K.L₁.hYX hz)) (fun r hr => cbtm_d_R K hpq hr)
      (fun i => by rcases i with r | ⟨s, b⟩ <;> rfl)
  have htY : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => (K.t_comm_Y z hz).symm
  have hcomm : cbtmD K hpq * t = t * cbtmD K hpq :=
    cbtm_comm hS (cbtm_d_act K hrel hpq) (cbtm_t_act K) (fun r hr => cbtm_d_R K hpq hr)
      hrel.t_fix_R (fun i => by rcases i with r | ⟨s, b⟩ <;> rfl)
  have hdG : cbtmD K hpq ∈ G := by
    unfold cbtmD
    exact G.mul_mem (G.mul_mem (K.h₁.le_G (K.L₁.xElt hpq).2) (K.h₂.le_G (K.L₂.xElt hpq).2))
      (K.h₁.le_G (K.L₁.xElt hpq).2)
  have hd2 : cbtmD K hpq ^ 2 = 1 := by
    have e1 := K.L₁.xElt_sq hpq
    have e2 := K.L₂.xElt_sq hpq
    unfold cbtmD
    rw [sq]
    calc (K.L₁.xElt hpq : MulAut V) * (K.L₂.xElt hpq : MulAut V) * (K.L₁.xElt hpq : MulAut V) *
          ((K.L₁.xElt hpq : MulAut V) * (K.L₂.xElt hpq : MulAut V) * (K.L₁.xElt hpq : MulAut V))
        = (K.L₁.xElt hpq : MulAut V) * ((K.L₂.xElt hpq : MulAut V) *
            ((K.L₁.xElt hpq : MulAut V) * (K.L₁.xElt hpq : MulAut V)) *
              (K.L₂.xElt hpq : MulAut V)) * (K.L₁.xElt hpq : MulAut V) := by group
      _ = (K.L₁.xElt hpq : MulAut V) * ((K.L₂.xElt hpq : MulAut V) *
            (K.L₂.xElt hpq : MulAut V)) * (K.L₁.xElt hpq : MulAut V) := by rw [e1, mul_one]
      _ = (K.L₁.xElt hpq : MulAut V) * (K.L₁.xElt hpq : MulAut V) := by rw [e2, mul_one]
      _ = 1 := e1
  have hdv₁ : cbtmD K hpq K.L₁.vvec = K.L₂.vvec := by
    rw [cbtm_v₁_eq K, map_mul, cbtm_d_act K hrel hpq, cbtm_d_act K hrel hpq]
    exact (cbtm_v₂_eq K).symm
  have hv₁v₂ : K.L₁.vvec ≠ K.L₂.vvec := by
    intro h
    have h1 : K.L₁.vvec ∈ commV X₁ ⊓ fixV X₁ := by
      refine ⟨?_, by rw [h]; exact hrel.v₂_fix⟩
      exact mul_mem (K.L₁.D.hwmem K.L₁.D.a).1 (K.L₁.D.hwmem K.L₁.D.b).1
    rw [(K.L₁.D.split K.hm K.hodd).2, Subgroup.mem_bot] at h1
    exact K.L₁.vvec_ne_one K.hV h1
  have hd1 : cbtmD K hpq ≠ 1 := by
    intro h
    rw [h, MulAut.one_apply] at hdv₁
    exact hv₁v₂ hdv₁
  have hdt : cbtmD K hpq ≠ t := by
    intro h
    rw [h, K.L₁.t_vvec] at hdv₁
    exact hv₁v₂ hdv₁
  exact K.h2 V K.hV G T Y K.h m K.hm K.hodd K.hY (cbtmD K hpq) t hdG K.htG hdY htY hd2 K.ht2
    hd1 K.ht1 hdt hcomm

end CFSG.CGT.PushingUpLit.CGT6
