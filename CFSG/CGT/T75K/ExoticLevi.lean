module

public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup
public import CFSG.CGT.T75K.ExoticData

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75 Module
open scoped MatrixGroups Matrix

variable {G : Type} [Group G]

section Basic

variable {T T₁ : Subgroup G} {n m : ℕ}

theorem m_ne_zero (hc : Sec6Ctx T T₁ n m) : m ≠ 0 := by
  rintro rfl
  have h4 := hc.hy.card
  rw [hc.hT, pow_zero, one_pow] at h4
  omega

theorem card_F (hc : Sec6Ctx T T₁ n m) : Nat.card (GaloisField 2 m) = 2 ^ m :=
  GaloisField.card 2 m (m_ne_zero hc)

theorem mul_comm_T (hc : Sec6Ctx T T₁ n m) {t s : G} (ht : t ∈ T) (hs : s ∈ T) :
    t * s = s * t :=
  elemAbelian_mul_comm hc.hy.pair.wc.1 ht hs

theorem mul_self_T₁ (hc : Sec6Ctx T T₁ n m) {u : G} (hu : u ∈ T₁) : u * u = 1 :=
  elemAbelian_mul_self hc.sec3.cfg.wc₁.1 hu

theorem comm_L_L₁ (hc : Sec6Ctx T T₁ n m) {c u : G} (hc' : c ∈ normIn T T₁)
    (hu : u ∈ normIn T₁ T) : c * u = u * c :=
  hc.sec3.cfg.comm_L_L₁ hc' hu

theorem conj_eq_iff (hc : Sec6Ctx T T₁ n m) {u t : G} (hu : u ∈ normIn T₁ T) (hu1 : u ≠ 1)
    (ht : t ∈ T) : u * t * u⁻¹ = t ↔ t ∈ normIn T T₁ := by
  rw [← hc.sec3.cfg.inf_centralizer_eq_normIn hu hu1, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => ⟨ht, h.symm⟩, fun h => h.2.symm⟩

end Basic

section Fix

variable {T T₁ H : Subgroup G} {n m : ℕ} {D : LinData T H n m}

theorem fixvec_iff (hc : Sec6Ctx T T₁ n m) (hL₁H : normIn T₁ T ≤ H) {u t : G}
    (hu : u ∈ normIn T₁ T) (hu1 : u ≠ 1) (ht : t ∈ T) :
    sv (D.mat u) (D.vec t) = D.vec t ↔ t ∈ normIn T T₁ := by
  obtain ⟨hmem, hv⟩ := LinData.vec_conj (D := D) (hL₁H hu) ht
  rw [← hv, ← conj_eq_iff hc hu hu1 ht]
  constructor
  · intro h; exact LinData.vec_inj hmem ht h
  · intro h; rw [h]

theorem card_fix (hc : Sec6Ctx T T₁ n m) (hL₁H : normIn T₁ T ≤ H) {x : G}
    (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1) :
    Nat.card {w : Fin n → GaloisField 2 m // sv (D.mat x) w = w} =
      Nat.card ↥(normIn T T₁) := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun t : ↥(normIn T T₁) =>
    (⟨D.vec t, (fixvec_iff hc hL₁H hx hx1 (normIn_le _ _ t.2)).2 t.2⟩ :
      {w : Fin n → GaloisField 2 m // sv (D.mat x) w = w})) ⟨?_, ?_⟩
  · intro t t' h
    have h' : D.vec (t : G) = D.vec (t' : G) := congrArg Subtype.val h
    exact Subtype.ext (LinData.vec_inj (normIn_le _ _ t.2) (normIn_le _ _ t'.2) h')
  · rintro ⟨w, hw⟩
    obtain ⟨t, ht, rfl⟩ := LinData.exists_vec (D := D) w
    have htL : t ∈ normIn T T₁ := (fixvec_iff hc hL₁H hx hx1 ht).1 hw
    exact ⟨⟨t, htL⟩, rfl⟩

end Fix

section Ctx

variable {T T₁ H : Subgroup G} {n m : ℕ}

structure LCtx (T T₁ H : Subgroup G) (n m : ℕ) (D : LinData T H n m) (x : G) where
  hc : Sec6Ctx T T₁ n m
  hL₁H : normIn T₁ T ≤ H
  hx : x ∈ normIn T₁ T
  hx1 : x ≠ 1
  f₀ : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)
  p : Fin n → GaloisField 2 m
  e₁ : Fin n → GaloisField 2 m
  hfp : f₀ p = 0
  hf₀ : f₀ ≠ 0
  hp : p ≠ 0
  he : f₀ e₁ = 1
  htr : IsTransvection (D.mat x)
  hxact : ∀ y, sv (D.mat x) y = y + f₀ y • p

theorem exists_lctx (hc : Sec6Ctx T T₁ n m) (D : LinData T H n m) (hL₁H : normIn T₁ T ≤ H)
    {x : G} (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1) : Nonempty (LCtx T T₁ H n m D x) := by
  have hxH : x ∈ H := hL₁H hx
  have hxT₁ : x ∈ T₁ := normIn_le _ _ hx
  have hxT : x ∉ T := fun h => hx1 (by
    have : x ∈ T ⊓ T₁ := ⟨h, hxT₁⟩
    rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at this
    exact this)
  have hx2 : D.mat x * D.mat x = 1 := by
    rw [← LinData.mat_mul hxH hxH, mul_self_T₁ hc hxT₁, LinData.mat_one]
  have hx1' : D.mat x ≠ 1 := fun h => hxT ((LinData.mat_eq_one_iff hxH).1 h)
  have hcard : Nat.card {w : Fin n → GaloisField 2 m //
      (D.mat x : Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ w = w} =
      Nat.card (GaloisField 2 m) ^ (n - 1) := by
    have := card_fix (D := D) hc hL₁H hx hx1
    rw [hc.card_normIn] at this
    rw [card_F hc]
    exact this
  have htr := isTransvection_of_card_fixed hx2 hx1' hcard
  obtain ⟨f₀, p, hfp, hf₀, hp, hxact⟩ := exists_data_of_isTransvection htr
  obtain ⟨e₁, he⟩ := exists_apply_eq_one_of_ne_zero hf₀
  exact ⟨⟨hc, hL₁H, hx, hx1, f₀, p, e₁, hfp, hf₀, hp, he, htr, hxact⟩⟩

namespace LCtx

variable {D : LinData T H n m} {x : G} (C : LCtx T T₁ H n m D x)

theorem mem_L_iff {t : G} (ht : t ∈ T) : t ∈ normIn T T₁ ↔ C.f₀ (D.vec t) = 0 := by
  rw [← fixvec_iff C.hc C.hL₁H C.hx C.hx1 ht, C.hxact]
  constructor
  · intro h
    have h1 : C.f₀ (D.vec t) • C.p = 0 := by
      rwa [add_eq_left] at h
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 C.hp
  · intro h
    rw [h, zero_smul, add_zero]

theorem unip_mat {u : G} (hu : u ∈ normIn T₁ T) : D.mat u ∈ Unip C.f₀ := by
  by_cases hu1 : u = 1
  · rw [hu1, LinData.mat_one]
    exact unip_one
  · apply unip_of_invol
    · rw [← LinData.mat_mul (C.hL₁H hu) (C.hL₁H hu), mul_self_T₁ C.hc (normIn_le _ _ hu),
        LinData.mat_one]
    · intro y
      obtain ⟨t, ht, rfl⟩ := LinData.exists_vec (D := D) y
      rw [fixvec_iff C.hc C.hL₁H hu hu1 ht, C.mem_L_iff ht]

@[expose] noncomputable def lb (u : G) : Fin n → GaloisField 2 m := lab C.e₁ (D.mat u)

theorem lb_mem {u : G} (hu : u ∈ normIn T₁ T) : C.f₀ (C.lb u) = 0 :=
  unip_lab_mem (C.unip_mat hu)

theorem lb_mul {u v : G} (hu : u ∈ normIn T₁ T) (hv : v ∈ normIn T₁ T) :
    C.lb (u * v) = C.lb u + C.lb v := by
  unfold lb
  rw [LinData.mat_mul (C.hL₁H hu) (C.hL₁H hv)]
  exact unip_lab_mul (C.unip_mat hu) (C.unip_mat hv)

theorem lb_inv {u : G} (hu : u ∈ normIn T₁ T) : C.lb u⁻¹ = - C.lb u := by
  unfold lb
  rw [LinData.mat_inv (C.hL₁H hu)]
  exact unip_lab_inv (C.unip_mat hu)

theorem lb_x : C.lb x = C.p := by
  unfold lb lab
  rw [C.hxact, C.he, one_smul]
  abel

theorem lb_inj {u v : G} (hu : u ∈ normIn T₁ T) (hv : v ∈ normIn T₁ T) (h : C.lb u = C.lb v) :
    u = v := by
  have hm : D.mat u = D.mat v := unip_ext C.he (C.unip_mat hu) (C.unip_mat hv) h
  have huH := C.hL₁H hu
  have hvH := C.hL₁H hv
  have h1 : u⁻¹ * v ∈ T := by
    rw [← LinData.mat_eq_one_iff (H.mul_mem (H.inv_mem huH) hvH),
      LinData.mat_mul (H.inv_mem huH) hvH, LinData.mat_inv huH, hm, inv_mul_cancel]
  have h2 : u⁻¹ * v ∈ T₁ := T₁.mul_mem (T₁.inv_mem (normIn_le _ _ hu)) (normIn_le _ _ hv)
  have h3 : u⁻¹ * v ∈ T ⊓ T₁ := ⟨h1, h2⟩
  rw [C.hc.sec3.cfg.inf, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.1 h3

theorem card_ker : Nat.card ↥(LinearMap.ker C.f₀) = Nat.card ↥(normIn T T₁) := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun t : ↥(normIn T T₁) =>
    (⟨D.vec t, LinearMap.mem_ker.2 ((C.mem_L_iff (normIn_le _ _ t.2)).1 t.2)⟩ :
      ↥(LinearMap.ker C.f₀))) ⟨?_, ?_⟩
  · intro t t' h
    have h' : D.vec (t : G) = D.vec (t' : G) := congrArg Subtype.val h
    exact Subtype.ext (LinData.vec_inj (normIn_le _ _ t.2) (normIn_le _ _ t'.2) h')
  · rintro ⟨w, hw⟩
    obtain ⟨t, ht, rfl⟩ := LinData.exists_vec (D := D) w
    have := (C.mem_L_iff ht).2 (LinearMap.mem_ker.1 hw)
    exact ⟨⟨t, this⟩, rfl⟩

theorem lb_surj {w : Fin n → GaloisField 2 m} (hw : C.f₀ w = 0) :
    ∃ u ∈ normIn T₁ T, C.lb u = w := by
  let g : ↥(normIn T₁ T) → ↥(LinearMap.ker C.f₀) :=
    fun u => ⟨C.lb u, LinearMap.mem_ker.2 (C.lb_mem u.2)⟩
  have hinj : Function.Injective g := fun u v h =>
    Subtype.ext (C.lb_inj u.2 v.2 (congrArg Subtype.val h))
  have hle : Nat.card ↥(LinearMap.ker C.f₀) ≤ Nat.card ↥(normIn T₁ T) := by
    rw [C.card_ker, C.hc.card_normIn_swap]
  obtain ⟨u, hu⟩ := (Function.Injective.bijective_of_nat_card_le hinj hle).2
    ⟨w, LinearMap.mem_ker.2 hw⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem conj_L₁ {τ : SL(n, GaloisField 2 m)} (hτ : ∀ y, C.f₀ (sv τ y) = C.f₀ y) {u : G}
    (hu : u ∈ normIn T₁ T) :
    ∃ u' ∈ normIn T₁ T, D.mat u' = τ * D.mat u * τ⁻¹ ∧ C.lb u' = sv τ (C.lb u) := by
  obtain ⟨hmem, hlab⟩ := unip_conj C.he hτ (C.unip_mat hu)
  obtain ⟨u', hu', hlb'⟩ := C.lb_surj (w := lab C.e₁ (τ * D.mat u * τ⁻¹)) (unip_lab_mem hmem)
  refine ⟨u', hu', unip_ext C.he (C.unip_mat hu') hmem hlb', ?_⟩
  rw [hlb', hlab]
  rfl

end LCtx

end Ctx

section H0

variable {T T₁ H : Subgroup G} {n m : ℕ} {D : LinData T H n m} {x : G}

structure H0 (C : LCtx T T₁ H n m D x) where
  h₀ : G
  τ : SL(n, GaloisField 2 m)
  f₁ : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)
  v : Fin n → GaloisField 2 m
  uv : G
  hH : h₀ ∈ H
  hsq : h₀ * h₀ = 1
  hmat : D.mat h₀ = τ
  hτ : ∀ y, sv τ y = y + f₁ y • C.p
  hf₁p : f₁ C.p = 0
  hf₁v : f₁ v = 1
  hfv : C.f₀ v = 0
  huv : uv ∈ normIn T₁ T
  hlbv : C.lb uv = v

variable (C : LCtx T T₁ H n m D x)

theorem exists_H0 (hn : 3 ≤ n) : Nonempty (H0 C) := by
  have hc := C.hc
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 (m_ne_zero hc))
  have hv : ∃ v, C.f₀ v = 0 ∧ v ∉ Submodule.span (GaloisField 2 m) {C.p} := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card ↥(LinearMap.ker C.f₀) ≤
        Nat.card ↥(Submodule.span (GaloisField 2 m) {C.p}) :=
      Nat.card_le_card_of_injective (fun w => ⟨w.1, hcon w.1 (LinearMap.mem_ker.1 w.2)⟩)
        (fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext h')
    have h2 : Nat.card ↥(Submodule.span (GaloisField 2 m) {C.p}) ≤ Nat.card (GaloisField 2 m) := by
      apply Nat.card_le_card_of_surjective (fun a : GaloisField 2 m =>
        (⟨a • C.p, Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)⟩ :
          ↥(Submodule.span (GaloisField 2 m) {C.p})))
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      exact ⟨a, rfl⟩
    rw [C.card_ker, hc.card_normIn] at h1
    rw [card_F hc] at h2
    have h3 : (2 ^ m) ^ 2 ≤ (2 ^ m) ^ (n - 1) :=
      Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq) (by omega)
    have h4 : (2 ^ m) ^ 2 ≤ 2 ^ m := h3.trans (h1.trans h2)
    nlinarith
  obtain ⟨v, hfv, hvspan⟩ := hv
  obtain ⟨f₁, hf₁p, hf₁v⟩ := exists_dual_of_notMem_span hvspan
  have hf₁ : f₁ ≠ 0 := fun h => by rw [h] at hf₁v; simp at hf₁v
  obtain ⟨τ, hτ, hτtr⟩ := exists_isTransvection hf₁p hf₁ C.hp
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection C.htr hτtr
  obtain ⟨g, hgH, hg⟩ := LinData.exists_mat (D := D) W
  obtain ⟨uv, huv, hlbv⟩ := C.lb_surj hfv
  have hxH : x ∈ H := C.hL₁H C.hx
  refine ⟨⟨g * x * g⁻¹, τ, f₁, v, uv, ?_, ?_, ?_, hτ, hf₁p, hf₁v, hfv, huv, hlbv⟩⟩
  · exact H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH)
  · have e : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    rw [e, mul_self_T₁ hc (normIn_le _ _ C.hx)]
    group
  · rw [LinData.mat_mul (H.mul_mem hgH hxH) (H.inv_mem hgH), LinData.mat_mul hgH hxH,
      LinData.mat_inv hgH, hg]
    exact hW

end H0

section Lift

variable {T T₁ H : Subgroup G} {n m : ℕ} {D : LinData T H n m} {x : G} {C : LCtx T T₁ H n m D x}
  (P : H0 C)

theorem H0.hτf (y : Fin n → GaloisField 2 m) : C.f₀ (sv P.τ y) = C.f₀ y := by
  rw [P.hτ, map_add, map_smul, C.hfp, smul_zero, add_zero]

theorem H0.vec_conj_lift {g : G} (hg : g ∈ H) (hm : D.mat g = P.τ) {t : G} (ht : t ∈ T) :
    g * t * g⁻¹ ∈ T ∧ D.vec (g * t * g⁻¹) = sv P.τ (D.vec t) := by
  obtain ⟨h1, h2⟩ := LinData.vec_conj (D := D) hg ht
  exact ⟨h1, by rw [h2, hm]⟩

theorem H0.conj_L₁_mod {g : G} (hg : g ∈ H) (hm : D.mat g = P.τ) {u : G}
    (hu : u ∈ normIn T₁ T) :
    ∃ u' ∈ normIn T₁ T, C.lb u' = sv P.τ (C.lb u) ∧ ∃ t ∈ T, g * u * g⁻¹ = u' * t := by
  obtain ⟨u', hu', hmat, hlb⟩ := C.conj_L₁ P.hτf hu
  refine ⟨u', hu', hlb, u'⁻¹ * (g * u * g⁻¹), ?_, by group⟩
  have hH' : u'⁻¹ * (g * u * g⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem (C.hL₁H hu')) (H.mul_mem (H.mul_mem hg (C.hL₁H hu)) (H.inv_mem hg))
  rw [← LinData.mat_eq_one_iff hH', LinData.mat_mul (H.inv_mem (C.hL₁H hu'))
    (H.mul_mem (H.mul_mem hg (C.hL₁H hu)) (H.inv_mem hg)),
    LinData.mat_mul (H.mul_mem hg (C.hL₁H hu)) (H.inv_mem hg), LinData.mat_mul hg (C.hL₁H hu),
    LinData.mat_inv (C.hL₁H hu'), LinData.mat_inv hg, hm, hmat]
  group

theorem H0.conj_L₁ {g : G} (hg : g ∈ H) (hm : D.mat g = P.τ)
    (hT₁ : g ∈ Subgroup.normalizer (T₁ : Set G)) {u : G} (hu : u ∈ normIn T₁ T) :
    g * u * g⁻¹ ∈ normIn T₁ T ∧ C.lb (g * u * g⁻¹) = sv P.τ (C.lb u) := by
  have hmem : g * u * g⁻¹ ∈ normIn T₁ T := by
    refine mem_normIn.2 ⟨conj_mem_of_mem_normalizer hT₁ (normIn_le _ _ hu), ?_⟩
    have hgN := D.hHN hg
    have huN : u ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hu).2
    exact (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hgN huN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hgN)
  refine ⟨hmem, ?_⟩
  obtain ⟨-, hlab⟩ := unip_conj C.he P.hτf (C.unip_mat hu)
  show lab C.e₁ (D.mat (g * u * g⁻¹)) = sv P.τ (lab C.e₁ (D.mat u))
  rw [LinData.mat_mul (H.mul_mem hg (C.hL₁H hu)) (H.inv_mem hg), LinData.mat_mul hg (C.hL₁H hu),
    LinData.mat_inv hg, hm]
  exact hlab

end Lift

section Conj

variable {T T₁ H : Subgroup G} {n m : ℕ} {D : LinData T H n m} {x : G} (C : LCtx T T₁ H n m D x)

theorem LCtx.cx_formula {t : G} (ht : t ∈ T) :
    t * x * t⁻¹ = x * (x * t * x⁻¹ * t⁻¹) ∧ x * t * x⁻¹ * t⁻¹ ∈ T ∧
      D.vec (x * t * x⁻¹ * t⁻¹) = C.f₀ (D.vec t) • C.p := by
  have hxH := C.hL₁H C.hx
  have hx2 : x * x = 1 := mul_self_T₁ C.hc (normIn_le _ _ C.hx)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  obtain ⟨hmem, hv⟩ := LinData.vec_conj (D := D) hxH ht
  have hmem2 : x * t * x⁻¹ * t⁻¹ ∈ T := T.mul_mem hmem (T.inv_mem ht)
  refine ⟨?_, hmem2, ?_⟩
  · rw [hxi]
    calc t * x * t⁻¹ = x * x * (t * x * t⁻¹) := by rw [hx2, one_mul]
      _ = x * (x * t * x * t⁻¹) := by group
  · rw [LinData.vec_mul hmem (T.inv_mem ht), hv, LinData.vec_inv ht, C.hxact]
    abel

theorem LCtx.exists_conj_eq {w : G} (hw : w ∈ T) (hw' : ∃ a : GaloisField 2 m, D.vec w = a • C.p) :
    ∃ t ∈ T, t * x * t⁻¹ = x * w := by
  obtain ⟨a, ha⟩ := hw'
  obtain ⟨t, ht, hvt⟩ := LinData.exists_vec (D := D) (a • C.e₁)
  obtain ⟨h1, hmem, hv⟩ := C.cx_formula ht
  have h2 : x * t * x⁻¹ * t⁻¹ = w := by
    apply LinData.vec_inj hmem hw
    rw [hv, hvt, ha, map_smul, C.he, smul_eq_mul, mul_one]
  exact ⟨t, ht, by rw [h1, h2]⟩

end Conj

section Z

variable {T T₁ H : Subgroup G} {n m : ℕ} {D : LinData T H n m} {x : G} {C : LCtx T T₁ H n m D x}
  (P : H0 C)

theorem H0.exists_z : ∃ z zv : G, z ∈ normIn T T₁ ∧ zv ∈ normIn T T₁ ∧
    P.h₀ * x * P.h₀⁻¹ = x * z ∧ P.h₀ * P.uv * P.h₀⁻¹ = (P.uv * x) * zv ∧
    ∃ a : GaloisField 2 m, D.vec z = a • C.p := by
  have hc := C.hc
  have hxT₁ : x ∈ T₁ := normIn_le _ _ C.hx
  have hx2 : x * x = 1 := mul_self_T₁ hc hxT₁
  have huvT₁ : P.uv ∈ T₁ := normIn_le _ _ P.huv
  have huv2 : P.uv * P.uv = 1 := mul_self_T₁ hc huvT₁
  obtain ⟨u', hu', hlb', z, hzT, hz⟩ := P.conj_L₁_mod P.hH P.hmat C.hx
  have hu'x : u' = x := by
    apply C.lb_inj hu' C.hx
    rw [hlb', C.lb_x, P.hτ, P.hf₁p, zero_smul, add_zero]
  subst hu'x
  have hzL : z ∈ normIn T T₁ := by
    refine mem_normIn_of_mul_mul_self hc C.hx C.hx1 hzT ?_
    rw [← hz]
    calc P.h₀ * u' * P.h₀⁻¹ * (P.h₀ * u' * P.h₀⁻¹) = P.h₀ * (u' * u') * P.h₀⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨u'', hu'', hlb'', zv, hzvT, hzv⟩ := P.conj_L₁_mod P.hH P.hmat P.huv
  have hu''e : u'' = P.uv * u' := by
    apply C.lb_inj hu'' ((normIn T₁ T).mul_mem P.huv C.hx)
    rw [hlb'', P.hlbv, P.hτ, P.hf₁v, one_smul, C.lb_mul P.huv C.hx, P.hlbv, C.lb_x]
  subst hu''e
  have hne : P.uv * u' ≠ 1 := by
    intro h
    have h1 : C.lb (P.uv * u') = 0 := by
      rw [h]
      unfold LCtx.lb
      rw [LinData.mat_one]
      exact unip_lab_one
    rw [C.lb_mul P.huv C.hx, P.hlbv, C.lb_x] at h1
    have h2 := congrArg P.f₁ h1
    rw [map_add, P.hf₁v, P.hf₁p, add_zero, map_zero] at h2
    exact one_ne_zero h2
  have hzvL : zv ∈ normIn T T₁ := by
    refine mem_normIn_of_mul_mul_self hc ((normIn T₁ T).mul_mem P.huv C.hx) hne hzvT ?_
    rw [← hzv]
    calc P.h₀ * P.uv * P.h₀⁻¹ * (P.h₀ * P.uv * P.h₀⁻¹) = P.h₀ * (P.uv * P.uv) * P.h₀⁻¹ := by group
      _ = 1 := by rw [huv2]; group
  have hinv : P.h₀⁻¹ = P.h₀ := inv_eq_of_mul_eq_one_right P.hsq
  have e2 : P.h₀ * (P.h₀ * P.uv * P.h₀⁻¹) * P.h₀⁻¹ = P.uv := by
    rw [hinv]
    calc P.h₀ * (P.h₀ * P.uv * P.h₀) * P.h₀ = (P.h₀ * P.h₀) * P.uv * (P.h₀ * P.h₀) := by group
      _ = P.uv := by rw [P.hsq]; group
  have e1 : P.h₀ * ((P.uv * u') * zv) * P.h₀⁻¹ =
      (P.h₀ * P.uv * P.h₀⁻¹) * (P.h₀ * u' * P.h₀⁻¹) * (P.h₀ * zv * P.h₀⁻¹) := by group
  obtain ⟨hwT, hwv⟩ := P.vec_conj_lift P.hH P.hmat hzvT
  rw [hzv] at e2
  rw [e1, hzv, hz] at e2
  have hcomm : zv * u' = u' * zv := comm_L_L₁ hc hzvL C.hx
  have e3 : P.uv * (zv * z * (P.h₀ * zv * P.h₀⁻¹)) = P.uv * 1 := by
    calc P.uv * (zv * z * (P.h₀ * zv * P.h₀⁻¹)) = P.uv * zv * z * (P.h₀ * zv * P.h₀⁻¹) := by group
      _ = P.uv * (zv * (u' * u')) * z * (P.h₀ * zv * P.h₀⁻¹) := by rw [hx2]; group
      _ = P.uv * (zv * u') * u' * z * (P.h₀ * zv * P.h₀⁻¹) := by group
      _ = P.uv * (u' * zv) * u' * z * (P.h₀ * zv * P.h₀⁻¹) := by rw [hcomm]
      _ = (P.uv * u' * zv) * (u' * z) * (P.h₀ * zv * P.h₀⁻¹) := by group
      _ = P.uv := e2
      _ = P.uv * 1 := (mul_one _).symm
  have e4 := mul_left_cancel e3
  have hzvT' : zv ∈ T := normIn_le _ _ hzvL
  have hv : D.vec zv + D.vec z + D.vec (P.h₀ * zv * P.h₀⁻¹) = 0 := by
    rw [← LinData.vec_mul hzvT' hzT, ← LinData.vec_mul (T.mul_mem hzvT' hzT) hwT, e4,
      LinData.vec_one]
  rw [hwv, P.hτ] at hv
  have hchar : D.vec zv + D.vec zv = 0 := add_self_of_char_two _
  refine ⟨z, zv, hzL, hzvL, hz, hzv, -(P.f₁ (D.vec zv)), ?_⟩
  calc D.vec z = (D.vec zv + D.vec z + (D.vec zv + P.f₁ (D.vec zv) • C.p)) -
        (D.vec zv + D.vec zv) - P.f₁ (D.vec zv) • C.p := by abel
    _ = (-(P.f₁ (D.vec zv))) • C.p := by rw [hv, hchar]; simp

end Z

section Levi

variable {T T₁ H : Subgroup G} {n m : ℕ}

structure LeviProps (T T₁ : Subgroup G) (x h : G) (q : ℕ) : Prop where
  hT : h ∈ Subgroup.normalizer (T : Set G)
  hx : h * x * h⁻¹ = x
  hZ₀ : ∃ Z₀ : Set G, Z₀.ncard ≤ q ∧ ∀ c ∈ normIn T T₁, h * c * h⁻¹ * c⁻¹ ∈ Z₀
  hZ₁ : ∃ Z₁ : Set G, Z₁.ncard ≤ q ∧ ∀ u ∈ normIn T₁ T, h * u * h⁻¹ * u⁻¹ ∈ Z₁
  hv : ∃ u ∈ normIn T₁ T, h * u * h⁻¹ = u * x
  hT0 : ∀ c ∈ normIn T T₁, ∃ t ∈ T, t * x * t⁻¹ = x * (c * (h * c⁻¹ * h⁻¹))

theorem exists_levi (hc : Sec6Ctx T T₁ n m) (hn : 3 ≤ n) (D : LinData T H n m)
    (hL₁H : normIn T₁ T ≤ H) {x : G} (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1) :
    ∃ h : G, LeviProps T T₁ x h (2 ^ m) := by
  obtain ⟨C⟩ := exists_lctx hc D hL₁H hx hx1
  obtain ⟨P⟩ := exists_H0 C hn
  obtain ⟨z, zv, hzL, hzvL, hz, hzv, a, hza⟩ := P.exists_z
  obtain ⟨t₀, ht₀, htx⟩ := C.exists_conj_eq (normIn_le _ _ hzL) ⟨a, hza⟩
  have ht₀H : t₀⁻¹ ∈ H := D.hTH (T.inv_mem ht₀)
  have hhH : t₀⁻¹ * P.h₀ ∈ H := H.mul_mem ht₀H P.hH
  have hhm : D.mat (t₀⁻¹ * P.h₀) = P.τ := by
    rw [LinData.mat_mul ht₀H P.hH, LinData.mat_of_mem_T (T.inv_mem ht₀), one_mul, P.hmat]
  have hhx : t₀⁻¹ * P.h₀ * x * (t₀⁻¹ * P.h₀)⁻¹ = x := by
    calc t₀⁻¹ * P.h₀ * x * (t₀⁻¹ * P.h₀)⁻¹ = t₀⁻¹ * (P.h₀ * x * P.h₀⁻¹) * t₀ := by group
      _ = t₀⁻¹ * (x * z) * t₀ := by rw [hz]
      _ = t₀⁻¹ * (t₀ * x * t₀⁻¹) * t₀ := by rw [htx]
      _ = x := by group
  generalize t₀⁻¹ * P.h₀ = h at hhH hhm hhx
  have hhN : h ∈ Subgroup.normalizer (T : Set G) := D.hHN hhH
  have hxT₁ : x ∈ T₁ := normIn_le _ _ hx
  have hhT₁ : h ∈ Subgroup.normalizer (T₁ : Set G) := by
    refine hc.sec3.cfg.wc₁.centralizer_le_normalizer hxT₁ hx1 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hhx
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  refine ⟨h, ⟨hhN, hhx, ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨{t | t ∈ T ∧ ∃ a : GaloisField 2 m, D.vec t = a • C.p}, ?_, ?_⟩
    · calc _ ≤ (Set.range (fun a : GaloisField 2 m => a • C.p)).ncard :=
            Set.ncard_le_ncard_of_injOn D.vec
              (fun t ht => by obtain ⟨-, a, ha⟩ := ht; exact ⟨a, ha.symm⟩)
              (fun t ht t' ht' h => LinData.vec_inj ht.1 ht'.1 h) (Set.toFinite _)
        _ ≤ Nat.card (GaloisField 2 m) := ncard_range_smul_le _
        _ = 2 ^ m := card_F hc
    · intro c hcL
      have hcT := normIn_le _ _ hcL
      obtain ⟨h1, h2⟩ := P.vec_conj_lift hhH hhm hcT
      have h3 : h * c * h⁻¹ * c⁻¹ ∈ T := T.mul_mem h1 (T.inv_mem hcT)
      refine ⟨h3, P.f₁ (D.vec c), ?_⟩
      rw [LinData.vec_mul h1 (T.inv_mem hcT), h2, LinData.vec_inv hcT, P.hτ]
      abel
  · refine ⟨{u | u ∈ normIn T₁ T ∧ ∃ a : GaloisField 2 m, C.lb u = a • C.p}, ?_, ?_⟩
    · calc _ ≤ (Set.range (fun a : GaloisField 2 m => a • C.p)).ncard :=
            Set.ncard_le_ncard_of_injOn C.lb
              (fun t ht => by obtain ⟨-, a, ha⟩ := ht; exact ⟨a, ha.symm⟩)
              (fun u hu u' hu' h => C.lb_inj hu.1 hu'.1 h) (Set.toFinite _)
        _ ≤ Nat.card (GaloisField 2 m) := ncard_range_smul_le _
        _ = 2 ^ m := card_F hc
    · intro u hu
      obtain ⟨hmem, hlb⟩ := P.conj_L₁ hhH hhm hhT₁ hu
      have hmem2 : h * u * h⁻¹ * u⁻¹ ∈ normIn T₁ T :=
        (normIn T₁ T).mul_mem hmem ((normIn T₁ T).inv_mem hu)
      refine ⟨hmem2, P.f₁ (C.lb u), ?_⟩
      rw [C.lb_mul hmem ((normIn T₁ T).inv_mem hu), hlb, C.lb_inv hu, P.hτ]
      abel
  · refine ⟨P.uv, P.huv, ?_⟩
    obtain ⟨hmem, hlb⟩ := P.conj_L₁ hhH hhm hhT₁ P.huv
    apply C.lb_inj hmem ((normIn T₁ T).mul_mem P.huv C.hx)
    rw [hlb, P.hlbv, P.hτ, P.hf₁v, one_smul, C.lb_mul P.huv C.hx, P.hlbv, C.lb_x]
  · intro c hcL
    have hcT := normIn_le _ _ hcL
    have hci : c⁻¹ ∈ T := T.inv_mem hcT
    obtain ⟨h1, h2⟩ := P.vec_conj_lift hhH hhm hci
    have hwT : c * (h * c⁻¹ * h⁻¹) ∈ T := T.mul_mem hcT h1
    refine C.exists_conj_eq hwT ⟨-(P.f₁ (D.vec c)), ?_⟩
    rw [LinData.vec_mul hcT h1, h2, LinData.vec_inv hcT, sv_neg, P.hτ, neg_smul]
    abel

end Levi

end CFSG.CGT.T75K
