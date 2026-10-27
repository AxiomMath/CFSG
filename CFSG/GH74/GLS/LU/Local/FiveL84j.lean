module

public import CFSG.GH74.GLS.LU.Local.FiveL84f
public import CFSG.GH74.GLS.LU.Local.FiveL84g
public import CFSG.GH74.GLS.LU.Local.FiveL84i
public import CFSG.GH74.GLS.LU.Local.FiveL85c

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section J4

variable {G : Type} [Group G]

theorem QV.sub_congr {R X : Subgroup G} [Fact (QData R X)] {A B : Subgroup G} (hAB : A = B)
    (hA : A ≤ R) (hB : B ≤ R) : QV.sub (X := X) A hA = QV.sub (X := X) B hB := by
  subst hAB; rfl

theorem QV.sub_eq_bot_of_le {R X : Subgroup G} [Fact (QData R X)] {A : Subgroup G} (hA : A ≤ R)
    (hAX : A ≤ X) : QV.sub (X := X) A hA = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨a, ha, rfl⟩ := (QV.mem_sub hA).1 hv
  rw [(QV.mk_eq_zero_iff (hA ha)).2 (hAX ha)]
  exact Submodule.zero_mem _

theorem sup_inf_sup_le {A B M Xs : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) (hM : M ⊓ Xs = ⊥)
    (hAB : A ⊓ B = ⊥) (hcA : ∀ a ∈ A, ∀ s ∈ Xs, a * s = s * a)
    (hcB : ∀ b ∈ B, ∀ s ∈ Xs, b * s = s * b) : (A ⊔ Xs) ⊓ (B ⊔ Xs) ≤ Xs := by
  intro x ⟨hxA, hxB⟩
  obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_of_commute hcA).1 hxA
  obtain ⟨b, hb, s', hs', hbs⟩ := (mem_sup_of_commute hcB).1 hxB
  have hba : b⁻¹ * a ∈ Xs := by
    have e : b⁻¹ * a = s' * s⁻¹ := by
      have h1 : a * s = b * s' := hbs.symm
      calc b⁻¹ * a = b⁻¹ * (a * s) * s⁻¹ := by group
        _ = b⁻¹ * (b * s') * s⁻¹ := by rw [h1]
        _ = s' * s⁻¹ := by group
    rw [e]; exact mul_mem hs' (inv_mem hs)
  have hbaM : b⁻¹ * a ∈ M := mul_mem (inv_mem (hB hb)) (hA ha)
  have h1 : b⁻¹ * a = 1 := by
    have : b⁻¹ * a ∈ M ⊓ Xs := ⟨hbaM, hba⟩
    rw [hM] at this; exact Subgroup.mem_bot.mp this
  have hab : a = b := by
    have := congrArg (b * ·) h1
    simpa using this
  have ha1 : a = 1 := by
    have : a ∈ A ⊓ B := ⟨ha, hab ▸ hb⟩
    rw [hAB] at this; exact Subgroup.mem_bot.mp this
  rw [ha1, one_mul]; exact hs

end J4

section J6

variable {G : Type} [Group G]

theorem cjL_zpowers (g a : G) : cjL g (zpowers a) = zpowers (g * a * g⁻¹) := by
  exact MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom a

theorem act_line {R Xs : Subgroup G} [Fact (QData R Xs)] {A : Subgroup G} (hA : A ≤ R) {a : G}
    (haA : A = zpowers a) (g : ↥(normalizer (R : Set G) ⊓ normalizer (Xs : Set G))) {k : ℕ}
    (hk : (g : G) * a * (g : G)⁻¹ = a ^ k) :
    ∀ v ∈ QV.sub (X := Xs) A hA, QV.actHom g v = (k : ZMod 5) • v := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := (QV.mem_sub hA).1 hv
  rw [haA] at hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hgy : (g : G) * a ^ n * (g : G)⁻¹ = (a ^ n) ^ k := by
    rw [← conj_zpow, hk, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hyR : a ^ n ∈ R := hA (haA ▸ Subgroup.zpow_mem_zpowers a n)
  rw [QV.actHom_mk g hyR (R.pow_mem hyR k) hgy.symm, QV.mk_pow hyR k,
    Nat.cast_smul_eq_nsmul (ZMod 5)]

end J6

section J7

variable {G : Type} [Group G] {R Xs : Subgroup G} [Fact (QData R Xs)]

theorem act_fix {A : Subgroup G} (hA : A ≤ R)
    (g : ↥(normalizer (R : Set G) ⊓ normalizer (Xs : Set G)))
    (hg : ∀ y ∈ A, (g : G) * y * (g : G)⁻¹ = y) :
    ∀ v ∈ QV.sub (X := Xs) A hA, QV.actHom g v = v := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := (QV.mem_sub hA).1 hv
  rw [QV.actHom_mk g (hA hy) (hA hy) (hg y hy).symm]

theorem act_neg {A : Subgroup G} (hA : A ≤ R)
    (g : ↥(normalizer (R : Set G) ⊓ normalizer (Xs : Set G)))
    (hg : ∀ y ∈ A, (g : G) * y * (g : G)⁻¹ = y⁻¹) :
    ∀ v ∈ QV.sub (X := Xs) A hA, QV.actHom g v = -v := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := (QV.mem_sub hA).1 hv
  rw [QV.actHom_mk g (hA hy) (hA (A.inv_mem hy)) (hg y hy).symm, QV.mk_inv (hA hy)]

theorem act_neg_all (g : ↥(normalizer (R : Set G) ⊓ normalizer (Xs : Set G)))
    (hg : ∀ r ∈ R, (g : G) * r * (g : G)⁻¹ * r ∈ Xs) (v : QV R Xs) : QV.actHom g v = -v := by
  obtain ⟨r, hr, rfl⟩ := QV.mk_surjective v
  have h1 := QV.conj_mem g hr
  have h2 : (QV.mk (X := Xs) ((g : G) * r * (g : G)⁻¹ * r) (R.mul_mem h1 hr)) = 0 :=
    (QV.mk_eq_zero_iff _).2 (hg r hr)
  rw [QV.mk_add h1 hr] at h2
  rw [QV.actHom_mk' g hr]
  exact eq_neg_of_add_eq_zero_left h2

theorem mem_closure_subtype {N : Subgroup G} {x y z : G} (hx : x ∈ N) (hy : y ∈ N) (hz : z ∈ N)
    (h : z ∈ Subgroup.closure ({x, y} : Set G)) :
    (⟨z, hz⟩ : ↥N) ∈ Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥N) := by
  have hmap : (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥N)).map N.subtype =
      Subgroup.closure ({x, y} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext w
    simp
  rw [← hmap] at h
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp h
  have : c = ⟨z, hz⟩ := Subtype.ext hcz
  rwa [← this]

end J7

section J8
variable {V : Type} [AddCommGroup V] [Module (ZMod 5) V]
theorem le_coe_pow (x : V ≃ₗ[ZMod 5] V) (n : ℕ) (v : V) :
    (x ^ n : V ≃ₗ[ZMod 5] V) v = ((x : V →ₗ[ZMod 5] V) ^ n) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', LinearEquiv.mul_apply, Module.End.mul_apply, ih]
    rfl
theorem pow_five_apply (x : V ≃ₗ[ZMod 5] V) (h : x ^ 5 = 1) (v : V) :
    x (x (x (x (x v)))) = v := by
  have := congrArg (fun f : V ≃ₗ[ZMod 5] V => f v) h
  simpa [pow_succ, LinearEquiv.mul_apply] using this

end J8

section J9
theorem kw_pow_apply {V : Type} [AddCommGroup V] [Module (ZMod 5) V]
    (x : V ≃ₗ[ZMod 5] V) (hphi : ∀ v, x (x v) - 2 • x v + v = 0) (n : ℕ) (v : V) :
    ((x : V →ₗ[ZMod 5] V) ^ n) v = v + n • (x v - v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    show x (v + n • (x v - v)) = _
    have h1 : x (x v) = 2 • x v - v := by
      have := hphi v
      rw [sub_add_eq_add_sub, sub_eq_zero] at this
      rw [eq_sub_iff_add_eq]; exact this
    rw [map_add, map_nsmul, map_sub, h1, succ_nsmul (x v - v) n]
    have : 2 • x v - v - x v = x v - v := by
      rw [two_nsmul]; abel
    rw [this]
    abel

theorem K_weight_linear {V : Type} [AddCommGroup V] [Module (ZMod 5) V] [Finite V]
    (x u w h : V ≃ₗ[ZMod 5] V)
    (L3 L4 L5 L6 : Submodule (ZMod 5) V)
    (hc : IsCompl (L3 ⊔ L4) (L5 ⊔ L6))
    (h34 : Disjoint L3 L4) (h56 : Disjoint L5 L6)
    (d3 : Module.finrank (ZMod 5) L3 = 1) (d4 : Module.finrank (ZMod 5) L4 = 1)
    (d5 : Module.finrank (ZMod 5) L5 = 1) (d6 : Module.finrank (ZMod 5) L6 = 1)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v)
    (hx5 : ∀ v, x (x (x (x (x v)))) = v)
    (huF : ∀ v ∈ L3 ⊔ L4, u v = -v) (huF' : ∀ v ∈ L5 ⊔ L6, u v = v)
    (hux : ∀ v, u (x v) = x.symm (u v))
    (hww : ∀ v, w (w v) = -v)
    (hw3 : L3.map (w : V →ₗ[ZMod 5] V) = L5) (hw4 : L4.map (w : V →ₗ[ZMod 5] V) = L6)
    (hgen : w ∈ Subgroup.closure ({x, w * x * w⁻¹} : Set (V ≃ₗ[ZMod 5] V)))
    (k : ℕ) (a3 a4 a5 a6 : ZMod 5)
    (hh3 : ∀ v ∈ L3, h v = a3 • v) (hh4 : ∀ v ∈ L4, h v = a4 • v)
    (hh5 : ∀ v ∈ L5, h v = a5 • v) (hh6 : ∀ v ∈ L6, h v = a6 • v) (h34' : a3 ≠ a4)
    (hhx : ∀ v, h (x v) = ((x : V →ₗ[ZMod 5] V) ^ k) (h v))
    (h' : V ≃ₗ[ZMod 5] V) (k' : ℕ) (b3 b5 : ZMod 5)
    (hh3' : ∀ v ∈ L3, h' v = b3 • v) (hh5' : ∀ v ∈ L5, h' v = b5 • v)
    (hhx' : ∀ v, h' (x v) = ((x : V →ₗ[ZMod 5] V) ^ k') (h' v)) :
    b3 = (k' : ZMod 5) * b5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hphi, h3, -, hinj⟩ := K_linear x u w h L3 L4 L5 L6 hc h34 h56 d3 d4 d5 d6 hxF hx5 huF huF'
    hux hww hw3 hw4 hgen k a3 a4 a5 a6 hh3 hh4 hh5 hh6 h34' hhx
  have hne : L5 ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at d5
    exact absurd d5 (by norm_num)
  obtain ⟨m, hm5, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hmx : x m - m ≠ 0 := by
    intro h0
    exact hm0 (hinj m (Submodule.mem_sup_left hm5) (sub_eq_zero.mp h0))
  have hmem : x m - m ∈ L3 := h3 m hm5
  have e1 : h' (x m - m) = b3 • (x m - m) := hh3' _ hmem
  have e2 : h' (x m - m) = ((k' : ZMod 5) * b5) • (x m - m) := by
    rw [map_sub, hhx', hh5' m hm5, map_smul, kw_pow_apply x hphi k' m, smul_add,
      add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul (ZMod 5), ← mul_smul, mul_comm]
  have e3 : (b3 - (k' : ZMod 5) * b5) • (x m - m) = 0 := by
    rw [sub_smul, ← e1, ← e2, sub_self]
  rcases smul_eq_zero.mp e3 with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hmx

end J9

section J10

variable {G : Type} [Group G]

theorem orderOf_conj_eq {a g : G} (ha : orderOf a = 5) : orderOf (g * a * g⁻¹) = 5 := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  simpa [MulAut.conj_apply, ha] using this

theorem exists_exp_conj {a g : G} {H : Subgroup G} (hg : cjL g H = H)
    (hexp : ∀ h ∈ H, ∃ k : ℕ, h * a * h⁻¹ = a ^ k) :
    ∀ h ∈ H, ∃ k : ℕ, h * (g * a * g⁻¹) * h⁻¹ = (g * a * g⁻¹) ^ k := by
  intro h hh
  have hmem : g⁻¹ * h * g ∈ H := by
    have : h ∈ cjL g H := by rw [hg]; exact hh
    exact mem_cjL.mp this
  obtain ⟨k, hk⟩ := hexp _ hmem
  refine ⟨k, ?_⟩
  have e1 : h * (g * a * g⁻¹) * h⁻¹ = g * ((g⁻¹ * h * g) * a * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by group
  rw [e1, hk, conj_pow]

theorem wt_conj_H {a g h : G} {H : Subgroup G} (ha : orderOf a = 5) (hg : cjL g H = H)
    (hexp : ∀ h ∈ H, ∃ k : ℕ, h * a * h⁻¹ = a ^ k) (hh : h ∈ H) :
    wt (g * a * g⁻¹) h = wt a (g⁻¹ * h * g) := by
  have hmem : g⁻¹ * h * g ∈ H := by
    have : h ∈ cjL g H := by rw [hg]; exact hh
    exact mem_cjL.mp this
  obtain ⟨k, hk⟩ := hexp _ hmem
  exact wt_conj ha hk

end J10

section J4b

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg3.qData0 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    QData0 (RR t X₁) (XB t X₁) := ⟨c.X2_le_RR, c.z_inv_R.2, c.X2_central⟩

theorem Cfg3.qData (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    QData (RR t X₁) (XB t X₁) :=
  { c.qData0 with
    five := QData.five_of_gen c.qData0 c.Y_le_RR c.Yw_le_RR c.R_eq
      (fun a ha => by
        rw [c.b83.Y_ab.2 a ha]; exact Subgroup.one_mem _)
      (fun b hb => by
        rw [c.Yw_ab.1.2 b hb]; exact Subgroup.one_mem _) }

theorem Cfg3.X3_le_Y' (_c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) (hvX : cjL v (XX t X₁) = Y) :
    X3 v X₁ ≤ Y := by
  have := cjL_mono v (le_sup_left : X₁ ≤ XX t X₁)
  rwa [hvX] at this

theorem Cfg3.X4_le_Y' (_c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) (hvX : cjL v (XX t X₁) = Y) :
    X4 v t X₁ ≤ Y := by
  have := cjL_mono v (le_sup_right : XB t X₁ ≤ XX t X₁)
  rwa [hvX] at this

theorem Cfg3.X34_eq (_c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) (hvX : cjL v (XX t X₁) = Y) :
    X3 v X₁ ⊔ X4 v t X₁ = Y := by
  show cjL v X₁ ⊔ cjL v (XB t X₁) = Y
  rw [← cjL_sup]; exact hvX

theorem Cfg3.X56_eq (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) (hvX : cjL v (XX t X₁) = Y) :
    X5 v w₁ X₁ ⊔ X6 v t w₁ X₁ = cjL w₁ Y := by
  show cjL w₁ (X3 v X₁) ⊔ cjL w₁ (X4 v t X₁) = cjL w₁ Y
  rw [← cjL_sup, c.X34_eq hvX]

theorem Cfg3.Yw_inf_XY (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    cjL w₁ Y ⊓ (XB t X₁ ⊔ Y) = ⊥ := by
  rw [eq_bot_iff, ← c.XY_inf_Cu]
  intro w ⟨hw1, hw2⟩
  refine ⟨hw2, ?_⟩
  have : w ∈ centralizer ({u} : Set G) ⊓ RR t X₁ := by rw [← c.Yw_eq]; exact hw1
  exact this.1

theorem Cfg3.Y_inf_X2 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Y ⊓ XB t X₁ = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hy, hx⟩
  have h1 : x ∈ XX t X₁ ⊓ Y := ⟨(le_sup_right : XB t X₁ ≤ XX t X₁) hx, hy⟩
  rw [c.b83.XY_disj] at h1
  exact h1

theorem Cfg3.Yw_inf_X2 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : cjL w₁ Y ⊓ XB t X₁ = ⊥ := by
  rw [eq_bot_iff, ← c.Yw_inf_XY]
  exact inf_le_inf_left _ le_sup_left

theorem Cfg3.X3_inf_X4 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    X3 v X₁ ⊓ X4 v t X₁ = ⊥ := by
  show cjL v X₁ ⊓ cjL v (XB t X₁) = ⊥
  rw [← cjL_inf, c.X1_inf_X2]; exact Subgroup.map_bot _

theorem Cfg3.X5_inf_X6 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    X5 v w₁ X₁ ⊓ X6 v t w₁ X₁ = ⊥ := by
  show cjL w₁ (X3 v X₁) ⊓ cjL w₁ (X4 v t X₁) = ⊥
  rw [← cjL_inf, c.X3_inf_X4]; exact Subgroup.map_bot _

theorem Cfg3.card_X3' (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(X3 v X₁) = 5 :=
  (card_cjL v X₁).trans c.card_X1
theorem Cfg3.card_X4' (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(X4 v t X₁) = 5 :=
  (card_cjL v _).trans c.card_X2
theorem Cfg3.card_X5' (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    Nat.card ↥(X5 v w₁ X₁) = 5 := (card_cjL w₁ _).trans (c.card_X3' (v := v))
theorem Cfg3.card_X6' (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    Nat.card ↥(X6 v t w₁ X₁) = 5 := (card_cjL w₁ _).trans (c.card_X4' (v := v))

theorem Cfg3.K_rel (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {v : G} (hv : v ∈ NN z u)
    (hvX : cjL v (XX t X₁) = Y) {a : G} (ha : a ∈ X₁) (ha1 : a ≠ 1) :
    ∀ h ∈ H, wt (v * a * v⁻¹) h = wt a h * wt (w₁ * (v * a * v⁻¹) * w₁⁻¹) h := by
  intro h hh
  have hQ : Fact (QData (RR t X₁) (XB t X₁)) := ⟨c.qData⟩
  have hA3R : X3 v X₁ ≤ RR t X₁ := (c.X3_le_Y' hvX).trans c.Y_le_RR
  have hA4R : X4 v t X₁ ≤ RR t X₁ := (c.X4_le_Y' hvX).trans c.Y_le_RR
  have hYR : Y ≤ RR t X₁ := c.Y_le_RR
  have hY'R : cjL w₁ Y ≤ RR t X₁ := c.Yw_le_RR
  have hA5R : X5 v w₁ X₁ ≤ RR t X₁ := (cjL_mono w₁ (c.X3_le_Y' hvX)).trans hY'R
  have hA6R : X6 v t w₁ X₁ ≤ RR t X₁ := (cjL_mono w₁ (c.X4_le_Y' hvX)).trans hY'R
  have hcen : ∀ r ∈ RR t X₁, ∀ s ∈ XB t X₁, r * s = s * r := c.X2_central
  have hF : QV.sub (X := XB t X₁) (X3 v X₁) hA3R ⊔ QV.sub (X := XB t X₁) (X4 v t X₁) hA4R =
      QV.sub (X := XB t X₁) Y hYR := by
    rw [← QV.sub_sup hA3R hA4R (sup_le hA3R hA4R)]
    exact QV.sub_congr (c.X34_eq hvX) _ _
  have hF' : QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R ⊔ QV.sub (X := XB t X₁) (X6 v t w₁ X₁) hA6R =
      QV.sub (X := XB t X₁) (cjL w₁ Y) hY'R := by
    rw [← QV.sub_sup hA5R hA6R (sup_le hA5R hA6R)]
    exact QV.sub_congr (c.X56_eq hvX) _ _
  have hd34 : Disjoint (QV.sub (X := XB t X₁) (X3 v X₁) hA3R) (QV.sub (X := XB t X₁) (X4 v t X₁) hA4R) :=
    QV.sub_disjoint hA3R hA4R (sup_inf_sup_le (c.X3_le_Y' hvX) (c.X4_le_Y' hvX) c.Y_inf_X2
      c.X3_inf_X4 (fun a ha s hs => hcen a (hA3R ha) s hs) (fun b hb s hs => hcen b (hA4R hb) s hs))
  have hd56 : Disjoint (QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R) (QV.sub (X := XB t X₁) (X6 v t w₁ X₁) hA6R) :=
    QV.sub_disjoint hA5R hA6R (sup_inf_sup_le (cjL_mono w₁ (c.X3_le_Y' hvX)) (cjL_mono w₁ (c.X4_le_Y' hvX))
      c.Yw_inf_X2 c.X5_inf_X6 (fun a ha s hs => hcen a (hA5R ha) s hs) (fun b hb s hs => hcen b (hA6R hb) s hs))
  have hdFF : Disjoint (QV.sub (X := XB t X₁) Y hYR) (QV.sub (X := XB t X₁) (cjL w₁ Y) hY'R) := by
    apply QV.sub_disjoint hYR hY'R
    intro x ⟨hx1, hx2⟩
    obtain ⟨y, hy, s, hs, rfl⟩ :=
      (mem_sup_of_commute (fun y hy s hs => hcen y (hYR hy) s hs)).1 hx1
    obtain ⟨y', hy', s', hs', hyy⟩ :=
      (mem_sup_of_commute (fun y hy s hs => hcen y (hY'R hy) s hs)).1 hx2
    have hmem : y' ∈ XB t X₁ ⊔ Y := by
      have e : y' = y * (s * s'⁻¹) := by
        calc y' = (y' * s') * s'⁻¹ := by group
          _ = (y * s) * s'⁻¹ := by rw [hyy]
          _ = y * (s * s'⁻¹) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_right hy)
        (Subgroup.mem_sup_left (mul_mem hs (inv_mem hs')))
    have h1 : y' ∈ cjL w₁ Y ⊓ (XB t X₁ ⊔ Y) := ⟨hy', hmem⟩
    rw [c.Yw_inf_XY] at h1
    have h2 : y' = 1 := Subgroup.mem_bot.mp h1
    rw [← hyy, h2, one_mul]; exact hs'
  have hTop : QV.sub (X := XB t X₁) Y hYR ⊔ QV.sub (X := XB t X₁) (cjL w₁ Y) hY'R = ⊤ := by
    have h1 : QV.sub (X := XB t X₁) (RR t X₁) le_rfl = ⊤ := QV.sub_top
    have h2 : QV.sub (X := XB t X₁) (RR t X₁) le_rfl =
        QV.sub (X := XB t X₁) (XB t X₁ ⊔ Y ⊔ cjL w₁ Y) c.D5_le_RR := QV.sub_congr c.R_eq _ _
    rw [h2, QV.sub_sup (sup_le c.X2_le_RR hYR) hY'R c.D5_le_RR,
      QV.sub_sup c.X2_le_RR hYR (sup_le c.X2_le_RR hYR),
      QV.sub_eq_bot_of_le c.X2_le_RR le_rfl, bot_sup_eq] at h1
    exact h1
  have hc : IsCompl (QV.sub (X := XB t X₁) (X3 v X₁) hA3R ⊔ QV.sub (X := XB t X₁) (X4 v t X₁) hA4R)
      (QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R ⊔ QV.sub (X := XB t X₁) (X6 v t w₁ X₁) hA6R) := by
    rw [hF, hF']
    exact ⟨hdFF, codisjoint_iff.mpr hTop⟩
  have hX3X2 : X3 v X₁ ⊓ XB t X₁ = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_right _ (c.X3_le_Y' hvX)) c.Y_inf_X2.le)
  have hX4X2 : X4 v t X₁ ⊓ XB t X₁ = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_right _ (c.X4_le_Y' hvX)) c.Y_inf_X2.le)
  have hX5X2 : X5 v w₁ X₁ ⊓ XB t X₁ = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_right _ (cjL_mono w₁ (c.X3_le_Y' hvX))) c.Yw_inf_X2.le)
  have hX6X2 : X6 v t w₁ X₁ ⊓ XB t X₁ = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_right _ (cjL_mono w₁ (c.X4_le_Y' hvX))) c.Yw_inf_X2.le)
  have d3 := QV.finrank_sub (X := XB t X₁) hA3R hX3X2 c.card_X3'
  have d4 := QV.finrank_sub (X := XB t X₁) hA4R hX4X2 c.card_X4'
  have d5 := QV.finrank_sub (X := XB t X₁) hA5R hX5X2 c.card_X5'
  have d6 := QV.finrank_sub (X := XB t X₁) hA6R hX6X2 c.card_X6'
  have hmemK : ∀ g ∈ K₁, g ∈ normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G) :=
    fun g hg => ⟨c.K1_le_normalizer_RR hg, c.K1_le_normalizer_X2 hg⟩
  have hmemH : ∀ g ∈ H, g ∈ normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G) :=
    fun g hg => ⟨normalizer_le_normalizer_RR t X₁ (c.H_le_normalizer_X2 hg),
      c.H_le_normalizer_X2 hg⟩
  have haK : a ∈ K₁ := c.b82.X₁_syl.1 ha
  have hvH : cjL v H = H := c.cjL_H hv
  have hwH : cjL w₁ H = H := c.cjL_H c.w₁_NN
  have htH : cjL t H = H := c.b66.t_normH
  have ha5 : orderOf a = 5 := orderOf_eq_five_of_card c.card_X1 ha ha1
  have hexp : ∀ g ∈ H, ∃ k : ℕ, g * a * g⁻¹ = a ^ k :=
    fun g hg => exists_exp_of_hinv c.card_X1 ha ha1 c.hinv_X1 hg
  have hX1 : X₁ = zpowers a := eq_zpowers_of_card_five c.card_X1 ha ha1
  have hXB : XB t X₁ = zpowers (t * a * t⁻¹) := by
    show cjL t X₁ = _
    rw [hX1, cjL_zpowers]
  have hX3 : X3 v X₁ = zpowers (v * a * v⁻¹) := by
    show cjL v X₁ = _
    rw [hX1, cjL_zpowers]
  have hX4 : X4 v t X₁ = zpowers (v * (t * a * t⁻¹) * v⁻¹) := by
    show cjL v (XB t X₁) = _
    rw [hXB, cjL_zpowers]
  have hX5 : X5 v w₁ X₁ = zpowers (w₁ * (v * a * v⁻¹) * w₁⁻¹) := by
    show cjL w₁ (X3 v X₁) = _
    rw [hX3, cjL_zpowers]
  have hX6 : X6 v t w₁ X₁ = zpowers (w₁ * (v * (t * a * t⁻¹) * v⁻¹) * w₁⁻¹) := by
    show cjL w₁ (X4 v t X₁) = _
    rw [hX4, cjL_zpowers]
  have ha2 : orderOf (t * a * t⁻¹) = 5 := orderOf_conj_eq ha5
  have ha3 : orderOf (v * a * v⁻¹) = 5 := orderOf_conj_eq ha5
  have hexp2 := exists_exp_conj htH hexp
  have hexp3 := exists_exp_conj hvH hexp
  have hexp4 := exists_exp_conj hvH hexp2
  have hexp5 := exists_exp_conj hwH hexp3
  have hexp6 := exists_exp_conj hwH hexp4
  obtain ⟨h1, hh1, hne⟩ := c.exists_wt_ne ha ha1
  have hh0 : v * h1 * v⁻¹ ∈ H := by
    have := mem_cjL_self (g := v) hh1
    rwa [hvH] at this
  obtain ⟨kx, hkx⟩ := hexp _ hh0
  obtain ⟨k3, hk3⟩ := hexp3 _ hh0
  obtain ⟨k4, hk4⟩ := hexp4 _ hh0
  obtain ⟨k5, hk5⟩ := hexp5 _ hh0
  obtain ⟨k6, hk6⟩ := hexp6 _ hh0
  have hscal3 : (k3 : ZMod 5) = wt a h1 := by
    rw [← wt_eq ha3 hk3, wt_conj_H ha5 hvH hexp hh0]
    congr 1; group
  have hscal4 : (k4 : ZMod 5) = wt (t * a * t⁻¹) h1 := by
    rw [← wt_eq (orderOf_conj_eq ha2) hk4, wt_conj_H ha2 hvH hexp2 hh0]
    congr 1; group
  have h34' : (k3 : ZMod 5) ≠ (k4 : ZMod 5) := by
    rw [hscal3, hscal4]; exact hne
  obtain ⟨nx, hnx⟩ : ∃ n : ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G)),
      (n : G) = a := ⟨⟨a, hmemK a haK⟩, rfl⟩
  obtain ⟨nu, hnu⟩ : ∃ n : ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G)),
      (n : G) = u := ⟨⟨u, hmemH u c.b66.u_mem⟩, rfl⟩
  obtain ⟨nw, hnw⟩ : ∃ n : ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G)),
      (n : G) = w₁ := ⟨⟨w₁, hmemK w₁ c.b66.w₁_mem⟩, rfl⟩
  obtain ⟨nz, hnz⟩ : ∃ n : ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G)),
      (n : G) = z := ⟨⟨z, hmemH z c.b66.z_mem⟩, rfl⟩
  obtain ⟨nh0, hnh0⟩ : ∃ n : ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G)),
      (n : G) = v * h1 * v⁻¹ := ⟨⟨_, hmemH _ hh0⟩, rfl⟩
  obtain ⟨nh, hnh⟩ : ∃ n : ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G)),
      (n : G) = h := ⟨⟨h, hmemH h hh⟩, rfl⟩
  have ha5' : a ^ 5 = 1 := by simpa [ha5] using pow_orderOf_eq_one a
  have hxF : ∀ vv ∈ QV.sub (X := XB t X₁) (X3 v X₁) hA3R ⊔ QV.sub (X := XB t X₁) (X4 v t X₁) hA4R,
      QV.actHom nx vv = vv := by
    intro vv hvv
    rw [hF] at hvv
    refine act_fix hYR nx (fun y hy => ?_) vv hvv
    rw [hnx]
    exact mul_inv_eq_iff_eq_mul.2 (c.XX_comm a (Subgroup.mem_sup_left ha) y hy)
  have hx5 : ∀ vv, QV.actHom nx (QV.actHom nx (QV.actHom nx (QV.actHom nx (QV.actHom nx vv)))) = vv := by
    apply pow_five_apply
    have : nx ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hnx, Subgroup.coe_one]; exact ha5')
    rw [← map_pow, this, map_one]
  have huF : ∀ vv ∈ QV.sub (X := XB t X₁) (X3 v X₁) hA3R ⊔ QV.sub (X := XB t X₁) (X4 v t X₁) hA4R,
      QV.actHom nu vv = -vv := by
    intro vv hvv
    rw [hF] at hvv
    refine act_neg hYR nu (fun y hy => ?_) vv hvv
    rw [hnu]
    exact c.b83.u_inv y (Subgroup.mem_sup_right hy)
  have huF' : ∀ vv ∈ QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R ⊔ QV.sub (X := XB t X₁) (X6 v t w₁ X₁) hA6R,
      QV.actHom nu vv = vv := by
    intro vv hvv
    rw [hF'] at hvv
    refine act_fix hY'R nu (fun y hy => ?_) vv hvv
    rw [hnu]
    exact c.u_cent_Yw y hy
  have hux : ∀ vv, QV.actHom nu (QV.actHom nx vv) = (QV.actHom nx).symm (QV.actHom nu vv) := by
    have hrel : nu * nx = nx⁻¹ * nu := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnu, hnx]
      exact mul_inv_eq_iff_eq_mul.1 (c.b83.u_inv a (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)))
    have hrel' : QV.actHom nu * QV.actHom nx = (QV.actHom nx)⁻¹ * QV.actHom nu := by
      rw [← map_mul, ← map_inv, ← map_mul, hrel]
    intro vv
    have := congrArg (fun f : QV (RR t X₁) (XB t X₁) ≃ₗ[ZMod 5] QV (RR t X₁) (XB t X₁) => f vv) hrel'
    simpa [LinearEquiv.mul_apply] using this
  have hww : ∀ vv, QV.actHom nw (QV.actHom nw vv) = -vv := by
    have hrel : nw * nw = nz := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hnw, hnz]
      rw [← pow_two]; exact c.b66.w₁_sq
    intro vv
    have h1 : QV.actHom nw (QV.actHom nw vv) = QV.actHom nz vv := by
      rw [← LinearEquiv.mul_apply, ← map_mul, hrel]
    rw [h1]
    exact act_neg_all nz (fun r hr => by rw [hnz]; exact c.z_inv_R.1 r hr) vv
  have hw3 : (QV.sub (X := XB t X₁) (X3 v X₁) hA3R).map
      (QV.actHom nw : QV (RR t X₁) (XB t X₁) →ₗ[ZMod 5] QV (RR t X₁) (XB t X₁)) =
      QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R := by
    have h1 := QV.sub_map_act nw hA3R (by rw [hnw]; exact hA5R)
    exact h1.trans (QV.sub_congr (by rw [hnw]) _ _)
  have hw4 : (QV.sub (X := XB t X₁) (X4 v t X₁) hA4R).map
      (QV.actHom nw : QV (RR t X₁) (XB t X₁) →ₗ[ZMod 5] QV (RR t X₁) (XB t X₁)) =
      QV.sub (X := XB t X₁) (X6 v t w₁ X₁) hA6R := by
    have h1 := QV.sub_map_act nw hA4R (by rw [hnw]; exact hA6R)
    exact h1.trans (QV.sub_congr (by rw [hnw]) _ _)
  have hgen : QV.actHom nw ∈ Subgroup.closure
      ({QV.actHom nx, QV.actHom nw * QV.actHom nx * (QV.actHom nw)⁻¹} :
        Set (QV (RR t X₁) (XB t X₁) ≃ₗ[ZMod 5] QV (RR t X₁) (XB t X₁))) := by
    have hyK : w₁ * a * w₁⁻¹ ∈ K₁ :=
      mul_mem (mul_mem c.b66.w₁_mem haK) (inv_mem c.b66.w₁_mem)
    have hcl := mem_closure_subtype (hmemK a haK) (hmemK _ hyK) (hmemK w₁ c.b66.w₁_mem)
      (c.w1_mem_closure ha ha1)
    have hnw' : nw = ⟨w₁, hmemK w₁ c.b66.w₁_mem⟩ := Subtype.ext hnw
    have hnx' : nx = ⟨a, hmemK a haK⟩ := Subtype.ext hnx
    have hny : (⟨w₁ * a * w₁⁻¹, hmemK _ hyK⟩ :
        ↥(normalizer (RR t X₁ : Set G) ⊓ normalizer (XB t X₁ : Set G))) = nw * nx * nw⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnw, hnx]
    have h2 := Subgroup.mem_map_of_mem (QV.actHom (R := RR t X₁) (X := XB t X₁)) hcl
    rw [MonoidHom.map_closure, Set.image_pair, ← hnw', ← hnx', hny, map_mul, map_mul, map_inv] at h2
    exact h2
  have hh3 : ∀ vv ∈ QV.sub (X := XB t X₁) (X3 v X₁) hA3R,
      QV.actHom nh0 vv = (k3 : ZMod 5) • vv :=
    act_line hA3R hX3 nh0 (by rw [hnh0]; exact hk3)
  have hh4 : ∀ vv ∈ QV.sub (X := XB t X₁) (X4 v t X₁) hA4R,
      QV.actHom nh0 vv = (k4 : ZMod 5) • vv :=
    act_line hA4R hX4 nh0 (by rw [hnh0]; exact hk4)
  have hh5 : ∀ vv ∈ QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R,
      QV.actHom nh0 vv = (k5 : ZMod 5) • vv :=
    act_line hA5R hX5 nh0 (by rw [hnh0]; exact hk5)
  have hh6 : ∀ vv ∈ QV.sub (X := XB t X₁) (X6 v t w₁ X₁) hA6R,
      QV.actHom nh0 vv = (k6 : ZMod 5) • vv :=
    act_line hA6R hX6 nh0 (by rw [hnh0]; exact hk6)
  have hhx : ∀ vv, QV.actHom nh0 (QV.actHom nx vv) =
      ((QV.actHom nx : QV (RR t X₁) (XB t X₁) →ₗ[ZMod 5] QV (RR t X₁) (XB t X₁)) ^ kx)
        (QV.actHom nh0 vv) := by
    have hrel : nh0 * nx = nx ^ kx * nh0 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, hnh0, hnx]
      exact mul_inv_eq_iff_eq_mul.1 hkx
    have hrel' : QV.actHom nh0 * QV.actHom nx = QV.actHom nx ^ kx * QV.actHom nh0 := by
      rw [← map_mul, ← map_pow, ← map_mul, hrel]
    intro vv
    have := congrArg (fun f : QV (RR t X₁) (XB t X₁) ≃ₗ[ZMod 5] QV (RR t X₁) (XB t X₁) => f vv) hrel'
    simp only [LinearEquiv.mul_apply] at this
    rw [this, le_coe_pow]
  obtain ⟨kh, hkh⟩ := hexp h hh
  obtain ⟨kh3, hkh3⟩ := hexp3 h hh
  obtain ⟨kh5, hkh5⟩ := hexp5 h hh
  have hh3' : ∀ vv ∈ QV.sub (X := XB t X₁) (X3 v X₁) hA3R,
      QV.actHom nh vv = (kh3 : ZMod 5) • vv :=
    act_line hA3R hX3 nh (by rw [hnh]; exact hkh3)
  have hh5' : ∀ vv ∈ QV.sub (X := XB t X₁) (X5 v w₁ X₁) hA5R,
      QV.actHom nh vv = (kh5 : ZMod 5) • vv :=
    act_line hA5R hX5 nh (by rw [hnh]; exact hkh5)
  have hhx' : ∀ vv, QV.actHom nh (QV.actHom nx vv) =
      ((QV.actHom nx : QV (RR t X₁) (XB t X₁) →ₗ[ZMod 5] QV (RR t X₁) (XB t X₁)) ^ kh)
        (QV.actHom nh vv) := by
    have hrel : nh * nx = nx ^ kh * nh := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, hnh, hnx]
      exact mul_inv_eq_iff_eq_mul.1 hkh
    have hrel' : QV.actHom nh * QV.actHom nx = QV.actHom nx ^ kh * QV.actHom nh := by
      rw [← map_mul, ← map_pow, ← map_mul, hrel]
    intro vv
    have := congrArg (fun f : QV (RR t X₁) (XB t X₁) ≃ₗ[ZMod 5] QV (RR t X₁) (XB t X₁) => f vv) hrel'
    simp only [LinearEquiv.mul_apply] at this
    rw [this, le_coe_pow]
  have key := K_weight_linear (QV.actHom nx) (QV.actHom nu) (QV.actHom nw) (QV.actHom nh0)
    _ _ _ _ hc hd34 hd56 d3 d4 d5 d6 hxF hx5 huF huF' hux hww hw3 hw4 hgen kx
    (k3 : ZMod 5) (k4 : ZMod 5) (k5 : ZMod 5) (k6 : ZMod 5) hh3 hh4 hh5 hh6 h34' hhx
    (QV.actHom nh) kh (kh3 : ZMod 5) (kh5 : ZMod 5) hh3' hh5' hhx'
  rw [wt_eq ha3 hkh3, wt_eq ha5 hkh, wt_eq (orderOf_conj_eq ha3) hkh5]
  exact key

end J4b

end CFSG.GH74.GLS.LU.Local.Five
