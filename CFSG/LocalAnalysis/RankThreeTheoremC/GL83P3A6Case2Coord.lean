module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Mod
public import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod

open Subgroup

section Frame

variable {H : Type} [Group H]

structure Frame3 (x e₂ e₃ t ρ : H) (s : ℤ) : Prop where
  x3 : x ^ 3 = 1
  e₂3 : e₂ ^ 3 = 1
  e₃3 : e₃ ^ 3 = 1
  c₂ : x * e₂ = e₂ * x
  c₃ : x * e₃ = e₃ * x
  c₂₃ : e₂ * e₃ = e₃ * e₂
  tx : t * x * t⁻¹ = e₂
  te₂ : t * e₂ * t⁻¹ = e₃
  te₃ : t * e₃ * t⁻¹ = x
  ρx : ρ * x * ρ⁻¹ = x
  ρe₂ : ρ * e₂ * ρ⁻¹ = e₃ ^ s
  ρe₃ : ρ * e₃ * ρ⁻¹ = e₂ ^ (-s)
  s_cases : s = 1 ∨ s = -1

def gp (g : H) (a : ZMod 3) : H := g ^ a.val

theorem pow_mod3 {g : H} (hg : g ^ 3 = 1) (m : ℕ) : g ^ m = g ^ (m % 3) := by
  calc g ^ m = g ^ (3 * (m / 3) + m % 3) := by rw [Nat.div_add_mod]
    _ = g ^ (m % 3) := by rw [pow_add, pow_mul, hg, one_pow, one_mul]

theorem gp_add {g : H} (hg : g ^ 3 = 1) (a b : ZMod 3) : gp g (a + b) = gp g a * gp g b := by
  unfold gp
  rw [ZMod.val_add, ← pow_add]
  exact (pow_mod3 hg _).symm

theorem gp_zero (g : H) : gp g 0 = 1 := by simp [gp]

theorem gp_one {g : H} (hg : g ^ 3 = 1) : gp g 1 = g := by
  unfold gp
  have : (1 : ZMod 3).val = 1 := rfl
  rw [this, pow_one]

theorem zpow_eq_gp {g : H} (hg : g ^ 3 = 1) (n : ℤ) : g ^ n = gp g (n : ZMod 3) := by
  unfold gp
  have h1 := zpow_eq_zpow_emod' n hg
  have h2 : (((n : ZMod 3).val : ℕ) : ℤ) = n % ((3 : ℕ) : ℤ) := ZMod.val_intCast n
  rw [h1, ← h2, zpow_natCast]

theorem conj_gp (c g : H) (a : ZMod 3) : c * gp g a * c⁻¹ = gp (c * g * c⁻¹) a := by
  unfold gp
  rw [conj_pow]

theorem gp_gp {g : H} (hg : g ^ 3 = 1) (a b : ZMod 3) : gp (gp g a) b = gp g (a * b) := by
  unfold gp
  rw [← pow_mul, ZMod.val_mul]
  exact pow_mod3 hg _

def qel (x e₂ e₃ : H) (v : Vec) : H := gp x v.1 * gp e₂ v.2.1 * gp e₃ v.2.2

theorem mul3 {A₁ B₁ C₁ A₂ B₂ C₂ : H} (hBA : Commute B₁ A₂) (hCA : Commute C₁ A₂)
    (hCB : Commute C₁ B₂) :
    A₁ * B₁ * C₁ * (A₂ * B₂ * C₂) = A₁ * A₂ * (B₁ * B₂) * (C₁ * C₂) := by
  rw [(hCA.mul_right hCB).mul_mul_mul_comm (A₁ * B₁) C₂, hBA.mul_mul_mul_comm A₁ B₂]

theorem conj_mul3 (c X Y Z : H) :
    c * (X * Y * Z) * c⁻¹ = (c * X * c⁻¹) * (c * Y * c⁻¹) * (c * Z * c⁻¹) := by group

namespace Frame3

variable {x e₂ e₃ t ρ : H} {s : ℤ} (h : Frame3 x e₂ e₃ t ρ s)

include h

theorem comm_xe₂ (a b : ZMod 3) : Commute (gp x a) (gp e₂ b) :=
  Commute.pow_pow (show Commute x e₂ from h.c₂) _ _

theorem comm_xe₃ (a b : ZMod 3) : Commute (gp x a) (gp e₃ b) :=
  Commute.pow_pow (show Commute x e₃ from h.c₃) _ _

theorem comm_e₂e₃ (a b : ZMod 3) : Commute (gp e₂ a) (gp e₃ b) :=
  Commute.pow_pow (show Commute e₂ e₃ from h.c₂₃) _ _

theorem qel_add (a b : Vec) : qel x e₂ e₃ (a + b) = qel x e₂ e₃ a * qel x e₂ e₃ b := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  obtain ⟨b₁, b₂, b₃⟩ := b
  simp only [qel, Prod.mk_add_mk, gp_add h.x3, gp_add h.e₂3, gp_add h.e₃3]
  exact (mul3 (h.comm_xe₂ _ _).symm (h.comm_xe₃ _ _).symm (h.comm_e₂e₃ _ _).symm).symm

theorem qel_zero : qel x e₂ e₃ 0 = 1 := by
  simp [qel, gp_zero]

theorem conj_t (a b c : ZMod 3) :
    t * qel x e₂ e₃ (a, b, c) * t⁻¹ = qel x e₂ e₃ (c, a, b) := by
  simp only [qel]
  rw [conj_mul3, conj_gp, conj_gp, conj_gp, h.tx, h.te₂, h.te₃]
  have hc : Commute (gp x c) (gp e₂ a * gp e₃ b) := (h.comm_xe₂ c a).mul_right (h.comm_xe₃ c b)
  rw [mul_assoc (gp x c)]
  exact hc.eq.symm

theorem sv_sq : (s : ZMod 3) * (s : ZMod 3) = 1 := by
  rcases h.s_cases with rfl | rfl <;> decide

theorem conj_ρ (a b c : ZMod 3) :
    ρ * qel x e₂ e₃ (a, b, c) * ρ⁻¹ =
      qel x e₂ e₃ (a, -((s : ZMod 3) * c), (s : ZMod 3) * b) := by
  simp only [qel]
  rw [conj_mul3, conj_gp, conj_gp, conj_gp, h.ρx, h.ρe₂, h.ρe₃, zpow_eq_gp h.e₃3 s,
    zpow_eq_gp h.e₂3 (-s), gp_gp h.e₃3, gp_gp h.e₂3]
  have e1 : (((-s : ℤ) : ZMod 3)) * c = -((s : ZMod 3) * c) := by
    rcases h.s_cases with rfl | rfl <;> revert c <;> decide
  rw [e1, mul_assoc, mul_assoc, (h.comm_e₂e₃ _ _).eq]

theorem conj_ρρ (a b c : ZMod 3) :
    ρ * (ρ * qel x e₂ e₃ (a, b, c) * ρ⁻¹) * ρ⁻¹ = qel x e₂ e₃ (a, -b, -c) := by
  rw [h.conj_ρ, h.conj_ρ]
  have e1 : -((s : ZMod 3) * ((s : ZMod 3) * b)) = -b := by
    rcases h.s_cases with rfl | rfl <;> revert b <;> decide
  have e2 : (s : ZMod 3) * -((s : ZMod 3) * c) = -c := by
    rcases h.s_cases with rfl | rfl <;> revert c <;> decide
  rw [e1, e2]

theorem conj_tinv (a b c : ZMod 3) :
    t⁻¹ * qel x e₂ e₃ (a, b, c) * t = qel x e₂ e₃ (b, c, a) := by
  have := h.conj_t b c a
  rw [← this]
  group

theorem conj_g1 (a b c : ZMod 3) :
    (ρ * ρ) * qel x e₂ e₃ (a, b, c) * (ρ * ρ)⁻¹ = qel x e₂ e₃ (a, -b, -c) := by
  rw [← h.conj_ρρ a b c]
  group

theorem conj_g2 (a b c : ZMod 3) :
    (t * (ρ * ρ) * t⁻¹) * qel x e₂ e₃ (a, b, c) * (t * (ρ * ρ) * t⁻¹)⁻¹ =
      qel x e₂ e₃ (-a, b, -c) := by
  have e1 : (t * (ρ * ρ) * t⁻¹) * qel x e₂ e₃ (a, b, c) * (t * (ρ * ρ) * t⁻¹)⁻¹ =
      t * ((ρ * ρ) * (t⁻¹ * qel x e₂ e₃ (a, b, c) * t) * (ρ * ρ)⁻¹) * t⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e1, h.conj_tinv, h.conj_g1, h.conj_t]

theorem conj_g3 (a b c : ZMod 3) :
    (t * (t * (ρ * ρ) * t⁻¹) * t⁻¹) * qel x e₂ e₃ (a, b, c) *
        (t * (t * (ρ * ρ) * t⁻¹) * t⁻¹)⁻¹ = qel x e₂ e₃ (-a, -b, c) := by
  have e1 : (t * (t * (ρ * ρ) * t⁻¹) * t⁻¹) * qel x e₂ e₃ (a, b, c) *
        (t * (t * (ρ * ρ) * t⁻¹) * t⁻¹)⁻¹ =
      t * (((t * (ρ * ρ) * t⁻¹) * (t⁻¹ * qel x e₂ e₃ (a, b, c) * t) *
        (t * (ρ * ρ) * t⁻¹)⁻¹)) * t⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e1, h.conj_tinv, h.conj_g2, h.conj_t]

end Frame3

section Action

variable (W : Subgroup H) (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)

abbrev commW : CommGroup ↥W :=
  { (inferInstance : Group ↥W) with mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }

def WA (_hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : Type := Additive ↥W

instance instAddCommGroupWA : AddCommGroup (WA W hab) :=
  @Additive.addCommGroup ↥W (commW W hab)

instance instFiniteWA [Finite H] : Finite (WA W hab) := inferInstanceAs (Finite ↥W)

def WA.of (w : ↥W) : WA W hab := Additive.ofMul w

def WA.val (v : WA W hab) : ↥W := Additive.toMul v

variable {W hab}

theorem WA.val_of (w : ↥W) : WA.val W hab (WA.of W hab w) = w := rfl

theorem WA.val_add (a b : WA W hab) : WA.val W hab (a + b) = WA.val W hab a * WA.val W hab b :=
  rfl

theorem WA.val_zero : WA.val W hab (0 : WA W hab) = 1 := rfl

theorem WA.of_mul (a b : ↥W) : WA.of W hab (a * b) = WA.of W hab a + WA.of W hab b := rfl

theorem WA.val_injective : Function.Injective (WA.val W hab) := fun a b h => h

def cj (q : H) (hq : q ∈ normalizer (W : Set H)) (w : ↥W) : ↥W :=
  ⟨q * w * q⁻¹, (mem_normalizer_iff.mp hq w).mp w.2⟩

theorem cj_mul (q : H) (hq : q ∈ normalizer (W : Set H)) (a b : ↥W) :
    cj q hq (a * b) = cj q hq a * cj q hq b :=
  Subtype.ext (by simp only [cj, Subgroup.coe_mul]; group)

def actHom (q : H) (hq : q ∈ normalizer (W : Set H)) : WA W hab →+ WA W hab :=
  AddMonoidHom.mk' (fun w => WA.of W hab (cj q hq (WA.val W hab w))) (by
    intro a b
    rw [WA.val_add, cj_mul, WA.of_mul])

theorem actHom_apply (q : H) (hq : q ∈ normalizer (W : Set H)) (w : WA W hab) :
    (WA.val W hab (actHom q hq w) : H) = q * (WA.val W hab w : H) * q⁻¹ := rfl

namespace Frame3

variable {x e₂ e₃ t ρ : H} {s : ℤ} (h : Frame3 x e₂ e₃ t ρ s)
variable {W : Subgroup H} {hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a}

include h

theorem modData (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hq : ∀ v : Vec, qel x e₂ e₃ v ∈ normalizer (W : Set H)) :
    ModData (fun v => (actHom (W := W) (hab := hab) (qel x e₂ e₃ v) (hq v))) := by
  refine ⟨?_, ?_, ?_⟩
  · ext w
    apply WA.val_injective
    apply Subtype.ext
    show (WA.val W hab (actHom (qel x e₂ e₃ 0) (hq 0) w) : H) = _
    rw [actHom_apply, h.qel_zero]
    simp
  · intro a b
    ext w
    apply WA.val_injective
    apply Subtype.ext
    show (WA.val W hab (actHom (qel x e₂ e₃ (a + b)) (hq (a + b)) w) : H) = _
    rw [AddMonoidHom.comp_apply, actHom_apply, actHom_apply, actHom_apply, h.qel_add]
    group
  · intro v
    apply WA.val_injective
    apply Subtype.ext
    rw [WA.val_add, WA.val_zero]
    have := hW2 _ (WA.val W hab v).2
    simpa [sq] using this

end Frame3

end Action

section Fixed

variable {V : Type} [AddCommGroup V] {T : Vec → V →+ V}

theorem fixedSub_eq_map {a b : Vec} (c : V ≃+ V) (hc : ∀ v, c (T a v) = T b (c v)) :
    fixedSub T b = (fixedSub T a).map c.toAddMonoidHom := by
  ext z
  simp only [AddSubgroup.mem_map, mem_fixedSub]
  constructor
  · intro hz
    refine ⟨c.symm z, ?_, c.apply_symm_apply z⟩
    apply c.injective
    rw [hc, c.apply_symm_apply, hz]
  · rintro ⟨y, hy, rfl⟩
    show T b (c y) = c y
    rw [← hc, hy]

theorem card_fixedSub_of_equiv {a b : Vec} (c : V ≃+ V) (hc : ∀ v, c (T a v) = T b (c v)) :
    Nat.card (fixedSub T a) = Nat.card (fixedSub T b) := by
  rw [fixedSub_eq_map c hc]
  exact (AddSubgroup.card_map_of_injective c.injective).symm

theorem ModData.fixedSub_neg_eq (h : ModData T) (a : Vec) : fixedSub T (-a) = fixedSub T a := by
  ext v
  simp only [mem_fixedSub]
  have h1 : (a + -a : Vec) = 0 := add_neg_cancel a
  have h2 : (-a + a : Vec) = 0 := neg_add_cancel a
  constructor
  · intro hv
    have := h.apply_apply a (-a) v
    rw [h1, h.apply_zero, hv] at this
    exact this
  · intro hv
    have := h.apply_apply (-a) a v
    rw [h2, h.apply_zero, hv] at this
    exact this

end Fixed

section Main

variable {W : Subgroup H} {hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a}

def actEquiv (q : H) (hq : q ∈ normalizer (W : Set H)) : WA W hab ≃+ WA W hab where
  toFun := actHom q hq
  invFun := actHom q⁻¹ ((normalizer (W : Set H)).inv_mem hq)
  left_inv w := by
    apply WA.val_injective
    apply Subtype.ext
    rw [actHom_apply, actHom_apply]
    group
  right_inv w := by
    apply WA.val_injective
    apply Subtype.ext
    rw [actHom_apply, actHom_apply]
    group
  map_add' := map_add _

theorem actHom_fixed_iff (q : H) (hq : q ∈ normalizer (W : Set H)) (v : WA W hab) :
    actHom q hq v = v ↔ q * (WA.val W hab v : H) = (WA.val W hab v : H) * q := by
  constructor
  · intro h
    have := congrArg (fun z => (WA.val W hab z : H)) h
    simp only [actHom_apply] at this
    rwa [mul_inv_eq_iff_eq_mul] at this
  · intro h
    apply WA.val_injective
    apply Subtype.ext
    rw [actHom_apply, mul_inv_eq_iff_eq_mul]
    exact h

end Main

theorem card_ge_of_frame [Finite H] {x e₂ e₃ t ρ : H} {s : ℤ} (hF : Frame3 x e₂ e₃ t ρ s)
    {W : Subgroup H} (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hnx : x ∈ normalizer (W : Set H)) (hn₂ : e₂ ∈ normalizer (W : Set H))
    (hn₃ : e₃ ∈ normalizer (W : Set H)) (hnt : t ∈ normalizer (W : Set H))
    (hnρ : ρ ∈ normalizer (W : Set H))
    (hfx : ∀ w ∈ W, x * w = w * x → w = 1) (hf₂ : ∀ w ∈ W, e₂ * w = w * e₂ → w = 1)
    (hf₃ : ∀ w ∈ W, e₃ * w = w * e₃ → w = 1) (hne : W ≠ ⊥) : 256 ≤ Nat.card W := by
  classical
  have hq : ∀ v : Vec, qel x e₂ e₃ v ∈ normalizer (W : Set H) := by
    intro v
    exact (normalizer (W : Set H)).mul_mem ((normalizer (W : Set H)).mul_mem
      ((normalizer (W : Set H)).pow_mem hnx _) ((normalizer (W : Set H)).pow_mem hn₂ _))
      ((normalizer (W : Set H)).pow_mem hn₃ _)
  let T : Vec → WA W hWab →+ WA W hWab := fun v => actHom (qel x e₂ e₃ v) (hq v)
  have hM : ModData T := hF.modData hW2 hq
  have hcoord : ∀ l v, T (cv l) v = v → v = 0 := by
    intro l v hv
    have key : ∀ g : H, qel x e₂ e₃ (cv l) = g → (∀ w ∈ W, g * w = w * g → w = 1) → v = 0 := by
      intro g hg hfg
      have hfix := (actHom_fixed_iff (hab := hWab) _ (hq (cv l)) v).mp hv
      rw [hg] at hfix
      apply WA.val_injective
      exact Subtype.ext (hfg _ (WA.val W hWab v).2 hfix)
    fin_cases l
    · exact key x (by simp [qel, cv, gp_one hF.x3, gp_zero]) hfx
    · exact key e₂ (by simp [qel, cv, gp_one hF.e₂3, gp_zero]) hf₂
    · exact key e₃ (by simp [qel, cv, gp_one hF.e₃3, gp_zero]) hf₃
  have hconj : ∀ (g : H) (hg : g ∈ normalizer (W : Set H)) (a b : Vec),
      g * qel x e₂ e₃ a * g⁻¹ = qel x e₂ e₃ b →
      Nat.card (fixedSub T a) = Nat.card (fixedSub T b) := by
    intro g hg a b hab'
    refine card_fixedSub_of_equiv (actEquiv (hab := hWab) g hg) fun v => ?_
    apply WA.val_injective
    apply Subtype.ext
    show (WA.val W hWab (actHom g hg (actHom (qel x e₂ e₃ a) (hq a) v)) : H) =
      (WA.val W hWab (actHom (qel x e₂ e₃ b) (hq b) (actHom g hg v)) : H)
    rw [actHom_apply, actHom_apply, actHom_apply, actHom_apply, ← hab']
    group
  have hg1 : ρ * ρ ∈ normalizer (W : Set H) := (normalizer (W : Set H)).mul_mem hnρ hnρ
  have hg2 : t * (ρ * ρ) * t⁻¹ ∈ normalizer (W : Set H) :=
    (normalizer (W : Set H)).mul_mem ((normalizer (W : Set H)).mul_mem hnt hg1)
      ((normalizer (W : Set H)).inv_mem hnt)
  have hg3 : t * (t * (ρ * ρ) * t⁻¹) * t⁻¹ ∈ normalizer (W : Set H) :=
    (normalizer (W : Set H)).mul_mem ((normalizer (W : Set H)).mul_mem hnt hg2)
      ((normalizer (W : Set H)).inv_mem hnt)
  have hv0 : dv 0 = (1, 1, 1) := by decide
  have hv3 : dv 3 = (1, -1, -1) := by decide
  have hv2 : -dv 2 = (-1, 1, -1) := by decide
  have hv1 : -dv 1 = (-1, -1, 1) := by decide
  have h3 : Nat.card (fixedSub T (dv 3)) = Nat.card (fixedSub T (dv 0)) := by
    refine (hconj (ρ * ρ) hg1 (dv 0) (dv 3) ?_).symm
    rw [hv0, hv3, hF.conj_g1]
  have h2 : Nat.card (fixedSub T (dv 2)) = Nat.card (fixedSub T (dv 0)) := by
    have e : Nat.card (fixedSub T (-dv 2)) = Nat.card (fixedSub T (dv 0)) := by
      refine (hconj _ hg2 (dv 0) (-dv 2) ?_).symm
      rw [hv0, hv2, hF.conj_g2]
    rwa [hM.fixedSub_neg_eq] at e
  have h1 : Nat.card (fixedSub T (dv 1)) = Nat.card (fixedSub T (dv 0)) := by
    have e : Nat.card (fixedSub T (-dv 1)) = Nat.card (fixedSub T (dv 0)) := by
      refine (hconj _ hg3 (dv 0) (-dv 1) ?_).symm
      rw [hv0, hv1, hF.conj_g3]
    rwa [hM.fixedSub_neg_eq] at e
  have hsym : ∀ i j : Fin 4, Nat.card (fixedSub T (dv i)) = Nat.card (fixedSub T (dv j)) := by
    have hk : ∀ k : Fin 4, Nat.card (fixedSub T (dv k)) = Nat.card (fixedSub T (dv 0)) := by
      intro k
      fin_cases k
      · rfl
      · exact h1
      · exact h2
      · exact h3
    intro i j
    rw [hk i, hk j]
  have hne' : ∃ v : WA W hWab, v ≠ 0 := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    refine ⟨WA.of W hWab ⟨w, hw⟩, fun h0 => hw1 ?_⟩
    have := congrArg (WA.val W hWab) h0
    simpa [WA.val_of, WA.val_zero] using this
  have key := hM.card_ge hcoord hsym hne'
  have hc : Nat.card (WA W hWab) = Nat.card W := Nat.card_congr (Additive.toMul : Additive ↥W ≃ ↥W)
  rw [hc] at key
  exact key

end Frame

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod
