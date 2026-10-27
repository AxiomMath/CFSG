module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EModel
public import CFSG.Assembly.Defs

public section

set_option linter.unusedSectionVars false

open CFSG.Open

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

theorem exists_vec (C : Type) [Group C] (hc : ∀ x y : C, x * y = y * x) (h3 : ∀ x : C, x ^ 3 = 1) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V), Nonempty (C ≃* Multiplicative V) := by
  let _ : CommGroup C := { ‹Group C› with mul_comm := hc }
  have h : ∀ x : Additive C, (3 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    simpa using h3 (Additive.toMul x)
  let _ := AddCommGroup.zmodModule h
  exact ⟨Additive C, inferInstance, inferInstance, ⟨{
    toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
    invFun := fun y => Additive.toMul (Multiplicative.toAdd y)
    left_inv := fun x => rfl
    right_inv := fun y => rfl
    map_mul' := fun x y => rfl }⟩⟩

section Iso
variable {C : Type} [Group C] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  (e : C ≃* Multiplicative V)

@[expose] def ev (x : C) : V := Multiplicative.toAdd (e x)

@[simp] theorem ev_mul (x y : C) : ev e (x * y) = ev e x + ev e y := by simp [ev]
@[simp] theorem ev_one : ev e 1 = 0 := by simp [ev]
@[simp] theorem ev_inv (x : C) : ev e x⁻¹ = - ev e x := by simp [ev]

@[expose] def evEquiv : C ≃ V := e.toEquiv.trans Multiplicative.toAdd

@[simp] theorem evEquiv_apply (x : C) : evEquiv e x = ev e x := rfl
theorem ev_injective : Function.Injective (ev e) := (evEquiv e).injective
theorem ev_eq_zero {x : C} : ev e x = 0 ↔ x = 1 := by
  rw [← ev_one e]; exact (ev_injective e).eq_iff
@[simp] theorem ev_symm (v : V) : ev e (e.symm (Multiplicative.ofAdd v)) = v := by simp [ev]
theorem exists_ev (v : V) : ∃ x, ev e x = v := ⟨_, ev_symm e v⟩

@[simp] theorem symm_ev (x : C) : e.symm (Multiplicative.ofAdd (ev e x)) = x := by simp [ev]

@[expose] def glAdd (g : MulAut C) : V →+ V where
  toFun v := ev e (g (e.symm (Multiplicative.ofAdd v)))
  map_zero' := by
    have : e.symm (Multiplicative.ofAdd (0 : V)) = 1 := by rw [ofAdd_zero, map_one]
    simp
  map_add' x y := by simp

@[expose] def gl (g : MulAut C) : V ≃ₗ[ZMod 3] V where
  toFun := glAdd e g
  map_add' := map_add _
  map_smul' c x := ZMod.map_smul (glAdd e g) c x
  invFun := glAdd e g.symm
  left_inv v := by simp [glAdd]
  right_inv v := by simp [glAdd]

theorem gl_apply (g : MulAut C) (x : C) : gl e g (ev e x) = ev e (g x) := by simp [gl, glAdd]


@[expose] def glMonoid : MulAut C →* (V ≃ₗ[ZMod 3] V) where
  toFun := gl e
  map_one' := by
    ext v
    obtain ⟨x, rfl⟩ := exists_ev e v
    simp [gl_apply]
  map_mul' g h := by
    ext v
    obtain ⟨x, rfl⟩ := exists_ev e v
    simp [gl_apply]

theorem glMonoid_bijective : Function.Bijective (glMonoid e) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro g hg
    ext x
    have := congrArg (fun φ : V ≃ₗ[ZMod 3] V => φ (ev e x)) hg
    simp only [glMonoid, MonoidHom.coe_mk, OneHom.coe_mk, gl_apply] at this
    exact ev_injective e (by simpa using this)
  · intro φ
    let g : MulAut C :=
      { toFun := fun x => e.symm (Multiplicative.ofAdd (φ (ev e x)))
        invFun := fun x => e.symm (Multiplicative.ofAdd (φ.symm (ev e x)))
        left_inv := fun x => by simp
        right_inv := fun x => by simp
        map_mul' := fun x y => by simp [← map_mul] }
    refine ⟨g, ?_⟩
    ext v
    obtain ⟨x, rfl⟩ := exists_ev e v
    simp [glMonoid, gl_apply, g]

@[expose] noncomputable def glHom : MulAut C ≃* (V ≃ₗ[ZMod 3] V) :=
  MulEquiv.ofBijective (glMonoid e) (glMonoid_bijective e)

theorem glHom_apply (g : MulAut C) (v : V) : glHom e g v = gl e g v := rfl

theorem glHom_ev (g : MulAut C) (x : C) : glHom e g (ev e x) = ev e (g x) := gl_apply e g x

@[expose] noncomputable def gmap (H : Subgroup (MulAut C)) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  H.map (glHom e).toMonoidHom

theorem mem_gmap {H : Subgroup (MulAut C)} {y : V ≃ₗ[ZMod 3] V} :
    y ∈ gmap e H ↔ (glHom e).symm y ∈ H := by
  unfold gmap
  rw [Subgroup.mem_map_equiv]

theorem glHom_mem_gmap {H : Subgroup (MulAut C)} {g : MulAut C} : glHom e g ∈ gmap e H ↔ g ∈ H := by
  rw [mem_gmap]; simp

@[expose] def toAddSub (S : Subgroup C) : AddSubgroup V where
  carrier := {v | e.symm (Multiplicative.ofAdd v) ∈ S}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have : e.symm (Multiplicative.ofAdd (a + b)) =
        e.symm (Multiplicative.ofAdd a) * e.symm (Multiplicative.ofAdd b) := by
      rw [← map_mul]; rfl
    show _ ∈ S
    rw [this]; exact S.mul_mem ha hb
  neg_mem' := fun {a} ha => by
    have : e.symm (Multiplicative.ofAdd (-a)) = (e.symm (Multiplicative.ofAdd a))⁻¹ := by
      rw [← map_inv]; rfl
    show _ ∈ S
    rw [this]; exact S.inv_mem ha

theorem ev_mem_toAddSub {S : Subgroup C} {x : C} : ev e x ∈ toAddSub e S ↔ x ∈ S := by
  show e.symm (Multiplicative.ofAdd (ev e x)) ∈ S ↔ _
  rw [symm_ev]

@[expose] def toSub (S : Subgroup C) : Submodule (ZMod 3) V :=
  AddSubgroup.toZModSubmodule 3 (toAddSub e S)

theorem ev_mem_toSub {S : Subgroup C} {x : C} : ev e x ∈ toSub e S ↔ x ∈ S :=
  ev_mem_toAddSub e

theorem mem_toSub {S : Subgroup C} {v : V} : v ∈ toSub e S ↔ e.symm (Multiplicative.ofAdd v) ∈ S :=
  Iff.rfl

theorem card_of_iff (S : Subgroup C) (T : AddSubgroup V) (h : ∀ x, x ∈ S ↔ ev e x ∈ T) :
    Nat.card S = Nat.card T :=
  Nat.card_congr (Equiv.subtypeEquiv (evEquiv e) h)

theorem card_toSub (S : Subgroup C) : Nat.card (toSub e S) = Nat.card S := by
  rw [card_of_iff e S (toAddSub e S) (fun x => (ev_mem_toAddSub e).symm)]
  exact Nat.card_congr (Equiv.refl _)

theorem toSub_eq_iff {S S' : Subgroup C} : toSub e S = toSub e S' ↔ S = S' := by
  constructor
  · intro h
    ext x
    rw [← ev_mem_toSub e, ← ev_mem_toSub e (S := S'), h]
  · rintro rfl; rfl

theorem toSub_map [Finite V] (g : MulAut C) (S : Subgroup C) :
    toSub e (S.map g.toMonoidHom) = Datum.img (glHom e g) (toSub e S) := by
  ext v
  obtain ⟨x, rfl⟩ := exists_ev e v
  rw [ev_mem_toSub, Datum.mem_img]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨ev e s, (ev_mem_toSub e).2 hs, glHom_ev e g s⟩
  · rintro ⟨s', hs', h⟩
    obtain ⟨s, rfl⟩ := exists_ev e s'
    rw [glHom_ev] at h
    exact ⟨s, (ev_mem_toSub e).1 hs', ev_injective e h⟩


theorem gmap_elim {H : Subgroup (MulAut C)} {y : V ≃ₗ[ZMod 3] V} (hy : y ∈ gmap e H) :
    ∃ g ∈ H, y = glHom e g :=
  ⟨(glHom e).symm y, mem_gmap e |>.1 hy, by simp⟩

theorem gmap_mono {H H' : Subgroup (MulAut C)} (h : H ≤ H') : gmap e H ≤ gmap e H' :=
  Subgroup.map_mono h

end Iso

section Build
variable {G : Type} [Group G] {B : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [Finite V] (e : ↥B ≃* Multiplicative V)

structure Setup (W Q : Subgroup (MulAut ↥B)) (A F : Subgroup ↥B) : Prop where
  card_B : Nat.card ↥B = 81
  card_A : Nat.card A = 9
  card_F : Nat.card F = 9
  Q_le_W : Q ≤ W
  Q_fix_A : ∀ q ∈ Q, ∀ a ∈ A, q a = a
  Q_mem_F : ∀ q ∈ Q, ∀ f ∈ F, q f ∈ F
  Q_faith_F : ∀ q ∈ Q, (∀ f ∈ F, q f = f) → q = 1
  quat : Nonempty (Q ≃* QuaternionGroup 2)

variable {W Q : Subgroup (MulAut ↥B)} {A F : Subgroup ↥B}

theorem Setup.planeQ (e : ↥B ≃* Multiplicative V) (h : Setup W Q A F) : PlaneQ (gmap e Q) (toSub e F) where
  card_F := (card_toSub e F).trans h.card_F
  quat := ⟨((MulEquiv.subgroupMap (glHom e) Q).symm).trans h.quat.some⟩
  mem := by
    intro q hq f hf
    obtain ⟨q', hq', rfl⟩ := gmap_elim e hq
    obtain ⟨x, rfl⟩ := exists_ev e f
    rw [glHom_ev, ev_mem_toSub]
    exact h.Q_mem_F q' hq' x ((ev_mem_toSub e).1 hf)
  faith := by
    intro q hq hqf
    obtain ⟨q', hq', rfl⟩ := gmap_elim e hq
    have : q' = 1 := h.Q_faith_F q' hq' fun x hx => by
      have := hqf (ev e x) ((ev_mem_toSub e).2 hx)
      rw [glHom_ev] at this
      exact ev_injective e this
    rw [this, map_one]

theorem Setup.isCompl (e : ↥B ≃* Multiplicative V) (h : Setup W Q A F) : IsCompl (toSub e A) (toSub e F) := by
  have hP := h.planeQ e
  have hdis : Disjoint (toSub e A) (toSub e F) := by
    rw [Submodule.disjoint_def]
    intro x hxA hxF
    obtain ⟨t, ht, ht1, -, -⟩ := hP.exists_t
    apply hP.free t ht ht1 x hxF
    obtain ⟨t', ht', rfl⟩ := gmap_elim e ht
    obtain ⟨a, rfl⟩ := exists_ev e x
    rw [glHom_ev, h.Q_fix_A t' ht' a ((ev_mem_toSub e).1 hxA)]
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro v _
  let f : toSub e A × toSub e F → V := fun p => (p.1 : V) + p.2
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : V) + b = a' + b' := hab
    have h1 : ((a : V) - a') = (b' : V) - b := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (b' : V) a']; exact hab'
    have h0 : ((a : V) - a') = 0 := by
      rw [Submodule.disjoint_def] at hdis
      exact hdis _ (Submodule.sub_mem _ a.2 a'.2) (h1 ▸ Submodule.sub_mem _ b'.2 b.2)
    have h2 : (a : V) = a' := sub_eq_zero.1 h0
    have h3 : (b : V) = b' := by rw [h2] at hab'; exact add_left_cancel hab'
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hcardV : Nat.card V = 81 := by
    rw [← h.card_B]; exact (Nat.card_congr (evEquiv e)).symm
  have hbij : Function.Bijective f := by
    apply hinj.bijective_of_nat_card_le
    rw [Nat.card_prod, card_toSub, card_toSub, h.card_A, h.card_F, hcardV]
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 v
  rw [← hab]
  exact Submodule.add_mem_sup a.2 b.2

@[expose] noncomputable def Setup.datum (e : ↥B ≃* Multiplicative V) (h : Setup W Q A F) : Datum V where
  W := gmap e W
  Q := gmap e Q
  A := toSub e A
  F := toSub e F
  card_A := (card_toSub e A).trans h.card_A
  isCompl := h.isCompl e
  Q_le_W := gmap_mono e h.Q_le_W
  Q_fix_A := by
    intro q hq a ha
    obtain ⟨q', hq', rfl⟩ := gmap_elim e hq
    obtain ⟨x, rfl⟩ := exists_ev e a
    rw [glHom_ev, h.Q_fix_A q' hq' x ((ev_mem_toSub e).1 ha)]
  planeQ := h.planeQ e


@[simp] theorem Setup.datum_W (h : Setup W Q A F) : (h.datum e).W = gmap e W := rfl
@[simp] theorem Setup.datum_Q (h : Setup W Q A F) : (h.datum e).Q = gmap e Q := rfl
@[simp] theorem Setup.datum_A (h : Setup W Q A F) : (h.datum e).A = toSub e A := rfl
@[simp] theorem Setup.datum_F (h : Setup W Q A F) : (h.datum e).F = toSub e F := rfl

theorem faithfulOver_gmap (h : Setup W Q A F) {S : Subgroup (MulAut ↥B)} (hSW : S ≤ W) (hQS : Q ≤ S)
    (hmem : ∀ s ∈ S, ∀ f ∈ F, s f ∈ F) (hfaith : ∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1) :
    (h.datum e).FaithfulOver (gmap e S) where
  le_W := gmap_mono e hSW
  Q_le := gmap_mono e hQS
  mem_F := by
    intro s hs f hf
    obtain ⟨s', hs', rfl⟩ := gmap_elim e hs
    obtain ⟨x, rfl⟩ := exists_ev e f
    show glHom e s' (ev e x) ∈ toSub e F
    rw [glHom_ev, ev_mem_toSub]
    exact hmem s' hs' x ((ev_mem_toSub e).1 hf)
  faith := by
    intro s hs hsf
    obtain ⟨s', hs', rfl⟩ := gmap_elim e hs
    have : s' = 1 := hfaith s' hs' fun x hx => by
      have := hsf (ev e x) ((ev_mem_toSub e).2 hx)
      rw [glHom_ev] at this
      exact ev_injective e this
    rw [this, map_one]

theorem hasKa_of (h : Setup W Q A F)
    (hK : ∀ a ∈ A, a ≠ 1 → ∃ S : Subgroup (MulAut ↥B), S ≤ W ∧ Q ≤ S ∧
      (∀ s ∈ S, ∀ f ∈ F, s f ∈ F) ∧ (∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1) ∧
      ∀ w ∈ W, (w a = a ∨ w a = a⁻¹) → ∀ s ∈ S, w * s * w⁻¹ ∈ S) :
    (h.datum e).HasKa := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := exists_ev e v
  have ha : a ∈ A := (ev_mem_toSub e).1 hv
  have ha1 : a ≠ 1 := fun h1 => hv0 (by rw [h1, ev_one])
  obtain ⟨S, hSW, hQS, hmem, hfaith, hnorm⟩ := hK a ha ha1
  refine ⟨gmap e S, faithfulOver_gmap e h hSW hQS hmem hfaith, ?_⟩
  intro w hw hwa s hs
  obtain ⟨w', hw', rfl⟩ := gmap_elim e hw
  obtain ⟨s', hs', rfl⟩ := gmap_elim e hs
  have hwa' : w' a = a ∨ w' a = a⁻¹ := by
    rcases hwa with h1 | h1
    · left
      exact ev_injective e (by rw [← glHom_ev]; exact h1)
    · right
      refine ev_injective e ?_
      rw [ev_inv, ← glHom_ev]; exact h1
  have := hnorm w' hw' hwa' s' hs'
  have h2 := (glHom_mem_gmap e (H := S)).2 this
  simpa using h2

theorem hasJ_of (h : Setup W Q A F)
    (hJ : ∃ S : Subgroup (MulAut ↥B), S ≤ W ∧ Q ≤ S ∧
      (∀ s ∈ S, ∀ f ∈ F, s f ∈ F) ∧ (∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1) ∧
      ∀ w ∈ W, (∀ a ∈ A, w a ∈ A) → ∀ s ∈ S, w * s * w⁻¹ ∈ S) :
    (h.datum e).HasJ := by
  obtain ⟨S, hSW, hQS, hmem, hfaith, hnorm⟩ := hJ
  refine ⟨gmap e S, faithfulOver_gmap e h hSW hQS hmem hfaith, ?_⟩
  intro w hw hwA s hs
  obtain ⟨w', hw', rfl⟩ := gmap_elim e hw
  obtain ⟨s', hs', rfl⟩ := gmap_elim e hs
  have hwA' : ∀ a ∈ A, w' a ∈ A := by
    intro a ha
    have := hwA (ev e a) ((ev_mem_toSub e).2 ha)
    change glHom e w' (ev e a) ∈ toSub e A at this
    rw [glHom_ev, ev_mem_toSub] at this
    exact this
  have := hnorm w' hw' hwA' s' hs'
  have h2 := (glHom_mem_gmap e (H := S)).2 this
  simpa using h2

end Build

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
