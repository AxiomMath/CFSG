module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV
public import CFSG.CGT.PushingUpLit.CGT6.EmbTY
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open scoped commutatorElement

theorem card_sup_le_mul {V : Type} [CommGroup V] [Finite V] (A B : Subgroup V) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hsurj : Function.Surjective
      (fun p : A × B => (⟨(p.1 : V) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod] at this

section Stab

variable {V : Type} [CommGroup V]

@[expose] def stabV (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ w : V, x w ∈ W ↔ w ∈ W}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro a b ha hb w
    rw [MulAut.mul_apply, ha, hb]
  inv_mem' := by
    intro a ha w
    have := ha (a⁻¹ w)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem apply_mem_of_mem_stabV {W : Subgroup V} {x : MulAut V} (hx : x ∈ stabV W) {w : V}
    (hw : w ∈ W) : x w ∈ W :=
  (hx w).2 hw

@[expose] noncomputable def resStab (W : Subgroup V) : stabV W →* MulAut ↥W where
  toFun x := restrictAut (x : MulAut V) W (fun _ hh => apply_mem_of_mem_stabV x.2 hh)
    (fun _ hh => apply_mem_of_mem_stabV ((stabV W).inv_mem x.2) hh)
  map_one' := by
    ext h
    rfl
  map_mul' x y := by
    ext h
    rfl

theorem resStab_apply (W : Subgroup V) (x : stabV W) (w : ↥W) :
    ((resStab W x w : ↥W) : V) = (x : MulAut V) (w : V) := rfl

theorem mem_stabV_commV {X : Subgroup (MulAut V)} {k : MulAut V}
    (hk : k ∈ Subgroup.normalizer (X : Set (MulAut V))) : k ∈ stabV (commV X) := by
  intro w
  have h1 : ∀ w' ∈ commV X, k w' ∈ commV X := fun w' hw' =>
    G6.apply_mem_commV (fun x hx => (Subgroup.mem_normalizer_iff.mp hk x).mp hx) hw'
  have hk' : k⁻¹ ∈ Subgroup.normalizer (X : Set (MulAut V)) := (Subgroup.normalizer _).inv_mem hk
  have h2 : ∀ w' ∈ commV X, k⁻¹ w' ∈ commV X := fun w' hw' =>
    G6.apply_mem_commV (fun x hx => (Subgroup.mem_normalizer_iff.mp hk' x).mp hx) hw'
  refine ⟨fun hw => ?_, h1 w⟩
  have := h2 _ hw
  rwa [MulAut.inv_apply_self] at this

theorem le_stabV_commV (X : Subgroup (MulAut V)) : X ≤ stabV (commV X) :=
  fun _ hx => mem_stabV_commV (Subgroup.le_normalizer hx)

@[expose] def trV (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ v : V, x v * v⁻¹ ∈ W}
  one_mem' := fun v => by simp
  mul_mem' := by
    intro a b ha hb v
    have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
      simp [MulAut.mul_apply]
    rw [this]
    exact mul_mem (ha (b v)) (hb v)
  inv_mem' := by
    intro a ha v
    have : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by simp
    rw [this]
    exact inv_mem (ha (a⁻¹ v))

@[expose] def centW (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ w ∈ W, x w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb w hw
    rw [MulAut.mul_apply, hb w hw, ha w hw]
  inv_mem' := by
    intro a ha w hw
    have h := congrArg (fun z => a⁻¹ z) (ha w hw)
    simp only [MulAut.inv_apply_self] at h
    exact h.symm

@[expose] def stabGrp (W : Subgroup V) : Subgroup (MulAut V) := centW W ⊓ trV W

theorem mem_stabGrp {W : Subgroup V} {x : MulAut V} :
    x ∈ stabGrp W ↔ (∀ w ∈ W, x w = w) ∧ ∀ v : V, x v * v⁻¹ ∈ W := Iff.rfl

theorem le_trV_commV (X : Subgroup (MulAut V)) : X ≤ trV (commV X) :=
  fun _ hx v => G6.mem_commV_of_mem hx v

theorem sq_eq_one_of_mem_stabGrp (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {x : MulAut V}
    (hx : x ∈ stabGrp W) : x ^ 2 = 1 := by
  ext v
  have hw : x v * v⁻¹ ∈ W := hx.2 v
  have h1 : x (x v * v⁻¹) = x v * v⁻¹ := hx.1 _ hw
  rw [map_mul, map_inv] at h1
  have hvv : v * v = 1 := by rw [← pow_two]; exact hV v
  have hxx : x v * x v = 1 := by rw [← pow_two]; exact hV _
  have h2 : (x ^ 2) v = x (x v) := by simp [pow_two, MulAut.mul_apply]
  rw [h2]
  calc x (x v) = (x (x v) * (x v)⁻¹) * x v := (inv_mul_cancel_right _ _).symm
    _ = (x v * v⁻¹) * x v := by rw [h1]
    _ = (x v * x v) * v⁻¹ := mul_right_comm _ _ _
    _ = v⁻¹ := by rw [hxx, one_mul]
    _ = v := inv_eq_of_mul_eq_one_right hvv

theorem isPGroup_two_stabGrp (hV : ∀ v : V, v ^ 2 = 1) (W : Subgroup V) :
    IsPGroup 2 ↥(stabGrp W) := fun x =>
  ⟨1, Subtype.ext (by simpa using sq_eq_one_of_mem_stabGrp hV x.2)⟩

theorem stabV_le_normalizer_stabGrp (W : Subgroup V) :
    stabV W ≤ Subgroup.normalizer (stabGrp W : Set (MulAut V)) := by
  have key : ∀ n ∈ stabV W, ∀ x ∈ stabGrp W, n * x * n⁻¹ ∈ stabGrp W := by
    intro n hn x hx
    have hn' : n⁻¹ ∈ stabV W := (stabV W).inv_mem hn
    refine ⟨?_, ?_⟩
    · intro w hw
      have h1 : n⁻¹ w ∈ W := apply_mem_of_mem_stabV hn' hw
      have h2 := hx.1 _ h1
      show n (x (n⁻¹ w)) = w
      rw [h2]
      exact MulAut.apply_inv_self _ n w
    · intro v
      have h3 : (n * x * n⁻¹) v * v⁻¹ = n (x (n⁻¹ v) * (n⁻¹ v)⁻¹) := by
        simp [MulAut.mul_apply]
      rw [h3]
      exact apply_mem_of_mem_stabV hn (hx.2 _)
  intro n hn
  refine mem_normalizer_of_conj_mem (key n hn) (fun x hx => ?_)
  have := key n⁻¹ ((stabV W).inv_mem hn) x hx
  simpa using this

end Stab

theorem card_mulAut_of_card_four {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hc : Nat.card W = 4) : Nat.card (MulAut W) = 6 := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn2 : n = 2 := by
    have : 2 ^ n = 2 ^ 2 := by rw [← hn, hc]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hn2
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  rw [hGL, Matrix.card_GL_field]
  simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]

theorem commute_of_sup_three_group {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {Y Y' : Subgroup (MulAut V)} (hU : Nat.card ↥(commV Y) ≤ 4) (hU' : Nat.card ↥(commV Y') ≤ 4)
    (h3 : IsPGroup 3 ↥(Y ⊔ Y')) : ∀ a ∈ Y ⊔ Y', ∀ b ∈ Y ⊔ Y', a * b = b * a := by
  refine commute_of_three_group hV h3 ?_
  have h1 : Nat.card ↥(commV (Y ⊔ Y')) ≤ Nat.card ↥(commV Y ⊔ commV Y') :=
    Subgroup.card_le_of_le (commV_sup_le Y Y')
  have h2 := card_sup_le_mul (commV Y) (commV Y')
  calc Nat.card ↥(commV (Y ⊔ Y')) ≤ Nat.card ↥(commV Y ⊔ commV Y') := h1
    _ ≤ Nat.card ↥(commV Y) * Nat.card ↥(commV Y') := h2
    _ ≤ 4 * 4 := Nat.mul_le_mul hU hU'

structure Sec5Hyp (V : Type) [CommGroup V] (G T Y : Subgroup (MulAut V)) : Prop where
  elem : ∀ v : V, v ^ 2 = 1
  tle : T ≤ G
  tTwo : IsPGroup 2 ↥T
  yle : Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V))
  ysub : (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal
  ycard : Nat.card ↥Y = 3
  ucard : Nat.card ↥(commV Y) = 4

namespace Sec5Hyp

variable {V : Type} [CommGroup V] {G T Y : Subgroup (MulAut V)} (h : Sec5Hyp V G T Y)
include h

theorem pow_three {y : MulAut V} (hy : y ∈ Y) : y ^ 3 = 1 := by
  have : (⟨y, hy⟩ : ↥Y) ^ Nat.card ↥Y = 1 := pow_card_eq_one'
  rw [h.ycard] at this
  simpa using congrArg Subtype.val this

theorem odd_orderOf {y : MulAut V} (hy : y ∈ Y) : Odd (orderOf y) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (h.pow_three hy))

theorem noTwoQuotient : SubTwo.NoTwoQuotient Y := by
  intro N hNY _ h2
  apply le_antisymm hNY
  intro y hy
  obtain ⟨k, hk⟩ := h2 y hy
  have hy3 := h.pow_three hy
  have h4 : y ^ (4 ^ k) = y := by
    have hmod : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    calc y ^ (4 ^ k) = y ^ (3 * (4 ^ k / 3) + 4 ^ k % 3) := by rw [Nat.div_add_mod]
      _ = y := by rw [pow_add, pow_mul, hy3, one_pow, one_mul, hmod, pow_one]
  have : y = (y ^ 2 ^ k) ^ 2 ^ k := by
    rw [← pow_mul, ← mul_pow]
    exact h4.symm
  rw [this]
  exact N.pow_mem hk _

theorem oTwoIn_eq_bot : oTwoIn Y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxY : x ∈ Y := SixThree.oTwoIn_le _ hx
  obtain ⟨k, hk⟩ := SixThree.isPGroup_oTwoIn Y ⟨x, hx⟩
  have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hx3 := h.pow_three hxY
  have hg : Nat.gcd (2 ^ k) 3 = 1 := by
    apply Nat.Coprime.pow_left
    norm_num
  have := pow_gcd_eq_one.mpr ⟨hx2, hx3⟩
  rw [hg, pow_one] at this
  exact this ▸ one_mem _

theorem oTwo_comm : ⁅oTwoIn Y, Y⁆ = ⊥ := by
  rw [h.oTwoIn_eq_bot]
  simp

theorem mem_normalizer_Y_of_mem_T {x : MulAut V} (hx : x ∈ T) :
    x ∈ Subgroup.normalizer (Y : Set (MulAut V)) := by
  have hc : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ = y := by
    intro t ht y hy
    have := Subgroup.mem_centralizer_iff.mp (h.yle hy).2 t ht
    rw [this]
    group
  refine mem_normalizer_of_conj_mem (fun y hy => by rw [hc x hx y hy]; exact hy) (fun y hy => ?_)
  have := hc x⁻¹ (T.inv_mem hx) y hy
  simp only [inv_inv] at this
  rw [this]
  exact hy

theorem stab_T : T ≤ stabV (commV Y) := fun _ hx => mem_stabV_commV (h.mem_normalizer_Y_of_mem_T hx)

theorem comm_eq_bot [Finite V] {B : Subgroup (MulAut V)} (hBG : B ≤ G) (hB2 : IsPGroup 2 ↥B)
    (hTB : T ≤ Subgroup.normalizer (B : Set (MulAut V)))
    (hYB : Y ≤ Subgroup.normalizer (B : Set (MulAut V))) : ⁅B, Y⁆ = ⊥ :=
  commutator_eq_bot_of_centralizer (G₀ := G) h.noTwoQuotient (Or.inr h.ycard) h.oTwo_comm h.tTwo
    hB2 hBG hTB hYB h.yle h.ysub

variable [Finite V]

omit [Finite V] in
theorem injective_res :
    Function.Injective ((resStab (commV Y)).comp (Subgroup.inclusion (le_stabV_commV Y))) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have htriv : ∀ w ∈ commV Y, (y : MulAut V) w = w := by
    intro w hw
    have := congrArg (fun φ : MulAut ↥(commV Y) => ((φ ⟨w, hw⟩ : ↥(commV Y)) : V)) hy
    simpa [resStab_apply] using this
  exact Subtype.ext (eq_one_of_trivial_on_commV h.elem y.2 (h.odd_orderOf y.2) htriv)

theorem conj_mem_of_stabV {g : MulAut V} (hg : g ∈ G) (hgU : g ∈ stabV (commV Y)) {y : MulAut V}
    (hy : y ∈ Y) : g * y * g⁻¹ ∈ Y := by
  set U : Subgroup V := commV Y with hUdef
  have hyG : y ∈ G := (h.yle hy).1
  set y' : MulAut V := g * y * g⁻¹ with hy'def
  have hy'G : y' ∈ G := G.mul_mem (G.mul_mem hg hyG) (G.inv_mem hg)
  have hy'stab : y' ∈ stabV U :=
    (stabV U).mul_mem ((stabV U).mul_mem hgU (le_stabV_commV Y hy)) ((stabV U).inv_mem hgU)
  have hy'3 : y' ^ 3 = 1 := by
    have : y' ^ 3 = g * y ^ 3 * g⁻¹ := conj_pow
    rw [this, h.pow_three hy]
    group
  have hy'tr : y' ∈ trV U := by
    intro v
    have e : y' v * v⁻¹ = g (y (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
      simp [hy'def, MulAut.mul_apply]
    rw [e]
    exact apply_mem_of_mem_stabV hgU (G6.mem_commV_of_mem hy _)
  set φ : ↥Y →* MulAut ↥U := (resStab U).comp (Subgroup.inclusion (le_stabV_commV Y)) with hφ
  have hφinj : Function.Injective φ := h.injective_res
  have hW : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.elem w)
  have hcardAut : Nat.card (MulAut ↥U) = 6 := card_mulAut_of_card_four hW h.ucard
  have hrange : Nat.card φ.range = 3 := by
    rw [← h.ycard]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hindex : φ.range.index = 2 := by
    have := Subgroup.card_mul_index φ.range
    rw [hrange, hcardAut] at this
    omega
  have : φ.range.Normal := Subgroup.normal_of_index_eq_two hindex
  have hρ3 : (resStab U ⟨y', hy'stab⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y', hy'stab⟩ : stabV U) ^ 3 = 1 := Subtype.ext (by simpa using hy'3)
    rw [this, map_one]
  have hmem : resStab U ⟨y', hy'stab⟩ ∈ φ.range := by
    rw [← QuotientGroup.eq_one_iff]
    set q : MulAut ↥U ⧸ φ.range := QuotientGroup.mk (resStab U ⟨y', hy'stab⟩) with hq
    have hq3 : q ^ 3 = 1 := by
      rw [hq, ← QuotientGroup.mk_pow, hρ3]
      rfl
    have hq2 : q ^ 2 = 1 := by
      have : Nat.card (MulAut ↥U ⧸ φ.range) = 2 := by
        rw [← Subgroup.index_eq_card]
        exact hindex
      rw [← this]
      exact pow_card_eq_one'
    calc q = q ^ 3 * (q ^ 2)⁻¹ := by group
      _ = 1 := by rw [hq3, hq2]; simp
  obtain ⟨y₀, hy₀⟩ := hmem
  set b : MulAut V := (y₀ : MulAut V)⁻¹ * y' with hbdef
  have hy₀G : (y₀ : MulAut V) ∈ G := (h.yle y₀.2).1
  have hbG : b ∈ G := G.mul_mem (G.inv_mem hy₀G) hy'G
  have hbcent : b ∈ centW U := by
    intro w hw
    have e1 : (y₀ : MulAut V) w = y' w := by
      have := congrArg (fun ψ : MulAut ↥U => ((ψ ⟨w, hw⟩ : ↥U) : V)) hy₀
      simpa [hφ, resStab_apply] using this
    show ((y₀ : MulAut V)⁻¹ * y') w = w
    rw [MulAut.mul_apply, ← e1]
    exact MulAut.inv_apply_self _ _ _
  have hbtr : b ∈ trV U := (trV U).mul_mem ((trV U).inv_mem (le_trV_commV Y y₀.2)) hy'tr
  have hbstab : b ∈ stabGrp U := ⟨hbcent, hbtr⟩
  set B : Subgroup (MulAut V) := stabGrp U ⊓ G with hBdef
  have hB2 : IsPGroup 2 ↥B := (isPGroup_two_stabGrp h.elem U).to_le inf_le_left
  have hTB : T ≤ Subgroup.normalizer (B : Set (MulAut V)) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨stabV_le_normalizer_stabGrp U (h.stab_T hx), Subgroup.le_normalizer (h.tle hx)⟩
  have hYB : Y ≤ Subgroup.normalizer (B : Set (MulAut V)) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨stabV_le_normalizer_stabGrp U (le_stabV_commV Y hx), Subgroup.le_normalizer (h.yle hx).1⟩
  have hcomm : ⁅B, Y⁆ = ⊥ := h.comm_eq_bot inf_le_right hB2 hTB hYB
  have hbB : b ∈ B := ⟨hbstab, hbG⟩
  have hbc : (y₀ : MulAut V) * b = b * y₀ :=
    Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hbB)
      y₀ y₀.2
  have hb2 : b ^ 2 = 1 := sq_eq_one_of_mem_stabGrp h.elem hbstab
  have hy'eq : y' = (y₀ : MulAut V) * b := by simp [hbdef]
  have hb3 : b ^ 3 = 1 := by
    have h1 : y' ^ 3 = (y₀ : MulAut V) ^ 3 * b ^ 3 := by
      rw [hy'eq]
      exact Commute.mul_pow hbc 3
    rw [hy'3, h.pow_three y₀.2, one_mul] at h1
    exact h1.symm
  have hb1 : b = 1 := by
    calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
      _ = 1 := by rw [hb3, hb2]; simp
  rw [hy'eq, hb1, mul_one]
  exact y₀.2

theorem normalizer_of_stabV :
    G ⊓ stabV (commV Y) ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
  intro g ⟨hgG, hgU⟩
  refine mem_normalizer_of_conj_mem (fun y hy => h.conj_mem_of_stabV hgG hgU hy) (fun y hy => ?_)
  have := h.conj_mem_of_stabV (G.inv_mem hgG) ((stabV (commV Y)).inv_mem hgU) hy
  simpa using this

end Sec5Hyp

end CFSG.CGT.PushingUpLit.CGT6
