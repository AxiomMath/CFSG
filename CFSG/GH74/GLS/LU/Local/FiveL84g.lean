module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

open Subgroup

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

structure QData0 (R X : Subgroup G) : Prop where
  le : X ≤ R
  cl : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ X
  cen : ∀ r ∈ R, ∀ a ∈ X, r * a = a * r

structure QData (R X : Subgroup G) : Prop extends QData0 R X where
  five : ∀ r ∈ R, r ^ 5 ∈ X

variable {R X : Subgroup G}

theorem QData0.normal (h : QData0 R X) : (X.subgroupOf R).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have e : (g : G) * a * (g : G)⁻¹ = a := by
    rw [h.cen g.1 g.2 a.1 ha]; group
  simpa [e] using ha

instance QData.instFactQData0 [h : Fact (QData R X)] : Fact (QData0 R X) := ⟨h.out.toQData0⟩

instance QData0.instNormal [h : Fact (QData0 R X)] : (X.subgroupOf R).Normal := h.out.normal

variable (R X) in
@[expose] def QM : Type := ↥R ⧸ X.subgroupOf R

instance QM.instCommGroup [hf : Fact (QData0 R X)] : CommGroup (QM R X) :=
  { (inferInstance : Group (↥R ⧸ X.subgroupOf R)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      show ((a : ↥R ⧸ X.subgroupOf R)) * (b : ↥R ⧸ X.subgroupOf R) =
        (b : ↥R ⧸ X.subgroupOf R) * a
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have := hf.out.cl (b : G)⁻¹ (R.inv_mem b.2) (a : G)⁻¹ (R.inv_mem a.2)
      have e : (((a * b)⁻¹ * (b * a) : ↥R) : G) =
          (b : G)⁻¹ * (a : G)⁻¹ * ((b : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e]; exact this }

variable (R X) in
@[expose] def QV : Type := Additive (QM R X)

instance QV.instAddCommGroup [Fact (QData0 R X)] : AddCommGroup (QV R X) :=
  inferInstanceAs (AddCommGroup (Additive (QM R X)))

instance QV.instFinite [Finite G] : Finite (QV R X) :=
  inferInstanceAs (Finite (Additive (↥R ⧸ X.subgroupOf R)))

@[expose] def QV.mk (r : G) (hr : r ∈ R) : QV R X :=
  Additive.ofMul (show QM R X from QuotientGroup.mk (⟨r, hr⟩ : ↥R))

theorem QV.mk_congr {r s : G} (hr : r ∈ R) (hs : s ∈ R) (h : r = s) :
    (QV.mk r hr : QV R X) = QV.mk s hs := by subst h; rfl

theorem QV.mk_surjective (v : QV R X) : ∃ r, ∃ hr : r ∈ R, (QV.mk r hr : QV R X) = v := by
  obtain ⟨m, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective (s := X.subgroupOf R) m
  exact ⟨s.1, s.2, rfl⟩

section Mk

variable [Fact (QData0 R X)]

theorem QV.mk_add {r s : G} (hr : r ∈ R) (hs : s ∈ R) (h : r * s ∈ R := R.mul_mem hr hs) :
    (QV.mk (r * s) h : QV R X) = QV.mk r hr + QV.mk s hs := rfl

theorem QV.mk_one (h : (1 : G) ∈ R := R.one_mem) : (QV.mk 1 h : QV R X) = 0 := rfl

theorem QV.mk_inv {r : G} (hr : r ∈ R) (h : r⁻¹ ∈ R := R.inv_mem hr) :
    (QV.mk r⁻¹ h : QV R X) = -QV.mk r hr := rfl

theorem QV.mk_pow {r : G} (hr : r ∈ R) (n : ℕ) (h : r ^ n ∈ R := R.pow_mem hr n) :
    (QV.mk (r ^ n) h : QV R X) = n • QV.mk r hr := rfl

theorem QV.mk_eq_zero_iff {r : G} (hr : r ∈ R) : (QV.mk r hr : QV R X) = 0 ↔ r ∈ X := by
  show Additive.ofMul (show QM R X from QuotientGroup.mk (⟨r, hr⟩ : ↥R)) = Additive.ofMul 1 ↔ _
  rw [Additive.ofMul.injective.eq_iff]
  exact (QuotientGroup.eq_one_iff (N := X.subgroupOf R) (⟨r, hr⟩ : ↥R)).trans
    (Subgroup.mem_subgroupOf)

theorem QV.mk_eq_mk_iff {r s : G} (hr : r ∈ R) (hs : s ∈ R) :
    (QV.mk r hr : QV R X) = QV.mk s hs ↔ r⁻¹ * s ∈ X := by
  rw [← neg_add_eq_zero, ← QV.mk_inv hr, ← QV.mk_add (R.inv_mem hr) hs, QV.mk_eq_zero_iff]

@[expose] def QV.pre (S : AddSubgroup (QV R X)) : Subgroup G where
  carrier := {c | ∃ hc : c ∈ R, (QV.mk c hc : QV R X) ∈ S}
  one_mem' := ⟨R.one_mem, by rw [QV.mk_one]; exact S.zero_mem⟩
  mul_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    exact ⟨R.mul_mem hc hd, by rw [QV.mk_add hc hd]; exact S.add_mem hc' hd'⟩
  inv_mem' := by
    rintro c ⟨hc, hc'⟩
    exact ⟨R.inv_mem hc, by rw [QV.mk_inv hc]; exact S.neg_mem hc'⟩

end Mk

theorem QData.five_of_gen {A B : Subgroup G} (h : QData0 R X) (hA : A ≤ R) (hB : B ≤ R)
    (hR : R = X ⊔ A ⊔ B) (hAp : ∀ a ∈ A, a ^ 5 ∈ X) (hBp : ∀ b ∈ B, b ^ 5 ∈ X) :
    ∀ r ∈ R, r ^ 5 ∈ X := by
  have : Fact (QData0 R X) := ⟨h⟩
  let S : AddSubgroup (QV R X) :=
    { carrier := {v | (5 : ℕ) • v = 0}
      zero_mem' := smul_zero 5
      add_mem' := fun {a b} (ha : (5 : ℕ) • a = 0) (hb : (5 : ℕ) • b = 0) => by
        show (5 : ℕ) • (a + b) = 0
        rw [smul_add, ha, hb, add_zero]
      neg_mem' := fun {a} (ha : (5 : ℕ) • a = 0) => by
        show (5 : ℕ) • (-a) = 0
        rw [smul_neg, ha, neg_zero] }
  have hX : X ≤ QV.pre S := fun x hx => ⟨h.le hx, by
    show (5 : ℕ) • (QV.mk x (h.le hx) : QV R X) = 0
    rw [(QV.mk_eq_zero_iff (h.le hx)).2 hx, smul_zero]⟩
  have hA' : A ≤ QV.pre S := fun a ha => ⟨hA ha, by
    show (5 : ℕ) • (QV.mk a (hA ha) : QV R X) = 0
    rw [← QV.mk_pow (hA ha) 5]
    exact (QV.mk_eq_zero_iff _).2 (hAp a ha)⟩
  have hB' : B ≤ QV.pre S := fun b hb => ⟨hB hb, by
    show (5 : ℕ) • (QV.mk b (hB hb) : QV R X) = 0
    rw [← QV.mk_pow (hB hb) 5]
    exact (QV.mk_eq_zero_iff _).2 (hBp b hb)⟩
  intro r hr
  have hr' : r ∈ X ⊔ A ⊔ B := by rw [← hR]; exact hr
  obtain ⟨_, hr5⟩ := sup_le (sup_le hX hA') hB' hr'
  have hr5' : (5 : ℕ) • (QV.mk r hr : QV R X) = 0 := hr5
  rw [← QV.mk_pow hr 5] at hr5'
  exact (QV.mk_eq_zero_iff _).1 hr5'

theorem QV.five_nsmul [Fact (QData R X)] (v : QV R X) : (5 : ℕ) • v = 0 := by
  obtain ⟨r, hr, rfl⟩ := QV.mk_surjective v
  rw [← QV.mk_pow hr, QV.mk_eq_zero_iff]
  exact (Fact.out : QData R X).five r hr

instance QV.instModule [Fact (QData R X)] : Module (ZMod 5) (QV R X) :=
  AddCommGroup.zmodModule QV.five_nsmul

section Sub

variable [Fact (QData0 R X)]

@[expose] def QV.subAdd (A : Subgroup G) (hA : A ≤ R) : AddSubgroup (QV R X) where
  carrier := {v | ∃ a, ∃ ha : a ∈ A, (QV.mk a (hA ha) : QV R X) = v}
  zero_mem' := ⟨1, A.one_mem, QV.mk_one _⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, A.mul_mem ha hb, QV.mk_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, QV.mk_inv _ _⟩

theorem QV.subAdd_le_iff {A : Subgroup G} (hA : A ≤ R) {S : AddSubgroup (QV R X)} :
    QV.subAdd A hA ≤ S ↔ A ≤ QV.pre S :=
  ⟨fun h a ha => ⟨hA ha, h ⟨a, ha, rfl⟩⟩, by rintro h _ ⟨a, ha, rfl⟩; exact (h ha).2⟩

end Sub

section SubMod

variable [Fact (QData R X)]

@[expose] def QV.sub (A : Subgroup G) (hA : A ≤ R) : Submodule (ZMod 5) (QV R X) :=
  AddSubgroup.toZModSubmodule 5 (QV.subAdd A hA)

theorem QV.mem_sub {A : Subgroup G} (hA : A ≤ R) {v : QV R X} :
    v ∈ QV.sub A hA ↔ ∃ a, ∃ ha : a ∈ A, (QV.mk a (hA ha) : QV R X) = v := Iff.rfl

theorem QV.sub_le_iff {A : Subgroup G} (hA : A ≤ R) {T : Submodule (ZMod 5) (QV R X)} :
    QV.sub A hA ≤ T ↔ A ≤ QV.pre T.toAddSubgroup := by
  rw [← QV.subAdd_le_iff hA (S := T.toAddSubgroup)]
  exact Iff.rfl

theorem QV.sub_sup {A B : Subgroup G} (hA : A ≤ R) (hB : B ≤ R)
    (hAB : A ⊔ B ≤ R := sup_le hA hB) :
    QV.sub (X := X) (A ⊔ B) hAB = QV.sub A hA ⊔ QV.sub B hB := by
  apply le_antisymm
  · rw [QV.sub_le_iff]
    exact sup_le ((QV.sub_le_iff hA).1 le_sup_left) ((QV.sub_le_iff hB).1 le_sup_right)
  · refine sup_le ?_ ?_
    · rw [QV.sub_le_iff]; exact fun a ha => ⟨hA ha, ⟨a, Subgroup.mem_sup_left ha, rfl⟩⟩
    · rw [QV.sub_le_iff]; exact fun a ha => ⟨hB ha, ⟨a, Subgroup.mem_sup_right ha, rfl⟩⟩

theorem QV.sub_top : QV.sub (X := X) R le_rfl = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨r, hr, rfl⟩ := QV.mk_surjective v
  exact ⟨r, hr, rfl⟩

theorem QV.sub_disjoint {A B : Subgroup G} (hA : A ≤ R) (hB : B ≤ R)
    (h : (A ⊔ X) ⊓ (B ⊔ X) ≤ X) : Disjoint (QV.sub (X := X) A hA) (QV.sub B hB) := by
  rw [Submodule.disjoint_def]
  intro v hvA hvB
  obtain ⟨a, ha, rfl⟩ := (QV.mem_sub hA).1 hvA
  obtain ⟨b, hb, hab⟩ := (QV.mem_sub hB).1 hvB
  have hx : b⁻¹ * a ∈ X := (QV.mk_eq_mk_iff (hB hb) (hA ha)).1 hab
  have haB : a ∈ B ⊔ X := by
    have e : a = b * (b⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hx)
  exact (QV.mk_eq_zero_iff (hA ha)).2 (h ⟨Subgroup.mem_sup_left ha, haB⟩)

theorem QV.finrank_sub {A : Subgroup G} (hA : A ≤ R) (hAX : A ⊓ X = ⊥) (hcard : Nat.card A = 5) :
    Module.finrank (ZMod 5) (QV.sub (X := X) A hA) = 1 := by
  let φ : A → QV.sub (X := X) A hA := fun a => ⟨QV.mk a (hA a.2), a, a.2, rfl⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have hab' : (QV.mk (a : G) (hA a.2) : QV R X) = QV.mk (b : G) (hA b.2) :=
      congrArg Subtype.val hab
    have hx : (a : G)⁻¹ * b ∈ X := (QV.mk_eq_mk_iff (hA a.2) (hA b.2)).1 hab'
    have h1 : (a : G)⁻¹ * b ∈ A ⊓ X := ⟨A.mul_mem (A.inv_mem a.2) b.2, hx⟩
    rw [hAX, Subgroup.mem_bot] at h1
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hfinA : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfin : Finite (QV.sub (X := X) A hA) := Finite.of_surjective φ hsurj
  have hc : Nat.card (QV.sub (X := X) A hA) = 5 :=
    (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm.trans hcard
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := QV.sub (X := X) A hA)
  rw [hc, Nat.card_zmod] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) (h.symm.trans (pow_one 5).symm)

end SubMod

theorem QV.conj_mem (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) {r : G} (hr : r ∈ R) :
    (g : G) * r * (g : G)⁻¹ ∈ R := (g.2.1 r).1 hr

@[expose] def QV.conjR (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) : MulAut ↥R :=
  Subgroup.normalizerMonoidHom R ⟨g.1, g.2.1⟩

theorem QV.conjR_map (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) :
    (X.subgroupOf R).map (QV.conjR g).toMonoidHom = X.subgroupOf R := by
  ext s
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact (g.2.2 _).1 ht
  · intro hs
    rw [Subgroup.mem_subgroupOf] at hs
    refine ⟨⟨(g : G)⁻¹ * s * (g : G), (mem_set_normalizer_iff''.1 g.2.1 _).1 s.2⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (mem_set_normalizer_iff''.1 g.2.2 _).1 hs
    · ext
      show (g : G) * ((g : G)⁻¹ * s * (g : G)) * (g : G)⁻¹ = s
      group

section Act

variable [Fact (QData R X)]

@[expose] def QV.actEquiv (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) :
    QV R X ≃ₗ[ZMod 5] QV R X :=
  AddEquiv.toLinearEquiv
    (MulEquiv.toAdditive
      (QuotientGroup.congr (X.subgroupOf R) (X.subgroupOf R) (QV.conjR g) (QV.conjR_map g)))
    (fun c x => ZMod.map_smul _ c x)

theorem QV.actEquiv_mk (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) {r : G}
    (hr : r ∈ R) {s : G} (hs : s ∈ R) (h : s = (g : G) * r * (g : G)⁻¹) :
    QV.actEquiv g (QV.mk r hr) = (QV.mk s hs : QV R X) := by
  subst h; rfl

theorem QV.actEquiv_mk' (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) {r : G}
    (hr : r ∈ R) :
    QV.actEquiv g (QV.mk r hr) = (QV.mk ((g : G) * r * (g : G)⁻¹) (QV.conj_mem g hr) : QV R X) :=
  QV.actEquiv_mk g hr _ rfl

@[expose] def QV.actHom :
    ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G)) →* (QV R X ≃ₗ[ZMod 5] QV R X) where
  toFun := QV.actEquiv
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨r, hr, rfl⟩ := QV.mk_surjective v
    exact QV.actEquiv_mk 1 hr hr (by simp)
  map_mul' g h := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨r, hr, rfl⟩ := QV.mk_surjective v
    show QV.actEquiv (g * h) (QV.mk r hr) = QV.actEquiv g (QV.actEquiv h (QV.mk r hr))
    rw [QV.actEquiv_mk' h hr, QV.actEquiv_mk' g (QV.conj_mem h hr), QV.actEquiv_mk' (g * h) hr]
    exact QV.mk_congr _ _ (by simp [mul_assoc])

theorem QV.actHom_mk (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) {r : G}
    (hr : r ∈ R) {s : G} (hs : s ∈ R) (h : s = (g : G) * r * (g : G)⁻¹) :
    QV.actHom g (QV.mk r hr) = (QV.mk s hs : QV R X) := QV.actEquiv_mk g hr hs h

theorem QV.actHom_mk' (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G))) {r : G}
    (hr : r ∈ R) :
    QV.actHom g (QV.mk r hr) = (QV.mk ((g : G) * r * (g : G)⁻¹) (QV.conj_mem g hr) : QV R X) :=
  QV.actEquiv_mk g hr _ rfl

theorem QV.sub_map_act (g : ↥(normalizer (R : Set G) ⊓ normalizer (X : Set G)))
    {A : Subgroup G} (hA : A ≤ R) (hA' : A.map (MulAut.conj (g : G)).toMonoidHom ≤ R) :
    (QV.sub A hA).map (QV.actHom g).toLinearMap =
      QV.sub (A.map (MulAut.conj (g : G)).toMonoidHom) hA' := by
  ext v
  rw [Submodule.mem_map, QV.mem_sub]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (QV.mem_sub hA).1 hu
    refine ⟨(g : G) * a * (g : G)⁻¹, ⟨a, ha, by simp⟩, ?_⟩
    exact (QV.actHom_mk g (hA ha) _ rfl).symm
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    exact ⟨QV.mk a (hA ha), ⟨a, ha, rfl⟩, QV.actHom_mk g (hA ha) (hA' hb) (by simp)⟩

end Act

end CFSG.GH74.GLS.LU.Local.Five
