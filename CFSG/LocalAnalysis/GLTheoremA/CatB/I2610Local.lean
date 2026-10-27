module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev NL (L : Subgroup G) : Type := ↥(Subgroup.normalizer (L : Set G))

abbrev Lv (L : Subgroup G) : Subgroup (NL L) := L.subgroupOf (Subgroup.normalizer (L : Set G))

abbrev Np (p : ℕ) (L : Subgroup G) : Subgroup (NL L) :=
  (GLAPPrimeCoreOf p L).subgroupOf (Subgroup.normalizer (L : Set G))

abbrev Ev (L E : Subgroup G) : Subgroup (NL L) := E.subgroupOf (Subgroup.normalizer (L : Set G))

theorem mem_Lv {L : Subgroup G} (x : NL L) : x ∈ Lv L ↔ (x : G) ∈ L :=
  Subgroup.mem_subgroupOf

theorem mem_Np {p : ℕ} {L : Subgroup G} (x : NL L) :
    x ∈ Np p L ↔ (x : G) ∈ GLAPPrimeCoreOf p L :=
  Subgroup.mem_subgroupOf

theorem mem_Ev {L E : Subgroup G} (x : NL L) : x ∈ Ev L E ↔ (x : G) ∈ E :=
  Subgroup.mem_subgroupOf

instance Lv.normal (L : Subgroup G) : (Lv L).Normal where
  conj_mem n hn g := by
    rw [mem_Lv] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 g.2 _).1 hn

instance Np.normal (p : ℕ) (L : Subgroup G) : (Np p L).Normal where
  conj_mem n hn g := by
    rw [mem_Np] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L g.2) _).1 hn

theorem Np_conj {p : ℕ} {L : Subgroup G} {n : NL L} (hn : n ∈ Np p L) (g : NL L) :
    g * n * g⁻¹ ∈ Np p L :=
  Subgroup.Normal.conj_mem (Np.normal p L) n hn g

theorem Lv_conj {L : Subgroup G} {n : NL L} (hn : n ∈ Lv L) (g : NL L) :
    g * n * g⁻¹ ∈ Lv L :=
  Subgroup.Normal.conj_mem (Lv.normal L) n hn g

abbrev Gam (p : ℕ) (L : Subgroup G) : Type := NL L ⧸ Np p L

noncomputable abbrev psi (p : ℕ) (L : Subgroup G) : NL L →* Gam p L :=
  QuotientGroup.mk' (Np p L)

theorem L_le_normalizer (L : Subgroup G) : L ≤ Subgroup.normalizer (L : Set G) :=
  Subgroup.le_normalizer

theorem Np_le_Lv (p : ℕ) (L : Subgroup G) : Np p L ≤ Lv L := by
  intro x hx
  rw [mem_Np] at hx
  rw [mem_Lv]
  have hO : GLAPPrimeCoreOf p L ≤ L := by
    show (GLAPPrimeCore p ↥L).map L.subtype ≤ L
    exact Subgroup.map_subtype_le _
  exact hO hx

theorem psi_eq_one_iff {p : ℕ} {L : Subgroup G} (x : NL L) : psi p L x = 1 ↔ x ∈ Np p L := by
  change (QuotientGroup.mk x : Gam p L) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]

theorem coprime_card_Np (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    Nat.Coprime p (Nat.card ↥(Np p L)) := by
  have h1 : Nat.card ↥(Np p L) = Nat.card ↥(GLAPPrimeCoreOf p L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show GLAPPrimeCoreOf p L ≤ Subgroup.normalizer (L : Set G) from
        (show GLAPPrimeCoreOf p L ≤ L from by
          show (GLAPPrimeCore p ↥L).map L.subtype ≤ L
          exact Subgroup.map_subtype_le _).trans (L_le_normalizer L))).toEquiv
  have h2 : Nat.card ↥(GLAPPrimeCoreOf p L) = Nat.card ↥(GLAPPrimeCore p ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [h1, h2]
  exact CFSG.pPrimeCore_coprime_card

theorem psi_comm_iff {p : ℕ} {L : Subgroup G} (e l : NL L) :
    psi p L e * psi p L l = psi p L l * psi p L e ↔ e * l * e⁻¹ * l⁻¹ ∈ Np p L := by
  rw [← map_mul, ← map_mul]
  change (QuotientGroup.mk (e * l) : Gam p L) = QuotientGroup.mk (l * e) ↔ _
  rw [QuotientGroup.eq]
  have key : e * l * e⁻¹ * l⁻¹ = l * (e * ((e * l)⁻¹ * (l * e))⁻¹ * e⁻¹) * l⁻¹ := by group
  constructor
  · intro h
    have h2 : e * ((e * l)⁻¹ * (l * e))⁻¹ * e⁻¹ ∈ Np p L :=
      Np_conj (Subgroup.inv_mem _ h) e
    rw [key]
    exact Np_conj h2 l
  · intro h
    have h2 := Np_conj h l⁻¹
    rw [inv_inv] at h2
    have h3 := Np_conj h2 e⁻¹
    rw [inv_inv] at h3
    have h4 : (e * l)⁻¹ * (l * e) =
        (e⁻¹ * (l⁻¹ * (e * l * e⁻¹ * l⁻¹) * l) * e)⁻¹ := by group
    rw [h4]
    exact Subgroup.inv_mem _ h3

theorem psi_mem_centralizer_iff {p : ℕ} {L : Subgroup G} (e : NL L) :
    psi p L e ∈ Subgroup.centralizer (((Lv L).map (psi p L) : Subgroup (Gam p L)) : Set (Gam p L)) ↔
      ∀ l ∈ L, ⁅l, (e : G)⁆ ∈ GLAPPrimeCoreOf p L := by
  rw [Subgroup.mem_centralizer_iff]
  have hcomm : ∀ x : NL L, x ∈ Lv L →
      (psi p L x * psi p L e = psi p L e * psi p L x ↔ ⁅(x : G), (e : G)⁆ ∈ GLAPPrimeCoreOf p L) := by
    intro x _
    rw [psi_comm_iff]
    constructor
    · intro h
      have hm := (mem_Np _).1 h
      simpa [commutatorElement_def, mul_assoc] using hm
    · intro h
      rw [mem_Np]
      simpa [commutatorElement_def, mul_assoc] using h
  constructor
  · intro h l hl
    have hx : (⟨l, L_le_normalizer L hl⟩ : NL L) ∈ Lv L := (mem_Lv _).2 hl
    have hmem : psi p L (⟨l, L_le_normalizer L hl⟩ : NL L) ∈ ((Lv L).map (psi p L) : Set (Gam p L)) :=
      Subgroup.mem_map_of_mem _ hx
    have h1 := h _ hmem
    exact (hcomm _ hx).1 h1
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_map).1 hy
    exact (hcomm x hx).2 (h (x : G) ((mem_Lv x).1 hx))

abbrev CosetT (p : ℕ) (L : Subgroup G) (l : NL L) : Type := {x : NL L // x ∈ Lv L ∧ x * l⁻¹ ∈ Np p L}

theorem lift_fixed {p : ℕ} (hp : p.Prime) {L : Subgroup G} (E : Subgroup (NL L))
    (hE : IsPGroup p E) (hcop : Nat.Coprime p (Nat.card ↥(Np p L)))
    {l : NL L} (hl : l ∈ Lv L) (hfix : ∀ e ∈ E, e * l * e⁻¹ * l⁻¹ ∈ Np p L) :
    ∃ l' ∈ Lv L, l' * l⁻¹ ∈ Np p L ∧ ∀ e ∈ E, e * l' = l' * e := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmemconj : ∀ e ∈ E, ∀ t : CosetT p L l,
      e * t.1 * e⁻¹ ∈ Lv L ∧ e * t.1 * e⁻¹ * l⁻¹ ∈ Np p L := by
    intro e he t
    refine ⟨Lv_conj t.2.1 e, ?_⟩
    have h1 : e * t.1 * e⁻¹ * l⁻¹ = (e * (t.1 * l⁻¹) * e⁻¹) * (e * l * e⁻¹ * l⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Np_conj t.2.2 e) (hfix e he)
  letI : MulAction E (CosetT p L l) :=
    { smul := fun e t => ⟨(e : NL L) * t.1 * (e : NL L)⁻¹, (hmemconj e e.2 t).1, (hmemconj e e.2 t).2⟩
      one_smul := fun t => Subtype.ext (by
        show ((1 : E) : NL L) * t.1 * ((1 : E) : NL L)⁻¹ = t.1
        simp)
      mul_smul := fun e₁ e₂ t => Subtype.ext (by
        show ((e₁ * e₂ : E) : NL L) * t.1 * ((e₁ * e₂ : E) : NL L)⁻¹ =
          (e₁ : NL L) * ((e₂ : NL L) * t.1 * (e₂ : NL L)⁻¹) * (e₁ : NL L)⁻¹
        simp [mul_assoc]) }
  have hfin : Nat.card (CosetT p L l) = Nat.card ↥(Np p L) := by
    apply Nat.card_congr
    exact
      { toFun := fun t => ⟨t.1 * l⁻¹, t.2.2⟩
        invFun := fun n => ⟨(n : NL L) * l, Subgroup.mul_mem _ (Np_le_Lv p L n.2) hl, by simpa using n.2⟩
        left_inv := fun t => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hndvd : ¬ p ∣ Nat.card (CosetT p L l) := by
    rw [hfin]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop
  have hmod := hE.card_modEq_card_fixedPoints (CosetT p L l)
  have hfix0 : Nat.card (MulAction.fixedPoints E (CosetT p L l)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hndvd ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨x, hx⟩, -⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix0)
  have hfixed : ∀ m : E, m • x = x := MulAction.mem_fixedPoints.1 hx
  refine ⟨x.1, x.2.1, x.2.2, fun e he => ?_⟩
  have h := congrArg Subtype.val (hfixed ⟨e, he⟩)
  change (e : NL L) * x.1 * (e : NL L)⁻¹ = x.1 at h
  calc e * x.1 = (e * x.1 * e⁻¹) * e := by group
    _ = x.1 * e := by rw [h]

theorem map_inf_centralizer_eq {p : ℕ} (hp : p.Prime) {L : Subgroup G} (E : Subgroup (NL L))
    (hE : IsPGroup p E) (hcop : Nat.Coprime p (Nat.card ↥(Np p L))) :
    (Lv L ⊓ Subgroup.centralizer (E : Set (NL L))).map (psi p L) =
      (Lv L).map (psi p L) ⊓
        Subgroup.centralizer ((E.map (psi p L) : Subgroup (Gam p L)) : Set (Gam p L)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxL, hxC⟩, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hxL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hxC e he]
  · rintro ⟨hyK, hyC⟩
    obtain ⟨l, hl, rfl⟩ := (Subgroup.mem_map).1 hyK
    have hfix : ∀ e ∈ E, e * l * e⁻¹ * l⁻¹ ∈ Np p L := by
      intro e he
      have h1 : psi p L e * psi p L l = psi p L l * psi p L e :=
        Subgroup.mem_centralizer_iff.1 hyC (psi p L e) (Subgroup.mem_map_of_mem _ he)
      exact (psi_comm_iff e l).1 h1
    obtain ⟨l', hl', hl'N, hcomm⟩ := lift_fixed hp E hE hcop hl hfix
    refine ⟨l', Subgroup.mem_inf.2 ⟨hl', ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact hcomm e he
    · have h1 : psi p L (l' * l⁻¹) = 1 := (psi_eq_one_iff _).2 hl'N
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.1 h1

theorem card_map_psi {p : ℕ} (hp : p.Prime) {L : Subgroup G} (E : Subgroup (NL L))
    (hE : IsElemAbelian p E) (hcop : Nat.Coprime p (Nat.card ↥(Np p L))) :
    Nat.card ↥(E.map (psi p L)) = Nat.card ↥E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Set.InjOn (psi p L) (E : Set (NL L)) := by
    intro a ha b hb hab
    have h1 : psi p L (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ Np p L := (psi_eq_one_iff _).1 h1
    have h3 : a⁻¹ * b ∈ E := E.mul_mem (E.inv_mem ha) hb
    by_contra hne
    have hne' : a⁻¹ * b ≠ 1 := fun h => hne (inv_mul_eq_one.1 h)
    have hpow : (a⁻¹ * b) ^ p = 1 := hE.2 _ h3
    have hord : orderOf (a⁻¹ * b) = p := orderOf_eq_prime hpow hne'
    have hdvd : orderOf (⟨a⁻¹ * b, h2⟩ : ↥(Np p L)) ∣ Nat.card ↥(Np p L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd
  have himg : (E.map (psi p L) : Set (Gam p L)) = psi p L '' (E : Set (NL L)) :=
    Subgroup.coe_map _ _
  calc Nat.card ↥(E.map (psi p L))
      = Nat.card ((E.map (psi p L) : Subgroup (Gam p L)) : Set (Gam p L)) := rfl
    _ = Nat.card (psi p L '' (E : Set (NL L))) := by rw [himg]
    _ = Nat.card (E : Set (NL L)) := Nat.card_image_of_injOn hinj
    _ = Nat.card ↥E := rfl

theorem isElemAbelian_map_psi {p : ℕ} {L : Subgroup G} {E : Subgroup (NL L)}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map (psi p L)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := (Subgroup.mem_map).1 a.2
    obtain ⟨y, hy, hyb⟩ := (Subgroup.mem_map).1 b.2
    change (a : Gam p L) * (b : Gam p L) = (b : Gam p L) * (a : Gam p L)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, isElemAbelian_commute hE hx hy]
  · intro w hw
    obtain ⟨x, hx, hxw⟩ := (Subgroup.mem_map).1 hw
    rw [← hxw, ← map_pow, hE.2 x hx, map_one]

noncomputable abbrev Kgrp (p : ℕ) (L : Subgroup G) : Subgroup (Gam p L) := (Lv L).map (psi p L)

instance Kgrp.normal (p : ℕ) (L : Subgroup G) : (Kgrp p L).Normal :=
  Subgroup.Normal.map (Lv.normal L) (psi p L) (QuotientGroup.mk'_surjective _)

noncomputable def pQuotEquivK (p : ℕ) (L : Subgroup G) :
    PQuot p L ≃* ↥(Kgrp p L) := by
  let f : ↥L →* Gam p L := (psi p L).comp (Subgroup.inclusion (L_le_normalizer L))
  have hrange : f.range = Kgrp p L := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion (L_le_normalizer L) l, (mem_Lv _).2 l.2, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨(x : NL L).1, (mem_Lv x).1 hx⟩, rfl⟩
  have hker : f.ker = GLAPPrimeCore p ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    change psi p L (Subgroup.inclusion (L_le_normalizer L) l) = 1 ↔ _
    rw [psi_eq_one_iff, mem_Np]
    show (l : G) ∈ (GLAPPrimeCore p ↥L).map L.subtype ↔ _
    exact Subgroup.mem_map_iff_mem L.subtype_injective
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))

noncomputable def quotCenterCongr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)

theorem catalogIs_of_mulEquiv {S S' : Type} [Group S] [Group S'] {Q : TauCeti.CFSGIndex → Prop}
    (e : S ≃* S') (h : catalogIs S Q) : catalogIs S' Q := by
  obtain ⟨i, hi, ⟨e'⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans e'⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
