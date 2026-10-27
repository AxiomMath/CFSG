module

public import CFSG.GH74.QTGen4.Recog.Ku.HStructC
public import CFSG.GH74.QTGen4.Recog.Ku.HStructH

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjP {P : Subgroup G} {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G)) :
    ↥P →* ↥P where
  toFun p := ⟨g * p * g⁻¹, (Subgroup.mem_normalizer_iff.mp hN p).mp p.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjP_mem_center {P : Subgroup G} {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G))
    {c : ↥P} (hc : c ∈ Subgroup.center ↥P) : conjP hN c ∈ Subgroup.center ↥P := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  have hy : g⁻¹ * (y : G) * g⁻¹⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hN) y).mp y.2
  have e : (g⁻¹ * (y : G) * g⁻¹⁻¹) * (c : G) = (c : G) * (g⁻¹ * (y : G) * g⁻¹⁻¹) :=
    congrArg Subtype.val (hc ⟨_, hy⟩)
  apply Subtype.ext
  change (y : G) * (g * (c : G) * g⁻¹) = (g * (c : G) * g⁻¹) * (y : G)
  calc (y : G) * (g * (c : G) * g⁻¹)
      = g * ((g⁻¹ * (y : G) * g⁻¹⁻¹) * (c : G)) * g⁻¹ := by group
    _ = g * ((c : G) * (g⁻¹ * (y : G) * g⁻¹⁻¹)) * g⁻¹ := by rw [e]
    _ = (g * (c : G) * g⁻¹) * (y : G) := by group

@[expose] noncomputable def actQ {P : Subgroup G} {g : G}
    (hN : g ∈ Subgroup.normalizer (P : Set G)) :
    ↥P ⧸ Subgroup.center ↥P →* ↥P ⧸ Subgroup.center ↥P :=
  QuotientGroup.map _ _ (conjP hN) (by
    intro c hc
    exact conjP_mem_center hN hc)

section Vec

attribute [local instance] IsMulCommutative.instCommGroup

variable {P : Subgroup G}

@[expose] noncomputable def actV [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]
    {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G)) :
    Additive (↥P ⧸ Subgroup.center ↥P) →ₗ[ZMod 2] Additive (↥P ⧸ Subgroup.center ↥P) :=
  AddMonoidHom.toZModLinearMap 2 (actQ hN).toAdditive

section Lemmas

variable [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]

theorem actV_mk {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G)) (q : ↥P) :
    actV hN (Additive.ofMul (QuotientGroup.mk q : ↥P ⧸ Subgroup.center ↥P)) =
      Additive.ofMul (QuotientGroup.mk (conjP hN q) : ↥P ⧸ Subgroup.center ↥P) :=
  rfl

theorem actV_mul {g g' : G} (hN : g ∈ Subgroup.normalizer (P : Set G))
    (hN' : g' ∈ Subgroup.normalizer (P : Set G)) (v : Additive (↥P ⧸ Subgroup.center ↥P)) :
    actV (mul_mem hN hN') v = actV hN (actV hN' v) := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : Additive.ofMul (QuotientGroup.mk q : ↥P ⧸ Subgroup.center ↥P) = v :=
    congrArg Additive.ofMul hq
  have e : conjP (mul_mem hN hN') q = conjP hN (conjP hN' q) :=
    Subtype.ext (by
      show g * g' * (q : G) * (g * g')⁻¹ = g * (g' * (q : G) * g'⁻¹) * g⁻¹
      group)
  rw [← hv, actV_mk, actV_mk, actV_mk, e]

end Lemmas

end Vec

section Psi

variable {G : Type} [Group G] {P : Subgroup G}

@[expose] noncomputable def psi (p : ↥P) : Additive (↥P ⧸ Subgroup.center ↥P) :=
  Additive.ofMul (QuotientGroup.mk p : ↥P ⧸ Subgroup.center ↥P)

theorem psi_mul (p q : ↥P) : psi (p * q) = psi p + psi q := rfl

theorem psi_eq_zero_iff (p : ↥P) : psi p = 0 ↔ p ∈ Subgroup.center ↥P := by
  unfold psi
  rw [← QuotientGroup.eq_one_iff]
  rfl

end Psi

section Comm

attribute [local instance] IsMulCommutative.instCommGroup

variable {G : Type} [Group G] {P : Subgroup G} {u b : G}
variable [CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P)]

theorem psi_comm_eq (hN : u ∈ Subgroup.normalizer (P : Set G)) (a w : ↥P)
    (hw : (w : G) = (a : G) * u * (a : G)⁻¹ * u⁻¹) :
    psi w = psi a + actV hN (psi a) := by
  have e : w = a * conjP hN a⁻¹ := Subtype.ext (by
    rw [hw, Subgroup.coe_mul]
    show _ = (a : G) * (u * ((a⁻¹ : ↥P) : G) * u⁻¹)
    rw [Subgroup.coe_inv]
    group)
  have h0 : psi a + psi a⁻¹ = 0 := by
    rw [← psi_mul, mul_inv_cancel]
    rfl
  have hneg : psi a⁻¹ = -psi a := eq_neg_of_add_eq_zero_right h0
  have hdef : psi (conjP hN a⁻¹) = actV hN (psi a⁻¹) := (actV_mk hN a⁻¹).symm
  have hv : -actV hN (psi a) = actV hN (psi a) :=
    (eq_neg_of_add_eq_zero_right (add_self_eq_zero_V (actV hN (psi a)))).symm
  rw [e, psi_mul, hdef, hneg, map_neg, hv]

theorem actV_eq_id_of_mem {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G)) (hgP : g ∈ P) :
    actV hN = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : Additive.ofMul (QuotientGroup.mk q : ↥P ⧸ Subgroup.center ↥P) = v :=
    congrArg Additive.ofMul hq
  rw [← hv, actV_mk, LinearMap.id_apply]
  congr 1
  have e : conjP hN q = (⟨g, hgP⟩ : ↥P) * q * (⟨g, hgP⟩ : ↥P)⁻¹ := Subtype.ext rfl
  rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    mul_inv_eq_iff_eq_mul]
  exact mul_comm _ _

theorem actV_eq_of_mul_mem (hb : b ∈ Subgroup.normalizer (P : Set G))
    (hu : u ∈ Subgroup.normalizer (P : Set G)) (hbu : b * u ∈ P) (huu : u * u ∈ P) :
    actV hb = actV hu := by
  have h1 : actV (mul_mem hb hu) = LinearMap.id := actV_eq_id_of_mem _ hbu
  have h2 : actV (mul_mem hu hu) = LinearMap.id := actV_eq_id_of_mem _ huu
  refine LinearMap.ext fun v => ?_
  have hv : actV hu (actV hu v) = v := by
    rw [← actV_mul hu hu, h2]
    rfl
  calc actV hb v = actV hb (actV hu (actV hu v)) := by rw [hv]
    _ = actV (mul_mem hb hu) (actV hu v) := by rw [actV_mul hb hu]
    _ = actV hu v := by rw [h1]; rfl

theorem psi_comm_mem_range (hb : b ∈ Subgroup.normalizer (P : Set G))
    (hcase : b ∈ P ∨ b * u ∈ P) (hu : u ∈ Subgroup.normalizer (P : Set G))
    (huu : u * u ∈ P) (a w : ↥P) (hw : (w : G) = (a : G) * b * (a : G)⁻¹ * b⁻¹) :
    psi w ∈ LinearMap.range (kuDeltaLin (actV hu)) := by
  rw [psi_comm_eq hb a w hw]
  rcases hcase with hbP | hbu
  · rw [actV_eq_id_of_mem hb hbP, LinearMap.id_apply, add_self_eq_zero_V]
    exact zero_mem _
  · rw [actV_eq_of_mul_mem hb hu hbu huu]
    exact ⟨psi a, rfl⟩

theorem psi_inv (p : ↥P) : psi p⁻¹ = -psi p :=
  eq_neg_of_add_eq_zero_right (by rw [← psi_mul, mul_inv_cancel]; rfl)

theorem actV_eq_id_of_eq_one {g : G} (hN : g ∈ Subgroup.normalizer (P : Set G)) (hg : g = 1) :
    actV hN = LinearMap.id := by
  subst hg
  exact actV_eq_id_of_mem hN P.one_mem

theorem actV_involutive {u : G} (hu : u ∈ Subgroup.normalizer (P : Set G))
    (huu : u * u ∈ P) (v : Additive (↥P ⧸ Subgroup.center ↥P)) :
    actV hu (actV hu v) = v := by
  rw [← actV_mul hu hu, actV_eq_id_of_mem _ huu]
  rfl

@[expose] def psiPre (R : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P))) :
    Subgroup G where
  carrier := {g | ∃ hg : g ∈ P, psi (⟨g, hg⟩ : ↥P) ∈ R}
  mul_mem' := by
    rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
    refine ⟨P.mul_mem ha hb, ?_⟩
    show psi (⟨a, ha⟩ * ⟨b, hb⟩ : ↥P) ∈ R
    rw [psi_mul]
    exact R.add_mem hpa hpb
  one_mem' := ⟨P.one_mem, by
    show psi (1 : ↥P) ∈ R
    have : psi (1 : ↥P) = 0 := rfl
    rw [this]
    exact R.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, hpa⟩
    refine ⟨P.inv_mem ha, ?_⟩
    show psi (⟨a, ha⟩ : ↥P)⁻¹ ∈ R
    rw [psi_inv]
    exact R.neg_mem hpa

theorem mem_psiPre_iff {R : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P))} {g : G} :
    g ∈ psiPre R ↔ ∃ hg : g ∈ P, psi (⟨g, hg⟩ : ↥P) ∈ R :=
  Iff.rfl

noncomputable def psiHom (R : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P))) :
    psiPre R →* Multiplicative R where
  toFun k := Multiplicative.ofAdd ⟨psi (⟨k.1, (mem_psiPre_iff.mp k.2).1⟩ : ↥P),
    (mem_psiPre_iff.mp k.2).2⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show psi (1 : ↥P) = 0
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact psi_mul (⟨(a : G), (mem_psiPre_iff.mp a.2).1⟩ : ↥P)
      (⟨(b : G), (mem_psiPre_iff.mp b.2).1⟩ : ↥P)

theorem psiHom_apply_eq_zero_iff {R : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P))}
    (k : psiPre R) :
    psiHom R k = 1 ↔ (⟨k.1, (mem_psiPre_iff.mp k.2).1⟩ : ↥P) ∈ Subgroup.center ↥P := by
  constructor
  · intro h
    have h' : psi (⟨k.1, (mem_psiPre_iff.mp k.2).1⟩ : ↥P) = 0 := by
      have h2 : (psiHom R k).toAdd = 0 := by rw [h]; rfl
      exact congrArg Subtype.val h2
    exact (psi_eq_zero_iff (⟨k.1, (mem_psiPre_iff.mp k.2).1⟩ : ↥P)).mp h'
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show psi (⟨k.1, (mem_psiPre_iff.mp k.2).1⟩ : ↥P) = 0
    exact (psi_eq_zero_iff (⟨k.1, (mem_psiPre_iff.mp k.2).1⟩ : ↥P)).mpr h

theorem psiHom_surjective (R : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P))) :
    Function.Surjective (psiHom R) := by
  intro r
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd r).1)
  have hpsi : psi q = (Multiplicative.toAdd r).1 := congrArg Additive.ofMul hq
  have hqR : (q : G) ∈ psiPre R := mem_psiPre_iff.mpr ⟨q.2, by
    show psi (⟨(q : G), q.2⟩ : ↥P) ∈ R
    rw [show (⟨(q : G), q.2⟩ : ↥P) = q from rfl, hpsi]
    exact (Multiplicative.toAdd r).2⟩
  refine ⟨⟨q, hqR⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hpsi

theorem card_psiPre [Finite G] (R : Submodule (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P))) :
    Nat.card (psiPre R) = Nat.card R * Nat.card (Subgroup.center ↥P) := by
  have hcard : Nat.card (psiPre R ⧸ (psiHom R).ker) = Nat.card R := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (psiHom R)
      (psiHom_surjective R)).toEquiv]
    exact (Nat.card_congr (Multiplicative.ofAdd : R ≃ Multiplicative R)).symm
  have hker : Nat.card (psiHom R).ker = Nat.card (Subgroup.center ↥P) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x => (⟨⟨x.1.1, (mem_psiPre_iff.mp x.1.2).1⟩, (psiHom_apply_eq_zero_iff x.1).mp
        (MonoidHom.mem_ker.mp x.2)⟩ : Subgroup.center ↥P)) ⟨?_, ?_⟩)
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have h1 : (x : G) = (y : G) := congrArg (fun c : Subgroup.center ↥P => ((c : ↥P) : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨c, hc⟩
      have hpsi0 : psi c = 0 := (psi_eq_zero_iff c).mpr hc
      have hk : (c : G) ∈ psiPre R := mem_psiPre_iff.mpr ⟨c.2, by
        show psi (⟨(c : G), c.2⟩ : ↥P) ∈ R
        rw [show (⟨(c : G), c.2⟩ : ↥P) = c from rfl, hpsi0]
        exact R.zero_mem⟩
      refine ⟨⟨(⟨c, hk⟩ : psiPre R), ?_⟩, ?_⟩
      · exact MonoidHom.mem_ker.mpr ((psiHom_apply_eq_zero_iff (⟨c, hk⟩ : psiPre R)).mpr hc)
      · rfl
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (psiHom R).ker, hcard, hker]

end Comm

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_comm_eq_z (h : KuHyp G T M H P z) {c : G} (hcP : c ∈ P)
    (hc : c ∉ Subgroup.zpowers z) : ∃ p ∈ P, ⁅p, c⁆ = z := by
  by_contra hno
  set C := h.kuZCore_P with hC
  let c' : ↥P := ⟨c, hcP⟩
  let z' : ↥P := ⟨z, h.zP_mem⟩
  have key : ∀ p : ↥P, ⁅p, c'⁆ = 1 := fun p => by
    rcases C.comm_pair p c' with h1 | h1
    · exact h1
    · exfalso
      exact hno ⟨p.1, p.2, by
        have := congrArg Subtype.val h1
        simpa [commutatorElement_def] using this⟩
  have hcen : c' ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : g * c' * g⁻¹ * c'⁻¹ = 1 := by
      have := key g
      rwa [commutatorElement_def] at this
    have h3 : g * c' * g⁻¹ = c' := mul_inv_eq_one.mp h2
    calc g * c' = (g * c' * g⁻¹) * g := by group
      _ = c' * g := by rw [h3]
  rw [C.center_eq] at hcen
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcen
  apply hc
  refine ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

end KuHyp

end CFSG.GH74.QTGen4.Ku
