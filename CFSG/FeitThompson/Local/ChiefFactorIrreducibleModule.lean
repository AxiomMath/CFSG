module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Field.ZMod
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
public import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

section Factor

variable (X Y : Subgroup G) [Y.Normal]

def quotientFactor : Subgroup (G ⧸ Y) := X.map (QuotientGroup.mk' Y)

instance quotientFactor_normal [X.Normal] : (quotientFactor X Y).Normal := by
  unfold quotientFactor; infer_instance

theorem mem_quotientFactor {q : G ⧸ Y} : q ∈ quotientFactor X Y ↔ ∃ x ∈ X, (x : G ⧸ Y) = q := by
  simp [quotientFactor, Subgroup.mem_map]

theorem mk_mem_quotientFactor {x : G} (hx : x ∈ X) : (x : G ⧸ Y) ∈ quotientFactor X Y :=
  (mem_quotientFactor X Y).2 ⟨x, hx, rfl⟩

theorem map_mk'_eq_quotientFactor : X.map (QuotientGroup.mk' Y) = quotientFactor X Y := (rfl)

theorem comap_mk'_quotientFactor (hYX : Y ≤ X) :
    (quotientFactor X Y).comap (QuotientGroup.mk' Y) = X := by
  rw [quotientFactor, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hYX]

theorem ker_mk'_comp_subtype_eq_subgroupOf :
    ((QuotientGroup.mk' Y).comp X.subtype).ker = Y.subgroupOf X := by
  ext x
  simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem range_mk'_comp_subtype_eq_quotientFactor :
    ((QuotientGroup.mk' Y).comp X.subtype).range = quotientFactor X Y := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, quotientFactor]

noncomputable def quotientFactorMulEquiv : (↥X ⧸ Y.subgroupOf X) ≃* ↥(quotientFactor X Y) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk'_comp_subtype_eq_subgroupOf X Y).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (range_mk'_comp_subtype_eq_quotientFactor X Y)))

instance [Group.IsSolvable G] : Group.IsSolvable ↥(quotientFactor X Y) :=
  haveI : Group.IsSolvable ↥X := isSolvable_of_le (le_top : X ≤ ⊤)
  isSolvable_map (QuotientGroup.mk' Y) X

theorem quotientFactor_ne_bot (h : Y < X) : quotientFactor X Y ≠ ⊥ := by
  obtain ⟨x, hxX, hxY⟩ := SetLike.exists_of_lt h
  intro hc
  have hx : (x : G ⧸ Y) ∈ quotientFactor X Y := mk_mem_quotientFactor X Y hxX
  rw [hc, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hx
  exact hxY hx

theorem nontrivial_quotientFactor (h : Y < X) : Nontrivial ↥(quotientFactor X Y) :=
  (Subgroup.nontrivial_iff_ne_bot _).2 (quotientFactor_ne_bot X Y h)

theorem eq_bot_of_normal_lt_quotientFactor (h : IsChiefFactor X Y) (K : Subgroup (G ⧸ Y))
    (hK : K.Normal) (hKlt : K < quotientFactor X Y) : K = ⊥ := by
  have hYle : Y ≤ K.comap (QuotientGroup.mk' Y) := by
    intro y hy
    simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [show ((y : G ⧸ Y)) = 1 from (QuotientGroup.eq_one_iff y).2 hy]
    exact one_mem _
  have hXle : K.comap (QuotientGroup.mk' Y) ≤ X :=
    (Subgroup.comap_mono hKlt.le).trans_eq (comap_mk'_quotientFactor X Y h.le)
  have hnormal : (K.comap (QuotientGroup.mk' Y)).Normal := hK.comap _
  rcases h.eq_or_eq hnormal hYle hXle with he | he
  · have hmap := congrArg (Subgroup.map (QuotientGroup.mk' Y)) he
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y),
      show Y.map (QuotientGroup.mk' Y) = ⊥ by simp] at hmap
  · exfalso
    have hmap := congrArg (Subgroup.map (QuotientGroup.mk' Y)) he
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y),
      map_mk'_eq_quotientFactor] at hmap
    exact absurd hmap hKlt.ne

variable [X.Normal]

def quotientFactorConj : G →* MulAut ↥(quotientFactor X Y) :=
  (MulAut.conjNormal (H := quotientFactor X Y)).comp (QuotientGroup.mk' Y)

@[simp] theorem coe_quotientFactorConj_apply (g : G) (q : ↥(quotientFactor X Y)) :
    ((quotientFactorConj X Y g q : ↥(quotientFactor X Y)) : G ⧸ Y)
      = (g : G ⧸ Y) * (q : G ⧸ Y) * (g : G ⧸ Y)⁻¹ := by
  simp [quotientFactorConj, MulAut.conjNormal_apply]

theorem coe_quotientFactorConj_apply_mk (g x : G) (hx : x ∈ X) :
    ((quotientFactorConj X Y g ⟨(x : G ⧸ Y), mk_mem_quotientFactor X Y hx⟩ :
        ↥(quotientFactor X Y)) : G ⧸ Y) = ((g * x * g⁻¹ : G) : G ⧸ Y) := by
  simp

theorem eq_bot_or_eq_top_of_quotientFactorConj_invariant (h : IsChiefFactor X Y)
    (S : Subgroup ↥(quotientFactor X Y))
    (hS : ∀ (g : G) (q : ↥(quotientFactor X Y)), q ∈ S → quotientFactorConj X Y g q ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have hTnormal : (S.map (quotientFactor X Y).subtype).Normal := by
    constructor
    intro n hn q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Y q
    obtain ⟨s, hs, rfl⟩ := hn
    exact ⟨quotientFactorConj X Y g s, hS g s hs, by simp⟩
  have hTle : S.map (quotientFactor X Y).subtype ≤ quotientFactor X Y := Subgroup.map_subtype_le S
  rcases eq_or_lt_of_le hTle with hT | hT
  · right
    rw [← Subgroup.map_subtype_inj, ← MonoidHom.range_eq_map, Subgroup.subtype_range, hT]
  · left
    refine (Subgroup.map_eq_bot_iff_of_injective S (quotientFactor X Y).subtype_injective).1 ?_
    exact eq_bot_of_normal_lt_quotientFactor X Y h _ hTnormal hT

end Factor

section OfMulAut

variable {M : Type*} [Monoid M] {A : Type*} [Group A] {V : Type*} [AddCommGroup V]

noncomputable def representationOfMulAut (r : ℕ) [Module (ZMod r) V] (σ : M →* MulAut A)
    (e : A ≃* Multiplicative V) : Representation (ZMod r) M V where
  toFun g := AddMonoidHom.toZModLinearMap r
    { toFun := fun v => Multiplicative.toAdd (e (σ g (e.symm (Multiplicative.ofAdd v))))
      map_zero' := by simp
      map_add' := fun a b => by simp only [ofAdd_add, map_mul, toAdd_mul] }
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

variable (r : ℕ) [Module (ZMod r) V] (σ : M →* MulAut A) (e : A ≃* Multiplicative V)

theorem representationOfMulAut_apply (m : M) (v : V) :
    representationOfMulAut r σ e m v
      = Multiplicative.toAdd (e (σ m (e.symm (Multiplicative.ofAdd v)))) := (rfl)

theorem representationOfMulAut_apply_toAdd (m : M) (a : A) :
    representationOfMulAut r σ e m (Multiplicative.toAdd (e a))
      = Multiplicative.toAdd (e (σ m a)) := by
  rw [representationOfMulAut_apply]; simp

def subgroupOfSubmodule (W : Submodule (ZMod r) V) : Subgroup A where
  carrier := {a | Multiplicative.toAdd (e a) ∈ W}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simpa using W.add_mem ha hb
  inv_mem' := by intro a ha; simpa using W.neg_mem ha

@[simp] theorem mem_subgroupOfSubmodule (W : Submodule (ZMod r) V) (a : A) :
    a ∈ subgroupOfSubmodule r e W ↔ Multiplicative.toAdd (e a) ∈ W := (Iff.rfl)

theorem isIrreducible_of_forall_submodule_eq_bot_or_eq_top {k W : Type*} [Field k]
    [AddCommGroup W] [Module k W] (ρ : Representation k M W) [Nontrivial W]
    (h : ∀ U : Submodule k W, (∀ (g : M), ∀ w ∈ U, ρ g w ∈ U) → U = ⊥ ∨ U = ⊤) :
    ρ.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hc
    have h2 : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule := by
      rw [hc]
    simp only [show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl,
      show (⊤ : Subrepresentation ρ).toSubmodule = ⊤ from rfl] at h2
    exact absurd h2 bot_ne_top
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbt⟩
  refine ⟨fun U => ?_⟩
  rcases h U.toSubmodule (fun g w hw => U.apply_mem_toSubmodule g hw) with hU | hU
  · left; exact Subrepresentation.ext (by rw [hU]; rfl)
  · right; exact Subrepresentation.ext (by rw [hU]; rfl)

theorem isIrreducible_representationOfMulAut [Fact r.Prime] [Nontrivial A]
    (hmin : ∀ S : Subgroup A, (∀ (m : M) (a : A), a ∈ S → σ m a ∈ S) → S = ⊥ ∨ S = ⊤) :
    (representationOfMulAut r σ e).IsIrreducible := by
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : A)
  have hnt : Nontrivial V := by
    refine ⟨Multiplicative.toAdd (e a₀), 0, fun hc => ha₀ ?_⟩
    simpa using e.injective (by simpa using congrArg Multiplicative.ofAdd hc)
  refine isIrreducible_of_forall_submodule_eq_bot_or_eq_top _ (fun W hW => ?_)
  have hinv : ∀ (m : M) (a : A),
      a ∈ subgroupOfSubmodule r e W → σ m a ∈ subgroupOfSubmodule r e W := by
    intro m a ha
    rw [mem_subgroupOfSubmodule] at ha ⊢
    simpa [representationOfMulAut_apply_toAdd] using hW m _ ha
  rcases hmin (subgroupOfSubmodule r e W) hinv with hS | hS
  · left
    refine (Submodule.eq_bot_iff W).2 fun v hv => ?_
    have hm : e.symm (Multiplicative.ofAdd v) ∈ subgroupOfSubmodule r e W := by simpa using hv
    rw [hS, Subgroup.mem_bot] at hm
    simpa using congrArg (fun x => Multiplicative.toAdd (e x)) hm
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have hm : e.symm (Multiplicative.ofAdd v) ∈ subgroupOfSubmodule r e W :=
      hS ▸ Subgroup.mem_top _
    simpa using hm

end OfMulAut

section Main

variable (X Y : Subgroup G) [X.Normal] [Y.Normal]

theorem isIrreducible_representationOfFactorConjAut (h : IsChiefFactor X Y) {r d : ℕ}
    (hr : r.Prime) (e : ↥(quotientFactor X Y) ≃* Multiplicative (Fin d → ZMod r)) :
    letI := Fact.mk hr
    (representationOfMulAut r (quotientFactorConj X Y) e).IsIrreducible := by
  let _ := Fact.mk hr
  have : Nontrivial ↥(quotientFactor X Y) := nontrivial_quotientFactor X Y h.lt
  exact isIrreducible_representationOfMulAut r _ e
    (eq_bot_or_eq_top_of_quotientFactorConj_invariant X Y h)

theorem exists_prime_mulEquiv_isIrreducible_of_isChiefFactor [Finite G] [Group.IsSolvable G]
    (h : IsChiefFactor X Y) :
    ∃ (r d : ℕ) (hr : r.Prime) (_ : 1 ≤ d)
      (e : ↥(quotientFactor X Y) ≃* Multiplicative (Fin d → ZMod r)),
      letI := Fact.mk hr
      (representationOfMulAut r (quotientFactorConj X Y) e).IsIrreducible := by
  obtain ⟨r, d, hr, hd, ⟨e⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot
      (quotientFactor_ne_bot X Y h.lt)
      (fun K hK hKlt => eq_bot_of_normal_lt_quotientFactor X Y h K hK hKlt)
  exact ⟨r, d, hr, hd, e, isIrreducible_representationOfFactorConjAut X Y h hr e⟩

variable {L : Subgroup G}

theorem le_ker_quotientFactorConj (hLX : ⁅L, X⁆ ≤ Y) : L ≤ (quotientFactorConj X Y).ker := by
  intro l hl
  rw [MonoidHom.mem_ker]
  ext q
  obtain ⟨x, hx, hxq⟩ := (mem_quotientFactor X Y).1 q.2
  have hmem : ((l * x * l⁻¹ : G) : G ⧸ Y) = (x : G ⧸ Y) := by
    rw [QuotientGroup.eq_iff_div_mem]
    have hc := Subgroup.commutator_mem_commutator hl hx
    rw [commutatorElement_def] at hc
    have hrw : (l * x * l⁻¹ : G) / x = l * x * l⁻¹ * x⁻¹ := by rw [div_eq_mul_inv]
    exact hrw ▸ hLX hc
  change ((quotientFactorConj X Y l q : ↥(quotientFactor X Y)) : G ⧸ Y)
    = ((q : ↥(quotientFactor X Y)) : G ⧸ Y)
  rw [coe_quotientFactorConj_apply, ← hxq]
  calc ((l : G ⧸ Y)) * (x : G ⧸ Y) * ((l : G ⧸ Y))⁻¹
      = ((l * x * l⁻¹ : G) : G ⧸ Y) := by simp
    _ = (x : G ⧸ Y) := hmem

variable [L.Normal]

def quotientFactorConjAut (hLX : ⁅L, X⁆ ≤ Y) : G ⧸ L →* MulAut ↥(quotientFactor X Y) :=
  QuotientGroup.lift L (quotientFactorConj X Y) (le_ker_quotientFactorConj X Y hLX)

@[simp] theorem quotientFactorConjAut_mk (hLX : ⁅L, X⁆ ≤ Y) (g : G) :
    quotientFactorConjAut X Y hLX (g : G ⧸ L) = quotientFactorConj X Y g := (rfl)

theorem isIrreducible_representationOfQuotientFactorConjAut (h : IsChiefFactor X Y)
    (hLX : ⁅L, X⁆ ≤ Y) {r d : ℕ} (hr : r.Prime)
    (e : ↥(quotientFactor X Y) ≃* Multiplicative (Fin d → ZMod r)) :
    letI := Fact.mk hr
    (representationOfMulAut r (quotientFactorConjAut X Y hLX) e).IsIrreducible := by
  let _ := Fact.mk hr
  have : Nontrivial ↥(quotientFactor X Y) := nontrivial_quotientFactor X Y h.lt
  refine isIrreducible_representationOfMulAut r _ e (fun S hS => ?_)
  refine eq_bot_or_eq_top_of_quotientFactorConj_invariant X Y h S (fun g q hq => ?_)
  simpa using hS (g : G ⧸ L) q hq

theorem exists_prime_mulEquiv_isIrreducible_quotient_of_isChiefFactor [Finite G]
    [Group.IsSolvable G] (h : IsChiefFactor X Y) (hLX : ⁅L, X⁆ ≤ Y) :
    ∃ (r d : ℕ) (hr : r.Prime) (_ : 1 ≤ d)
      (e : ↥(quotientFactor X Y) ≃* Multiplicative (Fin d → ZMod r)),
      letI := Fact.mk hr
      (representationOfMulAut r (quotientFactorConjAut X Y hLX) e).IsIrreducible := by
  obtain ⟨r, d, hr, hd, ⟨e⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot
      (quotientFactor_ne_bot X Y h.lt)
      (fun K hK hKlt => eq_bot_of_normal_lt_quotientFactor X Y h K hK hKlt)
  exact ⟨r, d, hr, hd, e,
    isIrreducible_representationOfQuotientFactorConjAut X Y h hLX hr e⟩

end Main

end CFSG.FeitThompson
