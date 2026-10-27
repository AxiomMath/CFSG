module

public import CFSG.FeitThompson.Representations.ScalarAxisWeightsMinimumDegreeCount
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarAxis

open SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

def sdpEquivProd {N G : Type*} [Group N] [Group G] (ψ : G →* MulAut N) : (N ⋊[ψ] G) ≃ N × G where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

structure AxisSystem (p q : ℕ) [Fact p.Prime] (V U B : Type u) [AddCommGroup V]
    [Module (ZMod p) V] [Group U] [Group B] where
  scalar : ScalarCoordinateSystem p q V U
  a : ℕ
  one_lt_a : 1 < a
  index_lineCentralizer : ∀ i, (scalar.lineCentralizer i).index = a
  actB : B →* (V ≃ₗ[ZMod p] V)
  autB : B →* MulAut U
  compat : ∀ (g : B) (u : U) (v : V), actB g (scalar.act u v) = scalar.act (autB g u) (actB g v)
  gen : B
  card_B : Nat.card B = q
  mem_zpowers_gen : ∀ x : B, x ∈ Subgroup.zpowers gen
  perm : Equiv.Perm (Fin q)
  isCycle_perm : perm.IsCycle
  support_perm : perm.support = Finset.univ
  map_line_gen : ∀ i, Submodule.map (actB gen : V →ₗ[ZMod p] V) (scalar.line i)
    = scalar.line (perm i)

variable {p q : ℕ} [Fact p.Prime] {V U B : Type u} [AddCommGroup V] [Module (ZMod p) V]
  [Group U] [Group B]

namespace AxisSystem

variable (S : AxisSystem p q V U B)

def mulAutV (g : B) : Multiplicative V ≃* Multiplicative V :=
  AddEquiv.toMultiplicative (S.actB g).toAddEquiv

@[simp] theorem mulAutV_apply (g : B) (v : V) :
    S.mulAutV g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (S.actB g v) := (rfl)

def autCore : B →* MulAut S.scalar.grp where
  toFun g := SemidirectProduct.congr (S.mulAutV g) (S.autB g) (by
    intro u
    refine MulEquiv.ext fun x => ?_
    change S.mulAutV g (S.scalar.mulAutHom u x) = S.scalar.mulAutHom (S.autB g u) (S.mulAutV g x)
    induction x using Multiplicative.rec with
    | _ v => simp [S.compat g u v])
  map_one' := by
    refine MulEquiv.ext fun x => SemidirectProduct.ext ?_ ?_
    · change S.mulAutV 1 x.left = x.left
      induction x.left using Multiplicative.rec with
      | _ v => simp [mulAutV_apply]
    · change S.autB 1 x.right = x.right
      simp
  map_mul' g₁ g₂ := by
    refine MulEquiv.ext fun x => SemidirectProduct.ext ?_ ?_
    · change S.mulAutV (g₁ * g₂) x.left = S.mulAutV g₁ (S.mulAutV g₂ x.left)
      induction x.left using Multiplicative.rec with
      | _ v => simp [mulAutV_apply]
    · change S.autB (g₁ * g₂) x.right = S.autB g₁ (S.autB g₂ x.right)
      simp [MulAut.mul_apply]

theorem autCore_apply_left (g : B) (x : S.scalar.grp) :
    (S.autCore g x).left = S.mulAutV g x.left := (rfl)

theorem autCore_apply_right (g : B) (x : S.scalar.grp) :
    (S.autCore g x).right = S.autB g x.right := (rfl)

abbrev amb : Type u := S.scalar.grp ⋊[S.autCore] B

include S in
theorem finite_module : Finite V := S.scalar.finite_of_finite_line

include S in
theorem finite_complement : Finite B := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [S.card_B]
  have := S.scalar.two_le_q
  omega

variable [Finite U]

instance finite_grp : Finite S.scalar.grp := by
  have h1 : Finite V := S.finite_module
  have h2 : Finite (Multiplicative V) := h1
  exact Finite.of_equiv _ (sdpEquivProd S.scalar.mulAutHom).symm

instance finite_amb : Finite S.amb := by
  have h1 : Finite B := S.finite_complement
  have h2 := S.finite_grp
  exact Finite.of_equiv _ (sdpEquivProd S.autCore).symm

noncomputable instance fintypeAmb : Fintype S.amb := Fintype.ofFinite _

noncomputable instance fintypeBase : Fintype S.scalar.base := Fintype.ofFinite _

def core : Subgroup S.amb := (SemidirectProduct.inl : S.scalar.grp →* S.amb).range

instance core_normal : (S.core).Normal := range_inl_normal

theorem inl_mem_core (x : S.scalar.grp) : (inl x : S.amb) ∈ S.core := ⟨x, rfl⟩

theorem mem_core {z : S.amb} : z ∈ S.core ↔ ∃ x : S.scalar.grp, inl x = z := Iff.rfl

noncomputable def coreMulEquiv : S.scalar.grp ≃* S.core :=
  MonoidHom.ofInjective (f := (SemidirectProduct.inl : S.scalar.grp →* S.amb)) inl_injective

@[simp] theorem coe_coreMulEquiv_apply (x : S.scalar.grp) :
    (S.coreMulEquiv x : S.amb) = inl x := (rfl)

noncomputable def pushChar (θ : S.scalar.grp → ℂ) : S.core → ℂ := θ ∘ S.coreMulEquiv.symm

theorem pushChar_apply (θ : S.scalar.grp → ℂ) (x : S.scalar.grp) :
    S.pushChar θ (S.coreMulEquiv x) = θ x := by
  simp only [pushChar, Function.comp_apply, MulEquiv.symm_apply_apply]

noncomputable def baseCore : Subgroup S.core :=
  Subgroup.map S.coreMulEquiv.toMonoidHom S.scalar.base

noncomputable def commCentralizer : Subgroup U :=
  ⁅S.scalar.totalCentralizer, S.scalar.totalCentralizer⁆

noncomputable def axisIrr : Set (S.scalar.grp → ℂ) :=
  {θ | θ ∈ Irr S.scalar.grp ∧ (∀ u ∈ commutator U, θ (inr u) = θ 1) ∧
    ∃ lam ∈ resConstituents S.scalar.base θ, ∃ i : Fin q,
      (∃ v ∈ S.scalar.line i, lam (S.scalar.baseHom (Multiplicative.ofAdd v)) ≠ lam 1) ∧
      ∀ j, j ≠ i → ∀ v ∈ S.scalar.line j,
        lam (S.scalar.baseHom (Multiplicative.ofAdd v)) = lam 1}

theorem mem_axisIrr {θ : S.scalar.grp → ℂ} :
    θ ∈ S.axisIrr ↔ θ ∈ Irr S.scalar.grp ∧ (∀ u ∈ commutator U, θ (inr u) = θ 1) ∧
      ∃ lam ∈ resConstituents S.scalar.base θ, ∃ i : Fin q,
        (∃ v ∈ S.scalar.line i, lam (S.scalar.baseHom (Multiplicative.ofAdd v)) ≠ lam 1) ∧
        ∀ j, j ≠ i → ∀ v ∈ S.scalar.line j,
          lam (S.scalar.baseHom (Multiplicative.ofAdd v)) = lam 1 := Iff.rfl

theorem axisIrr_subset_Irr : S.axisIrr ⊆ Irr S.scalar.grp := fun _ hθ => hθ.1

noncomputable def axisFamily : Set (S.amb → ℂ) :=
  (fun θ => indClassFun S.core (S.pushChar θ)) '' S.axisIrr

theorem mem_axisFamily {f : S.amb → ℂ} :
    f ∈ S.axisFamily ↔ ∃ θ ∈ S.axisIrr, indClassFun S.core (S.pushChar θ) = f := Iff.rfl

theorem indClassFun_mem_axisFamily {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) :
    indClassFun S.core (S.pushChar θ) ∈ S.axisFamily := ⟨θ, hθ, rfl⟩

theorem pushChar_mem_Irr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ Irr S.scalar.grp) :
    S.pushChar θ ∈ Irr S.core :=
  FrobeniusInduction.mem_Irr_comp_mulEquiv hθ S.coreMulEquiv.symm

theorem axisFamily_subset_indFam :
    S.axisFamily ⊆ indFam S.core (Irr S.core) := by
  rintro _ ⟨θ, hθ, rfl⟩
  exact indClassFun_mem_indFam S.core (S.pushChar_mem_Irr (S.axisIrr_subset_Irr hθ))

theorem axisFamily_finite : (S.axisFamily).Finite :=
  (finite_Irr.subset S.axisIrr_subset_Irr).image _

theorem pushChar_one (θ : S.scalar.grp → ℂ) : S.pushChar θ 1 = θ 1 := by
  have h : S.pushChar θ (S.coreMulEquiv 1) = θ 1 := S.pushChar_apply θ 1
  simpa using h

theorem natCard_core : Nat.card S.core = Nat.card S.scalar.grp :=
  (Nat.card_congr S.coreMulEquiv.toEquiv).symm

theorem index_core : (S.core).index = q := by
  have hcard : Nat.card S.amb = Nat.card S.scalar.grp * Nat.card B := SemidirectProduct.card
  have h := Subgroup.card_mul_index S.core
  rw [S.natCard_core, hcard, S.card_B] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem indClassFun_pushChar_one (θ : S.scalar.grp → ℂ) :
    indClassFun S.core (S.pushChar θ) 1 = (q : ℂ) * θ 1 := by
  rw [indClassFun_one]
  have hi := S.index_core
  have h := Subgroup.card_mul_index S.core
  rw [hi] at h
  have hcpos : (Nat.card S.core : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [S.pushChar_one, ← h]
  push_cast
  field_simp

theorem pushChar_star (θ : S.scalar.grp → ℂ) : S.pushChar (star θ) = star (S.pushChar θ) := by
  funext x
  have h1 : S.pushChar (star θ) (S.coreMulEquiv (S.coreMulEquiv.symm x))
      = star θ (S.coreMulEquiv.symm x) := S.pushChar_apply _ _
  have h2 : S.pushChar θ (S.coreMulEquiv (S.coreMulEquiv.symm x))
      = θ (S.coreMulEquiv.symm x) := S.pushChar_apply _ _
  rw [MulEquiv.apply_symm_apply] at h1 h2
  rw [h1, Pi.star_apply, Pi.star_apply, h2]

theorem resClassFun_star {G : Type*} [Group G] (H : Subgroup G) (χ : G → ℂ) :
    resClassFun H (star χ) = star (resClassFun H χ) := by
  funext s
  rw [resClassFun_apply, Pi.star_apply, Pi.star_apply, resClassFun_apply]

theorem star_mem_axisIrr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) : star θ ∈ S.axisIrr := by
  obtain ⟨hIrr, hU, lam, hlam, i, ⟨v, hv, hne⟩, hother⟩ := S.mem_axisIrr.1 hθ
  refine S.mem_axisIrr.2 ⟨star_mem_Irr hIrr, fun u hu => ?_, star lam, ?_, i, ⟨v, hv, ?_⟩, ?_⟩
  · rw [Pi.star_apply, Pi.star_apply, hU u hu]
  · rw [mem_resConstituents] at hlam ⊢
    refine ⟨star_mem_Irr hlam.1, ?_⟩
    rw [resClassFun_star, cfInner_star_star]
    have h := hlam.2
    rw [RCLike.pos_iff] at h ⊢
    simpa using h
  · rw [Pi.star_apply, Pi.star_apply]
    exact fun hcon => hne (star_injective hcon)
  · intro j hj w hw
    rw [Pi.star_apply, Pi.star_apply, hother j hj w hw]

theorem star_mem_axisFamily {f : S.amb → ℂ} (hf : f ∈ S.axisFamily) :
    star f ∈ S.axisFamily := by
  obtain ⟨θ, hθ, rfl⟩ := S.mem_axisFamily.1 hf
  refine S.mem_axisFamily.2 ⟨star θ, S.star_mem_axisIrr hθ, ?_⟩
  rw [S.pushChar_star, DisjointCoherentFamilies.indClassFun_star]

theorem mem_baseCore {x : S.core} :
    x ∈ S.baseCore ↔ ∃ y ∈ S.scalar.base, S.coreMulEquiv y = x := by
  refine ⟨fun h => ?_, fun ⟨y, hy, h⟩ => ?_⟩
  · obtain ⟨y, hy, h⟩ := Subgroup.mem_map.1 h
    exact ⟨y, hy, h⟩
  · exact Subgroup.mem_map.2 ⟨y, hy, h⟩

theorem subset_charValueKernel_pushChar_iff (θ : S.scalar.grp → ℂ) :
    (S.baseCore : Set S.core) ⊆ charValueKernel (S.pushChar θ) ↔
      (S.scalar.base : Set S.scalar.grp) ⊆ charValueKernel θ := by
  refine ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · have h2 := h ((S.mem_baseCore).2 ⟨y, hy, rfl⟩)
    rw [mem_charValueKernel, S.pushChar_apply, S.pushChar_one] at h2
    exact mem_charValueKernel.2 h2
  · obtain ⟨y, hy, rfl⟩ := (S.mem_baseCore).1 hx
    refine mem_charValueKernel.2 ?_
    rw [S.pushChar_apply, S.pushChar_one]
    exact mem_charValueKernel.1 (h hy)

theorem not_subset_charValueKernel_of_mem_axisIrr {θ : S.scalar.grp → ℂ}
    (hθ : θ ∈ S.axisIrr) :
    ¬ ((S.scalar.base : Set S.scalar.grp) ⊆ charValueKernel θ) := by
  obtain ⟨-, -, lam, hlam, i, ⟨v, hv, hne⟩, -⟩ := S.mem_axisIrr.1 hθ
  intro hker
  have hres : resClassFun S.scalar.base θ = θ 1 • (1 : S.scalar.base → ℂ) :=
    CFSG.FeitThompson.resClassFun_eq_smul_one_of_subset_charValueKernel hker
  have h1 : lam = 1 := by
    by_contra hne1
    have h0 : cfInner (resClassFun S.scalar.base θ) lam = 0 := by
      rw [hres, cfInner_smul_left,
        cfInner_eq_ite_of_mem_Irr CFSG.FeitThompson.one_mem_Irr
        (mem_resConstituents.1 hlam).1, if_neg (Ne.symm hne1), mul_zero]
    have hpos := (mem_resConstituents.1 hlam).2
    rw [h0] at hpos
    exact absurd hpos (by simp)
  rw [h1] at hne
  simp at hne

theorem commCentralizer_le_commutator : S.commCentralizer ≤ commutator U := by
  rw [AxisSystem.commCentralizer, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem exists_detecting_of_mem_axisFamily {f : S.amb → ℂ} (hf : f ∈ S.axisFamily) :
    ∃ θ ∈ Irr S.core,
      (∀ u ∈ S.commCentralizer, θ (S.coreMulEquiv (inr u)) = θ 1) ∧
      ¬ ((S.baseCore : Set S.core) ⊆ charValueKernel θ) ∧
      indClassFun S.core θ = f := by
  obtain ⟨θ, hθ, rfl⟩ := S.mem_axisFamily.1 hf
  refine ⟨S.pushChar θ, S.pushChar_mem_Irr (S.axisIrr_subset_Irr hθ), fun u hu => ?_, ?_, rfl⟩
  · rw [S.pushChar_apply, S.pushChar_one]
    exact (S.mem_axisIrr.1 hθ).2.1 u (S.commCentralizer_le_commutator hu)
  · rw [S.subset_charValueKernel_pushChar_iff]
    exact S.not_subset_charValueKernel_of_mem_axisIrr hθ

section Orbit

open NormalInduction (conjClassFun conjClassFun_apply)

open scoped ComplexOrder

include S in
theorem orderOf_perm : orderOf S.perm = q := by
  classical
  rw [S.isCycle_perm.orderOf, S.support_perm, Finset.card_univ, Fintype.card_fin]

include S in
theorem orderOf_gen : orderOf S.gen = q := by
  have hB : Finite B := S.finite_complement
  have htop : Subgroup.zpowers S.gen = ⊤ := le_antisymm le_top fun x _ => S.mem_zpowers_gen x
  have hc : Nat.card (Subgroup.zpowers S.gen) = Nat.card B := by
    rw [htop]; exact Subgroup.card_top
  rw [← Nat.card_zpowers, hc, S.card_B]

include S in
theorem pow_gen_eq_one_of_perm_pow_apply_eq {k : ℕ} {i : Fin q}
    (h : (S.perm ^ k) i = i) : S.gen ^ k = 1 := by
  have hperm : S.perm ^ k = 1 := by
    refine (S.isCycle_perm.pow_eq_one_iff).2 ⟨i, ?_, h⟩
    exact Equiv.Perm.mem_support.1 (by rw [S.support_perm]; exact Finset.mem_univ i)
  have hdvd : q ∣ k := by
    rw [← S.orderOf_perm]
    exact orderOf_dvd_of_pow_eq_one hperm
  rw [← S.orderOf_gen] at hdvd
  exact orderOf_dvd_iff_pow_eq_one.1 hdvd

include S in
theorem exists_pow_gen_eq (g : B) : ∃ k : ℕ, S.gen ^ k = g := by
  have hB : Finite B := S.finite_complement
  exact (mem_powers_iff_mem_zpowers (x := S.gen) (y := g)).2 (S.mem_zpowers_gen g)

noncomputable def charActB (g : B) (χ : Multiplicative V →* ℂˣ) : Multiplicative V →* ℂˣ :=
  χ.comp (S.mulAutV g).toMonoidHom

theorem charActB_apply (g : B) (χ : Multiplicative V →* ℂˣ) (v : Multiplicative V) :
    S.charActB g χ v = χ (S.mulAutV g v) := (rfl)

theorem charActB_apply_ofAdd (g : B) (χ : Multiplicative V →* ℂˣ) (v : V) :
    S.charActB g χ (Multiplicative.ofAdd v) = χ (Multiplicative.ofAdd (S.actB g v)) := by
  rw [S.charActB_apply, S.mulAutV_apply]

theorem charActB_mul (g h : B) (χ : Multiplicative V →* ℂˣ) :
    S.charActB (g * h) χ = S.charActB h (S.charActB g χ) := by
  refine MonoidHom.ext fun x => ?_
  induction x using Multiplicative.rec with
  | _ v =>
    rw [S.charActB_apply_ofAdd, S.charActB_apply_ofAdd, S.charActB_apply_ofAdd]
    congr 2
    rw [map_mul]; rfl

theorem charActB_one (χ : Multiplicative V →* ℂˣ) : S.charActB 1 χ = χ := by
  refine MonoidHom.ext fun x => ?_
  induction x using Multiplicative.rec with
  | _ v => rw [S.charActB_apply_ofAdd, map_one]; rfl

include S in
theorem actB_gen_mem_line (i : Fin q) {v : V} (hv : v ∈ S.scalar.line i) :
    S.actB S.gen v ∈ S.scalar.line (S.perm i) := by
  rw [← S.map_line_gen i]
  exact Submodule.mem_map_of_mem hv

include S in
theorem exists_actB_gen_eq_of_mem_line (i : Fin q) {w : V}
    (hw : w ∈ S.scalar.line (S.perm i)) : ∃ v ∈ S.scalar.line i, S.actB S.gen v = w := by
  rw [← S.map_line_gen i] at hw
  obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.1 hw
  exact ⟨v, hv, hvw⟩

theorem isAxisChar_charActB_gen {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.scalar.IsAxisChar (S.perm i) χ) :
    S.scalar.IsAxisChar i (S.charActB S.gen χ) := by
  refine ScalarCoordinateSystem.isAxisChar_of ?_ fun j hj v hv => ?_
  · obtain ⟨w, hw, hwne⟩ := h.exists_ne_one
    obtain ⟨v, hv, hvw⟩ := S.exists_actB_gen_eq_of_mem_line i hw
    exact ⟨v, hv, by rw [S.charActB_apply_ofAdd, hvw]; exact hwne⟩
  · rw [S.charActB_apply_ofAdd]
    refine h.eq_one_of_ne ?_ (S.actB_gen_mem_line j hv)
    intro hcon
    exact hj (S.perm.injective hcon)

theorem isAxisChar_charActB_pow (k : ℕ) {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.scalar.IsAxisChar ((S.perm ^ k) i) χ) :
    S.scalar.IsAxisChar i (S.charActB (S.gen ^ k) χ) := by
  induction k generalizing i with
  | zero => simpa [S.charActB_one] using h
  | succ n ih =>
    have h1 : (S.perm ^ (n + 1)) i = (S.perm ^ n) (S.perm i) := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    rw [h1] at h
    have h2 : S.gen ^ (n + 1) = S.gen ^ n * S.gen := by rw [pow_succ]
    rw [h2, S.charActB_mul]
    exact S.isAxisChar_charActB_gen (ih h)

theorem isAxisChar_of_isAxisChar_charActB_gen {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.scalar.IsAxisChar i (S.charActB S.gen χ)) :
    S.scalar.IsAxisChar (S.perm i) χ := by
  refine ScalarCoordinateSystem.isAxisChar_of ?_ fun j' hj' w hw => ?_
  · obtain ⟨v, hv, hvne⟩ := h.exists_ne_one
    rw [S.charActB_apply_ofAdd] at hvne
    exact ⟨S.actB S.gen v, S.actB_gen_mem_line i hv, hvne⟩
  · obtain ⟨v, hv, hvw⟩ := S.exists_actB_gen_eq_of_mem_line (S.perm.symm j') (by
      rw [Equiv.apply_symm_apply]; exact hw)
    rw [← hvw, ← S.charActB_apply_ofAdd]
    refine h.eq_one_of_ne ?_ hv
    intro hcon
    exact hj' (by rw [← hcon, Equiv.apply_symm_apply])

theorem isAxisChar_charActB_pow_iff (k : ℕ) {i : Fin q} {χ : Multiplicative V →* ℂˣ} :
    S.scalar.IsAxisChar i (S.charActB (S.gen ^ k) χ) ↔
      S.scalar.IsAxisChar ((S.perm ^ k) i) χ := by
  refine ⟨?_, S.isAxisChar_charActB_pow k⟩
  induction k generalizing i χ with
  | zero => intro h; simpa [S.charActB_one] using h
  | succ n ih =>
    intro h
    have h2 : S.gen ^ (n + 1) = S.gen ^ n * S.gen := by rw [pow_succ]
    rw [h2, S.charActB_mul] at h
    have h3 := S.isAxisChar_of_isAxisChar_charActB_gen (χ := S.charActB (S.gen ^ n) χ) h
    have h4 : (S.perm ^ (n + 1)) i = S.perm ((S.perm ^ n) i) := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
    rw [h4, ← Equiv.Perm.mul_apply, ← pow_succ', pow_succ, Equiv.Perm.mul_apply]
    exact ih h3

theorem autCore_inr (g : B) (u : U) : S.autCore g (inr u) = inr (S.autB g u) :=
  SemidirectProduct.ext (by rw [S.autCore_apply_left, left_inr, left_inr, map_one])
    (by rw [S.autCore_apply_right, right_inr, right_inr])

theorem autB_mem_commutator (g : B) {u : U} (hu : u ∈ commutator U) :
    S.autB g u ∈ commutator U := by
  have h := (instCharacteristicCommutator U).fixed (S.autB g).symm
  rw [← h, Subgroup.mem_comap]
  simpa using hu

theorem autCore_inl (g : B) (v : Multiplicative V) :
    S.autCore g (inl v) = inl (S.mulAutV g v) :=
  SemidirectProduct.ext (by rw [S.autCore_apply_left, left_inl, left_inl])
    (by rw [S.autCore_apply_right, right_inl, right_inl, map_one])

theorem mulAutV_mul (g h : B) (x : Multiplicative V) :
    S.mulAutV (g * h) x = S.mulAutV g (S.mulAutV h x) := by
  induction x using Multiplicative.rec with
  | _ v =>
    rw [S.mulAutV_apply, S.mulAutV_apply, S.mulAutV_apply]
    congr 1
    rw [map_mul]; rfl

theorem mulAutV_one (x : Multiplicative V) : S.mulAutV 1 x = x := by
  induction x using Multiplicative.rec with
  | _ v => rw [S.mulAutV_apply, map_one]; rfl

theorem mulAutV_symm_apply (g : B) (x : Multiplicative V) :
    (S.mulAutV g).symm x = S.mulAutV g⁻¹ x := by
  have h2 : S.mulAutV g (S.mulAutV g⁻¹ x) = x := by
    rw [← S.mulAutV_mul, mul_inv_cancel, S.mulAutV_one]
  conv_lhs => rw [← h2]
  rw [MulEquiv.symm_apply_apply]

theorem conjClassFun_inr_pushChar (g : B) (θ : S.scalar.grp → ℂ) :
    conjClassFun S.core (inr g) (S.pushChar θ) = S.pushChar (θ ∘ S.autCore g⁻¹) := by
  funext y
  obtain ⟨x, rfl⟩ : ∃ x, S.coreMulEquiv x = y := ⟨S.coreMulEquiv.symm y, by simp⟩
  rw [conjClassFun_apply, S.pushChar_apply]
  have hc : (MulAut.conjNormal (inr g : S.amb)⁻¹) (S.coreMulEquiv x)
      = S.coreMulEquiv (S.autCore g⁻¹ x) := by
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, S.coe_coreMulEquiv_apply, S.coe_coreMulEquiv_apply, inv_inv]
    have h := inl_aut_inv (φ := S.autCore) g x
    have hinv : ((inr g : S.amb))⁻¹ = (inr g⁻¹ : S.amb) :=
      (map_inv (SemidirectProduct.inr : B →* S.amb) g).symm
    rw [hinv, ← h, map_inv]
  rw [hc, S.pushChar_apply]
  rfl

theorem cfInner_resClassFun_baseChar_comp_autCore (θ : S.scalar.grp → ℂ) (g : B)
    (χ : Multiplicative V →* ℂˣ) [Fintype (Multiplicative V)] :
    cfInner (resClassFun S.scalar.base (θ ∘ S.autCore g)) (S.scalar.baseChar χ)
      = cfInner (resClassFun S.scalar.base θ) (S.scalar.baseChar (S.charActB g⁻¹ χ)) := by
  rw [S.scalar.cfInner_resClassFun_baseChar_eq, S.scalar.cfInner_resClassFun_baseChar_eq,
    ← cfInner_comp_equiv (S.mulAutV g).symm.toEquiv]
  congr 1
  · funext v
    change θ (S.autCore g (inl ((S.mulAutV g).symm v))) = θ (inl v)
    rw [S.autCore_inl, MulEquiv.apply_symm_apply]
  · funext v
    change (χ ((S.mulAutV g).symm v) : ℂ) = ((S.charActB g⁻¹ χ) v : ℂ)
    rw [S.charActB_apply, S.mulAutV_symm_apply]

theorem mem_resConstituents_baseChar_comp_autCore (θ : S.scalar.grp → ℂ) (g : B)
    (χ : Multiplicative V →* ℂˣ) :
    S.scalar.baseChar χ ∈ resConstituents S.scalar.base (θ ∘ S.autCore g)
      ↔ S.scalar.baseChar (S.charActB g⁻¹ χ) ∈ resConstituents S.scalar.base θ := by
  have hfin : Finite V := S.scalar.finite_of_finite_line
  have : Finite (Multiplicative V) := hfin
  let _ : Fintype (Multiplicative V) := Fintype.ofFinite _
  rw [mem_resConstituents, mem_resConstituents, S.cfInner_resClassFun_baseChar_comp_autCore]
  exact and_congr_left fun _ => ⟨fun _ => S.scalar.baseChar_mem_Irr _,
    fun _ => S.scalar.baseChar_mem_Irr _⟩

theorem eq_one_of_comp_autCore_eq {θ : S.scalar.grp → ℂ} {i : Fin q}
    (hθ : θ ∈ S.scalar.axisWeightFinset i) {g : B} (h : θ ∘ S.autCore g = θ) : g = 1 := by
  obtain ⟨hIrr, χ, hχ, hres⟩ := (S.scalar.mem_axisWeightFinset_iff_baseChar).1 hθ
  obtain ⟨k, rfl⟩ := S.exists_pow_gen_eq g
  set χ' := S.charActB (S.gen ^ k)⁻¹ χ with hχ'def
  have hmem : S.scalar.baseChar χ' ∈ resConstituents S.scalar.base θ := by
    rw [← S.mem_resConstituents_baseChar_comp_autCore θ (S.gen ^ k) χ, h]
    exact hres
  have haxis : S.scalar.IsAxisChar i χ' := by
    obtain ⟨χ'', hχ'', hχ''eq⟩ := (S.scalar.mem_axisBaseFinset).1
      (S.scalar.mem_axisBaseFinset_of_mem_resConstituents hθ hmem)
    have heq : χ'' = χ' := S.scalar.baseChar_injective hχ''eq
    rw [← heq]; exact hχ''
  have hback : S.charActB (S.gen ^ k) χ' = χ := by
    rw [hχ'def, ← S.charActB_mul, inv_mul_cancel, S.charActB_one]
  have hj : (S.perm ^ k) ((S.perm ^ k)⁻¹ i) = i := by
    change ((S.perm ^ k) * (S.perm ^ k)⁻¹) i = i
    rw [mul_inv_cancel]
    rfl
  have h2 : S.scalar.IsAxisChar ((S.perm ^ k)⁻¹ i) (S.charActB (S.gen ^ k) χ') :=
    S.isAxisChar_charActB_pow k (by rw [hj]; exact haxis)
  rw [hback] at h2
  have hji : (S.perm ^ k)⁻¹ i = i := h2.unique hχ
  have hfix : (S.perm ^ k) i = i := by
    conv_lhs => rw [← hji]
    exact hj
  exact S.pow_gen_eq_one_of_perm_pow_apply_eq hfix

theorem pushChar_injective : Function.Injective S.pushChar := by
  intro θ θ' h
  funext x
  have h1 := congrFun h (S.coreMulEquiv x)
  rw [S.pushChar_apply, S.pushChar_apply] at h1
  exact h1

theorem inertiaGroup_pushChar_eq_core {θ : S.scalar.grp → ℂ} {i : Fin q}
    (hθ : θ ∈ S.scalar.axisWeightFinset i) :
    inertiaGroup S.core (S.pushChar θ) = S.core := by
  have hcf : S.pushChar θ ∈ classFun S.core :=
    Irr_subset_classFun (S.pushChar_mem_Irr (S.scalar.axisWeightFinset_subset_Irr i hθ))
  refine le_antisymm (fun y hy => ?_) (le_inertiaGroup S.core hcf)
  have hK : S.core ≤ inertiaGroup S.core (S.pushChar θ) := le_inertiaGroup S.core hcf
  have hy2 : (inr y.right : S.amb) ∈ inertiaGroup S.core (S.pushChar θ) := by
    have hdec : (inl y.left : S.amb) * inr y.right = y := inl_left_mul_inr_right y
    have h1 : (inl y.left : S.amb) ∈ inertiaGroup S.core (S.pushChar θ) := hK (S.inl_mem_core _)
    rw [eq_inv_mul_of_mul_eq hdec]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) hy
  have hfix : conjClassFun S.core (inr y.right) (S.pushChar θ) = S.pushChar θ :=
    mem_inertiaGroup.1 hy2
  rw [S.conjClassFun_inr_pushChar] at hfix
  have hg : y.right⁻¹ = 1 := S.eq_one_of_comp_autCore_eq hθ (S.pushChar_injective hfix)
  have hg1 : y.right = 1 := by rw [← inv_inv y.right, hg, inv_one]
  have hyeq : y = inl y.left :=
    SemidirectProduct.ext (by rw [left_inl]) (by rw [right_inl, hg1])
  rw [hyeq]
  exact S.inl_mem_core _

theorem card_conjOrbit_pushChar {θ : S.scalar.grp → ℂ} {i : Fin q}
    (hθ : θ ∈ S.scalar.axisWeightFinset i) :
    (NormalInduction.conjOrbit S.core (S.pushChar θ)).card = q := by
  rw [card_conjOrbit, S.inertiaGroup_pushChar_eq_core hθ, S.index_core]

theorem mem_axisIrr_iff {θ : S.scalar.grp → ℂ} :
    θ ∈ S.axisIrr ↔ (∀ u ∈ commutator U, θ (inr u) = θ 1) ∧
      ∃ i : Fin q, θ ∈ S.scalar.axisWeightFinset i := by
  rw [S.mem_axisIrr]
  constructor
  · intro h
    obtain ⟨hIrr, hker, lam, hlam, i, h1, h2⟩ := h
    exact ⟨hker, i, (S.scalar.mem_axisWeightFinset_iff).2 ⟨hIrr, lam, hlam, h1, h2⟩⟩
  · intro h
    obtain ⟨hker, i, hi⟩ := h
    obtain ⟨hIrr, lam, hlam, h1, h2⟩ := (S.scalar.mem_axisWeightFinset_iff).1 hi
    exact ⟨hIrr, hker, lam, hlam, i, h1, h2⟩

theorem comp_autCore_mem_axisIrr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) (g : B) :
    θ ∘ S.autCore g ∈ S.axisIrr := by
  obtain ⟨hker, i, hi⟩ := (S.mem_axisIrr_iff).1 hθ
  obtain ⟨hIrr, χ, hχ, hres⟩ := (S.scalar.mem_axisWeightFinset_iff_baseChar).1 hi
  obtain ⟨k, rfl⟩ := S.exists_pow_gen_eq g
  have hj : (S.perm ^ k) ((S.perm ^ k)⁻¹ i) = i := by
    change ((S.perm ^ k) * (S.perm ^ k)⁻¹) i = i
    rw [mul_inv_cancel]; rfl
  refine (S.mem_axisIrr_iff).2 ⟨fun u hu => ?_, (S.perm ^ k)⁻¹ i, ?_⟩
  · simp only [Function.comp_apply]
    rw [S.autCore_inr, map_one]
    exact hker _ (S.autB_mem_commutator _ hu)
  · refine (S.scalar.mem_axisWeightFinset_iff_baseChar).2 ⟨
      FrobeniusInduction.mem_Irr_comp_mulEquiv hIrr (S.autCore (S.gen ^ k)),
      S.charActB (S.gen ^ k) χ, ?_, ?_⟩
    · rw [S.isAxisChar_charActB_pow_iff, hj]
      exact hχ
    · rw [S.mem_resConstituents_baseChar_comp_autCore, ← S.charActB_mul, mul_inv_cancel,
        S.charActB_one]
      exact hres

theorem pushChar_mem_classFun {θ : S.scalar.grp → ℂ} (hθ : θ ∈ classFun S.scalar.grp) :
    S.pushChar θ ∈ classFun S.core := by
  refine mem_classFun.2 fun g x hgx => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 hgx
  obtain ⟨y, rfl⟩ : ∃ y, S.coreMulEquiv y = g := ⟨S.coreMulEquiv.symm g, by simp⟩
  obtain ⟨z, rfl⟩ : ∃ z, S.coreMulEquiv z = x := ⟨S.coreMulEquiv.symm x, by simp⟩
  obtain ⟨w, rfl⟩ : ∃ w, S.coreMulEquiv w = c := ⟨S.coreMulEquiv.symm c, by simp⟩
  rw [S.pushChar_apply, S.pushChar_apply]
  refine mem_classFun.1 hθ y z (isConj_iff.2 ⟨w, ?_⟩)
  refine S.coreMulEquiv.injective ?_
  rw [map_mul, map_mul, map_inv]
  exact hc

theorem comp_autCore_mem_classFun {θ : S.scalar.grp → ℂ} (hθ : θ ∈ classFun S.scalar.grp)
    (g : B) : θ ∘ S.autCore g ∈ classFun S.scalar.grp := by
  refine mem_classFun.2 fun x y hxy => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  simp only [Function.comp_apply]
  refine mem_classFun.1 hθ _ _ (isConj_iff.2 ⟨S.autCore g c, ?_⟩)
  rw [← map_inv, ← map_mul, ← map_mul, hc]

theorem conjClassFun_pushChar (t : S.amb) {θ : S.scalar.grp → ℂ}
    (hθ : θ ∈ classFun S.scalar.grp) :
    conjClassFun S.core t (S.pushChar θ) = S.pushChar (θ ∘ S.autCore t.right⁻¹) := by
  have hdec : (inl t.left : S.amb) * inr t.right = t := inl_left_mul_inr_right t
  have hfix : conjClassFun S.core (inl t.left) (S.pushChar (θ ∘ S.autCore t.right⁻¹))
      = S.pushChar (θ ∘ S.autCore t.right⁻¹) :=
    mem_inertiaGroup.1 (le_inertiaGroup S.core
      (S.pushChar_mem_classFun (S.comp_autCore_mem_classFun hθ _)) (S.inl_mem_core t.left))
  calc conjClassFun S.core t (S.pushChar θ)
      = conjClassFun S.core (inl t.left * inr t.right) (S.pushChar θ) := by rw [hdec]
    _ = conjClassFun S.core (inl t.left) (conjClassFun S.core (inr t.right) (S.pushChar θ)) := by
        rw [← conjClassFun_mul]
    _ = conjClassFun S.core (inl t.left) (S.pushChar (θ ∘ S.autCore t.right⁻¹)) := by
        rw [S.conjClassFun_inr_pushChar]
    _ = S.pushChar (θ ∘ S.autCore t.right⁻¹) := hfix

theorem exists_mem_axisIrr_pushChar_eq {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr)
    {f : S.core → ℂ} (hf : f ∈ NormalInduction.conjOrbit S.core (S.pushChar θ)) :
    ∃ θ' ∈ S.axisIrr, S.pushChar θ' = f := by
  obtain ⟨t, ht⟩ := NormalInduction.mem_conjOrbit.1 hf
  refine ⟨θ ∘ S.autCore t.right⁻¹, S.comp_autCore_mem_axisIrr hθ _, ?_⟩
  rw [← S.conjClassFun_pushChar t (Irr_subset_classFun (S.axisIrr_subset_Irr hθ))]
  exact ht

theorem indClassFun_pushChar_eq_iff {θ θ' : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr)
    (hθ' : θ' ∈ S.axisIrr) :
    indClassFun S.core (S.pushChar θ) = indClassFun S.core (S.pushChar θ')
      ↔ S.pushChar θ ∈ NormalInduction.conjOrbit S.core (S.pushChar θ') := by
  rw [NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun S.core
    (S.pushChar_mem_Irr (S.axisIrr_subset_Irr hθ)) (S.pushChar_mem_Irr (S.axisIrr_subset_Irr hθ')),
    NormalInduction.mem_conjOrbit]

theorem card_conjOrbit_pushChar_axisIrr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) :
    (NormalInduction.conjOrbit S.core (S.pushChar θ)).card = q := by
  obtain ⟨-, i, hi⟩ := (S.mem_axisIrr_iff).1 hθ
  exact S.card_conjOrbit_pushChar hi

open scoped Classical in
noncomputable def axisIrrFinset : Finset (S.scalar.grp → ℂ) :=
  {θ ∈ irrFinset S.scalar.grp | θ ∈ S.axisIrr}

theorem mem_axisIrrFinset {θ : S.scalar.grp → ℂ} : θ ∈ S.axisIrrFinset ↔ θ ∈ S.axisIrr := by
  classical
  rw [axisIrrFinset, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_irrFinset.2 (S.axisIrr_subset_Irr h), h⟩⟩

open scoped Classical in
noncomputable def axisFamilyFinset : Finset (S.amb → ℂ) :=
  S.axisIrrFinset.image fun θ => indClassFun S.core (S.pushChar θ)

theorem natCard_axisIrr_eq_card : Nat.card S.axisIrr = S.axisIrrFinset.card := by
  rw [Finset.card_eq_natCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => (S.mem_axisIrrFinset).symm)

theorem natCard_axisFamily_eq_card : Nat.card S.axisFamily = S.axisFamilyFinset.card := by
  classical
  rw [Finset.card_eq_natCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [axisFamilyFinset, Finset.mem_image, S.mem_axisFamily]
  exact ⟨fun ⟨θ, hθ, h⟩ => ⟨θ, (S.mem_axisIrrFinset).2 hθ, h⟩,
    fun ⟨θ, hθ, h⟩ => ⟨θ, (S.mem_axisIrrFinset).1 hθ, h⟩⟩

open scoped Classical in
theorem card_fiber_eq {f : S.amb → ℂ} (hf : f ∈ S.axisFamilyFinset) :
    {θ ∈ S.axisIrrFinset | indClassFun S.core (S.pushChar θ) = f}.card = q := by
  obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.1 hf
  have hθ₀' : θ₀ ∈ S.axisIrr := (S.mem_axisIrrFinset).1 hθ₀
  have hcard : {θ ∈ S.axisIrrFinset | indClassFun S.core (S.pushChar θ)
      = indClassFun S.core (S.pushChar θ₀)}.card
      = (NormalInduction.conjOrbit S.core (S.pushChar θ₀)).card := by
    refine Finset.card_bij (fun θ _ => S.pushChar θ) ?_ ?_ ?_
    · intro θ hθ
      rw [Finset.mem_filter] at hθ
      exact (S.indClassFun_pushChar_eq_iff ((S.mem_axisIrrFinset).1 hθ.1) hθ₀').1 hθ.2
    · intro θ₁ _ θ₂ _ h
      exact S.pushChar_injective h
    · intro g hg
      obtain ⟨θ', hθ', rfl⟩ := S.exists_mem_axisIrr_pushChar_eq hθ₀' hg
      refine ⟨θ', ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨(S.mem_axisIrrFinset).2 hθ', (S.indClassFun_pushChar_eq_iff hθ' hθ₀').2 hg⟩
  rw [hcard, S.card_conjOrbit_pushChar_axisIrr hθ₀']

theorem card_axisIrrFinset : S.axisIrrFinset.card = S.axisFamilyFinset.card * q := by
  classical
  have hmaps : Set.MapsTo (fun θ => indClassFun S.core (S.pushChar θ))
      (S.axisIrrFinset : Set (S.scalar.grp → ℂ)) (S.axisFamilyFinset : Set (S.amb → ℂ)) :=
    fun θ hθ => Finset.mem_coe.2 (Finset.mem_image.2 ⟨θ, Finset.mem_coe.1 hθ, rfl⟩)
  rw [Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl fun f hf => S.card_fiber_eq hf, Finset.sum_const, smul_eq_mul]

theorem natCard_axisFamily_mul : Nat.card S.axisFamily * q = Nat.card S.axisIrr := by
  rw [S.natCard_axisFamily_eq_card, S.natCard_axisIrr_eq_card, S.card_axisIrrFinset]

theorem axisIrr_eq_image :
    S.axisIrr = (fun θ' : (S.scalar.quot).grp → ℂ => θ' ∘ S.scalar.quotHom) ''
      ((S.scalar.quot).allAxisWeightFinset : Set ((S.scalar.quot).grp → ℂ)) := by
  ext θ
  rw [S.mem_axisIrr_iff]
  constructor
  · intro h
    obtain ⟨hker, i, hi⟩ := h
    have hIrr := S.scalar.axisWeightFinset_subset_Irr i hi
    obtain ⟨θ', hθ'Irr, hθ'eq⟩ := S.scalar.exists_comp_quotHom_of_kernel hIrr hker
    refine ⟨θ', ?_, hθ'eq⟩
    refine Finset.mem_coe.2 (((S.scalar.quot).mem_allAxisWeightFinset).2 ⟨i, ?_⟩)
    rw [← S.scalar.mem_axisWeightFinset_comp_quotHom_iff hθ'Irr, hθ'eq]
    exact hi
  · intro h
    obtain ⟨θ', hθ', rfl⟩ := h
    obtain ⟨i, hi⟩ := ((S.scalar.quot).mem_allAxisWeightFinset).1 (Finset.mem_coe.1 hθ')
    have hθ'Irr := (S.scalar.quot).axisWeightFinset_subset_Irr i hi
    refine ⟨fun u hu => ?_, i, ?_⟩
    · change θ' (S.scalar.quotHom (inr u)) = θ' (S.scalar.quotHom 1)
      rw [S.scalar.quotHom_inr, map_one]
      have h1 : (QuotientGroup.mk u : U ⧸ commutator U) = 1 := (QuotientGroup.eq_one_iff _).2 hu
      rw [h1, map_one]
    · rw [S.scalar.mem_axisWeightFinset_comp_quotHom_iff hθ'Irr]
      exact hi

theorem natCard_axisIrr_mul_sq :
    Nat.card S.axisIrr * S.a ^ 2 = q * ((p - 1) * (commutator U).index) := by
  have hinj : Function.Injective
      (fun θ' : (S.scalar.quot).grp → ℂ => θ' ∘ S.scalar.quotHom) := by
    intro θ₁ θ₂ h
    funext y
    obtain ⟨x, rfl⟩ := S.scalar.quotHom_surjective y
    exact congrFun h x
  have hcard : Nat.card S.axisIrr
      = Nat.card ((S.scalar.quot).allAxisWeightFinset : Set ((S.scalar.quot).grp → ℂ)) := by
    rw [S.axisIrr_eq_image]
    exact Nat.card_image_of_injective hinj _
  have h2 : Nat.card ((S.scalar.quot).allAxisWeightFinset : Set ((S.scalar.quot).grp → ℂ))
      = (S.scalar.quot).allAxisWeightFinset.card := by
    rw [Finset.card_eq_natCard]
    exact Nat.card_congr (Equiv.refl _)
  rw [hcard, h2, Subgroup.index_eq_card]
  refine (S.scalar.quot).card_allAxisWeightFinset_mul_sq S.a fun i => ?_
  rw [S.scalar.index_lineCentralizer_quot i, S.index_lineCentralizer i]

theorem apply_one_of_mem_axisIrr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) :
    θ 1 = (S.a : ℂ) := by
  obtain ⟨hker, i, hi⟩ := (S.mem_axisIrr_iff).1 hθ
  have hIrr := S.scalar.axisWeightFinset_subset_Irr i hi
  obtain ⟨θ', hθ'Irr, hθ'eq⟩ := S.scalar.exists_comp_quotHom_of_kernel hIrr hker
  have hi' : θ' ∈ (S.scalar.quot).axisWeightFinset i := by
    rw [← S.scalar.mem_axisWeightFinset_comp_quotHom_iff hθ'Irr, hθ'eq]
    exact hi
  have hdeg := (S.scalar.quot).apply_one_of_mem_axisWeightFinset hi'
  rw [S.scalar.index_lineCentralizer_quot i, S.index_lineCentralizer i] at hdeg
  rw [← hθ'eq]
  change θ' (S.scalar.quotHom 1) = (S.a : ℂ)
  rw [map_one]
  exact hdeg

end Orbit

private theorem axisIrr_degree_and_card :
    (∀ θ ∈ S.axisIrr, θ 1 = (S.a : ℂ)) ∧
      Nat.card S.axisFamily * S.a ^ 2 = (p - 1) * (commutator U).index := by
  refine ⟨fun θ hθ => S.apply_one_of_mem_axisIrr hθ, ?_⟩
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) S.scalar.two_le_q
  have h1 := S.natCard_axisIrr_mul_sq
  rw [← S.natCard_axisFamily_mul] at h1
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  calc Nat.card S.axisFamily * S.a ^ 2 * q
      = Nat.card S.axisFamily * q * S.a ^ 2 := by ring
    _ = q * ((p - 1) * (commutator U).index) := h1
    _ = (p - 1) * (commutator U).index * q := by ring

theorem apply_one_eq_of_mem_axisFamily {f : S.amb → ℂ} (hf : f ∈ S.axisFamily) :
    f 1 = (q * S.a : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := S.mem_axisFamily.1 hf
  rw [S.indClassFun_pushChar_one, S.axisIrr_degree_and_card.1 θ hθ]

theorem natCard_axisFamily_mul_sq :
    Nat.card S.axisFamily * S.a ^ 2 = (p - 1) * (commutator U).index :=
  S.axisIrr_degree_and_card.2

theorem sq_dvd_sub_one_mul_index : S.a ^ 2 ∣ (p - 1) * (commutator U).index :=
  Dvd.intro_left _ S.natCard_axisFamily_mul_sq

theorem axisFamily_spec :
    (∀ f ∈ S.axisFamily, f 1 = (q * S.a : ℂ)) ∧
    (∀ f ∈ S.axisFamily, star f ∈ S.axisFamily) ∧
    Nat.card S.axisFamily * S.a ^ 2 = (p - 1) * (commutator U).index ∧
    S.a ^ 2 ∣ (p - 1) * (commutator U).index ∧
    (∀ f ∈ S.axisFamily, ∃ θ ∈ Irr S.core,
      (∀ u ∈ S.commCentralizer, θ (S.coreMulEquiv (inr u)) = θ 1) ∧
      ¬ ((S.baseCore : Set S.core) ⊆ charValueKernel θ) ∧
      indClassFun S.core θ = f) :=
  ⟨fun _ hf => S.apply_one_eq_of_mem_axisFamily hf, fun _ hf => S.star_mem_axisFamily hf,
    S.natCard_axisFamily_mul_sq, S.sq_dvd_sub_one_mul_index,
    fun _ hf => S.exists_detecting_of_mem_axisFamily hf⟩

end AxisSystem

end ScalarAxis

end CFSG.FeitThompson
