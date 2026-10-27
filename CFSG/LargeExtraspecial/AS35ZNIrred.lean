module

public import CFSG.LargeExtraspecial.AS35ZNFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def zuStab (U : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {g | ∀ u ∈ U, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U ∧
    ((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U}
  mul_mem' {a b} ha hb u hu := by
    refine ⟨(ha _ (hb u hu).1).1, ?_⟩
    change (((b⁻¹ * a⁻¹ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U
    exact (hb _ (ha u hu).2).2
  one_mem' u hu := ⟨hu, hu⟩
  inv_mem' {a} ha u hu := by
    refine ⟨(ha u hu).2, ?_⟩
    rw [inv_inv]
    exact (ha u hu).1

theorem closure_le_zuStab {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ d ∈ S.DbarAsc, ∀ u ∈ U, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) :
    closure S.DbarAsc ≤ zuStab U := by
  rw [Subgroup.closure_le]
  intro d hd u hu
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (ZUHyp.mul_self hd)
  rw [hdinv]
  exact ⟨hU d hd u hu, hU d hd u hu⟩

theorem polar_sub_self_eq_zero_of_typeA {d : S.O} (hd : IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (x : S.Qt) : polar S.q x ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = 0 := by
  have h1 := hd.1 x
  have h2 := hd.2.2.2.2 _ (sub_mem_commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) x)
  have e : (d : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x + ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by abel
  rw [e, map_add_eq, h2, add_zero] at h1
  linear_combination h1

theorem card_eq_two_pow_finrank_zmod2 (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] [Finite M] :
    Nat.card M = 2 ^ finrank (ZMod 2) M := by
  have : Fintype M := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem ZULocal.sq_mem {t : S.O} {P : Subgroup S.O} (hP : S.ZULocal t P) (ht2 : t * t = 1)
    {p : S.O} (hp : p ∈ P) : p * p = 1 ∨ p * p = t := by
  have hcomm : ∀ p' ∈ P, p * p' * p⁻¹ * p'⁻¹ = 1 ∨ p * p' * p⁻¹ * p'⁻¹ = t := by
    intro p' hp'
    have hc : ⁅(⟨p, hp⟩ : P), ⟨p', hp'⟩⁆ ∈ Subgroup.center P := by
      rw [← hP.extra.2.1]
      exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
    refine hP.center _ (P.mul_mem (P.mul_mem (P.mul_mem hp hp') (P.inv_mem hp)) (P.inv_mem hp'))
      fun y hy => ?_
    have := (Subgroup.mem_center_iff.1 hc) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  refine hP.center _ (P.mul_mem hp hp) fun p' hp' => ?_
  set c := p * p' * p⁻¹ * p'⁻¹ with hcdef
  have hcc : c * c = 1 := by
    rcases hcomm p' hp' with h1 | h1 <;> rw [hcdef, h1]
    · rw [mul_one]
    · exact ht2
  have hcp : c * p = p * c := by
    rcases hcomm p' hp' with h1 | h1 <;> rw [hcdef, h1]
    · rw [one_mul, mul_one]
    · exact (hP.mul_comm_t hp).symm
  have hpp' : p * p' = c * p' * p := by rw [hcdef]; group
  calc p * p * p' = p * (p * p') := by group
    _ = p * (c * p' * p) := by rw [hpp']
    _ = p * c * p' * p := by group
    _ = (c * p) * p' * p := by rw [← hcp]
    _ = c * (p * p') * p := by group
    _ = c * (c * p' * p) * p := by rw [hpp']
    _ = (c * c) * p' * (p * p) := by group
    _ = p' * (p * p) := by rw [hcc, one_mul]

@[expose] def zuMoveSub (P : Subgroup S.O) (U B : Submodule (ZMod 2) S.Qt)
    (hPU : P ≤ zuStab U) : Subgroup S.O where
  carrier := {p | p ∈ P ∧ ∀ x ∈ U, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ B}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨P.mul_mem ha hb, fun x hx => ?_⟩
    have e : ((a * b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
        ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) ((b : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          (b : S.Qt ≃ₗ[ZMod 2] S.Qt) x) + ((b : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by
      change (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ((b : S.Qt ≃ₗ[ZMod 2] S.Qt) x) - x = _
      abel
    rw [e]
    exact B.add_mem (ha' _ (hPU hb x hx).1) (hb' x hx)
  one_mem' := ⟨P.one_mem, fun x _ => by
    change x - x ∈ B
    rw [sub_self]
    exact B.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨P.inv_mem ha, fun x hx => ?_⟩
    have hx'U : ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ U := (hPU ha x hx).2
    have hax : (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = x := by
      change ((a * a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x
      rw [mul_inv_cancel]
      rfl
    have e : ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
        -((a : S.Qt ≃ₗ[ZMod 2] S.Qt) (((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
      rw [hax]; abel
    rw [e]
    exact B.neg_mem (ha' _ hx'U)

theorem mem_zuMoveSub {P : Subgroup S.O} {U B : Submodule (ZMod 2) S.Qt} {hPU : P ≤ zuStab U}
    {p : S.O} :
    p ∈ zuMoveSub P U B hPU ↔ p ∈ P ∧ ∀ x ∈ U, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ B :=
  Iff.rfl

@[expose] noncomputable def zuMoveHom (P : Subgroup S.O) (A B : Submodule (ZMod 2) S.Qt)
    (x₀ : S.Qt) (hA : ∀ p ∈ P, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ A)
    (hB : ∀ p ∈ P, ∀ w ∈ A, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ B) :
    P →* Multiplicative (A ⧸ B.comap A.subtype) where
  toFun p := Multiplicative.ofAdd
    (Submodule.Quotient.mk ⟨(p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀, hA p p.2⟩)
  map_one' := by
    have e : (⟨(((1 : P) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀, hA 1 P.one_mem⟩ : A) = 0 :=
      Subtype.ext (by change x₀ - x₀ = 0; rw [sub_self])
    change Multiplicative.ofAdd (Submodule.Quotient.mk _) = 1
    rw [e, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' p p' := by
    change Multiplicative.ofAdd (Submodule.Quotient.mk _) =
      Multiplicative.ofAdd (Submodule.Quotient.mk _ + Submodule.Quotient.mk _)
    rw [← Submodule.Quotient.mk_add]
    congr 1
    rw [Submodule.Quotient.eq]
    change ((p * p' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ -
      (((p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) + ((p' : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀)) ∈ B
    have e : ((p * p' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ -
        (((p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) + ((p' : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀)) =
        (p : S.Qt ≃ₗ[ZMod 2] S.Qt) ((p' : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) -
          ((p' : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) := by
      change (p : S.Qt ≃ₗ[ZMod 2] S.Qt) ((p' : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀) - x₀ - _ = _
      rw [map_sub]
      abel
    rw [e]
    exact hB p p.2 _ (hA p' p'.2)

theorem zuMoveHom_eq_one {P : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {x₀ : S.Qt}
    {hA : ∀ p ∈ P, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ A}
    {hB : ∀ p ∈ P, ∀ w ∈ A, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ B} {p : P}
    (h1 : zuMoveHom P A B x₀ hA hB p = 1) : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ B := by
  have h2 : (Submodule.Quotient.mk ⟨(p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀, hA p p.2⟩ :
      A ⧸ B.comap A.subtype) = 0 := congrArg Multiplicative.toAdd h1
  rw [Submodule.Quotient.mk_eq_zero] at h2
  exact h2

theorem card_le_of_zuMoveHom {P K : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {x₀ : S.Qt}
    {hA : ∀ p ∈ P, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ A}
    {hB : ∀ p ∈ P, ∀ w ∈ A, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ B}
    (hK : ∀ p : P, zuMoveHom P A B x₀ hA hB p = 1 → (p : S.O) ∈ K) :
    Nat.card P ≤ Nat.card K * Nat.card (A ⧸ B.comap A.subtype) := by
  set θ := zuMoveHom P A B x₀ hA hB with hθ
  have : Finite (A ⧸ B.comap A.subtype) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Finite (Multiplicative (A ⧸ B.comap A.subtype)) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  have h1 := Subgroup.card_mul_index θ.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card θ.ker ≤ Nat.card K := by
    have hle : θ.ker.map P.subtype ≤ K := by
      rintro _ ⟨p, hp, rfl⟩
      exact hK p hp
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective P.subtype_injective] at this
  have h3 : Nat.card θ.range ≤ Nat.card (A ⧸ B.comap A.subtype) :=
    (Subgroup.card_le_card_group θ.range).trans
      (Nat.card_congr Multiplicative.toAdd).le
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

namespace ZUHyp

variable {k : ℕ} (h : S.ZUHyp k) (hloc : ∀ t ∈ S.DbarAsc, ∃ P, S.ZULocal t P)
include h hloc

theorem exists_ne_of_inv {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ d ∈ S.DbarAsc, ∀ u ∈ U, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) (hU0 : U ≠ ⊥)
    {d : S.O} (hd : d ∈ S.DbarAsc) : ∃ x ∈ U, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) x ≠ x := by
  by_contra hall
  push Not at hall
  apply hU0
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine h.eq_zero_of_fix hloc (fun d' hd' => ?_)
  obtain ⟨g, hg, rfl⟩ := h.cls d hd d' hd'
  have hgU := closure_le_zuStab hU hg
  have hx' := (hgU x hx).2
  calc ((g * d * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x
      = (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((d : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x)) := rfl
    _ = (g : S.Qt ≃ₗ[ZMod 2] S.Qt) (((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
        rw [hall _ hx']
    _ = x := by
        change ((g * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x
        rw [mul_inv_cancel]
        rfl

theorem not_commSpace_le {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ d ∈ S.DbarAsc, ∀ u ∈ U, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) (hUtop : U ≠ ⊤)
    {d : S.O} (hd : d ∈ S.DbarAsc) : ¬ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U := by
  intro hle
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  apply hUtop
  have hperp : LinearMap.BilinForm.orthogonal S.q.polarBilin U = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    refine h.eq_zero_of_fix hloc (fun d' hd' => ?_)
    obtain ⟨g, hg, rfl⟩ := h.cls d hd d' hd'
    have hgU := closure_le_zuStab hU hg
    rw [← mem_fixSpace, fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate (g * d * g⁻¹).2,
      OrthoF2.mem_orthogonal_iff_polar]
    intro a ha
    obtain ⟨v, rfl⟩ := mem_commSpace.1 ha
    have hmem : ((g * d * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ U := by
      have e : ((g * d * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
          (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((d : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
              ((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
        rw [map_sub]
        congr 1
        change v = ((g * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
        rw [mul_inv_cancel]
        rfl
      rw [e]
      exact (hgU _ (hle (sub_mem_commSpace _ _))).1
    rw [OrthoF2.mem_orthogonal_iff_polar] at hy
    exact hy _ hmem
  have h1 := finrank_add_finrank_orthogonal_Qt (S := S) U
  rw [hperp, finrank_bot, add_zero] at h1
  exact Submodule.eq_top_of_finrank_eq h1

theorem exists_point {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ d ∈ S.DbarAsc, ∀ u ∈ U, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) (hU0 : U ≠ ⊥)
    (hUtop : U ≠ ⊤) {d : S.O} (hd : d ∈ S.DbarAsc) :
    ∃ x₀ ∈ U, ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ≠ 0) ∧
      (∀ w ∈ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt), w ∈ U →
        w = 0 ∨ w = (d : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) ∧
      ∀ y ∈ U, polar S.q y ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) = 0 := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨x₀, hx₀, hne⟩ := h.exists_ne_of_inv hloc hU hU0 hd
  set D : S.Qt ≃ₗ[ZMod 2] S.Qt := (d : S.Qt ≃ₗ[ZMod 2] S.Qt) with hD
  set u := D x₀ - x₀ with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hne
  have huU : u ∈ U := U.sub_mem (hU d hd x₀ hx₀) hx₀
  have hucomm : u ∈ commSpace D := sub_mem_commSpace D x₀
  have hB : ∀ w ∈ commSpace D, w ∈ U → w = 0 ∨ w = u := by
    intro w hw hwU
    set B := commSpace D ⊓ U with hBdef
    have hlt : B < commSpace D := by
      refine lt_of_le_of_ne inf_le_left fun heq => h.not_commSpace_le hloc hU hUtop hd ?_
      rw [← heq]
      exact inf_le_right
    have hfin : finrank (ZMod 2) B ≤ 1 := by
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      rw [(h.isTypeA hd).2.2.2.1] at h1
      omega
    have hspan : Submodule.span (ZMod 2) {u} = B := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_inf.2 ⟨hucomm, huU⟩
      · rw [finrank_span_singleton hu0]
        exact hfin
    have hwB : w ∈ Submodule.span (ZMod 2) {u} := by
      rw [hspan]
      exact Submodule.mem_inf.2 ⟨hw, hwU⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hwB
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  refine ⟨x₀, hx₀, hu0, hB, fun y hy => ?_⟩
  have hy' : D y - y ∈ commSpace D := sub_mem_commSpace D y
  rcases hB _ hy' (U.sub_mem (hU d hd y hy) hy) with h0 | h1
  ·
    have e : D (y + x₀) - (y + x₀) = u := by
      rw [map_add, hu]
      have : D y = y := sub_eq_zero.1 h0
      rw [this]
      abel
    have h2 := polar_sub_self_eq_zero_of_typeA (h.isTypeA hd) (y + x₀)
    have h3 := polar_sub_self_eq_zero_of_typeA (h.isTypeA hd) x₀
    rw [e, polar_add_left] at h2
    rw [← hu] at h3
    rw [← hu]
    linear_combination h2 - h3
  · have h2 := polar_sub_self_eq_zero_of_typeA (h.isTypeA hd) y
    rwa [h1] at h2

theorem false_of_isotropic {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ d ∈ S.DbarAsc, ∀ u ∈ U, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) (hU0 : U ≠ ⊥)
    (hUtop : U ≠ ⊤) (hUiso : ∀ x ∈ U, ∀ y ∈ U, polar S.q x y = 0) : False := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hk := h.two_le
  have hw := h.width_eq
  obtain ⟨t, ht⟩ := h.nonempty
  obtain ⟨P, hP⟩ := hloc t ht
  obtain ⟨ψ⟩ := h.psu
  have ht2 : t * t = 1 := mul_self ht
  set T : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hT
  obtain ⟨x₀, hx₀, hu0, hB, -⟩ := h.exists_point hloc hU hU0 hUtop ht
  obtain ⟨u, hu⟩ : ∃ u, u = T x₀ - x₀ := ⟨_, rfl⟩
  rw [← hu] at hu0 hB
  have hPU := (hP.le.trans (closure_le_zuStab hU))
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Submodule (ZMod 2) S.Qt, Bs = commSpace T ⊓ U := ⟨_, rfl⟩
  have hBs2 : ∀ w ∈ Bs, w = 0 ∨ w = u := fun w hw => by
    rw [hBs] at hw
    exact hB w (Submodule.mem_inf.1 hw).1 (Submodule.mem_inf.1 hw).2
  have huBs : u ∈ Bs := by
    rw [hBs, hu]
    exact Submodule.mem_inf.2 ⟨sub_mem_commSpace T x₀, U.sub_mem (hU t ht x₀ hx₀) hx₀⟩
  have hBsc : Bs ≤ commSpace T := by rw [hBs]; exact inf_le_left
  have hBsU : Bs ≤ U := by rw [hBs]; exact inf_le_right
  have hmkBs : ∀ w ∈ commSpace T, w ∈ U → w ∈ Bs := fun w h1 h2 => by
    rw [hBs]; exact Submodule.mem_inf.2 ⟨h1, h2⟩
  obtain ⟨Ah, hAh⟩ : ∃ Ah : Subgroup S.O, Ah = zuMoveSub P U Bs hPU := ⟨_, rfl⟩
  have hmemAh : ∀ p, p ∈ Ah ↔ p ∈ P ∧ ∀ x ∈ U, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Bs := by
    intro p; rw [hAh]; exact mem_zuMoveSub
  have hAhP : Ah ≤ P := fun p hp => ((hmemAh p).1 hp).1
  have htAh : t ∈ Ah := (hmemAh t).2 ⟨hP.mem, fun x hx =>
    hmkBs _ (sub_mem_commSpace T x) (U.sub_mem (hU t ht x hx) hx)⟩
  have hTU : ¬ ∀ x ∈ U, T x - x = 0 := fun hall => hu0 (by rw [hu]; exact hall x₀ hx₀)
  have hsq : ∀ p ∈ Ah, p * p = 1 := by
    intro p hp
    obtain ⟨hpP, hp2⟩ := (hmemAh p).1 hp
    have htriv : ∀ x ∈ U, ((p * p : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x = 0 := by
      intro x hx
      have hb := hp2 x hx
      set b := (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x with hbdef
      have hpx : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x + b := by rw [hbdef]; abel
      change (p : S.Qt ≃ₗ[ZMod 2] S.Qt) ((p : S.Qt ≃ₗ[ZMod 2] S.Qt) x) - x = 0
      rw [hpx, map_add, hP.triv p hpP b (hBsc hb), hpx]
      have : b + b = 0 := by rw [← two_smul (ZMod 2) b, show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [add_assoc, this, add_zero, sub_self]
    rcases hP.sq_mem ht2 hpP with h1 | h1
    · exact h1
    · exfalso
      apply hTU
      intro x hx
      have := htriv x hx
      rwa [h1] at this
  have hD := h.hyp.isTClass ht
  have hnormO : ∀ g ∈ closure S.DbarAsc, g * t = t * g → ∀ w ∈ Ah, g * w * g⁻¹ ∈ Ah := by
    intro g hgL hgt w hw
    obtain ⟨hwP, hw2⟩ := (hmemAh w).1 hw
    have hgU := closure_le_zuStab hU hgL
    refine (hmemAh _).2 ⟨hP.norm g (closure_le hgL) hgt _ hwP, fun x hx => ?_⟩
    obtain ⟨x', hx'U, hgx⟩ : ∃ x' ∈ U, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) x' = x :=
      ⟨((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x, (hgU x hx).2, by
        change ((g * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x
        rw [mul_inv_cancel]
        rfl⟩
    have hgi : ((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x' := by
      rw [← hgx]
      change ((g⁻¹ * g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x' = x'
      rw [inv_mul_cancel]
      rfl
    have e2 : ((g * w * g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
        (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((w : S.Qt ≃ₗ[ZMod 2] S.Qt) x' - x') := by
      change (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((w : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((g⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x)) - x = _
      rw [hgi, map_sub, hgx]
    rw [e2]
    have hbc := hBsc (hw2 x' hx'U)
    have hbU := hBsU (hw2 x' hx'U)
    refine hmkBs _ ?_ (hgU _ hbU).1
    obtain ⟨v, hv⟩ := mem_commSpace.1 hbc
    rw [← hv, map_sub]
    have : (g : S.Qt ≃ₗ[ZMod 2] S.Qt) (T v) = T ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      change ((g * t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = ((t * g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
      rw [hgt]
    rw [this]
    exact sub_mem_commSpace T _
  have hnormL : ∀ g : closure S.DbarAsc, g * mkL ht * g⁻¹ = mkL ht →
      ∀ w ∈ Ah.subgroupOf (closure S.DbarAsc), g * w * g⁻¹ ∈ Ah.subgroupOf (closure S.DbarAsc) := by
    intro g hg w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    have hgt : (g : S.O) * t = t * g := by
      have := congrArg Subtype.val (show g * mkL ht = mkL ht * g by
        calc g * mkL ht = g * mkL ht * g⁻¹ * g := by group
          _ = mkL ht * g := by rw [hg])
      exact this
    exact hnormO g g.2 hgt w hw
  have hW := AS35Z.eq_one_or_eq_of_normalized_L hD h.two_le ψ
    (fun u hu huu => h.center_pow hu (j := 1) (by rw [pow_one, _root_.sq, huu])) ht
    (W := Ah.subgroupOf (closure S.DbarAsc))
    (fun w hw => Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.1 hw)))
    (Subgroup.mem_subgroupOf.2 htAh) hnormL
  have hAhle : Ah ≤ zpowers t := by
    intro p hp
    have hpL : p ∈ closure S.DbarAsc := hP.le ((hmemAh p).1 hp).1
    rcases hW ⟨p, hpL⟩ (Subgroup.mem_subgroupOf.2 hp) with h1 | h1
    · rw [show p = 1 from congrArg Subtype.val h1]
      exact one_mem _
    · rw [show p = t from congrArg Subtype.val h1]
      exact mem_zpowers t
  have hcardAh : Nat.card Ah ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hAhle
    rwa [Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq, ht2])
      (fun h1 => (h.isTypeA ht).2.1 (by rw [h1]; rfl))] at h1
  obtain ⟨A, hA⟩ : ∃ A : Submodule (ZMod 2) S.Qt, A = U ⊓ fixSpace T := ⟨_, rfl⟩
  have hpA : ∀ p ∈ P, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ A := fun p hp => by
    rw [hA]
    exact Submodule.mem_inf.2 ⟨U.sub_mem (hPU hp x₀ hx₀).1 hx₀,
      sub_mem_fixSpace_of_triv (hP.triv p hp) x₀⟩
  have hfixBs : ∀ p ∈ P, ∀ w ∈ A, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Bs := by
    intro p hp w hwA
    rw [hA] at hwA
    obtain ⟨hwU, hwf⟩ := Submodule.mem_inf.1 hwA
    exact hmkBs _ (hP.fix p hp w hwf) (U.sub_mem (hPU hp w hwU).1 hwU)
  have hker : ∀ p : P, zuMoveHom P A Bs x₀ hpA hfixBs p = 1 → (p : S.O) ∈ Ah := by
    intro p hp1
    have hp0 : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ Bs := zuMoveHom_eq_one hp1
    refine (hmemAh _).2 ⟨p.2, fun x hx => ?_⟩
    by_cases hTx : T x - x = 0
    · exact hfixBs p p.2 x (by
        rw [hA]; exact Submodule.mem_inf.2 ⟨hx, mem_fixSpace.2 (sub_eq_zero.1 hTx)⟩)
    · have hTx' : T x - x = u := (hBs2 _ (hmkBs _ (sub_mem_commSpace T x)
        (U.sub_mem (hU t ht x hx) hx))).resolve_left hTx
      have hsum : x + x₀ ∈ A := by
        rw [hA]
        refine Submodule.mem_inf.2 ⟨U.add_mem hx hx₀, mem_fixSpace.2 ?_⟩
        have e1 : T x = x + u := by rw [← hTx']; abel
        have e2 : T x₀ = x₀ + u := by rw [hu]; abel
        rw [map_add, e1, e2]
        have h2 : u + u = 0 := by
          rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
        linear_combination (norm := module) h2
      have h3 := hfixBs p p.2 _ hsum
      have e : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
          ((p : S.Qt ≃ₗ[ZMod 2] S.Qt) (x + x₀) - (x + x₀)) -
            ((p : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) := by
        rw [map_add]; abel
      rw [e]
      exact Bs.sub_mem h3 hp0
  have hcardP : Nat.card P ≤ Nat.card Ah * Nat.card (A ⧸ Bs.comap A.subtype) :=
    card_le_of_zuMoveHom hker
  have hAquot := Submodule.card_eq_card_quotient_mul_card (Bs.comap A.subtype)
  have huA : u ∈ A := by
    rw [hA]
    exact Submodule.mem_inf.2 ⟨hBsU huBs,
      commSpace_le_fixSpace (h.isTypeA ht).2.2.1 (hBsc huBs)⟩
  have hB'pos : 2 ≤ Nat.card (Bs.comap A.subtype) := by
    have hne : Bs.comap A.subtype ≠ ⊥ := by
      intro hbot
      have : (⟨u, huA⟩ : A) ∈ Bs.comap A.subtype := huBs
      rw [hbot, Submodule.mem_bot] at this
      exact hu0 (congrArg Subtype.val this)
    have h1 : 1 ≤ finrank (ZMod 2) (Bs.comap A.subtype) := by
      rw [Submodule.one_le_finrank_iff]
      exact hne
    rw [card_eq_two_pow_finrank_zmod2 (Bs.comap A.subtype)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2) (Bs.comap A.subtype) := Nat.pow_le_pow_right (by norm_num) h1
  have hUorth : U ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin U := by
    intro x hx
    rw [OrthoF2.mem_orthogonal_iff_polar]
    exact fun y hy => hUiso x hx y hy
  have hdimU : finrank (ZMod 2) U ≤ k + 2 := by
    have h1 := Submodule.finrank_mono hUorth
    have h2 := finrank_add_finrank_orthogonal_Qt (S := S) U
    rw [S.finrank_Qt_eq_two_mul_width, hw] at h2
    omega
  have hAU : A < U := by
    rw [hA]
    refine lt_of_le_of_ne inf_le_left fun heq => hu0 ?_
    have : x₀ ∈ U ⊓ fixSpace T := by rw [heq]; exact hx₀
    rw [hu]
    exact sub_eq_zero.2 (mem_fixSpace.1 (Submodule.mem_inf.1 this).2)
  have hdimA := Submodule.finrank_lt_finrank_of_lt hAU
  rw [card_eq_two_pow_finrank_zmod2 A] at hAquot
  have hPcard := hP.card
  rw [hw] at hPcard
  have key : 2 ^ (2 * (k + 2) - 3) * 2 ≤ 2 * 2 ^ finrank (ZMod 2) A := by
    calc 2 ^ (2 * (k + 2) - 3) * 2 ≤ Nat.card P * Nat.card (Bs.comap A.subtype) := by
          rw [hPcard]; exact Nat.mul_le_mul_left _ hB'pos
      _ ≤ Nat.card Ah * Nat.card (A ⧸ Bs.comap A.subtype) * Nat.card (Bs.comap A.subtype) :=
          Nat.mul_le_mul_right _ hcardP
      _ = Nat.card Ah * (Nat.card (Bs.comap A.subtype) * Nat.card (A ⧸ Bs.comap A.subtype)) := by
          ring
      _ = Nat.card Ah * 2 ^ finrank (ZMod 2) A := by rw [← hAquot]
      _ ≤ 2 * 2 ^ finrank (ZMod 2) A := Nat.mul_le_mul_right _ hcardAh
  have key2 : 2 ^ (2 * (k + 2) - 3) ≤ 2 ^ (k + 1) := by
    have h1 : 2 ^ (2 * (k + 2) - 3) ≤ 2 ^ finrank (ZMod 2) A := by
      rw [mul_comm] at key
      exact Nat.le_of_mul_le_mul_left key (by norm_num)
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 key2
  omega

end ZUHyp

end Setting

end CFSG.LargeExtraspecial
