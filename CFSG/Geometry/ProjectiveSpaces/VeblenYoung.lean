module

public import CFSG.Geometry.ProjectiveSpaces.Coordinates
public import CFSG.Geometry.ProjectiveSpaces.LinearModel
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public section

open scoped LinearAlgebra.Projectivization
open Module

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} (G : ProjectiveSpace P)

theorem exists_isHyperplane {n : ℕ} (hn : 1 ≤ n) (hG : G.HasDimension n) :
    ∃ H, G.IsHyperplane H := by
  obtain ⟨⟨S, hS, hmono, hlast⟩, hmax⟩ := hG
  let i : Fin (n + 1) := ⟨n - 1, by omega⟩
  have hi : i < Fin.last n := Fin.mk_lt_mk.2 (by omega)
  have hSi : S i ⊂ Set.univ := by
    rw [← hlast]
    exact hmono hi
  refine ⟨S i, ⟨(hS i).1, ?_, fun p q hpq => ?_⟩⟩
  · obtain ⟨x, -, hx⟩ := Set.exists_of_ssubset hSi
    exact ⟨x, hx⟩
  by_cases hp : p ∈ S i
  · exact ⟨p, G.left_mem_line p q, hp⟩
  have hJ : G.join (S i) p = Set.univ := by
    by_contra hJ
    let T : Fin (n + 2) → Set P := fun j =>
      if h : j.val < n then S ⟨j.val, by omega⟩ else if j.val = n then G.join (S i) p
      else Set.univ
    have hT : G.IsSubspaceChain (n + 1) T := by
      refine ⟨fun j => ?_, ?_, ?_⟩
      · simp only [T]
        split_ifs
        · exact hS _
        · exact ⟨G.isSubspace_join (hS i).1 hp, ⟨p, G.mem_join_self (hS i).2 p⟩⟩
        · exact ⟨G.isSubspace_univ, ⟨p, Set.mem_univ p⟩⟩
      · rw [Fin.strictMono_iff_lt_succ]
        intro j
        have hj := j.isLt
        simp only [T, Fin.val_castSucc, Fin.val_succ]
        by_cases h1 : j.val + 1 < n
        · rw [dite_eq_left (by omega : j.val < n), dite_eq_left h1]
          exact hmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self _))
        by_cases h2 : j.val + 1 = n
        · rw [dite_eq_left (by omega : j.val < n), dite_eq_right h1, ite_eq_left h2]
          have hji : (⟨j.val, by omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp [i]; omega)
          rw [hji]
          exact Set.ssubset_iff_subset_ne.2 ⟨G.subset_join _ _,
            fun e => hp (by rw [e]; exact G.mem_join_self (hS i).2 p)⟩
        · rw [dite_eq_right (by omega : ¬ j.val < n), ite_eq_left (by omega : j.val = n),
            dite_eq_right h1, ite_eq_right h2]
          exact Set.ssubset_univ_iff.2 hJ
      · simp [T]
    have := hmax (n + 1) T hT
    omega
  have hq : q ∈ G.join (S i) p := by
    rw [hJ]
    exact Set.mem_univ q
  obtain ⟨s, hs, hqs⟩ := G.mem_join.1 hq
  refine ⟨s, ?_, hs⟩
  rw [G.line_eq_of_mem hqs (Ne.symm hpq)]
  exact G.right_mem_line p s

theorem exists_not_collinear {n : ℕ} (hn : 2 ≤ n) (hG : G.HasDimension n) :
    ∃ x y z : P, ¬ G.Collinear x y z := by
  obtain ⟨S, hS, hmono, -⟩ := hG.1
  let i₀ : Fin (n + 1) := ⟨0, by omega⟩
  let i₁ : Fin (n + 1) := ⟨1, by omega⟩
  let i₂ : Fin (n + 1) := ⟨2, by omega⟩
  have h01 : S i₀ < S i₁ := hmono (Fin.mk_lt_mk.2 (by norm_num))
  have h12 : S i₁ < S i₂ := hmono (Fin.mk_lt_mk.2 (by norm_num))
  obtain ⟨x₀, hx₀⟩ := (hS i₀).2
  obtain ⟨x₁, hx₁, hx₁0⟩ := Set.exists_of_ssubset h01
  obtain ⟨x₂, -, hx₂1⟩ := Set.exists_of_ssubset h12
  have hx₀₁ : x₀ ≠ x₁ := fun e => hx₁0 (e ▸ hx₀)
  exact ⟨x₀, x₁, x₂, fun h => hx₂1 ((hS i₁).1.line_subset (h01.le hx₀) hx₁
    ((G.collinear_iff_of_ne hx₀₁).1 h))⟩

section Opposite

variable (E : Type u) [DivisionRing E] (n : ℕ)

local instance : RingHomInvPair (RingEquiv.opOp E : E →+* Eᵐᵒᵖᵐᵒᵖ) (RingEquiv.opOp E).symm :=
  RingHomInvPair.of_ringEquiv _

local instance : RingHomInvPair ((RingEquiv.opOp E).symm : Eᵐᵒᵖᵐᵒᵖ →+* E) (RingEquiv.opOp E) :=
  RingHomInvPair.of_ringEquiv_symm _

@[expose] def opPiSemilinearEquiv :
    (Fin n → E) ≃ₛₗ[(RingEquiv.opOp E : E →+* Eᵐᵒᵖᵐᵒᵖ)] (Fin n → Eᵐᵒᵖ) where
  toFun v i := MulOpposite.op (v i)
  invFun w i := (w i).unop
  map_add' v w := by
    ext i
    simp
  map_smul' a v := by
    ext i
    simp
  left_inv v := by
    ext i
    simp
  right_inv w := by
    ext i
    simp

theorem exists_orderIso_submodule_opposite {V : Type u} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h : finrank E V = n) :
    ∃ e : Submodule E V ≃o Submodule Eᵐᵒᵖᵐᵒᵖ (Fin n → Eᵐᵒᵖ),
      ∀ U : Submodule E V, finrank Eᵐᵒᵖᵐᵒᵖ (e U) = finrank E U := by
  let e₁ : V ≃ₗ[E] (Fin n → E) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h, Module.finrank_fin_fun])
  let e₂ := e₁.trans (opPiSemilinearEquiv E n)
  refine ⟨Submodule.orderIsoMapComap e₂, fun U => ?_⟩
  rw [Submodule.orderIsoMapComap_apply]
  have := rank_eq_of_equiv_equiv (RingEquiv.opOp E) (e₂.submoduleMap U).toAddEquiv
    (RingEquiv.opOp E).bijective fun r m => (e₂.submoduleMap U).map_smulₛₗ r m
  unfold Module.finrank
  rw [this]

end Opposite

variable {G}

theorem exists_eq_line {ℓ : Set P} (hℓ : ℓ ∈ G.lines) : ∃ p q, p ≠ q ∧ ℓ = G.line p q := by
  obtain ⟨a, b, c, ha, hb, -, hab, -, -⟩ := G.exists_three ℓ hℓ
  exact ⟨a, b, hab, G.eq_line hℓ hab ha hb⟩

theorem IsModel.exists_veblenYoung {E V : Type u} [DivisionRing E] [AddCommGroup V] [Module E V]
    {ψ : P ≃ ℙ E V} (hψ : G.IsModel ψ) [FiniteDimensional E V] {n : ℕ}
    (hrank : finrank E V = n + 1) {x y : P} (hxy : x ≠ y) :
    ∃ φ : P ≃ {U : Submodule Eᵐᵒᵖᵐᵒᵖ (Fin (n + 1) → Eᵐᵒᵖ) // finrank Eᵐᵒᵖᵐᵒᵖ U = 1},
      (∀ ℓ ∈ G.lines, ∃ W : Submodule Eᵐᵒᵖᵐᵒᵖ (Fin (n + 1) → Eᵐᵒᵖ),
        finrank Eᵐᵒᵖᵐᵒᵖ W = 2 ∧
          φ '' ℓ = {U | U.1 ≤ W}) ∧
      (∀ W : Submodule Eᵐᵒᵖᵐᵒᵖ (Fin (n + 1) → Eᵐᵒᵖ), finrank Eᵐᵒᵖᵐᵒᵖ W = 2 →
        ∃! ℓ, ℓ ∈ G.lines ∧
          φ '' ℓ = {U | U.1 ≤ W}) ∧
      (Finite P → Finite Eᵐᵒᵖ ∧ (∀ ℓ ∈ G.lines, Nat.card ℓ = Nat.card Eᵐᵒᵖ + 1) ∧
        Nat.card P = (Nat.card Eᵐᵒᵖ ^ (n + 1) - 1) / (Nat.card Eᵐᵒᵖ - 1)) := by
  obtain ⟨e, he⟩ := exists_orderIso_submodule_opposite E (n + 1) (V := V) hrank
  have h1 : ∀ p, finrank Eᵐᵒᵖᵐᵒᵖ (e (ψ p).submodule) = 1 := fun p => by
    rw [he, Projectivization.finrank_submodule]
  let φ₀ : P → {U : Submodule Eᵐᵒᵖᵐᵒᵖ (Fin (n + 1) → Eᵐᵒᵖ) // finrank Eᵐᵒᵖᵐᵒᵖ U = 1} :=
    fun p => ⟨e (ψ p).submodule, h1 p⟩
  have hinj : Function.Injective φ₀ := fun p q h => ψ.injective
    (Projectivization.submodule_injective (e.injective (congrArg Subtype.val h)))
  have hsurj : Function.Surjective φ₀ := by
    rintro ⟨U, hU⟩
    have hU' : finrank E (e.symm U) = 1 := by rw [← he, e.apply_symm_apply, hU]
    refine ⟨ψ.symm (Projectivization.mk'' _ hU'), Subtype.ext ?_⟩
    simp only [φ₀, Equiv.apply_symm_apply, Projectivization.submodule_mk'',
      OrderIso.apply_symm_apply]
  let φ := Equiv.ofBijective φ₀ ⟨hinj, hsurj⟩
  have hfin2 : ∀ p q, p ≠ q → finrank E ↥((ψ p).submodule ⊔ (ψ q).submodule) = 2 := by
    intro p q hpq
    have hli : LinearIndependent E ![(ψ p).rep, (ψ q).rep] :=
      Projectivization.linearIndependent_pair_iff_ne.2 (ψ.injective.ne hpq)
    have hS : (ψ p).submodule ⊔ (ψ q).submodule =
        Submodule.span E (Set.range ![(ψ p).rep, (ψ q).rep]) := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Submodule.span_union, Projectivization.submodule_eq, Projectivization.submodule_eq]
    rw [hS, finrank_span_eq_card hli, Fintype.card_fin]
  have himage : ∀ p q, p ≠ q → φ '' G.line p q =
      {U | U.1 ≤ e ((ψ p).submodule ⊔ (ψ q).submodule)} := by
    intro p q hpq
    ext U
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact e.le_iff_le.2 ((hψ p q r hpq).1 hr)
    · intro hU
      refine ⟨φ.symm U, (hψ p q _ hpq).2 ?_, φ.apply_symm_apply U⟩
      have h' : (φ (φ.symm U) : Submodule Eᵐᵒᵖᵐᵒᵖ (Fin (n + 1) → Eᵐᵒᵖ)) ≤
          e ((ψ p).submodule ⊔ (ψ q).submodule) := by
        rw [φ.apply_symm_apply]
        exact hU
      exact e.le_iff_le.1 h'
  refine ⟨φ, fun ℓ hℓ => ?_, fun W hW => ?_, fun hfin => ?_⟩
  · obtain ⟨p, q, hpq, rfl⟩ := exists_eq_line hℓ
    exact ⟨_, by rw [he, hfin2 p q hpq], himage p q hpq⟩
  · have hS : finrank E (e.symm W) = 2 := by rw [← he, e.apply_symm_apply, hW]
    let b := Module.finBasisOfFinrankEq E (e.symm W) hS
    have hb0 : (b 0 : V) ≠ 0 := fun h => b.linearIndependent.ne_zero 0 (Subtype.ext h)
    have hb1 : (b 1 : V) ≠ 0 := fun h => b.linearIndependent.ne_zero 1 (Subtype.ext h)
    have hpq : ψ.symm (Projectivization.mk E (b 0 : V) hb0) ≠
        ψ.symm (Projectivization.mk E (b 1 : V) hb1) := by
      intro h
      have h' := ψ.symm.injective h
      rw [Projectivization.mk_eq_mk_iff'] at h'
      obtain ⟨a, ha⟩ := h'
      have hmem : b 0 ∈ Submodule.span E (b '' {1}) := by
        rw [Set.image_singleton, Submodule.mem_span_singleton]
        exact ⟨a, Subtype.ext ha⟩
      exact b.linearIndependent.notMem_span_image (by simp) hmem
    have hSpq : (ψ (ψ.symm (Projectivization.mk E (b 0 : V) hb0))).submodule ⊔
        (ψ (ψ.symm (Projectivization.mk E (b 1 : V) hb1))).submodule = e.symm W := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hfin2 _ _ hpq, hS])
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Projectivization.submodule_mk,
        Projectivization.submodule_mk, sup_le_iff, Submodule.span_singleton_le_iff_mem,
        Submodule.span_singleton_le_iff_mem]
      exact ⟨(b 0).2, (b 1).2⟩
    refine ⟨_, ⟨G.line_mem_lines hpq, ?_⟩, fun ℓ hℓ => ?_⟩
    · rw [himage _ _ hpq, hSpq, OrderIso.apply_symm_apply]
    · refine Set.image_injective.2 φ.injective ?_
      rw [hℓ.2, himage _ _ hpq, hSpq, OrderIso.apply_symm_apply]
  · have hli : LinearIndependent E ![(ψ x).rep, (ψ y).rep] :=
      Projectivization.linearIndependent_pair_iff_ne.2 (ψ.injective.ne hxy)
    rw [LinearIndependent.pair_iff] at hli
    have : Finite (ℙ E V) := Finite.of_equiv P ψ
    have hne : ∀ a : E, (ψ x).rep + a • (ψ y).rep ≠ 0 := fun a h =>
      one_ne_zero (hli 1 a (by rw [one_smul]; exact h)).1
    have hE : Finite E := by
      refine Finite.of_injective
        (fun a => Projectivization.mk E ((ψ x).rep + a • (ψ y).rep) (hne a)) fun a a' h => ?_
      simp only [Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c, hc⟩ := h
      have h0 : (c - 1) • (ψ x).rep + (c * a' - a) • (ψ y).rep = 0 := by
        rw [smul_add, smul_smul, ← sub_eq_zero] at hc
        rw [sub_smul, sub_smul, one_smul, ← hc]
        abel
      obtain ⟨h2, h3⟩ := hli _ _ h0
      rw [sub_eq_zero.1 h2, one_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hcardD : Nat.card Eᵐᵒᵖ = Nat.card E := (Nat.card_congr MulOpposite.opEquiv).symm
    have hq : 1 < Nat.card E := Finite.one_lt_card
    have hcard : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W] (k : ℕ),
        finrank E W = k → Nat.card W = Nat.card E ^ k := by
      intro W _ _ _ k hk
      rw [Nat.card_congr (LinearEquiv.ofFinrankEq W (Fin k → E)
        (by rw [hk, Module.finrank_fin_fun])).toEquiv, Nat.card_fun, Nat.card_fin]
    refine ⟨Finite.of_equiv E MulOpposite.opEquiv, fun ℓ hℓ => ?_, ?_⟩
    · obtain ⟨p, q, hpq, rfl⟩ := exists_eq_line hℓ
      set S := (ψ p).submodule ⊔ (ψ q).submodule with hS_def
      have hrange : ψ '' G.line p q =
          Set.range (Projectivization.map S.subtype S.injective_subtype) := by
        ext z
        constructor
        · rintro ⟨r, hr, rfl⟩
          have hmem : (ψ r).rep ∈ S := (hψ p q r hpq).1 hr (by
            rw [Projectivization.submodule_eq]
            exact Submodule.mem_span_singleton_self _)
          refine ⟨Projectivization.mk E ⟨(ψ r).rep, hmem⟩
            (fun h => (ψ r).rep_nonzero (congrArg Subtype.val h)), ?_⟩
          rw [Projectivization.map_mk]
          exact Projectivization.mk_rep _
        · rintro ⟨w, rfl⟩
          refine ⟨ψ.symm (Projectivization.map S.subtype S.injective_subtype w),
            (hψ p q _ hpq).2 ?_, ψ.apply_symm_apply _⟩
          rw [ψ.apply_symm_apply]
          induction w using Projectivization.ind with
          | h v hv =>
            rw [Projectivization.map_mk, Projectivization.submodule_mk,
              Submodule.span_singleton_le_iff_mem]
            exact v.2
      have hℓ' : Nat.card (G.line p q) = Nat.card (ℙ E S) := by
        rw [← Nat.card_image_of_injective ψ.injective, hrange,
          Nat.card_range_of_injective (Projectivization.map_injective _ _)]
      have h2 := Projectivization.card E S
      rw [hcard S 2 (hfin2 p q hpq)] at h2
      rw [hℓ', hcardD]
      obtain ⟨k, hk⟩ : ∃ k, Nat.card E = k + 1 := ⟨Nat.card E - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, show (k + 1) ^ 2 = (k + 1 + 1) * k + 1 by ring,
        Nat.add_sub_cancel] at h2
      rw [hk]
      exact (Nat.eq_of_mul_eq_mul_right (by omega) h2).symm
    · have h2 := Projectivization.card E V
      rw [hcard V (n + 1) hrank] at h2
      rw [Nat.card_congr ψ, hcardD]
      exact (Nat.div_eq_of_eq_mul_left (by omega) h2).symm

variable (G)

theorem veblen_young {n : ℕ} (hn : 3 ≤ n) (hG : G.HasDimension n) :
    ∃ (D : Type u) (_ : DivisionRing D)
      (φ : P ≃ {U : Submodule Dᵐᵒᵖ (Fin (n + 1) → D) // finrank Dᵐᵒᵖ U = 1}),
      (∀ ℓ ∈ G.lines, ∃ W : Submodule Dᵐᵒᵖ (Fin (n + 1) → D), finrank Dᵐᵒᵖ W = 2 ∧
        φ '' ℓ = {U | U.1 ≤ W}) ∧
      (∀ W : Submodule Dᵐᵒᵖ (Fin (n + 1) → D), finrank Dᵐᵒᵖ W = 2 →
        ∃! ℓ, ℓ ∈ G.lines ∧ φ '' ℓ = {U | U.1 ≤ W}) ∧
      (Finite P → Finite D ∧ (∀ ℓ ∈ G.lines, Nat.card ℓ = Nat.card D + 1) ∧
        Nat.card P = (Nat.card D ^ (n + 1) - 1) / (Nat.card D - 1)) := by
  obtain ⟨H, hH⟩ := G.exists_isHyperplane (by omega) hG
  have hA : G.AffineData H :=
    ⟨hH, fun _ _ _ h => G.exists_not_mem_plane hn hG h, G.exists_not_collinear (by omega) hG⟩
  obtain ⟨ψ, hψ⟩ := G.exists_coordinatization hA
  have hψ' : G.IsModel ψ := hψ
  obtain ⟨hfd, hrank⟩ := hψ'.finrank_eq hG
  obtain ⟨x, y, z, hxyz⟩ := hA.triangle
  exact ⟨(Scalar hA)ᵐᵒᵖ, inferInstance,
    hψ'.exists_veblenYoung hrank (G.ne_of_not_collinear hxyz).1⟩

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
