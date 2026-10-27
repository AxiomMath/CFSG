module

public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped commutatorElement

section Unitary

@[expose] def heldGU (a : ℕ) (M : Type) [Field M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x) :
    Subgroup (GL (Fin a) M) where
  carrier := {A | ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1}
  mul_mem' := by
    intro A B hA hB
    have hA' : ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1 := hA
    have hB' : ((B : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (B : Matrix (Fin a) (Fin a) M) = 1 := hB
    have hmapmul : ∀ X Y : Matrix (Fin a) (Fin a) M, (X * Y).map τ = X.map τ * Y.map τ :=
      fun X Y => Matrix.map_mul (f := τ.toRingHom)
    show ((((A * B : GL (Fin a) M)) : Matrix (Fin a) (Fin a) M).map τ)ᵀ *
      ((A * B : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = 1
    rw [Units.val_mul, hmapmul, Matrix.transpose_mul, mul_assoc,
      ← mul_assoc (((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ), hA', one_mul, hB']
  one_mem' := by
    show (((1 : GL (Fin a) M) : Matrix (Fin a) (Fin a) M).map τ)ᵀ *
      ((1 : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one,
      Matrix.one_mul]
  inv_mem' := by
    intro A hA
    have hA' : ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1 := hA
    show ((((A⁻¹ : GL (Fin a) M)) : Matrix (Fin a) (Fin a) M).map τ)ᵀ *
      ((A⁻¹ : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = 1
    rw [Matrix.coe_units_inv]
    have hNinv := Matrix.inv_eq_left_inv hA'
    have hNN : (A : Matrix (Fin a) (Fin a) M) * (A : Matrix (Fin a) (Fin a) M)⁻¹ = 1 := by
      rw [← Matrix.coe_units_inv]
      exact Units.mul_inv A
    have hmap : ((A : Matrix (Fin a) (Fin a) M)⁻¹).map τ = (A : Matrix (Fin a) (Fin a) M)ᵀ := by
      rw [hNinv, Matrix.transpose_map, Matrix.map_map]
      have hid : (⇑τ ∘ ⇑τ) = id := funext hτ
      rw [hid, Matrix.map_id]
    rw [hmap, Matrix.transpose_transpose]
    exact hNN

theorem mem_heldGU {a : ℕ} {M : Type} [Field M] {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}
    {A : GL (Fin a) M} :
    A ∈ heldGU a M τ hτ ↔ ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1 :=
  Iff.rfl

@[expose] def heldSU (a : ℕ) (M : Type) [Field M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x) :
    Subgroup (GL (Fin a) M) :=
  heldGU a M τ hτ ⊓ StatedSL a M

theorem commutatorElement_mem_heldSU {a : ℕ} {M : Type} [Field M] {τ : M ≃+* M}
    {hτ : ∀ x, τ (τ x) = x} {x y : GL (Fin a) M} (hx : x ∈ heldGU a M τ hτ)
    (hy : y ∈ heldGU a M τ hτ) : ⁅x, y⁆ ∈ heldSU a M τ hτ := by
  refine Subgroup.mem_inf.mpr ⟨?_, commutatorElement_mem_statedSL x y⟩
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem mul_comm_GL_of_le_one {M : Type} [Field M] {a : ℕ} (ha : a ≤ 1) (x y : GL (Fin a) M) :
    x * y = y * x := by
  interval_cases a
  · exact Units.ext (Subsingleton.elim _ _)
  · apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]

end Unitary

theorem not_isQuasisimple_of_mulEquiv {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    (h : ∀ x y : Γ', x * y = y * x) : ¬ CFSG.Open.IsQuasisimple Γ :=
  not_isQuasisimple_of_comm fun x y => e.injective (by rw [map_mul, map_mul]; exact h _ _)

theorem comap_equiv_of_injective_le_range {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (T : Subgroup G') (hT : T ≤ f.range) :
    Nonempty (↥(T.comap f) ≃* ↥T) :=
  ⟨(Subgroup.equivMapOfInjective (T.comap f) f hf).trans
    (MulEquiv.subgroupCongr (by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hT]))⟩

theorem triv_comap {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (T : Subgroup G') (hT : T ≤ f.range)
    (hTt : ∀ X : Subgroup T, CFSG.Open.IsComponentOf X ⊤ → X = ⊤) :
    ∀ X : Subgroup (T.comap f), CFSG.Open.IsComponentOf X ⊤ → X = ⊤ := by
  intro X hX
  obtain ⟨e⟩ := comap_equiv_of_injective_le_range f hf T hT
  have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e X).2 hX
  exact eq_top_of_map_equiv_eq_top e X (hTt _ hXe)

@[expose] def SUComponentsTrivial : Prop :=
  ∀ (a Q : ℕ) (M : Type) [Field M] [Finite M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
    Nat.card M = Q ^ 2 → (∀ x, τ x = x ^ Q) →
      ∀ X : Subgroup (heldSU a M τ hτ), IsComponentOf X ⊤ → X = ⊤

@[expose] def UnitaryOrLinearBlock (Q : ℕ) (Γ : Type) [Group Γ] : Prop :=
  (∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
      Odd d ∧ (∀ x : M, τ x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
        Nonempty (Γ ≃* heldGU a M τ hτ)) ∨
  (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M),
      Nat.card M = Q ^ (2 * e) ∧ Nonempty (Γ ≃* GL (Fin b) M))

@[expose] def UnitaryCentralizerDecomposition : Prop :=
  ∀ (Q n : ℕ) (L : Type) [Field L] [Finite L] (τ : L ≃+* L) (hτ : ∀ x, τ (τ x) = x)
    (s : GL (Fin n) L), Nat.card L = Q ^ 2 → (∀ x, τ x = x ^ Q) → s ∈ heldSU n L τ hτ →
      (orderOf s : L) ≠ 0 →
      ∃ (r : ℕ) (H : Fin r → Type) (_ : ∀ k, Group (H k)) (_ : ∀ k, Finite (H k)),
        (∀ k, UnitaryOrLinearBlock Q (H k)) ∧
          Nonempty (↥(Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ) ≃*
            ∀ k, H k)

theorem mulSingle_injective' {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] (i : ι) :
    Function.Injective (MonoidHom.mulSingle H i) := fun a b hab => by
  have := congrFun hab i
  simpa [MonoidHom.mulSingle_apply] using this

theorem component_eq_factor_image {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ i, Group (H i)] [Finite ι] [∀ i, Finite (H i)] (S : ∀ i, Subgroup (H i))
    (hS : ∀ i (a b : H i), ⁅a, b⁆ ∈ S i)
    (hSt : ∀ i (X : Subgroup (S i)), IsComponentOf X ⊤ → X = ⊤)
    {J : Subgroup (∀ j, H j)} (hJ : IsComponentOf J ⊤) :
    ∃ i, J = (S i).map (MonoidHom.mulSingle H i) := by
  obtain ⟨i, hi⟩ := exists_factor_of_isComponentOf_top (H := H) hJ
  refine ⟨i, ?_⟩
  have hle : J ≤ (S i).map (MonoidHom.mulSingle H i) := by
    have h1 := commutator_eq_self_of_isComponentOf_top hJ
    have h2 := Subgroup.commutator_mono hi hi
    rw [h1] at h2
    exact h2.trans (commutator_factorSub_le (H := H) (S i) (hS i))
  have hms := mulSingle_injective' (H := H) i
  have hX : IsComponentOf (J.subgroupOf ((S i).map (MonoidHom.mulSingle H i))) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hJ hle
  let e : ↥((S i).map (MonoidHom.mulSingle H i)) ≃* ↥(S i) :=
    (Subgroup.equivMapOfInjective (S i) (MonoidHom.mulSingle H i) hms).symm
  have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
  have htop := hSt i _ hXe
  have hXtop := eq_top_of_map_equiv_eq_top e _ htop
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp hXtop)

theorem exists_blockSub {Γ : Type} [Group Γ] {Q : ℕ} (hSU0 : SUComponentsTrivial)
    (hSL0 : SLComponentsTrivial) (hΓ : UnitaryOrLinearBlock Q Γ) :
    ∃ S : Subgroup Γ, (∀ x y : Γ, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ((∃ (a : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M)
          (hτ : ∀ x, τ (τ x) = x), Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nonempty (S ≃* StatedSL b M))) := by
  have hSU : ∀ (a Q : ℕ) (M : Type) [Field M] [Finite M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
      Nat.card M = Q ^ 2 → (∀ x, τ x = x ^ Q) →
        ∀ X : Subgroup (heldSU a M τ hτ), IsComponentOf X ⊤ → X = ⊤ := hSU0
  have hSL : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ := hSL0
  rcases hΓ with ⟨a, d, M, hMF, hMfin, τ, hτ, _hodd, hτQ, hcard, ⟨ε⟩⟩ | ⟨b, e, M, hMF, hMfin, hcard, ⟨ε⟩⟩
  ·
    let f : Γ →* GL (Fin a) M := (heldGU a M τ hτ).subtype.comp ε.toMonoidHom
    have hf : Function.Injective f := fun x y h => ε.injective (Subtype.ext h)
    have hle : heldSU a M τ hτ ≤ f.range := by
      intro x hx
      have hxG : x ∈ heldGU a M τ hτ := (Subgroup.mem_inf.mp hx).1
      refine MonoidHom.mem_range.mpr ⟨ε.symm ⟨x, hxG⟩, ?_⟩
      simp [f]
    refine ⟨(heldSU a M τ hτ).comap f, ?_, ?_, Or.inl ⟨a, M, hMF, hMfin, τ, hτ, ?_⟩⟩
    · intro x y
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutatorElement_mem_heldSU (ε x).2 (ε y).2
    · exact triv_comap f hf _ hle (fun X hX => hSU a (Q ^ d) M τ hτ hcard hτQ X hX)
    · obtain ⟨eS⟩ := comap_equiv_of_injective_le_range f hf _ hle
      exact ⟨eS⟩
  ·
    let f : Γ →* GL (Fin b) M := ε.toMonoidHom
    have hf : Function.Injective f := ε.injective
    have hle : StatedSL b M ≤ f.range := by
      intro x _
      exact MonoidHom.mem_range.mpr ⟨ε.symm x, by simp [f]⟩
    refine ⟨(StatedSL b M).comap f, ?_, ?_, Or.inr ⟨b, M, hMF, hMfin, ?_⟩⟩
    · intro x y
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutatorElement_mem_statedSL _ _
    · exact triv_comap f hf _ hle (fun X hX => hSL b M X hX)
    · obtain ⟨eS⟩ := comap_equiv_of_injective_le_range f hf _ hle
      exact ⟨eS⟩

theorem held_unitary_components (hSU : SUComponentsTrivial) (hSL : SLComponentsTrivial)
    (hdec : UnitaryCentralizerDecomposition) {Q n : ℕ} {L : Type} [Field L] [Finite L]
    (τ : L ≃+* L) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2) (s : GL (Fin n) L) (hs : s ∈ heldSU n L τ hτ)
    (hord : (orderOf s : L) ≠ 0) (J : Subgroup (GL (Fin n) L))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    (∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
        (hτ' : ∀ x, τ' (τ' x) = x), 2 ≤ a ∧
      Nonempty (J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸
        Subgroup.center (heldSU a E τ' hτ'))) ∨
    (∃ (b : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL b E))) := by
  obtain ⟨r, H, hgrp, hfinH, hblk, ⟨ε⟩⟩ := hdec Q n L τ hτ s hL hτQ hs hord
  have hbl : ∀ k, ∃ S : Subgroup (H k), (∀ x y : H k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ((∃ (a : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M)
          (hτ : ∀ x, τ (τ x) = x), Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nonempty (S ≃* StatedSL b M))) :=
    fun k => exists_blockSub hSU hSL (hblk k)
  choose S hS hSt hty using hbl
  let C : Subgroup (GL (Fin n) L) := Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ
  let ψ : (∀ k, H k) →* GL (Fin n) L := C.subtype.comp ε.symm.toMonoidHom
  have hψinj : Function.Injective ψ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hrange : ψ.range = C := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (ε.symm w).2
    · intro hx
      refine ⟨ε ⟨x, hx⟩, ?_⟩
      simp [ψ]
  have hJle : J ≤ ψ.range := by
    rw [hrange]
    exact hJ.1
  have hJmap : (J.comap ψ).map ψ = J := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hJle]
  have hJ'top : IsComponentOf (J.comap ψ) ⊤ := by
    apply isComponentOf_of_map_injective ψ hψinj
    rw [hJmap, ← MonoidHom.range_eq_map, hrange]
    exact hJ
  obtain ⟨k, hk⟩ := component_eq_factor_image S hS hSt hJ'top
  have hJeq : J = ((S k).map (MonoidHom.mulSingle H k)).map ψ := by
    rw [← hk, hJmap]
  have hms := mulSingle_injective' (H := H) k
  obtain ⟨e1⟩ : Nonempty (↥J ≃* ↥(S k)) := ⟨(MulEquiv.subgroupCongr hJeq).trans
    (((Subgroup.equivMapOfInjective _ ψ hψinj).symm).trans
      ((Subgroup.equivMapOfInjective (S k) (MonoidHom.mulSingle H k) hms).symm))⟩
  rcases hty k with ⟨a, M, hMF, hMfin, τM, hτM, ⟨eS⟩⟩ | ⟨b, M, hMF, hMfin, ⟨eS⟩⟩
  ·
    let e : ↥J ≃* ↥(heldSU a M τM hτM) := e1.trans eS
    by_cases ha2 : 2 ≤ a
    · left
      exact ⟨a, M, hMF, hMfin, τM, hτM, ha2,
        ⟨QuotientGroup.congr (Subgroup.center J) (Subgroup.center (heldSU a M τM hτM)) e
          (Subgroup.map_center_eq e)⟩⟩
    · exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv e fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (by omega) (x : GL (Fin a) M) (y : GL (Fin a) M)))
  ·
    let e : ↥J ≃* ↥(StatedSL b M) := e1.trans eS
    by_cases hb2 : 2 ≤ b
    · right
      exact ⟨b, M, hMF, hMfin, hb2, nonempty_quotientCenter_equiv_statedProj e⟩
    · exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv e fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (by omega) (x : GL (Fin b) M) (y : GL (Fin b) M)))

end CFSG.LieType.SemisimpleCentralizers.Held

end
