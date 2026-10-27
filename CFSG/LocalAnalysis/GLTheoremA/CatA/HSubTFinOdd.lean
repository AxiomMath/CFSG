module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.SemisimpleCentralizers.Held Matrix
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open scoped commutatorElement

theorem exists_blockSub_odd {Γ : Type} [Group Γ] {Q : ℕ} (hSU0 : SUComponentsTrivial)
    (hSL0 : SLComponentsTrivial) (hΓ : UnitaryOrLinearBlock Q Γ) :
    ∃ S : Subgroup Γ, (∀ x y : Γ, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧ S.Normal ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
          Odd d ∧ (∀ x : M, τ x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
            Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nat.card M = Q ^ (2 * e) ∧
          Nonempty (S ≃* StatedSL b M))) := by
  have hSU : ∀ (a Q : ℕ) (M : Type) [Field M] [Finite M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
      Nat.card M = Q ^ 2 → (∀ x, τ x = x ^ Q) →
        ∀ X : Subgroup (heldSU a M τ hτ), IsComponentOf X ⊤ → X = ⊤ := hSU0
  have hSL : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ := hSL0
  rcases hΓ with ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ⟨ε⟩⟩ |
    ⟨b, e, M, hMF, hMfin, hcard, ⟨ε⟩⟩
  ·
    let f : Γ →* GL (Fin a) M := (heldGU a M τ hτ).subtype.comp ε.toMonoidHom
    have hf : Function.Injective f := fun x y h => ε.injective (Subtype.ext h)
    have hle : heldSU a M τ hτ ≤ f.range := by
      intro x hx
      have hxG : x ∈ heldGU a M τ hτ := (Subgroup.mem_inf.mp hx).1
      refine MonoidHom.mem_range.mpr ⟨ε.symm ⟨x, hxG⟩, ?_⟩
      simp [f]
    refine ⟨(heldSU a M τ hτ).comap f, ?_, ?_, ?_,
      Or.inl ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ?_⟩⟩
    · intro x y
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutatorElement_mem_heldSU (ε x).2 (ε y).2
    · exact triv_comap f hf _ hle (fun X hX => hSU a (Q ^ d) M τ hτ hcard hτQ X hX)
    · refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      exact heldSU_normal_in_heldGU hτ (f g) (ε g).2 (f x) hx
    · obtain ⟨eS⟩ := comap_equiv_of_injective_le_range f hf _ hle
      exact ⟨eS⟩
  ·
    let f : Γ →* GL (Fin b) M := ε.toMonoidHom
    have hf : Function.Injective f := ε.injective
    have hle : StatedSL b M ≤ f.range := by
      intro x _
      exact MonoidHom.mem_range.mpr ⟨ε.symm x, by simp [f]⟩
    refine ⟨(StatedSL b M).comap f, ?_, ?_, ?_, Or.inr ⟨b, e, M, hMF, hMfin, hcard, ?_⟩⟩
    · intro x y
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutatorElement_mem_statedSL _ _
    · exact triv_comap f hf _ hle (fun X hX => hSL b M X hX)
    · refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      exact (statedSL_normal_in_GL b M).conj_mem _ hx _
    · obtain ⟨eS⟩ := comap_equiv_of_injective_le_range f hf _ hle
      exact ⟨eS⟩

theorem held_unitary_components_gu_odd (hSU : SUComponentsTrivial) (hSL : SLComponentsTrivial)
    {Q n : ℕ} {L : Type} [Field L] [Finite L] {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x)
    (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2) (s : GL (Fin n) L)
    (hs : s ∈ heldGU n L τ hτ) (hord : (orderOf s : L) ≠ 0) (J : Subgroup (GL (Fin n) L))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    (∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x),
        2 ≤ a ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧ Odd dd ∧
        Nonempty (J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸
          Subgroup.center (heldSU a E τ' hτ'))) ∨
    (∃ (b e : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = Q ^ (2 * e) ∧
        Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL b E))) := by
  obtain ⟨r, H, hgrp, hfinH, hblk, ⟨ε⟩⟩ := centralizerDecomposition_gu hτ hτQ hL s hs hord
  have hbl : ∀ k, ∃ S : Subgroup (H k), (∀ x y : H k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧ S.Normal ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
          Odd d ∧ (∀ x : M, τ x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
            Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nat.card M = Q ^ (2 * e) ∧
          Nonempty (S ≃* StatedSL b M))) :=
    fun k => exists_blockSub_odd hSU hSL (hblk k)
  choose S hS hSt hSn hty using hbl
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
  rcases hty k with ⟨a, dd, M, hMF, hMfin, τM, hτM, hodd, hτMQ, hcardM, ⟨eS⟩⟩ |
    ⟨b, dd, M, hMF, hMfin, hcardM, ⟨eS⟩⟩
  ·
    let eJ : ↥J ≃* ↥(heldSU a M τM hτM) := e1.trans eS
    by_cases ha2 : 2 ≤ a
    · left
      exact ⟨a, dd, M, hMF, hMfin, τM, hτM, ha2, hτMQ, hcardM, hodd,
        ⟨QuotientGroup.congr (Subgroup.center J) (Subgroup.center (heldSU a M τM hτM)) eJ
          (Subgroup.map_center_eq eJ)⟩⟩
    · exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv eJ fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (by omega) (x : GL (Fin a) M) (y : GL (Fin a) M)))
  ·
    let eJ : ↥J ≃* ↥(StatedSL b M) := e1.trans eS
    by_cases hb2 : 2 ≤ b
    · right
      exact ⟨b, dd, M, hMF, hMfin, hb2, hcardM, nonempty_quotientCenter_equiv_statedProj eJ⟩
    · exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv eJ fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (by omega) (x : GL (Fin b) M) (y : GL (Fin b) M)))

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
