module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRoot
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelPieces
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldSL2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (mem_closure_sl2)
open scoped MatrixGroups

section Rigid

variable {K : Type} [Field K] {F : Type} [Field F]

theorem specialLinearMap_sl2Upper {R : Type} [Field R] (f : K →+* R) (c : K) :
    SpecialLinearGroup.map f (sl2Upper c) = sl2Upper (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Steinberg.coe_sl2Upper]

theorem specialLinearMap_sl2Lower {R : Type} [Field R] (f : K →+* R) (c : K) :
    SpecialLinearGroup.map f (sl2Lower c) = sl2Lower (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Steinberg.coe_sl2Lower]

theorem apply_apply_of_eq_one_or_eq {σ ρ : F ≃+* F} (hσ : orderOf σ = 2) (hρ : ρ = 1 ∨ ρ = σ)
    (a : F) : ρ (ρ a) = a := by
  rcases hρ with h | h
  · rw [h]
    rfl
  · have h2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    rw [h]
    change (σ * σ) a = a
    rw [h2]
    rfl

theorem apply_comm_of_eq_one_or_eq {σ ρ : F ≃+* F} (hρ : ρ = 1 ∨ ρ = σ) (a : F) :
    σ (ρ a) = ρ (σ a) := by
  rcases hρ with h | h
  · rw [h]
    rfl
  · rw [h]

theorem specialLinearMap_map_of_eq_one_or_eq {σ ρ : F ≃+* F} (hσ : orderOf σ = 2)
    (hρ : ρ = 1 ∨ ρ = σ) (A : SL(2, F)) :
    SpecialLinearGroup.map ρ.toRingHom (SpecialLinearGroup.map ρ.toRingHom A) = A := by
  ext i j
  simp [apply_apply_of_eq_one_or_eq hσ hρ]

theorem specialLinearMap_comm_of_eq_one_or_eq {σ ρ : F ≃+* F} (hρ : ρ = 1 ∨ ρ = σ)
    (A : SL(2, F)) :
    SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map ρ.toRingHom A) =
      SpecialLinearGroup.map ρ.toRingHom (SpecialLinearGroup.map σ.toRingHom A) := by
  ext i j
  simp [apply_comm_of_eq_one_or_eq hρ]

variable [Finite F] [CharP F 2]

theorem exists_eq_map_of_forall_fix {ι : K →+* F} {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (θ : MulAut SL(2, F))
    (hθ : ∀ A : SL(2, K), θ (SpecialLinearGroup.map ι A) = SpecialLinearGroup.map ι A) :
    ∃ ρ : F ≃+* F, (ρ = 1 ∨ ρ = σ) ∧ ∀ A : SL(2, F), θ A = SpecialLinearGroup.map ρ.toRingHom A := by
  have hU : ∀ c : K, θ (sl2Upper (ι c)) = sl2Upper (ι c) := fun c => by
    rw [← specialLinearMap_sl2Upper]
    exact hθ _
  have hL : ∀ c : K, θ (sl2Lower (ι c)) = sl2Lower (ι c) := fun c => by
    rw [← specialLinearMap_sl2Lower]
    exact hθ _
  obtain ⟨ρ, hρι, hρ⟩ := CFSG.SeitzReduction.E8Pilot.exists_ringEquiv_of_forall_sl2_of_charTwo ι θ hU hL
  have hρσ : ρ = 1 ∨ ρ = σ := F4Pilot.eq_one_or_eq_of_forall_fixSubfield hσ fun c => by
    obtain ⟨d, hd⟩ := (hfix c).1 c.2
    rw [← hd, hρι]
  refine ⟨ρ, hρσ, fun A => ?_⟩
  have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus θ.toMonoidHom (SpecialLinearGroup.map ρ.toRingHom) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change θ (sl2Upper c) = SpecialLinearGroup.map ρ.toRingHom (sl2Upper c)
      rw [(hρ c).1, specialLinearMap_sl2Upper]
      rfl
    · change θ (sl2Lower c) = SpecialLinearGroup.map ρ.toRingHom (sl2Lower c)
      rw [(hρ c).2, specialLinearMap_sl2Lower]
      rfl
  exact hle (mem_closure_sl2 A)

theorem exists_eq_comp_map_of_range_eq {G : Type*} [Group G] {ι : K →+* F} {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {α β : SL(2, F) →* G}
    (hα : Function.Injective α) (hβ : Function.Injective β) (hr : α.range = β.range)
    (hαβ : ∀ A : SL(2, K), α (SpecialLinearGroup.map ι A) = β (SpecialLinearGroup.map ι A)) :
    ∃ ρ : F ≃+* F, (ρ = 1 ∨ ρ = σ) ∧ ∀ A : SL(2, F), α A = β (SpecialLinearGroup.map ρ.toRingHom A) := by
  set θ : MulAut SL(2, F) := ((MonoidHom.ofInjective hα).trans (MulEquiv.subgroupCongr hr)).trans
    (MonoidHom.ofInjective hβ).symm with hθdef
  have hθ : ∀ A, β (θ A) = α A := by
    intro A
    have h := (MonoidHom.ofInjective hβ).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hα A))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hfixθ : ∀ A : SL(2, K), θ (SpecialLinearGroup.map ι A) = SpecialLinearGroup.map ι A :=
    fun A => hβ ((hθ _).trans (hαβ A))
  obtain ⟨ρ, hρ, hθρ⟩ := exists_eq_map_of_forall_fix hσ hfix θ hfixθ
  exact ⟨ρ, hρ, fun A => by rw [← hθ A, hθρ]⟩

end Rigid

section SiegelRoot

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

theorem simpleRootHom_mem_siegelLevi {j : Fin n} (h : j.val + 1 < n) (A : SL(2, F)) :
    simpleRootHom F j A ∈ siegelLevi F n :=
  siegelBlock_le_siegelLevi _ (simpleRootSL2_le_siegelBlock h ⟨A, rfl⟩)

theorem siegelBlock_pair_eq_simpleRootSL2' [Finite F] {j : Fin n} (h : j.val + 1 < n) :
    siegelBlock F {j, ⟨j.val + 1, h⟩} = simpleRootSL2 F j := by
  rw [← filter_pair_eq h, siegelBlock_pair_eq_simpleRootSL2 h]

@[expose] noncomputable def SiegelFieldParam.rootHom (S : SiegelFieldParam e t ι σ) {j : Fin n}
    (h : j.val + 1 < n) : SL(2, F) →* G :=
  S.Φ.comp ((simpleRootHom F j).codRestrict _ (simpleRootHom_mem_siegelLevi h))

variable (S : SiegelFieldParam e t ι σ) {j : Fin n} (h : j.val + 1 < n)

theorem SiegelFieldParam.rootHom_apply (A : SL(2, F)) :
    S.rootHom h A = S.Φ ⟨simpleRootHom F j A, simpleRootHom_mem_siegelLevi h A⟩ :=
  rfl

theorem SiegelFieldParam.rootHom_map (A : SL(2, K)) :
    S.rootHom h (SpecialLinearGroup.map ι A) = ((e.symm (simpleRootHom K j A) : L) : G) := by
  rw [← S.N1 _ (simpleRootHom_mem_siegelLevi h A), SiegelFieldParam.rootHom_apply]
  congr 1
  exact Subtype.ext (spFieldMap_simpleRootHom ι j A).symm

theorem SiegelFieldParam.conj_rootHom (A : SL(2, F)) :
    t * S.rootHom h A * t⁻¹ = S.rootHom h (SpecialLinearGroup.map σ.toRingHom A) := by
  rw [SiegelFieldParam.rootHom_apply, S.N3, SiegelFieldParam.rootHom_apply]
  congr 1
  apply Subtype.ext
  rw [coe_fieldSiegel_apply]
  exact spFieldMap_simpleRootHom σ.toRingHom j A

theorem SiegelFieldParam.range_rootHom [Finite G] [Finite F] (hK : 4 ≤ Nat.card K) :
    (S.rootHom h).range = pieceCore e ({j} : Finset (Fin n)) := by
  rw [S.pieceCore_singleton_eq_map hK h, siegelBlock_pair_eq_simpleRootSL2' h]
  ext y
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨⟨simpleRootHom F j A, simpleRootHom_mem_siegelLevi h A⟩, mem_subgroupOf.2 ⟨A, rfl⟩,
      rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨A, hA⟩ := mem_subgroupOf.1 hx
    refine ⟨A, ?_⟩
    rw [SiegelFieldParam.rootHom_apply]
    congr 1
    exact Subtype.ext hA

theorem SiegelFieldParam.injective_rootHom (hn : 3 ≤ n) : Function.Injective (S.rootHom h) := by
  set B : Finset (Fin n) := {j, ⟨j.val + 1, h⟩} with hBdef
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ B := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ B := fun x _ => hall x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, hBdef, card_pair_succ h] at this
    omega
  have hinj := S.injective_siegelBlock hk
  intro A A' hAA'
  have hmem : ∀ A : SL(2, F), simpleRootHom F j A ∈ siegelBlock F B := fun A => by
    rw [hBdef]
    exact simpleRootSL2_le_siegelBlock h ⟨A, rfl⟩ |> fun hx => by
      rwa [filter_pair_eq h] at hx
  have h1 := @hinj ⟨⟨simpleRootHom F j A, simpleRootHom_mem_siegelLevi h A⟩,
      mem_subgroupOf.2 (hmem A)⟩
    ⟨⟨simpleRootHom F j A', simpleRootHom_mem_siegelLevi h A'⟩, mem_subgroupOf.2 (hmem A')⟩ hAA'
  exact simpleRootHom_injective j (congrArg Subtype.val (congrArg Subtype.val h1))

end SiegelRoot

end CFSG.SeitzReduction.SymplecticPilot
