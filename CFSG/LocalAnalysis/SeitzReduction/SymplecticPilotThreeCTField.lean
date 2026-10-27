module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourOrth

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)
open scoped MatrixGroups

section Field

variable {K : Type} [Field K] {F : Type} [Field F]

theorem specialLinearMap_map_of_fix {ι : K →+* F} {ρ : F ≃+* F} (hρι : ∀ c, ρ (ι c) = ι c)
    (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map ρ.toRingHom (Matrix.SpecialLinearGroup.map ι A) =
      Matrix.SpecialLinearGroup.map ι A := by
  ext i j
  simp [hρι]

theorem fieldSp_simpleRootHom {n : ℕ} (σ : F ≃+* F) (j : Fin n) (A : SL(2, F)) :
    fieldSp n F σ (simpleRootHom F j A) =
      simpleRootHom F j (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  rw [F4Pilot.fieldSp_eq_statedSpMap, ← spFieldMap_eq_statedSpMap]
  exact spFieldMap_simpleRootHom (σ : F →+* F) j A

theorem fieldSiegel_simpleRootHom {n : ℕ} (ρ : F ≃+* F) {j : Fin n} (h : j.val + 1 < n)
    (A : SL(2, F)) :
    fieldSiegel ρ ⟨simpleRootHom F j A, simpleRootHom_mem_siegelLevi h A⟩ =
      ⟨simpleRootHom F j (Matrix.SpecialLinearGroup.map ρ.toRingHom A),
        simpleRootHom_mem_siegelLevi h _⟩ := by
  apply Subtype.ext
  rw [coe_fieldSiegel_apply]
  exact spFieldMap_simpleRootHom ρ.toRingHom j A

theorem range_comp_specialLinearMap {M : Type*} [Group M] {σ ρ : F ≃+* F} (hσ : orderOf σ = 2)
    (hρ : ρ = 1 ∨ ρ = σ) (φ : SL(2, F) →* M) :
    (φ.comp (Matrix.SpecialLinearGroup.map ρ.toRingHom)).range = φ.range := by
  ext z
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨A, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.map ρ.toRingHom A, ?_⟩
    change φ (Matrix.SpecialLinearGroup.map ρ.toRingHom
      (Matrix.SpecialLinearGroup.map ρ.toRingHom A)) = φ A
    rw [specialLinearMap_map_of_eq_one_or_eq hσ hρ]

end Field

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F]

theorem exists_injective_fieldRow_three_of_siegel (hK : 4 ≤ Nat.card K) {e : L ≃* StatedSp 3 K}
    {t : G} {ι : K →+* F} {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (P₀ : FieldNeighbourParam e t ι σ 0)
    (S : SiegelFieldParam e t ι σ)
    (hcomm : ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)),
      Commute a b) :
    ∃ ψ : StatedSp 3 F →* G, Function.Injective ψ ∧ ψ.range = spGlobal e ∧
      (∀ x : StatedSp 3 K, ψ (spFieldMap 3 ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp 3 F, t * ψ x * t⁻¹ = ψ (fieldSp 3 F σ x) := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hσι : ∀ c, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h1s : (1 : Fin 3).val + 1 < 3 → (0 : Fin 3).val ≠ (1 : Fin 3).val + 1 := fun _ => by decide
  have h2s : (2 : Fin 3).val + 1 < 3 → (0 : Fin 3).val ≠ (2 : Fin 3).val + 1 :=
    fun h => absurd h (by decide)
  have hj0 : (0 : Fin 3).val + 1 < 3 := by decide
  have hj1 : (1 : Fin 3).val + 1 < 3 := by decide
  have hu₁inj : Function.Injective (P₀.rootHom h01 h1s) := fun A B h =>
    simpleRootHom_injective (1 : Fin 3) (congrArg Subtype.val (P₀.injective h))
  obtain ⟨ρ, hρ, hs₁⟩ := exists_eq_comp_map_of_range_eq hσ hfix (S.injective_rootHom hj1 le_rfl)
    hu₁inj (by rw [S.range_rootHom hj1 hK, P₀.range_rootHom h01 h1s hK])
    (fun A => by rw [S.rootHom_map, P₀.rootHom_map])
  have hρι : ∀ c, ρ (ι c) = ι c := by
    intro c
    rcases hρ with h | h
    · rw [h]
      rfl
    · rw [h]
      exact hσι c
  set Φ' : siegelLevi F 3 →* G := S.Φ.comp (fieldSiegel ρ).toMonoidHom with hΦ'
  have hΦ'J : ∀ (j : Fin 3) (h : j.val + 1 < 3) (A : SL(2, F)),
      Φ' ⟨simpleRootHom F j A, simpleRootHom_mem_siegelLevi h A⟩ =
        S.rootHom h (Matrix.SpecialLinearGroup.map ρ.toRingHom A) := by
    intro j h A
    change S.Φ (fieldSiegel ρ ⟨simpleRootHom F j A, simpleRootHom_mem_siegelLevi h A⟩) = _
    rw [fieldSiegel_simpleRootHom ρ h A]
    rfl
  obtain ⟨ψ, hinj, hψ0, hψ1, hψ2⟩ := exists_injective_of_amalgam_three P₀.Φ P₀.injective Φ'
    (fun A => by
      rw [hΦ'J 1 hj1 A, hs₁, specialLinearMap_map_of_eq_one_or_eq hσ hρ]
      rfl)
    (fun A B => by
      rw [hΦ'J 0 hj0 A]
      refine hcomm _ ?_ _ ?_
      · rw [← S.range_rootHom hj0 hK]
        exact ⟨_, rfl⟩
      · rw [← P₀.range_rootHom h02 h2s hK]
        exact ⟨B, rfl⟩)
  have hψ0' : ∀ A, ψ (simpleRootHom F 0 A) =
      S.rootHom hj0 (Matrix.SpecialLinearGroup.map ρ.toRingHom A) := fun A =>
    (hψ0 A).trans (hΦ'J 0 hj0 A)
  have hψ1' : ∀ A, ψ (simpleRootHom F 1 A) = P₀.rootHom h01 h1s A := hψ1
  have hψ2' : ∀ A, ψ (simpleRootHom F 2 A) = P₀.rootHom h02 h2s A := hψ2
  refine ⟨ψ, hinj, ?_, ?_, ?_⟩
  ·
    have hmap : ∀ j : Fin 3, (simpleRootSL2 F j).map ψ = pieceCore e ({j} : Finset (Fin 3)) := by
      intro j
      rw [simpleRootSL2, ← MonoidHom.range_comp]
      obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      · rw [← S.range_rootHom hj0 hK, ← range_comp_specialLinearMap hσ hρ (S.rootHom hj0)]
        congr 1
        exact MonoidHom.ext hψ0'
      · rw [← P₀.range_rootHom h01 h1s hK]
        congr 1
        exact MonoidHom.ext hψ1'
      · rw [← P₀.range_rootHom h02 h2s hK]
        congr 1
        exact MonoidHom.ext hψ2'
    rw [MonoidHom.range_eq_map, ← iSup_simpleRootSL2_eq_top (show 1 ≤ 3 by omega),
      Subgroup.map_iSup, spGlobal]
    exact iSup_congr hmap
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp 3 K)) ≤
        MonoidHom.eqLocus (ψ.comp (spFieldMap 3 ι)) (L.subtype.comp e.symm.toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ 3 by omega), iSup_le_iff]
      intro j
      rintro _ ⟨A, rfl⟩
      change ψ (spFieldMap 3 ι (simpleRootHom K j A)) = ((e.symm (simpleRootHom K j A) : L) : G)
      rw [spFieldMap_simpleRootHom]
      obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      · rw [hψ0', specialLinearMap_map_of_fix hρι, S.rootHom_map]
      · rw [hψ1']
        exact P₀.rootHom_map h01 h1s A
      · rw [hψ2']
        exact P₀.rootHom_map h02 h2s A
    exact htop (mem_top x)
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp 3 F)) ≤
        MonoidHom.eqLocus ((MulAut.conj t).toMonoidHom.comp ψ)
          (ψ.comp (fieldSp 3 F σ).toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ 3 by omega), iSup_le_iff]
      intro j
      rintro _ ⟨A, rfl⟩
      change t * ψ (simpleRootHom F j A) * t⁻¹ = ψ (fieldSp 3 F σ (simpleRootHom F j A))
      rw [fieldSp_simpleRootHom]
      obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      · rw [hψ0', hψ0', S.conj_rootHom, specialLinearMap_comm_of_eq_one_or_eq hρ]
      · rw [hψ1', hψ1']
        exact P₀.conj_rootHom h01 h1s A
      · rw [hψ2', hψ2']
        exact P₀.conj_rootHom h02 h2s A
    exact htop (mem_top x)

end FieldRow

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F]

theorem exists_injective_fieldRow_three (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) (hsplit : OddCentralSplit (siegelLevi K 3))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ k : Fin 3, Nonempty (FieldNeighbourParam e t ι σ k)) :
    ∃ ψ : StatedSp 3 F →* G, Function.Injective ψ ∧ ψ.range = spGlobal e ∧
      (∀ x : StatedSp 3 K, ψ (spFieldMap 3 ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp 3 F, t * ψ x * t⁻¹ = ψ (fieldSp 3 F σ x) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  obtain ⟨S⟩ := nonempty_siegelFieldParam_of_fieldNeighbourParam hcat hdet hsplit hset hKc hf
    le_rfl e htC ht ι hσ1 hσσ hfix (hparam 2).some
  exact exists_injective_fieldRow_three_of_siegel hK4 hσ hfix (hparam 0).some S
    (commute_pieceCore_zero_two_three hset hKc hf e ht hKt ι hσ hfix hparam)

end Seitz

end CFSG.SeitzReduction.SymplecticPilot
