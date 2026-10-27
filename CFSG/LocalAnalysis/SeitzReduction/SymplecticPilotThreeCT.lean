module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCTRoot
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (rootDatum)
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

section Three

variable {F : Type} [Field F]

theorem simpleRootSL2_le_siegelLevi {n : ℕ} {j : Fin n} (h : j.val + 1 < n) :
    simpleRootSL2 F j ≤ siegelLevi F n := by
  rintro _ ⟨A, rfl⟩
  exact simpleRootHom_mem_siegelLevi h A

theorem simpleRootHom_zero_mem_siegelLevi_three (A : SL(2, F)) :
    simpleRootHom F (0 : Fin 3) A ∈ siegelLevi F 3 :=
  simpleRootHom_mem_siegelLevi (by decide) A

theorem simpleRootHom_one_mem_siegelLevi_three (A : SL(2, F)) :
    simpleRootHom F (1 : Fin 3) A ∈ siegelLevi F 3 :=
  simpleRootHom_mem_siegelLevi (by decide) A

theorem simpleRootHom_one_mem_spBlock_three (A : SL(2, F)) :
    simpleRootHom F (1 : Fin 3) A ∈ spBlock F ({0}ᶜ : Finset (Fin 3)) :=
  simpleRootHom_mem_spBlock (by decide) (fun _ => by decide) A

theorem simpleRootHom_two_mem_spBlock_three (A : SL(2, F)) :
    simpleRootHom F (2 : Fin 3) A ∈ spBlock F ({0}ᶜ : Finset (Fin 3)) :=
  simpleRootHom_mem_spBlock (by decide) (fun h => absurd h (by decide)) A

theorem commute_simpleRootSL2_zero_two_three :
    ∀ a ∈ simpleRootSL2 F (0 : Fin 3), ∀ b ∈ simpleRootSL2 F (2 : Fin 3), Commute a b := by
  intro a ha b hb
  exact commute_of_mem_spBlock_of_disjoint (I := {0, 1}) (J := {2}) (by decide)
    (simpleRootSL2_le_spBlock (by decide) (fun _ => by simp) ha)
    (simpleRootSL2_le_spBlock (by decide) (fun h => absurd h (by decide)) hb)

theorem simpleRootSL2_zero_inf_two_three :
    simpleRootSL2 F (0 : Fin 3) ⊓ simpleRootSL2 F (2 : Fin 3) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨ha, hb⟩
  have h1 := simpleRootSL2_le_spBlock (F := F) (N := ({0, 1} : Finset (Fin 3))) (by decide)
    (fun _ => by simp) ha
  have h2 := simpleRootSL2_le_spBlock (F := F) (N := ({2} : Finset (Fin 3))) (by decide)
    (fun h => absurd h (by decide)) hb
  exact mem_bot.2 (eq_one_of_isSupp_of_isSupp_compl h1
    (suppGroup_mono (planeCoords_subset_compl_of_disjoint (by decide)) h2))

theorem leviAmalgam_zero_two_three (J : {J : Finset (Fin 3) // J.card ≤ 2})
    (hJ : J.1 = {0, 2}) :
    (rootDatum 3 F).leviAmalgam J = simpleRootSL2 F (0 : Fin 3) ⊔ simpleRootSL2 F (2 : Fin 3) := by
  rw [leviAmalgam_eq_iSup, hJ, Finset.iSup_insert, Finset.iSup_singleton]

theorem eq_zero_two_three (J : Finset (Fin 3)) (hJ : J.card ≤ 2) (h0 : (0 : Fin 3) ∈ J)
    (h2 : (2 : Fin 3) ∈ J) : J = {0, 2} := by
  revert J
  decide

theorem subset_zero_one_three (J : Finset (Fin 3)) (hJ : J.card ≤ 2) (h02 : J ≠ {0, 2})
    (h0 : (0 : Fin 3) ∈ J) : J ⊆ {0, 1} := by
  revert J
  decide

theorem leviAmalgam_le_siegelLevi_three (J : {J : Finset (Fin 3) // J.card ≤ 2})
    (h02 : J.1 ≠ {0, 2}) (h0 : (0 : Fin 3) ∈ J.1) :
    (rootDatum 3 F).leviAmalgam J ≤ siegelLevi F 3 := by
  refine (leviAmalgam_eq_iSup J).le.trans (iSup₂_le fun j hj => ?_)
  have hj' := subset_zero_one_three J.1 J.2 h02 h0 hj
  refine simpleRootSL2_le_siegelLevi ?_
  rcases Finset.mem_insert.1 hj' with rfl | hj''
  · decide
  · rw [Finset.mem_singleton.1 hj'']
    decide

theorem leviAmalgam_le_spBlock_zero_three (J : {J : Finset (Fin 3) // J.card ≤ 2})
    (h0 : (0 : Fin 3) ∉ J.1) :
    (rootDatum 3 F).leviAmalgam J ≤ spBlock F ({0}ᶜ : Finset (Fin 3)) := by
  refine (leviAmalgam_eq_iSup J).le.trans (iSup₂_le fun j hj => ?_)
  exact simpleRootSL2_le_spBlock_compl' ⟨fun h => h0 (h ▸ hj), fun _ => by simp⟩

end Three

section Amalgam

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_injective_of_amalgam_three (Φ₀ : spBlock F ({0}ᶜ : Finset (Fin 3)) →* G)
    (hΦ₀ : Function.Injective Φ₀) (Φ' : siegelLevi F 3 →* G)
    (hagree : ∀ A : SL(2, F), Φ' ⟨simpleRootHom F 1 A, simpleRootHom_one_mem_siegelLevi_three A⟩ =
      Φ₀ ⟨simpleRootHom F 1 A, simpleRootHom_one_mem_spBlock_three A⟩)
    (hcomm : ∀ A B : SL(2, F),
      Commute (Φ' ⟨simpleRootHom F 0 A, simpleRootHom_zero_mem_siegelLevi_three A⟩)
        (Φ₀ ⟨simpleRootHom F 2 B, simpleRootHom_two_mem_spBlock_three B⟩)) :
    ∃ ψ : StatedSp 3 F →* G, Function.Injective ψ ∧
      (∀ A, ψ (simpleRootHom F 0 A) =
        Φ' ⟨simpleRootHom F 0 A, simpleRootHom_zero_mem_siegelLevi_three A⟩) ∧
      (∀ A, ψ (simpleRootHom F 1 A) =
        Φ₀ ⟨simpleRootHom F 1 A, simpleRootHom_one_mem_spBlock_three A⟩) ∧
      (∀ A, ψ (simpleRootHom F 2 A) =
        Φ₀ ⟨simpleRootHom F 2 A, simpleRootHom_two_mem_spBlock_three A⟩) := by
  classical
  have hJ0S : simpleRootSL2 F (0 : Fin 3) ≤ siegelLevi F 3 := simpleRootSL2_le_siegelLevi (by decide)
  have hJ2B : simpleRootSL2 F (2 : Fin 3) ≤ spBlock F ({0}ᶜ : Finset (Fin 3)) := by
    rintro _ ⟨A, rfl⟩
    exact simpleRootHom_two_mem_spBlock_three A
  set fA : simpleRootSL2 F (0 : Fin 3) →* G := Φ'.comp (Subgroup.inclusion hJ0S) with hfA
  set gB : simpleRootSL2 F (2 : Fin 3) →* G := Φ₀.comp (Subgroup.inclusion hJ2B) with hgB
  have hfg : ∀ a b, Commute (fA a) (gB b) := by
    rintro ⟨_, A, rfl⟩ ⟨_, B, rfl⟩
    exact hcomm A B
  set ρ := F4Pilot.supLift commute_simpleRootSL2_zero_two_three
    simpleRootSL2_zero_inf_two_three fA gB hfg with hρ
  have hρA : ∀ a : simpleRootSL2 F (0 : Fin 3), ρ ⟨a, mem_sup_left a.2⟩ = fA a :=
    F4Pilot.supLift_apply_left _ _ hfg
  have hρB : ∀ b : simpleRootSL2 F (2 : Fin 3), ρ ⟨b, mem_sup_right b.2⟩ = gB b :=
    F4Pilot.supLift_apply_right _ _ hfg
  obtain ⟨φ, hφ02, hφS, hφ0⟩ : ∃ φ : ∀ J : {J : Finset (Fin 3) // J.card ≤ 2},
      (rootDatum 3 F).leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (h : J.1 = {0, 2})
        (x : (rootDatum 3 F).leviAmalgam J),
        φ J x = ρ ⟨x, (leviAmalgam_zero_two_three J h).le x.2⟩) ∧
      (∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (h : J.1 ≠ {0, 2}) (h0 : (0 : Fin 3) ∈ J.1)
        (x : (rootDatum 3 F).leviAmalgam J),
        φ J x = Φ' ⟨x, leviAmalgam_le_siegelLevi_three J h h0 x.2⟩) ∧
      (∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (h0 : (0 : Fin 3) ∉ J.1)
        (x : (rootDatum 3 F).leviAmalgam J),
        φ J x = Φ₀ ⟨x, leviAmalgam_le_spBlock_zero_three J h0 x.2⟩) := by
    refine ⟨fun J => if h : J.1 = {0, 2} then
        ρ.comp (Subgroup.inclusion (leviAmalgam_zero_two_three J h).le)
      else if h0 : (0 : Fin 3) ∈ J.1 then
        Φ'.comp (Subgroup.inclusion (leviAmalgam_le_siegelLevi_three J h h0))
      else Φ₀.comp (Subgroup.inclusion (leviAmalgam_le_spBlock_zero_three J h0)), ?_, ?_, ?_⟩
    · intro J h x
      simp only [dite_eq_left h]
      rfl
    · intro J h h0 x
      simp only [dite_eq_right h, dite_eq_left h0]
      rfl
    · intro J h0 x
      have h : J.1 ≠ {0, 2} := fun h => h0 (by rw [h]; decide)
      simp only [dite_eq_right h, dite_eq_right h0]
      rfl
  have hmem : ∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (j : Fin 3), j ∈ J.1 → ∀ A : SL(2, F),
      simpleRootHom F j A ∈ (rootDatum 3 F).leviAmalgam J := fun J j hj A =>
    (leviAmalgam_eq_iSup J).ge (mem_iSup_of_mem j (mem_iSup_of_mem hj ⟨A, rfl⟩))
  have key0 : ∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (hJ : (0 : Fin 3) ∈ J.1) (A : SL(2, F)),
      φ J ⟨simpleRootHom F 0 A, hmem J 0 hJ A⟩ =
        Φ' ⟨simpleRootHom F 0 A, simpleRootHom_zero_mem_siegelLevi_three A⟩ := by
    intro J hJ A
    by_cases h : J.1 = {0, 2}
    · rw [hφ02 J h]
      exact hρA ⟨simpleRootHom F 0 A, ⟨A, rfl⟩⟩
    · rw [hφS J h hJ]
  have key1 : ∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (hJ : (1 : Fin 3) ∈ J.1) (A : SL(2, F)),
      φ J ⟨simpleRootHom F 1 A, hmem J 1 hJ A⟩ =
        Φ₀ ⟨simpleRootHom F 1 A, simpleRootHom_one_mem_spBlock_three A⟩ := by
    intro J hJ A
    have h : J.1 ≠ {0, 2} := fun h => by
      rw [h] at hJ
      exact absurd hJ (by decide)
    by_cases h0 : (0 : Fin 3) ∈ J.1
    · rw [hφS J h h0]
      exact hagree A
    · rw [hφ0 J h0]
  have key2 : ∀ (J : {J : Finset (Fin 3) // J.card ≤ 2}) (hJ : (2 : Fin 3) ∈ J.1) (A : SL(2, F)),
      φ J ⟨simpleRootHom F 2 A, hmem J 2 hJ A⟩ =
        Φ₀ ⟨simpleRootHom F 2 A, simpleRootHom_two_mem_spBlock_three A⟩ := by
    intro J hJ A
    by_cases h : J.1 = {0, 2}
    · rw [hφ02 J h]
      exact hρB ⟨simpleRootHom F 2 A, ⟨A, rfl⟩⟩
    · have h0 : (0 : Fin 3) ∉ J.1 := fun h0 => h (eq_zero_two_three J.1 J.2 h0 hJ)
      rw [hφ0 J h0]
  have hcomp : IsCompatible (rootDatum 3 F).leviAmalgam φ := by
    intro (I : {J : Finset (Fin 3) // J.card ≤ 2}) (J : {J : Finset (Fin 3) // J.card ≤ 2}) hIJ x y
      hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    have hle : (rootDatum 3 F).leviAmalgam I ≤ (rootDatum 3 F).leviAmalgam J := by
      rw [leviAmalgam_eq_iSup, leviAmalgam_eq_iSup]
      exact iSup₂_le fun j hj => le_iSup₂_of_le j (hIJ' hj) le_rfl
    have hgen : (rootDatum 3 F).leviAmalgam I ≤
        (MonoidHom.eqLocus (φ I) ((φ J).comp (Subgroup.inclusion hle))).map
          ((rootDatum 3 F).leviAmalgam I).subtype := by
      refine (leviAmalgam_eq_iSup I).le.trans (iSup₂_le fun (j : Fin 3) hj => ?_)
      rintro _ ⟨A, rfl⟩
      refine ⟨⟨simpleRootHom F j A, hmem I j hj A⟩, ?_, rfl⟩
      change φ I ⟨simpleRootHom F j A, hmem I j hj A⟩ =
        φ J ⟨simpleRootHom F j A, hmem J j (hIJ' hj) A⟩
      obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      · rw [key0 I hj A, key0 J (hIJ' hj) A]
      · rw [key1 I hj A, key1 J (hIJ' hj) A]
      · rw [key2 I hj A, key2 J (hIJ' hj) A]
    obtain ⟨x', hx', hxx'⟩ := hgen x.2
    have hx'' : φ I x' = φ J (Subgroup.inclusion hle x') := hx'
    have hxx : x' = x := Subtype.ext hxx'
    have hy : Subgroup.inclusion hle x' = y := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, hxx]
      exact hxy
    rw [← hxx, ← hy]
    exact hx''
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hleG : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (rootDatum 3 F).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hleG J)
    with hφ'
  have hcomp' : IsCompatible (rootDatum 3 F).leviAmalgam φ' := fun I J hIJ x y hxy =>
    Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hJs : ∀ j : Fin 3, ({j} : Finset (Fin 3)).card ≤ 2 := fun j => by simp
  set J0 : {J : Finset (Fin 3) // J.card ≤ 2} := ⟨{0}, hJs 0⟩ with hJ0
  set J1 : {J : Finset (Fin 3) // J.card ≤ 2} := ⟨{1}, hJs 1⟩ with hJ1
  set J2 : {J : Finset (Fin 3) // J.card ≤ 2} := ⟨{2}, hJs 2⟩ with hJ2
  have h0J0 : (0 : Fin 3) ∈ J0.1 := Finset.mem_singleton_self 0
  have h1J1 : (1 : Fin 3) ∈ J1.1 := Finset.mem_singleton_self 1
  have h2J2 : (2 : Fin 3) ∈ J2.1 := Finset.mem_singleton_self 2
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    refine ⟨J1, ⟨simpleRootHom F 1 (sl2Upper 1), hmem J1 1 h1J1 _⟩, fun h => ?_⟩
    have h1 : φ J1 ⟨simpleRootHom F 1 (sl2Upper 1), hmem J1 1 h1J1 _⟩ = 1 :=
      congrArg Subtype.val h
    rw [key1 J1 h1J1 _] at h1
    have h2 := hΦ₀ (h1.trans (map_one Φ₀).symm)
    have h3 : simpleRootHom F 1 (sl2Upper 1) = simpleRootHom F 1 1 :=
      (congrArg Subtype.val h2).trans (map_one _).symm
    have h4 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1)
      (simpleRootHom_injective 1 h3)
    simp [CFSG.LieType.Steinberg.coe_sl2Upper] at h4
  obtain ⟨g, hg1, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hadm : StatedLieAdmissible .PSp 3 2 g :=
    ⟨Nat.prime_two, hg1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_symplectic.{0} (F := F) hadm hFc (le_refl 3)
  obtain ⟨ψ₀, hψ₀, -, hker, -⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_statedSp_eq_bot 3).le
  set ψ : StatedSp 3 F →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψφ : ∀ J (x : (rootDatum 3 F).leviAmalgam J), ψ x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  refine ⟨ψ, G₀.subtype_injective.comp hinj₀, fun A => ?_, fun A => ?_, fun A => ?_⟩
  · exact (hψφ J0 ⟨_, hmem J0 0 h0J0 A⟩).trans (key0 J0 h0J0 A)
  · exact (hψφ J1 ⟨_, hmem J1 1 h1J1 A⟩).trans (key1 J1 h1J1 A)
  · exact (hψφ J2 ⟨_, hmem J2 2 h2J2 A⟩).trans (key2 J2 h2J2 A)

end Amalgam

end CFSG.SeitzReduction.SymplecticPilot
