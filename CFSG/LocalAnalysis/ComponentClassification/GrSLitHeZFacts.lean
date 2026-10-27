module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZFactsModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowAll
public import CFSG.Sporadic.HeldB.AutModel

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.UnbalancedGS HeFM

namespace HeZF

theorem four_of_mulEquiv {G H : Type*} [Group G] [Group H] {A : Subgroup G} {B : Subgroup H}
    (f : ↥A ≃* ↥B)
    (h : ∃ y₁ ∈ A, ∃ y₂ ∈ A, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁) :
    ∃ y₁ ∈ B, ∃ y₂ ∈ B, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁ := by
  obtain ⟨y₁, h₁, y₂, h₂, hs₁, hs₂, hn₁, hn₂, hne, hc⟩ := h
  have ha : (⟨y₁, h₁⟩ : ↥A) * ⟨y₁, h₁⟩ = 1 := Subtype.ext hs₁
  have hb : (⟨y₂, h₂⟩ : ↥A) * ⟨y₂, h₂⟩ = 1 := Subtype.ext hs₂
  have hab : (⟨y₁, h₁⟩ : ↥A) * ⟨y₂, h₂⟩ = ⟨y₂, h₂⟩ * ⟨y₁, h₁⟩ := Subtype.ext hc
  refine ⟨f ⟨y₁, h₁⟩, (f _).2, f ⟨y₂, h₂⟩, (f _).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coe_mul, ← map_mul, ha, map_one, coe_one]
  · rw [← coe_mul, ← map_mul, hb, map_one, coe_one]
  · intro h
    have h' : f ⟨y₁, h₁⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact hn₁ (congrArg Subtype.val h')
  · intro h
    have h' : f ⟨y₂, h₂⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact hn₂ (congrArg Subtype.val h')
  · intro h
    exact hne (congrArg Subtype.val (f.injective (Subtype.ext h)))
  · rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, hab]

theorem normal_trS {X X' : Type} [Group X] [Group X'] {L : Subgroup X} {L' : Subgroup X'}
    (φ : ↥L ≃* ↥L') {N T : Subgroup X} (hNT : N ≤ T) (hn : (N.subgroupOf T).Normal) :
    ((HeT.trS φ N).subgroupOf (HeT.trS φ T)).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨x, hx, hxe⟩ := (HeT.mem_trS φ).mp ha
  obtain ⟨z, hz, hze⟩ := (HeT.mem_trS φ).mp g.2
  have h1 := hn.conj_mem ⟨x, hNT hx⟩ (mem_subgroupOf.mpr hx) ⟨z, hz⟩
  rw [mem_subgroupOf] at h1
  have h2 := HeT.mem_trS_of_mem φ (x := z * x * z⁻¹) h1
  rw [map_mul, map_mul, map_inv] at h2
  simp only [coe_mul, coe_inv] at h2 ⊢
  rwa [hxe, hze] at h2

end HeZF

open HeZF

theorem heldOuterSolvableFact :
    HeldOuterSolvableFact := by
  intro X _ _ L ⟨e⟩
  obtain ⟨-, -, -, hcyc, -, -⟩ := ctbh_full_automorphism_permutation_model
  have : IsCyclic (OuterAutomorphisms.Outer ↥heP) := hcyc
  have : Group.IsSolvable (OuterAutomorphisms.Outer ↥heP) := inferInstance
  exact OuterAutomorphisms.solvable_of_equiv (toP e).symm


theorem heldTwoAKFact :
    HeldTwoAKFact := by
  intro X _ _ L ⟨e⟩ u hu
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hKle : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hK : HeT.trS φ (gsFixedLayer L u) = heK0 := by
    rw [HeT.trS_gsFixedLayer φ hu.1, hφ]
    rfl
  have hZ : ∀ y : ↥L, (φ y : Equiv.Perm (Fin 8330)) ∈ heZ0 ↔
      (y : X) ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro y
    rw [← mem_center_trS_iff φ hKle y, hK]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · let ι : ↥(gsFixedLayer L u) ≃* ↥heK0 :=
      (HeT.trEquiv φ hKle).trans (MulEquiv.subgroupCongr hK)
    rw [Nat.card_congr (centerCongr ι).toEquiv]
    exact HeGS.card_center_heK0
  · intro S hS hp
    have hSL : S ≤ L := hS.trans inf_le_left
    have hS' : HeT.trS φ S ≤ centralizerIn heP (heGenPerm 0) := by
      have h := HeT.trS_mono φ hS
      rw [HeT.trS_inf_centralizer φ hu.1, hφ] at h
      exact h
    have hp' : ⁅HeT.trS φ S, HeT.trS φ S⁆ = HeT.trS φ S := by
      have : Group.IsPerfect ↥S := isPerfect_iff.mpr hp
      exact isPerfect_iff.mp (Group.IsPerfect.ofSurjective
        (f := (HeT.trEquiv φ hSL).toMonoidHom) (HeT.trEquiv φ hSL).surjective)
    have h := HeGS.le_heK0_of_perfect hS' hp'
    rw [← hK] at h
    intro x hx
    exact HeT.mem_of_mem_trS φ (x := ⟨x, hSL hx⟩) (h (HeT.mem_trS_of_mem φ hx))
  · intro y hyL hyK
    have hc : ∀ k ∈ heK0, (φ ⟨y, hyL⟩ : Equiv.Perm (Fin 8330)) * k = k * φ ⟨y, hyL⟩ := by
      intro k hk
      rw [← hK] at hk
      obtain ⟨k', hk', rfl⟩ := (HeT.mem_trS φ).mp hk
      have h1 : (⟨y, hyL⟩ : ↥L) * k' = k' * ⟨y, hyL⟩ := Subtype.ext (hyK _ hk')
      rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h1]
    have hcase : ∀ p : Equiv.Perm (Fin 8330), (φ ⟨y, hyL⟩ : Equiv.Perm (Fin 8330)) = p →
        p ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) → p ∈ heZ0 →
        HeldTwoA L y ∧ y ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
      rintro p hp hpc hpZ
      subst hp
      exact ⟨(HeT.heldTwoA_iff φ hyL).mp ((HeLay.heldTwoA_heP_iff (φ _).2
        (orderOf_of_mem_conjClass hpc)).mpr hpc), (hZ ⟨y, hyL⟩).mp hpZ⟩
    rcases HeGS.eq_of_comm_heK0 (φ ⟨y, hyL⟩).2 hc with h | h | h | h
    · left
      have h' : φ ⟨y, hyL⟩ = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff] at h'
      exact congrArg Subtype.val h'
    · exact Or.inr (hcase _ h ⟨1, one_mem _, by group⟩
        (HeGS.mem_heZ0_of_mem_ker HeGS.heGST0_mem_ker))
    · exact Or.inr (hcase _ h HeGS.heGSU_mem_conjClass
        (HeGS.mem_heZ0_of_mem_ker HeGS.heGSU_mem_ker))
    · exact Or.inr (hcase _ h HeGS.heGST0U_mem_conjClass
        (HeGS.mem_heZ0_of_mem_ker (mul_mem HeGS.heGST0_mem_ker HeGS.heGSU_mem_ker)))

theorem heldTwoBFact :
    HeldTwoBFact := by
  intro X _ _ L ⟨e⟩ v hvL hv hv0
  obtain ⟨φ, hφ⟩ := exists_equiv_t1 e hvL hv hv0
  have hC0 := HeT.trS_inf_centralizer φ hvL
  rw [hφ] at hC0
  have hC : HeT.trS φ (L ⊓ centralizer ({v} : Set X)) = centralizerIn heP heT1P := hC0
  obtain ⟨-, hN⟩ := heldTwoBCentralizerStructure
  refine ⟨?_, fun N hNle hNn hNne => ?_⟩
  · rw [← HeT.card_trS φ inf_le_left, hC, card_heP_cent1]
  · have hNL : N ≤ L := hNle.trans inf_le_left
    have hN'le : HeT.trS φ N ≤ centralizerIn heP heT1P := by
      rw [← hC]
      exact HeT.trS_mono φ hNle
    have hN'n : ((HeT.trS φ N).subgroupOf (centralizerIn heP heT1P)).Normal := by
      have h := normal_trS φ hNle hNn
      rwa [hC] at h
    have hN'ne : HeT.trS φ N ≠ centralizerIn heP heT1P := fun h =>
      hNne (HeT.trS_injective φ hNL inf_le_left (h.trans hC.symm))
    exact (hN _ hN'le hN'n hN'ne).of_equiv (HeT.trEquiv φ hNL).symm

theorem heldSylowFourFact :
    HeldSylowFourFact := by
  intro X _ _ L ⟨e⟩ T hTL hT N hNT hNn hN4
  have hNL : N ≤ L := hNT.trans hTL
  obtain ⟨g, hg, hTg⟩ := HeldFix.exists_conj_hfT (HeT.trS_le (toP e) T)
    (by rw [HeT.card_trS (toP e) hTL, hT])
  let φ : ↥L ≃* ↥heP := (toP e).trans (conjP ⟨g, hg⟩⁻¹)
  have hφa : ∀ x : ↥L, (φ x : Equiv.Perm (Fin 8330)) = g⁻¹ * toP e x * g := fun x => by
    change (⟨g, hg⟩⁻¹ * toP e x * (⟨g, hg⟩⁻¹)⁻¹ : ↥heP).1 = _
    simp only [coe_mul, coe_inv, inv_inv]
  have hT' : HeT.trS φ T = HeldFix.hfT := by
    ext y
    rw [HeT.mem_trS]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := HeT.mem_trS_of_mem (toP e) hx
      rw [hTg, HeldFix.mem_map_conj_iff] at h1
      rw [hφa]
      exact h1
    · intro hy
      have h1 : g * y * g⁻¹ ∈ HeT.trS (toP e) T := by
        rw [hTg, HeldFix.mem_map_conj_iff]
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      obtain ⟨x, hx, hxe⟩ := (HeT.mem_trS (toP e)).mp h1
      refine ⟨x, hx, ?_⟩
      rw [hφa, hxe]
      group
  have hN'T : HeT.trS φ N ≤ HeldFix.hfT := by
    rw [← hT']
    exact HeT.trS_mono φ hNT
  have hN'n : ((HeT.trS φ N).subgroupOf HeldFix.hfT).Normal := by
    have h := normal_trS φ hNT hNn
    rwa [hT'] at h
  have hN'4 : 4 ≤ Nat.card (HeT.trS φ N) := by
    rw [HeT.card_trS φ hNL]
    exact hN4
  exact four_of_mulEquiv (HeT.trEquiv φ hNL).symm
    (HeGS.exists_four_of_normal_hfT hN'T hN'n hN'4)

end CFSG.ComponentClassification.GrSLit
