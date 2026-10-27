module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Nbr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Hex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Rel

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def BlockComm (Ω : Set (Subgroup G)) (L M : Subgroup G) : Prop :=
  ∃ L' ∈ aStar Ω L, ∃ M' ∈ aStar Ω M, M' ∈ omegaNbr Ω L'

theorem BlockComm.symm [Finite G] (hΩ : HypOmegaGen Ω) {L M : Subgroup G} (hL : L ∈ Ω)
    (h : BlockComm Ω L M) : BlockComm Ω M L := by
  obtain ⟨L', hL', M', hM', hn⟩ := h
  exact ⟨M', hM', L', hL',
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (mem_of_mem_aStar hL hL') hn.1 hn⟩

theorem BlockComm.of_aStar_eq_left {L M N : Subgroup G} (h : BlockComm Ω L N)
    (e : aStar Ω M = aStar Ω L) : BlockComm Ω M N := by
  obtain ⟨L', hL', N', hN', hn⟩ := h
  exact ⟨L', e ▸ hL', N', hN', hn⟩

end Rel

section Frame

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem BlockComm.le_conjStab (hs : FrameStd K z J zJ) {L M L' : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hM : M ∈ CoreAssembly.conjClass K)
    (hne : aStar (CoreAssembly.conjClass K) M ≠ aStar (CoreAssembly.conjClass K) L)
    (h : BlockComm (CoreAssembly.conjClass K) L M) (hL' : L' ∈ aStar (CoreAssembly.conjClass K) L) :
    L' ≤ conjStab (aStar (CoreAssembly.conjClass K) M) := by
  obtain ⟨L₀, hL₀, M₀, hM₀, hn⟩ := h
  have hL₀Ω := mem_of_mem_aStar hL hL₀
  have e1 : aStar (CoreAssembly.conjClass K) L₀ = aStar (CoreAssembly.conjClass K) L :=
    aStar_eq_of_mem_aStar hL hL₀
  have e2 : aStar (CoreAssembly.conjClass K) M₀ = aStar (CoreAssembly.conjClass K) M :=
    aStar_eq_of_mem_aStar hM hM₀
  have hM₀B : M₀ ∉ aStar (CoreAssembly.conjClass K) L₀ := fun h' =>
    hne (e2.symm.trans ((aStar_eq_of_mem_aStar hL₀Ω h').trans e1))
  have h1 := (aStar_le_conjStab_of_omegaNbr hs hL₀Ω hn hM₀B).1 L' (e1 ▸ hL')
  rwa [e2] at h1

theorem BlockComm.trans (hs : FrameStd K z J zJ) {L₁ L₂ L₃ : Subgroup T}
    (h₁ : L₁ ∈ CoreAssembly.conjClass K) (h₂ : L₂ ∈ CoreAssembly.conjClass K)
    (h₃ : L₃ ∈ CoreAssembly.conjClass K) (h12 : BlockComm (CoreAssembly.conjClass K) L₁ L₂)
    (h23 : BlockComm (CoreAssembly.conjClass K) L₂ L₃)
    (hne : aStar (CoreAssembly.conjClass K) L₃ ≠ aStar (CoreAssembly.conjClass K) L₁) :
    BlockComm (CoreAssembly.conjClass K) L₁ L₃ := by
  have hΩ := hs.hyp
  by_cases e21 : aStar (CoreAssembly.conjClass K) L₂ = aStar (CoreAssembly.conjClass K) L₁
  · exact h23.of_aStar_eq_left e21.symm
  by_cases e23 : aStar (CoreAssembly.conjClass K) L₂ = aStar (CoreAssembly.conjClass K) L₃
  · exact ((h12.symm hΩ h₁).of_aStar_eq_left e23.symm).symm hΩ h₃
  obtain ⟨J₁, zA, zJ₁, hv⟩ := hs.exists_aViol h₁
  have hAX : L₁ ≤ conjStab (aStar (CoreAssembly.conjClass K) L₂) :=
    h12.le_conjStab hs h₁ h₂ e21 Relation.ReflTransGen.refl
  have hJ₁X : J₁ ≤ conjStab (aStar (CoreAssembly.conjClass K) L₂) :=
    h12.le_conjStab hs h₁ h₂ e21 (mem_aStar_of_aViol hv)
  have hCX : L₃ ≤ conjStab (aStar (CoreAssembly.conjClass K) L₂) :=
    (h23.symm hΩ h₂).le_conjStab hs h₃ h₂ e23 Relation.ReflTransGen.refl
  have hCB : L₃ ∉ aStar (CoreAssembly.conjClass K) L₁ := fun h =>
    hne (aStar_eq_of_mem_aStar h₁ h)
  obtain ⟨R, -, hR, -⟩ := exists_mem_RSet_ge h₃ (isPGroup_two_bot' (G := T)) bot_le
  obtain ⟨n, -, hRn, hnB⟩ := exists_conj_omegaNbr_of_le_of_aViol hs.typeRHyp hs.below
    (hs.conjStab_ne_top h₂) h₁ hAX hJ₁X hv h₃ hCX hCB R hR
  exact ⟨conjSub n L₁, hnB, L₃, Relation.ReflTransGen.refl,
    ⟨h₃, fun h => hCB (h ▸ hnB), R, mem_RSet_of_isSylow2In h₃ hR, hR.1, hRn⟩⟩

theorem blockComm_of_dstarAdj (hs : FrameStd K z J zJ) {L M : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hM : M ∈ CoreAssembly.conjClass K)
    (hne : aStar (CoreAssembly.conjClass K) M ≠ aStar (CoreAssembly.conjClass K) L)
    (h : dstarAdj (CoreAssembly.conjClass K) L M) : BlockComm (CoreAssembly.conjClass K) L M := by
  have hMst : M ∈ omegaStarNbr (CoreAssembly.conjClass K) L := by
    rcases h with ⟨-, hst | hst⟩
    · exact hst
    · exact Q3T6.Mu.omegaStarNbr_symm hs.hyp hM hL hst
  have hMB : M ∉ aStar (CoreAssembly.conjClass K) L := fun h' => hne (aStar_eq_of_mem_aStar hL h')
  obtain ⟨L₀, hL₀, hn⟩ := exists_omegaNbr_of_omegaStarNbr hs hL hMst hMB
  exact ⟨L₀, hL₀, M, Relation.ReflTransGen.refl, hn⟩

theorem exists_not_blockComm (hs : FrameStd K z J zJ) :
    ∃ M ∈ CoreAssembly.conjClass K,
      aStar (CoreAssembly.conjClass K) M ≠ aStar (CoreAssembly.conjClass K) K ∧
        ¬ BlockComm (CoreAssembly.conjClass K) M K := by
  by_contra hcon
  push Not at hcon
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hΩc := hs.hyp.conjInvariant
  apply hs.conjStab_ne_top hK
  have hall : ∀ M ∈ CoreAssembly.conjClass K,
      M ≤ conjStab (aStar (CoreAssembly.conjClass K) K) := by
    intro M hM
    by_cases hMB : M ∈ aStar (CoreAssembly.conjClass K) K
    · exact le_conjStab_aStar hΩc hK hMB
    · have hne := aStar_ne_of_not_mem hMB
      exact (hcon M hM hne).le_conjStab hs hM hK hne.symm Relation.ReflTransGen.refl
  rw [eq_top_iff, ← hs.datum.selfGen]
  exact iSup_le fun g => hall _ ⟨g, rfl⟩

theorem dstarComp_eq_blocks (hs : FrameStd K z J zJ) :
    dstarComp (CoreAssembly.conjClass K) K =
      {M | M ∈ CoreAssembly.conjClass K ∧
        (aStar (CoreAssembly.conjClass K) M = aStar (CoreAssembly.conjClass K) K ∨
          BlockComm (CoreAssembly.conjClass K) M K)} := by
  have hΩ := hs.hyp
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  ext M
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hM
    induction hM with
    | refl => exact ⟨hK, Or.inl rfl⟩
    | @tail L M' _ hadj ih =>
      obtain ⟨hLΩ, hLU⟩ := ih
      have hM'Ω : M' ∈ CoreAssembly.conjClass K := hadj.1
      refine ⟨hM'Ω, ?_⟩
      rcases hLU with hLK | hLK
      · by_cases hLM : aStar (CoreAssembly.conjClass K) M' = aStar (CoreAssembly.conjClass K) L
        · exact Or.inl (hLM.trans hLK)
        · exact Or.inr (((blockComm_of_dstarAdj hs hLΩ hM'Ω hLM hadj).of_aStar_eq_left
            hLK.symm).symm hΩ hK)
      · by_cases hLM : aStar (CoreAssembly.conjClass K) M' = aStar (CoreAssembly.conjClass K) L
        · exact Or.inr (hLK.of_aStar_eq_left hLM)
        · by_cases hMK : aStar (CoreAssembly.conjClass K) M' = aStar (CoreAssembly.conjClass K) K
          · exact Or.inl hMK
          · exact Or.inr (BlockComm.trans hs hM'Ω hLΩ hK
              ((blockComm_of_dstarAdj hs hLΩ hM'Ω hLM hadj).symm hΩ hLΩ) hLK (Ne.symm hMK))
  · rintro ⟨hMΩ, hMK | hMK⟩
    · have hMA : M ∈ aStar (CoreAssembly.conjClass K) K := hMK ▸ Relation.ReflTransGen.refl
      exact (aStar_subset_dstarComp_gen hΩ hK hMA).2
    ·
      obtain ⟨M', hM', K', hK', hn⟩ := hMK
      have hM'Ω : M' ∈ CoreAssembly.conjClass K := mem_of_mem_aStar hMΩ hM'
      have hK'S : K' ∈ dstarComp (CoreAssembly.conjClass K) K :=
        (aStar_subset_dstarComp_gen hΩ hK hK').2
      have hM'n : M' ∈ omegaNbr (CoreAssembly.conjClass K) K' :=
        Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hM'Ω hn.1 hn
      have hM'S : M' ∈ dstarComp (CoreAssembly.conjClass K) K :=
        hK'S.tail ⟨hM'Ω, Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ K' hM'n)⟩
      exact hM'S.trans (aStar_subset_dstarComp_gen hΩ hM'Ω (mem_aStar_symm hMΩ hM').2).2

theorem sigmaOf_ne_conjClass (hs : FrameStd K z J zJ) : sigmaOf K ≠ CoreAssembly.conjClass K := by
  intro hσ
  obtain ⟨M, hM, hne, hnot⟩ := exists_not_blockComm hs
  have hMσ : M ∈ sigmaOf K := hσ ▸ hM
  have hMσ' : M ∈ dstarComp (CoreAssembly.conjClass K) K := hMσ
  rw [dstarComp_eq_blocks hs] at hMσ'
  rcases hMσ'.2 with h | h
  · exact hne h
  · exact hnot h

end Frame

theorem frame_dstarComp_ne_proved {T : Type} [Group T] [Finite T]
    {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T} (hs : FrameStd K z J zJ) :
    sigmaOf K ≠ CoreAssembly.conjClass K :=
  sigmaOf_ne_conjClass hs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
