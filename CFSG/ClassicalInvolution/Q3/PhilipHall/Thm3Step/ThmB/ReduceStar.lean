module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Hex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

section Rel

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

@[expose] def ClassComm (Φ : Set (Subgroup Y)) (L M : Subgroup Y) : Prop :=
  ∀ L' ∈ aStar Φ L, ∀ M' ∈ aStar Φ M, Commutes L' M'

theorem ClassComm.symm {L M : Subgroup Y} (h : ClassComm Φ L M) : ClassComm Φ M L :=
  fun M' hM' L' hL' => commutes_symm (h L' hL' M' hM')

theorem ClassComm.of_aStar_eq_left {L L₀ M : Subgroup Y} (h : ClassComm Φ L₀ M)
    (e : aStar Φ L = aStar Φ L₀) : ClassComm Φ L M := by
  unfold ClassComm
  rw [e]
  exact h

theorem ClassComm.of_aStar_eq_right {L M M₀ : Subgroup Y} (h : ClassComm Φ L M₀)
    (e : aStar Φ M = aStar Φ M₀) : ClassComm Φ L M := by
  unfold ClassComm
  rw [e]
  exact h

end Rel

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

namespace QFam

variable (h : QFam Φ Q)
include h

theorem classComm_of_dstarAdj {L M : Subgroup Y} (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hadj : dstarAdj Φ L M) (hne : aStar Φ M ≠ aStar Φ L) : ClassComm Φ L M := by
  have hΦ := h.hypGen
  have hMst : M ∈ omegaStarNbr Φ L := by
    rcases hadj with ⟨-, hst | hst⟩
    · exact hst
    · exact Q3T6.Mu.omegaStarNbr_symm hΦ hM hL hst
  have hMA : M ∉ aStar Φ L := fun h' => hne (aStar_eq_of_mem_aStar hL h')
  have hMn : M ∈ omegaNbr Φ L := h.mem_omegaNbr_of_omegaStar hL hMst hMA
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΦ hL
  have hMt : M ∉ twinSet Φ L := by
    rintro ⟨-, w, hwL, hwM⟩
    exact hMA (mem_aStar_of_twin Relation.ReflTransGen.refl hM hwL hwM)
  have hMO : M ∈ omegaOfSet Φ (twinSet Φ L) := mem_omegaOfSet_of_mem_omegaNbr hΦ hzL hMn hMt
  intro L' hL' M' hM'
  have hL'Φ : L' ∈ Φ := mem_of_mem_aStar hL hL'
  have hM'Φ : M' ∈ Φ := mem_of_mem_aStar hM hM'
  obtain ⟨-, eL⟩ := h.aStar_subset_vStar hL hL'
  obtain ⟨w', hw'⟩ := Sec6Gen.exists_uniqueInvolution hΦ hL'Φ
  have hML' : M ∈ omegaNbr Φ L' := by
    rw [eL] at hMO
    exact hMO.2 L' ⟨hL'Φ, w', hw', hw'⟩
  have hL'M : L' ∈ omegaNbr Φ M := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hL'Φ hM hML'
  obtain ⟨zM, hzM⟩ := Sec6Gen.exists_uniqueInvolution hΦ hM
  have hL'A : L' ∉ aStar Φ M := by
    intro h'
    apply hne
    rw [← aStar_eq_of_mem_aStar hM h', aStar_eq_of_mem_aStar hL hL']
  have hL't : L' ∉ twinSet Φ M := by
    rintro ⟨-, w, hwM, hwL'⟩
    exact hL'A (mem_aStar_of_twin Relation.ReflTransGen.refl hL'Φ hwM hwL')
  have hL'O := mem_omegaOfSet_of_mem_omegaNbr hΦ hzM hL'M hL't
  obtain ⟨-, eM⟩ := h.aStar_subset_vStar hM hM'
  obtain ⟨w'', hw''⟩ := Sec6Gen.exists_uniqueInvolution hΦ hM'Φ
  rw [eM] at hL'O
  exact commutes_symm (h.commutes_of_mem_omegaNbr hM'Φ (hL'O.2 M' ⟨hM'Φ, w'', hw'', hw''⟩))

theorem centralizer_ne_top {L : Subgroup Y} (hL : L ∈ Φ) {w : Y}
    (hw : IsUniqueInvolution L w) : Subgroup.centralizer ({w} : Set Y) ≠ ⊤ := by
  obtain ⟨J, zL, zJ, hv⟩ := not_aEmpty_iff.mp (h.notEmpty L hL)
  rw [hw.eq hv.hzK]
  obtain ⟨s, -, hs⟩ := Thm3Quot.exists_conj_mul_involution h.hypGen hL hv
  intro htop
  have hsC : s ∈ Subgroup.centralizer ({zL} : Set Y) := by
    rw [htop]
    exact Subgroup.mem_top s
  have e1 : s * zL * s⁻¹ = zL * zJ := (hv.hzK.conj s).eq hs
  have e2 : s * zL * s⁻¹ = zL := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hsC]
    group
  have e3 : zL * zJ = zL * 1 := by rw [← e1, e2, mul_one]
  exact hv.hzJ.ne_one (mul_left_cancel e3)

theorem classComm_trans (hb : Thm3A.Thm3RBelowG (Nat.card Y)) {L₁ L₂ L₃ : Subgroup Y}
    (h₁ : L₁ ∈ Φ) (h₂ : L₂ ∈ Φ) (h₃ : L₃ ∈ Φ) (h12 : ClassComm Φ L₁ L₂)
    (h23 : ClassComm Φ L₂ L₃) (hne : aStar Φ L₃ ≠ aStar Φ L₁) : ClassComm Φ L₁ L₃ := by
  by_cases e21 : aStar Φ L₂ = aStar Φ L₁
  · exact h23.of_aStar_eq_left e21.symm
  by_cases e23 : aStar Φ L₂ = aStar Φ L₃
  · exact h12.of_aStar_eq_right e23.symm
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution h.hypGen h₂
  have hC := h.centralizer_ne_top h₂ hw
  have hle : ∀ M : Subgroup Y, ClassComm Φ M L₂ → ∀ M' ∈ aStar Φ M,
      M' ≤ Subgroup.centralizer ({w} : Set Y) := fun M hM M' hM' x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hM M' hM' L₂ Relation.ReflTransGen.refl x hx w
      hw.mem)
  intro L₁' hL₁' L₃' hL₃'
  have hL₁'Φ : L₁' ∈ Φ := mem_of_mem_aStar h₁ hL₁'
  obtain ⟨J₁, z₁, j₁, hv₁⟩ := not_aEmpty_iff.mp (h.notEmpty L₁' hL₁'Φ)
  have e1 : aStar Φ L₁' = aStar Φ L₁ := aStar_eq_of_mem_aStar h₁ hL₁'
  have hJ₁ : J₁ ∈ aStar Φ L₁ := by
    rw [← e1]
    exact mem_aStar_of_aViol hv₁
  have hnot : L₃' ∉ aStar Φ L₁' := by
    rw [e1]
    intro h'
    apply hne
    rw [← aStar_eq_of_mem_aStar h₃ hL₃', aStar_eq_of_mem_aStar h₁ h']
  exact h.commutes_of_le_of_not_mem_aStar hb hC hL₁'Φ (hle L₁ h12 L₁' hL₁')
    (hle L₁ h12 J₁ hJ₁) hv₁ (mem_of_mem_aStar h₃ hL₃') (hle L₃ h23.symm L₃' hL₃') hnot

theorem aStar_eq_of_dstarComp_eq (hb : Thm3A.Thm3RBelowG (Nat.card Y)) {K : Subgroup Y}
    (hK : K ∈ Φ) (hgen : omegaGen Φ = ⊤) (htw : TwinOrbits Φ K) (hD : dstarComp Φ K = Φ) :
    aStar Φ K = Φ := by
  have hΦ := h.hypGen
  have hc := hΦ.conjInvariant
  have key : ∀ M ∈ dstarComp Φ K, aStar Φ M = aStar Φ K ∨ ClassComm Φ K M := by
    intro M hM
    induction hM with
    | refl => exact Or.inl rfl
    | @tail L M' hKL hadj ih =>
      have hLΦ : L ∈ Φ := (mem_dstarComp_symm hK hKL).1
      have hM'Φ : M' ∈ Φ := hadj.1
      by_cases hLM : aStar Φ M' = aStar Φ L
      · rcases ih with e | hc'
        · exact Or.inl (hLM.trans e)
        · exact Or.inr (hc'.of_aStar_eq_right hLM)
      · have hcLM := h.classComm_of_dstarAdj hLΦ hM'Φ hadj hLM
        rcases ih with e | hc'
        · exact Or.inr (hcLM.of_aStar_eq_left e.symm)
        · by_cases hMK : aStar Φ M' = aStar Φ K
          · exact Or.inl hMK
          · exact Or.inr (h.classComm_trans hb hK hLΦ hM'Φ hc' hcLM hMK)
  have hall : ∀ M ∈ Φ, M ≤ conjStab (aStar Φ K) := by
    intro M hM
    by_cases hMA : M ∈ aStar Φ K
    · exact le_conjStab_aStar hc hK hMA
    · rcases key M (by rw [hD]; exact hM) with e | hcm
      · exact absurd (by rw [← e]; exact Relation.ReflTransGen.refl) hMA
      · intro x hx
        have hcx : Commutes M K := commutes_symm
          (hcm K Relation.ReflTransGen.refl M Relation.ReflTransGen.refl)
        exact mem_conjStab_aStar hc hK Relation.ReflTransGen.refl
          (conjSub_eq_of_mem_normalizer (AscL62.le_normalizer_of_commutes hcx hx))
  have htop : conjStab (aStar Φ K) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le hall
  refine Set.Subset.antisymm (fun M hM => mem_of_mem_aStar hK hM) fun M hM => ?_
  obtain ⟨g, J, hJ, rfl⟩ := htw M hM
  obtain ⟨hJΦ, w, hwK, hwJ⟩ := hJ
  have hJA : J ∈ aStar Φ K := mem_aStar_of_twin Relation.ReflTransGen.refl hJΦ hwK hwJ
  have hg : g ∈ conjStab (aStar Φ K) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact (mem_conjStab_iff.mp hg J).mpr hJA

end QFam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
