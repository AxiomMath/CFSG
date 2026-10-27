module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1FlRad
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {F : Type} [Field F]

theorem mem_flag_two_one {v : Fin 2 ⊕ Fin 2 → F} :
    v ∈ flag 2 F 1 ↔ v (Sum.inl 1) = 0 ∧ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  rw [mem_flag_iff]
  constructor
  · intro h
    refine ⟨h _ ?_, h _ ?_, h _ ?_⟩
    · rw [flagOrder_inl]; decide
    · rw [flagOrder_inr]; decide
    · rw [flagOrder_inr]; decide
  · rintro ⟨h1, h2, h3⟩ x hx
    rcases x with i | i
    · fin_cases i
      · rw [flagOrder_inl] at hx
        exact absurd hx (by decide)
      · exact h1
    · fin_cases i
      · exact h2
      · exact h3

theorem mem_flag_two_two {v : Fin 2 ⊕ Fin 2 → F} :
    v ∈ flag 2 F 2 ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  rw [mem_flag_iff]
  constructor
  · intro h
    refine ⟨h _ ?_, h _ ?_⟩
    · rw [flagOrder_inr]; decide
    · rw [flagOrder_inr]; decide
  · rintro ⟨h2, h3⟩ x hx
    rcases x with i | i
    · fin_cases i
      · rw [flagOrder_inl] at hx
        exact absurd hx (by decide)
      · rw [flagOrder_inl] at hx
        exact absurd hx (by decide)
    · fin_cases i
      · exact h2
      · exact h3

theorem mem_flag_two_three {v : Fin 2 ⊕ Fin 2 → F} :
    v ∈ flag 2 F 3 ↔ v (Sum.inr 0) = 0 := by
  rw [mem_flag_iff]
  constructor
  · intro h
    exact h _ (by rw [flagOrder_inr]; decide)
  · intro h x hx
    rcases x with i | i
    · fin_cases i
      · rw [flagOrder_inl] at hx
        exact absurd hx (by decide)
      · rw [flagOrder_inl] at hx
        exact absurd hx (by decide)
    · fin_cases i
      · exact h
      · rw [flagOrder_inr] at hx
        exact absurd hx (by decide)

theorem flag_two_one_le_three : flag 2 F 1 ≤ flag 2 F 3 := flag_mono (by norm_num)

variable (F) in
@[expose] def spRad1 : Subgroup (StatedSp 2 F) :=
  radFl (StatedSp 2 F) (flag 2 F 1) (flag 2 F 3) flag_two_one_le_three

variable (F) in
@[expose] def spRad2 : Subgroup (StatedSp 2 F) :=
  radFl (StatedSp 2 F) (flag 2 F 2) (flag 2 F 2) le_rfl

theorem mulVec_mem_of_mem_stabilizer_sp {W : Submodule F (Fin 2 ⊕ Fin 2 → F)} {s : StatedSp 2 F}
    (hs : s ∈ stabilizer 2 F W) {w : Fin 2 ⊕ Fin 2 → F} (hw : w ∈ W) :
    ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W := by
  have hs' := mem_stabilizer.mp hs
  have : ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈
      W.map (mulVecLin ((s : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) := ⟨w, hw, mulVecLin_apply _ _⟩
  rwa [hs'] at this

theorem mulVec_mem_flag_three {s : StatedSp 2 F} (hs : s ∈ stabilizer 2 F (flag 2 F 1))
    {x : Fin 2 ⊕ Fin 2 → F} (hx : x ∈ flag 2 F 3) :
    ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ x ∈ flag 2 F 3 := by
  have h1 : flag 2 F 1 = isoFlag 2 F 1 := by rw [flag, ite_eq_left (by norm_num)]
  have h3 : flag 2 F 3 = (pairedSympForm F 2).orthogonal (isoFlag 2 F 1) := by
    rw [flag, ite_eq_right (by norm_num)]
  rw [h3] at hx ⊢
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  intro n hn
  have hsi : s⁻¹ ∈ stabilizer 2 F (flag 2 F 1) := inv_mem hs
  have hn' : ((s⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *ᵥ n ∈ isoFlag 2 F 1 := by
    rw [← h1] at hn ⊢
    exact mulVec_mem_of_mem_stabilizer_sp hsi hn
  have key := pairedSympForm_mulVec s (((s⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *ᵥ n) x
  rw [Matrix.mulVec_mulVec] at key
  have hss : ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      (((s⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      = 1 := by
    rw [Subgroup.coe_inv, Units.mul_inv]
  rw [hss, Matrix.one_mulVec] at key
  rw [key]
  exact hx _ hn'

theorem conj_mem_spRad1 {s : StatedSp 2 F} (hs : s ∈ stabilizer 2 F (flag 2 F 1))
    {g : StatedSp 2 F} (hg : g ∈ spRad1 F) : s * g * s⁻¹ ∈ spRad1 F :=
  conj_mem_radFl (fun _ hw => mulVec_mem_of_mem_stabilizer_sp hs hw)
    (fun _ hw => mulVec_mem_flag_three hs hw)
    (fun _ hw => mulVec_mem_of_mem_stabilizer_sp (inv_mem hs) hw)
    (fun _ hw => mulVec_mem_flag_three (inv_mem hs) hw) hg

theorem conj_mem_spRad2 {s : StatedSp 2 F} (hs : s ∈ stabilizer 2 F (flag 2 F 2))
    {g : StatedSp 2 F} (hg : g ∈ spRad2 F) : s * g * s⁻¹ ∈ spRad2 F :=
  conj_mem_radFl (fun _ hw => mulVec_mem_of_mem_stabilizer_sp hs hw)
    (fun _ hw => mulVec_mem_of_mem_stabilizer_sp hs hw)
    (fun _ hw => mulVec_mem_of_mem_stabilizer_sp (inv_mem hs) hw)
    (fun _ hw => mulVec_mem_of_mem_stabilizer_sp (inv_mem hs) hw) hg

theorem spRad1_le_stabilizer : spRad1 F ≤ stabilizer 2 F (flag 2 F 1) := by
  rintro g ⟨hg1, hg2, hg3⟩
  rw [mem_stabilizer]
  refine le_antisymm ?_ fun w hw => ⟨w, hw, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, hg1 w hw]
    exact hw
  · rw [mulVecLin_apply, hg1 w hw]

theorem spRad2_le_stabilizer : spRad2 F ≤ stabilizer 2 F (flag 2 F 2) := by
  rintro g ⟨hg1, hg2, hg3⟩
  rw [mem_stabilizer]
  refine le_antisymm ?_ fun w hw => ⟨w, hw, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, hg1 w hw]
    exact hw
  · rw [mulVecLin_apply, hg1 w hw]

@[expose] noncomputable def siegelElt (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C) : StatedSp 2 F :=
  upperUnipotentSp 2 F hC

theorem coe_siegelElt (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C) :
    (((siegelElt C hC : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 1 C 0 1 :=
  coe_upperUnipotentSp hC

theorem siegel_mulVec (C : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 ⊕ Fin 2 → F) :
    fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C 0 1 *ᵥ x =
      Sum.elim ((x ∘ Sum.inl) + C *ᵥ (x ∘ Sum.inr)) (x ∘ Sum.inr) := by
  rw [fromBlocks_mulVec]
  simp

theorem siegelElt_mem_spRad2 (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C) :
    siegelElt C hC ∈ spRad2 F := by
  have key : ∀ w ∈ flag 2 F 2, fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C 0 1 *ᵥ w = w := by
    intro w hw
    obtain ⟨h0, h1⟩ := mem_flag_two_two.mp hw
    have hr : w ∘ Sum.inr = 0 := by
      funext j
      fin_cases j
      · exact h0
      · exact h1
    rw [siegel_mulVec, hr]
    funext x
    rcases x with i | i
    · simp
    · simpa using (congrFun hr i).symm
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun x => ?_⟩
  · rw [coe_siegelElt]
    exact key w hw
  · rw [coe_siegelElt, key w hw, sub_self]
    exact Submodule.zero_mem _
  · rw [coe_siegelElt, siegel_mulVec, mem_flag_two_two]
    simp

theorem siegelElt_mem_spRad1 (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C) (h11 : C 1 1 = 0) :
    siegelElt C hC ∈ spRad1 F := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun x => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := mem_flag_two_one.mp hw
    have hr : w ∘ Sum.inr = 0 := by
      funext j
      fin_cases j
      · exact h1
      · exact h2
    rw [coe_siegelElt, siegel_mulVec, hr]
    funext x
    rcases x with i | i
    · simp
    · simpa using (congrFun hr i).symm
  · have h0 := mem_flag_two_three.mp hw
    rw [coe_siegelElt, siegel_mulVec, mem_flag_two_one]
    simp [Matrix.vecHead, Matrix.vecTail, h0, h11]
  · rw [coe_siegelElt, siegel_mulVec, mem_flag_two_three]
    simp

@[expose] def levUnit : GL (Fin 2) F :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[expose] noncomputable def leviElt : StatedSp 2 F :=
  SymplecticTorusWeyl.leviSp (levUnit (F := F))

theorem coe_leviElt :
    (((leviElt : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks !![1, 1; 0, 1] 0 0 !![1, 0; -1, 1] := by
  rw [leviElt, SymplecticTorusWeyl.coe_leviSp]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem levi_mulVec (x : Fin 2 ⊕ Fin 2 → F) :
    fromBlocks (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 !![1, 0; -1, 1] *ᵥ x =
      Sum.elim (!![1, 1; 0, 1] *ᵥ (x ∘ Sum.inl)) (!![1, 0; -1, 1] *ᵥ (x ∘ Sum.inr)) := by
  rw [fromBlocks_mulVec]
  simp

theorem leviElt_mem_spRad1 : (leviElt : StatedSp 2 F) ∈ spRad1 F := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun x => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := mem_flag_two_one.mp hw
    rw [coe_leviElt, levi_mulVec]
    funext x
    rcases x with i | i
    · fin_cases i
      · simp [dotProduct, Fin.sum_univ_two, h0]
      · simp [dotProduct, Fin.sum_univ_two, h0]
    · fin_cases i
      · simp [dotProduct, Fin.sum_univ_two, h1, h2]
      · simp [dotProduct, Fin.sum_univ_two, h1, h2]
  · have h0 := mem_flag_two_three.mp hw
    rw [coe_leviElt, levi_mulVec, mem_flag_two_one]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [dotProduct, Fin.sum_univ_two, h0]
  · rw [coe_leviElt, levi_mulVec, mem_flag_two_three]
    simp [dotProduct, Fin.sum_univ_two]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
