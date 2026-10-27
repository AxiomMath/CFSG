module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Models
public import CFSG.GH74.Generic.S45.LEvSporM12Spec
public import Certificates.Certificate397508

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3 CFSG.GH74.KGroups
  CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover

set_option linter.unusedSectionVars false

theorem firstBlock_iff {δ : Equiv.Perm (Fin 24)}
    (hδ : δ ∈ autModel) : firstBlock δ = true ↔ δ ∈ blockGroup := by
  have h00 : (0 : Fin 24) = Fin.castAdd 12 (0 : Fin 12) := by decide
  unfold firstBlock
  rw [decide_eq_true_iff]
  constructor
  · intro h0
    rcases mem_autModel.1 hδ with h | h
    · exact h
    · exfalso
      obtain ⟨⟨p, q⟩, -, hp⟩ := mem_blockGroup.1 h
      have hδ' : δ = m12Sigma * blockHom (p, q) := by
        rw [hp, ← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]
      rw [hδ', Equiv.Perm.mul_apply, h00, blockHom_castAdd, sigma_castAdd, Fin.val_natAdd] at h0
      omega
  · intro h
    obtain ⟨⟨p, q⟩, -, hp⟩ := mem_blockGroup.1 h
    rw [← hp, h00, blockHom_castAdd]
    exact (p 0).isLt

theorem normal_blockGroup_subgroupOf :
    (blockGroup.subgroupOf autModel).Normal := by
  rw [Subgroup.normal_subgroupOf_iff blockGroup_le_autModel]
  intro x g hx hg
  exact autModel_conj_mem hg x hx


theorem leaf_m12
    {n : ℕ} : TwinLeafS n SmallM12 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hF => by
    haveI := h.core.simple
    haveI := genFittingFStar_normal Y
    haveI := normal_blockGroup_subgroupOf
    obtain ⟨e⟩ := hF
    obtain ⟨f, hf⟩ := embedsAut_of_exactModel GH74.Generic.S45.EvSpor.m12_smallAutModel
      (e.trans m12EquivD) Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
      (Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab)
    refine false_of_nqCheck h (ι := autModel.subtype) Subtype.val_injective
      (L := elemsT m12D ++ (elemsT m12D).map (fun d => m12Sigma * d)) ?_
      (inX := firstBlock) (X := blockGroup.subgroupOf autModel)
      (fun y => (firstBlock_iff y.2).trans Subgroup.mem_subgroupOf.symm)
      Certificates.certificate397508.2.2.2 hf
    intro m
    rw [List.mem_append, List.mem_map, mem_elemsT m12D m12D_check.1 m]
    constructor
    · rintro (hm | ⟨d, hd', rfl⟩)
      · exact ⟨⟨m, mem_autModel.2 (Or.inl hm)⟩, rfl⟩
      · refine ⟨⟨m12Sigma * d, mem_autModel.2 (Or.inr ?_)⟩, rfl⟩
        rw [← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]
        exact (mem_elemsT m12D m12D_check.1 d).1 hd'
    · rintro ⟨⟨y, hy⟩, rfl⟩
      rcases mem_autModel.1 hy with hy' | hy'
      · exact Or.inl hy'
      · exact Or.inr ⟨m12Sigma * y, (mem_elemsT m12D m12D_check.1 _).2 hy',
          by rw [← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]; rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM
