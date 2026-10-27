module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T F : Subgroup Γ}

theorem iSup_map_aut_characteristic {B : Type*} [Group B] (W : Subgroup B) :
    (⨆ α : B ≃* B, W.map α.toMonoidHom).Characteristic := by
  have hmap : ∀ φ : B ≃* B,
      (⨆ α : B ≃* B, W.map α.toMonoidHom).map φ.toMonoidHom =
        ⨆ α : B ≃* B, W.map α.toMonoidHom := by
    intro φ
    apply le_antisymm
    · rw [Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_map]
      exact le_iSup (fun β : B ≃* B => W.map β.toMonoidHom) (α.trans φ)
    · refine iSup_le fun α => ?_
      have : W.map α.toMonoidHom =
          (W.map (α.trans φ.symm).toMonoidHom).map φ.toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp
      rw [this]
      exact Subgroup.map_mono (le_iSup (fun β : B ≃* B => W.map β.toMonoidHom) (α.trans φ.symm))
  refine ⟨fun φ => ?_⟩
  have h := hmap φ.symm
  ext x
  constructor
  · intro hx
    have : x ∈ (⨆ α : B ≃* B, W.map α.toMonoidHom).map φ.symm.toMonoidHom :=
      ⟨φ x, hx, by simp⟩
    rwa [h] at this
  · intro hx
    have : φ x ∈ (⨆ α : B ≃* B, W.map α.toMonoidHom).map φ.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmap φ] at this

theorem exists_aut_not_le_centralizer (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hF : IsBTBlock G T F) (hFC : ¬ F ≤ cStarIn G T) (hWB : blockW F ≤ baum T) :
    ∃ α : ↥(baum T) ≃* ↥(baum T),
      ¬ (((blockW F).subgroupOf (baum T)).map α.toMonoidHom ≤
        Subgroup.centralizer
          ((((blockW F).subgroupOf (baum T) : Subgroup ↥(baum T))) : Set ↥(baum T))) := by
  classical
  by_contra hcon
  push Not at hcon
  set B : Subgroup Γ := baum T with hB
  set W : Subgroup Γ := blockW F with hW
  set WB : Subgroup ↥B := W.subgroupOf B with hWB'
  set Wstar : Subgroup ↥B := ⨆ α : ↥B ≃* ↥B, WB.map α.toMonoidHom with hWstar
  set Wst : Subgroup Γ := Wstar.map B.subtype with hWst
  have hBN : B ≤ Subgroup.normalizer (F : Set Γ) := baum_le_normalizer_of_isBTBlock hF
  have hWF : W = pCoreOf 2 F := blockW_eq_pCoreOf hF
  have hFcent : F ⊓ Subgroup.centralizer (W : Set Γ) = W := by
    rw [hWF]
    exact inf_centralizer_pCoreOf_eq (charTwo_of_isBTBlock hG hT hF) hF.elemAbelian.1
  have hWnormF : F ≤ Subgroup.normalizer (W : Set Γ) := by
    rw [hWF]; exact le_normalizer_pCoreOf_self F
  have hWWstar : WB ≤ Wstar :=
    le_iSup_of_le (MulEquiv.refl ↥B) (by simp)
  have hWstle : Wstar ≤ Subgroup.centralizer (WB : Set ↥B) := iSup_le hcon
  have hWWst : W ≤ Wst := by
    intro x hx
    have hxB : x ∈ B := hWB hx
    exact ⟨⟨x, hxB⟩, hWWstar (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hWne : W ≠ ⊥ := by
    rw [hWF]
    exact pCoreOf_ne_bot hF (charTwo_of_isBTBlock hG hT hF)
  have hWstne : Wst ≠ ⊥ := by
    intro h
    apply hWne
    rw [eq_bot_iff]
    exact (hWWst.trans h.le)
  have hWstB : Wst ≤ B := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hchar : (Wst.subgroupOf B).Characteristic := by
    have h1 : Wst.subgroupOf B = Wstar :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective Wstar
    rw [h1]
    exact iSup_map_aut_characteristic WB
  have hcentW : ∀ w ∈ Wst, ∀ x ∈ W, w * x = x * w := by
    rintro _ ⟨wB, hwB, rfl⟩ x hx
    have hxB : x ∈ B := hWB hx
    have h1 := Subgroup.mem_centralizer_iff.mp (hWstle hwB) ⟨x, hxB⟩
      (Subgroup.mem_subgroupOf.mpr hx)
    have h2 := congrArg Subtype.val h1
    exact h2.symm
  have hmain : ∀ f ∈ F, ∀ w ∈ Wst, f * w * f⁻¹ ∈ Wst := by
    intro f hf w hw
    have hwB : w ∈ B := hWstB hw
    have hwf : w * f * w⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hBN hwB) f).mp hf
    set c : Γ := f⁻¹ * (w * f * w⁻¹) with hc
    have hcF : c ∈ F := F.mul_mem (F.inv_mem hf) hwf
    have hcC : c ∈ Subgroup.centralizer (W : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have e1 : w * h = h * w := hcentW w hw h hh
      have e2 : w * (f * h * f⁻¹) = (f * h * f⁻¹) * w :=
        hcentW w hw _ ((Subgroup.mem_normalizer_iff.mp (hWnormF hf) h).mp hh)
      have e3 : h * w⁻¹ = w⁻¹ * h := by
        have : w⁻¹ * (w * h) * w⁻¹ = w⁻¹ * (h * w) * w⁻¹ := by rw [e1]
        simpa [mul_assoc] using this
      calc h * c = f⁻¹ * ((f * h * f⁻¹) * w) * f * w⁻¹ := by rw [hc]; group
        _ = f⁻¹ * (w * (f * h * f⁻¹)) * f * w⁻¹ := by rw [e2]
        _ = f⁻¹ * w * f * (h * w⁻¹) := by group
        _ = f⁻¹ * w * f * (w⁻¹ * h) := by rw [e3]
        _ = c * h := by rw [hc]; group
    have hcW : c ∈ W := by
      have : c ∈ F ⊓ Subgroup.centralizer (W : Set Γ) := ⟨hcF, hcC⟩
      rwa [hFcent] at this
    have hfc : f * c⁻¹ * f⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWnormF hf) c⁻¹).mp (W.inv_mem hcW)
    have heq : f * w * f⁻¹ = (f * c⁻¹ * f⁻¹) * w := by rw [hc]; group
    rw [heq]
    exact Wst.mul_mem (hWWst hfc) hw
  have hFnorm : F ≤ Subgroup.normalizer (Wst : Set Γ) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hmain f hf h
    · intro hh
      have := hmain f⁻¹ (F.inv_mem hf) _ hh
      simpa [mul_assoc] using this
  apply hFC
  have hcg : G ⊓ Subgroup.normalizer (Wst : Set Γ) ≤ cgsIn G (baum T) :=
    le_iSup_of_le Wst (le_iSup_of_le hWstB (le_iSup_of_le hWstne (le_iSup_of_le hchar le_rfl)))
  exact (le_inf hF.le hFnorm).trans (hcg.trans le_sup_right)

end CFSG.CGT.PushingUpLit.BHS7
