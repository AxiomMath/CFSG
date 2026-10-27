module

public import CFSG.CGT.PushingUpLit.BHS6.NestedFamily
public import CFSG.CGT.PushingUpLit.BHS6.NestedLinear
public import CFSG.CGT.PushingUpLit.BHS6.NestedPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

theorem exists_altOn_nested (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {n : ℕ} (hn3 : 3 ≤ n) (hodd : Odd n) {W : Subgroup Γ} (hWE : W = pCoreOf 2 E)
    (βe : ↥W ≃* ↥(coreMod n)) (Ψ : ↥E →* Equiv.Perm (Fin n))
    (hΨ : ∀ (e : ↥E) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
      βe ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = coreAct n (Ψ e) (βe w))
    (hF : IsBTBlock G T F) (hFE : F ≤ E) {r : ℕ} (hr : 1 ≤ r) (hFr : IsNaturalAltModule ↥F r) :
    ∃ Ω₀ : Finset (Fin n), Ω₀.card = 2 * r + 1 ∧ (∀ f : ↥F, Ψ ⟨f, hFE f.2⟩ ∈ altOn Ω₀) ∧
      (∀ π ∈ altOn Ω₀, ∃ f : ↥F, Ψ ⟨f, hFE f.2⟩ = π) ∧
      ∀ x, x ∈ Ω₀ ↔ ∃ f : ↥F, Ψ ⟨f, hFE f.2⟩ x ≠ x := by
  classical
  subst hWE
  have hF' : F ∈ btBlocksG G T := mem_btBlocksG_of_isBTBlock hF
  have hWe : IsElemAbelian 2 (pCoreOf 2 E) :=
    isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥(pCoreOf 2 E) := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hFW : F ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := hFE.trans hEW
  set Θ : ↥F →* Equiv.Perm (Fin n) := Ψ.comp (Subgroup.inclusion hFE) with hΘ
  set Ft : Subgroup (Equiv.Perm (Fin n)) := Θ.range with hFt
  have hFres : opResidual 2 F = F := opResidual_eq_of_isBTBlock hF
  have hFtres : opResidual 2 Ft = Ft := opResidual_range_of_eq hFres Θ
  have hA : Ft.map (coreAct n) = (autOn F (pCoreOf 2 E)).map (MulAut.congr βe).toMonoidHom := by
    have h1 : (coreAct n).comp Θ =
        (MulAut.congr βe).toMonoidHom.comp (actOn (pCoreOf 2 E) F hFW) := by
      refine MonoidHom.ext fun f => MulEquiv.ext fun d => ?_
      obtain ⟨w, rfl⟩ := βe.surjective d
      show (coreAct n (Ψ ⟨(f : Γ), hFE f.2⟩)) (βe w) =
        (MulAut.congr βe (actOn (pCoreOf 2 E) F hFW f)) (βe w)
      rw [congr_apply_apply]
      have hw : (f : Γ) * (w : Γ) * (f : Γ)⁻¹ ∈ pCoreOf 2 E :=
        (Subgroup.mem_normalizer_iff.mp (hFW f.2) w).mp w.2
      have h3 : (actOn (pCoreOf 2 E) F hFW f) w = ⟨(f : Γ) * (w : Γ) * (f : Γ)⁻¹, hw⟩ :=
        Subtype.ext (actOn_apply_coe hFW f w)
      rw [h3]
      exact (hΨ ⟨(f : Γ), hFE f.2⟩ w hw).symm
    rw [← MonoidHom.range_comp, h1, MonoidHom.range_comp, range_actOn]
  have hirr : IsIrrSection (Ft.map (coreAct n))
      (commV (Ft.map (coreAct n)) ⊔ fixV (Ft.map (coreAct n))) (fixV (Ft.map (coreAct n))) :=
    isIrrSection_eq_map_congr βe hA (isIrrSection_autOn_nested hG hT hE hF' hFE hWe)
  have hW'W : pCoreOf 2 F ≤ pCoreOf 2 E := pCoreOf_le_of_le_block hG hT hE hF' hFE
  have hW'card : Nat.card ↥(pCoreOf 2 F) = Nat.card ↥(coreMod (2 * r + 1)) := by
    have hWe' : IsElemAbelian 2 (pCoreOf 2 F) :=
      isElemAbelian_of_forall' hF.elemAbelian.1 hF.elemAbelian.2
    let _ : CommGroup ↥(pCoreOf 2 F) := commGroupOfElemAbelian hWe'
    obtain ⟨D', -, -, hβ'bij, -⟩ := block_structure_symm hG hT hF hr hFr rfl hWe'
    exact Nat.card_congr (Equiv.ofBijective D'.β hβ'bij)
  have hcV : Nat.card ↥(commV (Ft.map (coreAct n))) = Nat.card ↥(coreMod (2 * r + 1)) := by
    refine (card_commV_eq_map_congr βe hA).trans ?_
    have h1 : commV (autOn F (pCoreOf 2 E)) = (pCoreOf 2 F).subgroupOf (pCoreOf 2 E) := by
      have := commOn_eq hWe hFW
      rw [commutator_eq_pCoreOf_nested hG hT hE hF' hFE] at this
      exact this
    rw [h1, ← hW'card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'W).toEquiv
  have hnatF : IsNatAlt F (pCoreOf 2 F) (2 * r + 1) := by
    have := isNatAlt_of_isBTBlock hG hT hF hFr
    rwa [blockW_eq_pCoreOf hF] at this
  have hcharF : CharTwo F := charTwo_of_isBTBlock hG hT hF
  have hW'ab : ∀ x ∈ pCoreOf 2 F, ∀ y ∈ pCoreOf 2 F, x * y = y * x := hF.elemAbelian.1
  have hcapF : F ⊓ Subgroup.centralizer (pCoreOf 2 F : Set Γ) = pCoreOf 2 F :=
    le_antisymm hcharF fun w hw =>
      Subgroup.mem_inf.mpr ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F hw,
        Subgroup.mem_centralizer_iff.mpr fun y hy => hW'ab y hy w hw⟩
  have hautF : Nat.card ↥(autOn F (pCoreOf 2 E)) =
      Nat.card ↥(alternatingGroup (Fin (2 * r + 1))) := by
    rw [card_autOn_eq_relIndex hFW, inf_centralizer_pCoreOf_nested hG hT hE hF' hFE]
    obtain ⟨hF1, -⟩ := relIndex_of_isNatBy hnatF
    rw [hcapF] at hF1
    exact hF1
  have hcF : Nat.card ↥Ft = (2 * r + 1).factorial / 2 := by
    have h1 : Nat.card ↥Ft = Nat.card ↥(autOn F (pCoreOf 2 E)) := by
      have e1 : Nat.card ↥(Ft.map (coreAct n)) = Nat.card ↥Ft :=
        Subgroup.card_map_of_injective (coreAct_injective hn3)
      have e2 : Nat.card ↥((autOn F (pCoreOf 2 E)).map (MulAut.congr βe).toMonoidHom) =
          Nat.card ↥(autOn F (pCoreOf 2 E)) :=
        Subgroup.card_map_of_injective (MulAut.congr βe).injective
      rw [← e1, hA, e2]
    rw [h1, hautF]
    have : Nontrivial (Fin (2 * r + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨hFtAlt, hFtcard⟩ := eq_altOn_movFin_of_card hodd hFtres hirr ⟨r, rfl⟩ hcV hcF
  refine ⟨movFin Ft, hFtcard, fun f => ?_, fun π hπ => ?_, fun x => ?_⟩
  · rw [← hFtAlt]
    exact ⟨f, rfl⟩
  · rw [← hFtAlt] at hπ
    obtain ⟨f, hf⟩ := hπ
    exact ⟨f, hf⟩
  · rw [mem_movFin]
    constructor
    · rintro ⟨π, ⟨f, rfl⟩, hπx⟩
      exact ⟨f, hπx⟩
    · rintro ⟨f, hfx⟩
      exact ⟨Θ f, ⟨f, rfl⟩, hfx⟩

end CFSG.CGT.PushingUpLit.BHS7
