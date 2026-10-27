module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameConj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameCount
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Open CFSG.EvenSmallLie.OmegaEightMinus

theorem omega8_frameProps (hM : Omega8FrameModel) {J' : Subgroup omegaT}
    (hab : IsElemAbelian 3 J') (hcard : Nat.card J' = 27) :
    FrameProps (fun x : omegaT => (x : Equiv.Perm (Fin 136)).support.card) 108 ⊤ J' := by
  obtain ⟨J₀, T₀, hJT, hTΩ, hT81, -, -, huniq, hF⟩ := hM.frame
  have hJΩ : J₀ ≤ omegaT := hJT.trans hTΩ
  have hT1 : Nat.card (T₀.subgroupOf omegaT) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΩ).toEquiv, hT81]
  refine FrameProps.of_sylow (J₀ := J₀.subgroupOf omegaT) (T₀ := T₀.subgroupOf omegaT)
    (fun g x => ?_) (IsPGroup.of_card (n := 4) (by rw [hT1]; norm_num)) ?_ ?_
    (hF.subgroupOf hJΩ) hab hcard
  · simp [Equiv.Perm.card_support_conj]
  · have h := (T₀.subgroupOf omegaT).card_mul_index
    rw [hT1, hM.card] at h
    omega
  · intro J'' hJ'' hab'' hcard''
    have hle : J''.map omegaT.subtype ≤ T₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hJ'' hx
    have heq := huniq _ hle (hab''.map _)
      (by rw [Subgroup.card_map_of_injective omegaT.subtype_injective, hcard''])
    rw [← heq]
    exact (Subgroup.comap_map_eq_self_of_injective omegaT.subtype_injective J'').symm

theorem kFactOmega8Frame_of_model (hM : Omega8FrameModel) : KFactOmega8Frame := by
  intro Y _ _ L d hd hLn hne J hJL hJab hJcard
  haveI := hLn
  classical
  obtain ⟨φ⟩ := hM.bridge L d hd hne
  let ν : Y → ℕ := fun y =>
    if hy : y ∈ L then ((φ ⟨y, hy⟩ : omegaT) : Equiv.Perm (Fin 136)).support.card else 0
  let θ : omegaT →* Y := L.subtype.comp φ.symm.toMonoidHom
  have hθ : Function.Injective θ := L.subtype_injective.comp φ.symm.injective
  have hθL : ∀ x, θ x ∈ L := fun x => (φ.symm x).2
  have hνθ : ∀ x : omegaT, ν (θ x) = ((x : omegaT) : Equiv.Perm (Fin 136)).support.card := by
    intro x
    have h1 : (⟨θ x, hθL x⟩ : L) = φ.symm x := rfl
    simp only [ν, dif_pos (hθL x), h1, MulEquiv.apply_symm_apply]
  have hconj : ∀ (y : Y), ∀ x ∈ L, ν (y * x * y⁻¹) = ν x := by
    intro y x hx
    have hx' : y * x * y⁻¹ ∈ L := hLn.conj_mem x hx y
    have h1 := hM.aut ((φ.symm.trans (MulAut.conjNormal y)).trans φ) (φ ⟨x, hx⟩)
    have h2 : ((φ.symm.trans (MulAut.conjNormal y)).trans φ) (φ ⟨x, hx⟩) =
        φ ⟨y * x * y⁻¹, hx'⟩ := by
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg φ (Subtype.ext (MulAut.conjNormal_apply y ⟨x, hx⟩))
    rw [h2] at h1
    simpa only [ν, dif_pos hx, dif_pos hx'] using h1
  have hinv : ∀ x ∈ L, ν x⁻¹ = ν x := by
    intro x hx
    have h1 : (⟨x⁻¹, L.inv_mem hx⟩ : L) = (⟨x, hx⟩ : L)⁻¹ := rfl
    simp only [ν, dif_pos hx, dif_pos (L.inv_mem hx), h1, map_inv, Subgroup.coe_inv,
      Equiv.Perm.support_inv]
  have hJ'ab : IsElemAbelian 3 ((J.subgroupOf L).map φ.toMonoidHom) :=
    (hJab.subgroupOf L).map _
  have hJ'card : Nat.card ((J.subgroupOf L).map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv, hJcard]
    norm_num
  have hFY := (omega8_frameProps hM hJ'ab hJ'card).map θ hθ hνθ
  have hR : (⊤ : Subgroup omegaT).map θ = L := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact hθL x
    · intro hy
      exact ⟨φ ⟨y, hy⟩, trivial, by simp [θ]⟩
  have hθφ : θ.comp φ.toMonoidHom = L.subtype := by
    ext z
    simp [θ]
  have hJe : ((J.subgroupOf L).map φ.toMonoidHom).map θ = J := by
    rw [Subgroup.map_map, hθφ]
    exact Subgroup.map_subgroupOf_eq_of_le hJL
  rw [hR, hJe] at hFY
  refine ⟨hFY.relIndex_dvd (fun x hx => hJab.2 x hx) (fun y _ x hx => hconj y x (hJL hx))
    (fun x hx => hinv x (hJL hx)), ?_⟩
  intro b hb hb3 hrel
  exact hFY.simple b hb (hFY.eq_of_relIndex_eq_three hb hb3 hrel)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
