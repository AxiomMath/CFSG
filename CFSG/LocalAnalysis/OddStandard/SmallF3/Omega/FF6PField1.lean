module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PStarN1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6p_sylow_E16 :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧
      IsNormalE16In P B₂ ∧ ∀ B : Subgroup G, IsNormalE16In P B → B = B₁ ∨ B = B₂ := by
  intro G _ _ L h P hP
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ⟩ := ff6p_exists_model_P h hP
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center h
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hPL : P ≤ L := hP.1
  have hP2 : IsPGroup 2 P := hP.2.1
  obtain ⟨y0, hy0G, hy0⟩ := ff6p_exists_y0 hQ hdim hsgn h2 fr
  let B2p : Subgroup ↥(omegaProj hQ) :=
    (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom
  have hB1le : ffB1p hQ fr ≤ ffImg (ff6mPhi e) P := by
    rw [hPφ]; exact ffB1p_le_ffP1p hQ fr
  have hB2p_norm : IsNormalE16In (ffP1p hQ fr) B2p :=
    ff6p_map_normalE16 hQ h2 fr hy0 (ffB1p_normalE16 hQ hπ fr)
  have hB2le : B2p ≤ ffImg (ff6mPhi e) P := by rw [hPφ]; exact hB2p_norm.1
  obtain ⟨B₁, hB₁P, hB₁φ⟩ := ff_cover_exists_of_le_img hφ hPL hP2 hB1le
  obtain ⟨B₂, hB₂P, hB₂φ⟩ := ff_cover_exists_of_le_img hφ hPL hP2 hB2le
  have hn₁ : IsNormalE16In P B₁ := by
    rw [ff_cover_normalE16_iff hφ hPL hP2 hB₁P, hPφ, hB₁φ]
    exact ffB1p_normalE16 hQ hπ fr
  have hn₂ : IsNormalE16In P B₂ := by
    rw [ff_cover_normalE16_iff hφ hPL hP2 hB₂P, hPφ, hB₂φ]
    exact hB2p_norm
  have hne : B₁ ≠ B₂ := by
    intro h12
    have hB2eq : B2p = ffB1p hQ fr := by rw [← hB₂φ, ← hB₁φ, h12]
    exact ff6p_B2_ne hQ h2 fr hy0G hB2eq
  refine ⟨B₁, B₂, hne, hn₁, hn₂, ?_⟩
  intro B hB
  have hB' : IsNormalE16In (ffP1p hQ fr) (ffImg (ff6mPhi e) B) := by
    have := (ff_cover_normalE16_iff hφ hPL hP2 hB.1).mp hB
    rwa [hPφ] at this
  rcases ff6p_normalE16_cases hQ hdim hsgn h2 fr hy0G hy0 hB' with h | h
  · exact Or.inl (ff_cover_img_injective hφ hPL hP2 hB.1 hB₁P (h.trans hB₁φ.symm))
  · exact Or.inr (ff_cover_img_injective hφ hPL hP2 hB.1 hB₂P (h.trans hB₂φ.symm))

theorem ff6p_center_le :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B → centerIn P ≤ B := by
  intro G _ _ L h P hP B hB
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ⟩ := ff6p_exists_model_P h hP
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center h
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hPL : P ≤ L := hP.1
  have hP2 : IsPGroup 2 P := hP.2.1
  intro g hg
  have hg' : g ∈ (Subgroup.center P).map P.subtype := hg
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg'
  have hgP : g ∈ P := by rw [← hxg]; exact x.2
  have hgc : ∀ m ∈ P, g * m = m * g := by
    intro m hm
    have hxcomm : m * (x : G) = (x : G) * m := by
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨m, hm⟩)
    rw [← hxg]
    exact hxcomm.symm
  let l : ↥L := ⟨g, hPL hgP⟩
  let w : ↥(omegaProj hQ) := ff6mPhi e l
  have hwP1 : w ∈ ffP1p hQ fr := by
    have hw : w ∈ ffImg (ff6mPhi e) P := by
      rw [mem_ffImg_iff]; exact ⟨l, hgP, rfl⟩
    rwa [hPφ] at hw
  have hwcomm : ∀ h' ∈ ffP1p hQ fr, h' * w = w * h' := by
    intro h' hh'
    have hh'P : h' ∈ ffImg (ff6mPhi e) P := by rw [hPφ]; exact hh'
    obtain ⟨m, hmP, hmφ⟩ := mem_ffImg_iff.mp hh'P
    have hml : m * l = l * m := by
      apply Subtype.ext
      exact (hgc (m : G) hmP).symm
    rw [← hmφ]
    show ff6mPhi e m * ff6mPhi e l = ff6mPhi e l * ff6mPhi e m
    rw [← map_mul, ← map_mul, hml]
  have hB' : IsNormalE16In (ffP1p hQ fr) (ffImg (ff6mPhi e) B) := by
    have := (ff_cover_normalE16_iff hφ hPL hP2 hB.1).mp hB
    rwa [hPφ] at this
  have hwB : w ∈ ffImg (ff6mPhi e) B := by
    rcases ffP1p_center hQ hπ fr hwP1 hwcomm with hw1 | hwz
    · rw [hw1]; exact (ffImg (ff6mPhi e) B).one_mem
    · rw [hwz]; exact ffZ0s_mem_normalE16 hQ hπ fr hB'
  obtain ⟨l', hl'B, hl'φ⟩ := mem_ffImg_iff.mp hwB
  have hl'P : (l' : G) ∈ P := hB.1 hl'B
  have heq : l = l' := ff_cover_eq_of_pGroup hφ hP2 hgP hl'P hl'φ.symm
  have hg_eq : g = (l' : G) := by
    show (l : G) = (l' : G)
    exact congrArg Subtype.val heq
  rw [hg_eq]
  exact hl'B

theorem ff6p_aut_B (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      QuotEquivTo (L ⊓ normalizer (B : Set G)) B (Equiv.Perm (Fin 5)) ∧
        L ⊓ centralizer (B : Set G) = B ∧
        ∃ φ : (Fin 5 → ZMod 2) → G,
          IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤ := by
  intro G _ _ L h P hP B hB
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ, hBφ⟩ := ff6p_exists_model_PB h hP hB
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center h
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc h
  let Φ : ↥L ≃* ↥(omegaProj hQ) := ffPhi hz e
  have hΦ : Φ.toMonoidHom = ff6mPhi e := ff6p_ffPhi_eq hQ hz e
  have hBL : B ≤ L := hB.1.trans hP.1
  have hBcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hB.2.1.1.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact ffIso_quotEquivTo Φ hBL (by
      rw [hΦ, hBφ]; exact ff6p_star_quotEquivTo hQ hdim hsgn fr)
  · refine ffIso_centralizer Φ hBL hBcomm ?_
    intro n hn
    rw [hΦ, hBφ] at hn ⊢
    exact ff6p_star_centralizer hQ hdim hsgn fr hn
  · exact ffIso_permModule_to Φ hBL (by
      rw [hΦ, hBφ]; exact ff6p_star_permModule hQ hdim hsgn fr)

end CFSG.OddStandard.SmallF3.Omega
