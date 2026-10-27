module

public import CFSG.CGT.PushingUpLit.T2K.FourSevenA
public import CFSG.CGT.PushingUpLit.T2K.FourFiveF
public import CFSG.CGT.PushingUpLit.T2K.FourFour
public import CFSG.CGT.PushingUpLit.T2K.FourSix

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneCenterOf_eq_of_isElemAbelian {B : Subgroup G} (hB : IsElemAbelian 2 B) :
    omegaOneCenterOf B = B := by
  apply le_antisymm
  · unfold omegaOneCenterOf omegaOneOf
    rw [Subgroup.closure_le]
    rintro x ⟨hxZ, -⟩
    exact hxZ.1
  · intro b hb
    unfold omegaOneCenterOf omegaOneOf
    exact Subgroup.subset_closure ⟨⟨hb, Subgroup.mem_centralizer_iff.2 fun d hd =>
      (isElemAbelian_comm' hB hd hb)⟩, hB.2 b hb⟩

omit [Finite G] in
theorem thompsonJ_eq_of_unique {Q B : Subgroup G} (hB : IsMaxElemAbelian Q B)
    (huniq : ∀ D, IsMaxElemAbelian Q D → D = B) : thompsonJ Q = B := by
  apply le_antisymm
  · exact iSup_le fun D => iSup_le fun hD => (huniq D hD).le
  · exact le_thompsonJ' hB

structure Sit47 (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (g : G)
    (D : Subgroup G) : Prop where
  hyp : T2Hyp G L M n
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  S_elem : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))
  N_T : Subgroup.normalizer (T : Set G) ≤ M
  noG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4
  g_J : g ∈ Subgroup.normalizer (thompsonJ T : Set G)
  g_M : g ∉ M
  D_P : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D
  Dg_T : IsMaxElemAbelian T (D.map (MulAut.conj g).toMonoidHom)
  Dg_P : ¬ D.map (MulAut.conj g).toMonoidHom ≤ T ⊓ Subgroup.centralizer (blockU L : Set G)

@[expose] def Print47Campbell : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (g : G) (D : Subgroup G),
    Sit47 G L M T n g D →
    (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (blockU L : Set G)))).map
      (MulAut.conj g).toMonoidHom ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) →
    blockZ L = ⊥

@[expose] def Print47Final : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (g : G) (D : Subgroup G),
    Sit47 G L M T n g D →
    ¬ (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (blockU L : Set G)))).map
      (MulAut.conj g).toMonoidHom ≤ T ⊓ Subgroup.centralizer (blockU L : Set G) → False

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
  (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
include h hE1 hT

omit hE1 hT in
theorem mem_of_normalized {X : Subgroup G} {g : G} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hL : L ≤ Subgroup.normalizer (X : Set G))
    (hLg : L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (X : Set G)) : g ∈ M := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (X : Set G)) := ⟨X, hX, hX2, rfl⟩
  obtain ⟨N, hle, hNmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hloc
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun x hx => hle (hL hx)⟩
    rw [h.unique] at this
    exact this
  have hN' : IsMaximalTwoLocal (M.map (MulAut.conj g⁻¹).toMonoidHom) :=
    RankThree.PartTwo.Late.isMaximalTwoLocal_map h.maxLocal (MulAut.conj g⁻¹)
  have hLN' : L ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro l hl
    have hmem : g * l * g⁻¹ ∈ M := by
      rw [← hNM]
      exact hle (hLg ⟨l, hl, rfl⟩)
    exact ⟨g * l * g⁻¹, hmem, by simp [mul_assoc]⟩
  have hN'M : M.map (MulAut.conj g⁻¹).toMonoidHom = M := by
    have : M.map (MulAut.conj g⁻¹).toMonoidHom ∈ maximalTwoLocalsContaining (L : Set G) :=
      ⟨hN', hLN'⟩
    rw [h.unique] at this
    exact this
  have hginv := RankThree.PartTwo.Late.mem_of_map_conj_eq_of_isMaximalTwoLocal h.maxLocal hN'M
  have := M.inv_mem hginv
  rwa [inv_inv] at this

omit [Finite G] h hE1 hT in
theorem normalizer_map_conj_of_le {D : Subgroup G} {g : G}
    (hL : L ≤ Subgroup.normalizer (D : Set G)) :
    L.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have h1 := Subgroup.mem_normalizer_iff.1 (hL hl) (g⁻¹ * x * g)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e2 : g⁻¹ * (g * l * g⁻¹ * x * (g * l * g⁻¹)⁻¹) * g = l * (g⁻¹ * x * g) * l⁻¹ := by
    group
  rw [e2]
  exact h1

theorem four_seven (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hE5 : Aschbacher78One) (hnG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4)
    (hCamp : Print47Campbell) (hFinal : Print47Final) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  obtain ⟨-, hS, -⟩ := h.four_four hE1 hE8 h25 hT
  have hN4 := h.four_six hE1 hE5 hT hnG4
  obtain ⟨D, hD, hDg, hDgP⟩ := h.exists_member_conj_not_le hE1 hT hg hgM
  have hsit : Sit47 G L M T n g D := ⟨h, hT, hS, hN4, hnG4, hg, hgM, hD, hDg, hDgP⟩
  by_cases hUP : (omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (blockU L : Set G)))).map
      (MulAut.conj g).toMonoidHom ≤ T ⊓ Subgroup.centralizer (blockU L : Set G)
  · have hZ : blockZ L = ⊥ := hCamp G L M T n g D hsit hUP
    have hAnt : ¬ D.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (blockU L : Set G) :=
      fun hc => hDgP (le_inf hDg.1 hc)
    have H : Hyp45 L M T (D.map (MulAut.conj g).toMonoidHom) n :=
      ⟨h.natBlock, h.le, h.normal hE1, hT, hDg, hAnt⟩
    have huniq : ∀ D', IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D' →
        D' = D := by
      rcases H.four_five_six hZ hS with ⟨-, -, hA'⟩ | ⟨-, -, hP'⟩
      · intro D' hD'
        have hD'g := h.isMaxElemAbelian_T_map_conj hE1 hT hg hD'
        have hnot : ¬ D'.map (MulAut.conj g).toMonoidHom ≤
            T ⊓ Subgroup.centralizer (blockU L : Set G) := by
          intro hle
          have hX := isMaxElemAbelian_P_of_le hD'g hle
          have hD'0 : D' ≠ ⊥ := fun hbot =>
            h.blockU_ne_bot (le_bot_iff.1 (hbot ▸ h.blockU_le_of_isMaxElemAbelian_P hE1 hT hD'))
          refine hgM (h.mem_of_normalized (X := D'.map (MulAut.conj g).toMonoidHom) ?_
            (hT.isPGroup.to_le hD'g.1) (H.le_normalizer_of_isMaxElemAbelian_P hX)
            (normalizer_map_conj_of_le (H.le_normalizer_of_isMaxElemAbelian_P hD')))
          intro hbot
          apply hD'0
          refine Subgroup.eq_bot_of_card_eq _ ?_
          rw [← card_map_conj D' g, hbot, Subgroup.card_bot]
        exact Subgroup.map_injective (MulAut.conj g).injective
          (hA' _ hD'g (fun hc => hnot (le_inf hD'g.1 hc)))
      · intro D' hD'
        exact (hP' D' hD').trans (hP' D hD).symm
    have hE : omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (blockU L : Set G))) = D := by
      rw [thompsonJ_eq_of_unique hD huniq]
      exact omegaOneCenterOf_eq_of_isElemAbelian hD.2.1
    rw [hE] at hUP
    exact hDgP hUP
  · exact hFinal G L M T n g D hsit hUP

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
