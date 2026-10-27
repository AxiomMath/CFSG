module

public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.RouteD.LocalLift

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv suppGroup coords pairPlanes form
  IsAdaptedShortIn shortBlock shortGroupNeg SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagTorus2)
open scoped MatrixGroups commutatorElement

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

section Lift

theorem linearBlockStandardPair_of_locImg_perfect [Finite G]
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hF : OddCoverSL3 (GaloisField p f)) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {A B : Subgroup G} (hA : A ≤ locLayer Ω x)
    (hB : B ≤ locLayer Ω x) (hAp : A ≤ ⁅A, A⁆) (hBp : B ≤ ⁅B, B⁆) {W : Subgroup (locQuot Ω x)}
    (h : LinearBlockStandardPair (GaloisField p f) W (locImg Ω x A) (locImg Ω x B)) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField p f) W' A B := by
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_lift (F := GaloisField p f) h4 hF
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) (perfect_subgroupOf hA hAp)
    (perfect_subgroupOf hB hBp) h
  have := linearBlockStandardPair_map hW' (locLayer Ω x).subtype (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA,
    inf_eq_left.mpr hB] at this
  exact ⟨_, this⟩

theorem oddCoverSL3_of_setup (S : CSetup p f m Ω K z) : OddCoverSL3 (GaloisField p f) :=
  CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3 (K := GaloisField p f) (p := p)
    (f := f) S.card_eq S.five

end Lift

@[expose] def IsShortNodeAt (Fr : Frame p f m Ω K z) (i j : Fin (m + 1)) (T : Subgroup G) : Prop :=
  T ≤ Mf Fr i j ∧ IsAdaptedShortIn (Mf Fr i j) (Fr.Tf i) (Fr.Tf j) (Fr.zf i) T

section ShortNodes

variable [Finite G] {Fr : Frame p f m Ω K z}

theorem exists_shortNodeAt (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j) : ∃ T, IsShortNodeAt Fr i j T := by
  obtain ⟨l, a, b, hab, rfl, rfl, ⟨LF⟩⟩ := exists_local_pair S Fr hij
  let X : Subgroup ↥(suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f))) :=
    (shortBlock (GaloisField p f) hab).range.subgroupOf (suppGroup (coords a ∪ coords b))
  have hle := LF.map_layerHom_le S hab X
  exact ⟨X.map (LF.layerHom S hab), hle,
    (LF.isAdaptedShortIn_iff S hab hle).mpr ⟨_, Or.inl rfl, rfl⟩⟩

omit [Finite G] in
theorem shortBlock_range_perfect (S : CSetup p f m Ω K z) {a b : Fin m} (hab : a ≠ b) :
    (shortBlock (GaloisField p f) hab).range ≤
      ⁅(shortBlock (GaloisField p f) hab).range, (shortBlock (GaloisField p f) hab).range⁆ := by
  have hperf : Group.IsPerfect SL(2, GaloisField p f) :=
    CFSG.ClassicalInvolution.sl2_isPerfect S.four_le
  have h1 : ⁅(⊤ : Subgroup SL(2, GaloisField p f)), (⊤ : Subgroup SL(2, GaloisField p f))⁆ =
      ⊤ := by
    rw [← commutator_def]
    exact hperf.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]

omit [Finite G] in
theorem shortGroup_perfect (S : CSetup p f m Ω K z) {a b : Fin m} (hab : a ≠ b)
    {s : Subgroup (StatedSp m (GaloisField p f))}
    (hs : s = (shortBlock (GaloisField p f) hab).range ∨
      s = shortGroupNeg (GaloisField p f) hab) : s ≤ ⁅s, s⁆ := by
  rcases hs with rfl | rfl
  · exact shortBlock_range_perfect S hab
  · rw [Models.SymplecticPairs.shortGroupNeg_eq_conj_left hab S.hex, ← Subgroup.map_commutator]
    exact Subgroup.map_mono (shortBlock_range_perfect S hab)

theorem shortGroup_le_supp {a b : Fin m} (hab : a ≠ b)
    {s : Subgroup (StatedSp m (GaloisField p f))}
    (hs : s = (shortBlock (GaloisField p f) hab).range ∨
      s = shortGroupNeg (GaloisField p f) hab) :
    s ≤ suppGroup (coords a ∪ coords b) := by
  rcases hs with rfl | rfl
  · exact Models.SymplecticPairs.shortBlock_range_le_suppGroup hab
  · exact Models.SymplecticPairs.shortGroupNeg_le_suppGroup hab

theorem locImg_layerHom_short (S : CSetup p f m Ω K z) {l : Fin (m + 1)} (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) {s : Subgroup (StatedSp m (GaloisField p f))}
    (hs : s = (shortBlock (GaloisField p f) hab).range ∨
      s = shortGroupNeg (GaloisField p f) hab) :
    locImg Ω (Fr.zf l) ((s.subgroupOf (suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerHom S hab)) = s.map LF.d.ψ := by
  rw [LF.locImg_map_layerHom S hab, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (shortGroup_le_supp hab hs)]

theorem layerHom_short_perfect (S : CSetup p f m Ω K z) {l : Fin (m + 1)} (LF : LocalFrame Fr l)
    {a b : Fin m} (hab : a ≠ b) {s : Subgroup (StatedSp m (GaloisField p f))}
    (hs : s = (shortBlock (GaloisField p f) hab).range ∨
      s = shortGroupNeg (GaloisField p f) hab) :
    (s.subgroupOf (suppGroup (coords a ∪ coords b) :
      Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerHom S hab) ≤
    ⁅(s.subgroupOf (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerHom S hab),
      (s.subgroupOf (suppGroup (coords a ∪ coords b) :
        Subgroup (StatedSp m (GaloisField p f)))).map (LF.layerHom S hab)⁆ := by
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (perfect_subgroupOf (shortGroup_le_supp hab hs)
    (shortGroup_perfect S hab hs))

theorem exists_linearBlockStandardPair_of_shortNodes (S : CSetup p f m Ω K z)
    (Fr : Frame p f m Ω K z) {i₁ i₂ i₃ : Fin (m + 1)} (h12 : i₁ ≠ i₂) (h23 : i₂ ≠ i₃)
    (h13 : i₁ ≠ i₃) {T₁ T₂ : Subgroup G} (hT₁ : IsShortNodeAt Fr i₁ i₂ T₁)
    (hT₂ : IsShortNodeAt Fr i₂ i₃ T₂) {l : Fin (m + 1)} (hl1 : l ≠ i₁) (hl2 : l ≠ i₂)
    (hl3 : l ≠ i₃) : ∃ W, LinearBlockStandardPair (GaloisField p f) W T₁ T₂ := by
  obtain ⟨LF⟩ := exists_localFrame S Fr l
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl1)
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl2)
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl3)
  have hab : a ≠ b := fun h => h12 (by rw [h])
  have hbc : b ≠ c := fun h => h23 (by rw [h])
  have hac : a ≠ c := fun h => h13 (by rw [h])
  obtain ⟨s₁, hs₁, rfl⟩ := (LF.isAdaptedShortIn_iff S hab hT₁.1).mp hT₁.2
  obtain ⟨s₂, hs₂, rfl⟩ := (LF.isAdaptedShortIn_iff S hbc hT₂.1).mp hT₂.2
  obtain ⟨W, hW⟩ := Models.SymplecticPairs.exists_linearBlockStandardPair_short_map hab hbc hac
    S.hex LF.d.ψ LF.d.ker_le hs₁ hs₂
  have hP1 := Fr.p1 S l
  refine linearBlockStandardPair_of_locImg_perfect S.four_le (oddCoverSL3_of_setup S) hP1
    (le_trans (LF.map_layerHom_le S hab _) (LocalFrame.Mf_le_locLayer S a b))
    (le_trans (LF.map_layerHom_le S hbc _) (LocalFrame.Mf_le_locLayer S b c))
    (layerHom_short_perfect S LF hab hs₁) (layerHom_short_perfect S LF hbc hs₂) (W := W) ?_
  rw [locImg_layerHom_short S LF hab hs₁, locImg_layerHom_short S LF hbc hs₂]
  exact hW

theorem exists_symplecticBlockStandardPair_of_shortNode (S : CSetup p f m Ω K z)
    (Fr : Frame p f m Ω K z) {i₀ j₀ : Fin (m + 1)} (hij : i₀ ≠ j₀) {T : Subgroup G}
    (hT : IsShortNodeAt Fr i₀ j₀ T) {l : Fin (m + 1)} (hl1 : l ≠ i₀) (hl2 : l ≠ j₀) :
    ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (Fr.Kf j₀) T := by
  obtain ⟨LF⟩ := exists_localFrame S Fr l
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl1)
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hl2)
  have hab : a ≠ b := fun h => hij (by rw [h])
  obtain ⟨s, hs, rfl⟩ := (LF.isAdaptedShortIn_iff S hab hT.1).mp hT.2
  obtain ⟨W, hW⟩ := Models.SymplecticPairs.exists_symplecticBlockStandardPair_short_comp
    (K := GaloisField p f) hab (LF.layerHom S hab) (LF.layerHom_injective S hab) hs
  have hKb : ((longBlock (GaloisField p f) m b).range.subgroupOf
      (suppGroup (coords a ∪ coords b) : Subgroup (StatedSp m (GaloisField p f)))).map
        (LF.layerHom S hab) = Fr.Kf (l.succAbove b) := by
    refine LF.injOn_locImg_Mf S hab (LF.map_layerHom_le S hab _)
      (Kf_le_Mf Fr (l.succAbove b) (Or.inr rfl)) ?_
    rw [LF.locImg_map_layerHom S hab, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (Models.SymplecticPairs.longBlock_range_le_suppGroup_right hab),
      LF.adapted b]
  rw [hKb] at hW
  exact ⟨W, hW⟩

end ShortNodes

section Chain

variable [Finite G]

noncomputable def shortNode (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (i : Fin m) :
    Subgroup G :=
  (exists_shortNodeAt S Fr (Fin.castSucc_lt_succ (i := i)).ne).choose

theorem isShortNode_shortNode (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (i : Fin m) :
    IsShortNodeAt Fr i.castSucc i.succ (shortNode S Fr i) :=
  (exists_shortNodeAt S Fr (Fin.castSucc_lt_succ (i := i)).ne).choose_spec

noncomputable def chain (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) :
    Fin (m + 1) → Subgroup G :=
  Fin.lastCases (Fr.Kf (Fin.last m)) (fun i => shortNode S Fr i)

theorem chain_last (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) :
    chain S Fr (Fin.last m) = Fr.Kf (Fin.last m) := by
  simp [chain]

theorem chain_castSucc (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (i : Fin m) :
    chain S Fr i.castSucc = shortNode S Fr i := by
  simp [chain]

theorem fin_ne_of_val_ne {n : ℕ} {x y : Fin n} (h : x.val ≠ y.val) : x ≠ y :=
  fun e => h (congrArg Fin.val e)

theorem chain_comm (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (hL : LayersCommute Fr) :
    ∀ i j : Fin (m + 1), i.val + 1 < j.val → ∀ a ∈ chain S Fr i, ∀ b ∈ chain S Fr j,
      a * b = b * a := by
  intro i j hij a ha b hb
  have hjlt := j.isLt
  obtain ⟨i', rfl⟩ : ∃ i' : Fin m, i = i'.castSucc := ⟨⟨i.val, by omega⟩, rfl⟩
  rw [chain_castSucc] at ha
  have hMa : a ∈ Mf Fr i'.castSucc i'.succ := (isShortNode_shortNode S Fr i').1 ha
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [chain_castSucc] at hb
    have hMb : b ∈ Mf Fr j'.castSucc j'.succ := (isShortNode_shortNode S Fr j').1 hb
    simp only [Fin.val_castSucc] at hij
    refine hL (i := i'.castSucc) (j := i'.succ) (k := j'.castSucc)
      (l := j'.succ) ?_ ?_ ?_ ?_ ?_ ?_ a hMa b hMb <;>
    · apply fin_ne_of_val_ne
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  · rw [chain_last] at hb
    simp only [Fin.val_last, Fin.val_castSucc] at hij
    refine commutes_Mf_Kf Fr (i := i'.castSucc) (j := i'.succ) (k := Fin.last m) ?_ ?_ a hMa b
      hb <;>
    · apply fin_ne_of_val_ne
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
      omega

theorem exists_index_outside (hm : 3 ≤ m) (i : ℕ) :
    ∃ l : Fin (m + 1), l.val ≠ i ∧ l.val ≠ i + 1 ∧ l.val ≠ i + 2 := by
  by_cases h0 : i = 0
  · exact ⟨Fin.last m, by simp; omega, by simp; omega, by simp; omega⟩
  · exact ⟨0, by simp; omega, by simp, by simp⟩

theorem chain_pair (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) :
    ∀ i j : Fin (m + 1), i.val + 1 = j.val → j.val + 1 < m + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (chain S Fr i) (chain S Fr j) := by
  intro i j hij hj
  obtain ⟨i', rfl⟩ : ∃ i' : Fin m, i = i'.castSucc := ⟨⟨i.val, by omega⟩, rfl⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = j'.castSucc := ⟨⟨j.val, by omega⟩, rfl⟩
  rw [chain_castSucc, chain_castSucc]
  simp only [Fin.val_castSucc] at hij
  have e : j'.castSucc = i'.succ := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  have hT₁ := isShortNode_shortNode S Fr i'
  have hT₂ := isShortNode_shortNode S Fr j'
  rw [e] at hT₂
  obtain ⟨l, hl1, hl2, hl3⟩ := exists_index_outside S.three i'.val
  refine exists_linearBlockStandardPair_of_shortNodes S Fr (i₁ := i'.castSucc) (i₂ := i'.succ)
    (i₃ := j'.succ) ?_ ?_ ?_ hT₁ hT₂ (l := l) ?_ ?_ ?_ <;>
  · apply fin_ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

theorem chain_sp (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) :
    ∀ i j : Fin (m + 1), i.val + 1 = m + 1 → j.val + 2 = m + 1 →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (chain S Fr i) (chain S Fr j) := by
  intro i j hi hj
  have hi' : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
  obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = j'.castSucc := ⟨⟨j.val, by omega⟩, rfl⟩
  subst hi'
  rw [chain_last, chain_castSucc]
  simp only [Fin.val_castSucc] at hj
  have e : j'.succ = Fin.last m := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
  have hT := isShortNode_shortNode S Fr j'
  rw [e] at hT
  have hm3 := S.three
  refine exists_symplecticBlockStandardPair_of_shortNode S Fr (i₀ := j'.castSucc)
    (j₀ := Fin.last m) ?_ hT (l := 0) ?_ ?_ <;>
  · apply fin_ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero]
    omega

end Chain

end CFSG.ClassicalInvolution.RouteD
