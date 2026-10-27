module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviChart
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviNormal

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock planeTorus longInv suppGroup coords
  shortBlock planeTorusElt leviCent mat_planeTorusElt planeTorusDiag mat_shortBlock transvOne)
open CFSG.ClassicalInvolution.RouteD.LeviModel
open CFSG.ClassicalInvolution.WeakCT (torusHom coe_torusHom)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

private theorem blockMat_diag_apply {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (b : Fˣ) (r t : Fin n) :
    blockMat i j !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)] r t =
      if r = t then (if r = i then (b : F) else if r = j then ((b⁻¹ : Fˣ) : F) else 1) else 0 := by
  have hji : j ≠ i := hij.symm
  rcases eq_or_ne r i with rfl | hri
  · rcases eq_or_ne t r with rfl | hti
    · simp [blockMat]
    · rcases eq_or_ne t j with rfl | htj
      · simp [blockMat, hij, hti]
      · simp [blockMat, hti, hti.symm]
  · rcases eq_or_ne r j with rfl | hrj
    · rcases eq_or_ne t r with rfl | htj
      · simp [blockMat, hji]
      · rcases eq_or_ne t i with rfl | hti
        · simp [blockMat, hji]
        · simp [blockMat, hri, htj, hti, htj.symm]
    · rcases eq_or_ne t r with rfl | htr
      · simp [blockMat, hri, hrj]
      · simp [blockMat, hri, hrj, Matrix.one_apply, htr.symm]

theorem shortBlock_torusHom {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : Fˣ) :
    shortBlock F hij (torusHom F a) = planeTorusElt F i j a a⁻¹ := by
  apply mat_injective
  rw [mat_shortBlock, mat_planeTorusElt hij, ← map_inv, coe_torusHom, coe_torusHom]
  ext r t
  rcases r with r | r <;> rcases t with t | t
  · rw [Matrix.fromBlocks_apply₁₁, blockMat_diag_apply hij]
    simp [Matrix.diagonal_apply, planeTorusDiag]
  · simp [Matrix.fromBlocks_apply₁₂]
  · simp [Matrix.fromBlocks_apply₂₁]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, blockMat_diag_apply hij]
    by_cases hrt : r = t
    · subst hrt
      simp [planeTorusDiag, eq_comm]
    · simp [hrt, Ne.symm hrt]

section Charts

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {Fr : Frame p f 2 Ω K z} {l : Fin 3}

private theorem supp_inf_eq {F : Type} [Field F] (X : Subgroup (StatedSp 2 F)) :
    X ⊓ (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) : Subgroup (StatedSp 2 F)) = X :=
  inf_eq_left.mpr (by
    rw [Models.SymplecticPairs.suppGroup_coords_zero_union_one]
    exact le_top)

theorem LocalFrameI.map_layerSp_eq (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    (X : Subgroup (StatedSp 2 (GaloisField p f))) :
    X.map (LF.layerSp S) =
      ((X.subgroupOf (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) :
        Subgroup (StatedSp 2 (GaloisField p f)))).map
        (LF.layerEquiv S fin_two_zero_ne_one).toMonoidHom).map
        (Mf Fr (l.succAbove 0) (l.succAbove 1)).subtype := by
  rw [← map_toSupp2, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem LocalFrameI.map_layerSp_planeTorus (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    (c : Fin 2) :
    (planeTorus (GaloisField p f) 2 c).map (LF.layerSp S) = Fr.Tf (l.succAbove c) := by
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  have hTf : Fr.Tf (l.succAbove c) ≤ Mf Fr (l.succAbove 0) (l.succAbove 1) :=
    Tf_le_Mf Fr _ (by rcases hc with rfl | rfl <;> simp)
  rw [LF.map_layerSp_eq S, LF.map_layerEquiv_planeTorus S fin_two_zero_ne_one c hc,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTf]

theorem LocalFrameI.locImg_map_layerSp (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    (X : Subgroup (StatedSp 2 (GaloisField p f))) :
    locImg Ω (Fr.zf l) (X.map (LF.layerSp S)) = X.map LF.d.ψ := by
  have h := LF.locImg_map_layerHom S fin_two_zero_ne_one
    (X.subgroupOf (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) :
      Subgroup (StatedSp 2 (GaloisField p f))))
  rw [Subgroup.subgroupOf_map_subtype, supp_inf_eq] at h
  rw [← h, ← map_toSupp2, Subgroup.map_map]
  rfl

theorem LocalFrameI.map_layerSp_longBlock (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    (c : Fin 2) :
    (longBlock (GaloisField p f) 2 c).range.map (LF.layerSp S) = Fr.Kf (l.succAbove c) := by
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  refine LF.injOn_locImg_Mf S fin_two_zero_ne_one ?_ (Kf_le_Mf Fr _ (by
    rcases hc with rfl | rfl <;> simp)) ?_
  · rw [← LF.layerSp_range S]
    exact Subgroup.map_le_range _ _
  · rw [LF.locImg_map_layerSp S, ← LF.adapted c]

private theorem range_inf_centralizer_eq_map {H : Type*} [Group H] {G' : Type*} [Group G']
    {ψ : H →* G'} (hψ : Function.Injective ψ) (u : H) :
    ψ.range ⊓ Subgroup.centralizer ({ψ u} : Set G') =
      (Subgroup.centralizer ({u} : Set H)).map ψ := by
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    apply hψ
    rw [map_mul, map_mul]
    exact hy'
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [← map_mul, ← map_mul, hy']

theorem LocalFrameI.leviNode_layerSp (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    {a : (GaloisField p f)ˣ}
    (ha : (a : GaloisField p f) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : GaloisField p f)) :
    leviNode (Mf Fr (l.succAbove 0) (l.succAbove 1))
      (LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
        LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a))) =
      (shortBlock (GaloisField p f) fin_two_zero_ne_one).range.map (LF.layerSp S) := by
  have hu : LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
      LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) =
      LF.layerSp S (planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a) :=
    (map_mul _ _ _).symm
  rw [hu, ← LF.layerSp_range S, leviNode,
    range_inf_centralizer_eq_map (LF.layerSp_injective S), ← Subgroup.map_commutator]
  congr 1
  have : Subgroup.centralizer ({planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a} :
      Set (StatedSp 2 (GaloisField p f))) = leviCent (GaloisField p f) (0 : Fin 2) 1 a := by
    rw [leviCent, Models.SymplecticPairs.suppGroup_coords_zero_union_one, top_inf_eq]
  rw [this]
  exact Models.SymplecticPairs.commutator_leviCent fin_two_zero_ne_one ha

theorem LocalFrameI.not_le_centralizer_levi (S : CSetupW p f 2 Ω K z) (LF : LocalFrameI Fr l)
    {a : (GaloisField p f)ˣ}
    (ha : (a : GaloisField p f) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : GaloisField p f)) :
    ¬ Mf Fr (l.succAbove 0) (l.succAbove 1) ≤ Subgroup.centralizer
      ({LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
        LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a))} :
        Set G) := by
  intro h
  have hu : LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
      LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) =
      LF.layerSp S (planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a) :=
    (map_mul _ _ _).symm
  rw [hu] at h
  have hmem : LF.layerSp S (longBlock (GaloisField p f) 2 0 (transvOne (GaloisField p f))) ∈
      Mf Fr (l.succAbove 0) (l.succAbove 1) := by
    rw [← LF.layerSp_range S]
    exact ⟨_, rfl⟩
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (h hmem)
  refine Models.SymplecticPairs.not_commute_longBlock_planeTorusElt fin_two_zero_ne_one ha a ?_
  show _ * _ = _ * _
  apply LF.layerSp_injective S
  rw [map_mul, map_mul]
  exact hc

theorem LocalFrameI.not_inf_le_centralizer_levi (S : CSetupW p f 2 Ω K z)
    (LF : LocalFrameI Fr l) (a : (GaloisField p f)ˣ) :
    ¬ (Mf Fr (l.succAbove 0) (l.succAbove 1) ⊓ Subgroup.centralizer
      ({LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
        LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a))} :
        Set G) ≤ Subgroup.centralizer ({Fr.zf (l.succAbove 0)} : Set G)) := by
  intro h
  have hu : LF.layerSp S (longBlock (GaloisField p f) 2 0 (torusHom (GaloisField p f) a)) *
      LF.layerSp S (longBlock (GaloisField p f) 2 1 (torusHom (GaloisField p f) a)) =
      LF.layerSp S (planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a) :=
    (map_mul _ _ _).symm
  rw [hu] at h
  have hmem : LF.layerSp S (shortBlock (GaloisField p f) fin_two_zero_ne_one
      (transvOne (GaloisField p f))) ∈ Mf Fr (l.succAbove 0) (l.succAbove 1) ⊓
        Subgroup.centralizer ({LF.layerSp S (planeTorusElt (GaloisField p f) (0 : Fin 2) 1 a a)} :
          Set G) := by
    refine ⟨by rw [← LF.layerSp_range S]; exact ⟨_, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Models.SymplecticPairs.commute_shortBlock_planeTorusElt
      fin_two_zero_ne_one a _).eq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (h hmem)
  rw [← LF.layerSp_longInv S 0] at hc
  refine Models.SymplecticPairs.not_commute_shortBlock_longInv fin_two_zero_ne_one S.two_ne_zero ?_
  show _ * _ = _ * _
  apply LF.layerSp_injective S
  rw [map_mul, map_mul]
  exact hc

end Charts

end CFSG.ClassicalInvolution.RouteD
