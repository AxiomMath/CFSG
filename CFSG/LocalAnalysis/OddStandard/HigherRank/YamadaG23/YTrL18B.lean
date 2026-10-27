module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJNorm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJSec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem lf18_3a_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_3a s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  change normIn L s.fr.B = normIn L (cen s.fr.B)
  obtain ⟨-, -, hR, -, -⟩ := s.facts.2.2.2.2.2.2.2.1
  obtain ⟨hA, -, -, -, -⟩ := hR
  have hBL : s.fr.B ≤ L := (s3_B_le_S s).trans (s3_S_le_L s)
  have hcenBL : cen s.fr.B ≤ L := (s3_cenB_le_B s).trans hBL
  have hB2 : IsPGroup 2 ↥s.fr.B := s3_isPGroup_of_le s (s3_B_le_S s)
  have hcenB2 : IsPGroup 2 ↥(cen s.fr.B) :=
    s3_isPGroup_of_le s ((s3_cenB_le_B s).trans (s3_B_le_S s))
  have e1 : jSub L (normIn L s.fr.B) =
      normIn (innerAut (L ⧸ center L)) s.fr'.B := by
    rw [jSub_normIn (L := L) hZ hBL hB2, jSub_self L, s3_jSub_B hS hZ s]
  have e2 : jSub L (normIn L (cen s.fr.B)) =
      normIn (innerAut (L ⧸ center L)) (cen s.fr'.B) := by
    rw [jSub_normIn (L := L) hZ hcenBL hcenB2, jSub_self L, s3_jSub_cenB hS hZ s]
  refine jSub_inj (L := L) (V := normIn L s.fr.B) (W := normIn L (cen s.fr.B))
    inf_le_left inf_le_left (zL_le_normIn hBL) (zL_le_normIn hcenBL) ?_
  rw [e1, e2, hA]

theorem lf18_3b_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_3b s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  change normIn L s.fr.B ≤ normIn L s.fr.F
  obtain ⟨-, -, hR, -, -⟩ := s.facts.2.2.2.2.2.2.2.1
  obtain ⟨-, hBleF, -, -, -⟩ := hR
  have hBL : s.fr.B ≤ L := (s3_B_le_S s).trans (s3_S_le_L s)
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans ((s3_A_le_S s).trans (s3_S_le_L s))
  have hB2 : IsPGroup 2 ↥s.fr.B := s3_isPGroup_of_le s (s3_B_le_S s)
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s ((s3_F_le_A s).trans (s3_A_le_S s))
  have e1 : jSub L (normIn L s.fr.B) =
      normIn (innerAut (L ⧸ center L)) s.fr'.B := by
    rw [jSub_normIn (L := L) hZ hBL hB2, jSub_self L, s3_jSub_B hS hZ s]
  have eF : jSub L (normIn L s.fr.F) =
      normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [jSub_normIn (L := L) hZ hFL hF2, jSub_self L, s3_jSub_F hS hZ s]
  refine (jSub_le_iff (L := L) (V := normIn L s.fr.B) (W := normIn L s.fr.F)
    inf_le_left inf_le_left (zL_le_normIn hFL)).mp ?_
  rw [e1, eF]
  exact hBleF

theorem lf18_3c_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_3c s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  change SecProp (normIn L s.fr.B) (zL L ⊔ s.fr.B)
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))
  obtain ⟨-, -, hR, -, -⟩ := s.facts.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hSec, -, -⟩ := hR
  have hBL : s.fr.B ≤ L := (s3_B_le_S s).trans (s3_S_le_L s)
  have hB2 : IsPGroup 2 ↥s.fr.B := s3_isPGroup_of_le s (s3_B_le_S s)
  have e1 : jSub L (normIn L s.fr.B) =
      normIn (innerAut (L ⧸ center L)) s.fr'.B := by
    rw [jSub_normIn (L := L) hZ hBL hB2, jSub_self L, s3_jSub_B hS hZ s]
  refine (secProp_jSub (L := L) (V := normIn L s.fr.B) (N := zL L ⊔ s.fr.B)
    (hV := (inf_le_left : normIn L s.fr.B ≤ L).trans Subgroup.le_normalizer)
    (hNV := ?_) (hK := ?_) (Q := fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ?_).mpr ?_
  · exact sup_le (zL_le_normIn hBL) (le_inf hBL Subgroup.le_normalizer)
  · intro x hx hxC
    exact Subgroup.mem_sup_left
      ((mem_zL_iff (L := L)).mpr ⟨(inf_le_left : normIn L s.fr.B ≤ L) hx, hxC⟩)
  · intro Y Y' _ _ e
    exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩
  · rw [e1, jSub_sup_zL (L := L) hBL, s3_jSub_B hS hZ s]
    exact hSec

theorem lf18_3d_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_3d s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  change ∃ k ∈ normIn L s.fr.B, IsPGroup 3 (zpowers k) ∧ k ∉ zL L
  obtain ⟨hP, -, hR, -, -⟩ := s.facts.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hSec, -, -⟩ := hR
  have hBL : s.fr.B ≤ L := (s3_B_le_S s).trans (s3_S_le_L s)
  have hB2 : IsPGroup 2 ↥s.fr.B := s3_isPGroup_of_le s (s3_B_le_S s)
  have e1 : jSub L (normIn L s.fr.B) =
      normIn (innerAut (L ⧸ center L)) s.fr'.B := by
    rw [jSub_normIn (L := L) hZ hBL hB2, jSub_self L, s3_jSub_B hS hZ s]
  have hBS : s.fr'.B ≤ s.fr'.S := inf_le_left
  have hSinner : s.fr'.S ≤ innerAut (L ⧸ center L) := by
    rw [← hP.2]
    exact inf_le_left
  have hKN : s.fr'.B ≤ normIn (innerAut (L ⧸ center L)) s.fr'.B :=
    le_inf (hBS.trans hSinner) Subgroup.le_normalizer
  obtain ⟨κ, hκN, hκ3, hκ1⟩ := exists_threeElem_of_secProp_perm3 hSec hKN
  have hκj : κ ∈ jSub L (normIn L s.fr.B) := by
    rw [e1]
    exact hκN
  exact exists_pElem_of_jSub (L := L) (p := 3) (N := normIn L s.fr.B)
    Nat.prime_three inf_le_left hκj hκ3 hκ1

theorem lf18_3f_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_3f s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  change centIn L (cen s.fr.B) = zL L ⊔ s.fr.B
  obtain ⟨-, -, hR, -, -⟩ := s.facts.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, hcent⟩ := hR
  have hBL : s.fr.B ≤ L := (s3_B_le_S s).trans (s3_S_le_L s)
  have hcenBL : cen s.fr.B ≤ L := (s3_cenB_le_B s).trans hBL
  have hcenB2 : IsPGroup 2 ↥(cen s.fr.B) :=
    s3_isPGroup_of_le s ((s3_cenB_le_B s).trans (s3_B_le_S s))
  have e3 : jSub L (centIn L (cen s.fr.B)) =
      centIn (innerAut (L ⧸ center L)) (cen s.fr'.B) := by
    rw [jSub_centIn (L := L) hZ hcenBL hcenB2, jSub_self L, s3_jSub_cenB hS hZ s]
  refine jSub_inj (L := L) (V := centIn L (cen s.fr.B)) (W := zL L ⊔ s.fr.B)
    inf_le_left (sup_le zL_le hBL) (zL_le_centIn hcenBL) le_sup_left ?_
  rw [e3, hcent, jSub_sup_zL (L := L) hBL, s3_jSub_B hS hZ s]

end CFSG.OddStandard.HigherRank.YamadaG23
