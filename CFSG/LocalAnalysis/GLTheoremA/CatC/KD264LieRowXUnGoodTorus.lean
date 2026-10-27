module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGoodFix
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGoodBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGoodMatrix
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.RankThree.PartTwo.Sec21.Tables

abbrev dgl {N : ℕ} (d : GL (Fin N) xunK) (j : Fin N) : xunK :=
  ((d : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) j j

theorem isGood_of_torus {N : ℕ} (hN1 : 1 ≤ N) (hN4 : 4 ≤ N) (i0 : Fin N) (hi0 : (i0 : ℕ) = 0)
    (T : Subgroup (uU xunH N))
    (hdiag : ∀ d ∈ T, IsDiagU N (d : GL (Fin N) xunK))
    (hfour : ∀ d ∈ T, ∀ j : Fin N, (j : ℕ) < 4 → dgl d j = dgl d i0)
    (hsep : ∃ d ∈ T, ∃ j : Fin N, dgl d j ≠ dgl d i0) :
    IsGood 3 (T.map (xunConj N hN1)) := by
  classical
  set C : Finset (Fin N) := Finset.univ.filter (fun j => ∀ d ∈ T, dgl d j = dgl d i0) with hCdef
  have memC : ∀ j, j ∈ C ↔ ∀ d ∈ T, dgl d j = dgl d i0 := by
    intro j
    simp [hCdef]
  have hfourC : ∀ j : Fin N, (j : ℕ) < 4 → j ∈ C := fun j hj =>
    (memC j).2 (fun d hd => hfour d hd j hj)
  have hCcard : 4 ≤ C.card := by
    have hsub : (Finset.univ : Finset (Fin 4)).map (Fin.castLEEmb hN4) ⊆ C := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
      exact hfourC _ (by simp [Fin.castLEEmb])
    have := Finset.card_le_card hsub
    simpa using this
  have hC1 : 1 ≤ C.card := by omega
  obtain ⟨d0, hd0, j0, hj0⟩ := hsep
  have hjout : j0 ∉ C := fun h => hj0 (((memC j0).1 h) d0 hd0)
  have hsepC : ∀ a b : Fin N, ((a ∈ C ∧ b ∉ C) ∨ (a ∉ C ∧ b ∈ C)) →
      ∃ d ∈ T, dgl d a ≠ dgl d b := by
    intro a b hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [memC] at hb
      push_neg at hb
      obtain ⟨d, hd, hne⟩ := hb
      refine ⟨d, hd, ?_⟩
      rw [(memC a).1 ha d hd]
      exact fun h => hne h.symm
    · rw [memC] at ha
      push_neg at ha
      obtain ⟨d, hd, hne⟩ := ha
      refine ⟨d, hd, ?_⟩
      rw [(memC b).1 hb d hd]
      exact hne
  set KW := blkRange hN1 C hC1 with hKW
  have hq : CFSG.Open.IsQuasisimple ↥KW := isQuasisimple_blkRange hN1 C hCcard j0 hjout
  obtain ⟨ω, hω0, hω1⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.exists_ne_zero_ne_one xunH
  have hdvd : 3 ∣ Nat.card (↥KW ⧸ Subgroup.center ↥KW) :=
    three_dvd_card_quotient_blkRange hN1 C hCcard j0 hjout ω hω0 hω1
  set S : Set (GL (Fin N) xunK) := (fun d : uU xunH N => (d : GL (Fin N) xunK)) '' (T : Set _)
    with hSdef
  set L : Subgroup (GL (Fin N) xunK) := Subgroup.centralizer S with hLdef
  have memL : ∀ g : GL (Fin N) xunK, g ∈ L ↔ ∀ d ∈ T, (d : GL (Fin N) xunK) * g = g * d := by
    intro g
    rw [hLdef, Subgroup.mem_centralizer_iff]
    constructor
    · intro h d hd
      exact h _ ⟨d, hd, rfl⟩
    · rintro h _ ⟨d, hd, rfl⟩
      exact h d hd
  have hmcomm : ∀ g ∈ L, ∀ d ∈ T,
      ((d : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) * (g : Matrix (Fin N) (Fin N) xunK) =
        (g : Matrix (Fin N) (Fin N) xunK) * ((d : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) := by
    intro g hg d hd
    have := congrArg Units.val (((memL g).1 hg) d hd)
    simpa using this
  set Lsub : Subgroup (StatedSU N (2 ^ 1) xunK) := L.subgroupOf (StatedSU N (2 ^ 1) xunK)
    with hLsub
  set Lbar : Subgroup (xunM N) := Lsub.map (projH _) with hLbar
  set X : Subgroup (xunM N) := ⨅ f ∈ T.map (xunConj N hN1), fixSubgroup f with hXdef
  have hX_mem : ∀ x : xunM N, x ∈ X ↔ ∀ d ∈ T, xunConj N hN1 d x = x := by
    intro x
    simp only [hXdef, Subgroup.mem_iInf, Subgroup.mem_map]
    constructor
    · intro h d hd
      exact h _ ⟨d, hd, rfl⟩
    · rintro h f ⟨d, hd, rfl⟩
      exact h d hd
  have hblock : ∀ g ∈ L, IsBlock (C : Set (Fin N)) (g : Matrix (Fin N) (Fin N) xunK) := by
    intro g hg
    apply isBlock_of_commute
    intro a b hab
    obtain ⟨d, hd, hdne⟩ := hsepC a b hab
    exact ⟨((d : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK), hdiag d hd, hmcomm g hg d hd, hdne⟩
  have hblk_mem : ∀ h : StatedSU C.card (2 ^ 1) xunK,
      ((blk hN1 C hC1 h : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) ∈ L := by
    intro h
    rw [memL]
    intro d hd
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    refine commute_of_const (C := (C : Set (Fin N))) (hdiag d hd) ?_ ?_
    · intro a b ha hb
      exact ((memC a).1 ha d hd).trans ((memC b).1 hb d hd).symm
    · exact (mem_range_blk hN1 C hC1 _).1 ⟨h, rfl⟩
  have hKW_le : KW ≤ Lbar := by
    intro x hx
    rw [hKW, blkRange, MonoidHom.mem_range] at hx
    obtain ⟨h, rfl⟩ := hx
    refine ⟨blk hN1 C hC1 h, ?_, rfl⟩
    rw [SetLike.mem_coe, hLsub, Subgroup.mem_subgroupOf]
    exact hblk_mem h
  have hLbar_le_X : Lbar ≤ X := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hLsub, Subgroup.mem_subgroupOf] at hg
    rw [hX_mem]
    intro d hd
    have hcomm := (memL _).1 hg d hd
    change uConjAut xunH hN1 d (projH _ g) = projH _ g
    rw [uConjAut_proj xunH hN1 d g]
    congr 1
    apply Subtype.ext
    show (d : GL (Fin N) xunK) * (g : GL (Fin N) xunK) * (d : GL (Fin N) xunK)⁻¹ =
      (g : GL (Fin N) xunK)
    rw [hcomm, mul_inv_cancel_right]
  have hKW_normal : (KW.subgroupOf Lbar).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.1 g.2
    rw [hKW, blkRange, MonoidHom.mem_range] at hn
    obtain ⟨h, hh⟩ := hn
    have hyL : ((y : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) ∈ L :=
      Subgroup.mem_subgroupOf.1 hy
    have hyinvL : ((y⁻¹ : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) ∈ L := by
      rw [Subgroup.coe_inv]
      exact L.inv_mem hyL
    have hyB := hblock _ hyL
    have hyinvB := hblock _ hyinvL
    have hMN : ((y : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) *
        (((y⁻¹ : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) = 1 := by
      rw [← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
    have hHB : IsIdOutside (C : Set (Fin N))
        ((blk hN1 C hC1 h : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) :=
      (mem_range_blk hN1 C hC1 _).1 ⟨h, rfl⟩
    have hconj := isIdOutside_conj hyB hyinvB hMN hHB
    obtain ⟨z, hz⟩ : ∃ z : StatedSU N (2 ^ 1) xunK, z = y * blk hN1 C hC1 h * y⁻¹ := ⟨_, rfl⟩
    have hzM : ((z : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) =
        ((y : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) *
          ((blk hN1 C hC1 h : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) *
          (((y⁻¹ : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) := by
      rw [hz, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    have hzrange : z ∈ (blk hN1 C hC1).range :=
      (mem_range_blk hN1 C hC1 z).2 (by rw [hzM]; exact hconj)
    obtain ⟨h', hh'⟩ := hzrange
    refine ⟨h', ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgy, ← hh]
    change projH _ (blk hN1 C hC1 h') = _
    rw [hh', hz]
    simp only [map_mul, map_inv]
    rfl
  have hLbar_normal : (Lbar.subgroupOf X).Normal := by
    constructor
    intro n hn k
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (k : xunM N)
    have hku : (k : xunM N) = projH _ u := hu.symm
    have hfix : ∀ d ∈ T, xunConj N hN1 d (projH _ u) = projH _ u := by
      intro d hd
      rw [← hku]
      exact (hX_mem _).1 k.2 d hd
    have hsfun := fun d hd => exists_conj_eq_mul_central hN1 d u (hfix d hd)
    obtain ⟨g, hg, hgn⟩ := Subgroup.mem_map.1 hn
    have hgL : ((g : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) ∈ L :=
      Subgroup.mem_subgroupOf.1 hg
    obtain ⟨z, hz⟩ : ∃ z : StatedSU N (2 ^ 1) xunK, z = u * g * u⁻¹ := ⟨_, rfl⟩
    have hzGL : ((z : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) =
        (u : GL (Fin N) xunK) * (g : GL (Fin N) xunK) * (u : GL (Fin N) xunK)⁻¹ := by
      rw [hz, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hzL : ((z : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK) ∈ L := by
      rw [memL]
      intro d hd
      obtain ⟨s, hs_mem, hs_eq⟩ := hsfun d hd
      have hcomm_g : (d : GL (Fin N) xunK) * (g : GL (Fin N) xunK) =
          (g : GL (Fin N) xunK) * (d : GL (Fin N) xunK) := (memL _).1 hgL d hd
      have hcomm_s : Commute s (g : GL (Fin N) xunK) :=
        (Subgroup.mem_center_iff.1 hs_mem _).symm
      rw [hzGL]
      exact commute_conj_of_conj_eq hs_eq hcomm_s hcomm_g
    refine Subgroup.mem_map.2 ⟨z, Subgroup.mem_subgroupOf.2 hzL, ?_⟩
    have hprod : projH _ z = projH _ u * projH _ g * (projH _ u)⁻¹ := by
      rw [hz, map_mul, map_mul, map_inv]
    rw [hprod, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgn, hku]
  have hsub : IsSubnormal KW X :=
    IsSubnormal.step hKW_le hKW_normal
      (IsSubnormal.step hLbar_le_X hLbar_normal (IsSubnormal.refl X))
  have hcomp : GLAPComponent 3 X KW :=
    CFSG.LocalAnalysis.GLTheoremA.S12.glaPComponent_of_quasisimple' (by norm_num) hsub hq hdvd
  show GLAPLayer 3 X ≠ ⊥
  intro hbot
  have hle : KW ≤ GLAPLayer 3 X := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  have hnt : Nontrivial (↥KW ⧸ Subgroup.center ↥KW) := hq.2.toNontrivial
  have hnt2 : Nontrivial ↥KW :=
    Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center ↥KW))
  exact ((Subgroup.nontrivial_iff_ne_bot KW).1 hnt2) hle

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

end
