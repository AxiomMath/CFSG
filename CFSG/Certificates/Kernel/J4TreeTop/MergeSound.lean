module

public import CFSG.Certificates.Kernel.J4TreeTop.TreeSound
public import Certificates.Data.Kernel.J4TreeTopMerge

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT


theorem mask_conj {xs TJ : List J} {Xs TB msk : List ℕ} (h2 : List.Forall₂ PK xs Xs)
    (hTB : List.Forall₂ PK TJ TB) {w : J} {Wc WI : ℕ} (hw : PK w Wc) (hwi : PK w⁻¹ WI)
    (hlen : Xs.length = msk.length)
    (hm : (Xs.zip msk).all (fun p => Nat.beq (M (M WI p.1) Wc) (prodMask TB p.2)) = true) :
    ∀ x ∈ xs, w⁻¹ * x * w ∈ Subgroup.closure {t | t ∈ TJ} := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hjl : j < Xs.length := by rw [← forall₂_length h2]; exact hj
  have hmj := zip_all_getD (a := 0) (b := 0) hm hlen j hjl
  have hxX := forall₂_getD (a := 1) (b := 0) h2 j hj
  rw [← List.getD_eq_getElem _ 1 hj,
    pk_beq (pk_mul (pk_mul hwi hxX) hw) (pk_prodMask hTB _) hmj]
  exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) _

theorem topMerge_sound {T : Tabs} (hT : tabsOK T = true) {g : TGlob} {c : TMerge}
    {es : List (ℕ × ℕ × ℕ)} (h : topMergeOK T g c es = true) {Gs : List J}
    (hG : List.Forall₂ PK Gs g.G) (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs g.GI)
    (hGC : ∀ s ∈ Gs, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) :
    g.k = (topNodes.getD c.i default).node ∧ c.j < (topNodes.getD c.i default).children.length ∧
      c.y = ((topNodes.getD c.i default).children.getD c.j default).y ∧
      c.tgt = ((topNodes.getD c.i default).children.getD c.j default).target ∧
      1 ≤ c.tgt ∧ c.tgt ≤ treeN ∧
      burnsideJ4NP_treeElt c.y ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) ∧
      burnsideJ4NP_treeElt c.y * burnsideJ4NP_treeElt c.y = 1 ∧
      (Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) = treeOrd g.k →
        burnsideJ4NP_MergeFact g.k c.tgt (burnsideJ4NP_treeElt c.y)) := by
  unfold topMergeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩ := h
  set C := Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) with hC
  set y := burnsideJ4NP_treeElt c.y with hy
  set bJ := (treeBasis g.k).map burnsideJ4NP_treeElt with hbJ
  have hY : PK y (ccT T c.y) := pk_cc hT h7
  have hB2 : List.Forall₂ PK bJ ((treeBasis g.k).map (ccT T)) :=
    forall₂_cc hT _ (List.all_eq_true.mp h8)
  have hAdef : burnsideJ4NP_Rep g.k = Subgroup.closure {x | x ∈ bJ} := rfl
  have hyC : y ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨hY.1, ?_⟩
    rw [hAdef]
    exact mem_cent_closure fun b hb =>
      comm_of_all (.cons hY .nil) hB2 (by rw [List.all_cons, List.all_nil, Bool.and_true]; exact h11) y List.mem_cons_self b hb
  refine ⟨h1, h2, h3, h4, h5, h6, hyC, (pk_sq hY).mpr h10, fun hN => ?_⟩
  set hW := wordProd xJ (wordC 64 c.h)
  have hHpk : PK hW (wordT T 64 c.h) := pk_word hT 64 c.h
  have hHi : PK hW⁻¹ c.hI := pk_inv hHpk h12
  have hTB := forall₂_cc hT _ (List.all_eq_true.mp h9)
  have hBY : List.Forall₂ PK (bJ ++ [y]) ((treeBasis g.k).map (ccT T) ++ [ccT T c.y]) :=
    List.rel_append hB2 (.cons hY .nil)
  have hconj : ∀ x ∈ bJ ++ [y], hW⁻¹ * x * hW ∈ burnsideJ4NP_Rep c.tgt :=
    mask_conj hBY hTB hHpk hHi (by rw [h13]; simp) h14
  refine ⟨hW, word_mem 64 c.h, ?_, ?_⟩
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · rw [hAdef, Subgroup.closure_le]
      intro b hb
      exact burnsideJ4KW_mem_map_conj.mpr (hconj b (List.mem_append_left _ hb))
    · exact burnsideJ4KW_mem_map_conj.mpr (hconj y (List.mem_append_right _ List.mem_cons_self))
  ·
    have hob := tree_orbit_bound hG hGI hGC hY rfl h17
    rw [h15, hN, ← h16] at hob
    have hpos : 0 < c.L := by
      have h0 : 0 < Nat.card ↥C := Nat.card_pos
      rw [hN, ← h16] at h0
      exact Nat.pos_of_mul_pos_right h0
    rw [cent_sup]
    exact Nat.le_of_mul_le_mul_left hob hpos

end CFSG.KC.J4TreeS
