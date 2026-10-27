module

public import CFSG.Certificates.Kernel.J4TreeTop.TreeSound

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

@[expose] noncomputable def topGs (g : TGlob) : List J :=
  g.wn.map (fun w => wordProd xJ (wordC 64 w)) ++ g.cc.map burnsideJ4NP_treeElt


theorem forall₂_sel {α β : Type*} {R : α → β → Prop} {a : α} {b : β} {xs : List α}
    {Xs : List β} (h : List.Forall₂ R xs Xs) :
    ∀ gi : List ℕ, (∀ j ∈ gi, j < Xs.length) →
      List.Forall₂ R (gi.map (xs.getD · a)) (gi.map (Xs.getD · b))
  | [], _ => .nil
  | j :: gi, hj => .cons (forall₂_getD h j (by rw [forall₂_length h]; exact hj j List.mem_cons_self))
      (forall₂_sel h gi fun j' hj' => hj j' (List.mem_cons_of_mem _ hj'))

theorem forall₂_of_beq {xs : List J} {Ys : List ℕ} (h : List.Forall₂ PK xs Ys) :
    ∀ {G : List ℕ}, G.length = Ys.length → (G.zip Ys).all (fun p => Nat.beq p.1 p.2) = true →
      List.Forall₂ PK xs G := by
  induction h with
  | nil =>
    intro G hl _
    rw [List.length_nil, List.length_eq_zero_iff] at hl
    rw [hl]
    exact .nil
  | @cons x Y xs Ys hx _ ih =>
    intro G hl hb
    cases G with
    | nil => simp at hl
    | cons Gh G =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hb
      refine .cons ?_ (ih (by simpa using hl) hb.2)
      rw [Nat.eq_of_beq_eq_true hb.1]
      exact hx

theorem topGlob_sound {T : Tabs} (hT : tabsOK T = true) (hq : Nat.beq (M QK QiK) oneK = true)
    {i : ℕ} {g : TGlob} (h : topGlobOK T i g = true) :
    g.k = (topNodes.getD i default).node ∧ g.kids = (topNodes.getD i default).kids ∧
      (∀ kd ∈ g.kids, kd.2 < (topNodes.getD i default).children.length ∧
        ((topNodes.getD i default).children.getD kd.2 default).target = kd.1 ∧ kd.1 ≠ 0) ∧
      g.k ∈ treeTopIds ∧
      List.Forall₂ PK (topGs g) g.G ∧ List.Forall₂ (fun s X => PK s⁻¹ X) (topGs g) g.GI ∧
      (∀ s ∈ topGs g, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) ∧
      (∀ s ∈ g.cc.map burnsideJ4NP_treeElt, s ∈ P0) ∧
      2 ^ g.cc.length ≤ Nat.card ↥(Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt}) ∧
      (∀ o ∈ g.odd, Nat.card ↥(Subgroup.closure
          {x | x ∈ o.2.1.map fun j => (topGs g).getD j 1}) = o.1 ∧ o.1 % 2 = 1) ∧
      coprimeAll (2 ^ g.cc.length :: g.odd.map Prod.fst) = true ∧
      treeOrd g.k = 2 ^ g.cc.length * (g.odd.map Prod.fst).foldr (· * ·) 1 := by
  unfold topGlobOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩ := h
  have hB2 := forall₂_cc hT _ (List.all_eq_true.mp h5)
  have hS2 := forall₂_cc hT _ (List.all_eq_true.mp h6)
  have hY2 := List.rel_append (forall₂_word hT g.wn) hS2
  have hG2 : List.Forall₂ PK (topGs g) g.G :=
    forall₂_of_beq hY2 (by rw [h7]; simp) h9
  have hGI2 := forall₂_inv hG2 h10 h8
  have hGC : ∀ s ∈ topGs g, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) := by
    intro s hs
    exact Subgroup.mem_inf.mpr ⟨mem_Hj_of hG2 s hs,
      mem_cent_closure fun b hb => comm_of_all hG2 hB2 h12 s hs b hb⟩
  refine ⟨h1, h2, fun kd hkd => ?_, by simpa using h4, hG2, hGI2, hGC, fun s hs => ?_, ?_,
    fun o ho => ?_, h15, h16⟩
  · have hk := List.all_eq_true.mp h3 kd hkd
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, Bool.not_eq_true'] at hk
    refine ⟨hk.1.1, hk.1.2, fun h0 => ?_⟩
    rw [h0] at hk
    exact absurd hk.2 (by decide)
  · obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hs
    have hc := List.all_eq_true.mp h6 ce hce
    unfold coordOK at hc
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
    exact burnsideJ4NP_treeElt_mem_P0 hc.2
  · have := card_ge_of_nw (K := Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt})
      (fun x hx => Subgroup.subset_closure hx) (leads_inj hq hS2 h13)
    rwa [List.length_map] at this
  · have hoK := List.all_eq_true.mp h14 o ho
    unfold oddOK at hoK
    simp only [Bool.and_eq_true, beq_iff_eq] at hoK
    obtain ⟨⟨⟨⟨hgi, hlen⟩, hodd⟩, htree⟩, hclosed⟩ := hoK
    have hgi' : ∀ j ∈ o.2.1, j < g.G.length := fun j hj =>
      Nat.blt_eq.mp (List.all_eq_true.mp hgi j hj)
    have hgiI : ∀ j ∈ o.2.1, j < g.GI.length := fun j hj => by rw [h8]; exact hgi' j hj
    have hGo := forall₂_sel (a := 1) (b := 0) hG2 o.2.1 hgi'
    have hGIo := forall₂_sel (a := 1) (b := 0) hGI2 o.2.1 hgiI
    have hne : o.2.2 ≠ [] := by
      intro he
      rw [he] at hlen
      simp only [List.length_nil] at hlen
      omega
    refine ⟨?_, hodd⟩
    rw [tree_closure_card hGo hGIo (by simp) htree hclosed hne, hlen]

end CFSG.KC.J4TreeS
