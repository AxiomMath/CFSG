module

public import CFSG.Certificates.Kernel.J4TreeTop.MergeSound
public import Certificates.Data.Kernel.J4TreeTopUneq
public import CFSG.Milestones.ASVolI.C31.J4NP.HCl

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

theorem card_mul_le_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {C X Y : Subgroup G}
    (hX : X ≤ C) (hY : Y ≤ C) (hXY : X ⊓ Y = ⊥) : Nat.card X * Nat.card Y ≤ Nat.card C := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => (⟨p.1.1 * p.2.1, C.mul_mem (hX p.1.2) (hY p.2.2)⟩ : C)) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
  simp only [Subtype.mk.injEq] at h
  have hm : a'⁻¹ * a ∈ X ⊓ Y := by
    refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem ha') ha, ?_⟩
    have e : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [e]
    exact Y.mul_mem hb' (Y.inv_mem hb)
  rw [hXY, Subgroup.mem_bot] at hm
  have e1 : a = a' := by
    have := congrArg (a' * ·) hm
    simpa using this
  subst e1
  have e2 : b = b' := mul_left_cancel h
  subst e2
  rfl

theorem two_max_of_card_le {G : Type*} [Group G] [Finite G] {C P Z : Subgroup G} (hZC : Z ≤ C)
    (hZ : Nat.card Z % 2 = 1) (hle : Nat.card C ≤ Nat.card P * Nat.card Z) :
    ∀ Q : Subgroup G, Q ≤ C → IsPGroup 2 ↥Q → P ≤ Q → Q = P := by
  intro Q hQC hQ2 hPQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card Z) := by
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hZ))
  have hdvd : Nat.card Q * Nat.card Z ∣ Nat.card C :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le hQC) (Subgroup.card_dvd_of_le hZC)
  have h1 : Nat.card Q * Nat.card Z ≤ Nat.card P * Nat.card Z :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hle
  exact (Subgroup.eq_of_le_of_card_ge hPQ (Nat.le_of_mul_le_mul_right h1 Nat.card_pos)).symm

theorem pow2F_spec : ∀ (f x : ℕ), pow2F f x = true → ∃ n, x = 2 ^ n
  | 0, _, h => by simp [pow2F] at h
  | f + 1, x, h => by
    simp only [pow2F, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Nat.blt_eq] at h
    rcases h with rfl | ⟨⟨h2, -⟩, h⟩
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := pow2F_spec f (x / 2) h
      refine ⟨n + 1, ?_⟩
      rw [pow_succ]
      omega

theorem map_getD_range {α : Type*} (l : List α) (d : α) {n : ℕ} (hn : n = l.length) :
    (List.range n).map (fun i => l.getD i d) = l := by
  subst hn
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

section PK

@[expose] noncomputable def wordJ (Gs : List J) (w : List ℕ) : J :=
  w.foldl (fun a j => a * if j < Gs.length then Gs.getD j 1 else (Gs.getD (j - Gs.length) 1)⁻¹) 1

theorem pk_getD_of {Gs : List J} {G GI : List ℕ} (hG : List.Forall₂ PK Gs G)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs GI) {j : ℕ} (hj : j < 2 * G.length) :
    PK (if j < Gs.length then Gs.getD j 1 else (Gs.getD (j - Gs.length) 1)⁻¹)
      (if Nat.blt j G.length then G.getD j 0 else GI.getD (j - G.length) 0) := by
  have hl : Gs.length = G.length := forall₂_length hG
  by_cases hjn : j < G.length
  · rw [if_pos (by omega), if_pos (Nat.blt_eq.mpr hjn)]
    exact forall₂_getD hG j (by omega)
  · rw [if_neg (by omega), if_neg (by rw [Nat.blt_eq]; exact hjn), hl]
    exact forall₂_getD hGI _ (by omega)

theorem pk_wordG {Gs : List J} {G GI : List ℕ} (hG : List.Forall₂ PK Gs G)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs GI) :
    ∀ (w : List ℕ), (∀ j ∈ w, j < 2 * G.length) → ∀ {acc : J} {ACC : ℕ}, PK acc ACC →
      PK (w.foldl (fun a j => a * if j < Gs.length then Gs.getD j 1 else
          (Gs.getD (j - Gs.length) 1)⁻¹) acc)
        (w.foldl (fun a j => M a (if Nat.blt j G.length then G.getD j 0 else
          GI.getD (j - G.length) 0)) ACC)
  | [], _, _, _, h => h
  | j :: w, hw, acc, ACC, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact pk_wordG hG hGI w (fun j' hj' => hw j' (List.mem_cons_of_mem _ hj'))
      (pk_mul h (pk_getD_of hG hGI (hw j List.mem_cons_self)))

theorem tree_closure_all {gl : List J} {Go GIo : List ℕ} (hG : List.Forall₂ PK gl Go)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) gl GIo) {n : ℕ} (hn : n = Go.length)
    {es : List (ℕ × ℕ × ℕ)} (ht : treeOK (fun j x => M x (GIo.getD j 0)) n oneK es = true)
    (hc : closedOK (fun j x => M x (Go.getD j 0)) n (es.map Prod.fst) = true) (hne : es ≠ []) :
    ∀ p ∈ Subgroup.closure {x | x ∈ gl}, ∃ e ∈ es, PK p e.1 := by
  classical
  set O := Subgroup.closure {x | x ∈ gl}
  have hcard := tree_closure_card hG hGI hn ht hc hne
  obtain ⟨hsort, hent⟩ := treeOK_spec ht
  set codes := es.map Prod.fst with hcodes
  have hcode : ∀ x ∈ codes, ∃ p ∈ O, PK p x := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact tree_right hG hGI hn ht e he
  have hcan : ∀ x ∈ codes, x < 2 ^ 144 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact (hent e he).1
  choose! q hqO hq using hcode
  set S : Finset J := codes.toFinset.image q with hS
  have hSO : (S : Set J) ⊆ (O : Set J) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
    exact hqO x (List.mem_toFinset.mp hx)
  have hnd : codes.Nodup := hsort.imp (fun h => ne_of_lt h)
  have hScard : S.card = es.length := by
    rw [hS, Finset.card_image_of_injOn (fun x hx y hy hxy => pk_canon (hq x (by simpa using hx))
      (hq y (by simpa using hy)) (hcan x (by simpa using hx)) (hcan y (by simpa using hy)) hxy),
      List.toFinset_card_of_nodup hnd, hcodes, List.length_map]
  have hSeq : (S : Set J) = (O : Set J) := by
    refine Set.eq_of_subset_of_ncard_le hSO ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hScard, ← hcard]
    exact (Nat.card_coe_set_eq (O : Set J)).symm.le
  intro p hp
  have hpS : p ∈ (S : Set J) := by rw [hSeq]; exact hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hpS)
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact ⟨e, he, hq _ (List.mem_toFinset.mp hx)⟩

theorem childBase_sound {T : Tabs} (hT : tabsOK T = true) {g : TGlob} {c : TUneq}
    {es : List (ℕ × ℕ × ℕ)} (h : childBaseOK T g c es = true) {Gs : List J}
    (hG : List.Forall₂ PK Gs g.G) (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs g.GI)
    (hGC : ∀ s ∈ Gs, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) :
    let C := Hj ⊓ Subgroup.centralizer
      ((burnsideJ4NP_Rep g.k ⊔ Subgroup.zpowers (burnsideJ4NP_treeElt c.y) : Subgroup J) : Set J)
    let Z := Subgroup.closure {x | x ∈ c.zw.map (wordJ Gs)}
    g.k = (topNodes.getD c.i default).node ∧ c.j < (topNodes.getD c.i default).children.length ∧
      c.y = ((topNodes.getD c.i default).children.getD c.j default).y ∧
      c.tgt = ((topNodes.getD c.i default).children.getD c.j default).target ∧
      coordOK c.y = true ∧ (treeBasis g.k).all coordOK = true ∧
      burnsideJ4NP_treeElt c.y ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) ∧
      burnsideJ4NP_treeElt c.y * burnsideJ4NP_treeElt c.y = 1 ∧
      c.L * Nat.card C ≤ Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) ∧
      Z ≤ C ∧ Nat.card Z = c.q ∧ c.q % 2 = 1 ∧ ∀ p ∈ Z, ∃ e ∈ c.zs, PK p e.1 := by
  intro C Z
  unfold childBaseOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, hz⟩ := h
  set y := burnsideJ4NP_treeElt c.y with hy
  set bJ := (treeBasis g.k).map burnsideJ4NP_treeElt with hbJ
  have hY : PK y (ccT T c.y) := pk_cc hT h5
  have hB2 : List.Forall₂ PK bJ ((treeBasis g.k).map (ccT T)) :=
    forall₂_cc hT _ (List.all_eq_true.mp h6)
  have hAdef : burnsideJ4NP_Rep g.k = Subgroup.closure {x | x ∈ bJ} := rfl
  have hyC : y ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) := by
    refine Subgroup.mem_inf.mpr ⟨hY.1, ?_⟩
    rw [hAdef]
    exact mem_cent_closure fun b hb => comm_of_all (.cons hY .nil) hB2
      (by rw [List.all_cons, List.all_nil, Bool.and_true]; exact h8) y List.mem_cons_self b hb
  have hCdef : C = (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) ⊓
      Subgroup.centralizer {y} := cent_sup _ y
  have hob := tree_orbit_bound hG hGI hGC hY rfl h10
  rw [h9, ← hCdef] at hob
  unfold zOK at hz
  simp only [Bool.and_eq_true] at hz
  obtain ⟨⟨⟨hzw, hinv⟩, hcom⟩, hodd⟩ := hz
  set Zl := c.zw.map (wordJ Gs) with hZl
  set Zc := c.zw.map (wordG g.G g.GI) with hZc
  set ZIc := c.zw.map fun w => wordG g.G g.GI (invWord g.G.length w) with hZIc
  have hZ2 : List.Forall₂ PK Zl Zc := by
    rw [hZl, hZc, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro w hw
    have hwj : ∀ j ∈ w, j < 2 * g.G.length := fun j hj =>
      Nat.blt_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hzw w hw) j hj)
    exact pk_wordG hG hGI w hwj pk_one
  have hZI2 : List.Forall₂ (fun s X => PK s⁻¹ X) Zl ZIc :=
    forall₂_inv hZ2 hinv (by simp [hZc, hZIc])
  have hZH : ∀ z ∈ Zl, z ∈ C := by
    intro z hz
    obtain ⟨X, hX, hzX⟩ := forall₂_exists hZ2 z hz
    have hc := List.all_eq_true.mp hcom X hX
    rw [Bool.and_eq_true] at hc
    rw [hCdef]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzX.1, ?_⟩, ?_⟩
    · rw [hAdef]
      exact mem_cent_closure fun b hb =>
        comm_of_all (.cons hzX .nil) hB2 (by simpa using hc.2) z List.mem_cons_self b hb
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (pk_comm hzX hY).mpr hc.1
  have hZC : Z ≤ C := (Subgroup.closure_le C).mpr hZH
  unfold oddOK at hodd
  simp only [Bool.and_eq_true, beq_iff_eq] at hodd
  obtain ⟨⟨⟨⟨-, hlen⟩, hq⟩, htree⟩, hclosed⟩ := hodd
  have hlZ : Zc.length = ZIc.length := by simp [hZc, hZIc]
  rw [map_getD_range Zc 0 rfl] at hclosed
  rw [map_getD_range ZIc 0 hlZ] at htree
  have hnl : (List.range Zc.length).length = Zc.length := List.length_range
  have hne : c.zs ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    omega
  have hcard := tree_closure_card hZ2 hZI2 hnl htree hclosed hne
  exact ⟨h1, h2, h3, h4, h5, h6, hyC, (pk_sq hY).mpr h7, hob, hZC, hcard.trans hlen, hq,
    tree_closure_all hZ2 hZI2 hnl htree hclosed hne⟩

theorem topUneq_sound {T : Tabs} (hT : tabsOK T = true) {g : TGlob} {c : TUneq}
    {es : List (ℕ × ℕ × ℕ)} (h : topUneqOK T g c es = true) {Gs : List J}
    (hG : List.Forall₂ PK Gs g.G) (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs g.GI)
    (hGC : ∀ s ∈ Gs, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) :
    g.k = (topNodes.getD c.i default).node ∧ c.j < (topNodes.getD c.i default).children.length ∧
      c.y = ((topNodes.getD c.i default).children.getD c.j default).y ∧
      c.tgt = ((topNodes.getD c.i default).children.getD c.j default).target ∧
      1 ≤ c.tgt ∧ c.tgt ≤ treeN ∧
      burnsideJ4NP_treeElt c.y ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) ∧
      burnsideJ4NP_treeElt c.y * burnsideJ4NP_treeElt c.y = 1 ∧
      (Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) = treeOrd g.k →
        Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep c.tgt : Set J)) ≤ treeOrd c.tgt ∧
        (treeOrd c.tgt ≤ Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep c.tgt : Set J)) →
          omegaZ (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep c.tgt : Set J)) =
            burnsideJ4NP_Rep c.tgt →
          ∃ h ∈ Hj, burnsideJ4NP_IsHCl
            (burnsideJ4NP_Rep g.k ⊔ Subgroup.zpowers (burnsideJ4NP_treeElt c.y))
            ((burnsideJ4NP_Rep c.tgt).map (MulAut.conj h).toMonoidHom))) := by
  unfold topUneqOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbase, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  obtain ⟨i1, i2, i3, i4, hyc, hbc, hyC, hyy, hob, hZC, hZq, hqodd, hZmem⟩ :=
    childBase_sound hT hbase hG hGI hGC
  refine ⟨i1, i2, i3, i4, Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, hyC, hyy,
    fun hN => ?_⟩
  set A := burnsideJ4NP_Rep g.k with hA
  set y := burnsideJ4NP_treeElt c.y with hy
  set C := Hj ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers y : Subgroup J) : Set J) with hC
  set Z := Subgroup.closure {x | x ∈ c.zw.map (wordJ Gs)} with hZ
  set bJ := (treeBasis g.k).map burnsideJ4NP_treeElt with hbJ
  set t := treeOrd c.tgt with ht
  have hY : PK y (ccT T c.y) := pk_cc hT hyc
  have hB2 : List.Forall₂ PK bJ ((treeBasis g.k).map (ccT T)) :=
    forall₂_cc hT _ (List.all_eq_true.mp hbc)
  have hAdef : A = Subgroup.closure {x | x ∈ bJ} := rfl
  set hW := wordProd xJ (wordC 64 c.h) with hhW
  have hHpk : PK hW (wordT T 64 c.h) := pk_word hT 64 c.h
  have hHi : PK hW⁻¹ c.hI := pk_inv hHpk h4
  have hTB := forall₂_cc hT _ (List.all_eq_true.mp h3)
  have hBY : List.Forall₂ PK (bJ ++ [y]) ((treeBasis g.k).map (ccT T) ++ [ccT T c.y]) :=
    List.rel_append hB2 (.cons hY .nil)
  have hconj : ∀ x ∈ bJ ++ [y], hW⁻¹ * x * hW ∈ burnsideJ4NP_Rep c.tgt :=
    mask_conj hBY hTB hHpk hHi (by rw [beq_iff_eq.mp h5]; simp) h6
  set TT := (burnsideJ4NP_Rep c.tgt).map (MulAut.conj hW).toMonoidHom with hTT
  have hAyT : A ⊔ Subgroup.zpowers y ≤ TT := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · rw [hAdef, Subgroup.closure_le]
      intro b hb
      exact burnsideJ4KW_mem_map_conj.mpr (hconj b (List.mem_append_left _ hb))
    · exact burnsideJ4KW_mem_map_conj.mpr (hconj y (List.mem_append_right _ List.mem_cons_self))
  set CT := Hj ⊓ Subgroup.centralizer (TT : Set J) with hCT
  have hCTC : CT ≤ C := inf_le_inf_left _ (Subgroup.centralizer_le hAyT)
  have hCTeq : (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep c.tgt : Set J)).map
      (MulAut.conj hW).toMonoidHom = CT := by
    rw [hCT, hTT, burnsideJ4NP_map_conj_inf, burnsideJ4NP_map_conj_of_mem (word_mem 64 c.h),
      burnsideJ4NP_centralizer_map_conj]
  have hCTcard : Nat.card CT =
      Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep c.tgt : Set J)) := by
    rw [← hCTeq, burnsideJ4KW_card_map_conj]
  have hZCT : Z ⊓ CT = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨hpZ, hpCT⟩ := Subgroup.mem_inf.mp hp
    rw [Subgroup.mem_bot]
    obtain ⟨e, he, hpe⟩ := hZmem p hpZ
    have hc := List.all_eq_true.mp h9 e he
    rw [Bool.or_eq_true] at hc
    rcases hc with h1' | h1'
    · exact pk_beq hpe pk_one h1'
    · exfalso
      obtain ⟨X, hX, hXc⟩ := List.any_eq_true.mp h1'
      obtain ⟨tb, htb, rfl⟩ := List.mem_map.mp hX
      obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp htb
      have hce' : coordOK ce = true := List.all_eq_true.mp h3 ce hce
      have hx := pk_mul (pk_mul hHpk (pk_cc hT hce')) hHi
      have hxT : hW * burnsideJ4NP_treeElt ce * hW⁻¹ ∈ TT := by
        rw [burnsideJ4KW_mem_map_conj]
        have e' : hW⁻¹ * (hW * burnsideJ4NP_treeElt ce * hW⁻¹) * hW = burnsideJ4NP_treeElt ce := by
          group
        rw [e']
        exact Subgroup.subset_closure (List.mem_map_of_mem hce)
      have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hpCT).2 _ hxT
      have hc' := (pk_comm hpe hx).mp hcomm.symm
      rw [hc'] at hXc
      simp at hXc
  have hqpos : 0 < c.q := by omega
  have hmul := card_mul_le_of_inf_eq_bot hZC hCTC hZCT
  rw [hZq, hCTcard] at hmul
  have hLpos : 0 < c.L := by
    have h0 : 0 < treeOrd g.k := by rw [← hN]; exact Nat.card_pos
    rw [← beq_iff_eq.mp h8] at h0
    exact Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right h0)
  have hCle : Nat.card C ≤ t * c.q := by
    rw [hN, ← beq_iff_eq.mp h8, mul_assoc] at hob
    exact Nat.le_of_mul_le_mul_left hob hLpos
  have hle : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep c.tgt : Set J)) ≤ t := by
    have := hmul.trans hCle
    rw [mul_comm t] at this
    exact Nat.le_of_mul_le_mul_left this hqpos
  refine ⟨hle, fun hlow homega => ⟨hW, word_mem 64 c.h, CT, hCTC, ?_, ?_, ?_⟩⟩
  · obtain ⟨n, hn⟩ := pow2F_spec 64 _ h7
    refine IsPGroup.of_card (n := n) ?_
    rw [hCTcard, le_antisymm hle hlow, ← hn]
  · refine two_max_of_card_le hZC (by rw [hZq]; exact hqodd) ?_
    rw [hCTcard, le_antisymm hle hlow, hZq]
    exact hCle
  · rw [← hCTeq, burnsideJ4NP_omegaZ_map_conj, homega]

theorem topPrune_sound {T : Tabs} (hT : tabsOK T = true) (hq : Nat.beq (M QK QiK) oneK = true)
    {g : TGlob} {c : TUneq} {es : List (ℕ × ℕ × ℕ)} (h : topPruneOK T g c es = true)
    {Gs : List J} (hG : List.Forall₂ PK Gs g.G)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs g.GI)
    (hGC : ∀ s ∈ Gs, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) :
    g.k = (topNodes.getD c.i default).node ∧ c.j < (topNodes.getD c.i default).children.length ∧
      c.y = ((topNodes.getD c.i default).children.getD c.j default).y ∧
      c.tgt = ((topNodes.getD c.i default).children.getD c.j default).target ∧ c.tgt = 0 ∧
      burnsideJ4NP_treeElt c.y ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) ∧
      burnsideJ4NP_treeElt c.y * burnsideJ4NP_treeElt c.y = 1 ∧
      (Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) = treeOrd g.k →
        ∃ B₀ : Subgroup J, burnsideJ4NP_IsHCl
            (burnsideJ4NP_Rep g.k ⊔ Subgroup.zpowers (burnsideJ4NP_treeElt c.y)) B₀ ∧
          2 ^ 6 < Nat.card ↥(B₀ ⊓ Eg uJ 11)) := by
  unfold topPruneOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbase, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  obtain ⟨i1, i2, i3, i4, hyc, hbc, hyC, hyy, hob, hZC, hZq, hqodd, -⟩ :=
    childBase_sound hT hbase hG hGI hGC
  refine ⟨i1, i2, i3, i4, beq_iff_eq.mp h1, hyC, hyy, fun hN => ?_⟩
  set A := burnsideJ4NP_Rep g.k with hA
  set y := burnsideJ4NP_treeElt c.y with hy
  set C := Hj ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers y : Subgroup J) : Set J) with hC
  set Z := Subgroup.closure {x | x ∈ c.zw.map (wordJ Gs)} with hZ
  set bJ := (treeBasis g.k).map burnsideJ4NP_treeElt with hbJ
  have hY : PK y (ccT T c.y) := pk_cc hT hyc
  have hB2 : List.Forall₂ PK bJ ((treeBasis g.k).map (ccT T)) :=
    forall₂_cc hT _ (List.all_eq_true.mp hbc)
  have hAdef : A = Subgroup.closure {x | x ∈ bJ} := rfl
  have hCdef : C = (Hj ⊓ Subgroup.centralizer (A : Set J)) ⊓ Subgroup.centralizer {y} :=
    cent_sup _ y
  have hmemC : ∀ x : J, ∀ X : ℕ, PK x X → commK X (ccT T c.y) = true →
      ((treeBasis g.k).map (ccT T)).all (fun b => commK X b) = true → x ∈ C := by
    intro x X hx hxy hxb
    rw [hCdef]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩, ?_⟩
    · rw [hAdef]
      exact mem_cent_closure fun b hb =>
        comm_of_all (.cons hx .nil) hB2 (by simpa using hxb) x List.mem_cons_self b hb
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (pk_comm hx hY).mpr hxy
  set sJ := c.sC.map burnsideJ4NP_treeElt with hsJ
  have hS2 : List.Forall₂ PK sJ (c.sC.map (ccT T)) := forall₂_cc hT _ (List.all_eq_true.mp h2)
  have hsC : ∀ s ∈ sJ, s ∈ C := by
    intro s hs
    obtain ⟨X, hX, hsX⟩ := forall₂_exists hS2 s hs
    have hc := List.all_eq_true.mp h4 X hX
    rw [Bool.and_eq_true] at hc
    exact hmemC s X hsX hc.1 hc.2
  have hsP0 : ∀ s ∈ sJ, s ∈ P0 := by
    intro s hs
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hs
    have hc := List.all_eq_true.mp h2 ce hce
    unfold coordOK at hc
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
    exact burnsideJ4NP_treeElt_mem_P0 hc.2
  set S := Subgroup.closure {x | x ∈ sJ} with hSdef
  have hSC : S ≤ C := (Subgroup.closure_le C).mpr hsC
  have hS2grp : IsPGroup 2 ↥S :=
    (CFSG.Quasithin.J4Loc.isPGroup_P0 j4Facts).to_le ((Subgroup.closure_le P0).mpr hsP0)
  have hScard : 2 ^ c.sC.length ≤ Nat.card S := by
    have := card_ge_of_nw (K := S) (fun x hx => Subgroup.subset_closure hx) (leads_inj hq hS2 h5)
    rwa [List.length_map] at this
  have hLpos : 0 < c.L := by
    have h0 : 0 < treeOrd g.k := by rw [← hN]; exact Nat.card_pos
    rw [← beq_iff_eq.mp h6] at h0
    exact Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right h0)
  have hCle : Nat.card C ≤ Nat.card S * Nat.card Z := by
    rw [hN, ← beq_iff_eq.mp h6, mul_assoc] at hob
    rw [hZq]
    exact (Nat.le_of_mul_le_mul_left hob hLpos).trans (Nat.mul_le_mul_right _ hScard)
  have hmax := two_max_of_card_le hZC (by rw [hZq]; exact hqodd) hCle
  set eJ := c.eC.map burnsideJ4NP_treeElt with heJ
  have hE2 : List.Forall₂ PK eJ (c.eC.map (ccT T)) := forall₂_cc hT _ (List.all_eq_true.mp h3)
  have heΩ : ∀ e ∈ eJ, e ∈ omegaZ S ⊓ Eg uJ 11 := by
    intro e he
    obtain ⟨X, hX, heX⟩ := forall₂_exists hE2 e he
    have hc := List.all_eq_true.mp h9 X hX
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hin, hsq⟩, hey⟩, heb⟩, hes⟩ := hc
    have heC : e ∈ C := hmemC e X heX hey heb
    have hes' : ∀ s ∈ sJ, e * s = s * e := fun s hs =>
      comm_of_all (.cons heX .nil) hS2 (by simpa using hes) e List.mem_cons_self s hs
    have heP0 : e ∈ P0 := by
      obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp he
      have hc := List.all_eq_true.mp h3 ce hce
      unfold coordOK at hc
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
      exact burnsideJ4NP_treeElt_mem_P0 hc.2
    have heS : e ∈ S := by
      have hle : Subgroup.closure {x | x ∈ e :: sJ} ≤ C := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact heC
        · exact hsC x hx
      have hP0 : Subgroup.closure {x | x ∈ e :: sJ} ≤ P0 := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact heP0
        · exact hsP0 x hx
      have hSle : S ≤ Subgroup.closure {x | x ∈ e :: sJ} :=
        Subgroup.closure_mono fun x hx => List.mem_cons_of_mem _ hx
      have heq := hmax _ hle ((CFSG.Quasithin.J4Loc.isPGroup_P0 j4Facts).to_le hP0) hSle
      rw [← heq]
      exact Subgroup.subset_closure List.mem_cons_self
    refine Subgroup.mem_inf.mpr ⟨CFSG.Quasithin.J4Loc.mem_omegaZ.mpr ⟨heS, fun w hw => ?_,
      (pk_sq heX).mpr hsq⟩, ?_⟩
    · have hcent : e ∈ Subgroup.centralizer (S : Set J) := mem_cent_closure hes'
      exact (Subgroup.mem_centralizer_iff.mp hcent w hw).symm
    · rw [burnsideJ4NP_mem_Eg_iff heX.1, ← burnsideJ4NP_encJ_of_mem heX.1, inE_eq heX.2]
      exact hin
  have h7' := card_ge_of_nw heΩ (leads_inj hq hE2 h8)
  have hlen : eJ.length = 7 := by rw [heJ, List.length_map]; exact beq_iff_eq.mp h7
  refine ⟨omegaZ S, ⟨S, hSC, hS2grp, hmax, rfl⟩, ?_⟩
  rw [hlen] at h7'
  calc 2 ^ 6 < 2 ^ 7 := by norm_num
    _ ≤ _ := h7'

end PK

end CFSG.KC.J4TreeS
