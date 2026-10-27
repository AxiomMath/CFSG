module

public import Certificates.Data.Kernel.FiveStdKOrb
public import CFSG.Certificates.Kernel.FiveStdKTreeSound
public import CFSG.GH74.GLS.LU.Local.FiveStdBase
public import CFSG.GroupTheory.CentralizerMapMulEquiv

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdBase

@[expose] noncomputable def decE (p : Nat) : E :=
  ⟨⟨fA0 p, Nat.mod_lt _ (by decide)⟩, ⟨fA1 p, Nat.mod_lt _ (by decide)⟩,
    ⟨fA2 p, Nat.mod_lt _ (by decide)⟩, ⟨fA3 p, Nat.mod_lt _ (by decide)⟩,
    ⟨fB0 p, Nat.mod_lt _ (by decide)⟩, ⟨fB1 p, Nat.mod_lt _ (by decide)⟩,
    ⟨fB2 p, Nat.mod_lt _ (by decide)⟩, ⟨fB3 p, Nat.mod_lt _ (by decide)⟩, decide (fS p = 1)⟩

theorem codeE_decE {p : Nat} (h : p < 781250) : codeE (decE p) = p := by
  simp only [codeE, decE, fA0, fA1, fA2, fA3, fB0, fB1, fB2, fB3, fS, nat_div, nat_mod]
  by_cases hs : p / 390625 = 1
  · simp only [hs, decide_true, if_true]
    omega
  · simp only [hs, decide_false, Bool.false_eq_true, if_false]
    omega

theorem decE_codeE (x : E) : decE (codeE x) = x :=
  codeE_injective (codeE_decE (codeE_lt x))

theorem validK_lt {p : Nat} (h : validK p = true) : p < 781250 :=
  (blt_iff _ _).1 (andB_true h).1

theorem valid_decE {p : Nat} (h : validK p = true) : validE (decE p) = true := by
  rw [← validK_codeE, codeE_decE (validK_lt h), h]

@[expose] noncomputable def decL (f : Nat → Nat) (n : Nat) : List E := (List.range n).map fun j => decE (f j)

theorem mem_decL {f : Nat → Nat} {n : Nat} {x : E} : x ∈ decL f n ↔ ∃ j < n, decE (f j) = x := by
  simp [decL]

theorem decL_nodup {f : Nat → Nat} {n : Nat} (hlt : ∀ j < n, f j < 781250)
    (hmono : ∀ i j, i < j → j < n → f i < f j) : (decL f n).Nodup := by
  unfold decL
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  rw [List.mem_range] at hi hj
  have h := congrArg codeE hij
  rw [codeE_decE (hlt i hi), codeE_decE (hlt j hj)] at h
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd h (Nat.ne_of_lt (hmono i j h' hj))
  · exact h'
  · exact absurd h.symm (Nat.ne_of_lt (hmono j i h' hi))

theorem length_flatMap_const {α β : Type} (L : List α) (f : α → List β) (k : Nat)
    (h : ∀ a ∈ L, (f a).length = k) : (L.flatMap f).length = k * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb), List.length_cons]
    ring

theorem gl_filter_length : ∀ d : Fin 5, d ≠ 0 →
    (glBlocks.filter fun b => decide (d * det4 b = 1)).length = 120 := by decide +kernel

theorem gl_norm_length :
    (glBlocks.filter fun a => a.1 = 1 || (a.1 = 0 && a.2.1 = 1)).length = 120 := by decide +kernel

theorem length_Cs : Cs.length = 28800 := by
  unfold Cs
  rw [length_flatMap_const _ _ 240, gl_norm_length]
  intro a ha
  have hgl : det4 a ≠ 0 := by
    have := (List.mem_filter.1 (List.mem_filter.1 ha).1).2
    simpa using this
  rw [length_flatMap_const _ _ 2, gl_filter_length _ hgl]
  intro b _
  rfl

variable {Gp : Type} [Group Gp]

theorem tree_cover {ι : E → Gp} (hM : Model ι) {T G nG : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (h : ∀ i < 28800, tPt T G nG 28800 i = true) :
    ∀ x, validE x = true → ∃ i < 28800, rCode (f64 T i) = codeE x := by
  classical
  obtain ⟨h1, h2⟩ := tree_sound hM gE hg h
  have hlt : ∀ i < 28800, rCode (f64 T i) < 781250 := by
    intro i hi
    obtain ⟨x, -, hx, -⟩ := h1 i hi
    rw [← hx]
    exact codeE_lt x
  set Lt := decL (fun i => rCode (f64 T i)) 28800 with hLt
  have hnd : Lt.Nodup := decL_nodup hlt h2
  have hsub : Lt.toFinset ⊆ Cs.toFinset := by
    intro y hy
    rw [List.mem_toFinset] at hy ⊢
    obtain ⟨i, hi, rfl⟩ := mem_decL.1 hy
    obtain ⟨x, hx, hxc, -⟩ := h1 i hi
    rw [← hxc, decE_codeE]
    exact (mem_Cs_iff x).2 hx
  have hcard : Cs.toFinset.card ≤ Lt.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, hLt, decL, List.length_map, List.length_range]
    exact (List.toFinset_card_le Cs).trans length_Cs.le
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro x hx
  have : x ∈ Lt := by
    rw [← List.mem_toFinset, heq, List.mem_toFinset]
    exact (mem_Cs_iff x).2 hx
  obtain ⟨i, hi, hix⟩ := mem_decL.1 this
  refine ⟨i, hi, ?_⟩
  rw [← hix, codeE_decE (hlt i hi)]

theorem tree_ind {ι : E → Gp} (hM : Model ι) {T G nG N : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (h : ∀ i < N, tPt T G nG N i = true) (P : E → Prop) (h1 : P oneE)
    (hs : ∀ x l, validE x = true → l < nG → P x → P (mulE x (gE l))) :
    ∀ i < N, ∃ x, validE x = true ∧ codeE x = rCode (f64 T i) ∧ P x := by
  have hpt := fun i hi => tPt_spec (h i hi)
  suffices H : ∀ n, ∀ i < N, rDep (f64 T i) = n →
      ∃ x, validE x = true ∧ codeE x = rCode (f64 T i) ∧ P x from fun i hi => H _ i hi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hn
    by_cases hz : rDep (f64 T i) = 0
    · exact ⟨oneE, hM.valid_one, by rw [codeE_oneE, (hpt i hi).2.1 hz], h1⟩
    · obtain ⟨hp, hl, hd, hm⟩ := (hpt i hi).2.2 hz
      obtain ⟨x, hx, hxc, hxP⟩ := ih _ (hn ▸ hd) _ hp rfl
      obtain ⟨hgv, hgc⟩ := hg _ hl
      exact ⟨mulE x (gE (rLet (f64 T i))), hM.valid_mul _ _ hx hgv,
        by rw [codeE_mulE, hxc, hgc, hm], hs _ _ hx hl hxP⟩

theorem all_of_tree {ι : E → Gp} (hM : Model ι) {T G nG : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (h : ∀ i < 28800, tPt T G nG 28800 i = true) (P : E → Prop) (h1 : P oneE)
    (hs : ∀ x l, validE x = true → l < nG → P x → P (mulE x (gE l))) :
    ∀ x, validE x = true → P x := by
  intro x hx
  obtain ⟨i, hi, hic⟩ := tree_cover hM gE hg h x hx
  obtain ⟨y, -, hyc, hyP⟩ := tree_ind hM gE hg h P h1 hs i hi
  rwa [codeE_injective (hyc.trans hic)] at hyP

@[expose] def vSub {ι : E → Gp} (hM : Model ι) : Subgroup Gp where
  carrier := {g | ∃ x, validE x = true ∧ ι x = g}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨mulE x y, hM.valid_mul _ _ hx hy, hM.map_mul _ _ hx hy⟩
  one_mem' := ⟨oneE, hM.valid_one, hM.map_one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨invE x, hM.valid_inv _ hx, hM.map_inv _ hx⟩

theorem mem_vSub {ι : E → Gp} (hM : Model ι) {g : Gp} : g ∈ vSub hM ↔ ∃ x, validE x = true ∧ ι x = g :=
  Iff.rfl

theorem card_vSub {ι : E → Gp} (hM : Model ι) {T G nG : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (h : ∀ i < 28800, tPt T G nG 28800 i = true) : Nat.card (vSub hM) = 28800 := by
  obtain ⟨h1, h2⟩ := tree_sound hM gE hg h
  have hlt : ∀ i < 28800, rCode (f64 T i) < 781250 := by
    intro i hi
    obtain ⟨x, -, hx, -⟩ := h1 i hi
    rw [← hx]
    exact codeE_lt x
  have hV : V (decL (fun i => rCode (f64 T i)) 28800) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_decL.1 hy
    obtain ⟨x, hx, hxc, -⟩ := h1 i hi
    rw [← hxc, decE_codeE]
    exact hx
  have hS : ((vSub hM : Subgroup Gp) : Set Gp) = S ι (decL (fun i => rCode (f64 T i)) 28800) := by
    ext g
    rw [SetLike.mem_coe, mem_vSub, mem_S]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi, hic⟩ := tree_cover hM gE hg h x hx
      exact ⟨x, mem_decL.2 ⟨i, hi, by rw [hic, decE_codeE]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hV x hx, rfl⟩
  rw [natCard_eq_of_coe _ hS, natCard_S hM hV (decL_nodup hlt h2), decL, List.length_map,
    List.length_range]

theorem cjK_codeE (a x : E) : cjK (codeE a) (codeE (invE a)) (codeE x) = codeE (conjE a x) := by
  simp only [cjK, conjE, codeE_mulE]

theorem oPt_spec {G GI nG R M root j : Nat} (h : oPt G GI nG R M root j = true) :
    (j + 1 < M → oCode (f96 R j) < oCode (f96 R (j + 1))) ∧
    (∀ l < nG, oNx (f96 R j) l < M ∧
      oCode (f96 R (oNx (f96 R j) l)) = cjK (f20 G l) (f20 GI l) (oCode (f96 R j))) ∧
    (oDep (f96 R j) = 0 → oCode (f96 R j) = root) ∧
    (oDep (f96 R j) ≠ 0 → oPar (f96 R j) < M ∧ oLet (f96 R j) < nG ∧
      oDep (f96 R (oPar (f96 R j))) < oDep (f96 R j) ∧
      cjK (f20 G (oLet (f96 R j))) (f20 GI (oLet (f96 R j))) (oCode (f96 R (oPar (f96 R j)))) =
        oCode (f96 R j)) := by
  unfold oPt at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  have h4' := ifB_true h4
  refine ⟨fun hj => (blt_iff _ _).1 ((ifB_true h1).1 ((blt_iff _ _).2 hj)), fun l hl => ?_,
    fun hz => ?_, fun hz => ?_⟩
  · have := (allN_iff _ _).1 h3 l hl
    rw [letB_eq] at this
    obtain ⟨ha, hb⟩ := andB_true this
    exact ⟨(blt_iff _ _).1 ha, Nat.eq_of_beq_eq_true hb⟩
  · exact Nat.eq_of_beq_eq_true (h4'.1 (by rw [hz]; rfl))
  · have hb : Nat.beq (oDep (f96 R j)) 0 = false := by
      cases hb : Nat.beq (oDep (f96 R j)) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hz
    have h5 := h4'.2 hb
    rw [letB_eq, letB_eq, letB_eq] at h5
    obtain ⟨ha, h6⟩ := andB_true h5
    obtain ⟨hl, h7⟩ := andB_true h6
    obtain ⟨hd, hm⟩ := andB_true h7
    exact ⟨(blt_iff _ _).1 ha, (blt_iff _ _).1 hl, (blt_iff _ _).1 hd, Nat.eq_of_beq_eq_true hm⟩

theorem cPt_spec {B g M k : Nat} (h : cPt B g M k = true) :
    validK (f20 B k) = true ∧ (k + 1 < M → f20 B k < f20 B (k + 1)) ∧
      mulK (f20 B k) g = mulK g (f20 B k) := by
  unfold cPt at h
  rw [letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  exact ⟨h1, fun hk => (blt_iff _ _).1 ((ifB_true h3).1 ((blt_iff _ _).2 hk)), Nat.eq_of_beq_eq_true h4⟩

theorem clsOK_spec {G GI nG g R M B Mc v : Nat} (h : clsOK G GI nG g R M B Mc v = true) :
    (∀ l < nG, validK (f20 G l) = true ∧ mulK (f20 G l) (f20 GI l) = oneK) ∧ validK g = true ∧
      0 < M ∧ (∀ j < M, oPt G GI nG R M g j = true) ∧ (∀ k < Mc, cPt B g Mc k = true) ∧
      validK v = true ∧ cjK v (invK v) g = invK g := by
  unfold clsOK genOK at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  obtain ⟨h7, h8⟩ := andB_true h6
  obtain ⟨h9, h10⟩ := andB_true h8
  obtain ⟨h11, h12⟩ := andB_true h10
  refine ⟨fun l hl => ?_, h3, (blt_iff _ _).1 h5, (allN_iff _ _).1 h7, (allN_iff _ _).1 h9, h11,
    Nat.eq_of_beq_eq_true h12⟩
  obtain ⟨ha, hb⟩ := andB_true ((allN_iff _ _).1 h1 l hl)
  exact ⟨ha, Nat.eq_of_beq_eq_true hb⟩

theorem gi_eq {ι : E → Gp} (hM : Model ι) {G GI nG : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (hgi : ∀ l < nG, validK (f20 GI l) = true)
    (hm : ∀ l < nG, mulK (f20 G l) (f20 GI l) = oneK) :
    ∀ l < nG, f20 GI l = codeE (invE (gE l)) := by
  intro l hl
  obtain ⟨hv, hc⟩ := hg l hl
  have hy := valid_decE (hgi l hl)
  have h1 : mulE (gE l) (decE (f20 GI l)) = oneE := by
    apply codeE_injective
    rw [codeE_mulE, hc, codeE_decE (validK_lt (hgi l hl)), hm l hl, codeE_oneE]
  have h2 : ι (decE (f20 GI l)) = ι (invE (gE l)) := by
    rw [hM.map_inv _ hv]
    apply eq_inv_of_mul_eq_one_right
    rw [← hM.map_mul _ _ hv hy, h1, hM.map_one]
  rw [← hM.inj _ _ hy (hM.valid_inv _ hv) h2, codeE_decE (validK_lt (hgi l hl))]

theorem orb_sound {ι : E → Gp} (hM : Model ι) {G GI nG R M : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (hgi : ∀ l < nG, f20 GI l = codeE (invE (gE l))) {gx : E} (hgx : validE gx = true)
    (h : ∀ j < M, oPt G GI nG R M (codeE gx) j = true) :
    ∀ j < M, ∃ x, validE x = true ∧ codeE x = oCode (f96 R j) ∧
      ∃ c, validE c = true ∧ ι x = ι c * ι gx * (ι c)⁻¹ := by
  have hpt := fun j hj => oPt_spec (h j hj)
  suffices H : ∀ n, ∀ j < M, oDep (f96 R j) = n → ∃ x, validE x = true ∧ codeE x = oCode (f96 R j) ∧
      ∃ c, validE c = true ∧ ι x = ι c * ι gx * (ι c)⁻¹ from fun j hj => H _ j hj rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj hn
    by_cases hz : oDep (f96 R j) = 0
    · refine ⟨gx, hgx, ((hpt j hj).2.2.1 hz).symm, oneE, hM.valid_one, ?_⟩
      rw [hM.map_one]
      group
    · obtain ⟨hp, hl, hd, hm⟩ := (hpt j hj).2.2.2 hz
      obtain ⟨x, hx, hxc, c, hc, hxe⟩ := ih _ (hn ▸ hd) _ hp rfl
      obtain ⟨hgv, hgc⟩ := hg _ hl
      refine ⟨conjE (gE (oLet (f96 R j))) x, hM.valid_conjE hgv hx, ?_, mulE (gE (oLet (f96 R j))) c,
        hM.valid_mul _ _ hgv hc, ?_⟩
      · rw [← hm, ← hxc, ← hgc, hgi _ hl, cjK_codeE]
      · rw [hM.map_conjE hgv hx, hxe, hM.map_mul _ _ hgv hc]
        group

theorem orb_closed {ι : E → Gp} (hM : Model ι) {T G GI nG R M root : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (hgi : ∀ l < nG, f20 GI l = codeE (invE (gE l)))
    (hT : ∀ i < 28800, tPt T G nG 28800 i = true)
    (h : ∀ j < M, oPt G GI nG R M root j = true) :
    ∀ c, validE c = true → ∀ y, validE y = true → (∃ j < M, oCode (f96 R j) = codeE y) →
      ∃ j < M, oCode (f96 R j) = codeE (conjE c y) := by
  have hpt := fun j hj => oPt_spec (h j hj)
  refine all_of_tree hM gE hg hT _ ?_ ?_
  · intro y hy hj
    have : conjE oneE y = y := by
      apply hM.inj _ _ (hM.valid_conjE hM.valid_one hy) hy
      rw [hM.map_conjE hM.valid_one hy, hM.map_one]
      group
    rwa [this]
  · intro x l hx hl hP y hy hj
    obtain ⟨hgv, hgc⟩ := hg l hl
    obtain ⟨j, hjM, hjc⟩ := hj
    obtain ⟨hn, hnc⟩ := (hpt j hjM).2.1 l hl
    have h1 : conjE (mulE x (gE l)) y = conjE x (conjE (gE l) y) := by
      apply hM.inj _ _ (hM.valid_conjE (hM.valid_mul _ _ hx hgv) hy)
        (hM.valid_conjE hx (hM.valid_conjE hgv hy))
      rw [hM.map_conjE (hM.valid_mul _ _ hx hgv) hy, hM.map_conjE hx (hM.valid_conjE hgv hy),
        hM.map_conjE hgv hy, hM.map_mul _ _ hx hgv]
      group
    rw [h1]
    refine hP _ (hM.valid_conjE hgv hy) ⟨_, hn, ?_⟩
    rw [hnc, hjc, ← hgc, hgi l hl, cjK_codeE]

theorem cls_sound {ι : E → Gp} (hM : Model ι) {T G GI nG g R M B Mc v : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (hgiv : ∀ l < nG, validK (f20 GI l) = true)
    (hT : ∀ i < 28800, tPt T G nG 28800 i = true)
    (h : clsOK G GI nG g R M B Mc v = true) (hMM : M * Mc = 28800) :
    validE (decE g) = true ∧
    (∀ x, validE x = true →
      ((∃ c, validE c = true ∧ conjE c (decE g) = x) ↔ x ∈ decL (fun j => oCode (f96 R j)) M)) ∧
    (decL (fun j => oCode (f96 R j)) M).Nodup ∧
    (∀ b, validE b = true → (mulE b (decE g) = mulE (decE g) b ↔ b ∈ decL (f20 B) Mc)) ∧
    (decL (f20 B) Mc).Nodup ∧
    validE (decE v) = true ∧ conjE (decE v) (decE g) = invE (decE g) := by
  obtain ⟨hgen, hgk, hM0, hor, hce, hvk, hinv⟩ := clsOK_spec h
  have hgi := gi_eq hM gE hg hgiv fun l hl => (hgen l hl).2
  set gx := decE g with hgxd
  have hgx : validE gx = true := valid_decE hgk
  have hgc : codeE gx = g := codeE_decE (validK_lt hgk)
  rw [← hgc] at hor hce
  have hos := orb_sound hM gE hg hgi hgx hor
  have hoc := orb_closed hM gE hg hgi hT hor
  set Lo := decL (fun j => oCode (f96 R j)) M with hLo
  have hlt : ∀ j < M, oCode (f96 R j) < 781250 := by
    intro j hj
    obtain ⟨x, -, hx, -⟩ := hos j hj
    rw [← hx]
    exact codeE_lt x
  have hmono : ∀ i j, i < j → j < M → oCode (f96 R i) < oCode (f96 R j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := (oPt_spec (hor j (by omega))).1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih h' (by omega)).trans hs
      · exact hs
  have hLond : Lo.Nodup := decL_nodup hlt hmono
  have hgxin : ∃ j < M, oCode (f96 R j) = codeE gx := by
    obtain ⟨x, hx, hxc, c, hc, hxe⟩ := hos 0 hM0
    have hcx : conjE (invE c) x = gx := by
      apply hM.inj _ _ (hM.valid_conjE (hM.valid_inv _ hc) hx) hgx
      rw [hM.map_conjE (hM.valid_inv _ hc) hx, hM.map_inv _ hc, hxe]
      group
    rw [← hcx]
    exact hoc _ (hM.valid_inv _ hc) x hx ⟨0, hM0, hxc.symm⟩
  have hmemLo : ∀ x, validE x = true → (x ∈ Lo ↔ ∃ j < M, oCode (f96 R j) = codeE x) := by
    intro x hx
    rw [hLo, mem_decL]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, (codeE_decE (hlt j hj)).symm⟩
    · rintro ⟨j, hj, hjc⟩
      exact ⟨j, hj, by rw [hjc, decE_codeE]⟩
  have hVo : V Lo := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := mem_decL.1 hy
    obtain ⟨x, hx, hxc, -⟩ := hos j hj
    rw [← hxc, decE_codeE]
    exact hx
  have horb : ∀ x, validE x = true → ((∃ c, validE c = true ∧ conjE c gx = x) ↔ x ∈ Lo) := by
    intro x hx
    rw [hmemLo x hx]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hoc c hc gx hgx hgxin
    · rintro ⟨j, hj, hjc⟩
      obtain ⟨y, hy, hyc, c, hc, hye⟩ := hos j hj
      have : y = x := codeE_injective (hyc.trans hjc)
      subst this
      refine ⟨c, hc, hM.inj _ _ (hM.valid_conjE hc hgx) hy ?_⟩
      rw [hM.map_conjE hc hgx, hye]
  set Lc := decL (f20 B) Mc with hLc
  have hcs := fun k hk => cPt_spec (hce k hk)
  have hclt : ∀ k < Mc, f20 B k < 781250 := fun k hk => validK_lt (hcs k hk).1
  have hcmono : ∀ i j, i < j → j < Mc → f20 B i < f20 B j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := (hcs j (by omega)).2.1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih h' (by omega)).trans hs
      · exact hs
  have hLcnd : Lc.Nodup := decL_nodup hclt hcmono
  have hVc : V Lc := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_decL.1 hy
    exact valid_decE (hcs k hk).1
  have hcomm : ∀ y ∈ Lc, mulE y gx = mulE gx y := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_decL.1 hy
    apply codeE_injective
    rw [codeE_mulE, codeE_mulE, codeE_decE (hclt k hk), (hcs k hk).2.2]
  set K := vSub hM with hK
  have hKc : Nat.card K = 28800 := card_vSub hM gE hg hT
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKc]; norm_num)
  set X0 : K := ⟨ι gx, gx, hgx, rfl⟩ with hX0
  have hos2 := CFSG.GroupTheory.ncard_orbit_conjAct_mul_card_centralizer K X0
  have hOrb : Subtype.val '' MulAction.orbit (ConjAct K) X0 = S ι Lo := by
    ext y
    rw [mem_S]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.1 hw
      obtain ⟨c, hc, hce⟩ := (ConjAct.ofConjAct a).2
      refine ⟨conjE c gx, (horb _ (hM.valid_conjE hc hgx)).1 ⟨c, hc, rfl⟩, ?_⟩
      rw [hM.map_conjE hc hgx, ← ConjAct.toConjAct_ofConjAct a, ConjAct.toConjAct_smul]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hce]
      rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (horb x (hVo x hx)).2 hx
      refine ⟨ConjAct.toConjAct (⟨ι c, c, hc, rfl⟩ : K) • X0, MulAction.mem_orbit _ _, ?_⟩
      rw [ConjAct.toConjAct_smul, hM.map_conjE hc hgx]
      rfl
  have hOrbc : (MulAction.orbit (ConjAct K) X0).ncard = M := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, hOrb, ← Nat.card_coe_set_eq,
      natCard_S hM hVo hLond, hLo, decL, List.length_map, List.length_range]
  have hCc : Nat.card (Subgroup.centralizer ({X0} : Set K)) = Mc := by
    rw [hOrbc, hKc] at hos2
    exact Nat.eq_of_mul_eq_mul_left hM0 (hos2.trans hMM.symm)
  have hsubC : S ι Lc ⊆ Subtype.val '' (Subgroup.centralizer ({X0} : Set K) : Set K) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := mem_S.1 hw
    refine ⟨⟨ι y, y, hVc y hy, rfl⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hX0]
    rw [← hM.map_mul _ _ hgx (hVc y hy), ← hM.map_mul _ _ (hVc y hy) hgx, hcomm y hy]
  have hfin : (Subtype.val '' (Subgroup.centralizer ({X0} : Set K) : Set K)).Finite :=
    Set.Finite.image _ (Set.toFinite _)
  have hSeq : S ι Lc = Subtype.val '' (Subgroup.centralizer ({X0} : Set K) : Set K) := by
    refine Set.eq_of_subset_of_ncard_le hsubC ?_ hfin
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hCc, ← Nat.card_coe_set_eq, natCard_S hM hVc hLcnd, hLc, decL,
      List.length_map, List.length_range]
  have hcen : ∀ b, validE b = true → (mulE b gx = mulE gx b ↔ b ∈ Lc) := by
    intro b hb
    constructor
    · intro hbc
      have : ι b ∈ S ι Lc := by
        rw [hSeq]
        refine ⟨⟨ι b, b, hb, rfl⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hX0]
        rw [← hM.map_mul _ _ hgx hb, ← hM.map_mul _ _ hb hgx, hbc]
      obtain ⟨y, hy, hye⟩ := mem_S.1 this
      rwa [← hM.inj _ _ (hVc y hy) hb hye]
    · exact hcomm b
  have hv : validE (decE v) = true := valid_decE hvk
  have hvc : codeE (decE v) = v := codeE_decE (validK_lt hvk)
  have hiv : conjE (decE v) gx = invE gx := by
    apply codeE_injective
    rw [codeE_invE, ← cjK_codeE, codeE_invE, hvc, hgc, hinv]
  exact ⟨hgx, horb, hLond, hcen, hLcnd, hv, hiv⟩

end CFSG.KC.FiveStdK

end
