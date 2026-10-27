module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelMk
public import CFSG.Sporadic.Recognition.PresentedWords

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.OddStandard.ChengHeldData
open CFSG.CosetTable CFSG.Sporadic.Recognition.PresentedWords

theorem regGens_ok :
    ∀ α < 3, ∀ j < 7, ((regGens α)[j]!).size = regN α ∧ ((regGens α)[j]!)[0]! < regN α := by
  decide +kernel

theorem regGens_size : ∀ α < 3, (regGens α).size = 7 := by decide +kernel

theorem regN_pos (α : ℕ) : 0 < regN α := by
  unfold regN
  split <;> norm_num

theorem chPres_parts (h : chPresOK = true) :
    pres4OK = true ∧ pres2OK = true ∧
      ∀ α, α ≤ 2 → regRelOK α = true ∧ regOrderOK α = true := by
  simp only [chPresOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, fun α hα => ?_⟩
  interval_cases α
  · exact ⟨h3, h6⟩
  · exact ⟨h4, h7⟩
  · exact ⟨h5, h8⟩

theorem exists_tabRep {n : ℕ} {t s : Tab} (hts : t.size = n) (hss : s.size = n)
    (hc : comp n s t = idTab n) (h0 : n = 0 ∨ t[0]! < n) :
    ∃ g : Equiv.Perm (Fin n), TabRep t g := by
  have hcg : ∀ i : Fin n, s[t[i.val]!]! = i.val := fun i => by
    have := congrArg (fun u : Tab => u[i.val]!) hc
    simpa [TabRep.comp_getElem!, TabRep.idTab_getElem!] using this
  have hlt : ∀ i : Fin n, t[i.val]! < n := by
    intro i
    by_contra hge
    have hge := not_lt.1 hge
    have h1 : s[t[i.val]!]! = 0 := by
      rw [getElem!_neg s _ (by omega)]
      rfl
    have h2 := hcg i
    rw [h1] at h2
    have hi0 : i.val = 0 := h2.symm
    rcases h0 with h0 | h0
    · exact absurd i.2 (by omega)
    · rw [hi0] at hge
      omega
  have hinj : Function.Injective (fun i : Fin n => (⟨t[i.val]!, hlt i⟩ : Fin n)) := by
    intro i j hij
    have h1 : t[i.val]! = t[j.val]! := by simpa using congrArg Fin.val hij
    exact Fin.ext (by rw [← hcg i, ← hcg j, h1])
  refine ⟨Equiv.ofBijective _ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩, hts, fun i => ?_⟩
  rfl

noncomputable def permOf (α j : ℕ) : Equiv.Perm (Fin (regN α)) :=
  open Classical in
  if h : ∃ g : Equiv.Perm (Fin (regN α)), TabRep (regGens α)[j]! g then h.choose else 1

theorem regRel_parts {α : ℕ} (hr : regRelOK α = true) :
    invsOK (regN α) (regGens α) ((regGens α).map (invTab (regN α))) = true ∧
      ∀ w ∈ regRelWords α, wordPermTab (regN α) (regGens α) ((regGens α).map (invTab (regN α))) w =
        idTab (regN α) := by
  simp only [regRelOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hr
  exact ⟨hr.1.2, hr.2⟩

theorem permOf_rep {α : ℕ} (hα : α ≤ 2) (hr : regRelOK α = true) {j : ℕ} (hj : j < 7) :
    TabRep (regGens α)[j]! (permOf α j) := by
  have hex : ∃ g : Equiv.Perm (Fin (regN α)), TabRep (regGens α)[j]! g := by
    have hinv := (regRel_parts hr).1
    have hα3 : α < 3 := by omega
    obtain ⟨hs, h0⟩ := regGens_ok α hα3 j hj
    have hsz := regGens_size α hα3
    simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Array.size_map] at hinv
    obtain ⟨-, hall⟩ := hinv
    obtain ⟨h1, h2⟩ := hall j (by omega)
    have hgi : ((regGens α).map (invTab (regN α)))[j]! = invTab (regN α) ((regGens α)[j]!) := by
      rw [getElem!_pos _ _ (by simp; omega), Array.getElem_map, getElem!_pos _ _ (by omega)]
    exact exists_tabRep hs h1 h2 (Or.inr h0)
  unfold permOf
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

theorem permOf_inv_rep {α : ℕ} (hα : α ≤ 2) (hr : regRelOK α = true) {j : ℕ} (hj : j < 7) :
    TabRep (((regGens α).map (invTab (regN α)))[j]!) (permOf α j)⁻¹ := by
  have hinv := (regRel_parts hr).1
  have hsz := regGens_size α (by omega)
  have := invsOK_spec hinv (k := j) (by omega) (permOf_rep hα hr hj)
  simpa using this

theorem wordPermTab_rep {α : ℕ} (hα : α ≤ 2) (hr : regRelOK α = true) (w : List (Fin 7 × Bool)) :
    ∀ (acc : Tab) (a : Equiv.Perm (Fin (regN α))), TabRep acc a →
      TabRep (w.foldl (fun acc l => comp (regN α) acc (if l.2 then (regGens α)[l.1.val]!
        else (((regGens α).map (invTab (regN α)))[l.1.val]!))) acc)
        (a * wprod (fun j : Fin 7 => permOf α j.val) w) := by
  induction w with
  | nil =>
    intro acc a ha
    simpa using ha
  | cons l w ih =>
    intro acc a ha
    rw [List.foldl_cons, wprod_cons, ← mul_assoc]
    refine ih _ _ (ha.comp ?_)
    by_cases hb : l.2
    · simpa [hb] using permOf_rep hα hr l.1.2
    · simpa [hb] using permOf_inv_rep hα hr l.1.2

theorem wprod_permOf {α : ℕ} (hα : α ≤ 2) (hr : regRelOK α = true) :
    ∀ w ∈ regRelWords α, wprod (fun j : Fin 7 => permOf α j.val) w = 1 := by
  intro w hw
  have h1 := (regRel_parts hr).2 w hw
  have h2 := wordPermTab_rep hα hr w _ 1 TabRep.idTab
  rw [wordPermTab] at h1
  rw [h1, one_mul] at h2
  exact h2.perm_eq TabRep.idTab

theorem length_eraseDups_le_and (l : List ℕ) :
    l.eraseDups.length ≤ l.length ∧ (l.eraseDups.length = l.length → l.Nodup) := by
  induction' hn : l.length using Nat.strong_induction_on with n ih generalizing l
  match l, hn with
  | [], _ => simp
  | a :: as, hn =>
    have hf : (as.filter fun b => !b == a).length ≤ as.length := List.length_filter_le _ _
    simp only [List.length_cons] at hn
    obtain ⟨h1, h2⟩ := ih (as.filter fun b => !b == a).length (by omega)
      (as.filter fun b => !b == a) rfl
    rw [List.eraseDups_cons]
    refine ⟨by simp only [List.length_cons]; omega, fun h => ?_⟩
    simp only [List.length_cons] at h
    have hl : (as.filter fun b => !b == a).length = as.length := by omega
    rw [List.length_filter_eq_length_iff] at hl
    have hfe : (as.filter fun b => !b == a) = as := List.filter_eq_self.2 hl
    rw [hfe] at h2 h
    have hnd := h2 (by omega)
    refine List.nodup_cons.2 ⟨fun ha => ?_, hnd⟩
    have := hl a ha
    simp at this

theorem nodup_of_length_eraseDups {l : List ℕ} (h : l.eraseDups.length = l.length) : l.Nodup :=
  (length_eraseDups_le_and l).2 h

theorem regData {α : ℕ} (hα : α ≤ 2) (hP : chPresOK = true) :
    RegData (regN α) (regGens α) (regEnum α) (permOf α) := by
  obtain ⟨-, -, hpart⟩ := chPres_parts hP
  obtain ⟨hr, ho⟩ := hpart α hα
  have hsz := regGens_size α (by omega)
  simp only [regOrderOK, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨⟨hen, hs⟩, hd⟩ := ho
  refine ⟨regN_pos α, fun j hj => permOf_rep hα hr (hsz ▸ hj), hen, hs, fun i j hi hj hij => ?_⟩
  have hnd := nodup_of_length_eraseDups (l := ((regEnum α).tabs.map fun t => t[0]!).toList)
    (by simpa [hs] using hd)
  rw [List.nodup_iff_injective_getElem] at hnd
  have := @hnd ⟨i, by simpa [hs] using hi⟩ ⟨j, by simpa [hs] using hj⟩ (by
    simp only [Array.getElem_toList, Array.getElem_map]
    simpa [getElem!_pos, hs, hi, hj] using hij)
  simpa using this

theorem pres_card (hP : chPresOK = true) {α : ℕ} (hα : α ≤ 2) :
    Finite (PG 7 (regRelWords α)) ∧ Nat.card (PG 7 (regRelWords α)) ≤ regN α := by
  obtain ⟨h4, h2, -⟩ := chPres_parts hP
  simp only [pres4OK, Bool.and_eq_true] at h4
  interval_cases α
  · simpa [regRelWords, regN] using card_le_of_subsetCheckC_nil (relWords4 0) h4.1
  · simpa [regRelWords, regN] using card_le_of_subsetCheckC_nil (relWords4 1) h4.2
  · simpa [regRelWords, regN] using card_le_of_subsetCheckC_nil relWords2 h2

@[expose] def Rep.ofMulEquiv {M : RegModel} {K H : Type} [Group K] [Group H] (R : Rep M K)
    (e : H ≃* K) : Rep M H where
  pt h := R.pt (e h)
  pt_lt h := R.pt_lt _
  pt_inj := R.pt_inj.comp e.injective
  pt_surj a ha := by
    obtain ⟨k, hk⟩ := R.pt_surj a ha
    exact ⟨e.symm k, by simpa using hk⟩
  pt_mul a b := by simp only [map_mul, R.pt_mul]
  pt_one := by simp only [map_one, R.pt_one]
  pt_inv a := by simp only [map_inv, R.pt_inv]

theorem Rep.ofMulEquiv_pt {M : RegModel} {K H : Type} [Group K] [Group H] (R : Rep M K)
    (e : H ≃* K) (h : H) : (R.ofMulEquiv e).pt h = R.pt (e h) := rfl

theorem range_pgHom' {m : ℕ} {ws : List (List (Fin m × Bool))} {G : Type*} [Group G]
    (x : Fin m → G) (hx : ∀ w ∈ ws, wprod x w = 1) :
    (pgHom x hx).range = Subgroup.closure (Set.range x) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext i
  simp [pgHom_of]

abbrev modelS (α : ℕ) : Type := ↥(permGroup (regN α) (permOf α) (regGens α).size)

theorem exists_mulEquiv {α : ℕ} (hα : α ≤ 2) (hP : chPresOK = true) {H : Type} [Group H]
    (x : Fin 7 → H) (hrel : ∀ w ∈ regRelWords α, wprod x w = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) (hcard : Nat.card H = regN α) :
    ∃ e : H ≃* modelS α, ∀ j : Fin 7,
      ((e (x j) : modelS α) : Equiv.Perm (Fin (regN α))) = permOf α j.val := by
  obtain ⟨-, -, hpart⟩ := chPres_parts hP
  obtain ⟨hr, -⟩ := hpart α hα
  have hd := regData hα hP
  have hsz := regGens_size α (by omega)
  obtain ⟨hfin, hpres⟩ := pres_card hP hα
  let K := permGroup (regN α) (permOf α) (regGens α).size
  let q : Fin 7 → ↥K := fun j => ⟨permOf α j.val, RegData.gen_mem _ _ (by rw [hsz]; exact j.2)⟩
  have hqrel : ∀ w ∈ regRelWords α, wprod q w = 1 := by
    intro w hw
    apply Subtype.ext
    have h1 := wprod_permOf hα hr w hw
    have h2 := map_wprod K.subtype q w
    simp only [Subgroup.coe_subtype] at h2
    rw [h2]
    exact h1
  have hqgen : Subgroup.closure (Set.range q) = ⊤ := by
    have key : Subgroup.closure ((Subtype.val : ↥K → Equiv.Perm (Fin (regN α))) ⁻¹'
        {a : Equiv.Perm (Fin (regN α)) | ∃ j < (regGens α).size, a = permOf α j}) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    refine eq_top_iff.2 ?_
    rw [← key]
    refine Subgroup.closure_mono ?_
    rintro g ⟨j, hj, hg⟩
    exact ⟨⟨j, by rw [← hsz]; exact hj⟩, Subtype.ext hg.symm⟩
  have hcardK : Nat.card K = regN α := hd.card_group
  have hφ : Function.Bijective (pgHom x hrel) := by
    have hs : Function.Surjective (pgHom x hrel) := by
      rw [← MonoidHom.range_eq_top, range_pgHom', hgen]
    exact hs.bijective_of_nat_card_le (by rw [hcard]; exact hpres)
  have hψ : Function.Bijective (pgHom q hqrel) := by
    have hs : Function.Surjective (pgHom q hqrel) := by
      rw [← MonoidHom.range_eq_top, range_pgHom', hqgen]
    exact hs.bijective_of_nat_card_le (by rw [hcardK]; exact hpres)
  let e : H ≃* ↥K := (MulEquiv.ofBijective (pgHom x hrel) hφ).symm.trans
    (MulEquiv.ofBijective (pgHom q hqrel) hψ)
  refine ⟨e, fun j => ?_⟩
  have h1 : (MulEquiv.ofBijective (pgHom x hrel) hφ) (PresentedGroup.of j) = x j :=
    pgHom_of x hrel j
  have he : e (x j) = q j := by
    simp only [e, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
    exact pgHom_of q hqrel j
  rw [he]

theorem exists_rep {α : ℕ} (hα : α ≤ 2) (hP : chPresOK = true) {H : Type} [Group H]
    (x : Fin 7 → H) (hrel : ∀ w ∈ regRelWords α, wprod x w = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) (hcard : Nat.card H = regN α) :
    ∃ R : Rep (mkReg α) H, ∀ j : Fin 7, R.pt (x j) = (mkReg α).gpt[j.val]! := by
  obtain ⟨e, he⟩ := exists_mulEquiv hα hP x hrel hgen hcard
  obtain ⟨-, -, hpart⟩ := chPres_parts hP
  obtain ⟨hr, -⟩ := hpart α hα
  have hd := regData hα hP
  have hsz := regGens_size α (by omega)
  let rep0 : Rep (mkReg α) (modelS α) := hd.rep
  refine ⟨rep0.ofMulEquiv e, fun j => ?_⟩
  rw [Rep.ofMulEquiv_pt]
  have hj : j.val < (regGens α).size := by rw [hsz]; exact j.2
  have hg : ((regGens α).map fun g => g[0]!)[j.val]! = ((regGens α)[j.val]!)[0]! := by
    rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map, getElem!_pos (regGens α) j.val hj]
  show hd.ptOf (e (x j)) = _
  have h0 := (permOf_rep hα hr (j := j.val) j.2).apply ⟨0, hd.pos⟩
  show ((e (x j) : modelS α) : Equiv.Perm (Fin (regN α))) ⟨0, hd.pos⟩ =
    ((regGens α).map fun g => g[0]!)[j.val]!
  rw [he j, hg]
  exact h0.symm

theorem treeSpec_mkReg {α : ℕ} (hα : α ≤ 2) (hP : chPresOK = true) : TreeSpec (mkReg α) :=
  (regData hα hP).tree (regGens_size α (by omega))

end CFSG.OddStandard.ChengHeld.Model

