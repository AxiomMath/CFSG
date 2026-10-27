module

public import Certificates.Data.Kernel.ChengHeldPropsK
public import CFSG.Certificates.Kernel.ChengHeldS2Bind
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.KC.ChengHeldS2

variable {n w : ℕ} {gens : Array Tab} {E : Enum} {p : ℕ → Equiv.Perm (Fin n)} {T PL G : ℕ → ℕ}
  {IXP IVP : ℕ}

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bindW_parts (h : bindW n w T PL IXP IVP = true) {a : ℕ} (ha : a < n) :
    pg w (mask w) IXP a < n ∧ pg w (mask w) (T (pg w (mask w) IXP a)) 0 = a ∧
      iW n w IVP a < n ∧ mW n w T IXP a (iW n w IVP a) = 0 ∧ parOf PL a < n := by
  have h1 := allN_spec h a ha
  simp only [bAnd_iff, Nat.blt_eq] at h1
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  exact ⟨a1, Nat.eq_of_beq_eq_true a2, a3, Nat.eq_of_beq_eq_true a4, a5⟩

structure Bound (M : RegModel) (n w : ℕ) (T PL G : ℕ → ℕ) (IXP IVP : ℕ) : Prop where
  N_eq : M.N = n
  m_eq : ∀ a b, M.m a b = mW n w T IXP a b
  inv_eq : ∀ a, M.inv[a]! = iW n w IVP a
  g_eq : ∀ j, M.g j = gW w G j
  tree : TreeSpec M
  order_eq : ∀ i, M.order[i]! = oW n w T i
  parent_eq : ∀ i, M.parent[i]! = pW n w T PL i
  label_eq : ∀ i, M.label[i]! = lW n PL i

theorem bound_of (hd : RegData n gens E p) (hgs : gens.size = 7)
    (hE : E = penumRec n w n T PL) (hG : GensOK n w 7 G gens)
    (hb : bindW n w T PL IXP IVP = true) : Bound (mkRegGen n gens E) n w T PL G IXP IVP := by
  set M := mkRegGen n gens E with hM
  have hn : 0 < n := hd.pos
  have hN : M.N = n := rfl
  have hm : ∀ a b, M.m a b = mW n w T IXP a b := fun a b =>
    m_eq_mK hd hE (IX := fun a => pg w (mask w) IXP a)
      (fun a ha => ⟨(bindW_parts hb ha).1, (bindW_parts hb ha).2.1⟩) a b
  have hT : TreeSpec M := hd.tree hgs
  refine ⟨hN, hm, fun a => ?_, fun j => ?_, hT, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [inv_eq hd (INV := fun a => pg w (mask w) IVP a) (fun a ha => ?_) a]
    · unfold iW
      by_cases ha : a < n
      · rw [if_pos ha]
      · rw [if_neg ha]
    · have h := bindW_parts hb ha
      have e : iW n w IVP a = pg w (mask w) IVP a := by unfold iW; rw [if_pos ha]
      rw [← e]
      exact ⟨h.2.2.1, by rw [hm]; exact h.2.2.2.1⟩
  · change (gens.map fun t => t[0]!)[j]! = gW w G j
    unfold gW
    by_cases hj : j < 7
    · rw [if_pos hj, getElem!_pos _ _ (by simpa [hgs] using hj), Array.getElem_map,
        ← getElem!_pos gens j (by rw [hgs]; exact hj), (hG.2 j hj).1, unpack_get' hn]
    · rw [if_neg hj, getElem!_neg _ _ (by simpa [hgs] using hj)]
      rfl
  · unfold oW
    by_cases hi : i < n
    · change (E.tabs.map fun t => t[0]!)[i]! = _
      rw [if_pos hi, hd.order_get hi, tabs_get hE hi, unpack_get' hn]
    · rw [if_neg hi, getElem!_neg _ _ (by rw [hT.size_order]; exact hi)]
      rfl
  · change (E.par.map fun q => (E.tabs[q]!)[0]!)[i]! = _
    rw [hd.parent_get]
    unfold pW
    by_cases hi : i < n
    · have hp : E.par[i]! = parOf PL i := by
        subst hE
        rw [penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
      have hpl := (bindW_parts hb hi).2.2.2.2
      rw [if_pos hi, hp, tabs_get hE hpl, unpack_get' hn]
    · have hp : E.par[i]! = 0 := by
        subst hE
        rw [penumRec_eq, getElem!_neg _ _ (by simpa using hi)]
        rfl
      rw [if_neg hi, hp, hd.tab_zero_zero]
  · change E.lab[i]! = _
    unfold lW
    by_cases hi : i < n
    · subst hE
      rw [if_pos hi, penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
    · subst hE
      rw [if_neg hi, penumRec_eq, getElem!_neg _ _ (by simpa using hi)]
      rfl

variable {M : RegModel}

theorem autMap_of (hB : Bound M n w T PL G IXP IVP) (hn : 0 < n) {img : Array ℕ} {im : ℕ → ℕ}
    (himg : ∀ j < 7, img[j]! = im j) {P : ℕ}
    (h : autRecW n w (mW n w T IXP) T PL im P = true) :
    ∀ x, (M.autMap img)[x]! = aW n w P x := by
  unfold autRecW at h
  rw [bAnd_iff] at h
  have h0 : aW n w P 0 = 0 := Nat.eq_of_beq_eq_true h.1
  have hr : ∀ i, 0 < i → i < n → aW n w P (oW n w T i) =
      mW n w T IXP (im (lW n PL i)) (aW n w P (pW n w T PL i)) := by
    intro i hi0 hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact Nat.eq_of_beq_eq_true (allN_spec h.2 j (by omega))
  intro x
  rw [autMap_get hB.tree (by rw [hB.N_eq]; exact hn) img (f := aW n w P) h0 (fun i hi0 hi => ?_) x]
  · unfold aW
    by_cases hx : x < n
    · rw [hB.N_eq, if_pos hx, if_pos hx]
    · rw [hB.N_eq, if_neg hx, if_neg hx]
  · obtain ⟨-, -, -, hl, -⟩ := hB.tree.step i hi0 hi
    have hi' : i < n := by rw [← hB.N_eq]; exact hi
    rw [hB.order_eq, hB.parent_eq, hB.m_eq, himg _ hl, hB.label_eq]
    exact hr i hi0 hi'

theorem evalT_eq (hB : Bound M n w T PL G IXP IVP) :
    ∀ t : Tm, M.evalT t = evalK (mW n w T IXP) (iW n w IVP) (gW w G) t := by
  intro t
  induction t with
  | var i => exact hB.g_eq i
  | one => rfl
  | mul a b iha ihb => simp only [RegModel.evalT, evalK, iha, ihb, hB.m_eq]
  | inv a iha => simp only [RegModel.evalT, evalK, iha, hB.inv_eq]

theorem tabImgs_eq (hB : Bound M n w T PL G IXP IVP) (α k : ℕ) {j : ℕ} (hj : j < 7) :
    (M.tabImgs α k)[j]! = imgL (mW n w T IXP) (iW n w IVP) (gW w G)
      (if α = 2 then act2Rels k else actRels α k) j := by
  unfold RegModel.tabImgs imgL
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map, Array.getElem_range]
  cases (if α = 2 then act2Rels k else actRels α k).find? (fun e => e.1 == j) with
  | none => rfl
  | some e => exact evalT_eq hB e.2

theorem gImgs_eq (hB : Bound M n w T PL G IXP IVP) (α : ℕ) {j : ℕ} (hj : j < 7) :
    (M.gImgs α)[j]! = imgL (mW n w T IXP) (iW n w IVP) (gW w G) (gRels α) j := by
  unfold RegModel.gImgs imgL
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map, Array.getElem_range]
  cases (gRels α).find? (fun e => e.1 == j) with
  | none => rfl
  | some e => exact evalT_eq hB e.2

theorem mW_row {x y : ℕ} (hx : x < n) (hy : y < n) :
    mW n w T IXP x y = pg w (mask w) (T (pg w (mask w) IXP x)) y := by
  have hn : 0 < n := by omega
  have h1 : x * n + y < n * n := by nlinarith
  have e1 : (x * n + y) / n = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy, Nat.zero_add]
  have e2 : (x * n + y) % n = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  unfold mW
  rw [if_pos h1, e1, e2]

theorem ltW_spec {P : ℕ} (h : ltW n w P = true) {x : ℕ} (hx : x < n) : aW n w P x < n :=
  Nat.blt_eq.mp (allN_spec h x hx)

theorem isHom_of (hB : Bound M n w T PL G IXP IVP) {a : Array ℕ} {P : ℕ} (ha : a.size = n)
    (hP : ∀ x, a[x]! = aW n w P x) (hlt : ltW n w P = true) (hh : homW n w T IXP P = true) :
    M.isHom a = true := by
  unfold RegModel.isHom
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨by rw [ha, hB.N_eq], fun x hx => ?_⟩
  rw [List.all_eq_true]
  intro y hy
  rw [List.mem_range, hB.N_eq] at hx hy
  rw [beq_iff_eq, hB.m_eq, hB.m_eq, hP, hP, hP, mW_row hx hy,
    mW_row (ltW_spec hlt hx) (ltW_spec hlt hy)]
  have h1 := allN_spec hh x hx
  rw [strictB_eq, strictB_eq] at h1
  exact Nat.eq_of_beq_eq_true (allN_spec h1 y hy)

theorem isInvolAut_of (hB : Bound M n w T PL G IXP IVP) {a : Array ℕ} {P : ℕ} (ha : a.size = n)
    (hP : ∀ x, a[x]! = aW n w P x) (hlt : ltW n w P = true) (hh : homW n w T IXP P = true)
    (hi : invoW n w P = true) : M.isInvolAut a = true := by
  have hhom := isHom_of hB ha hP hlt hh
  unfold RegModel.isHom at hhom
  rw [Bool.and_eq_true] at hhom
  unfold RegModel.isInvolAut
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hhom.1, ?_⟩, hhom.2⟩
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_range, hB.N_eq] at hx
  rw [beq_iff_eq, hP, hP]
  exact Nat.eq_of_beq_eq_true (allN_spec hi x hx)

theorem ord3_parts {P x0 : ℕ} (h : ord3W n w P x0 = true) :
    x0 < n ∧ aW n w P x0 ≠ x0 ∧ ∀ x < n, aW n w P (aW n w P (aW n w P x)) = x := by
  unfold ord3W at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, fun e => ?_, fun x hx => Nat.eq_of_beq_eq_true (allN_spec h3 x hx)⟩
  rw [e, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem isBij_of (hB : Bound M n w T PL G IXP IVP) {a : Array ℕ} {P x0 : ℕ}
    (hP : ∀ x, a[x]! = aW n w P x) (hlt : ltW n w P = true) (h3 : ord3W n w P x0 = true) :
    M.isBij a = true := by
  obtain ⟨-, -, hc⟩ := ord3_parts h3
  have hl : ∀ y ∈ List.range M.N, a[y]! < (Array.replicate M.N false).size := by
    intro y hy
    rw [List.mem_range, hB.N_eq] at hy
    rw [hP, Array.size_replicate, hB.N_eq]
    exact ltW_spec hlt hy
  obtain ⟨h1, h2⟩ := foldl_set_true (fun y => a[y]!) _ _ hl
  unfold RegModel.isBij
  rw [Array.all_eq_true]
  simp only [Array.size_replicate] at h1
  intro i hi
  rw [h1, hB.N_eq] at hi
  rw [id, ← getElem!_pos, h2]
  refine Or.inr ⟨aW n w P (aW n w P i), ?_, ?_⟩
  · rw [List.mem_range, hB.N_eq]
    exact ltW_spec hlt (ltW_spec hlt hi)
  · rw [hP]
    exact hc i hi

theorem permOrd_of (hB : Bound M n w T PL G IXP IVP) {a : Array ℕ} {P x0 : ℕ}
    (hP : ∀ x, a[x]! = aW n w P x) (h3 : ord3W n w P x0 = true) : M.permOrd a = 3 := by
  obtain ⟨hx0, hm0, hc⟩ := ord3_parts h3
  have hx0' : x0 < M.N := by rw [hB.N_eq]; exact hx0
  have test : ∀ k, (k > 0 && (List.range M.N).all fun x =>
      (List.range k).foldl (fun y _ => a[y]!) x == x) = true ↔
      0 < k ∧ ∀ x < M.N, (fun y => a[y]!)^[k] x = x := by
    intro k
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
      foldl_range_iterate]
  have p0 : ¬ (0 > 0 && (List.range M.N).all fun x =>
      (List.range 0).foldl (fun y _ => a[y]!) x == x) = true := by
    rw [test]
    omega
  have p1 : ¬ (1 > 0 && (List.range M.N).all fun x =>
      (List.range 1).foldl (fun y _ => a[y]!) x == x) = true := by
    rw [test]
    rintro ⟨-, h⟩
    have := h x0 hx0'
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hP] at this
    exact hm0 this
  have p2 : ¬ (2 > 0 && (List.range M.N).all fun x =>
      (List.range 2).foldl (fun y _ => a[y]!) x == x) = true := by
    rw [test]
    rintro ⟨-, h⟩
    have := h x0 hx0'
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hP] at this
    apply hm0
    have e := hc x0 hx0
    rw [this] at e
    exact e
  have p3 : (3 > 0 && (List.range M.N).all fun x =>
      (List.range 3).foldl (fun y _ => a[y]!) x == x) = true := by
    rw [test]
    refine ⟨by norm_num, fun x hx => ?_⟩
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hP]
    exact hc x (by rw [← hB.N_eq]; exact hx)
  unfold RegModel.permOrd
  have key : (List.range 13).find? (fun k => k > 0 && (List.range M.N).all fun x =>
      (List.range k).foldl (fun y _ => a[y]!) x == x) = some 3 := by
    rw [List.find?_range_eq_some]
    refine ⟨p3, by simp, fun j hj => ?_⟩
    interval_cases j
    · simpa using p0
    · simpa using p1
    · simpa using p2
  rw [key]
  rfl

end CFSG.KC.ChengHeldP

end
