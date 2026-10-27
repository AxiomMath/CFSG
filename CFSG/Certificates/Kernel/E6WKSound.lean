module

public import Certificates.Data.Kernel.E6WK
public import Certificates.Data.TwE6WKMatrix
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LieType.Chevalley.SignCharacterCertificates
public import CFSG.LieType.Chevalley.WeylExchange

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

theorem wkRho_getD (k : Fin TwistTag.E6.tag.rank) :
    wkRho.getD k 0 = (TwistTag.E6.perm k : ℕ) := by
  revert k
  decide

theorem wkEnt_eq {t : List ℕ} {w : WeylGroup TwistTag.E6.tag}
    (hrep : e6Certificate.Represents t w) (i k : Fin TwistTag.E6.tag.rank) :
    wkEnt (wkRows (t.map fun r => (RootTables.ofCert e6Certificate).vecs.getD r [])) i k =
      wkMatrix w i k := by
  have hi : (i : ℕ) < t.length := by rw [hrep.1]; exact i.2
  have hrs : (t.map fun r => (RootTables.ofCert e6Certificate).vecs.getD r []).getD i [] =
      List.ofFn (e6Certificate.root (t.getD i 0)) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hi]
    exact vecs_getD e6Certificate (hrep.2 i).1
  have hρ : (TwistTag.E6.perm k : ℕ) <
      (List.ofFn (e6Certificate.root (t.getD i 0))).length := by
    rw [List.length_ofFn]
    exact (TwistTag.E6.perm k).2
  unfold wkEnt wkRows
  rw [getD_range_map' _ _ (show (i : ℕ) < 6 from i.2)]
  dsimp only
  rw [getD_range_map' _ _ (show (k : ℕ) < 6 from k.2), hrs, wkRho_getD,
    List.getD_eq_getElem _ _ hρ, List.getElem_ofFn, (hrep.2 i).2]
  simp only [wkMatrix, Fin.val_inj]
  rfl

theorem dotL_ofFn_wk {f : Fin TwistTag.E6.tag.rank → ℤ} (b : List ℤ) :
    dotL (List.ofFn f) b = ∑ j : Fin TwistTag.E6.tag.rank, f j * b.getD j 0 :=
  sum_zipWith_ofFn_left f b

theorem wkTrichotomy_of_wkTuple {t : List ℕ} {w : WeylGroup TwistTag.E6.tag}
    (hrep : e6Certificate.Represents t w)
    (htup : wkTuple (RootTables.ofCert e6Certificate) t = true) :
    (∃ i, IsRoot TwistTag.E6.tag (wkMatrix w i)) ∨ wkMatrix w = 0 ∨
      ∃ R C : Fin 3 → Fin TwistTag.E6.tag.rank,
        ((wkMatrix w).submatrix R C).det ∈ ({1, -1, 2, -2} : Finset ℤ) := by
  classical
  set nl := wkRows (t.map fun r => (RootTables.ofCert e6Certificate).vecs.getD r []) with hnl
  have hent : ∀ i k : Fin TwistTag.E6.tag.rank, wkEnt nl i k = wkMatrix w i k :=
    wkEnt_eq hrep
  simp only [wkTuple, Bool.or_eq_true] at htup
  rcases htup with (hR | hZ) | hM
  ·
    left
    simp only [wkRowRoot, List.any_eq_true, List.mem_finRange, true_and,
      decide_eq_true_eq] at hR
    obtain ⟨i, hi⟩ := hR
    refine ⟨i, ?_⟩
    rw [dotL_ofFn_wk] at hi
    have hsum : ∑ j, TwistTag.E6.tag.cartan i j * wkMatrix w i j = 1 := by
      rw [← hi]
      exact Finset.sum_congr rfl fun j _ => by rw [← hent i j]; rfl
    set γ : Fin TwistTag.E6.tag.rank → ℤ :=
      permLattice TwistTag.E6.perm.symm (w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
      with hγ
    have hγr : IsRoot TwistTag.E6.tag γ :=
      (IsRoot.smul (isRoot_single _ i) w).permLattice
        (cartan_perm_symm (TwistTag.cartan_perm TwistTag.E6))
    have hγk : ∀ k, γ k = wkMatrix w i k - if i = k then 1 else 0 := by
      intro k
      simp only [hγ, permLattice, Function.comp_apply, Equiv.symm_symm, wkMatrix]
      ring
    have hpair : ∑ j, TwistTag.E6.tag.cartan i j * γ j = -1 := by
      simp only [hγk, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hsum, Tag.cartan_self]
      norm_num
    have hrow : wkMatrix w i = reflect TwistTag.E6.tag i γ := by
      unfold reflect
      rw [hpair]
      funext k
      rw [Pi.sub_apply, Pi.smul_apply, hγk, smul_eq_mul, Pi.single_apply]
      by_cases hik : i = k
      · subst hik
        simp only [if_true]
        ring
      · rw [if_neg hik, if_neg (Ne.symm hik)]
        ring
    rw [hrow]
    exact IsRoot.reflect i hγr
  ·
    right
    left
    simp only [wkZero, List.all_eq_true, List.mem_range, beq_iff_eq] at hZ
    funext i k
    rw [← hent]
    exact hZ i i.2 k k.2
  ·
    right
    right
    simp only [wkMinor, List.any_eq_true] at hM
    obtain ⟨r, hr, c, hc, hdet⟩ := hM
    have hlt : ∀ x ∈ wkTriples, x.1 < 6 ∧ x.2.1 < 6 ∧ x.2.2 < 6 := by decide
    obtain ⟨hr1, hr2, hr3⟩ := hlt r hr
    obtain ⟨hc1, hc2, hc3⟩ := hlt c hc
    refine ⟨![⟨r.1, hr1⟩, ⟨r.2.1, hr2⟩, ⟨r.2.2, hr3⟩], ![⟨c.1, hc1⟩, ⟨c.2.1, hc2⟩, ⟨c.2.2, hc3⟩],
      ?_⟩
    have hval : ((wkMatrix w).submatrix ![⟨r.1, hr1⟩, ⟨r.2.1, hr2⟩, ⟨r.2.2, hr3⟩]
        ![⟨c.1, hc1⟩, ⟨c.2.1, hc2⟩, ⟨c.2.2, hc3⟩]).det = wkDet3 nl r c := by
      rw [Matrix.det_fin_three]
      simp only [Matrix.submatrix_apply, ← hent]
      rfl
    rw [hval]
    have hmem : wkDet3 nl r c ∈ [1, -1, 2, -2] := List.contains_iff_mem.1 hdet
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hmem

end CFSG.StandardType.TwE6RootKill

namespace CFSG.KC.E6WK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.StandardType.TwE6RootKill CFSG.Blueprint.Chevalley.RootCertificate

theorem lane_encodeT : ∀ {l : List ℕ}, (∀ x ∈ l, x < 256) → ∀ k, lane (encodeT l) k = l.getD k 0
  | [], _, k => by simp [lane, encodeT]
  | a :: l, h, k => by
    have ha : a < 256 := h a List.mem_cons_self
    have hl : ∀ x ∈ l, x < 256 := fun x hx => h x (List.mem_cons_of_mem a hx)
    have he : encodeT (a :: l) = a + 256 * encodeT l := rfl
    cases k with
    | zero => simp [lane, he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    | succ k =>
      rw [List.getD_cons_succ, ← lane_encodeT hl k, lane, lane, he, pow_succ',
        ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha,
        zero_add]

theorem getD_decodeT {n q k : ℕ} (hk : k < n) : (decodeT n q).getD k 0 = lane q k :=
  getD_range_map' _ _ hk

theorem length_decodeT (n q : ℕ) : (decodeT n q).length = n := by
  simp [decodeT]

theorem decodeT_encodeT {l : List ℕ} (hl : ∀ x ∈ l, x < 256) {n : ℕ} (hn : l.length = n) :
    decodeT n (encodeT l) = l := by
  refine List.ext_getElem (by rw [length_decodeT, hn]) fun j h1 h2 => ?_
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2,
    getD_decodeT (by rw [length_decodeT] at h1; exact h1), lane_encodeT hl]

theorem decodeT_mapLanes {n : ℕ} {f : ℕ → ℕ} {q : ℕ} (hf : ∀ k < n, f (lane q k) < 256) :
    decodeT n (mapLanes n f q) = (decodeT n q).map f := by
  refine decodeT_encodeT ?_ (by rw [List.length_map, length_decodeT])
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
  have hj' : j < n := length_decodeT n q ▸ hj
  rw [← List.getD_eq_getElem _ 0 hj, getD_decodeT hj']
  exact hf j hj'

theorem lane_mapLanes {n : ℕ} {f : ℕ → ℕ} {q : ℕ} (hf : ∀ k < n, f (lane q k) < 256) {k : ℕ}
    (hk : k < n) : lane (mapLanes n f q) k = f (lane q k) := by
  have h : (decodeT n (mapLanes n f q)).getD k 0 = ((decodeT n q).map f).getD k 0 := by
    rw [decodeT_mapLanes hf]
  have hk' : k < (decodeT n q).length := by rw [length_decodeT]; exact hk
  rw [getD_decodeT hk] at h
  rw [h, List.getD_eq_getElem _ 0 (by rw [List.length_map]; exact hk'), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hk', getD_decodeT hk]

theorem getD_mem' {α : Type*} {l : List α} {k : ℕ} (d : α) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem lane_mod_pow {p j n : ℕ} (hj : j < n) : lane (p % 256 ^ n) j = lane p j := by
  unfold lane
  have h : 256 ^ n = 256 ^ j * 256 ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 256 (by omega)

theorem roots_length : e6Certificate.roots.length = 72 := by decide

theorem rank_E6 : Tag.E6.rank = 6 := rfl

section Tables

variable {vp ir rm : ℕ} (h : tabCheckWith vp ir rm = true)
include h

theorem tab_parts :
    (∀ r < 72, vp / 2 ^ (24 * r) % 2 ^ 24 = e6Certificate.roots.getD r 0) ∧
    (∀ j < 6, ∀ k < 72, irL ir j k = e6Certificate.table.getD k 0 / 256 ^ j % 256) ∧
    (∀ i : Fin 6, ∀ r < 72, (rm / 2 ^ (72 * (i : ℕ) + r) % 2 == 1) =
      rowRootAt i ((RootTables.ofCert e6Certificate).vecs.getD r [])) := by
  simp only [tabCheckWith, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.mem_finRange, true_implies] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem vecP_eq {r : ℕ} (hr : r < 72) :
    vecP vp r = (RootTables.ofCert e6Certificate).vecs.getD r [] := by
  rw [vecs_getD e6Certificate (by rw [roots_length]; exact hr)]
  refine List.ext_getElem (by
    simp only [vecP, List.length_map, List.length_range]
    exact List.length_ofFn.symm) fun m h1 h2 => ?_
  simp only [vecP, List.getElem_map, List.getElem_range, List.getElem_ofFn, RootCertificate.root,
    decodeVec]
  rw [(tab_parts h).1 r hr]

theorem irL_eq {j k : ℕ} (hj : j < 6) (hk : k < 72) :
    irL ir j k = e6Certificate.image k ⟨j, hj⟩ :=
  (tab_parts h).2.1 j hj k hk

theorem irL_lt {j k : ℕ} (hj : j < 6) (hk : k < 72) :
    irL ir j k < 72 := by
  rw [irL_eq h hj hk, ← roots_length]
  exact (image_spec e6Certificate_check (by rw [roots_length]; exact hk) ⟨j, hj⟩).1

end Tables

theorem root_single
    (j : Fin Tag.E6.rank) :
    e6Certificate.root j = Pi.single j 1 := by
  have h := ((represents_one e6Certificate_check).2 j).2
  rwa [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact j.2), List.getElem_range,
    one_smul] at h

theorem lt_of_represents {t : List ℕ} {w : WeylGroup Tag.E6}
    (hrep : e6Certificate.Represents t w) : ∀ x ∈ t, x < 72 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj6 : j < Tag.E6.rank := by rw [← hrep.1]; exact hj
  have := (hrep.2 ⟨j, hj6⟩).1
  rwa [List.getD_eq_getElem _ _ hj, roots_length] at this

theorem exists_wordPerm_spec
    {vp ir rm : ℕ} (htab : tabCheckWith vp ir rm = true) :
    ∀ word : List ℕ, (∀ i ∈ word, i < 6) → ∃ g : WeylGroup Tag.E6, ∀ k < 72,
      lane (wordPerm ir word) k < 72 ∧
        e6Certificate.root (lane (wordPerm ir word) k) = g • e6Certificate.root k
  | [], _ => by
    refine ⟨1, fun k hk => ?_⟩
    have hid : lane idPerm k = k := by
      rw [idPerm, lane_encodeT (fun x hx => by rw [List.mem_range] at hx; omega),
        List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hk), List.getElem_range]
    simp only [wordPerm, List.foldr_nil, hid, one_smul]
    exact ⟨hk, trivial⟩
  | i :: word, hw => by
    have hi : i < 6 := hw i List.mem_cons_self
    obtain ⟨g, hg⟩ := exists_wordPerm_spec htab word fun x hx => hw x (List.mem_cons_of_mem i hx)
    have hP : wordPerm ir (i :: word) = mapLanes 72 (irL ir i) (wordPerm ir word) := by
      unfold wordPerm
      rw [List.foldr_cons]
    have hf : ∀ k < 72, irL ir i (lane (wordPerm ir word) k) < 256 :=
      fun k hk => (irL_lt htab hi (hg k hk).1).trans (by norm_num)
    refine ⟨simple Tag.E6 ⟨i, hi⟩ * g, fun k hk => ?_⟩
    rw [hP, lane_mapLanes hf hk, irL_eq htab hi (hg k hk).1]
    obtain ⟨h1, h2⟩ := image_spec e6Certificate_check
      (by rw [roots_length]; exact (hg k hk).1) (⟨i, hi⟩ : Fin Tag.E6.rank)
    rw [roots_length] at h1
    refine ⟨h1, ?_⟩
    rw [h2, (hg k hk).2, mul_smul, simple_smul]

theorem exists_up {up : List ℕ}
    (hk : kCheckWith up = true) (u : WeylGroup Tag.E6)
    (hu : ∀ j : Fin Tag.E6.rank, (j : ℕ) ≠ 0 →
      0 < height (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) :
    ∃ p ∈ up, e6Certificate.Represents (decodeT 6 (p % 256 ^ 6)) u := by
  have hw : ∀ β ∈ (kCert up).simple, 0 < height (u • e6Certificate.root β) := by
    intro β hβ
    have hβ' : β ∈ [1, 2, 3, 4, 5] := hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ'
    have hβ6 : β < 6 := by omega
    have h : e6Certificate.root β = Pi.single (⟨β, hβ6⟩ : Fin Tag.E6.rank) 1 :=
      root_single ⟨β, hβ6⟩
    rw [h]
    exact hu ⟨β, hβ6⟩ (by change β ≠ 0; omega)
  have hk' : (kCert up).check e6Certificate = true := hk
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_represents_of_check e6Certificate_check hk' u hw
  obtain ⟨k, hk', rfl⟩ := StabCert3.mem_elems.1 ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk'
  exact ⟨p, hp, hrep⟩

theorem represents_mapLanes
    {vp ir rm : ℕ} (htab : tabCheckWith vp ir rm = true) {c : ℕ} {v : WeylGroup Tag.E6}
    (hrep : e6Certificate.Represents (decodeT 6 c) v) (j : Fin Tag.E6.rank) :
    e6Certificate.Represents (decodeT 6 (mapLanes 6 (irL ir j) c))
      (simple Tag.E6 j * v) := by
  have hlt := lt_of_represents hrep
  have hlane : ∀ k < 6, lane c k < 72 := fun k hk => by
    rw [← getD_decodeT hk]
    exact hlt _ (getD_mem' 0 (by rw [length_decodeT]; exact hk))
  rw [decodeT_mapLanes fun k hk => (irL_lt htab j.2 (hlane k hk)).trans (by norm_num)]
  have he : (decodeT 6 c).map (irL ir j) = e6Certificate.tupleImage j (decodeT 6 c) :=
    List.map_congr_left fun x hx => irL_eq htab j.2 (hlt x hx)
  rw [he]
  exact represents_tupleImage e6Certificate_check hrep j

theorem exists_vk
    {vp ir rm : ℕ} (htab : tabCheckWith vp ir rm = true) {vk : List ℕ}
    (hv : vCheckWith ir vk (KTree.ofSorted vk) = true) :
    ∀ ω : List (Fin Tag.E6.rank), (∀ j ∈ ω, (j : ℕ) ≠ 0) →
      ∃ c ∈ vk, e6Certificate.Represents (decodeT 6 c) ((coxeterSystem Tag.E6).wordProd ω)
  | [], _ => by
    simp only [vCheckWith, Bool.and_eq_true, List.all_eq_true] at hv
    refine ⟨_, KTree.mem_of_mem_ofSorted hv.1, ?_⟩
    rw [decodeT_encodeT (fun x hx => by rw [List.mem_range] at hx; omega) (List.length_range),
      CoxeterSystem.wordProd_nil]
    exact represents_one e6Certificate_check
  | j :: ω, hω => by
    obtain ⟨c, hc, hrep⟩ := exists_vk htab hv ω fun x hx => hω x (List.mem_cons_of_mem j hx)
    have hj : (j : ℕ) ∈ [1, 2, 3, 4, 5] := by
      have h0' := hω j List.mem_cons_self
      have h6 : (j : ℕ) < 6 := j.2
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    simp only [vCheckWith, Bool.and_eq_true, List.all_eq_true] at hv
    refine ⟨_, KTree.mem_of_mem_ofSorted (hv.2 c hc j hj), ?_⟩
    rw [CoxeterSystem.wordProd_cons]
    exact represents_mapLanes htab hrep j

theorem exists_decomp
    (w : WeylGroup Tag.E6) :
    ∃ u : WeylGroup Tag.E6, ∃ ω : List (Fin Tag.E6.rank), (∀ j ∈ ω, (j : ℕ) ≠ 0) ∧
      (∀ j : Fin Tag.E6.rank, (j : ℕ) ≠ 0 →
        0 < height (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) ∧
      w = u * (coxeterSystem Tag.E6).wordProd ω := by
  suffices key : ∀ n : ℕ, ∀ w : WeylGroup Tag.E6,
      (coxeterSystem Tag.E6).length w = n →
      ∃ u : WeylGroup Tag.E6, ∃ ω : List (Fin Tag.E6.rank), (∀ j ∈ ω, (j : ℕ) ≠ 0) ∧
        (∀ j : Fin Tag.E6.rank, (j : ℕ) ≠ 0 →
          0 < height (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) ∧
        w = u * (coxeterSystem Tag.E6).wordProd ω from key _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn
    by_cases hpos : ∀ j : Fin Tag.E6.rank, (j : ℕ) ≠ 0 →
        0 < height (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
    · exact ⟨w, [], by simp, hpos, by rw [CoxeterSystem.wordProd_nil, mul_one]⟩
    simp only [not_forall, not_lt] at hpos
    obtain ⟨j, hj0, hj⟩ := hpos
    have hroot := IsRoot.smul (isRoot_single Tag.E6 j) w
    have hneg : height (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) < 0 :=
      lt_of_le_of_ne hj hroot.height_ne_zero
    have hdesc := (smul_single_mem_negRoots_iff w j).1 ⟨hroot, hneg⟩
    have hlen := (isRightDescent_iff_length w j).1 hdesc
    obtain ⟨u, ω, hω, hu, he⟩ := ih _ (by omega) (w * simple Tag.E6 j) rfl
    refine ⟨u, ω ++ [j], fun x hx => ?_, hu, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact hω x hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        exact hj0
    · rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton, ← mul_assoc, ← he,
        mul_assoc, simple_mul_simple_self, mul_one]

theorem wkTuple_of_witOK {vp ir rm : ℕ} (htab : tabCheckWith vp ir rm = true) {t : List ℕ}
    (ht : t.length = 6) (hlt : ∀ x ∈ t, x < 72) {c : ℕ} (h : witOK vp rm (encodeT t) c = true) :
    wkTuple (RootTables.ofCert e6Certificate) t = true := by
  have h256 : ∀ x ∈ t, x < 256 := fun x hx => (hlt x hx).trans (by norm_num)
  have hdec : decodeT 6 (encodeT t) = t := decodeT_encodeT h256 ht
  have hrows : rowsOf vp (encodeT t) =
      wkRows (t.map fun k => (RootTables.ofCert e6Certificate).vecs.getD k []) := by
    rw [rowsOf, hdec, List.map_congr_left fun x hx => vecP_eq htab (hlt x hx)]
  simp only [wkTuple, Bool.or_eq_true]
  unfold witOK at h
  split_ifs at h with h6 h6'
  ·
    left
    left
    have hc : c < t.length := by rw [ht]; exact h6
    have hbit : (rm / 2 ^ (72 * c + t.getD c 0) % 2 == 1) =
        rowRootAt ⟨c, h6⟩ ((RootTables.ofCert e6Certificate).vecs.getD (t.getD c 0) []) :=
      (tab_parts htab).2.2 ⟨c, h6⟩ (t.getD c 0) (hlt _ (getD_mem' 0 hc))
    rw [lane_encodeT h256] at h
    rw [h] at hbit
    simp only [wkRowRoot, List.any_eq_true, List.mem_finRange, true_and]
    refine ⟨⟨c, h6⟩, ?_⟩
    unfold rowRootAt at hbit
    have hrow : (wkRows (t.map fun k => (RootTables.ofCert e6Certificate).vecs.getD k [])).getD c
        [] = rowOf c ((RootTables.ofCert e6Certificate).vecs.getD (t.getD c 0) []) := by
      unfold wkRows rowOf
      rw [getD_range_map' _ _ h6]
      dsimp only
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hc), List.getElem_map,
        ← List.getD_eq_getElem _ 0 hc]
    rw [hrow]
    exact hbit.symm
  ·
    left
    right
    rw [← hrows]
    exact h
  ·
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h407, hm⟩ := h
    rw [hrows] at hm
    unfold minorAt at hm
    have hlen : wkTriples.length = 20 := rfl
    have hd : c - 7 < 400 := by omega
    simp only [wkMinor, List.any_eq_true]
    refine ⟨_, getD_mem' _ (by rw [hlen]; omega), _, getD_mem' _ (by rw [hlen]; omega), hm⟩

theorem trichotomy_of_checks
    {vp ir rm : ℕ} {words : List (List ℕ)} {up vk : List ℕ} {wit : List (List ℕ)}
    (htab : tabCheckWith vp ir rm = true) (hup : upCheckWith ir words up = true)
    (hk : kCheckWith up = true) (hv : vCheckWith ir vk (KTree.ofSorted vk) = true)
    (hu : ∀ n < up.length, uCheckWith vp rm (up.getD n 0) vk (wit.getD n []) = true)
    (w : WeylGroup TwistTag.E6.tag) :
    (∃ i, IsRoot TwistTag.E6.tag (wkMatrix w i)) ∨ wkMatrix w = 0 ∨
      ∃ R C : Fin 3 → Fin TwistTag.E6.tag.rank,
        ((wkMatrix w).submatrix R C).det ∈ ({1, -1, 2, -2} : Finset ℤ) := by
  obtain ⟨u, ω, hω, hupos, rfl⟩ := exists_decomp w
  obtain ⟨c, hc, hvrep⟩ := exists_vk htab hv ω hω
  obtain ⟨p, hp, hurep⟩ := exists_up hk u hupos
  obtain ⟨n, hn, hpn⟩ := List.getElem_of_mem hp
  simp only [upCheckWith, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hup
  obtain ⟨hlen, hall⟩ := hup
  have hnw : n < words.length := by rw [hlen]; exact hn
  have hzip := hall (words[n], up[n]) (by
    rw [List.mem_iff_getElem]
    exact ⟨n, by rw [List.length_zip, hlen, min_self]; exact hn, by rw [List.getElem_zip]⟩)
  have hw6 : ∀ i ∈ words[n], i < 6 := hzip.1
  have hwp : wordPerm ir words[n] = up[n] := hzip.2
  obtain ⟨g, hg⟩ := exists_wordPerm_spec htab _ hw6
  rw [hwp, hpn] at hg
  have hug : u = g := by
    refine ext_single fun j => ?_
    have hj6 : (j : ℕ) < 6 := j.2
    have h1 := (hurep.2 j).2
    rw [getD_decodeT hj6, lane_mod_pow hj6] at h1
    rw [← h1, (hg j (by omega)).2, root_single]
  subst hug
  set t := (decodeT 6 c).map (lane p) with htdef
  have hvlt := lt_of_represents hvrep
  have hvlen : (decodeT 6 c).length = 6 := length_decodeT 6 c
  have ht : t.length = 6 := by rw [htdef, List.length_map, hvlen]
  have htlt : ∀ x ∈ t, x < 72 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (hg y (hvlt y hy)).1
  have hrep : e6Certificate.Represents t (u * (coxeterSystem Tag.E6).wordProd ω) := by
    refine ⟨ht.trans rfl, fun j => ?_⟩
    have hj : (j : ℕ) < (decodeT 6 c).length := by rw [hvlen]; exact j.2
    have hget : t.getD j 0 = lane p ((decodeT 6 c).getD j 0) := by
      rw [htdef, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
        ← List.getD_eq_getElem _ 0 hj]
    have hy := hvlt _ (getD_mem' 0 hj)
    rw [hget]
    refine ⟨by rw [roots_length]; exact (hg _ hy).1, ?_⟩
    rw [(hg _ hy).2, (hvrep.2 j).2, mul_smul]
  have hun := hu n hn
  rw [List.getD_eq_getElem _ _ hn, hpn] at hun
  simp only [uCheckWith, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hun
  obtain ⟨hwl, hwall⟩ := hun
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  have hm' : m < (wit.getD n []).length := by rw [hwl]; exact hm
  have hel := hwall (vk[m], (wit.getD n [])[m]) (by
    rw [List.mem_iff_getElem]
    exact ⟨m, by rw [List.length_zip, hwl, min_self]; exact hm, by rw [List.getElem_zip]⟩)
  rw [hcm] at hel
  have hwit : witOK vp rm (encodeT t) (wit.getD n [])[m] = true := hel
  exact wkTrichotomy_of_wkTuple hrep (wkTuple_of_witOK htab ht htlt hwit)

end CFSG.KC.E6WK
