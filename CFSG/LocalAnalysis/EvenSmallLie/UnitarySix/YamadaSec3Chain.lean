module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Data
public import CFSG.Certificates.NativeSchreierCard

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def gP (k : ℕ) : Equiv.Perm (Fin 693) := permOfArr 693 (gA k)

@[expose] def wP (w : List ℕ) : Equiv.Perm (Fin 693) := (w.map gP).prod

theorem tabs_spec (h : tabsCheck = true) {k : ℕ} (hk : k < 18) :
    tabC yamCodes[k]! = gA k ∧ validA 693 (gA k) = true := by
  have := List.all_eq_true.1 h k (List.mem_range.2 hk)
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem rep_gA (h : tabsCheck = true) {k : ℕ} (hk : k < 18) : Rep 693 (gA k) (gP k) :=
  rep_of_validA (tabs_spec h hk).2

theorem rep_wA (h : tabsCheck = true) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 18) → Rep 693 (wA w) (wP w)
  | [], _ => by simpa [wA, wP] using (rep_idA (n := 693))
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 18 := fun j hj => hw j (List.mem_cons_of_mem k hj)
    have := rep_compA (rep_gA h hk) (rep_wA h w hw')
    simpa [wA, wP] using this

theorem permOfArr_wA (h : tabsCheck = true) {w : List ℕ} (hw : ∀ k ∈ w, k < 18) :
    permOfArr 693 (wA w) = wP w :=
  permOfArr_eq_of_rep (rep_wA h w hw)

namespace ChainData

variable (c : ChainData)

@[expose] def grp : Subgroup (Equiv.Perm (Fin 693)) :=
  Subgroup.closure {G | ∃ w ∈ c.gens, G = wP w}

@[expose] def GensOK : Prop := ∀ w ∈ c.gens, ∀ k ∈ w, k < 18

@[expose] def baseFin : List (Fin 693) := c.base.map fun b => ⟨b % 693, Nat.mod_lt _ (by norm_num)⟩

theorem O_size : c.O.size = c.gens.length := by simp [O]

theorem S_size : c.S.size = c.gens.length + c.words.length := by
  have key : ∀ (ws : List (List ℤ)) (S : Array (Array ℕ)),
      (ws.foldl (fun S w => S.push (wordA 693 S (rawInvs 693 S) w)) S).size =
        S.size + ws.length := by
    intro ws
    induction ws with
    | nil => intro S; simp
    | cons w ws ih => intro S; rw [List.foldl_cons, ih]; simp; omega
  rw [S, key, O_size]

theorem S_getElem_of_lt {i : ℕ} (hi : i < c.gens.length) : c.S[i]! = c.O[i]! := by
  have key : ∀ (ws : List (List ℤ)) (S : Array (Array ℕ)), i < S.size →
      (ws.foldl (fun S w => S.push (wordA 693 S (rawInvs 693 S) w)) S)[i]! = S[i]! := by
    intro ws
    induction ws with
    | nil => intro S _; rfl
    | cons w ws ih =>
      intro S hS
      rw [List.foldl_cons, ih _ (by simp; omega)]
      rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i hS, Array.getElem_push_lt]
  exact key _ _ (by rw [O_size]; exact hi)

theorem O_getElem {i : ℕ} (hi : i < c.gens.length) : c.O[i]! = wA c.gens[i] := by
  rw [getElem!_pos _ i (by rw [O_size]; exact hi)]
  simp [O]

theorem gens_le_S : c.gens.length ≤ c.S.size := by rw [S_size]; omega

@[expose] def Q (hb : c.baseFin.Nodup) : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by norm_num) c.S c.gens.length c.gens_le_S c.baseFin hb c.W

end ChainData

namespace ChainData

variable {c : ChainData}

theorem base_val (hok : c.ok = true) : (c.baseFin.map Fin.val).toArray = c.B := by
  have hF := chainCheckFacts hok
  have hlt : ∀ b ∈ c.base, b < 693 := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi' : i < c.B.size := by simpa [B] using hi
    have h1 := hF.base_lt i hi'
    rw [getElem!_pos c.B i hi'] at h1
    simpa [B] using h1
  rw [B, baseFin, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id c.base]
  apply List.map_congr_left
  intro b hb
  simp [Nat.mod_eq_of_lt (hlt b hb)]

theorem chainArrays (hok : c.ok = true) (hb : c.baseFin.Nodup) :
    ChainArrays (c.Q hb) (c.S.extract 0 c.gens.length) c.S c.B c.W := by
  have hF := chainCheckFacts hok
  have h := chainArrays_ofArrays (n := 693) (hn := by norm_num) (S := c.S) (k := c.gens.length)
    (hk := c.gens_le_S) (base := c.baseFin) (hb := hb) (W := c.W) hF.strong_inv
  rw [base_val hok] at h
  exact h

theorem valid (hok : c.ok = true) (hb : c.baseFin.Nodup) : ValidSchreier (c.Q hb) :=
  (validSchreier_of_chainOK (c.chainArrays hok hb) one_pos hok).1

theorem mem_Q_original {hb : c.baseFin.Nodup} {G : Equiv.Perm (Fin 693)} :
    G ∈ (c.Q hb).original.toList ↔ ∃ i < c.gens.length, permOfArr 693 c.S[i]! = G :=
  RawSchreierDatum.mem_ofArrays_original

theorem original_eq (htabs : tabsCheck = true) (hg : c.GensOK) (hb : c.baseFin.Nodup) :
    (c.Q hb).originalSubgroup = c.grp := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun G hG => ?_
    obtain ⟨i, hi, rfl⟩ := mem_Q_original.1 hG
    refine Subgroup.subset_closure ⟨c.gens[i], List.getElem_mem hi, ?_⟩
    rw [S_getElem_of_lt _ hi, O_getElem _ hi, permOfArr_wA htabs (hg _ (List.getElem_mem hi))]
  · refine (Subgroup.closure_le _).2 fun G hG => ?_
    obtain ⟨w, hw, rfl⟩ := hG
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    refine Subgroup.subset_closure (mem_Q_original.2 ⟨i, hi, ?_⟩)
    rw [S_getElem_of_lt _ hi, O_getElem _ hi, permOfArr_wA htabs (hg _ hw)]

theorem card_grp (htabs : tabsCheck = true) (hg : c.GensOK) (hok : c.ok = true)
    (hb : c.baseFin.Nodup) : Nat.card c.grp = c.order := by
  rw [← original_eq htabs hg hb,
    card_originalSubgroup_of_chainOK (c.chainArrays hok hb) one_pos hok]
  rfl

theorem mem_grp_iff (htabs : tabsCheck = true) (hg : c.GensOK) (hok : c.ok = true)
    (hb : c.baseFin.Nodup) {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ c.grp ↔ siftA 693 c.levels c.B 0 g = true := by
  rw [← original_eq htabs hg hb,
    ← siftA_iff_mem_originalSubgroup (c.chainArrays hok hb) one_pos hok hG]
  rfl

theorem closure_permsA (htabs : tabsCheck = true) (hg : c.GensOK) :
    Subgroup.closure (permsA 693 c.O) = c.grp := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun G hG => ?_
    obtain ⟨k, hk, rfl⟩ := hG
    have hk' : k < c.gens.length := by rw [← O_size]; exact hk
    refine Subgroup.subset_closure ⟨c.gens[k], List.getElem_mem hk', ?_⟩
    show permOfArr 693 c.O[k]! = _
    rw [O_getElem _ hk', permOfArr_wA htabs (hg _ (List.getElem_mem hk'))]
  · refine (Subgroup.closure_le _).2 fun G hG => ?_
    obtain ⟨w, hw, rfl⟩ := hG
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    refine Subgroup.subset_closure ⟨i, by rw [Set.mem_ofPred_eq, O_size]; exact hi, ?_⟩
    show permOfArr 693 c.O[i]! = _
    rw [O_getElem _ hi, permOfArr_wA htabs (hg _ hw)]

theorem forall_of_enum (htabs : tabsCheck = true) (hg : c.GensOK) {e : ArrCert}
    (he : enumOK 693 c.O c.base e = true) (hbase : ∀ p ∈ c.base, p < 693)
    {P : Equiv.Perm (Fin 693) → Prop}
    (h : ∀ i < e.pts.size, P (permOfArr 693 e.pts[i]!)) : ∀ x ∈ c.grp, P x := by
  intro x hx
  rw [← closure_permsA htabs hg] at hx
  obtain ⟨i, hi, rfl⟩ := ((enumOK_spec hbase he).1 x).1 hx
  exact h i hi

theorem valid_of_enum {e : ArrCert} (he : enumOK 693 c.O c.base e = true)
    (hbase : ∀ p ∈ c.base, p < 693) {i : ℕ} (hi : i < e.pts.size) :
    Rep 693 e.pts[i]! (permOfArr 693 e.pts[i]!) ∧ validA 693 e.pts[i]! = true :=
  ⟨rep_of_validA ((enumOK_spec hbase he).2.2 i hi), (enumOK_spec hbase he).2.2 i hi⟩

theorem card_of_enum (htabs : tabsCheck = true) (hg : c.GensOK) {e : ArrCert}
    (he : enumOK 693 c.O c.base e = true) (hbase : ∀ p ∈ c.base, p < 693) :
    Nat.card c.grp = e.pts.size := by
  rw [← closure_permsA htabs hg]
  exact (enumOK_spec hbase he).2.1

end ChainData

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
