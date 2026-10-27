module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.List.GetD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

abbrev Tab := List ℕ

@[expose] def Rep (σ : Equiv.Perm (Fin 45)) (t : Tab) : Prop :=
  t.length = 45 ∧ ∀ i (hi : i < 45), (σ ⟨i, hi⟩ : ℕ) = t.getD i 0

@[expose] def tmul (a b : Tab) : Tab := b.map fun i => a.getD i 0

@[expose] def tid : Tab := List.range 45

theorem rep_one : Rep 1 tid := by
  refine ⟨by simp [tid], fun i hi => ?_⟩
  simp [tid, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem rep_mul {σ τ : Equiv.Perm (Fin 45)} {a b : Tab} (ha : Rep σ a) (hb : Rep τ b) :
    Rep (σ * τ) (tmul a b) := by
  refine ⟨by simp [tmul, hb.1], fun i hi => ?_⟩
  have hib : i < b.length := hb.1 ▸ hi
  have h1 : (tmul a b).getD i 0 = a.getD (b.getD i 0) 0 := by
    simp [tmul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hib]
  rw [h1, Equiv.Perm.mul_apply, ← hb.2 i hi]
  exact ha.2 _ _

theorem rep_unique {σ τ : Equiv.Perm (Fin 45)} {t : Tab} (hσ : Rep σ t) (hτ : Rep τ t) :
    σ = τ := by
  ext ⟨i, hi⟩
  rw [hσ.2 i hi, hτ.2 i hi]

theorem rep_eq_tab {σ : Equiv.Perm (Fin 45)} {a b : Tab} (ha : Rep σ a) (hb : Rep σ b) :
    a = b := by
  apply List.ext_getElem (ha.1.trans hb.1.symm)
  intro i hia hib
  have hi : i < 45 := ha.1 ▸ hia
  have e1 := ha.2 i hi
  have e2 := hb.2 i hi
  rw [List.getD_eq_getElem _ _ hia] at e1
  rw [List.getD_eq_getElem _ _ hib] at e2
  rw [← e1, ← e2]

theorem rep_ne {σ τ : Equiv.Perm (Fin 45)} {a b : Tab} (ha : Rep σ a) (hb : Rep τ b)
    (hab : a ≠ b) : σ ≠ τ := by
  rintro rfl
  exact hab (rep_eq_tab ha hb)

theorem rep_pow {σ : Equiv.Perm (Fin 45)} {a : Tab} (ha : Rep σ a) :
    ∀ k : ℕ, Rep (σ ^ k) ((tmul a)^[k] tid)
  | 0 => by simpa using rep_one
  | k + 1 => by
    rw [pow_succ', Function.iterate_succ_apply']
    exact rep_mul ha (rep_pow ha k)

@[expose] def allDistinct : List Tab → Bool
  | [] => true
  | t :: ts => ts.all (fun s => s != t) && allDistinct ts

theorem allDistinct_nodup : ∀ {l : List Tab}, allDistinct l = true → l.Nodup
  | [], _ => List.nodup_nil
  | t :: ts, h => by
    simp only [allDistinct, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    exact List.nodup_cons.2 ⟨fun hm => h.1 t hm rfl, allDistinct_nodup h.2⟩

@[expose] def treeOK (gens elems : List Tab) (par : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  i == 0 || (decide ((par.getD i (0, 0)).1 < i) && decide ((par.getD i (0, 0)).2 < gens.length) &&
    elems.getD i [] ==
      tmul (gens.getD (par.getD i (0, 0)).2 []) (elems.getD (par.getD i (0, 0)).1 []))

@[expose] def actOK (gens elems : List Tab) (act : List (List ℕ)) (j i : ℕ) : Bool :=
  decide ((act.getD j []).getD i 0 < elems.length) &&
    tmul (gens.getD j []) (elems.getD i []) == elems.getD ((act.getD j []).getD i 0) []

@[expose] def enumOK (gens elems : List Tab) (par : List (ℕ × ℕ)) (act : List (List ℕ)) : Bool :=
  (elems.getD 0 [] == tid) && (elems.all fun t => t.length == 45) &&
  ((List.range elems.length).all fun i => treeOK gens elems par i) &&
  ((List.range gens.length).all fun j => (List.range elems.length).all fun i =>
    actOK gens elems act j i) &&
  allDistinct elems

section Enum

variable {gens elems : List Tab} {par : List (ℕ × ℕ)} {act : List (List ℕ)}
  {σs : List (Equiv.Perm (Fin 45))}

abbrev gen (σs : List (Equiv.Perm (Fin 45))) : Subgroup (Equiv.Perm (Fin 45)) :=
  Subgroup.closure {g | g ∈ σs}

theorem enumOK_parts (h : enumOK gens elems par act = true) :
    elems.getD 0 [] = tid ∧ (∀ t ∈ elems, t.length = 45) ∧
    (∀ i < elems.length, treeOK gens elems par i = true) ∧
    (∀ j < gens.length, ∀ i < elems.length, actOK gens elems act j i = true) ∧
    elems.Nodup := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h0, hlen⟩, htree⟩, hact⟩, hd⟩ := h
  exact ⟨h0, fun t ht => hlen t ht, htree, hact, allDistinct_nodup hd⟩

variable (hσ : σs.length = gens.length)
  (hg : ∀ j < gens.length, Rep (σs.getD j 1) (gens.getD j []))

include hσ hg in
theorem gen_mem_of_lt {j : ℕ} (hj : j < gens.length) : σs.getD j 1 ∈ gen σs := by
  apply Subgroup.subset_closure
  show σs.getD j 1 ∈ σs
  rw [List.getD_eq_getElem _ _ (hσ ▸ hj)]
  exact List.getElem_mem _

include hσ hg in
theorem exists_mem_rep_of_enumOK (h : enumOK gens elems par act = true) :
    ∀ i < elems.length, ∃ g ∈ gen σs, Rep g (elems.getD i []) := by
  obtain ⟨h0, -, htree, -, -⟩ := enumOK_parts h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have ht := htree i hi
    simp only [treeOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ht
    rcases ht with rfl | ⟨⟨hp, hj⟩, heq⟩
    · exact ⟨1, Subgroup.one_mem _, h0 ▸ rep_one⟩
    · obtain ⟨g, hgS, hgr⟩ := ih _ hp (by omega)
      refine ⟨σs.getD (par.getD i (0, 0)).2 1 * g, Subgroup.mul_mem _ (gen_mem_of_lt hσ hg hj) hgS,
        ?_⟩
      rw [heq]
      exact rep_mul (hg _ hj) hgr

include hσ hg in
theorem exists_rep_of_mem_of_enumOK (h : enumOK gens elems par act = true) {g : Equiv.Perm (Fin 45)}
    (hgS : g ∈ gen σs) : ∃ i < elems.length, Rep g (elems.getD i []) := by
  obtain ⟨h0, -, -, hact, -⟩ := enumOK_parts h
  have hlen : 0 < elems.length := by
    rcases elems with _ | ⟨a, l⟩
    · simp [tid] at h0
    · simp
  have hleft : ∀ j < gens.length, ∀ y : Equiv.Perm (Fin 45),
      (∃ i < elems.length, Rep y (elems.getD i [])) →
        ∃ i < elems.length, Rep (σs.getD j 1 * y) (elems.getD i []) := by
    rintro j hj y ⟨i, hi, hy⟩
    have ha := hact j hj i hi
    simp only [actOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
    exact ⟨_, ha.1, ha.2 ▸ rep_mul (hg j hj) hy⟩
  have hpow : ∀ j < gens.length, ∀ k : ℕ, ∀ y : Equiv.Perm (Fin 45),
      (∃ i < elems.length, Rep y (elems.getD i [])) →
        ∃ i < elems.length, Rep ((σs.getD j 1) ^ k * y) (elems.getD i []) := by
    intro j hj k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hleft j hj _ (ih y hy)
  induction hgS using Subgroup.closure_induction_left with
  | one => exact ⟨0, hlen, h0 ▸ rep_one⟩
  | mul_left x hx y _ ih =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < gens.length := hσ ▸ hj
    have := hleft j hj' y ih
    rwa [List.getD_eq_getElem _ _ hj] at this
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < gens.length := hσ ▸ hj
    have hinv : (σs[j])⁻¹ = σs[j] ^ (orderOf σs[j] - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos _),
        pow_orderOf_eq_one]
    rw [hinv]
    have := hpow j hj' (orderOf σs[j] - 1) y ih
    rwa [List.getD_eq_getElem _ _ hj] at this

include hσ hg in
theorem mem_gen_iff_of_enumOK (h : enumOK gens elems par act = true) (g : Equiv.Perm (Fin 45)) :
    g ∈ gen σs ↔ ∃ i < elems.length, Rep g (elems.getD i []) := by
  refine ⟨exists_rep_of_mem_of_enumOK hσ hg h, ?_⟩
  rintro ⟨i, hi, hgr⟩
  obtain ⟨g', hg'S, hg'r⟩ := exists_mem_rep_of_enumOK hσ hg h i hi
  rwa [rep_unique hgr hg'r]

include hσ hg in
theorem card_gen_of_enumOK (h : enumOK gens elems par act = true) :
    Nat.card (gen σs) = elems.length := by
  obtain ⟨-, -, -, -, hnd⟩ := enumOK_parts h
  have hex := exists_mem_rep_of_enumOK hσ hg h
  choose f hfS hfr using hex
  let F : Fin elems.length → gen σs := fun i => ⟨f i.1 i.2, hfS i.1 i.2⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i k hik
      have e : f i.1 i.2 = f k.1 k.2 := congrArg Subtype.val hik
      have hr := hfr k.1 k.2
      rw [← e] at hr
      have htab := rep_eq_tab (hfr i.1 i.2) hr
      rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ k.2] at htab
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 htab)
    · rintro ⟨g, hgS⟩
      obtain ⟨i, hi, hgr⟩ := exists_rep_of_mem_of_enumOK hσ hg h hgS
      exact ⟨⟨i, hi⟩, Subtype.ext (rep_unique (hfr i hi) hgr)⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

end Enum

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
