module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleyCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleyList
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem enumW_of_cayleyOK {T : Type} [Group T] [DecidableEq T] {cap m : ℕ} {ws : List (List ℕ)}
    {ts : List T} (h : cayleyOK cap m ws ts = true) : enumW cap m ws = true := by
  simp only [cayleyOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

theorem nonempty_mulEquiv_of_cayleyOK {T : Type} [Group T] [DecidableEq T] {cap m : ℕ}
    {ws : List (List ℕ)} {ts : List T} (h : cayleyOK cap m ws ts = true) (hT : Nat.card T = m) :
    Nonempty (↥(closure (elemW '' {w | w ∈ ws})) ≃* T) := by
  simp only [cayleyOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨henum, hlen⟩, hpos⟩, h0⟩, hsz⟩, hf0⟩, hstep⟩, hdist⟩ := h
  obtain ⟨hgens, hwsok⟩ := enumW_gens_words henum
  obtain ⟨hcard, hS⟩ := enumW_spec henum
  have hsizeL : (subgroupList cap ws).size = m := enumW_size henum
  set X := closure (elemW '' {w | w ∈ ws}) with hX
  set L := subgroupList cap ws with hL
  set fv := cayleyImages ts.toArray (mulClosureH 1408 (tabsW ws).toArray cap).2.1
    (mulClosureH 1408 (tabsW ws).toArray cap).2.2 with hfv
  have hLE : (mulClosureH 1408 (tabsW ws).toArray cap).1 = L := rfl
  rw [hLE] at hpos h0 hsz hstep
  have hrepk : ∀ k : Fin L.size, Rep 1408 L[k.val]! (tablePerm 1408 L[k.val]!) ∧
      tablePerm 1408 L[k.val]! ∈ X := by
    intro k
    obtain ⟨g, hg, hr⟩ := hS.rep k.val k.2
    rw [tablePerm_eq hr]
    exact ⟨hr, hg⟩
  have hcov : ∀ x ∈ X, ∃ k : Fin L.size, tablePerm 1408 L[k.val]! = x := by
    intro x hx
    obtain ⟨k, hk, hr⟩ := hS.cov x hx
    exact ⟨⟨k, hk⟩, tablePerm_eq hr⟩
  have hinjE : Function.Injective (fun k : Fin L.size => tablePerm 1408 L[k.val]!) := by
    let e' : Fin L.size → ↥X := fun k => ⟨tablePerm 1408 L[k.val]!, (hrepk k).2⟩
    have hsurj : Function.Surjective e' := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := hcov x hx
      exact ⟨k, Subtype.ext hk⟩
    have hb : Function.Bijective e' :=
      hsurj.bijective_of_nat_card_le (by rw [Nat.card_fin, hsizeL, hcard])
    intro a b hab
    exact hb.1 (Subtype.ext hab)
  have hinjF : Function.Injective (fun k : Fin L.size => fv.getD k.val 1) := by
    intro a b hab
    by_contra hne
    have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
    have hall := allIn_eq_true.1 hdist
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · have := allIn_eq_true.1 (hall a.val (Nat.zero_le _) (by omega)) b.val (by omega)
        (by omega)
      exact (of_decide_eq_true this) hab
    · have := allIn_eq_true.1 (hall b.val (Nat.zero_le _) (by omega)) a.val (by omega)
        (by omega)
      exact (of_decide_eq_true this) hab.symm
  have hlen' : (ws.map elemW).length = ts.length := by simpa using hlen
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT, ← hsizeL]; exact hpos.ne')
  refine TwoHSData.nonempty_mulEquiv_of_cayley_enum X (ws.map elemW) ts hlen'
    (by rw [hX, mem_map_elemW_set]) (n := L.size) (fun k => tablePerm 1408 L[k.val]!)
    (fun k => fv.getD k.val 1) hinjE (fun k => (hrepk k).2) hcov ⟨0, hpos⟩
    ((tblEq_iff_eq (hrepk ⟨0, hpos⟩).1 (Rep.idT (by norm_num))).1 h0) hf0 ?_ hinjF
    (hinjF.bijective_of_nat_card_le (by rw [hT, Nat.card_fin, hsizeL])).2
  intro k i
  have hiw : i.val < ws.length := by simpa using i.2
  have hgs : (tabsW ws).toArray.size = ws.length := by simp [tabsW]
  have h1 := allIn_eq_true.1 hstep k.val (Nat.zero_le _) k.2
  have h2 := allIn_eq_true.1 h1 i.val (Nat.zero_le _) (by rw [hgs]; exact hiw)
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range] at h2
  obtain ⟨j, hj, hy, hfj⟩ := h2
  have hwi : wordOK (ws.get ⟨i.val, hiw⟩) = true :=
    List.all_eq_true.1 hwsok _ (List.get_mem _ _)
  have hrw := rep_elemW_of_gensOK hgens hwi
  have htab : (tabsW ws).toArray[i.val]! = tabW (ws.get ⟨i.val, hiw⟩) := by
    rw [getElem!_pos _ i.val (by rw [hgs]; exact hiw)]
    simp [tabsW]
  have hprod := Rep.compT (hrepk k).1 hrw
  rw [← htab] at hprod
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · have := (tblEq_iff_eq hprod (hrepk ⟨j, hj⟩).1).1 hy
    simpa [List.getElem_map] using this.symm
  · have hit : i.val < ts.length := by omega
    have e1 : ts.toArray.getD i.val 1 = ts.get (Fin.cast hlen' i) := by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hit]
      simp
    rw [e1] at hfj
    exact hfj

end CFSG.EvenSporadicStandard.HNRecog
