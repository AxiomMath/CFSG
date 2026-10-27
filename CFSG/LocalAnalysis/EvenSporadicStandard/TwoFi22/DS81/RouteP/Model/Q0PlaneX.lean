module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0Gen

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] def ptOfNat (n : ℕ) : Ω := ⟨n % 920808, Nat.mod_lt _ (by norm_num)⟩

theorem ptOfNat_val {n : ℕ} (h : n < 920808) : (ptOfNat n).val = n := Nat.mod_eq_of_lt h

theorem ptOfNat_val_eq (p : Ω) : ptOfNat p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)

@[expose] noncomputable def planeXN (i : ℕ) : Finset Ω :=
  (Finset.range 24).image fun j => ptOfNat (((planeXData ())[i]!)[j]!)

@[expose] noncomputable def planeX (i : Fin 891) : Finset Ω := planeXN i.val

section Rows

theorem row_strictMono {i : ℕ} (hi : i < 891) {j j' : ℕ} (h : j < j') (hj' : j' < 24) :
    ((planeXData ())[i]!)[j]! < ((planeXData ())[i]!)[j']! := by
  induction j', h using Nat.le_induction with
  | base => exact planesFacts.rowMono i hi j (by omega)
  | succ k hk ih =>
    exact (ih (by omega)).trans (planesFacts.rowMono i hi k (by omega))

theorem mem_planeXN_iff {i : ℕ} (hi : i < 891) {p : Ω} :
    p ∈ planeXN i ↔ ∃ j < 24, ((planeXData ())[i]!)[j]! = p.val := by
  unfold planeXN
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hjp⟩
    have hj' : j < 24 := Finset.mem_range.1 hj
    refine ⟨j, hj', ?_⟩
    rw [← hjp, ptOfNat_val (planesFacts.rowLt i hi j hj')]
  · rintro ⟨j, hj, hjp⟩
    exact ⟨j, Finset.mem_range.2 hj, by rw [hjp, ptOfNat_val_eq]⟩

theorem rowPt_injOn {i : ℕ} (hi : i < 891) :
    Set.InjOn (fun j => ptOfNat (((planeXData ())[i]!)[j]!)) (Finset.range 24 : Set ℕ) := by
  intro j hj j' hj' h
  have hj1 : j < 24 := Finset.mem_range.1 hj
  have hj2 : j' < 24 := Finset.mem_range.1 hj'
  have e := congrArg Fin.val h
  simp only [ptOfNat_val (planesFacts.rowLt i hi j hj1),
    ptOfNat_val (planesFacts.rowLt i hi j' hj2)] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd e (Nat.ne_of_lt (row_strictMono hi hlt hj2))
  · exact absurd e.symm (Nat.ne_of_lt (row_strictMono hi hlt hj1))

theorem card_planeXN {i : ℕ} (hi : i < 891) : (planeXN i).card = 24 := by
  unfold planeXN
  rw [Finset.card_image_of_injOn (rowPt_injOn hi), Finset.card_range]

theorem planeXN_zero : planeXN 0 = plane := by
  have hsub : planeXN 0 ⊆ plane := by
    intro p hp
    obtain ⟨j, hj, hjp⟩ := (mem_planeXN_iff (by norm_num)).1 hp
    obtain ⟨i, hi, hie⟩ := planesFacts.base j hj
    rw [mem_plane_iff]
    refine ⟨⟨i, hi⟩, Fin.ext ?_⟩
    rw [planePt_val]
    exact hie.trans hjp
  exact Finset.eq_of_subset_of_card_le hsub (by rw [card_plane, card_planeXN (by norm_num)])

theorem planeXN_inj {i j : ℕ} (hi : i < 891) (hj : j < 891) (h : planeXN i = planeXN j) :
    i = j := by
  by_contra hne
  have key : ∀ i j : ℕ, i < 891 → j < i → planeXN i = planeXN j → False := by
    intro i j hi hji h
    obtain ⟨a, ha, hne⟩ := planesFacts.distinct i hi j hji
    have hp : ptOfNat (((planeXData ())[i]!)[a]!) ∈ planeXN i :=
      Finset.mem_image.2 ⟨a, Finset.mem_range.2 ha, rfl⟩
    rw [h, mem_planeXN_iff (hji.trans hi)] at hp
    obtain ⟨b, hb, hbe⟩ := hp
    rw [ptOfNat_val (planesFacts.rowLt i hi a ha)] at hbe
    exact hne b hb hbe
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact key j i hj hlt h.symm
  · exact key i j hi hlt h

theorem planeX_zero : planeX 0 = plane := planeXN_zero

theorem planeX_injective : Function.Injective planeX := fun i j h =>
  Fin.ext (planeXN_inj i.isLt j.isLt h)

theorem interAux_eq {a b : ℕ} (ha : a < 891) (hb : b < 891) :
    ∀ m ≤ 24, interAux (planeXData ()) a b m =
      ((Finset.range m).filter fun j => ptOfNat (((planeXData ())[a]!)[j]!) ∈ planeXN b).card := by
  intro m
  induction m with
  | zero => intro _; simp [interAux]
  | succ m ih =>
    intro hm
    have hm' : m < 24 := by omega
    have hP : ptOfNat (((planeXData ())[a]!)[m]!) ∈ planeXN b ↔
        memRow ((planeXData ())[b]!) (((planeXData ())[a]!)[m]!) = true := by
      rw [mem_planeXN_iff hb, memRow_eq_true, ptOfNat_val (planesFacts.rowLt a ha m hm')]
    rw [interAux, ih (by omega), Finset.range_add_one, Finset.filter_insert]
    by_cases h : memRow ((planeXData ())[b]!) (((planeXData ())[a]!)[m]!) = true
    · rw [if_pos h, if_pos (hP.2 h), Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg h, if_neg (fun h' => h (hP.1 h'))]
      simp

theorem card_planeXN_inter {a b : ℕ} (ha : a < 891) (hb : b < 891) :
    (planeXN a ∩ planeXN b).card = planeInterCount (planeXData ()) a b := by
  classical
  unfold planeInterCount
  rw [interAux_eq ha hb 24 le_rfl]
  have e : planeXN a = (Finset.range 24).image fun j => ptOfNat (((planeXData ())[a]!)[j]!) :=
    rfl
  rw [← Finset.filter_mem_eq_inter, e, Finset.filter_image, Finset.card_image_of_injOn]
  intro j hj j' hj' h
  exact rowPt_injOn ha (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj').1 h

theorem card_planeX_inter (a b : Fin 891) :
    (planeX a ∩ planeX b).card = planeInterCount (planeXData ()) a.val b.val :=
  card_planeXN_inter a.isLt b.isLt

theorem planeTabs_lt {s i : ℕ} (hs : s < 14) (hi : i < 891) :
    ((planeTabs ())[s]!)[i]! < 891 :=
  planesFacts.tabLt s hs i hi

theorem planeTabs_size : (planeTabs ()).size = 14 := planesFacts.tabsSize

theorem planeDTabs_size : (planeDTabs ()).size = 13 := by
  simp [planeDTabs, planeTabs_size]

theorem planeDTabs_getElem {s : ℕ} (hs : s < 13) : (planeDTabs ())[s]! = (planeTabs ())[s]! := by
  have h1 : s < (planeDTabs ()).size := by rw [planeDTabs_size]; exact hs
  have h2 : s < (planeTabs ()).size := by rw [planeTabs_size]; omega
  rw [getElem!_pos (planeDTabs ()) s h1, getElem!_pos (planeTabs ()) s h2]
  simp [planeDTabs]

end Rows

section Action

theorem planeGen_smul_planeXN {s i : ℕ} (hs : s < 14) (hi : i < 891) :
    planeGen s • planeXN i = planeXN (((planeTabs ())[s]!)[i]!) := by
  have hi' := planeTabs_lt hs hi
  have hsub : planeGen s • planeXN i ⊆ planeXN (((planeTabs ())[s]!)[i]!) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hq
    obtain ⟨a, ha, hap⟩ := (mem_planeXN_iff hi).1 hp
    obtain ⟨b, hb, hbe⟩ := planesFacts.act s hs i hi a ha
    rw [mem_planeXN_iff hi']
    refine ⟨b, hb, ?_⟩
    rw [hbe, smul_val_of_rep (rep_planeGen s) p, ← hap]
  exact Finset.eq_of_subset_of_card_le hsub
    (by rw [card_planeXN hi', Finset.card_smul_finset, card_planeXN hi])

theorem gen_smul_planeX (s : Fin 14) (i : Fin 891) :
    planeGen s.val • planeX i =
      planeX ⟨((planeTabs ())[s.val]!)[i.val]!, planeTabs_lt s.isLt i.isLt⟩ :=
  planeGen_smul_planeXN s.isLt i.isLt

theorem exists_mem_smul_plane_eq_planeXN (K : Subgroup Q3) (hK : ∀ s < 14, planeGen s ∈ K) :
    ∀ i < 891, ∃ k ∈ K, k • plane = planeXN i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨1, K.one_mem, by rw [one_smul, planeXN_zero]⟩
    · obtain ⟨hpar, hlab, hT⟩ := planesFacts.tree i hi0 hi
      obtain ⟨k, hk, hkp⟩ := ih _ hpar (hpar.trans hi)
      refine ⟨planeGen (planeLab ())[i]! * k, K.mul_mem (hK _ hlab) hk, ?_⟩
      rw [mul_smul, hkp, planeGen_smul_planeXN hlab (hpar.trans hi), hT]

theorem exists_mem_smul_plane_eq_planeX (K : Subgroup Q3) (hK : ∀ s < 14, planeGen s ∈ K)
    (i : Fin 891) : ∃ k ∈ K, k • plane = planeX i :=
  exists_mem_smul_plane_eq_planeXN K hK i.val i.isLt

theorem planeX_mem_orbit (i : Fin 891) :
    planeX i ∈ MulAction.orbit ↥Q0 plane := by
  obtain ⟨k, hk, hkp⟩ := exists_mem_smul_plane_eq_planeX Q0 (fun s hs => planeGen_mem_Q0 hs) i
  exact ⟨⟨k, hk⟩, hkp⟩

end Action

section Inter

theorem exists_planeXN_inter_plane {p : Ω} (hp : p ∈ plane) (h0 : p ≠ x0) (h1 : p ≠ x1)
    (h2 : p ≠ x2) :
    ∃ i < 891, ∀ q ∈ plane, (q ∈ planeXN i ↔ q = x0 ∨ q = x1 ∨ q = x2 ∨ q = p) := by
  obtain ⟨a, rfl⟩ := mem_plane_iff.1 hp
  have ha : 3 ≤ a.val := by
    by_contra hlt
    have : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by omega
    rcases this with h | h | h
    · exact h0 (by rw [← planePt_zero]; congr 1; exact Fin.ext h)
    · exact h1 (by rw [← planePt_one]; congr 1; exact Fin.ext h)
    · exact h2 (by rw [← planePt_two]; congr 1; exact Fin.ext h)
  have ht : a.val - 3 < 21 := by have := a.isLt; omega
  refine ⟨(planeSep ())[a.val - 3]!, planesFacts.sepLt _ ht, ?_⟩
  intro q hq
  obtain ⟨c, rfl⟩ := mem_plane_iff.1 hq
  rw [mem_planeXN_iff (planesFacts.sepLt _ ht)]
  have hs := planesFacts.sepMem (a.val - 3) ht c.val c.isLt
  simp only [planePt_val]
  rw [hs]
  constructor
  · rintro (hc | hc)
    · have : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
      rcases this with h | h | h
      · exact Or.inl (by rw [← planePt_zero]; congr 1; exact Fin.ext h)
      · exact Or.inr (Or.inl (by rw [← planePt_one]; congr 1; exact Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (by rw [← planePt_two]; congr 1; exact Fin.ext h)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hcv : c.val = a.val := by rw [hc]; exact Nat.sub_add_cancel ha
      rw [Fin.ext hcv]
  · rintro (hc | hc | hc | hc)
    · left
      have := planePt_injective (hc.trans planePt_zero.symm)
      rw [this]
      norm_num
    · left
      have := planePt_injective (hc.trans planePt_one.symm)
      rw [this]
      norm_num
    · left
      have := planePt_injective (hc.trans planePt_two.symm)
      rw [this]
      norm_num
    · right
      have := planePt_injective hc
      rw [this]
      exact (Nat.sub_add_cancel ha).symm

end Inter

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
