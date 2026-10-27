module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7
public import Certificates.Certificate17339
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Leaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Rec
public import CFSG.RankThree.PartOne.N143.SecRankHard
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionReduce

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native CFSG.HardMathSupport.Solomon.Coordinator.YS08 CFSG.HardMathSupport.Dickson.I271.TabFi23Y CFSG.YGroups
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.RankThree.PartOne.N143.O7 (Om)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Check

theorem yRelsD_eq : yRelsD = yRels 3 2 2 := by decide +kernel

theorem y322_of_check {x : CFSG.Sporadic.Fi23.J} {T : Table} (hT : Rep 31671 T x) {ks : List ℕ}
    (h : yCheck orb (dTable orb) (genTables orb (-2)) T ks = true) :
    ∃ s : Fin 8 → CFSG.Sporadic.Fi23.J, (∀ w ∈ yRels 3 2 2, evalWord (y322Img s) w = 1) ∧
      (∃ i j, s i * s j ≠ s j * s i) ∧ ∀ i, s i * x = x * s i := by
  unfold yCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlen, hlt⟩, hfix⟩, hlet⟩, hrel⟩, hnc⟩ := h
  have hmem : ∀ i : Fin 8, ks[i.val]! ∈ ks := fun i => by
    have hi : i.val < ks.length := by rw [hlen]; exact i.2
    rw [getElem!_pos ks i.val hi]
    exact List.getElem_mem hi
  refine ⟨fun i => conjPt ks[i.val]!, ?_, ?_, ?_⟩
  · intro w hw
    rw [← yRelsD_eq] at hw
    have hl : ∀ c ∈ w, c < 8 := fun c hc => by simpa using hlet w hw c hc
    have h2 := rep_starWordTab_dTable (w.map fun c => ks[c]!)
    have h3 : ((w.map fun c => ks[c]!).map conjPt).prod = 1 :=
      eq_of_eqTab h2 (Rep.idT (by norm_num)) (hrel w hw)
    show (w.map (y322Img (fun i : Fin 8 => conjPt ks[i.val]!))).prod = 1
    rw [← h3, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun c hc => ?_)
    have hc8 : c < 8 := hl c hc
    show y322Img (fun i : Fin 8 => conjPt ks[i.val]!) c = conjPt ks[c]!
    unfold y322Img
    rw [dif_pos hc8]
  · refine ⟨0, 1, fun hcomm => ?_⟩
    have hA := rep_starWordTab_dTable [ks[0]!, ks[1]!]
    have hB := rep_starWordTab_dTable [ks[1]!, ks[0]!]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hA hB
    have hcomm' : conjPt ks[1]! * conjPt ks[0]! = conjPt ks[0]! * conjPt ks[1]! := hcomm.symm
    rw [hcomm'] at hB
    rw [eqTab_of_rep_eq hA hB] at hnc
    exact absurd hnc (by decide)
  · intro i
    have hk := hlt _ (hmem i)
    have hf := hfix _ (hmem i)
    have hf' : x • (⟨ks[i.val]!, hk⟩ : Fin 31671) = ⟨ks[i.val]!, hk⟩ := by
      apply Fin.ext
      rw [← ap_eq_smul hT]
      exact hf
    have h5 := (fix_iff_comm x ⟨ks[i.val]!, hk⟩).1 hf'
    exact h5

end Check

section Top

open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem shapeRkAt_of_data_solvable {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') (x : G)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) = ⊥) {m : ℕ}
    (hk : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Nat.card ↥L * m) (hm : m ∣ 6)
    (hG : Good ↥L) (hR : Rk ↥L) : ShapeRkAt p Good Rk x := by
  let x' : ↥(⊤ : Subgroup G) := ⟨x, Subgroup.mem_top x⟩
  have h1 : L ≤ Subgroup.centralizer ({((x' : ↥(⊤ : Subgroup G)) : G)} : Set G) ⊓
      (⊤ : Subgroup G) := fun l hl => ⟨hLC hl, Subgroup.mem_top l⟩
  have h2 : ∀ g ∈ Subgroup.centralizer ({((x' : ↥(⊤ : Subgroup G)) : G)} : Set G) ⊓
      (⊤ : Subgroup G), ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl => hLn g hg.1 l hl
  have h4 : Nat.card ↥(Subgroup.centralizer ({((x' : ↥(⊤ : Subgroup G)) : G)} : Set G) ⊓
      (⊤ : Subgroup G)) = Nat.card ↥L * m := by
    rw [inf_top_eq]
    exact hk
  have h5 : GLAPPrimeCore p ↥(Subgroup.centralizer ({x'} : Set ↥(⊤ : Subgroup G))) = ⊥ := by
    let e : ↥(⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    have hmap := map_glaPPrimeCoreOf_of_injective p e.toMonoidHom e.injective
      (Subgroup.centralizer ({x'} : Set ↥(⊤ : Subgroup G)))
    rw [map_centralizer_singleton e x'] at hmap
    have hex : e x' = x := rfl
    rw [hex, hcore] at hmap
    have h2 : GLAPPrimeCoreOf p (Subgroup.centralizer ({x'} : Set ↥(⊤ : Subgroup G))) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap
    exact (glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore p _).1 h2
  have hshape : ShapeRkAt p Good Rk x' :=
    shapeRkAt_of_subgroup_data_solvable hp hGood hRk (⊤ : Subgroup G) x' L h1 h2 hs hnab hpL h5
      h4 hm hG hR
  exact ShapeRkAt.of_equiv hp hGood hRk (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G) hshape

theorem shapeRkAt_of_om {G : Type} [Group G] [Finite G] (x : G)
    (hcore : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) = ⊥) (L : Subgroup G)
    (e : ↥L ≃* ↥Om) (hLC : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hk : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Nat.card ↥L * 3) :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) x := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True :=
    fun _ _ _ _ _ h => h
  have hs : IsSimpleGroup ↥L := tabFi23_isSimpleGroup_of_equiv_om e
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := tabFi23_nonabelian_of_equiv_om e
  have hpL : 3 ∣ Nat.card ↥L := by
    rw [tabFi23_card_of_equiv_om e]
    norm_num
  exact shapeRkAt_of_data_solvable Nat.prime_three hGood hRk x L hLC hLn hs hnab hpL hcore
    (m := 3) hk (by norm_num) (tabFi23_leafType_of_equiv_om e) trivial

end Top

section ThreeA

theorem shapeRkAt_t3_zero : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (t3 0) := by
  haveI := finite_J23
  have hcl := t3_classData.1
  have hz : orderOf (t3 0) = 3 := hcl.1
  have hcardC := card_cent_t3_zero
  have h17339 : yCheck orb (dTable orb) (genTables orb (-2)) (t3Tabs orb letters)[0]! y322Ks =
      true := Certificates.certificate17339
  obtain ⟨s, hrel, hnc, hzc⟩ := y322_of_check (rep_t3Tabs 0) h17339
  have hcl' : Subgroup.closure (Set.range s ∪ {t3 0}) ≤
      Subgroup.centralizer ({t3 0} : Set CFSG.Sporadic.Fi23.J) := by
    rw [Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | hg)
    · exact cen_iff' (hzc i)
    · rw [Set.mem_singleton_iff.1 hg]
      exact cen_iff' rfl
  have hcard : Nat.card ↥(Subgroup.closure (Set.range s ∪ {t3 0})) ≤ 3 * 4585351680 := by
    have h1 := Subgroup.card_le_of_le hcl'
    rw [hcardC] at h1
    omega
  obtain ⟨⟨e⟩, hLcard, hzL⟩ := tabFi23_y322_recognition s hrel hnc (t3 0) hz hzc hcard
  set L : Subgroup CFSG.Sporadic.Fi23.J := Subgroup.closure (Set.range s) with hL
  set N : Subgroup CFSG.Sporadic.Fi23.J := Subgroup.closure (Set.range s ∪ {t3 0}) with hN
  set C : Subgroup CFSG.Sporadic.Fi23.J := Subgroup.centralizer ({t3 0} : Set CFSG.Sporadic.Fi23.J) with hC
  have hLN : L ≤ N := Subgroup.closure_mono Set.subset_union_left
  have hLC : L ≤ C := hLN.trans hcl'
  have hCL : Nat.card C = Nat.card L * 3 := by
    rw [hC, hcardC, hLcard]
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hNC : N = C := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hLN
    have hNd : Nat.card N ∣ Nat.card C := Subgroup.card_dvd_of_le hcl'
    rw [hc, hCL] at hNd
    have hc3 : c ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hLpos hNd
    rcases (Nat.dvd_prime Nat.prime_three).1 hc3 with h1 | h3
    · exfalso
      have hEq : L = N := Subgroup.eq_of_le_of_card_ge hLN (by rw [hc, h1, mul_one])
      apply hzL
      rw [hEq]
      exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
    · exact Subgroup.eq_of_le_of_card_ge hcl' (by rw [hCL, hc, h3])
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    have hNn : N ≤ Subgroup.normalizer L := by
      rw [hN, Subgroup.closure_le]
      rintro g (⟨i, rfl⟩ | hg)
      · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨i, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hg]
        refine Subgroup.mem_normalizer_iff.2 fun h => ?_
        have hcomm : ∀ l ∈ L, t3 0 * l * (t3 0)⁻¹ = l := fun l hl => by
          have h1 := cen_iff (hLC hl)
          calc t3 0 * l * (t3 0)⁻¹ = (l * t3 0) * (t3 0)⁻¹ := by rw [h1]
            _ = l := by group
        constructor
        · intro hh
          rw [hcomm h hh]
          exact hh
        · intro hh
          have hh' := hcomm _ hh
          have h3 : t3 0 * h * (t3 0)⁻¹ = h := by
            calc t3 0 * h * (t3 0)⁻¹
                = (t3 0)⁻¹ * (t3 0 * (t3 0 * h * (t3 0)⁻¹) * (t3 0)⁻¹) * t3 0 := by group
              _ = (t3 0)⁻¹ * (t3 0 * h * (t3 0)⁻¹) * t3 0 := by rw [hh']
              _ = h := by group
          rw [h3] at hh
          exact hh
    intro g hg l hl
    rw [← hNC] at hg
    exact (Subgroup.mem_normalizer_iff.1 (hNn hg) l).1 hl
  exact shapeRkAt_of_om (t3 0) (classData_core t3_classData.1) L e hLC hLn hCL

end ThreeA

end CFSG.HardMathSupport.Dickson.I271.TabFi23
