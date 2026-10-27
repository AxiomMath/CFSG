module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwCen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Quasithin.H13.U43 CFSG.KGroups.U43 Certificates.Asc82Swap

private lemma sw_commB_iff {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (hu : Rep n u h) : commB n t u = true ↔ g * h = h * g := by
  rw [commB, eqA_iff (rep_compA ht hu) (rep_compA hu ht)]

private lemma sw_map_conjArr_getElem {O Oi O1 : Array (Array ℕ)} {a : ℕ} (ha : a < O1.size) :
    (O1.map (conjArr 820 O Oi))[a]! = conjArr 820 O Oi O1[a]! := by
  rw [getElem!_pos _ a (by simpa using ha), Array.getElem_map, getElem!_pos O1 a ha]

private lemma sw_size_filter_eq_count_range {α : Type*} [Inhabited α] (T : Array α) (p : α → Bool) :
    (T.filter p).size = ((List.range T.size).filter (fun k => p T[k]!)).length := by
  have hmap : (List.range T.size).map (fun k => T[k]!) = T.toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [getElem!_pos T i (by simpa using h1)]
      simp
  rw [← Array.countP_eq_size_filter, ← Array.countP_toList, List.countP_eq_length_filter]
  rw [← hmap, List.filter_map, List.length_map]
  rfl

private lemma sw_length_filter_range_ncard (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = ({d : ℕ | d < n ∧ p d = true} : Set ℕ).ncard := by
  have hset : ({d : ℕ | d < n ∧ p d = true} : Set ℕ) =
      ↑((Finset.range n).filter fun d => p d = true) := by
    ext d
    simp
  rw [hset, Set.ncard_coe_finset]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  simp

private lemma sw_size_filter_eq_ncard {α : Type*} [Inhabited α] (T : Array α) (p : α → Bool) :
    (T.filter p).size = ({i : ℕ | i < T.size ∧ p T[i]! = true} : Set ℕ).ncard := by
  rw [sw_size_filter_eq_count_range, sw_length_filter_range_ncard]

theorem sw_orderOf_xElt_of_check (h : swapTCheck 820 tabA tabB = true) : orderOf xElt = 2 := by
  unfold swapTCheck at h
  simp only [Bool.and_eq_true] at h
  exact CFSG.Quasithin.H13.U43.orderOf_xElt_of_eqA h.1.2

theorem sw_tables_of_check
    (h : swapTCheck 820 tabA tabB = true) : SwTables := by
  rw [SwTables]
  intro g₁ hg₁C g₂ hg₂C hodd₁ hodd₂ hne₁ hne₂ hg₁cen hg₂cen
  unfold swapTCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hLi, hOi⟩, hA⟩, hT⟩ := h
  set L : Array (Array ℕ) := elemList 820 tabA tabB with hLdef
  set Li : Array (Array ℕ) := invArrs 820 L with hLidef
  set O : Array (Array ℕ) := oddList 820 L with hOdef
  set Oi : Array (Array ℕ) := invArrs 820 O with hOidef
  set O1 : Array (Array ℕ) := oddNe 820 O (idA 820) with hO1def
  set CT : Array (Array (Array ℕ)) := O1.map (conjArr 820 O Oi) with hCTdef
  have hL : SwCover L (SwC : Set X₀) := by rw [hLdef]; exact (sw_elemList_enum).cover
  have hO : SwCover O {o | o ∈ SwC ∧ Odd (orderOf o)} := by
    rw [hOdef, hLdef]; exact sw_oddList_cover
  have hO1 : SwCover O1 {o | o ∈ SwC ∧ Odd (orderOf o) ∧ o ≠ 1} := by
    rw [hO1def, hOdef, hLdef]; exact sw_oddNe_cover
  obtain ⟨a, ha, harep⟩ := hO1.2 g₁ ⟨hg₁C, hodd₁, hne₁⟩
  obtain ⟨b, hb, hbrep⟩ := hO1.2 g₂ ⟨hg₂C, hodd₂, hne₂⟩
  have hcen1 : cenB 820 CT[b]! O1[a]! = true := by
    rw [hCTdef, sw_map_conjArr_getElem hb]
    exact (sw_cenB_iff hO hOi hbrep harep).2 (fun o ho hodd => hg₁cen.2 o ho hodd)
  have hcen2 : cenB 820 CT[a]! O1[b]! = true := by
    rw [hCTdef, sw_map_conjArr_getElem ha]
    exact (sw_cenB_iff hO hOi harep hbrep).2 (fun o ho hodd => hg₂cen.2 o ho hodd)
  have hspec := allLt_spec (allLt_spec hT ha) hb
  rw [hcen1, hcen2] at hspec
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hspec
  obtain ⟨ht1, ht2⟩ := hspec
  rw [hCTdef, sw_map_conjArr_getElem ha, sw_map_conjArr_getElem hb] at ht1 ht2
  refine ⟨?_, ?_⟩
  · intro hh hh1 hh2
    exact sw_t1_sound hL hO hOi harep hbrep (by rw [map_one]; exact rep_idA) rep_tabA ht1 hh hh1 hh2
  · exact sw_t2_sound hL hLi hO hOi harep hbrep ht2

theorem sw_oddCent_of_check
    (h : oddCentCheck 820 tabA tabB = true) : SwOddCent := by
  rw [SwOddCent]
  intro y hyC hyodd hyne P hP2 hPC hPcen
  unfold oddCentCheck at h
  simp only [oddCentAux] at h
  set L : Array (Array ℕ) := elemList 820 tabA tabB with hLdef
  set O : Array (Array ℕ) := oddList 820 L with hOdef
  set O1 : Array (Array ℕ) := oddNe 820 O (idA 820) with hO1def
  have hO1 : SwCover O1 {o | o ∈ SwC ∧ Odd (orderOf o) ∧ o ≠ 1} := by
    rw [hO1def, hOdef, hLdef]; exact sw_oddNe_cover
  obtain ⟨a, ha, harep⟩ := hO1.2 y ⟨hyC, hyodd, hyne⟩
  have hcount : (L.filter (fun h => commB 820 O1[a]! h)).size % 16 ≠ 0 := by
    have hspec := allLt_spec h ha
    simpa [bne_iff_ne] using hspec
  obtain ⟨f, hf, hinj, himg⟩ :=
    show SwEnum L (SwC : Set X₀) from by rw [hLdef]; exact sw_elemList_enum
  have hcomm_iff : ∀ (i : ℕ) (hi : i < L.size),
      commB 820 O1[a]! L[i]! = true ↔ y * f i = f i * y := by
    intro i hi
    rw [sw_commB_iff harep (hf i hi), ← map_mul, ← map_mul,
      CFSG.Quasithin.H13.U43.psi_inj.eq_iff]
  have hcard : (L.filter (fun h => commB 820 O1[a]! h)).size
      = ((SwC ⊓ Subgroup.centralizer ({y} : Set X₀) : Subgroup X₀) : Set X₀).ncard := by
    rw [sw_size_filter_eq_ncard]
    have himage : (fun i : ℕ => f i) ''
        {i : ℕ | i < L.size ∧ commB 820 O1[a]! L[i]! = true}
        = (↑(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) : Set X₀) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hxSwC : f i ∈ SwC := by
          have h2 : f i ∈ f '' Set.Iio L.size := ⟨i, hi.1, rfl⟩
          rw [himg] at h2
          exact h2
        refine Subgroup.mem_inf.mpr ⟨hxSwC, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hcomm_iff i hi.1).1 hi.2
      · intro hx
        obtain ⟨hxSwC, hxcen⟩ := Subgroup.mem_inf.mp hx
        have hxSwC' : x ∈ f '' Set.Iio L.size := by rw [himg]; exact hxSwC
        obtain ⟨i, hi, hfi⟩ := hxSwC'
        refine ⟨i, ⟨hi, ?_⟩, hfi⟩
        rw [hcomm_iff i hi, hfi]
        exact (Subgroup.mem_centralizer_iff.mp hxcen) y (Set.mem_singleton y)
    rw [← himage]
    exact (Set.InjOn.ncard_image (s := {i : ℕ | i < L.size ∧ commB 820 O1[a]! L[i]! = true})
      (hinj.mono (fun i hi => hi.1))).symm
  by_contra hge
  rw [not_lt] at hge
  have hPle : P ≤ SwC ⊓ Subgroup.centralizer ({y} : Set X₀) := by
    refine le_inf hPC ?_
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hPcen p hp).symm
  have hdvd : Nat.card P ∣ Nat.card ↥(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) :=
    Subgroup.card_dvd_of_le hPle
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hP2
  have hk4 : 4 ≤ k := by
    have h2 : 2 ^ 4 ≤ 2 ^ k := by rw [← hk]; simpa using hge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  have h16P : 16 ∣ Nat.card P := by
    rw [hk]; simpa using Nat.pow_dvd_pow 2 hk4
  have h16S : 16 ∣ Nat.card ↥(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) :=
    dvd_trans h16P hdvd
  have h16size : 16 ∣ (L.filter (fun h => commB 820 O1[a]! h)).size := by
    rw [hcard, ← Nat.card_coe_set_eq]
    exact h16S
  exact hcount (Nat.mod_eq_zero_of_dvd h16size)

end CFSG.OddStandard.SmallF3.Omega
