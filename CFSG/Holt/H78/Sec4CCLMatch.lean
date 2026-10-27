module

public import CFSG.Holt.H78.Sec4CCL
public import CFSG.Holt.H78.Lemma27Blocks
import CFSG.Holt.H78.KernelSplit
import CFSG.Holt.H78.Lemma27Real

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt Equiv

namespace HoltData

section Match

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X] (D : HoltData K X)
  {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {Λc : ι' → Type*} [∀ i, Fintype (Λc i)]
  [∀ i, DecidableEq (Λc i)] {ε : (∀ i, Λc i) → X} {α β : X}

abbrev boxSupport (ε : (∀ i, Λc i) → X) (j : D.ι) : Set ι' :=
  CCL.coordSupport fun x => D.coord (ε x) j

omit [Finite K] [Fintype ι'] [DecidableEq ι']
  [∀ i, Fintype (Λc i)] [∀ i, DecidableEq (Λc i)] in
theorem coord_box_smul {c : jHull K X} {y : ∀ i, Perm (Λc i)}
    (hc : ∀ x, (c : K) • ε x = ε fun i => y i (x i)) (x : ∀ i, Λc i) (j : D.ι) :
    D.coord (ε fun i => y i (x i)) j = D.ρ j c (D.coord (ε x) j) := by
  rw [← hc, D.coord_smul]

omit [Finite K] in
theorem coord_box_eq_iff (hbox : CCLBox K Λc ε α β) (j : D.ι) {x x' : ∀ i, Λc i} :
    D.coord (ε x) j = D.coord (ε x') j ↔ ∀ i ∈ D.boxSupport ε j, x i = x' i := by
  refine CCL.eq_iff_forall_mem_coordSupport (f := fun x => D.coord (ε x) j) hbox.odd_card
    hbox.five_le ?_
  intro y hy z z' h
  obtain ⟨c, hc, hcε⟩ := hbox.exists_smul_eq y hy
  have hcε' : ∀ x, ((⟨c, mem_jHull_of_mem_longInv hc.1⟩ : jHull K X) : K) • ε x =
      ε fun i => y i (x i) := hcε
  rw [D.coord_box_smul hcε', D.coord_box_smul hcε', h]

omit [Fintype ι'] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem coord_box_mem_holtDelta (hbox : CCLBox K Λc ε α β) (x : ∀ i, Λc i) (j : D.ι) :
    D.coord (ε x) j ∈ holtDelta (D.ρ j).range (D.Ψc j) (D.coord α j) (D.coord β j) :=
  D.coord_mem_holtDelta (hbox.mem_holtDelta x) j

omit [Fintype ι'] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem coord_box_eq_of_coord_eq (hbox : CCLBox K Λc ε α β) {j : D.ι}
    (hab : D.coord α j = D.coord β j) (x : ∀ i, Λc i) : D.coord (ε x) j = D.coord α j := by
  have h := D.coord_box_mem_holtDelta hbox x j
  rw [← hab, D.holtDelta_range_rho_self] at h
  exact h

omit [Fintype ι'] [∀ i, DecidableEq (Λc i)] in
theorem boxSupport_eq_empty_of_coord_eq (hbox : CCLBox K Λc ε α β) {j : D.ι}
    (hab : D.coord α j = D.coord β j) : D.boxSupport ε j = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro i ⟨x, μ, h⟩
  exact h ((D.coord_box_eq_of_coord_eq hbox hab _).trans
    (D.coord_box_eq_of_coord_eq hbox hab x).symm)

theorem boxSupport_eq_empty_of_isNaturalSE (hbox : CCLBox K Λc ε α β) {j : D.ι}
    (hSE : IsNaturalSE (D.M j)) (hab : D.coord α j ≠ D.coord β j) : D.boxSupport ε j = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro i hi
  obtain ⟨x⟩ := hbox.nonempty
  have hodd := hbox.odd_card
  obtain ⟨μ, hμ, -⟩ :=
    CCL.exists_ne_ne_of_three_le (by have := hbox.five_le i; omega) (x i) (x i)
  obtain ⟨y, hy, y', hy', -, hw⟩ :=
    CCL.exists_mem_longInvAt_perm_mul_mul_self_eq_one (hodd i) (hbox.five_le i) hμ
  obtain ⟨z, hz⟩ := CCL.exists_forall_mem_longInvAt hodd
    (fun k => by have := hbox.five_le k; omega) x
  obtain ⟨c, hc, hcε⟩ := hbox.exists_smul_eq _ fun k => (CCL.update_mem_longInvAt hz hy k).1
  obtain ⟨c', hc', hc'ε⟩ := hbox.exists_smul_eq _ fun k => (CCL.update_mem_longInvAt hz hy' k).1
  set u : jHull K X := ⟨c, mem_jHull_of_mem_longInv hc.1⟩
  set u' : jHull K X := ⟨c', mem_jHull_of_mem_longInv hc'.1⟩
  have huε : ∀ x, (u : K) • ε x = ε fun k => Function.update z i y k (x k) := hcε
  have hu'ε : ∀ x, (u' : K) • ε x = ε fun k => Function.update z i y' k (x k) := hc'ε
  have hP : D.ρ j u (D.coord (ε x) j) = D.coord (ε x) j := by
    rw [← D.coord_box_smul huε, CCL.apply_eq_self_of_forall_mem_longInvAt
      (CCL.update_mem_longInvAt hz hy)]
  have hP' : D.ρ j u' (D.coord (ε x) j) = D.coord (ε x) j := by
    rw [← D.coord_box_smul hu'ε, CCL.apply_eq_self_of_forall_mem_longInvAt
      (CCL.update_mem_longInvAt hz hy')]
  have hs := D.rho_mem_swapSet (u := u) hc j
  have hs' := D.rho_mem_swapSet (u := u') hc' j
  have hrange := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
  have haP : D.coord α j ≠ D.coord (ε x) j := by
    intro h
    have h1 := hs.2.2
    rw [h, hP, ← h] at h1
    exact hab h1
  have heq : D.ρ j u = D.ρ j u' := hSE.eq_of_mem_longInvAt_of_apply_eq (hrange ▸ hs.1)
    (hrange ▸ hs'.1) ⟨hs.2.1, hP⟩ ⟨hs'.2.1, hP'⟩ haP (by rw [hs.2.2, hs'.2.2])
  have key : ∀ q : Λc i, y q = y' q := by
    intro q
    have h1 : D.coord (ε fun k => Function.update z i y k (Function.update x i q k)) j =
        D.coord (ε fun k => Function.update z i y' k (Function.update x i q k)) j := by
      rw [D.coord_box_smul huε, D.coord_box_smul hu'ε, heq]
    have h2 := (D.coord_box_eq_iff hbox j).mp h1 i hi
    simpa using h2
  apply hw
  rw [Perm.mul_apply, key (y' μ), CCL.apply_apply_of_mem_longInv hy'.1]

omit [Fintype ι'] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem exists_box_of_forall_mem_swapSet (hbox : CCLBox K Λc ε α β) (w : ∀ l, Perm (D.Ψc l))
    (hw : ∀ l, w l ∈ swapSet (D.ρ l).range (D.coord α l) (D.coord β l)) :
    ∃ Y : ∀ i, Perm (Λc i), (∀ i, Y i ∈ longInv (Perm (Λc i)) (Λc i)) ∧
      ∀ x l, D.coord (ε fun i => Y i (x i)) l = w l (D.coord (ε x) l) := by
  obtain ⟨u, hu, hρ⟩ := D.exists_mem_longInvSwap_rho_eq w (fun l => (hw l).1)
    (fun l => (hw l).2.1) fun l => (hw l).2.2
  obtain ⟨Y, hY, hYε⟩ := hbox.smul_eq u hu
  exact ⟨Y, hY, fun x l => by rw [D.coord_box_smul hYε, hρ]⟩

omit [Fintype ι'] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem exists_forall_mem_swapSet (hbox : CCLBox K Λc ε α β) :
    ∃ s : ∀ l, Perm (D.Ψc l), ∀ l, s l ∈ swapSet (D.ρ l).range (D.coord α l) (D.coord β l) := by
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨t, ht, -⟩ := hbox.mem_holtDelta x
  exact ⟨fun l => D.ρ l ⟨t, mem_jHull_of_mem_longInv ht.1⟩, fun l => D.rho_mem_swapSet ht l⟩

theorem boxSupport_subsingleton_of_alternatingGroup (hbox : CCLBox K Λc ε α β) {j : D.ι}
    (hA : D.M j = alternatingGroup (D.Ψc j)) (hab : D.coord α j ≠ D.coord β j) :
    (D.boxSupport ε j).Subsingleton := by
  intro i₁ hi₁ i₂ hi₂
  by_contra hne
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨μ, hμ, -⟩ :=
    CCL.exists_ne_ne_of_three_le (by have := hbox.five_le i₂; omega) (x i₂) (x i₂)
  obtain ⟨ν, hν, -⟩ :=
    CCL.exists_ne_ne_of_three_le (by have := hbox.five_le i₁; omega) (x i₁) (x i₁)
  have hchar := fun z z' => D.coord_box_eq_iff hbox j (x := z) (x' := z')
  have hX : ∀ z, D.coord (ε z) j ≠ D.coord α j ∧ D.coord (ε z) j ≠ D.coord β j := by
    intro z
    have h := D.coord_box_mem_holtDelta hbox z j
    rw [D.holtDelta_range_rho_eq_compl hA hab] at h
    simpa [not_or] using h
  have hRP : D.coord (ε x) j ≠ D.coord (ε (Function.update x i₂ μ)) j := fun h => by
    have h1 := (hchar _ _).mp h i₂ hi₂
    rw [Function.update_self] at h1
    exact hμ h1.symm
  have hRQ : D.coord (ε x) j ≠ D.coord (ε (Function.update x i₁ ν)) j := fun h => by
    have h1 := (hchar _ _).mp h i₁ hi₁
    rw [Function.update_self] at h1
    exact hν h1.symm
  have hPQ : D.coord (ε (Function.update x i₂ μ)) j ≠
      D.coord (ε (Function.update x i₁ ν)) j := fun h => by
    have h1 := (hchar _ _).mp h i₁ hi₁
    rw [Function.update_of_ne hne, Function.update_self] at h1
    exact hν h1.symm
  obtain ⟨w, hw, hwa, hwP⟩ := exists_mem_longInvAt_perm_apply_eq_apply_eq (D.odd_card_Ψc j)
    hab (hX x).1.symm (hX _).1.symm (hX _).1.symm (hX x).2.symm (hX _).2.symm (hX _).2.symm
    hRP hRQ hPQ
  have hAle : alternatingGroup (D.Ψc j) ≤ (D.ρ j).range := by
    rw [← hA]
    exact Subgroup.map_le_range _ _
  have hwN : w ∈ (D.ρ j).range := longInv_perm_subset_of_alternatingGroup_le hAle
    ⟨D.tHull, rfl⟩ (D.rho_mem_longInv D.t_mem j) hw.1
  obtain ⟨s, hs⟩ := D.exists_forall_mem_swapSet hbox
  have hws : ∀ l, Function.update s j w l ∈
      swapSet (D.ρ l).range (D.coord α l) (D.coord β l) := by
    intro l
    by_cases hl : l = j
    · subst hl
      rw [Function.update_self]
      exact ⟨hwN, hw.1, hwa⟩
    · rw [Function.update_of_ne hl]
      exact hs l
  obtain ⟨Y, -, hY⟩ := D.exists_box_of_forall_mem_swapSet hbox _ hws
  have hwR : w (D.coord (ε x) j) = D.coord (ε x) j := hw.2
  have h1 : D.coord (ε fun i => Y i (x i)) j = D.coord (ε x) j := by
    rw [hY, Function.update_self, hwR]
  have h2 : D.coord (ε fun i => Y i (Function.update x i₂ μ i)) j =
      D.coord (ε (Function.update x i₁ ν)) j := by
    rw [hY, Function.update_self, hwP]
  have h3 := (hchar _ _).mp h1 i₁ hi₁
  have h4 := (hchar _ _).mp h2 i₁ hi₁
  simp only [Function.update_of_ne hne, Function.update_self] at h3 h4
  exact hν (h4.symm.trans h3)

theorem coord_ne_and_eq_alternatingGroup_of_mem_boxSupport (hbox : CCLBox K Λc ε α β)
    {k : D.ι} {i : ι'} (hi : i ∈ D.boxSupport ε k) :
    D.coord α k ≠ D.coord β k ∧ D.M k = alternatingGroup (D.Ψc k) ∧
      7 ≤ Fintype.card (D.Ψc k) := by
  have hab : D.coord α k ≠ D.coord β k := fun h => by
    rw [D.boxSupport_eq_empty_of_coord_eq hbox h] at hi
    exact hi
  rcases D.factor k with ⟨hA, h7⟩ | hSE
  · exact ⟨hab, hA, h7⟩
  · rw [D.boxSupport_eq_empty_of_isNaturalSE hbox hSE hab] at hi
    exact absurd hi (Set.notMem_empty i)

theorem eq_of_mem_boxSupport (hbox : CCLBox K Λc ε α β) {i : ι'} {j k : D.ι}
    (hj : i ∈ D.boxSupport ε j) (hk : i ∈ D.boxSupport ε k) : j = k := by
  by_contra hjk
  obtain ⟨habk, hAk, -⟩ := D.coord_ne_and_eq_alternatingGroup_of_mem_boxSupport hbox hk
  have hsing := D.boxSupport_subsingleton_of_alternatingGroup hbox hAk habk
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨μ, hμ, -⟩ :=
    CCL.exists_ne_ne_of_three_le (by have := hbox.five_le i; omega) (x i) (x i)
  have hPk : D.coord (ε (Function.update x i μ)) k ≠ D.coord (ε x) k := fun h => by
    have h1 := (D.coord_box_eq_iff hbox k).mp h i hk
    rw [Function.update_self] at h1
    exact hμ h1
  obtain ⟨wj, hwj, hwjR⟩ :=
    mem_holtDelta_subgroup_perm_iff.mp (D.coord_box_mem_holtDelta hbox x j)
  obtain ⟨wk, hwk, hwkP⟩ :=
    mem_holtDelta_subgroup_perm_iff.mp (D.coord_box_mem_holtDelta hbox (Function.update x i μ) k)
  obtain ⟨s, hs⟩ := D.exists_forall_mem_swapSet hbox
  have hww : ∀ l, Function.update (Function.update s j wj) k wk l ∈
      swapSet (D.ρ l).range (D.coord α l) (D.coord β l) := by
    intro l
    by_cases hlk : l = k
    · subst hlk
      rw [Function.update_self]
      exact hwk
    · rw [Function.update_of_ne hlk]
      by_cases hlj : l = j
      · subst hlj
        rw [Function.update_self]
        exact hwj
      · rw [Function.update_of_ne hlj]
        exact hs l
  obtain ⟨Y, -, hY⟩ := D.exists_box_of_forall_mem_swapSet hbox _ hww
  have h1 : D.coord (ε fun i => Y i (x i)) j = D.coord (ε x) j := by
    rw [hY, Function.update_of_ne hjk, Function.update_self]
    exact hwjR
  have h3 := (D.coord_box_eq_iff hbox j).mp h1 i hj
  apply hPk
  have h2 : wk (D.coord (ε x) k) = D.coord (ε x) k := by
    rw [← Function.update_self k wk (Function.update s j wj), ← hY]
    refine (D.coord_box_eq_iff hbox k).mpr fun l hl => ?_
    rw [hsing hl hk]
    exact h3
  exact hwk.2.1.2.unique hwkP h2

omit [Fintype ι'] in
theorem exists_mem_boxSupport (hK : IsStarGroup K X) (hbox : CCLBox K Λc ε α β) (i : ι') :
    ∃ j, i ∈ D.boxSupport ε j := by
  by_contra h
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨μ, hμ, -⟩ :=
    CCL.exists_ne_ne_of_three_le (by have := hbox.five_le i; omega) (x i) (x i)
  have hc : D.coord (ε x) = D.coord (ε (Function.update x i μ)) := funext fun j =>
    (CCL.apply_update_eq_of_notMem_coordSupport (not_exists.mp h j) x μ).symm
  have h1 := congrFun (hbox.eq_of_mem_orbit hK ((D.coord_eq_iff _ _).mp hc)) i
  rw [Function.update_self] at h1
  exact hμ h1.symm

omit [Fintype ι'] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)] in
theorem exists_coord_box_eq (hbox : CCLBox K Λc ε α β) {j : D.ι} {P : D.Ψc j}
    (hP : P ∈ holtDelta (D.ρ j).range (D.Ψc j) (D.coord α j) (D.coord β j)) :
    ∃ z, D.coord (ε z) j = P := by
  obtain ⟨x⟩ := hbox.nonempty
  have hmem : Function.update (D.coord (ε x)) j P ∈ Set.univ.pi fun l =>
      holtDelta (D.ρ l).range (D.Ψc l) (D.coord α l) (D.coord β l) := by
    rw [Set.mem_univ_pi]
    intro l
    by_cases hl : l = j
    · subst hl
      rw [Function.update_self]
      exact hP
    · rw [Function.update_of_ne hl]
      exact D.coord_box_mem_holtDelta hbox x l
  rw [← D.coord_holtDelta_eq, ← hbox.range_eq] at hmem
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hmem
  exact ⟨z, by rw [hz, Function.update_self]⟩

theorem card_Ψc_eq_of_mem_boxSupport (hbox : CCLBox K Λc ε α β) {i : ι'} {j : D.ι}
    (hi : i ∈ D.boxSupport ε j) : Fintype.card (D.Ψc j) = Fintype.card (Λc i) + 2 := by
  obtain ⟨hab, hA, h7⟩ := D.coord_ne_and_eq_alternatingGroup_of_mem_boxSupport hbox hi
  have hsing := D.boxSupport_subsingleton_of_alternatingGroup hbox hA hab
  obtain ⟨x⟩ := hbox.nonempty
  have hinj : Function.Injective fun q : Λc i => D.coord (ε (Function.update x i q)) j := by
    intro q q' h
    have h1 := (D.coord_box_eq_iff hbox j).mp h i hi
    simpa using h1
  have himage : Finset.univ.image (fun q : Λc i => D.coord (ε (Function.update x i q)) j) =
      ({D.coord α j, D.coord β j} : Finset (D.Ψc j))ᶜ := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨q, rfl⟩
      have h := D.coord_box_mem_holtDelta hbox (Function.update x i q) j
      rw [D.holtDelta_range_rho_eq_compl hA hab] at h
      simpa [not_or] using h
    · rintro ⟨hPa, hPb⟩
      have hP : P ∈ holtDelta (D.ρ j).range (D.Ψc j) (D.coord α j) (D.coord β j) := by
        rw [D.holtDelta_range_rho_eq_compl hA hab]
        simp [hPa, hPb]
      obtain ⟨z, hz⟩ := D.exists_coord_box_eq hbox hP
      refine ⟨z i, ?_⟩
      rw [← hz]
      refine (D.coord_box_eq_iff hbox j).mpr fun l hl => ?_
      rw [hsing hl hi, Function.update_self]
  have hcard := Finset.card_image_of_injective Finset.univ hinj
  rw [himage, Finset.card_compl, Finset.card_pair hab, Finset.card_univ] at hcard
  omega

theorem exists_ne_mem_holtDelta_range_rho {k : D.ι} {a b : D.Ψc k} (hab : a ≠ b) :
    ∃ P ∈ holtDelta (D.ρ k).range (D.Ψc k) a b,
      ∃ P' ∈ holtDelta (D.ρ k).range (D.Ψc k) a b, P ≠ P' := by
  rcases D.factor k with ⟨hA, h7⟩ | hSE
  · rw [D.holtDelta_range_rho_eq_compl hA hab]
    obtain ⟨P, hPa, hPb⟩ := CCL.exists_ne_ne_of_three_le (by omega) a b
    obtain ⟨P', hP'a, hP'b, hP'P⟩ := CCL.exists_ne_ne_ne_of_four_le (by omega) a b P
    exact ⟨P, by simp [hPa, hPb], P', by simp [hP'a, hP'b], hP'P.symm⟩
  · obtain ⟨n, i, e, hA⟩ := hSE.exists_isBenderAction
    have hrange := D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor
    have hset : holtDelta (D.ρ k).range (D.Ψc k) a b = holtDelta (D.M k) (D.Ψc k) a b := by
      ext c
      rw [mem_holtDelta_subgroup_perm_iff, mem_holtDelta_subgroup_perm_iff, hrange]
    have h1 : 1 < (holtDelta (D.M k) (D.Ψc k) a b).ncard := by
      rw [hA.ncard_holtDelta hab]
      have := hA.four_le_q
      omega
    obtain ⟨P, P', hP, hP', hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1
    rw [hset]
    exact ⟨P, hP, P', hP', hne⟩

theorem coord_eq_of_boxSupport_eq_empty (hbox : CCLBox K Λc ε α β) {k : D.ι}
    (hk : D.boxSupport ε k = ∅) :
    D.coord α k = D.coord β k ∧ ∀ x, D.coord (ε x) k = D.coord α k := by
  have hconst : ∀ x x', D.coord (ε x) k = D.coord (ε x') k := fun x x' =>
    (D.coord_box_eq_iff hbox k).mpr fun i hi => by
      rw [hk] at hi
      exact absurd hi (Set.notMem_empty i)
  have hab : D.coord α k = D.coord β k := by
    by_contra hab
    obtain ⟨P, hP, P', hP', hne⟩ := D.exists_ne_mem_holtDelta_range_rho hab
    obtain ⟨z, rfl⟩ := D.exists_coord_box_eq hbox hP
    obtain ⟨z', rfl⟩ := D.exists_coord_box_eq hbox hP'
    exact hne (hconst z z')
  exact ⟨hab, D.coord_box_eq_of_coord_eq hbox hab⟩

end Match

section Main

variable {K : Type} [Group K] [Finite K] {X : Type} [MulAction K X] [Finite X]
  [FaithfulSMul K X]

@[nolint unusedArguments]
theorem ccl (hK : IsStarGroup K X)
    (hB : HoltTheorem1Below (Nat.card K) (Nat.card X + 1)) (D : HoltData K X) {α β : X}
    (_hαβ : α ≠ β) {ι' : Type} [Fintype ι'] {Λc : ι' → Type} [∀ i, Fintype (Λc i)]
    [∀ i, DecidableEq (Λc i)] (e : holtDelta K X α β ≃ ∀ i, Λc i)
    (h5 : ∀ i, 5 ≤ Fintype.card (Λc i))
    (hcoord : ∀ c ∈ longInvSwap K X α β, ∃ y : ∀ i, Equiv.Perm (Λc i),
      (∀ i, y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) ∧ ∀ δ δ' : holtDelta K X α β,
        (δ' : X) = c • (δ : X) → e δ' = fun i => y i (e δ i))
    (hreal : ∀ y : ∀ i, Equiv.Perm (Λc i), (∀ i, y i ∈ longInv (Equiv.Perm (Λc i)) (Λc i)) →
      ∃ c ∈ longInvSwap K X α β, ∀ δ : holtDelta K X α β, ∀ δ' : holtDelta K X α β,
        (δ' : X) = c • (δ : X) → e δ' = fun i => y i (e δ i)) :
    ∃ c : ι' → D.ι, Function.Injective c ∧
      (∀ i, factorImage K X (D.L (c i)) (D.ρ (c i)) = alternatingGroup (D.Ψc (c i)) ∧
        Fintype.card (D.Ψc (c i)) = Fintype.card (Λc i) + 2 ∧
        D.coord α (c i) ≠ D.coord β (c i) ∧
        ∀ δ δ' : holtDelta K X α β, (D.coord δ (c i) = D.coord δ' (c i) ↔ e δ i = e δ' i) ∧
          D.coord δ (c i) ≠ D.coord α (c i) ∧ D.coord δ (c i) ≠ D.coord β (c i)) ∧
      (∀ k, k ∉ Set.range c → ∀ δ : holtDelta K X α β,
        D.coord δ k = D.coord α k ∧ D.coord β k = D.coord α k) ∧
      (Odd (Nat.card ↥(stabilizer K α ⊓ stabilizer K β ⊓
        fixingSubgroup K (holtDelta K X α β))) → Set.range c = Set.univ) := by
  classical
  have hbox := CCLBox.of_equiv (e := e) h5 hcoord hreal
  set ε : (∀ i, Λc i) → X := fun x => (e.symm x : X) with hεdef
  have hεδ : ∀ δ : holtDelta K X α β, ε (e δ) = δ := fun δ => by simp [hεdef]
  choose σ hσ using D.exists_mem_boxSupport hK hbox
  have hinj : Function.Injective σ := fun i i' h => by
    have h1 := hσ i
    rw [h] at h1
    obtain ⟨hab, hA, -⟩ := D.coord_ne_and_eq_alternatingGroup_of_mem_boxSupport hbox (hσ i')
    exact D.boxSupport_subsingleton_of_alternatingGroup hbox hA hab h1 (hσ i')
  have hpar : ∀ k, k ∉ Set.range σ → D.boxSupport ε k = ∅ := by
    intro k hk
    rw [Set.eq_empty_iff_forall_notMem]
    intro i hi
    exact hk ⟨i, D.eq_of_mem_boxSupport hbox (hσ i) hi⟩
  refine ⟨σ, hinj, fun i => ?_, fun k hk δ => ?_, fun hodd => ?_⟩
  · obtain ⟨hab, hA, -⟩ := D.coord_ne_and_eq_alternatingGroup_of_mem_boxSupport hbox (hσ i)
    have hsing := D.boxSupport_subsingleton_of_alternatingGroup hbox hA hab
    refine ⟨hA, D.card_Ψc_eq_of_mem_boxSupport hbox (hσ i), hab, fun δ δ' => ⟨?_, ?_⟩⟩
    · rw [← hεδ δ, ← hεδ δ', D.coord_box_eq_iff hbox]
      refine ⟨fun h => h i (hσ i), fun h l hl => ?_⟩
      rw [hsing hl (hσ i)]
      exact h
    · have h := D.coord_box_mem_holtDelta hbox (e δ) (σ i)
      rw [hεδ, D.holtDelta_range_rho_eq_compl hA hab] at h
      simpa [not_or] using h
  · obtain ⟨hab, hx⟩ := D.coord_eq_of_boxSupport_eq_empty hbox (hpar k hk)
    refine ⟨?_, hab.symm⟩
    rw [← hεδ δ]
    exact hx _
  · by_contra hne
    obtain ⟨k, hk⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hne
    obtain ⟨hab, hx⟩ := D.coord_eq_of_boxSupport_eq_empty hbox (hpar k hk)
    obtain ⟨v, hvL, hv2, hva, hvj⟩ := D.exists_mem_L_orderOf_eq_two k (D.coord α k)
    have hstab : ∀ ω, D.coord ω k = D.coord α k → (v : K) • ω = ω := by
      intro ω hω
      have hc : D.coord ω = D.coord ((v : K) • ω) := funext fun l => by
        rw [D.coord_smul]
        by_cases hl : l = k
        · subst hl
          rw [hω, hva]
        · rw [hvj l hl, Equiv.Perm.one_apply]
      exact (D.lemma_2_4_iv hK hB v.2 (by rw [Subgroup.orderOf_coe, hv2])
        ((D.coord_eq_iff _ _).mp hc)).1 (D.L_le_socPre k hvL) ω (mem_orbit_self ω)
    have hfix : (v : K) ∈ fixingSubgroup K (holtDelta K X α β) := by
      rw [mem_fixingSubgroup_iff]
      intro γ hγ
      rw [← hbox.range_eq] at hγ
      obtain ⟨x, rfl⟩ := hγ
      exact hstab _ (hx x)
    have hvmem : (v : K) ∈ stabilizer K α ⊓ stabilizer K β ⊓
        fixingSubgroup K (holtDelta K X α β) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hstab α rfl, hstab β hab.symm⟩, hfix⟩
    have h2 := Subgroup.orderOf_dvd_natCard _ hvmem
    rw [Subgroup.orderOf_coe, hv2] at h2
    obtain ⟨m, hm⟩ := hodd
    omega

end Main

end HoltData

end CFSG.Holt.H78
