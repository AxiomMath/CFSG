module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerTwo

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover (xr RootPair f4Len f4Ip)
open CFSG.LieType.Ree (ReeTag)
open scoped commutatorElement

@[expose] def f4MidJ : Set (Fin Tag.F4.rank) := {i | (i : ℕ) = 1 ∨ (i : ℕ) = 2}

@[expose] def f4MidRadical : List ℕ := [24, 26, 29, 31, 32] ++ List.range' 33 15

@[expose] def f4MidParabolic : List ℕ := f4MidRadical ++ [25, 27, 28, 30, 22, 20, 19, 17]

@[expose] def f4MidDeriv : List (ℕ × ℕ × ℕ × ℕ) :=
  [(36, 24, 35, 0), (44, 24, 43, 0), (26, 24, 25, 0), (29, 24, 28, 0), (38, 26, 35, 0),
    (31, 26, 28, 0), (24, 26, 22, 0), (41, 29, 35, 0), (43, 31, 35, 0), (39, 32, 33, 0),
    (42, 32, 34, 0), (47, 32, 35, 44), (45, 32, 37, 0), (46, 32, 40, 0), (34, 33, 27, 0),
    (37, 33, 30, 0), (35, 34, 25, 37), (40, 34, 30, 0), (33, 34, 20, 0), (32, 27, 26, 29)]

@[expose] def f4MidKillOrder : List ℕ :=
  [25, 28, 30, 35, 37, 40, 43, 27, 34, 41, 33, 38, 36, 29, 31, 32, 46, 26, 45, 24, 42, 39]

@[expose] def f4MidKillRows : List (ℕ × ℕ) :=
  [(26, 24), (29, 24), (31, 24), (36, 24), (38, 24), (41, 24), (44, 24), (29, 26), (36, 26),
    (44, 26), (36, 29), (44, 29), (44, 31), (36, 33), (38, 33), (39, 33), (47, 33), (36, 34),
    (47, 34), (36, 35), (47, 37), (47, 40)]

@[expose] def f4KOSupport (KO : List ℕ) (n : ℕ) : List ℕ :=
  f4PosList.filter fun i => decide (i ∉ KO.take n)

@[expose] def f4KillOK (KO : List ℕ) (rows : List (ℕ × ℕ)) : Bool :=
  (List.range KO.length).all fun n =>
    f4RowOK (rows.getD n (0, 0)).1 (f4KOSupport KO n) [(rows.getD n (0, 0)).2] &&
      (f4Contribs (rows.getD n (0, 0)).1 (f4KOSupport KO n) [(rows.getD n (0, 0)).2] ==
        [(KO.getD n 0, 1, (rows.getD n (0, 0)).2, 1)])

theorem f4Mid_check :
    f4DerivOK f4MidRadical f4MidParabolic [] f4MidDeriv = true ∧
      (∀ p ∈ f4MidRadical, p ∈ f4MidDeriv.map Prod.fst) ∧
      (∀ p ∈ f4MidRadical, p ∈ f4MidParabolic) ∧
      (∀ p ∈ f4MidParabolic, p < 48 ∧ (p = 47 ∨ f4CommuteRule p 47 = true) ∧
        (p = 44 ∨ f4CommuteRule p 44 = true)) ∧
      (∀ p ∈ f4MidRadical, 24 ≤ p ∧ p ≤ 47 ∧
        ∃ i : Fin Tag.F4.rank, ¬((i : ℕ) = 1 ∨ (i : ℕ) = 2) ∧ orbitCertRoot .F4 p i ≠ 0) ∧
      (∀ p ∈ f4PosList, p ∉ f4MidRadical →
        ∀ i : Fin Tag.F4.rank, ((i : ℕ) = 1 ∨ (i : ℕ) = 2) ∨ orbitCertRoot .F4 p i = 0) ∧
      f4KillOK f4MidKillOrder f4MidKillRows = true ∧
      (∀ n < f4MidKillOrder.length, (f4MidKillRows.getD n (0, 0)).2 ∈ f4MidRadical) ∧
      (∀ i ∈ f4PosList, decide (i = 44 ∨ i = 47) = false → i ∈ f4MidKillOrder) := by
  decide +kernel

theorem dualRoot_mem_parabolicRadicalRoots_mid : ∀ p ∈ f4MidRadical,
    ∃ q ∈ f4MidRadical, List.ofFn (ReeTag.F4.dualRoot (orbitCertRoot .F4 p)) =
      List.ofFn (orbitCertRoot .F4 q) := by
  decide +kernel


variable {K : Type} [Field K]

theorem orbitCertRoot_mem_parabolicRadicalRoots_mid_iff {p : ℕ} (hp : 24 ≤ p ∧ p ≤ 47) :
    orbitCertRoot .F4 p ∈ parabolicRadicalRoots .F4 f4MidJ ↔ p ∈ f4MidRadical := by
  obtain ⟨-, -, -, -, hR, hnR, -⟩ := f4Mid_check
  rw [mem_parabolicRadicalRoots_iff]
  constructor
  · rintro ⟨-, -, i, hi, hne⟩
    by_contra hp'
    rcases hnR p (List.mem_ofFn.2 ⟨⟨p - 24, by omega⟩, by simp; omega⟩) hp' i with h | h
    · exact hi h
    · exact hne h
  · intro hp'
    obtain ⟨-, -, i, hi, hne⟩ := hR p hp'
    exact ⟨(f4_isRoot_pos hp).1, (f4_isRoot_pos hp).2, i, hi, hne⟩

theorem f4x_mem_parabolicRadical_mid {p : ℕ} (hp : p ∈ f4MidRadical) (c : K) :
    f4x K p c ∈ parabolicRadical .F4 K f4MidJ := by
  obtain ⟨-, -, -, -, hR, -⟩ := f4Mid_check
  obtain ⟨h1, h2, -⟩ := hR p hp
  exact pinnedX_mem_rootSpan ((orbitCertRoot_mem_parabolicRadicalRoots_mid_iff ⟨h1, h2⟩).2 hp) c

theorem mem_of_mem_parabolicRadical_mid_of_forall_xr (hK : Nat.card K = 2)
    {H : Subgroup (adjointGroup .F4 K)}
    (h : ∀ p ∈ f4MidRadical, xr (K := K) (orbitCertRoot .F4 p) ∈ H)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ parabolicRadical .F4 K f4MidJ) : u ∈ H := by
  have hle : parabolicRadical .F4 K f4MidJ ≤ H.map (adjointGroup .F4 K).subtype := by
    rw [parabolicRadical, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨β, hβ, d, rfl⟩
    obtain ⟨p, hp, hp', rfl⟩ :=
      (f4_even_positive_root_commutator_table.{0}.1 β).1 ⟨(mem_parabolicRadicalRoots_iff.1 hβ).1,
        (mem_parabolicRadicalRoots_iff.1 hβ).2.1⟩
    have hpR := (orbitCertRoot_mem_parabolicRadicalRoots_mid_iff ⟨hp, hp'⟩).1 hβ
    rcases eq_zero_or_eq_one_of_card_eq_two hK d with rfl | rfl
    · rw [pinnedX_zero]
      exact one_mem _
    · exact ⟨_, h p hpR, rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  rwa [show u = x from Subtype.ext hxu.symm]

theorem parabolicRadical_mid_le_closure_odd [Finite K] (hK : Nat.card K = 2)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ parabolicRadical .F4 K f4MidJ) :
    u ∈ closure {c : adjointGroup .F4 K |
      c * (xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44)) =
        (xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44)) * c ∧ Odd (orderOf c)} := by
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hder, hcov, hsub, hcomm, -⟩ := f4Mid_check
  set A : Subgroup (adjointGroup .F4 K) :=
    closure ((fun p => xr (K := K) (orbitCertRoot .F4 p)) '' {p | p ∈ f4MidRadical}) with hA
  set P : Subgroup (adjointGroup .F4 K) :=
    closure ((fun p => xr (K := K) (orbitCertRoot .F4 p)) '' {p | p ∈ f4MidParabolic}) with hP
  have hgenA : ∀ p ∈ f4MidRadical, xr (K := K) (orbitCertRoot .F4 p) ∈ A :=
    fun p hp => subset_closure ⟨p, hp, rfl⟩
  have hgenP : ∀ p ∈ f4MidParabolic, xr (K := K) (orbitCertRoot .F4 p) ∈ P :=
    fun p hp => subset_closure ⟨p, hp, rfl⟩
  have hAP : A ≤ P := by
    rw [hA, closure_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hgenP p (hsub p hp)
  have hPt : ∀ x ∈ P, x * (xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44)) =
      (xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44)) * x := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨hp48, h47, h44⟩ := hcomm p hp
      have c47 : Commute (xr (K := K) (orbitCertRoot .F4 p)) (xr (orbitCertRoot .F4 47)) := by
        rcases h47 with h | h
        · rw [h]
        · exact f4_commute_sound hK hp48 (by norm_num) h
      have c44 : Commute (xr (K := K) (orbitCertRoot .F4 p)) (xr (orbitCertRoot .F4 44)) := by
        rcases h44 with h | h
        · rw [h]
        · exact f4_commute_sound hK hp48 (by norm_num) h
      exact (c47.mul_right c44).eq
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy => exact (Commute.mul_left (hx : Commute x _) hy).eq
    | inv x _ hx => exact (Commute.inv_left (hx : Commute x _)).eq
  have hcomA : A ≤ ⁅A, P⁆ := by
    rw [hA, closure_le]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (hcov p hp)
    exact f4_deriv_sound hK hgenA hgenP f4MidDeriv [] (by simp) hder s hs
  exact le_closure_odd_of_le_commutator hAP (fun x hx => hPt x hx) hcomA
    (mem_of_mem_parabolicRadical_mid_of_forall_xr hK hgenA hu)

theorem f4_kill_sound [Finite K] [CharP K 2] {KO : List ℕ} {rows : List (ℕ × ℕ)}
    (hok : f4KillOK KO rows = true) (c : ℕ → K)
    (hcomm : ∀ n < KO.length,
      ⁅(f4PosList.map fun i => f4x K i (c i)).prod, f4x K (rows.getD n (0, 0)).2 1⁆ = 1) :
    ∀ j ∈ KO, c j = 0 := by
  have key : ∀ n ≤ KO.length, ∀ j ∈ KO.take n, c j = 0 := by
    intro n
    induction n with
    | zero => intro _ j hj; simp at hj
    | succ n ih =>
      intro hn
      have hD := ih (by omega)
      have hrow := (List.all_eq_true.1 hok) n (List.mem_range.2 (by omega))
      rw [Bool.and_eq_true, beq_iff_eq] at hrow
      have hw : ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
          ([(rows.getD n (0, 0)).2].map fun p => f4x K p ((fun _ => (1 : K)) p)).prod⁆ = 1 := by
        simpa using hcomm n (by omega)
      rw [← list_prod_map_filter_of_eq_one f4PosList (fun i => decide (i ∉ KO.take n)) _
        (fun i _ hi => by
          simp only [decide_eq_false_iff_not, not_not] at hi
          rw [hD i hi, f4x_zero])] at hw
      have h := f4_row hrow.1 c (fun _ => 1) hw
      rw [hrow.2] at h
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_one, one_pow,
        mul_one, add_zero] at h
      intro j hj
      rw [List.take_add_one, List.mem_append] at hj
      rcases hj with hj | hj
      · exact hD j hj
      · simp only [Option.mem_toList] at hj
        rw [List.getD_eq_getElem?_getD, hj, Option.getD_some] at h
        exact h
  intro j hj
  exact key KO.length le_rfl j (by rw [List.take_length]; exact hj)

theorem f4x_44_mul_f4x_47_sq [CharP K 2]
    (c d : K) : (f4x K 44 c * f4x K 47 d) ^ 2 = 1 := by
  have hcomm : f4x K 44 c * f4x K 47 d = f4x K 47 d * f4x K 44 c :=
    f4x_central (Or.inr rfl) d (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ c)
  rw [sq, show f4x K 44 c * f4x K 47 d * (f4x K 44 c * f4x K 47 d) =
      (f4x K 44 c * f4x K 44 c) * (f4x K 47 d * f4x K 47 d) by
    rw [mul_assoc, ← mul_assoc (f4x K 47 d), ← hcomm]; group]
  simp only [f4x, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero, mul_one]

theorem exists_of_commute_parabolicRadical_mid [Finite K] [CharP K 2] {z : ModGL .F4 K}
    (hz : z ∈ parabolicRadical .F4 K f4MidJ)
    (hc : ∀ p ∈ f4MidRadical, z * f4x K p 1 = f4x K p 1 * z) :
    ∃ c d : K, f4x K 44 c * f4x K 47 d = z := by
  obtain ⟨-, -, -, -, -, -, hkill, hrows, hcover⟩ := f4Mid_check
  obtain ⟨c, rfl⟩ := exists_f4_coords (parabolicRadical_le_posUnipotent f4MidJ hz)
  have h0 := f4_kill_sound hkill c fun n hn => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hc _ (hrows n hn)
  refine ⟨c 44, c 47, ?_⟩
  rw [← list_prod_map_filter_of_eq_one f4PosList (fun i => decide (i = 44 ∨ i = 47)) _
    (fun i hi hne => by rw [h0 i (hcover i hi hne), f4x_zero]),
    show f4PosList.filter (fun i => decide (i = 44 ∨ i = 47)) = [44, 47] by decide]
  simp

theorem sq_eq_one_of_commute_parabolicRadical_mid [Finite K] [CharP K 2] {z : ModGL .F4 K}
    (hz : z ∈ parabolicRadical .F4 K f4MidJ)
    (hc : ∀ p ∈ f4MidRadical, z * f4x K p 1 = f4x K p 1 * z) : z ^ 2 = 1 := by
  obtain ⟨c, d, rfl⟩ := exists_of_commute_parabolicRadical_mid hz hc
  exact f4x_44_mul_f4x_47_sq c d

theorem dualRoot_mem_parabolicRadicalRoots_mid' {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots .F4 f4MidJ) :
    IsRoot ReeTag.F4.tag α ∧ ReeTag.F4.dualRoot α ∈ parabolicRadicalRoots .F4 f4MidJ := by
  obtain ⟨p, hp, hp', rfl⟩ :=
    (f4_even_positive_root_commutator_table.{0}.1 α).1 ⟨(mem_parabolicRadicalRoots_iff.1 hα).1,
      (mem_parabolicRadicalRoots_iff.1 hα).2.1⟩
  have hpR := (orbitCertRoot_mem_parabolicRadicalRoots_mid_iff ⟨hp, hp'⟩).1 hα
  obtain ⟨q, hq, he⟩ := dualRoot_mem_parabolicRadicalRoots_mid p hpR
  obtain ⟨-, -, -, -, hR, -⟩ := f4Mid_check
  obtain ⟨hq1, hq2, -⟩ := hR q hq
  refine ⟨(mem_parabolicRadicalRoots_iff.1 hα).1, ?_⟩
  rw [List.ofFn_injective he]
  exact (orbitCertRoot_mem_parabolicRadicalRoots_mid_iff ⟨hq1, hq2⟩).2 hq

section Outer

variable [Finite K] [CharP K ReeTag.F4.prime]

theorem f4Phi_pow_mem_parabolicRadical_mid (n : ℕ) {u : adjointGroup .F4 K}
    (hu : (u : ModGL .F4 K) ∈ parabolicRadical .F4 K f4MidJ) :
    (((f4Phi (K := K)) ^ n) u : ModGL .F4 K) ∈ parabolicRadical .F4 K f4MidJ := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    have h := CFSG.LieType.Ree.ReeTag.map_finiteReeAut_rootSpan_le (t := ReeTag.F4) (K := K)
      (a := 0) (S := parabolicRadicalRoots .F4 f4MidJ)
      (fun α hα => dualRoot_mem_parabolicRadicalRoots_mid' hα)
    rw [finiteReeAut_zero_F4] at h
    exact h ⟨_, ih, rfl⟩

end Outer

theorem parabolicSubgroup_mid_le_centralizer [CharP K 2] (hK : Nat.card K = 2) :
    parabolicSubgroup .F4 K f4MidJ ≤ centralizer {f4x K 44 1} := by
  have hroot := (f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩).1
  refine sup_le (sup_le (fun h hh => ?_) (fun u hu => ?_)) ((closure_le _).2 ?_)
  ·
    rw [mem_centralizer_iff]
    rintro _ rfl
    have e := conj_pinnedX_of_mem_torusGroup hh hroot 1
    rcases eq_zero_or_eq_one_of_card_eq_two hK (torusRootChar h (orbitCertRoot .F4 44)) with
      h0 | h1
    · exfalso
      rw [h0, zero_mul, pinnedX_zero, mul_inv_eq_one, mul_eq_left] at e
      have h01 : pinnedX .F4 K (orbitCertRoot .F4 44) (1 : K) =
          pinnedX .F4 K (orbitCertRoot .F4 44) 0 := by rw [e, pinnedX_zero]
      exact one_ne_zero (pinnedX_injective .F4 K _ h01)
    · rw [h1, one_mul, mul_inv_eq_iff_eq_mul] at e
      exact e.symm
  ·
    rw [mem_centralizer_iff]
    rintro _ rfl
    exact (f4x_central (Or.inl rfl) 1 hu).symm
  ·
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, hweyl, -⟩ := f4_field_two_root_pair_relations hK
    have hfix : reflect .F4 j (orbitCertRoot .F4 44) = orbitCertRoot .F4 44 := by
      have hj' : (j : ℕ) = 1 ∨ (j : ℕ) = 2 := hj
      have key : ∀ i : Fin Tag.F4.rank, ((i : ℕ) = 1 ∨ (i : ℕ) = 2) →
          List.ofFn (reflect .F4 i (orbitCertRoot .F4 44)) = List.ofFn (orbitCertRoot .F4 44) := by
        decide +kernel
      exact List.ofFn_injective (key j hj')
    have e := (hweyl j _ hroot).2.1
    rw [hfix, mul_inv_eq_iff_eq_mul] at e
    exact e.symm

theorem mem_diagonalFieldActors_of_forall_parabolicRadical_mid [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ parabolicRadical .F4 K f4MidJ →
      β u = u) :
    β ∈ diagonalFieldActors .F4 K := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form le_rfl K (by rw [pow_one]; exact hK)
  obtain ⟨⟨g₀, k⟩, hgk₀, -⟩ := hnf β
  set g : adjointGroup .F4 K := g₀
  have hgk : β = MulAut.conj g * (f4Phi (K := K)) ^ (k : ℕ) := hgk₀
  clear_value g
  clear hgk₀
  rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hgk, hj, ← two_mul, f4Phi_pow_two_mul]
    exact mul_mem ((Chevalley_diagonal_field_actor_data.1 .F4 K).2.2 ⟨g, rfl⟩)
      (pow_mem f4Fr_mem_diagonalFieldActors j)
  · exfalso
    have : Finite (ModGL .F4 K) := finite_modGL
    have hRC : parabolicRadical .F4 K f4MidJ ≤ adjointGroup .F4 K :=
      (parabolicRadical_le_posUnipotent f4MidJ).trans posUnipotent_le_adjointGroup
    have hconj : ∀ v ∈ parabolicRadical .F4 K f4MidJ,
        ((g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * v *
          ((g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K)⁻¹ ∈ parabolicRadical .F4 K f4MidJ := by
      intro v hv
      have h := hβ ⟨v, hRC hv⟩ hv
      rw [hgk, MulAut.mul_apply, MulAut.conj_apply] at h
      have e' := congrArg (fun x => g⁻¹ * x * g) h
      have e : g⁻¹ * ⟨v, hRC hv⟩ * g = ((f4Phi (K := K)) ^ (k : ℕ)) ⟨v, hRC hv⟩ := by
        rw [← e']; group
      have hmem := f4Phi_pow_mem_parabolicRadical_mid (K := K) (k : ℕ) (u := ⟨v, hRC hv⟩) hv
      rw [← e] at hmem
      simpa using hmem
    have hgN : ((g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ adjointGroup .F4 K ⊓
        normalizer (parabolicRadical .F4 K f4MidJ : Set (ModGL .F4 K)) :=
      mem_inf.2 ⟨(g⁻¹).2, mem_normalizer_fintype hconj⟩
    rw [adjointGroup_inf_normalizer_parabolicRadical] at hgN
    have hgP : (g : ModGL .F4 K) ∈ parabolicSubgroup .F4 K f4MidJ := by
      simpa using inv_mem hgN
    have hcen := mem_centralizer_iff.1 (parabolicSubgroup_mid_le_centralizer hK hgP) _ rfl
    have h47 := hβ ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩
      (f4x_mem_parabolicRadical_mid (by decide) 1)
    rw [hgk, MulAut.mul_apply, hj, f4Phi_pow_odd_f4x_47, MulAut.conj_apply] at h47
    have h47' := congrArg Subtype.val h47
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h47'
    rw [← hcen, mul_inv_cancel_right] at h47'
    exact f4x_44_ne_f4x_47 1 h47'

theorem mem_map_radicalIn_one_iff {J : Set (Fin (f4RootDatum K).rank)}
    {u : (f4RootDatum K).group} :
    u ∈ ((f4RootDatum K).radicalIn J).map (MulAut.conj (1 : (f4RootDatum K).group)).toMonoidHom ↔
      (u.1 : ModGL .F4 K) ∈ parabolicRadical .F4 K J := by
  rw [map_one, show (1 : MulAut (f4RootDatum K).group).toMonoidHom = MonoidHom.id _ from rfl,
    Subgroup.map_id, RootWeightDatum.radicalIn, Subgroup.mem_subgroupOf]
  rfl

theorem innerCentralizerCriterion_F4_longShortRoot_two [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    InnerCentralizerCriterion
      (⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) := by
  have hJ : (f4MidJ : Set (Fin (f4RootDatum K).rank)) ≠ Set.univ := by
    intro h
    have h0 := Set.eq_univ_iff_forall.1 h
      (⟨0, CFSG.Blueprint.Chevalley.Tag.rank_pos .F4⟩ : Fin (f4RootDatum K).rank)
    change (0 : ℕ) = 1 ∨ (0 : ℕ) = 2 at h0
    omega
  refine innerCentralizerCriterion_of_conj_radical (f4RootDatum K) hJ 1
    (fun u hu => parabolicRadical_mid_le_closure_odd hK (mem_map_radicalIn_one_iff.1 hu))
    (fun z hz hc _ => ?_)
    (fun β hβ => mem_diagonalFieldActors_of_forall_parabolicRadical_mid hK β
      fun u hu => hβ u (mem_map_radicalIn_one_iff.2 hu))
  have hz' := mem_map_radicalIn_one_iff.1 hz
  refine Subtype.ext ?_
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact sq_eq_one_of_commute_parabolicRadical_mid hz' fun p hp => congrArg Subtype.val
    (hc (⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ : (f4RootDatum K).group)
      (mem_map_radicalIn_one_iff.2 (f4x_mem_parabolicRadical_mid hp 1)))

theorem innerCentralizerCriterion_F4_longShortRoot' {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact innerCentralizerCriterion_F4_longShortRoot_two (by simpa using hK)
  · exact innerCentralizerCriterion_F4_longShortRoot h hK

theorem innerInvolutionInput_F4_of_classes' {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {v : adjointGroup .F4 K} (hv : InnerCentralizerCriterion v)
    (hrep : ∀ x : adjointGroup .F4 K, orderOf (MulAut.conj x) = 2 →
      ∃ ψ : MulAut (adjointGroup .F4 K), ∃ s ∈ ({⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩,
        ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩, v} : Set (adjointGroup .F4 K)), ψ s = x) :
    InnerInvolutionInput (adjointGroup .F4 K) := by
  refine innerInvolutionInput_of_representatives (fun s hs => ?_) hrep
  rcases hs with rfl | rfl | rfl
  · exact innerCentralizerCriterion_F4_longRoot' hf hK
  · exact innerCentralizerCriterion_F4_longShortRoot' hf hK
  · exact hv

end CFSG.SeitzReduction
