module

public import CFSG.CGT.M24R.N8Sem
public import CFSG.CGT.M24R.Interfaces

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.T75JM CFSG.CGT.Timmesfeld75 CFSG.CosetTable

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

variable {G : Type} [Group G] {T : Subgroup G}

theorem card_normalizer8 (h16 : Nat.card T = 16) (φ : NQuot T ≃* alternatingGroup (Fin 8)) :
    Nat.card (Subgroup.normalizer (T : Set G)) = 322560 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.subgroupOf (Subgroup.normalizer (T : Set G)))]
  have hq : Nat.card (NQuot T) = 20160 := (Nat.card_congr φ.toEquiv).trans card_alt8
  have ht : Nat.card (T.subgroupOf (Subgroup.normalizer (T : Set G))) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv).trans h16
  rw [hq, ht]

theorem card_complement8 (φ : NQuot T ≃* alternatingGroup (Fin 8)) {L : Subgroup G}
    (hLT : L ⊓ T = ⊥) (hTL : T ⊔ L = Subgroup.normalizer (T : Set G)) : Nat.card L = 20160 := by
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := by rw [← hTL]; exact le_sup_right
  let π : L →* NQuot T :=
    (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G)))).comp
      (Subgroup.inclusion hLN)
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hT : Subgroup.inclusion hLN l ∈ T.subgroupOf (Subgroup.normalizer (T : Set G)) :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hLN l)).1 hl
    have hbot : (l : G) ∈ L ⊓ T := ⟨l.2, hT⟩
    rw [hLT] at hbot
    exact Subtype.ext (Subgroup.mem_bot.1 hbot)
  have hsurj : Function.Surjective π := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    have hn : n ∈ T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊔
        L.subgroupOf (Subgroup.normalizer (T : Set G)) := by
      rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer hLN, hTL, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top n
    obtain ⟨t, ht, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hn
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hLN ⟨(l : G), hl⟩) : NQuot T) =
      QuotientGroup.mk (t * l)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).2 ht, one_mul]
    rfl
  rw [Nat.card_congr (Equiv.ofBijective π ⟨hinj, hsurj⟩), Nat.card_congr φ.toEquiv, card_alt8]

theorem eq_of_natEqB8 {n m : ℕ} (h : natEqB8 n m = true) : n = m := Nat.eq_of_beq_eq_true h

theorem mem_allCols8 {C : Cols} (hC : ∀ j, C.col j < 16) : C ∈ allCols8 := by
  obtain ⟨a, b, d, e⟩ := C
  have ha := hC 0
  have hb := hC 1
  have hd := hC 2
  have he := hC 3
  simp only [Cols.col] at ha hb hd he
  refine List.mem_map.2 ⟨a + 16 * b + 256 * d + 4096 * e, List.mem_range.2 (by omega), ?_⟩
  simp only [colsOfCode8, Cols.mk.injEq]
  omega

theorem isGL8_colsOf (c : Coords T) (g : Subgroup.normalizer (T : Set G)) :
    isGL8 (colsOf c g) = true := by
  have hinv : ∀ v, v < 16 → applyC (colsOf c g⁻¹) (applyC (colsOf c g) v) = v := by
    intro v hv
    rw [← applyC_compC, ← colsOf_mul, inv_mul_cancel, colsOf_one, applyC_idC hv]
  unfold isGL8
  rw [List.all_eq_true]
  intro v hv
  rw [List.mem_range] at hv
  rw [bne_iff_ne]
  intro h0
  have h1 := hinv (v + 1) (by omega)
  rw [h0, applyC_zero] at h1
  omega

theorem exists_mem_complement_colsOf (c : Coords T) (hC : Subgroup.centralizer (T : Set G) = T)
    {L : Subgroup G} (hLT : L ⊓ T = ⊥) (hLN : L ≤ Subgroup.normalizer (T : Set G))
    (hL : Nat.card L = 20160) (hgl : glCountCheck = true) {A : Cols} (hA : ∀ j, A.col j < 16)
    (hAg : isGL8 A = true) :
    ∃ l : Subgroup.normalizer (T : Set G), (l : G) ∈ L ∧ colsOf c l = A := by
  classical
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fintype L := Fintype.ofFinite L
  let ρ : L → Cols := fun x => colsOf c ⟨x, hLN x.2⟩
  have hρ : Function.Injective ρ := by
    intro x y hxy
    have h1 : colsOf c ((⟨x, hLN x.2⟩ : Subgroup.normalizer (T : Set G))⁻¹ * ⟨y, hLN y.2⟩) =
        idC := by
      rw [colsOf_mul]
      change compC _ (ρ y) = idC
      rw [← hxy]
      change compC _ (colsOf c ⟨x, hLN x.2⟩) = idC
      rw [← colsOf_mul, inv_mul_cancel, colsOf_one]
    have h2 := eq_one_of_colsOf_eq_idC8 c L hC hLT (L.mul_mem (L.inv_mem x.2) y.2) h1
    rw [inv_mul_eq_one] at h2
    exact Subtype.ext (congrArg (fun z : Subgroup.normalizer (T : Set G) => (z : G)) h2)
  have hsub : Finset.univ.image ρ ⊆ (allCols8.filter isGL8).toFinset := by
    intro C hC'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hC'
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_allCols8 (colsOf_lt c _), isGL8_colsOf c _⟩
  have h20 : (allCols8.filter isGL8).length = 20160 := eq_of_natEqB8 hgl
  have hcard : (allCols8.filter isGL8).toFinset.card ≤ (Finset.univ.image ρ).card := by
    rw [Finset.card_image_of_injective _ hρ, Finset.card_univ, ← Nat.card_eq_fintype_card, hL]
    exact (List.toFinset_card_le _).trans h20.le
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hAS : A ∈ (allCols8.filter isGL8).toFinset := by
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_allCols8 hA, hAg⟩
  rw [← heq] at hAS
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hAS
  exact ⟨⟨x, hLN x.2⟩, x.2, hx⟩

@[expose] def evalL8 {H : Type*} [Monoid H] (l : Fin 6 → H) (w : List (Fin 6)) : H :=
  (w.map l).prod

theorem colsOf_evalL8 (c : Coords T) {l : Fin 6 → Subgroup.normalizer (T : Set G)}
    (hcl : ∀ i, colsOf c (l i) = modelCols8 i) : ∀ w, colsOf c (evalL8 l w) = evalM8 w
  | [] => colsOf_one c
  | i :: w => by
    rw [evalL8, List.map_cons, List.prod_cons, colsOf_mul, hcl, ← evalL8, colsOf_evalL8 c hcl w]
    rfl

theorem evalL8_mem (L : Subgroup G) {l : Fin 6 → Subgroup.normalizer (T : Set G)}
    (hl : ∀ i, (l i : G) ∈ L) :
    ∀ w, ((evalL8 l w : Subgroup.normalizer (T : Set G)) : G) ∈ L
  | [] => L.one_mem
  | i :: w => by
    rw [evalL8, List.map_cons, List.prod_cons, ← evalL8, Subgroup.coe_mul]
    exact L.mul_mem (hl i) (evalL8_mem L hl w)

theorem exists_word_of_mem_complement (c : Coords T) {L : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (T : Set G)) (hL : Nat.card L = 20160)
    (hgen : ∃ W : List (List (Fin 6)), W.length = 20160 ∧ (W.map evalM8).Nodup)
    {l : Fin 6 → Subgroup.normalizer (T : Set G)}
    (hl : ∀ i, (l i : G) ∈ L) (hcl : ∀ i, colsOf c (l i) = modelCols8 i) {x : G} (hx : x ∈ L) :
    ∃ w : List (Fin 6), ((evalL8 l w : Subgroup.normalizer (T : Set G)) : G) = x := by
  classical
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨W, hlen, hnd⟩ := hgen
  let e : List (Fin 6) → L := fun w =>
    ⟨((evalL8 l w : Subgroup.normalizer (T : Set G)) : G), evalL8_mem L hl w⟩
  let ρ : L → Cols := fun y => colsOf c (⟨y, hLN y.2⟩ : Subgroup.normalizer (T : Set G))
  have hf : ρ ∘ e = evalM8 := funext fun w => colsOf_evalL8 c hcl w
  have hnd' : (W.map e).Nodup := by
    apply List.Nodup.of_map ρ
    rw [List.map_map, hf]
    exact hnd
  have huniv : (W.map e).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd', List.length_map, hlen, ← Nat.card_eq_fintype_card, hL]
  have hmem : (⟨x, hx⟩ : L) ∈ W.map e := by
    rw [← List.mem_toFinset, huniv]
    exact Finset.mem_univ _
  obtain ⟨w, -, hw⟩ := List.mem_map.1 hmem
  exact ⟨w, congrArg Subtype.val hw⟩

theorem exists_mulEquiv_normalizer8 (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hsq : ∀ a ∈ T, a ^ 2 = 1) (h16 : Nat.card T = 16)
    (hC : Subgroup.centralizer (T : Set G) = T) (φ : NQuot T ≃* alternatingGroup (Fin 8))
    {L : Subgroup G} (hLT : L ⊓ T = ⊥) (hTL : T ⊔ L = Subgroup.normalizer (T : Set G))
    (hgl : glCountCheck = true)
    (hgen : ∃ W : List (List (Fin 6)), W.length = 20160 ∧ (W.map evalM8).Nodup)
    [Finite (PG 10 relsN8Ten)]
    (hcard : Nat.card (PG 10 relsN8Ten) ≤ 322560) :
    ∃ ψ : PG 10 relsN8Ten ≃* Subgroup.normalizer (T : Set G),
      Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen8)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  classical
  obtain ⟨c⟩ := exists_coords hcomm hsq h16
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := by rw [← hTL]; exact le_sup_right
  have hL := card_complement8 φ hLT hTL
  choose l hlL hlc using fun i : Fin 6 =>
    exists_mem_complement_colsOf c hC hLT hLN hL hgl (modelCols8_lt i) (isGL8_modelCols8 i)
  set f := gens8 c l with hf
  let Φ : PG 10 relsN8Ten →* Subgroup.normalizer (T : Set G) :=
    PresentedGroup.toGroup (f := f) fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      exact lift_relsN8Ten_eq_one c L hC hLT hlL hlc w hw
  have hΦ : ∀ k, Φ (PresentedGroup.of k) = f k := fun k => PresentedGroup.toGroup.of _
  have hΦt : ∀ j : Fin 4, Φ (tGen8 j) = tN c j.val := by
    intro j
    show Φ (PresentedGroup.of _) = _
    rw [hΦ, hf]
    simp [gens8]
  set S := Subgroup.map Φ (Subgroup.closure (Set.range tGen8)) with hS
  have hSt : ∀ j : Fin 4, tN c j.val ∈ S := fun j =>
    ⟨tGen8 j, Subgroup.subset_closure ⟨j, rfl⟩, hΦt j⟩
  have hpart : ∀ (b : Bool) (n : ℕ), (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) →
      inN (tOf c (if b then n else 0)) ∈ S := by
    intro b n hn
    cases b
    · simp only [Bool.false_eq_true, ite_false, tOf_zero c]
      exact S.one_mem
    · simp only [ite_true]
      rcases hn with rfl | rfl | rfl | rfl
      · exact hSt 0
      · exact hSt 1
      · exact hSt 2
      · exact hSt 3
  have hT : ∀ t : T, inN t ∈ S := by
    intro t
    rw [decomp c t]
    simp only [← inN_mul]
    exact S.mul_mem (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
      (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
  have hSR : S ≤ Φ.range := Subgroup.map_le_range _ _
  have hlR : ∀ w : List (Fin 6), evalL8 l w ∈ Φ.range := by
    intro w
    induction w with
    | nil => exact Φ.range.one_mem
    | cons i w ih =>
      rw [evalL8, List.map_cons, List.prod_cons, ← evalL8]
      refine Φ.range.mul_mem ⟨PresentedGroup.of ⟨i.val, by omega⟩, ?_⟩ ih
      rw [hΦ, hf]
      simp [gens8]
  have hsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro y _
    have hK : T ⊔ L ≤ Φ.range.map (Subgroup.normalizer (T : Set G)).subtype := by
      refine sup_le (fun t ht => ⟨inN ⟨t, ht⟩, hSR (hT _), rfl⟩) fun x hx => ?_
      obtain ⟨w, hw⟩ := exists_word_of_mem_complement c hLN hL hgen hlL hlc hx
      exact ⟨evalL8 l w, hlR w, hw⟩
    obtain ⟨z, hz, hzy⟩ := hK (by rw [hTL]; exact y.2)
    rwa [show z = y from Subtype.ext hzy] at hz
  have hbij : Function.Bijective Φ :=
    hsurj.bijective_of_nat_card_le (by rw [card_normalizer8 h16 φ]; exact hcard)
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  show S = T.subgroupOf (Subgroup.normalizer (T : Set G))
  refine le_antisymm ?_ fun x hx => ?_
  · rw [hS, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    show Φ (tGen8 j) ∈ T.subgroupOf (Subgroup.normalizer (T : Set G))
    rw [hΦt]
    exact (tOf c (2 ^ j.val)).2
  · have hx' : x = inN (⟨(x : G), hx⟩ : T) := Subtype.ext rfl
    rw [hx']
    exact hT _

end CFSG.CGT.M24R
