module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCFamily
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCSpec

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Classical

theorem fcCard_fixSet_le {ms : Array (Array Nat)}
    (hmsN : ∀ i < ms.size, ∀ c < 10, ms[i]![c]! < 1024) {Z : List Nat}
    (hZN : ∀ i ∈ Z, i < ms.size) :
    (fixSet (fcMaps (fun i => fn ms[i]!) Z)).card ≤ fcFix (ms.map fcAct) Z := by
  unfold fcFix
  refine le_trans (Finset.card_le_card_of_injOn Fin.val
    (t := ((List.range 1024).filter fun v => Z.all fun x => (ms.map fcAct)[x]![v]! == v).toFinset)
    ?_ Fin.val_injective.injOn) (List.toFinset_card_le _)
  intro v hv
  simp only [Finset.mem_coe, fixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range, List.all_eq_true,
    beq_iff_eq]
  refine ⟨v.isLt, fun x hx => ?_⟩
  have hxN := hZN x hx
  have h2 := congrArg Fin.val (hv _ (mem_fcMaps.2 ⟨x, hx, rfl⟩))
  rw [fn_val (hmsN x hxN)] at h2
  rw [fcGetElem!_map _ _ hxN, fcAct_getElem! v.isLt]
  exact h2

theorem exists_fcIdx_of_mem {rows ms : Array (Array Nat)} {x : Nat}
    (h : x ∈ rows.map (fcIdx ms)) : ∃ k < rows.size, fcIdx ms rows[k]! = x := by
  obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 h
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
  exact ⟨k, hk, by rw [getElem!_pos rows k hk]⟩

theorem fcCore_sound {cu cw ms : Array (Array Nat)} {fam : List (List Nat)}
    {act tab : Array (Array Nat)} {e : Nat} {ia ib : Array Nat}
    (hact : act = ms.map fcAct) (htab : tab = fcMul ms act) (he : e = fcIdx ms idCols)
    (hia : ia = cu.map (fcIdx ms)) (hib : ib = cw.map (fcIdx ms))
    (h : fcCore cu cw ms fam act tab e ia ib = true) : fcSpec cu cw := by
  subst hact htab he hia hib
  simp only [fcCore, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hcu, hcw, hms, h128, hdist, htabN, hiaN, hibN, hcov, heN, hfam1, hext, hfix⟩ := h
  have colsOf : ∀ rows : Array (Array Nat), rows.all fcColsLt = true →
      ∀ k < rows.size, ∀ c < 10, rows[k]![c]! < 1024 := fun rows hr k hk c hc => by
    rw [getElem!_pos rows k hk]
    exact fcColsLt_iff.1 (Array.all_eq_true.1 hr k hk) c hc
  have hcuN := colsOf cu hcu
  have hcwN := colsOf cw hcw
  have hmsN := colsOf ms hms
  have hrows : ∀ rows : Array (Array Nat), (rows.map (fcIdx ms)).all (· < ms.size) = true →
      ∀ k < rows.size, fcIdx ms rows[k]! < ms.size ∧
        fn rows[k]! = fn ms[fcIdx ms rows[k]!]! := fun rows hr k hk => by
    obtain ⟨h1, h2⟩ := fcRows_spec hr hk
    exact ⟨h1, fcFn_congr h2⟩
  have hmul := fun {i j : Nat} (hi : i < ms.size) (hj : j < ms.size) =>
    fcMul_fn hmsN htabN hi hj
  have hFe : fn ms[fcIdx ms idCols]! = id := by
    rw [← fcFn_congr (fcIdx_spec heN), fn_idCols]
  have hM1 : ∀ f ∈ mset cu cw, ∃ i < ms.size, fn ms[i]! = f := by
    rintro f ⟨k0, hk0, k1, hk1, rfl⟩
    obtain ⟨ha, hfa⟩ := hrows cu hiaN k0 hk0
    obtain ⟨hb, hfb⟩ := hrows cw hibN k1 hk1
    refine ⟨_, (hmul ha hb).1, ?_⟩
    rw [(hmul ha hb).2, fn_compose (hcuN k0 hk0) (hcwN k1 hk1), hfa, hfb]
  have hM2 : ∀ i < ms.size, fn ms[i]! ∈ mset cu cw := by
    intro i hi
    obtain ⟨x, hx, y, hy, hxy⟩ := fcCover_spec hcov hi
    rw [mem_fcHits] at hx hy
    obtain ⟨k0, hk0, hk0x⟩ := exists_fcIdx_of_mem hx.2
    obtain ⟨k1, hk1, hk1y⟩ := exists_fcIdx_of_mem hy.2
    refine ⟨k0, hk0, k1, hk1, ?_⟩
    have hfa := (hrows cu hiaN k0 hk0).2
    have hfb := (hrows cw hibN k1 hk1).2
    rw [hk0x] at hfa
    rw [hk1y] at hfb
    rw [fn_compose (hcuN k0 hk0) (hcwN k1 hk1), hfa, hfb, ← hxy]
    exact (hmul hx.1 hy.1).2
  have hcard : 2 ^ 7 ≤ (mset cu cw).ncard := by
    have hinj : Set.InjOn (fun i => fn ms[i]!) ((Finset.range (2 ^ 7) : Finset Nat) : Set Nat) :=
      fun i hi j hj hij => fcDistinct_spec hdist hmsN
        (lt_of_lt_of_le (Finset.mem_range.1 hi) h128) (lt_of_lt_of_le (Finset.mem_range.1 hj) h128)
        hij
    calc 2 ^ 7 = ((Finset.range (2 ^ 7)).image fun i => fn ms[i]!).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ = (↑((Finset.range (2 ^ 7)).image fun i => fn ms[i]!) :
            Set (Fin 1024 → Fin 1024)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (mset cu cw).ncard := Set.ncard_le_ncard (fun f hf => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hf
          exact hM2 i (lt_of_lt_of_le (Finset.mem_range.1 hi) h128))
  unfold fcSpec
  refine ⟨hcard, ?_⟩
  intro X hXsub hXmul hXsq hXne
  obtain ⟨Z, hZ, hZN, hZX⟩ := fcFamily_closed (F := fun i => fn ms[i]!)
    (mul := fun i j => (fcMul ms (ms.map fcAct))[i]![j]!) (N := ms.size)
    (e := fcIdx ms idCols) (fam := fam) (fun i hi j hj => (hmul hi hj).1)
    (fun i hi j hj => (hmul hi hj).2)
    (fun i hi j hj hij => fcDistinct_spec hdist hmsN hi hj hij) heN hFe
    (List.contains_iff_mem.1 hfam1)
    (fun Y hY _ y hy hyy hyY hc => ⟨fcExt (fcMul ms (ms.map fcAct)) Y y,
      fcExtOK_spec hext hY hy hyy hyY hc, fun i => mem_fcExt⟩)
    (fun x hx => hM1 x (hXsub hx)) hXmul hXsq hXne
  subst hZX
  rcases fcFixOK_spec hfix hZ with hZe | hbound
  · left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_fcMaps.1 hx
    rw [hZe] at hi
    obtain rfl := List.mem_singleton.1 hi
    exact hFe
  · right
    exact le_trans (Nat.mul_le_mul (card_fcMaps_le _ _) (fcCard_fixSet_le hmsN hZN)) hbound

theorem fcCheck_sound {cu cw ms : Array (Array Nat)} {fam : List (List Nat)}
    (h : fcCheck cu cw ms fam = true) : fcSpec cu cw :=
  fcCore_sound rfl rfl rfl rfl rfl h

end CFSG.EvenSporadicStandard.TwoFi22.DS81
