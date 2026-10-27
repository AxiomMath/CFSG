module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXSpec

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem axFixOK_spec {act : Array (Array Nat)} {q : Nat → Bool} {fam : List (List Nat)}
    (h : axFixOK act q fam = true) {Z : List Nat} (hZ : Z ∈ fam) :
    (∀ i ∈ Z, q i = true) ∨ Z.length * fcFix act Z ≤ 2 ^ 8 := by
  simp only [axFixOK, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h Z hZ

theorem axCore_sound {ms : Array (Array Nat)} {qs : Array Bool} {fam : List (List Nat)}
    {act tab : Array (Array Nat)} {e : Nat}
    (hact : act = ms.map fcAct) (htab : tab = fcMul ms act) (he : e = fcIdx ms idCols)
    (h : axCore ms qs fam act tab e = true) : axSpec ms (fun k => qs[k]!) := by
  subst hact htab he
  simp only [axCore, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hms, hdist, htabN, heN, hfam1, hext, hfix⟩ := h
  have hmsN : ∀ i < ms.size, ∀ c < 10, ms[i]![c]! < 1024 := fun k hk c hc => by
    rw [getElem!_pos ms k hk]
    exact fcColsLt_iff.1 (Array.all_eq_true.1 hms k hk) c hc
  have hmul := fun {i j : Nat} (hi : i < ms.size) (hj : j < ms.size) =>
    fcMul_fn hmsN htabN hi hj
  have hFe : fn ms[fcIdx ms idCols]! = id := by
    rw [← fcFn_congr (fcIdx_spec heN), fn_idCols]
  intro X hXsub hXmul hXsq hXne
  obtain ⟨Z, hZ, hZN, hZX⟩ := fcFamily_closed (F := fun i => fn ms[i]!)
    (mul := fun i j => (fcMul ms (ms.map fcAct))[i]![j]!) (N := ms.size)
    (e := fcIdx ms idCols) (fam := fam) (fun i hi j hj => (hmul hi hj).1)
    (fun i hi j hj => (hmul hi hj).2)
    (fun i hi j hj hij => fcDistinct_spec hdist hmsN hi hj hij) heN hFe
    (List.contains_iff_mem.1 hfam1)
    (fun Y hY _ y hy hyy hyY hc => ⟨fcExt (fcMul ms (ms.map fcAct)) Y y,
      fcExtOK_spec hext hY hy hyy hyY hc, fun i => mem_fcExt⟩)
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := hXsub hx
      exact ⟨k, hk, rfl⟩)
    hXmul hXsq hXne
  subst hZX
  rcases axFixOK_spec hfix hZ with hq | hbound
  · left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_fcMaps.1 hx
    exact ⟨i, hZN i hi, hq i hi, rfl⟩
  · right
    exact le_trans (Nat.mul_le_mul (card_fcMaps_le _ _) (fcCard_fixSet_le hmsN hZN)) hbound

theorem axCheck_sound {ms : Array (Array Nat)} {qs : Array Bool} {fam : List (List Nat)}
    (h : axCheck ms qs fam = true) : axSpec ms (fun k => qs[k]!) :=
  axCore_sound rfl rfl rfl h

theorem axCheck_parts {ms : Array (Array Nat)} {qs : Array Bool} {fam : List (List Nat)}
    (h : axCheck ms qs fam = true) :
    ms.size = 2 ^ 8 ∧ (∀ k < ms.size, ∀ c < 10, ms[k]![c]! < 1024) ∧
      ∀ k < ms.size, ∀ k' < ms.size, fn ms[k]! = fn ms[k']! → k = k' := by
  simp only [axCheck, axCore, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hsz, hms, hdist, -⟩ := h
  have hmsN : ∀ i < ms.size, ∀ c < 10, ms[i]![c]! < 1024 := fun k hk c hc => by
    rw [getElem!_pos ms k hk]
    exact fcColsLt_iff.1 (Array.all_eq_true.1 hms k hk) c hc
  exact ⟨hsz, hmsN, fun k hk k' hk' hkk => fcDistinct_spec hdist hmsN hk hk' hkk⟩

theorem axWordCols_nil (gc : Array (Array Nat)) : axWordCols gc [] = idCols := rfl

theorem axWordCols_cons (gc : Array (Array Nat)) (k : Nat) (w : List Nat) :
    axWordCols gc (k :: w) = compose gc[k]! (axWordCols gc w) := rfl

theorem axWordCols_act {G : Type*} [Group G] {b : ℕ → G}
    (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i) (hsq : ∀ i < 10, b i * b i = 1)
    (g : ℕ → G) (gc : Array (Array Nat))
    (hg : ∀ k < gc.size, ∀ i < 10, g k * b i * (g k)⁻¹ = phi b gc[k]![i]!) (w : List Nat) :
    (∀ k ∈ w, k < gc.size) → ∀ i < 10,
      (w.map g).prod * b i * (w.map g).prod⁻¹ = phi b (axWordCols gc w)[i]! := by
  induction w with
  | nil =>
    intro _ i hi
    have h : idCols[i]! = 2 ^ i := by
      unfold idCols
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    rw [axWordCols_nil, h, phi_two_pow hi]
    simp
  | cons k w ih =>
    intro hw i hi
    have hk : k < gc.size := hw k List.mem_cons_self
    have ih' := ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
    rw [axWordCols_cons, compose_getElem! _ _ hi, List.map_cons, List.prod_cons]
    have e1 := conj_phi hb hsq (g k) gc[k]! (hg k hk) (axWordCols gc w)[i]!
    have e3 : g k * (w.map g).prod * b i * (g k * (w.map g).prod)⁻¹ =
        g k * ((w.map g).prod * b i * (w.map g).prod⁻¹) * (g k)⁻¹ := by group
    rw [e3, ih' i hi, e1]

theorem axWordsOK_spec {gc : Array (Array Nat)} {qs : Array Bool} {ws : Array (List Nat)}
    {ms : Array (Array Nat)} (h : axWordsOK gc qs ws ms = true) :
    (∀ k < gc.size, ∀ c < 10, gc[k]![c]! < 1024) ∧ ws.size = ms.size ∧
      ∀ j < ms.size, (∀ k ∈ ws[j]!, k < gc.size) ∧
        (∀ i < 10, (axWordCols gc ws[j]!)[i]! = ms[j]![i]!) ∧
        (qs[j]! = true → ∀ k ∈ ws[j]!, k < 9) := by
  simp only [axWordsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hgc, hsz⟩, hj⟩ := h
  refine ⟨fun k hk c hc => ?_, hsz, fun j hjl => ?_⟩
  · rw [getElem!_pos gc k hk]
    exact fcColsLt_iff.1 (Array.all_eq_true.1 hgc k hk) c hc
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hj j hjl
    refine ⟨fun k hk => by simpa using h1 k hk, fun i hi => fcMatEq_iff.1 h2 i hi,
      fun hq k hk => ?_⟩
    rcases h3 with h3 | h3
    · simp [hq] at h3
    · simpa using h3 k hk

end CFSG.EvenSporadicStandard.TwoFi22.DS81
