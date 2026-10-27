module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelMk
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelLoop

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

theorem autMap_eq_foldl (M : RegModel) (img : Array ℕ) :
    M.autMap img = (List.range' 1 (M.order.size - 1)).foldl
      (fun a i => a.set! M.order[i]! (M.m img[M.label[i]!]! a[M.parent[i]!]!))
      (Array.replicate M.N 0) := by
  unfold RegModel.autMap
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one, pure_bind]
  rfl

theorem twOrbits_eq_foldl (M : RegModel) (a : Array ℕ) :
    M.twOrbits a = ((M.twInvs a).foldl (fun st s => if (!st.1[s]!) = true then
      ((((List.range M.N).map fun x => M.m (M.m M.inv[x]! s) a[x]!).eraseDups).foldl
        (fun b y => b.set! y true) st.1,
       st.2 ++ [((List.range M.N).map fun x => M.m (M.m M.inv[x]! s) a[x]!).eraseDups])
      else st) (Array.replicate M.N false, [])).2 := by
  unfold RegModel.twOrbits
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind, forIn_list_ite]
  rfl

theorem getElem!_replicate_zero (N z : ℕ) : (Array.replicate N 0)[z]! = 0 := by
  by_cases hz : z < N
  · rw [getElem!_pos _ _ (by simpa using hz)]
    simp
  · rw [getElem!_neg _ _ (by simpa using hz)]
    rfl

theorem getElem!_range_map {α : Type} [Inhabited α] (n : ℕ) (f : ℕ → α) {i : ℕ} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem foldl_set_true {β : Type} (f : β → ℕ) (l : List β) (b : Array Bool)
    (hl : ∀ y ∈ l, f y < b.size) :
    (l.foldl (fun b y => b.set! (f y) true) b).size = b.size ∧
      ∀ z, (l.foldl (fun b y => b.set! (f y) true) b)[z]! = true ↔
        b[z]! = true ∨ ∃ y ∈ l, f y = z := by
  induction l generalizing b with
  | nil => simp
  | cons y l ih =>
    have hy : f y < b.size := hl y (by simp)
    obtain ⟨h1, h2⟩ := ih (b.set! (f y) true) (fun y' hy' => by
      rw [Array.size_set!]; exact hl y' (by simp [hy']))
    refine ⟨by rw [List.foldl_cons, h1, Array.size_set!], fun z => ?_⟩
    rw [List.foldl_cons, h2]
    by_cases hz : f y = z
    · subst hz
      rw [Array.getElem!_set!_self _ _ _ hy]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ hz]
      simp [hz]

theorem foldl_range_iterate (a : Array ℕ) (k x : ℕ) :
    (List.range k).foldl (fun y _ => a[y]!) x = (fun y => a[y]!)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']; rfl

theorem eraseDups_nodup (l : List ℕ) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.eraseDups_cons, List.nodup_cons, List.mem_eraseDups]
      refine ⟨by simp, ih _ ?_ _ rfl⟩
      rw [← h, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)

namespace Rep

variable {M : RegModel} {H : Type} [Group H]

theorem autMap_foldl_inv (R : Rep M H) (hT : TreeSpec M) (img : Array ℕ) (σ : H →* H)
    (x : Fin 7 → H) (hx : ∀ j : Fin 7, R.pt (x j) = M.gpt[j.val]!)
    (himg : ∀ j : Fin 7, R.pt (σ (x j)) = img[j.val]!) :
    ∀ k, k + 1 ≤ M.N →
      ((List.range' 1 k).foldl
        (fun a i => a.set! M.order[i]! (M.m img[M.label[i]!]! a[M.parent[i]!]!))
        (Array.replicate M.N 0)).size = M.N ∧
      ∀ i ≤ k, ∀ h, R.pt h = M.order[i]! →
        ((List.range' 1 k).foldl
          (fun a i => a.set! M.order[i]! (M.m img[M.label[i]!]! a[M.parent[i]!]!))
          (Array.replicate M.N 0))[R.pt h]! = R.pt (σ h) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp, fun i hi h hh => ?_⟩
    obtain rfl : i = 0 := by omega
    rw [hT.order_zero, ← R.pt_one] at hh
    obtain rfl := R.pt_inj hh
    rw [List.range'_zero, List.foldl_nil, getElem!_replicate_zero, map_one, R.pt_one]
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      show 1 + 1 * k = k + 1 by omega]
    refine ⟨by rw [Array.size_set!, ih1], fun i hi h hh => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · have hne : M.order[k + 1]! ≠ R.pt h := by
        rw [hh]
        exact fun he => by have := hT.order_inj _ _ (by omega) (by omega) he; omega
      rw [Array.getElem!_set!_ne _ _ _ _ hne, ih2 i (by omega) h hh]
    · rw [hh, Array.getElem!_set!_self _ _ _ (by rw [ih1]; exact hT.order_lt _ (by omega))]
      obtain ⟨p, hp, hpar, hlab, hord⟩ := hT.step (k + 1) (by omega) (by omega)
      obtain ⟨g, hg⟩ := R.pt_surj _ (hT.order_lt p (by omega))
      have hxg : h = x ⟨_, hlab⟩ * g := R.pt_inj (by rw [hh, R.pt_mul, hx, hg, hord])
      rw [hpar, ← hg, ih2 p (by omega) g hg, hxg, map_mul, R.pt_mul, himg]

theorem autMap_spec (R : Rep M H) (hT : TreeSpec M) (img : Array ℕ) (σ : H →* H)
    (x : Fin 7 → H) (hx : ∀ j : Fin 7, R.pt (x j) = M.gpt[j.val]!)
    (himg : ∀ j : Fin 7, R.pt (σ (x j)) = img[j.val]!) :
    (M.autMap img).size = M.N ∧ ∀ h : H, (M.autMap img)[R.pt h]! = R.pt (σ h) := by
  have hN : 0 < M.N := R.pt_one ▸ R.pt_lt 1
  obtain ⟨h1, h2⟩ := autMap_foldl_inv R hT img σ x hx himg (M.N - 1) (by omega)
  rw [autMap_eq_foldl, hT.size_order]
  refine ⟨h1, fun h => ?_⟩
  have hsurj : Function.Surjective (fun i : Fin M.N => (⟨M.order[i.1]!, hT.order_lt i.1 i.2⟩ :
      Fin M.N)) := Finite.surjective_of_injective fun i j hij =>
    Fin.ext (hT.order_inj i j i.2 j.2 (congrArg Fin.val hij))
  obtain ⟨i, hi⟩ := hsurj ⟨R.pt h, R.pt_lt h⟩
  exact h2 i (by omega) h (congrArg Fin.val hi).symm

theorem isInvolAut_iff (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (hs : a.size = M.N) :
    M.isInvolAut a = true ↔ (∀ h, σ (σ h) = h) ∧ ∀ x y, σ (x * y) = σ x * σ y := by
  unfold RegModel.isInvolAut
  simp only [Bool.and_eq_true, beq_iff_eq, hs, List.all_eq_true, List.mem_range, true_and]
  constructor
  · rintro ⟨H1, H2⟩
    refine ⟨fun h => ?_, fun x y => ?_⟩
    · have := H1 (R.pt h) (R.pt_lt h)
      simp only [ha] at this
      exact R.pt_inj this
    · have := H2 (R.pt x) (R.pt_lt x) (R.pt y) (R.pt_lt y)
      simp only [← R.pt_mul, ha] at this
      exact R.pt_inj this
  · rintro ⟨H1, H2⟩
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · obtain ⟨x, rfl⟩ := R.pt_surj x hx
      simp only [ha, H1]
    · obtain ⟨x, rfl⟩ := R.pt_surj x hx
      obtain ⟨y, rfl⟩ := R.pt_surj y hy
      simp only [← R.pt_mul, ha, H2]

theorem isHom_iff (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (hs : a.size = M.N) :
    M.isHom a = true ↔ ∀ x y, σ (x * y) = σ x * σ y := by
  unfold RegModel.isHom
  simp only [Bool.and_eq_true, beq_iff_eq, hs, List.all_eq_true, List.mem_range, true_and]
  constructor
  · intro H x y
    have := H (R.pt x) (R.pt_lt x) (R.pt y) (R.pt_lt y)
    simp only [← R.pt_mul, ha] at this
    exact R.pt_inj this
  · intro H x hx y hy
    obtain ⟨x, rfl⟩ := R.pt_surj x hx
    obtain ⟨y, rfl⟩ := R.pt_surj y hy
    simp only [← R.pt_mul, ha, H]

theorem isBij_iff (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) :
    M.isBij a = true ↔ Function.Surjective σ := by
  have hl : ∀ y ∈ List.range M.N, a[y]! < (Array.replicate M.N false).size := by
    intro y hy
    obtain ⟨h, rfl⟩ := R.pt_surj y (List.mem_range.1 hy)
    rw [ha, Array.size_replicate]
    exact R.pt_lt _
  obtain ⟨h1, h2⟩ := foldl_set_true (fun y => a[y]!) _ _ hl
  unfold RegModel.isBij
  rw [Array.all_eq_true]
  simp only [Array.size_replicate] at h1
  constructor
  · intro H g
    have := H (R.pt g) (by rw [h1]; exact R.pt_lt g)
    rw [id, ← getElem!_pos, h2, getElem!_replicate_false] at this
    obtain ⟨y, hy, hyg⟩ := this.resolve_left Bool.false_ne_true
    obtain ⟨h, rfl⟩ := R.pt_surj y (List.mem_range.1 hy)
    exact ⟨h, R.pt_inj (by rw [← ha]; exact hyg)⟩
  · intro H i hi
    rw [h1] at hi
    rw [id, ← getElem!_pos, h2]
    obtain ⟨g, rfl⟩ := R.pt_surj i hi
    obtain ⟨h, rfl⟩ := H g
    exact Or.inr ⟨R.pt h, List.mem_range.2 (R.pt_lt h), ha h⟩

theorem fixedPts_size (R : Rep M H) (a : Array ℕ) : (M.fixedPts a).size = M.N := by
  have _ := R.pt_one
  simp [RegModel.fixedPts]

theorem set_fixedPts (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) : R.set (M.fixedPts a) = {h | σ h = h} := by
  ext h
  rw [Rep.mem_set, RegModel.fixedPts, getElem!_range_map _ _ (R.pt_lt h), ha, beq_iff_eq,
    R.pt_inj.eq_iff]
  rfl

theorem iterate_pt (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (k : ℕ) (h : H) :
    (fun y => a[y]!)^[k] (R.pt h) = R.pt (σ^[k] h) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, ha, Function.iterate_succ_apply']

theorem permOrd_test_iff (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (k : ℕ) :
    (k > 0 && (List.range M.N).all fun x => (List.range k).foldl (fun y _ => a[y]!) x == x) =
      true ↔ 0 < k ∧ ∀ h, σ^[k] h = h := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
    foldl_range_iterate]
  refine and_congr_right fun _ => ⟨fun H h => R.pt_inj ?_, fun H x hx => ?_⟩
  · rw [← iterate_pt R σ ha, H _ (R.pt_lt h)]
  · obtain ⟨h, rfl⟩ := R.pt_surj x hx
    rw [iterate_pt R σ ha, H]

theorem permOrd_eq_iff (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) {k : ℕ} (hk : 0 < k ∧ k ≤ 12) :
    M.permOrd a = k ↔ (∀ h, σ^[k] h = h) ∧ ∀ j, 0 < j → j < k → ∃ h, σ^[j] h ≠ h := by
  have key : M.permOrd a = k ↔ (List.range 13).find? (fun k => k > 0 &&
      (List.range M.N).all fun x => (List.range k).foldl (fun y _ => a[y]!) x == x) = some k := by
    unfold RegModel.permOrd
    cases (List.range 13).find? _ with
    | none => simp only [Option.getD_none, reduceCtorEq, iff_false]; omega
    | some j => simp only [Option.getD_some, Option.some.injEq]
  rw [key, List.find?_range_eq_some]
  simp only [Bool.not_eq_true', ← Bool.not_eq_true, permOrd_test_iff R σ ha, List.mem_range]
  constructor
  · rintro ⟨⟨-, h1⟩, -, h2⟩
    refine ⟨h1, fun j hj hjk => ?_⟩
    by_contra hc
    exact h2 j hjk ⟨hj, fun h => Classical.byContradiction fun hne => hc ⟨h, hne⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hk.1, h1⟩, by omega, fun j hjk ⟨hj, hc⟩ => ?_⟩
    obtain ⟨h, hh⟩ := h2 j hj hjk
    exact hh (hc h)

theorem conjArr_size (R : Rep M H) (s : ℕ) : (M.conjArr s).size = M.N := by
  have _ := R.pt_one
  simp [RegModel.conjArr]

theorem conjArr_spec (R : Rep M H) (s h : H) :
    (M.conjArr (R.pt s))[R.pt h]! = R.pt (s⁻¹ * h * s) := by
  rw [R.pt_cj, RegModel.conjArr, getElem!_range_map _ _ (R.pt_lt h)]

theorem twInvs_nodup (a : Array ℕ) : (M.twInvs a).Nodup :=
  List.nodup_range.filter _

theorem mem_twInvs (R : Rep M H) {a : Array ℕ} (σ : H → H)
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) {s : ℕ} :
    s ∈ M.twInvs a ↔ ∃ h : H, R.pt h = s ∧ h * σ h = 1 := by
  unfold RegModel.twInvs
  simp only [List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hs, he⟩
    obtain ⟨h, rfl⟩ := R.pt_surj s hs
    refine ⟨h, rfl, R.pt_inj ?_⟩
    rw [R.pt_mul, R.pt_one, ← he, ha]
  · rintro ⟨h, rfl, he⟩
    refine ⟨R.pt_lt h, ?_⟩
    rw [ha, ← R.pt_mul, he, R.pt_one]

theorem twInvs_lt (R : Rep M H) (a : Array ℕ) : ∀ s ∈ M.twInvs a, s < M.N := by
  have _ := R.pt_one
  intro s hs
  unfold RegModel.twInvs at hs
  simp only [List.mem_filter, List.mem_range] at hs
  exact hs.1

theorem mem_twOrb (R : Rep M H) (σ : H → H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (s₀ : H) (y : ℕ) :
    y ∈ ((List.range M.N).map fun x => M.m (M.m M.inv[x]! (R.pt s₀)) a[x]!).eraseDups ↔
      ∃ x : H, y = R.pt (x⁻¹ * s₀ * σ x) := by
  rw [List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨x, rfl⟩ := R.pt_surj n (List.mem_range.1 hn)
    exact ⟨x, by rw [R.pt_mul, R.pt_mul, R.pt_inv, ha]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨R.pt x, List.mem_range.2 (R.pt_lt x), by rw [R.pt_mul, R.pt_mul, R.pt_inv, ha]⟩

theorem twOrb_mem_of_mem (R : Rep M H) (σ : H →* H) (orb : ℕ → List ℕ)
    (horb : ∀ s₀ : H, ∀ y, y ∈ orb (R.pt s₀) ↔ ∃ x : H, y = R.pt (x⁻¹ * s₀ * σ x))
    {s₀ t : H} {y : ℕ} (h1 : y ∈ orb (R.pt t)) (h2 : y ∈ orb (R.pt s₀)) :
    R.pt s₀ ∈ orb (R.pt t) := by
  obtain ⟨x, rfl⟩ := (horb t y).1 h1
  obtain ⟨z, hz⟩ := (horb s₀ _).1 h2
  have e := R.pt_inj hz
  refine (horb t _).2 ⟨x * z⁻¹, congrArg R.pt ?_⟩
  rw [map_mul, map_inv]
  have : s₀ = z * (z⁻¹ * s₀ * σ z) * (σ z)⁻¹ := by group
  rw [this, ← e]
  group

theorem twStep_spec (R : Rep M H) (σ : H →* H) (orb : ℕ → List ℕ)
    (horb : ∀ s₀ : H, ∀ y, y ∈ orb (R.pt s₀) ↔ ∃ x : H, y = R.pt (x⁻¹ * s₀ * σ x))
    (stp : Array Bool × List (List ℕ) → ℕ → Array Bool × List (List ℕ))
    (hstp : ∀ st s, stp st s = if (!st.1[s]!) = true then
      ((orb s).foldl (fun b y => b.set! y true) st.1, st.2 ++ [orb s]) else st)
    (st : Array Bool × List (List ℕ)) (s₀ : H) (h1 : st.1.size = M.N)
    (h2 : ∀ z, st.1[z]! = true ↔ ∃ o ∈ st.2, z ∈ o) (h3 : ∀ o ∈ st.2, ∃ t : H, o = orb (R.pt t))
    (h4 : st.2.Pairwise (fun o₁ o₂ => ∀ y ∈ o₁, y ∉ o₂)) :
    (stp st (R.pt s₀)).1.size = M.N ∧
      (∀ z, (stp st (R.pt s₀)).1[z]! = true ↔ ∃ o ∈ (stp st (R.pt s₀)).2, z ∈ o) ∧
      (∀ o ∈ (stp st (R.pt s₀)).2, ∃ t : H, o = orb (R.pt t)) ∧
      (stp st (R.pt s₀)).2.Pairwise (fun o₁ o₂ => ∀ y ∈ o₁, y ∉ o₂) ∧
      (∀ o ∈ st.2, o ∈ (stp st (R.pt s₀)).2) ∧ ∃ o ∈ (stp st (R.pt s₀)).2, R.pt s₀ ∈ o := by
  have hself : R.pt s₀ ∈ orb (R.pt s₀) := (horb s₀ _).2 ⟨1, by simp⟩
  rw [hstp]
  by_cases hc : st.1[R.pt s₀]! = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨h1, h2, h3, h4, fun o ho => ho, (h2 _).1 hc⟩
  · simp only [hc, Bool.not_false, ↓reduceIte]
    have hlt : ∀ y ∈ orb (R.pt s₀), y < st.1.size := by
      intro y hy
      obtain ⟨x, rfl⟩ := (horb s₀ y).1 hy
      rw [h1]; exact R.pt_lt _
    obtain ⟨k1, k2⟩ := foldl_set_true (fun y => y) (orb (R.pt s₀)) st.1 hlt
    refine ⟨by rw [k1, h1], fun z => ?_, fun o ho => ?_, ?_, fun o ho => by simp [ho],
      ⟨orb (R.pt s₀), by simp, hself⟩⟩
    · rw [k2, h2]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨o, ho, hz⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨o, Or.inl ho, hz⟩
        · exact ⟨_, Or.inr rfl, hy⟩
      · rintro ⟨o, ho | rfl, hz⟩
        · exact Or.inl ⟨o, ho, hz⟩
        · exact Or.inr ⟨z, hz, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact h3 o ho
      · exact ⟨s₀, rfl⟩
    · rw [List.pairwise_append]
      refine ⟨h4, List.pairwise_singleton _ _, fun o₁ ho₁ o₂ ho₂ y hy₁ hy₂ => hc ?_⟩
      rw [List.mem_singleton] at ho₂
      subst ho₂
      obtain ⟨t, rfl⟩ := h3 o₁ ho₁
      exact (h2 _).2 ⟨_, ho₁, twOrb_mem_of_mem R σ orb horb hy₁ hy₂⟩

theorem twFold_spec (R : Rep M H) (σ : H →* H) (orb : ℕ → List ℕ)
    (horb : ∀ s₀ : H, ∀ y, y ∈ orb (R.pt s₀) ↔ ∃ x : H, y = R.pt (x⁻¹ * s₀ * σ x))
    (stp : Array Bool × List (List ℕ) → ℕ → Array Bool × List (List ℕ))
    (hstp : ∀ st s, stp st s = if (!st.1[s]!) = true then
      ((orb s).foldl (fun b y => b.set! y true) st.1, st.2 ++ [orb s]) else st)
    (l : List ℕ) (hl : ∀ s ∈ l, s < M.N) :
    ∀ st : Array Bool × List (List ℕ), st.1.size = M.N →
      (∀ z, st.1[z]! = true ↔ ∃ o ∈ st.2, z ∈ o) → (∀ o ∈ st.2, ∃ t : H, o = orb (R.pt t)) →
      st.2.Pairwise (fun o₁ o₂ => ∀ y ∈ o₁, y ∉ o₂) →
      (∀ o ∈ (l.foldl stp st).2, ∃ t : H, o = orb (R.pt t)) ∧
      (l.foldl stp st).2.Pairwise (fun o₁ o₂ => ∀ y ∈ o₁, y ∉ o₂) ∧
      (∀ o ∈ st.2, o ∈ (l.foldl stp st).2) ∧ ∀ s ∈ l, ∃ o ∈ (l.foldl stp st).2, s ∈ o := by
  induction l with
  | nil => exact fun st _ _ h3 h4 => ⟨h3, h4, fun o ho => ho, by simp⟩
  | cons s l ih =>
    intro st h1 h2 h3 h4
    obtain ⟨t, rfl⟩ := R.pt_surj s (hl s (by simp))
    obtain ⟨k1, k2, k3, k4, k5, o₀, ho₀, hto₀⟩ :=
      twStep_spec R σ orb horb stp hstp st t h1 h2 h3 h4
    obtain ⟨m1, m2, m3, m4⟩ := ih (fun s hs => hl s (by simp [hs])) _ k1 k2 k3 k4
    rw [List.foldl_cons]
    refine ⟨m1, m2, fun o ho => m3 o (k5 o ho), fun s hs => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨o₀, m3 o₀ ho₀, hto₀⟩
    · exact m4 s hs

theorem twOrbits_spec (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (hs : a.size = M.N) :
    (∀ o ∈ M.twOrbits a, o.Nodup ∧ ∃ s : H, R.pt s ∈ o) ∧
    (∀ s : H, s * σ s = 1 → ∃ o ∈ M.twOrbits a, R.pt s ∈ o) ∧
    (∀ o ∈ M.twOrbits a, ∀ s₁ s₂ : H, R.pt s₁ ∈ o →
      (R.pt s₂ ∈ o ↔ ∃ x : H, s₂ = x⁻¹ * s₁ * σ x)) ∧
    (∀ o ∈ M.twOrbits a, ∀ y ∈ o, y < M.N) ∧
    (M.twOrbits a).Pairwise (fun o₁ o₂ => ∀ y ∈ o₁, y ∉ o₂) := by
  have _ := hs
  have horb := mem_twOrb R σ ha
  obtain ⟨k1, k2, -, k4⟩ := twFold_spec R σ
    (fun s => ((List.range M.N).map fun x => M.m (M.m M.inv[x]! s) a[x]!).eraseDups) horb _
    (fun _ _ => rfl) (M.twInvs a) (twInvs_lt R a) (Array.replicate M.N false, []) (by simp)
    (fun z => by simp [getElem!_replicate_false]) (by simp) List.Pairwise.nil
  rw [twOrbits_eq_foldl]
  refine ⟨fun o ho => ?_, fun s hs => k4 _ ((mem_twInvs R σ ha).2 ⟨s, rfl, hs⟩),
    fun o ho s₁ s₂ hs₁ => ?_, fun o ho y hy => ?_, k2⟩
  · obtain ⟨t, rfl⟩ := k1 o ho
    exact ⟨eraseDups_nodup _, t, (horb t _).2 ⟨1, by simp⟩⟩
  · obtain ⟨t, rfl⟩ := k1 o ho
    obtain ⟨y, hy⟩ := (horb t _).1 hs₁
    have e1 := R.pt_inj hy
    rw [horb]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨y⁻¹ * z, ?_⟩
      rw [R.pt_inj hz, e1, map_mul, map_inv]
      group
    · rintro ⟨x, rfl⟩
      refine ⟨y * x, congrArg R.pt ?_⟩
      rw [e1, map_mul]
      group
  · obtain ⟨t, rfl⟩ := k1 o ho
    obtain ⟨x, rfl⟩ := (horb t y).1 hy
    exact R.pt_lt _

end Rep

end CFSG.OddStandard.ChengHeld.Model
