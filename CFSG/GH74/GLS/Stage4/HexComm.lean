module

public import CFSG.GH74.GLS.Stage4.HexRoots
public import CFSG.GH74.GLS.SP.DatumBN
public import CFSG.GH74.GLS.SP.GlueDefs
public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LieType.TitsSimplicity.Unipotent

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

abbrev g2Shape
    {K : Type*} [Group K] (X : (Fin 2 → ℤ) → Subgroup K) :
    UniversalRootDatum K where
  rank := 2
  cartan := cartanG2
  isFiniteType := CFSG.LieType.Chevalley.isFiniteType_cartan .G2
  divisible := ∅
  rootGroup := X

section Shape

variable {K : Type*} [Group K] (X : (Fin 2 → ℤ) → Subgroup K)

theorem g2Shape_roots
    : (g2Shape X).roots = {γ | IsRoot .G2 γ} :=
  CFSG.LieType.Steinberg.Adjoint.roots_eq_setOf_isRoot (CFSG.LieType.Chevalley.isFiniteType_cartan .G2)

theorem mem_g2Shape_roots
    {γ : Fin 2 → ℤ} : γ ∈ (g2Shape X).roots ↔ IsRoot .G2 γ := by
  rw [g2Shape_roots]
  rfl

theorem hexPos_mem_roots
    {i : ℤ} (h0 : i ≠ 0) (h6 : i.natAbs ≤ 6) :
    hexPos i ∈ (g2Shape X).roots :=
  (mem_g2Shape_roots X).2 (isRoot_hexPos h0 h6)

@[expose] def hexGroup (i : ℤ) : Subgroup K := X (hexPos i)

end Shape

section Comm

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

theorem hexComm
    (hext : SteinbergExtras (g2Shape X) n H) : OctComm (hexGroup X) ((6 : ℕ) : ℤ) := by
  intro a b ha hab hb x hx y hy
  have hb6 : b ≤ 6 := by exact_mod_cast hb
  have hlin := linIndep_hexPos (by omega) (by omega) (by omega) hb6 hab.ne
  have hcomm := hext.commutator_mem (hexPos a) (hexPos_mem_roots X (by omega) (by omega))
    (hexPos b) (hexPos_mem_roots X (by omega) (by omega)) hlin x hx y hy
  refine (iSup₂_le fun ε hε => ?_ : (⨆ ε ∈ openCone (g2Shape X).roots (hexPos a) (hexPos b),
    (g2Shape X).rootGroup ε) ≤ _) hcomm
  obtain ⟨hεroot, i, j, hi, hj, he⟩ := hε
  obtain ⟨c, hac, hcb, rfl⟩ := cone_between (by omega) hab hb6 ((mem_g2Shape_roots X).1 hεroot) hi hj he
  exact le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo a b) => hexGroup X c) c ⟨hac, hcb⟩ le_rfl

end Comm

section Unique

variable {K : Type*} [Group K]

theorem prod_map_ite_eq_filter {α : Type*} (L : List α) (p : α → Bool) (f : α → K) :
    (L.map fun γ => if p γ = true then f γ else 1).prod = ((L.filter p).map f).prod := by
  induction L with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a = true
    · simp [h, ih]
    · simp [h, ih]

theorem prod_map_ite_single {α : Type*} [DecidableEq α] (L : List α) (hnd : L.Nodup) (r : α)
    (hr : r ∈ L) (x : K) : (L.map fun γ => if γ = r then x else 1).prod = x := by
  induction L with
  | nil => simp at hr
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    by_cases h : a = r
    · subst h
      have h1 : ∀ γ ∈ l, (if γ = a then x else (1 : K)) = 1 := by
        intro γ hγ
        have : γ ≠ a := fun e => hnd.1 (e ▸ hγ)
        simp [this]
      simp [List.map_congr_left h1]
    · have hr' : r ∈ l := (List.mem_cons.1 hr).resolve_left (Ne.symm h)
      simp [h, ih hnd.2 hr']

theorem inf_iSup_filter_eq_bot {ι : Type*} [DecidableEq ι] {A : ι → Subgroup K} {L : List ι}
    (hnd : L.Nodup)
    (hinj : ∀ f g : ι → K, (∀ γ ∈ L, f γ ∈ A γ) → (∀ γ ∈ L, g γ ∈ A γ) →
      (L.map f).prod = (L.map g).prod → ∀ γ ∈ L, f γ = g γ)
    {p : ι → Bool} {r : ι} (hr : r ∈ L) (hpr : p r = false)
    (hcoll : ∀ g ∈ ⨆ γ ∈ L.filter p, A γ,
      ∃ f : ι → K, (∀ γ ∈ L.filter p, f γ ∈ A γ) ∧ g = ((L.filter p).map f).prod) :
    A r ⊓ (⨆ γ ∈ L.filter p, A γ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxS⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨f, hf, hfx⟩ := hcoll x hxS
  have h := hinj (fun γ => if p γ = true then f γ else 1) (fun γ => if γ = r then x else 1)
    (fun γ hγ => by
      by_cases hp : p γ = true
      · simp [hp]
        exact hf γ (List.mem_filter.2 ⟨hγ, hp⟩)
      · simp [hp])
    (fun γ hγ => by
      by_cases hγr : γ = r
      · simp [hγr]
        exact hγr ▸ hxA
      · simp [hγr])
    (by rw [prod_map_ite_eq_filter, prod_map_ite_single L hnd r hr, hfx]) r hr
  simpa [hpr] using h.symm

end Unique

section HeightList

@[expose] def heightList : List (Fin 2 → ℤ) :=
  [hexPos 1, hexPos 6, hexPos 5, hexPos 3, hexPos 2, hexPos 4]

theorem heightList_nodup : heightList.Nodup := by
  decide +kernel

theorem heightList_sorted : heightList.Pairwise (fun γ δ => ht γ ≤ ht δ) := by
  decide +kernel

theorem hexPos_mem_heightList {k : ℤ} (h1 : 1 ≤ k) (h6 : k ≤ 6) : hexPos k ∈ heightList := by
  interval_cases k <;> decide +kernel

theorem mem_heightList_iff {γ : Fin 2 → ℤ} :
    γ ∈ heightList ↔ IsRoot .G2 γ ∧ 0 < ht γ ∧ ∀ δ : Fin 2 → ℤ, IsRoot .G2 δ → γ ≠ 2 • δ := by
  constructor
  · intro h
    have : ∃ k : ℤ, 1 ≤ k ∧ k ≤ 6 ∧ γ = hexPos k := by
      simp only [heightList, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, by norm_num, rfl⟩
      · exact ⟨6, by norm_num, by norm_num, rfl⟩
      · exact ⟨5, by norm_num, by norm_num, rfl⟩
      · exact ⟨3, by norm_num, by norm_num, rfl⟩
      · exact ⟨2, by norm_num, by norm_num, rfl⟩
      · exact ⟨4, by norm_num, by norm_num, rfl⟩
    obtain ⟨k, hk1, hk6, rfl⟩ := this
    exact ⟨isRoot_hexPos (by omega) (by omega), ht_hexPos_pos hk1 hk6,
      fun δ _ => hexPos_ne_two_smul hk1 hk6 δ⟩
  · rintro ⟨hr, hp, -⟩
    obtain ⟨k, hk1, hk6, rfl⟩ := pos_root_cases hr hp
    exact hexPos_mem_heightList hk1 hk6

end HeightList

section Suffix

theorem ht_nsmul_add (u v : Fin 2 → ℤ) (i j : ℕ) : ht (i • u + j • v) = i * ht u + j * ht v := by
  simp only [ht, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  ring

theorem cone_between_sym
    {a b : ℤ} (ha1 : 1 ≤ a) (ha6 : a ≤ 6) (hb1 : 1 ≤ b) (hb6 : b ≤ 6)
    (hab : a ≠ b) {ε : Fin 2 → ℤ} (hε : IsRoot .G2 ε) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (he : ε = i • hexPos a + j • hexPos b) :
    ∃ c : ℤ, min a b < c ∧ c < max a b ∧ ε = hexPos c := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨c, h1, h2, h3⟩ := cone_between ha1 h hb6 hε hi hj he
    exact ⟨c, by rw [min_eq_left h.le]; exact h1, by rw [max_eq_right h.le]; exact h2, h3⟩
  · rw [add_comm] at he
    obtain ⟨c, h1, h2, h3⟩ := cone_between hb1 h ha6 hε hj hi he
    exact ⟨c, by rw [min_eq_right h.le]; exact h1, by rw [max_eq_left h.le]; exact h2, h3⟩

@[expose] def sufPred (k : ℤ) (γ : Fin 2 → ℤ) : Bool :=
  decide (γ ∈ (intList (k + 1) 6).map hexPos)

@[expose] def sufList (k : ℤ) : List (Fin 2 → ℤ) :=
  heightList.filter (sufPred k)

theorem mem_sufList_iff {k : ℤ} (hk : 0 ≤ k) {γ : Fin 2 → ℤ} :
    γ ∈ sufList k ↔ ∃ c : ℤ, k + 1 ≤ c ∧ c ≤ 6 ∧ γ = hexPos c := by
  rw [sufList, List.mem_filter]
  constructor
  · rintro ⟨-, hp⟩
    simp only [sufPred, decide_eq_true_eq, List.mem_map, mem_intList_iff] at hp
    obtain ⟨c, ⟨h1, h2⟩, rfl⟩ := hp
    exact ⟨c, h1, h2, rfl⟩
  · rintro ⟨c, h1, h2, rfl⟩
    refine ⟨hexPos_mem_heightList (by omega) h2, ?_⟩
    simp only [sufPred, decide_eq_true_eq, List.mem_map, mem_intList_iff]
    exact ⟨c, ⟨h1, h2⟩, rfl⟩

theorem hexPos_notMem_sufList {k : ℤ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) : hexPos k ∉ sufList k := by
  intro h
  obtain ⟨c, h1, h2, e⟩ := (mem_sufList_iff (by omega)).1 h
  have := hexPos_inj (by omega) (by omega) (by omega) h2 e
  omega

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

theorem collection_suf
    (hext : SteinbergExtras (g2Shape X) n H) {k : ℤ} (hk0 : 0 ≤ k) (hk5 : k ≤ 5) :
    ∀ g ∈ ⨆ γ ∈ sufList k, X γ, ∃ f : (Fin 2 → ℤ) → K, (∀ γ ∈ sufList k, f γ ∈ X γ) ∧
      g = ((sufList k).map f).prod := by
  refine exists_prod_eq_of_commutator_mem X ht (heightList_nodup.filter _)
    (heightList_sorted.filter _) ?_
  intro a ha b hb hab x hx y hy
  obtain ⟨pa, hpa1, hpa6, rfl⟩ := (mem_sufList_iff hk0).1 ha
  obtain ⟨pb, hpb1, hpb6, rfl⟩ := (mem_sufList_iff hk0).1 hb
  have hpab : pa ≠ pb := fun e => hab (by rw [e])
  have hcomm := hext.commutator_mem (hexPos pa) (hexPos_mem_roots X (by omega) (by omega))
    (hexPos pb) (hexPos_mem_roots X (by omega) (by omega))
    (linIndep_hexPos (by omega) hpa6 (by omega) hpb6 hpab) x hx y hy
  refine (iSup₂_le fun ε hε => ?_ : (⨆ ε ∈ openCone (g2Shape X).roots (hexPos pa) (hexPos pb),
    (g2Shape X).rootGroup ε) ≤ _) hcomm
  obtain ⟨hεroot, i, j, hi, hj, he⟩ := hε
  obtain ⟨c, hc1, hc2, rfl⟩ := cone_between_sym (by omega) hpa6 (by omega) hpb6 hpab
    ((mem_g2Shape_roots X).1 hεroot) hi hj he
  have hmem : hexPos c ∈ sufList k := (mem_sufList_iff hk0).2 ⟨c, by omega, by omega, rfl⟩
  have hht : min (ht (hexPos pa)) (ht (hexPos pb)) < ht (hexPos c) := by
    rw [he, ht_nsmul_add]
    have ha := ht_hexPos_pos (show 1 ≤ pa by omega) hpa6
    have hb := ht_hexPos_pos (show 1 ≤ pb by omega) hpb6
    have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
    have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have := min_le_left (ht (hexPos pa)) (ht (hexPos pb))
    nlinarith
  exact le_iSup₂_of_le (f := fun c' (_ : c' ∈ sufList k) =>
    ⨆ (_ : min (ht (hexPos pa)) (ht (hexPos pb)) < ht c'), X c') (hexPos c) hmem
    (le_iSup_of_le hht le_rfl)

theorem hexProdInjective
    (hext : SteinbergExtras (g2Shape X) n H) :
    ProdInjectiveFor X heightList :=
  hext.prodInjective_pos heightList heightList_nodup
    (fun γ => by
      rw [mem_heightList_iff]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨(mem_g2Shape_roots X).2 h1, h2,
          fun δ hδ => h3 δ ((mem_g2Shape_roots X).1 hδ)⟩,
        fun ⟨h1, h2, h3⟩ => ⟨(mem_g2Shape_roots X).1 h1, h2,
          fun δ hδ => h3 δ ((mem_g2Shape_roots X).2 hδ)⟩⟩) heightList_sorted

end Suffix

section Disjoint

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

theorem hexGroup_inf_suf
    (hext : SteinbergExtras (g2Shape X) n H) {k : ℤ} (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) : hexGroup X k ⊓ (⨆ γ ∈ sufList k, X γ) = ⊥ := by
  have hinj := hexProdInjective hext
  have hpr : sufPred k (hexPos k) = false := by
    rw [sufPred, decide_eq_false_iff_not]
    intro hmem
    obtain ⟨c, hc, e⟩ := List.mem_map.1 hmem
    have hc' := mem_intList_iff.1 hc
    have := hexPos_inj (by omega) (by omega) (by omega) (by omega) e
    omega
  have := inf_iSup_filter_eq_bot (A := X) (L := heightList) heightList_nodup
    (fun f g hf hg h => hinj f g hf hg h) (p := sufPred k) (r := hexPos k)
    (hexPos_mem_heightList hk1 (by omega)) hpr (collection_suf hext (by omega) hk5)
  exact this

end Disjoint

section UniqueFinal

variable {K : Type*} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
  {H : Fin 2 → Subgroup K}

@[expose] def hexSuf (X : (Fin 2 → ℤ) → Subgroup K) (j : ℤ) : Subgroup K :=
  ⨆ i ∈ intList (j + 1) 6, hexGroup X i

theorem iSup_sufList_eq {j : ℤ} (hj : 0 ≤ j) : ⨆ γ ∈ sufList j, X γ = hexSuf X j := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) (iSup₂_le fun i hi => ?_)
  · obtain ⟨c, h1, h2, rfl⟩ := (mem_sufList_iff hj).1 hγ
    exact le_iSup₂_of_le (f := fun i (_ : i ∈ intList (j + 1) 6) => hexGroup X i) c
      (mem_intList_iff.2 ⟨h1, h2⟩) le_rfl
  · obtain ⟨h1, h2⟩ := mem_intList_iff.1 hi
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ sufList j) => X γ) (hexPos i)
      ((mem_sufList_iff hj).2 ⟨i, h1, h2, rfl⟩) le_rfl

theorem mem_hexSuf {j i : ℤ} (hji : j < i) (hi6 : i ≤ 6) {x : K} (hx : x ∈ hexGroup X i) :
    x ∈ hexSuf X j :=
  (le_iSup₂_of_le (f := fun i (_ : i ∈ intList (j + 1) 6) => hexGroup X i) i
    (mem_intList_iff.2 ⟨by omega, hi6⟩) le_rfl : hexGroup X i ≤ hexSuf X j) hx

theorem hexGroup_inf_hexSuf
    (hext : SteinbergExtras (g2Shape X) n H) {k : ℤ} (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) : hexGroup X k ⊓ hexSuf X k = ⊥ := by
  rw [← iSup_sufList_eq (by omega)]
  exact hexGroup_inf_suf hext hk1 hk5

theorem hexUnique
    (hext : SteinbergExtras (g2Shape X) n H) :
    ∀ f g : ℤ → K, (∀ k ∈ intList 1 ((6 : ℕ) : ℤ), f k ∈ hexGroup X k) →
      (∀ k ∈ intList 1 ((6 : ℕ) : ℤ), g k ∈ hexGroup X k) →
      ((intList 1 ((6 : ℕ) : ℤ)).map f).prod = ((intList 1 ((6 : ℕ) : ℤ)).map g).prod →
        ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), f k = g k := by
  have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
  intro f g hf hg hfg k hk
  rw [hl] at hf hg hfg hk
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hfg
  have hf' : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → f i ∈ hexGroup X i := fun i h1 h6 =>
    hf i (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  have hg' : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → g i ∈ hexGroup X i := fun i h1 h6 =>
    hg i (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  have step : ∀ j : ℤ, 1 ≤ j → j ≤ 5 → ∀ a b t u : K, a ∈ hexGroup X j → b ∈ hexGroup X j →
      t ∈ hexSuf X j → u ∈ hexSuf X j → a * t = b * u → a = b ∧ t = u := by
    intro j hj1 hj5 a b t u ha hb ht hu h
    have e : b⁻¹ * a = u * t⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a * t) * t⁻¹ := by group
        _ = b⁻¹ * (b * u) * t⁻¹ := by rw [h]
        _ = u * t⁻¹ := by group
    have hmem : b⁻¹ * a ∈ hexGroup X j ⊓ hexSuf X j :=
      Subgroup.mem_inf.2 ⟨(hexGroup X j).mul_mem ((hexGroup X j).inv_mem hb) ha,
        e ▸ (hexSuf X j).mul_mem hu ((hexSuf X j).inv_mem ht)⟩
    rw [hexGroup_inf_hexSuf hext hj1 hj5, Subgroup.mem_bot] at hmem
    have hab : b = a := inv_mul_eq_one.1 hmem
    subst hab
    exact ⟨rfl, mul_left_cancel h⟩
  have s : ∀ (j i : ℤ) (x : K), j < i → i ≤ 6 → 1 ≤ i → x ∈ hexGroup X i → x ∈ hexSuf X j :=
    fun j i x h1 h2 _ hx => mem_hexSuf h1 h2 hx
  obtain ⟨e1, h2⟩ := step 1 (by norm_num) (by norm_num) _ _ _ _ (hf' 1 (by norm_num) (by norm_num))
    (hg' 1 (by norm_num) (by norm_num))
    (mul_mem (s 1 2 _ (by norm_num) (by norm_num) (by norm_num) (hf' 2 (by norm_num) (by norm_num)))
      (mul_mem (s 1 3 _ (by norm_num) (by norm_num) (by norm_num) (hf' 3 (by norm_num) (by norm_num)))
        (mul_mem (s 1 4 _ (by norm_num) (by norm_num) (by norm_num) (hf' 4 (by norm_num) (by norm_num)))
          (mul_mem (s 1 5 _ (by norm_num) (by norm_num) (by norm_num) (hf' 5 (by norm_num) (by norm_num)))
            (s 1 6 _ (by norm_num) (by norm_num) (by norm_num) (hf' 6 (by norm_num) (by norm_num)))))))
    (mul_mem (s 1 2 _ (by norm_num) (by norm_num) (by norm_num) (hg' 2 (by norm_num) (by norm_num)))
      (mul_mem (s 1 3 _ (by norm_num) (by norm_num) (by norm_num) (hg' 3 (by norm_num) (by norm_num)))
        (mul_mem (s 1 4 _ (by norm_num) (by norm_num) (by norm_num) (hg' 4 (by norm_num) (by norm_num)))
          (mul_mem (s 1 5 _ (by norm_num) (by norm_num) (by norm_num) (hg' 5 (by norm_num) (by norm_num)))
            (s 1 6 _ (by norm_num) (by norm_num) (by norm_num) (hg' 6 (by norm_num) (by norm_num)))))))
    hfg
  obtain ⟨e2, h3⟩ := step 2 (by norm_num) (by norm_num) _ _ _ _ (hf' 2 (by norm_num) (by norm_num))
    (hg' 2 (by norm_num) (by norm_num))
    (mul_mem (s 2 3 _ (by norm_num) (by norm_num) (by norm_num) (hf' 3 (by norm_num) (by norm_num)))
      (mul_mem (s 2 4 _ (by norm_num) (by norm_num) (by norm_num) (hf' 4 (by norm_num) (by norm_num)))
        (mul_mem (s 2 5 _ (by norm_num) (by norm_num) (by norm_num) (hf' 5 (by norm_num) (by norm_num)))
          (s 2 6 _ (by norm_num) (by norm_num) (by norm_num) (hf' 6 (by norm_num) (by norm_num))))))
    (mul_mem (s 2 3 _ (by norm_num) (by norm_num) (by norm_num) (hg' 3 (by norm_num) (by norm_num)))
      (mul_mem (s 2 4 _ (by norm_num) (by norm_num) (by norm_num) (hg' 4 (by norm_num) (by norm_num)))
        (mul_mem (s 2 5 _ (by norm_num) (by norm_num) (by norm_num) (hg' 5 (by norm_num) (by norm_num)))
          (s 2 6 _ (by norm_num) (by norm_num) (by norm_num) (hg' 6 (by norm_num) (by norm_num))))))
    h2
  obtain ⟨e3, h4⟩ := step 3 (by norm_num) (by norm_num) _ _ _ _ (hf' 3 (by norm_num) (by norm_num))
    (hg' 3 (by norm_num) (by norm_num))
    (mul_mem (s 3 4 _ (by norm_num) (by norm_num) (by norm_num) (hf' 4 (by norm_num) (by norm_num)))
      (mul_mem (s 3 5 _ (by norm_num) (by norm_num) (by norm_num) (hf' 5 (by norm_num) (by norm_num)))
        (s 3 6 _ (by norm_num) (by norm_num) (by norm_num) (hf' 6 (by norm_num) (by norm_num)))))
    (mul_mem (s 3 4 _ (by norm_num) (by norm_num) (by norm_num) (hg' 4 (by norm_num) (by norm_num)))
      (mul_mem (s 3 5 _ (by norm_num) (by norm_num) (by norm_num) (hg' 5 (by norm_num) (by norm_num)))
        (s 3 6 _ (by norm_num) (by norm_num) (by norm_num) (hg' 6 (by norm_num) (by norm_num)))))
    h3
  obtain ⟨e4, h5⟩ := step 4 (by norm_num) (by norm_num) _ _ _ _ (hf' 4 (by norm_num) (by norm_num))
    (hg' 4 (by norm_num) (by norm_num))
    (mul_mem (s 4 5 _ (by norm_num) (by norm_num) (by norm_num) (hf' 5 (by norm_num) (by norm_num)))
      (s 4 6 _ (by norm_num) (by norm_num) (by norm_num) (hf' 6 (by norm_num) (by norm_num))))
    (mul_mem (s 4 5 _ (by norm_num) (by norm_num) (by norm_num) (hg' 5 (by norm_num) (by norm_num)))
      (s 4 6 _ (by norm_num) (by norm_num) (by norm_num) (hg' 6 (by norm_num) (by norm_num))))
    h4
  obtain ⟨e5, e6⟩ := step 5 (by norm_num) (by norm_num) _ _ _ _ (hf' 5 (by norm_num) (by norm_num))
    (hg' 5 (by norm_num) (by norm_num))
    (s 5 6 _ (by norm_num) (by norm_num) (by norm_num) (hf' 6 (by norm_num) (by norm_num)))
    (s 5 6 _ (by norm_num) (by norm_num) (by norm_num) (hg' 6 (by norm_num) (by norm_num)))
    h5
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

end UniqueFinal

end CFSG.GH74.GLS.Stage4.Hex
