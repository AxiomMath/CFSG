module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicCert
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique

namespace SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def tab (n : ℕ) [MulAction Γ (Fin n)] (g : Γ) : List ℕ :=
  (List.finRange n).map fun i => (g • i).val

@[expose] def compTab (s t : List ℕ) : List ℕ := t.map fun j => s.getD j 0

theorem tab_getD (g : Γ) (j : Fin n) : (tab n g).getD j.val 0 = (g • j).val := by
  simp [tab, List.getD_eq_getElem?_getD]

theorem tab_mul (g h : Γ) : tab n (g * h) = compTab (tab n g) (tab n h) := by
  unfold compTab
  simp only [tab, List.map_map]
  apply List.map_congr_left
  intro i _
  simp [Function.comp, mul_smul]

@[expose] def act (n : ℕ) [MulAction Γ (Fin n)] (g : Γ) (p : ℕ) : ℕ := (tab n g).getD p 0

theorem act_eq (g : Γ) (j : Fin n) : act n g j.val = (g • j).val := tab_getD g j

theorem act_lt (g : Γ) {p : ℕ} (hp : p < n) : act n g p < n := by
  have h : act n g p = (g • (⟨p, hp⟩ : Fin n)).val := act_eq g ⟨p, hp⟩
  rw [h]
  exact Fin.is_lt _

theorem act_mul (g h : Γ) {p : ℕ} (hp : p < n) : act n (g * h) p = act n g (act n h p) := by
  have e1 : act n h p = (h • (⟨p, hp⟩ : Fin n)).val := act_eq h ⟨p, hp⟩
  have e2 : act n g (act n h p) = (g • (h • (⟨p, hp⟩ : Fin n))).val := by
    rw [e1]; exact act_eq g (h • (⟨p, hp⟩ : Fin n))
  have e3 : act n (g * h) p = ((g * h) • (⟨p, hp⟩ : Fin n)).val := act_eq (g * h) ⟨p, hp⟩
  rw [e2, e3, mul_smul]

theorem act_one {p : ℕ} (hp : p < n) : act n (1 : Γ) p = p := by
  have e : act n (1 : Γ) p = ((1 : Γ) • (⟨p, hp⟩ : Fin n)).val := act_eq 1 ⟨p, hp⟩
  rw [e, one_smul]

theorem img_tab (g : Γ) (p : ℕ) : img (tab n g).toArray p = act n g p := by
  simp only [img, act, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

theorem act_conj (z g : Γ) {p : ℕ} (hp : p < n) :
    act n (g⁻¹ * z * g) p =
      conjImg (tab n z).toArray (tab n g).toArray (tab n g⁻¹).toArray p := by
  simp only [conjImg, img_tab]
  rw [act_mul _ _ hp, act_mul _ _ (act_lt g hp)]

theorem base_of_faithful [FaithfulSMul Γ (Fin n)] :
    ∀ g : Γ, (∀ b ∈ List.range n, act n g b = b) → g = 1 := by
  intro g hg
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin n) fun i => ?_
  rw [one_smul]
  apply Fin.ext
  have h := hg i.val (List.mem_range.mpr i.isLt)
  rwa [show act n g i.val = (g • i).val from act_eq g i] at h

@[expose] def rt (n : ℕ) [MulAction Γ (Fin n)] (P : List ℕ) (x : Γ) : List ℕ := P.map (act n x)

theorem rt_mul_left {P : List ℕ} (hP : ∀ p ∈ P, p < n) (s x : Γ) :
    rt n P (s * x) = applyTab (tab n s).toArray (rt n P x) := by
  unfold rt applyTab
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, img_tab]
  exact act_mul s x (hP p hp)

theorem rt_one {P : List ℕ} (hP : ∀ p ∈ P, p < n) : rt n P (1 : Γ) = P :=
  (List.map_congr_left (g := id) fun p hp => act_one (hP p hp)).trans (List.map_id P)

theorem rt_one_mul {P : List ℕ} (hP : ∀ p ∈ P, p < n) (z : Γ) :
    rt n P z = applyTab (tab n z).toArray P := by
  have := rt_mul_left hP z 1
  rwa [mul_one, rt_one hP] at this

theorem rt_injective {B P : List ℕ} (hB : ∀ b ∈ B, b < n) (hBP : ∀ b ∈ B, b ∈ P)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {x y : Γ}
    (h : rt n P x = rt n P y) : x = y := by
  have hxy : ∀ p ∈ P, act n x p = act n y p := List.map_inj_left.mp h
  have h1 : x⁻¹ * y = 1 := by
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb), ← hxy b (hBP b hb), ← act_mul _ _ (hB b hb), inv_mul_cancel,
      act_one (hB b hb)]
  exact inv_mul_eq_one.mp h1

theorem rt_getElem? (P : List ℕ) (x : Γ) (i : ℕ) :
    (rt n P x)[i]? = (P[i]?).map (act n x) := by
  simp [rt, List.getElem?_map]

theorem getD_of_getElem? {l : List ℕ} {i q : ℕ} (h : l[i]? = some q) : l.getD i 0 = q := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getElem?_flatMap_block {α β : Type*} (g : α → List β) (r : ℕ) :
    ∀ (L : List α), (∀ a ∈ L, (g a).length = r) → ∀ t j : ℕ, j < r →
      (L.flatMap g)[t * r + j]? = (L[t]?).bind fun a => (g a)[j]? := by
  intro L
  induction L with
  | nil => intro _ t j _; simp
  | cons a L ih =>
    intro hL t j hj
    have ha : (g a).length = r := hL a List.mem_cons_self
    have hL' : ∀ a' ∈ L, (g a').length = r := fun a' h' => hL a' (List.mem_cons_of_mem _ h')
    rw [List.flatMap_cons]
    cases t with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
      exact List.getElem?_append_left (by omega)
    | succ t =>
      have e : (t + 1) * r + j = r + (t * r + j) := by ring
      rw [e, List.getElem?_append_right (by omega)]
      simp only [ha, Nat.add_sub_cancel_left, List.getElem?_cons_succ]
      exact ih hL' t j hj

theorem ptsOf_getElem?_ext {B : List ℕ} {G : List (Array ℕ)} {t j : ℕ} (ht : t < G.length)
    (hj : j < B.length) :
    (ptsOf B G)[B.length * (1 + t) + j]? = some (img (G.getD t #[]) (B.getD j 0)) := by
  unfold ptsOf
  have e : B.length * (1 + t) + j = B.length + (t * B.length + j) := by ring
  rw [e, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  rw [getElem?_flatMap_block (fun s => B.map (img s)) B.length G (fun a _ => by simp) t j hj]
  have h1 : G[t]? = some (G.getD t #[]) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  have h2 : (B.map (img (G.getD t #[])))[j]? = some (img (G.getD t #[]) (B.getD j 0)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [h1]
  exact h2

theorem ptsOf_getElem?_base {B : List ℕ} {G : List (Array ℕ)} {j : ℕ} (hj : j < B.length) :
    (ptsOf B G)[j]? = some (B.getD j 0) := by
  unfold ptsOf
  rw [List.getElem?_append_left hj]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

@[expose] def genTabs (n : ℕ) [MulAction Γ (Fin n)] (gens : List Γ) : List (Array ℕ) :=
  gens.map fun s => (tab n s).toArray

@[expose] def genTabsInv (n : ℕ) [MulAction Γ (Fin n)] (gens : List Γ) : List (Array ℕ) :=
  gens.map fun s => (tab n s⁻¹).toArray

theorem ptsOf_lt {B : List ℕ} (hB : ∀ b ∈ B, b < n) (gens : List Γ) :
    ∀ p ∈ ptsOf B (genTabs n gens), p < n := by
  intro p hp
  unfold ptsOf at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hB p hp
  · obtain ⟨a, ha, hpa⟩ := List.mem_flatMap.mp hp
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hpa
    rw [img_tab]
    exact act_lt s (hB b hb)

theorem rt_comm_clause {B : List ℕ} (hB : ∀ b ∈ B, b < n) (gens : List Γ) (c : Γ)
    (hcc : ∀ s ∈ gens, c * s = s * c) :
    ∀ t < (genTabs n gens).length, ∀ j < B.length,
      (rt n (ptsOf B (genTabs n gens)) c).getD (B.length * (1 + t) + j) 0 =
        img ((genTabs n gens).getD t #[]) ((rt n (ptsOf B (genTabs n gens)) c).getD j 0) := by
  intro t ht j hj
  have ht' : t < gens.length := by simpa [genTabs] using ht
  have hb : B.getD j 0 < n := by
    apply hB
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hs : gens.getD t 1 ∈ gens := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
    exact List.getElem_mem ht'
  have hgt : (genTabs n gens).getD t #[] = (tab n (gens.getD t 1)).toArray := by
    simp only [genTabs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht']
    simp
  have hgen := ptsOf_getElem?_ext (B := B) (G := genTabs n gens) ht hj
  have hbase := ptsOf_getElem?_base (B := B) (G := genTabs n gens) hj
  rw [hgt] at hgen
  have hrt1 : (rt n (ptsOf B (genTabs n gens)) c)[B.length * (1 + t) + j]? =
      some (act n c (act n (gens.getD t 1) (B.getD j 0))) := by
    rw [rt_getElem?, hgen]
    simp [img_tab]
  have hrt2 : (rt n (ptsOf B (genTabs n gens)) c)[j]? = some (act n c (B.getD j 0)) := by
    rw [rt_getElem?, hbase]
    simp
  rw [getD_of_getElem? hrt1, getD_of_getElem? hrt2, hgt, img_tab]
  have := congrArg (fun x => act n x (B.getD j 0)) (hcc _ hs)
  rw [act_mul _ _ hb, act_mul _ _ hb] at this
  exact this

theorem benum_reach {B : List ℕ} (hB : ∀ b ∈ B, b < n) (gens : List Γ) (Ts : Array (List ℕ))
    (par cl : Array ℕ)
    (h : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl) :
    ∀ i, i < Ts.size → ∃ x ∈ Subgroup.closure {x | x ∈ gens},
      rt n (ptsOf B (genTabs n gens)) x = Ts[i]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [rt_one (ptsOf_lt hB gens), h.2.1]⟩
    · obtain ⟨hlt, s, hs, heq⟩ := h.2.2.2.1 i hi hpos
      obtain ⟨y, hy, hty⟩ := ih (par[i]!) hlt (lt_trans hlt hi)
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
      exact ⟨s' * y, mul_mem (Subgroup.subset_closure hs') hy,
        by rw [rt_mul_left (ptsOf_lt hB gens), hty, heq]⟩

theorem benum_closed {B : List ℕ} (hB : ∀ b ∈ B, b < n) (gens : List Γ) (Ts : Array (List ℕ))
    (par cl : Array ℕ)
    (h : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl) :
    ∀ x ∈ Subgroup.closure {x | x ∈ gens}, rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := by
  have hP := ptsOf_lt hB gens
  obtain ⟨h0, h1, _, _, _, hcl1, hcl2⟩ := h
  have key : ∀ y : Γ, rt n (ptsOf B (genTabs n gens)) y ∈ Ts.toList → ∀ s ∈ gens,
      rt n (ptsOf B (genTabs n gens)) (s * y) ∈ Ts.toList ∧
      rt n (ptsOf B (genTabs n gens)) (s⁻¹ * y) ∈ Ts.toList := by
    intro y hy s hs
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
    have hiT : i < Ts.size := by simpa using hi
    have hiy' : Ts[i]! = rt n (ptsOf B (genTabs n gens)) y := by
      rw [getElem!_pos Ts i hiT]; simpa using hiy
    obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
    have hjG : j < (genTabs n gens).length := by simpa [genTabs] using hj
    have hjGi : j < (genTabsInv n gens).length := by simpa [genTabsInv] using hj
    obtain ⟨hlt1, heq1⟩ := hcl1 i hiT j hjG
    obtain ⟨hlt2, heq2⟩ := hcl2 i hiT j hjGi
    have e1 : (genTabs n gens)[j]! = (tab n s).toArray := by
      rw [getElem!_pos _ j hjG]; simp [genTabs, hjs]
    have e2 : (genTabsInv n gens)[j]! = (tab n s⁻¹).toArray := by
      rw [getElem!_pos _ j hjGi]; simp [genTabsInv, hjs]
    constructor
    · rw [rt_mul_left hP, ← hiy', ← e1, ← heq1, getElem!_pos Ts _ hlt1]
      exact Array.getElem_mem_toList hlt1
    · rw [rt_mul_left hP, ← hiy', ← e2, ← heq2, getElem!_pos Ts _ hlt2]
      exact Array.getElem_mem_toList hlt2
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one =>
    rw [rt_one hP]
    have h0' : Ts[0]! ∈ Ts.toList := by
      rw [getElem!_pos Ts 0 h0]
      exact Array.getElem_mem_toList h0
    rwa [h1] at h0'
  | mul_left s hs y _ ih => exact (key y ih s hs).1
  | inv_mul_cancel s hs y _ ih => exact (key y ih s hs).2

theorem benum_card {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (gens : List Γ) (Ts : Array (List ℕ))
    (par cl : Array ℕ)
    (h : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl) :
    Nat.card ↥(Subgroup.closure {x | x ∈ gens}) = Ts.size := by
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  have hinj : Function.Injective (rt n (ptsOf B (genTabs n gens)) : Γ → List ℕ) :=
    fun x y hxy => rt_injective hB hBP hbase hxy
  have himg : rt n (ptsOf B (genTabs n gens)) '' (Subgroup.closure {x | x ∈ gens} : Set Γ) =
      {T | T ∈ Ts.toList} := by
    ext T
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact benum_closed hB gens Ts par cl h x hx
    · intro hT
      obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hT
      have hiT' : i < Ts.size := by simpa using hi
      obtain ⟨x, hx, hxT⟩ := benum_reach hB gens Ts par cl h i hiT'
      refine ⟨x, hx, ?_⟩
      rw [hxT, getElem!_pos Ts i hiT']
      simpa using hiT
  have h1 : Nat.card ↥(Subgroup.closure {x | x ∈ gens}) =
      (rt n (ptsOf B (genTabs n gens)) '' (Subgroup.closure {x | x ∈ gens} : Set Γ)).ncard := by
    rw [Set.ncard_image_of_injective _ hinj]
    exact Nat.card_coe_set_eq _
  rw [h1, himg]
  have hnodup : Ts.toList.Nodup := List.Nodup.of_map _ h.2.2.2.2.1
  have : {T | T ∈ Ts.toList} = ((Ts.toList.toFinset : Finset (List ℕ)) : Set (List ℕ)) := by
    ext T; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup]
  simp

theorem noStronglyClosedElemAbelian_of_baseCert [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (qs : List (Γ × Γ))
    (z g gi h hi : Γ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ)
    (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : BaseCert n B (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray))
      (tab n z).toArray (tab n g).toArray (tab n gi).toArray (tab n h).toArray
      (tab n hi).toArray Ts par cl k) :
    NoStronglyClosedElemAbelian Γ := by
  obtain ⟨hinv, hgi, hhi, hEnum, hsize, hcen, hu, hv, hnc⟩ := hcert
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  have hgi' : gi = g⁻¹ := hinv_of g gi hgi
  have hhi' : hi = h⁻¹ := hinv_of h hi hhi
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := fun p hp =>
    hinv_of p.1 p.2 (hinv _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  subst hgi' hhi'
  let gens : List Γ := qs.map Prod.fst
  have hG : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.fst =
      genTabs n gens := by
    simp only [genTabs, gens, List.map_map, Function.comp_def]
  have hGi : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.snd =
      genTabsInv n gens := by
    simp only [genTabsInv, gens, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [hqsinv p hp]
  rw [hG, hGi] at hEnum
  rw [hG] at hcen hu hv
  have hP : ∀ p ∈ ptsOf B (genTabs n gens), p < n := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  let Q : Subgroup Γ := Subgroup.closure {x | x ∈ gens}
  have hQmem : ∀ x : Γ, x ∈ Q ↔ rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := by
    intro x
    refine ⟨benum_closed hB gens Ts par cl hEnum x, fun hx => ?_⟩
    obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hx
    have hiT' : i < Ts.size := by simpa using hi
    obtain ⟨y, hy, hyT⟩ := benum_reach hB gens Ts par cl hEnum i hiT'
    have : rt n (ptsOf B (genTabs n gens)) y = rt n (ptsOf B (genTabs n gens)) x := by
      rw [hyT, getElem!_pos Ts i hiT']
      simpa using hiT
    rwa [← rt_injective hB hBP hbase this]
  have hcardQ : Nat.card Q = 2 ^ k := by
    rw [benum_card hB hbase gens Ts par cl hEnum, hsize]
  have hQp2 : IsPGroup 2 Q := IsPGroup.of_card hcardQ
  have hQindex : Q.index = m := by
    have h1 := Q.card_mul_index
    rw [hcardQ, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hQsyl : IsSylowTwoOf Q ⊤ := isSylowTwoOf_top_iff.mpr ⟨hQp2, by
    rw [hQindex]; exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)⟩
  have hconj : ∀ w x : Γ, rt n (ptsOf B (genTabs n gens)) (x⁻¹ * w * x) =
      (ptsOf B (genTabs n gens)).map
        (conjImg (tab n w).toArray (tab n x).toArray (tab n x⁻¹).toArray) := by
    intro w x
    unfold rt
    apply List.map_congr_left
    intro p hp
    exact act_conj w x (hP p hp)
  have hgQ : g⁻¹ * z * g ∈ Q := (hQmem _).mpr (by rw [hconj]; exact hu)
  have hhQ : h⁻¹ * z * h ∈ Q := (hQmem _).mpr (by rw [hconj]; exact hv)
  have hnc' : (g⁻¹ * z * g) * (h⁻¹ * z * h) ≠ (h⁻¹ * z * h) * (g⁻¹ * z * g) := by
    intro heq
    obtain ⟨j, hj, hne⟩ := hnc
    apply hne
    have hb : B.getD j 0 < n := by
      apply hB
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem hj
    have hact := congrArg (fun x => act n x (B.getD j 0)) heq
    rw [act_mul (g⁻¹ * z * g) (h⁻¹ * z * h) hb, act_mul (h⁻¹ * z * h) (g⁻¹ * z * g) hb,
      act_conj z g (act_lt (h⁻¹ * z * h) hb), act_conj z h (act_lt (g⁻¹ * z * g) hb),
      act_conj z h hb, act_conj z g hb] at hact
    exact hact
  have hcen' : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z := by
    intro c hcQ hcc
    have hcT : rt n (ptsOf B (genTabs n gens)) c ∈ Ts.toList := (hQmem c).mp hcQ
    have hcomm := rt_comm_clause hB gens c fun s hs =>
      hcc s (Subgroup.subset_closure hs)
    rcases hcen _ hcT hcomm with h1 | h1
    · left
      exact rt_injective hB hBP hbase (by rw [h1, rt_one hP])
    · right
      exact rt_injective hB hBP hbase (by rw [h1, rt_one_mul hP])
  exact noStronglyClosedElemAbelian_of_center_witness Q hQsyl z hcen' g h hgQ hhQ hnc'

theorem compArr_toList (s t : Array ℕ) : (compArr s t).toList = compTab s.toList t.toList := by
  unfold compTab compArr
  simp only [Array.toList_map]
  apply List.map_congr_left
  intro j _
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < s.size
  · simp [getElem!_pos s j h, Array.getElem?_eq_getElem h]
  · simp [getElem!_neg s j h, Array.getElem?_eq_none (by omega : s.size ≤ j)]

theorem getD_push_lt {α : Type*} (a : Array α) (x d : α) {i : ℕ} (hi : i < a.size) :
    (a.push x).getD i d = a.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hi]
  simp [Array.getElem?_eq_getElem hi]

theorem getD_push_self {α : Type*} (a : Array α) (x d : α) : (a.push x).getD a.size d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
  rfl

theorem getElem!_push_lt' {α : Type*} [Inhabited α] (a : Array α) (x : α) {i : ℕ}
    (hi : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i hi]
  exact Array.getElem_push_lt hi

theorem getElem!_push_self' {α : Type*} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  simp

@[expose] def eltStep (acc : Array Γ) (p : ℕ × ℕ) : Array Γ :=
  acc.push (acc.getD p.1 1 * acc.getD p.2 1)

@[expose] def slpElts (a b : Γ) (prog : List (ℕ × ℕ)) : Array Γ := prog.foldl eltStep #[a, b]

theorem slp_foldl_inv (prog : List (ℕ × ℕ)) (E : Array Γ) (T : Array (Array ℕ))
    (hE : E.size = T.size) (hT : ∀ i < T.size, tab n (E.getD i 1) = (T[i]!).toList)
    (hv : slpValidAux prog T.size = true) :
    (prog.foldl eltStep E).size = (prog.foldl slpStepA T).size ∧
    ∀ i < (prog.foldl slpStepA T).size, tab n ((prog.foldl eltStep E).getD i 1) =
      ((prog.foldl slpStepA T)[i]!).toList := by
  induction prog generalizing E T with
  | nil => exact ⟨hE, hT⟩
  | cons p prog ih =>
    simp only [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hp, hv'⟩ := hv
    simp only [List.foldl_cons]
    have hTs : (slpStepA T p).size = T.size + 1 := by simp [slpStepA]
    refine ih (eltStep E p) (slpStepA T p) ?_ ?_ (by rw [hTs]; exact hv')
    · simp [eltStep, slpStepA, hE]
    · intro i hi
      rw [hTs] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · simp only [eltStep, slpStepA]
        rw [getD_push_lt E _ 1 (by omega), getElem!_push_lt' T _ hi]
        exact hT i hi
      · subst hi
        simp only [eltStep, slpStepA]
        have e1 : (E.push (E.getD p.1 1 * E.getD p.2 1)).getD T.size 1 =
            E.getD p.1 1 * E.getD p.2 1 := by
          rw [← hE]; exact getD_push_self E _ 1
        have e2 : (T.push (compArr T[p.1]! T[p.2]!))[T.size]! = compArr T[p.1]! T[p.2]! :=
          getElem!_push_self' T _
        rw [e1, e2, tab_mul, compArr_toList, hT p.1 hp.1, hT p.2 hp.2]

theorem noStronglyClosedElemAbelian_of_baseCertS [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m)
    (hm : Odd m)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    NoStronglyClosedElemAbelian Γ := by
  obtain ⟨hqp, hz, hg, hgi, hh, hhi, hc⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  refine noStronglyClosedElemAbelian_of_baseCert B hB hbase
    (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1))
    ((slpElts a b prog).getD zn 1) ((slpElts a b prog).getD gn 1) ((slpElts a b prog).getD gin 1)
    ((slpElts a b prog).getD hn 1) ((slpElts a b prog).getD hin 1) Ts par cl k m hcard hm ?_
  rw [hE' zn hz, hE' gn hg, hE' gin hgi, hE' hn hh, hE' hin hhi]
  have : (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1)).map
      (fun p => ((tab n p.1).toArray, (tab n p.2).toArray)) =
        qp.map fun p => (T[p.1]!, T[p.2]!) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
  rw [this]
  exact hc

end SporadicPerm

end CFSG.QuasithinUnique.K1
