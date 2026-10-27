
module

public import CFSG.Fischer.Polar.HyperovalBase
import all CFSG.Fischer.Polar.HyperovalBase

public import CFSG.Fischer.Polar.LocalSets
public import CFSG.Fischer.Polar.PerpPerp
import all CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

local notation "PT" => perpTab ()
local notation "LAM" => lamTab ()
local notation "CT" => mkCtx (perpTab ()) (gWords ()) (lamTab ())
local notation "HU" => Prod.fst (hypEnum 1) ++ Prod.fst (hypEnum 2) ++ Prod.fst (hypEnum 3)

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  perpLists lineTab lamTab gWords hypEnum t46XT t46YT famIndex

theorem hypOrbitFacts (i : Fin 3) :
    HypOrbitFacts (rootFlags (i.val + 1)) (hypEnum (i.val + 1)) := by
  fin_cases i
  · exact hypOrbitFacts_of hypFacts.orbit₁
  · exact hypOrbitFacts_of hypFacts.orbit₂
  · exact hypOrbitFacts_of hypFacts.orbit₃

theorem rep_hypGensInv {l : ℕ} (hl : l < 2) : Rep 693 (hypGensInv ())[l]! (hypGen l)⁻¹ :=
  (rep_hypGens hl).inv_of_invOK ((hypOrbitFacts 0).inv l hl)

theorem flagSet_imgFlags_gen {l : ℕ} (hl : l < 2) (F : Flags) :
    flagSet (imgFlags (hypGensInv ())[l]! F) = ⇑(hypGen l) '' flagSet F :=
  flagSet_imgFlags (rep_hypGensInv hl) F

theorem hypList_length (i : Fin 3) : (hypList i).length = 1408 := by
  rw [hypList, List.length_map, Array.length_toList, (hypOrbitFacts i).size]

theorem mem_hypList {i : Fin 3} {O : Set (Fin 693)} :
    O ∈ hypList i ↔ ∃ k < 1408, O = hypSet i k := by
  rw [hypList, List.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨k, hk, hkF⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hF)
    refine ⟨k, by rw [← (hypOrbitFacts i).size]; exact hk, ?_⟩
    rw [hypSet, getElem!_pos _ k hk, hkF]
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < (hypEnum (i.val + 1)).1.size := by rw [(hypOrbitFacts i).size]; exact hk
    refine ⟨_, Array.mem_toList_iff.2 (Array.getElem_mem hk'), ?_⟩
    rw [hypSet, getElem!_pos _ k hk']

theorem hypSet_zero (i : Fin 3) : hypSet i 0 = hypRoot i := by
  rw [hypSet, (hypOrbitFacts i).root, flagSet_rootFlags]

theorem hypSet_mem_hypOrbit
    (i : Fin 3) : ∀ k < 1408, hypSet i k ∈ hypOrbit i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hypSet_zero]
      exact hypRoot_mem_hypOrbit i
    · obtain ⟨hpar, hlab, heq⟩ := (hypOrbitFacts i).tree k hk0 hk
      rw [hypSet, heq, flagSet_imgFlags_gen hlab]
      exact image_mem_hypOrbit (hypGen_mem _) (ih _ hpar (by omega))

theorem hypGen_image_mem (i : Fin 3) {l : ℕ} (hl : l < 2) {O : Set (Fin 693)}
    (hO : O ∈ hypList i) : ⇑(hypGen l) '' O ∈ hypList i := by
  obtain ⟨k, hk, rfl⟩ := mem_hypList.1 hO
  obtain ⟨k', hk', hkk'⟩ := (hypOrbitFacts i).closed k hk l hl
  rw [mem_hypList]
  refine ⟨k', hk', ?_⟩
  unfold hypSet
  rw [hkk', flagSet_imgFlags_gen hl]

theorem hypList_image_mem
    (i : Fin 3) {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46)
    {O : Set (Fin 693)} (hO : O ∈ hypList i) : ⇑g '' O ∈ hypList i := by
  let Inv : Equiv.Perm (Fin 693) → Prop := fun g => ∀ O ∈ hypList i, ⇑g '' O ∈ hypList i
  have hx : Inv t46x := fun O hO => by
    have := hypGen_image_mem i (l := 0) (by norm_num) hO
    unfold hypGen at this
    simpa using this
  have hy : Inv t46y := fun O hO => by
    have := hypGen_image_mem i (l := 1) (by norm_num) hO
    unfold hypGen at this
    simpa using this
  have hmul : ∀ g h, Inv g → Inv h → Inv (g * h) := fun g h hg hh O hO => by
    rw [image_mul]
    exact hg _ (hh O hO)
  have key : ∀ g ∈ Subgroup.closure ({t46x, t46y} : Set (Equiv.Perm (Fin 693))),
      Inv g ∧ Inv g⁻¹ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx' =>
      rcases hx' with rfl | rfl
      · exact ⟨hx, by rw [t46x_inv]; exact hx⟩
      · exact ⟨hy, by rw [t46y_inv]; exact hmul _ _ hy hy⟩
    | one => exact ⟨fun O hO => by simpa using hO, fun O hO => by simpa using hO⟩
    | mul x y _ _ hx' hy' =>
      exact ⟨hmul _ _ hx'.1 hy'.1, by rw [mul_inv_rev]; exact hmul _ _ hy'.2 hx'.2⟩
    | inv x _ hx' => exact ⟨hx'.2, by rw [inv_inv]; exact hx'.1⟩
  exact (key g (T46_le_closure hg)).1 O hO

theorem mem_hypOrbit_iff
    {i : Fin 3} {O : Set (Fin 693)} : O ∈ hypOrbit i ↔ O ∈ hypList i := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← hypSet_zero]
    exact hypList_image_mem i hg (mem_hypList.2 ⟨0, by norm_num, rfl⟩)
  · intro hO
    obtain ⟨k, hk, rfl⟩ := mem_hypList.1 hO
    exact hypSet_mem_hypOrbit i k hk

theorem isClosedHyperoval_of_rootOK
    {R : Flags} (h : rootOK PT (lineTab (perpTab ())) R = true) :
    IsClosedHyperoval (flagSet R) := by
  unfold rootOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hl⟩, hc⟩ := h
  refine ⟨fun L hL => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, hab, hp, rfl⟩ := hL
    wlog hlt : a < b generalizing a b
    · rw [lineThru_comm]
      exact this b a hab.symm (perp_comm.1 hp) (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
    have h1 := (allIn_eq_true.1 ((allIn_eq_true.1 hl) a.val (Nat.zero_le _) a.2)) b.val
      (Nat.zero_le _) b.2
    have hab' : (decide (a.val < b.val) && (PT[a.val]!)[b.val]!) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hlt, (perpTab_spec a b).2 hp⟩
    rw [hab', Bool.not_true, Bool.false_or, lineTab_get hp, Bool.or_eq_true, beq_iff_eq,
      beq_iff_eq] at h1
    have hset : lineThru a b ∩ flagSet R =
        {z : Fin 693 | z.val ∈ (lineC a.val b.val).toList.filter (R[·]!)} := by
      ext z
      rw [Set.mem_inter_iff, lineThru_eq_setOf_lineC hab hp, Set.mem_ofPred_eq, mem_flagSet,
        Set.mem_ofPred_eq, List.mem_filter]
    obtain ⟨-, hlt693, -⟩ := lineC_facts hlt hp
    rw [hset, ncard_setOf_mem_list ((lineC_nodup hlt hp).filter _)
      (fun i hi => hlt693 i (Array.mem_toList_iff.1 (List.mem_filter.1 hi).1))]
    exact h1
  · have hxm : x.val ∈ members R := mem_members.2 ⟨x.2, hx⟩
    have hq := (List.all_eq_true.1 hc) x.val hxm
    ext q
    rw [Set.mem_image_equiv, mem_flagSet, mem_flagSet, tvP_symm]
    have := (allIn_eq_true.1 hq) q.val (Nat.zero_le _) q.2
    rw [beq_iff_eq, rep_tvP x q.val q.2, idx_of_lt _ q.2] at this
    have e : ((tvP x) • (⟨q.val, q.2⟩ : Fin 693)).val = (tvP x q).val := rfl
    rw [e] at this
    rw [this]

theorem isClosedHyperoval_hypRoot
    (i : Fin 3) : IsClosedHyperoval (hypRoot i) := by
  rw [← flagSet_rootFlags]
  fin_cases i
  · exact isClosedHyperoval_of_rootOK hypFacts.root₁
  · exact isClosedHyperoval_of_rootOK hypFacts.root₂
  · exact isClosedHyperoval_of_rootOK hypFacts.root₃

theorem isClosedHyperoval_of_mem_hypOrbit
    {i : Fin 3} {O : Set (Fin 693)} (hO : O ∈ hypOrbit i) :
    IsClosedHyperoval O := by
  obtain ⟨g, hg, rfl⟩ := hO
  exact (isClosedHyperoval_hypRoot i).image_of_mem hg

theorem ncard_hypRoot (i : Fin 3) : (hypRoot i).ncard = 126 := by
  rw [← hypSet_zero, hypSet, ncard_flagSet, (hypOrbitFacts i).card 0 (by norm_num)]

theorem ncard_of_mem_hypOrbit {i : Fin 3} {O : Set (Fin 693)} (hO : O ∈ hypOrbit i) :
    O.ncard = 126 := by
  obtain ⟨g, hg, rfl⟩ := hO
  rw [Set.ncard_image_of_injective _ g.injective, ncard_hypRoot]

theorem hypEnum_size_one : (hypEnum 1).1.size = 1408 := (hypOrbitFacts 0).size
theorem hypEnum_size_two : (hypEnum 2).1.size = 1408 := (hypOrbitFacts 1).size
theorem hypEnum_size_three : (hypEnum 3).1.size = 1408 := (hypOrbitFacts 2).size

theorem HU_size : (HU).size = 4224 := by
  rw [Array.size_append, Array.size_append, hypEnum_size_one, hypEnum_size_two,
    hypEnum_size_three]

theorem HU_get {i : Fin 3} {k : ℕ} (hk : k < 1408) :
    (HU)[1408 * i.val + k]! = (hypEnum (i.val + 1)).1[k]! := by
  have hsz := HU_size
  have h12 : (Prod.fst (hypEnum 1) ++ Prod.fst (hypEnum 2)).size = 2816 := by
    rw [Array.size_append, hypEnum_size_one, hypEnum_size_two]
  fin_cases i
  · show (HU)[1408 * 0 + k]! = (hypEnum 1).1[k]!
    rw [getElem!_pos _ _ (by omega), Array.getElem_append_left (by omega),
      Array.getElem_append_left (by rw [hypEnum_size_one]; omega),
      getElem!_pos _ _ (by rw [hypEnum_size_one]; omega)]
    simp
  · show (HU)[1408 * 1 + k]! = (hypEnum 2).1[k]!
    rw [getElem!_pos _ _ (by omega), Array.getElem_append_left (by omega),
      Array.getElem_append_right (by rw [hypEnum_size_one]; omega),
      getElem!_pos _ _ (by rw [hypEnum_size_two]; omega)]
    simp [hypEnum_size_one]
  · show (HU)[1408 * 2 + k]! = (hypEnum 3).1[k]!
    rw [getElem!_pos _ _ (by omega), Array.getElem_append_right (by omega),
      getElem!_pos _ _ (by rw [hypEnum_size_three]; omega)]
    simp [h12]

theorem HU_get_of_lt {n : ℕ} (hn : n < 4224) :
    ∃ (i : Fin 3) (k : ℕ), k < 1408 ∧ n = 1408 * i.val + k ∧
      (HU)[n]! = (hypEnum (i.val + 1)).1[k]! := by
  by_cases h1 : n < 1408
  · have := HU_get (i := 0) h1
    simp only [Fin.val_zero, mul_zero, zero_add] at this
    exact ⟨0, n, h1, by simp, this⟩
  · by_cases h2 : n < 2816
    · have := HU_get (i := 1) (k := n - 1408) (by omega)
      rw [show 1408 * (1 : Fin 3).val + (n - 1408) = n by simp; omega] at this
      exact ⟨1, n - 1408, by omega, by simp; omega, this⟩
    · have := HU_get (i := 2) (k := n - 2816) (by omega)
      rw [show 1408 * (2 : Fin 3).val + (n - 2816) = n by simp; omega] at this
      exact ⟨2, n - 2816, by omega, by simp; omega, this⟩

theorem HU_inj {n m : ℕ} (hn : n < 4224) (hm : m < 4224)
    (h : flagSet (HU)[n]! = flagSet (HU)[m]!) : n = m := by
  have hf := hypFacts.fam
  unfold famOK at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have h1 := (allIn_eq_true.1 hf.2) n (Nat.zero_le _) hn
  have h2 := (allIn_eq_true.1 hf.2) m (Nat.zero_le _) hm
  rw [beq_iff_eq] at h1 h2
  rw [← h1, ← h2, members_congr h]

theorem hypSet_eq_iff {i j : Fin 3} {k k' : ℕ} (hk : k < 1408) (hk' : k' < 1408) :
    hypSet i k = hypSet j k' ↔ i = j ∧ k = k' := by
  constructor
  · intro h
    rw [hypSet, hypSet, ← HU_get hk, ← HU_get hk'] at h
    have := HU_inj (by have := i.2; omega) (by have := j.2; omega) h
    have hij : i.val = j.val := by omega
    exact ⟨Fin.ext hij, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem hypList_nodup (i : Fin 3) : (hypList i).Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro a b hab hb
  rw [hypList_length] at hb
  have ha : a < 1408 := by omega
  rw [hypList, List.getElem?_map, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_toList, Array.getElem?_eq_getElem (by rw [(hypOrbitFacts i).size]; exact ha),
    Array.getElem?_eq_getElem (by rw [(hypOrbitFacts i).size]; exact hb)]
  simp only [Option.map_some, ne_eq, Option.some.injEq]
  intro h
  have := (hypSet_eq_iff ha hb (i := i) (j := i)).1 (by
    rw [hypSet, hypSet, getElem!_pos _ a (by rw [(hypOrbitFacts i).size]; exact ha),
      getElem!_pos _ b (by rw [(hypOrbitFacts i).size]; exact hb)]
    exact h)
  omega

theorem hypOrbit_eq_image
    (i : Fin 3) : hypOrbit i = hypSet i '' Set.Iio 1408 := by
  ext O
  rw [mem_hypOrbit_iff, mem_hypList]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Set.mem_Iio.2 hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Set.mem_Iio.1 hk, rfl⟩

theorem ncard_hypOrbit
    (i : Fin 3) : (hypOrbit i).ncard = 1408 := by
  rw [hypOrbit_eq_image, Set.InjOn.ncard_image, Set.ncard_Iio_nat]
  intro k hk k' hk' h
  exact ((hypSet_eq_iff (Set.mem_Iio.1 hk) (Set.mem_Iio.1 hk')).1 h).2

theorem hypOrbit_disjoint
    {i j : Fin 3} (h : i ≠ j) : Disjoint (hypOrbit i) (hypOrbit j) := by
  rw [Set.disjoint_left]
  intro O hi hj
  rw [hypOrbit_eq_image] at hi hj
  obtain ⟨k, hk, rfl⟩ := hi
  obtain ⟨k', hk', hkk'⟩ := hj
  exact h ((hypSet_eq_iff (Set.mem_Iio.1 hk) (Set.mem_Iio.1 hk')).1 hkk'.symm).1

theorem search_facts {j : ℕ} (hj : j < 1024) :
    ∃ R, hsearch CT 40 ((CT).lam[j]!) (startX j) = some R ∧ R.length ≤ 1 ∧
      ∀ F ∈ R, ∃ n < 4224, (HU)[n]! = F := by
  have h := hypFacts.search
  unfold searchOK at h
  have h1 := (allIn_eq_true.1 h) j (Nat.zero_le _) hj
  simp only at h1
  unfold startX
  split at h1
  · cases h1
  · rename_i R hR
    rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
    refine ⟨R, hR, h1.1, fun F hF => ?_⟩
    have := h1.2 F hF
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨_, this.1, this.2⟩

theorem cons_start
    {A : Set (Fin 693)} {j : ℕ}
    (hj : ∀ z : Fin 693, perp 0 z → (z ∈ A ↔ (LAM[j]!)[z.val]! = true)) (hj' : j < 1024) :
    Cons ((CT).lam[j]!) (startX j) A := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [hypCtx_lam] at hp
    have h0p := (lam_facts hj').2.1 p.val p.2 hp
    exact (hj p ((perpTab_spec 0 p).1 h0p)).2 hp
  · unfold startX at hp
    rw [getElem!_pos _ p.val (by simp), Array.getElem_ofFn] at hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    rw [hypCtx_P, hypCtx_lam] at hp
    intro hpA
    have := (hj p ((perpTab_spec 0 p).1 hp.1)).1 hpA
    rw [hp.2] at this
    exact Bool.noConfusion this

theorem gx_inv_self (x : Fin 693) : (gx x)⁻¹ x = 0 := by
  calc (gx x)⁻¹ x = (gx x)⁻¹ (gx x 0) := by rw [gx_zero]
    _ = 0 := perm_inv_apply_self _ _

theorem IsClosedHyperoval.exists_mem_hypOrbit
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (hne : O.Nonempty) : ∃ i, O ∈ hypOrbit i := by
  obtain ⟨x, hx⟩ := hne
  have hg := gx_mem x
  have hA : IsClosedHyperoval (⇑(gx x)⁻¹ '' O) := hO.image_of_mem (T46.inv_mem hg)
  have h0 : (0 : Fin 693) ∈ ⇑(gx x)⁻¹ '' O := ⟨x, hx, gx_inv_self x⟩
  obtain ⟨j, hj, hjz⟩ := exists_lam_of_zero_mem hA h0
  obtain ⟨R, hR, -, hRH⟩ := search_facts hj
  obtain ⟨F, hF, hAF⟩ := hsearch_sound ctxOK_hypCtx 40 _ _ R hR _
    (localOK_of_isClosedHyperoval hA) (cons_start hjz hj)
  obtain ⟨n, hn, hnF⟩ := hRH F hF
  obtain ⟨i, k, hk, -, hHU⟩ := HU_get_of_lt hn
  refine ⟨i, ?_⟩
  have hAi : ⇑(gx x)⁻¹ '' O ∈ hypOrbit i := by
    rw [hAF, ← hnF, hHU]
    exact hypSet_mem_hypOrbit i k hk
  have := image_mem_hypOrbit hg hAi
  rwa [image_inv_image] at this

theorem IsClosedHyperoval.ncard_eq
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (hne : O.Nonempty) : O.ncard = 126 := by
  obtain ⟨i, hi⟩ := hO.exists_mem_hypOrbit hne
  exact ncard_of_mem_hypOrbit hi

theorem IsClosedHyperoval.eq_of_inter_perp
    {O O' : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (hO' : IsClosedHyperoval O') {p : Fin 693} (hp : p ∈ O) (_hp' : p ∈ O')
    (h : ∀ q, perp p q → (q ∈ O ↔ q ∈ O')) : O = O' := by
  have hg := gx_mem p
  have ha := isPolarAut_of_mem hg
  have hA : IsClosedHyperoval (⇑(gx p)⁻¹ '' O) := hO.image_of_mem (T46.inv_mem hg)
  have hA' : IsClosedHyperoval (⇑(gx p)⁻¹ '' O') := hO'.image_of_mem (T46.inv_mem hg)
  have h0 : (0 : Fin 693) ∈ ⇑(gx p)⁻¹ '' O := ⟨p, hp, gx_inv_self p⟩
  obtain ⟨j, hj, hjz⟩ := exists_lam_of_zero_mem hA h0
  have hjz' : ∀ z : Fin 693, perp 0 z → (z ∈ ⇑(gx p)⁻¹ '' O' ↔ (LAM[j]!)[z.val]! = true) := by
    intro z hz
    rw [← hjz z hz, Set.mem_image_equiv, Set.mem_image_equiv]
    show (gx p)⁻¹.symm z ∈ O' ↔ (gx p)⁻¹.symm z ∈ O
    have hpz : perp p ((gx p)⁻¹.symm z) := by
      rw [Equiv.Perm.inv_def, Equiv.symm_symm]
      have := (ha.map_perp 0 z).2 hz
      rwa [gx_zero] at this
    exact (h _ hpz).symm
  obtain ⟨R, hR, hlen, -⟩ := search_facts hj
  obtain ⟨F, hF, hAF⟩ := hsearch_sound ctxOK_hypCtx 40 _ _ R hR _
    (localOK_of_isClosedHyperoval hA) (cons_start hjz hj)
  obtain ⟨F', hF', hAF'⟩ := hsearch_sound ctxOK_hypCtx 40 _ _ R hR _
    (localOK_of_isClosedHyperoval hA') (cons_start hjz' hj)
  have hFF' : F = F' := eq_of_length_le_one hlen hF hF'
  have := congrArg (fun S => ⇑(gx p) '' S) (hAF.trans (hFF' ▸ hAF'.symm))
  simp only [image_inv_image] at this
  exact this

end CFSG.Fischer
