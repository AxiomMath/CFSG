
module

public import CFSG.Fischer.Polar.LinesBase

public import CFSG.Fischer.Polar.Span
public import CFSG.Fischer.Polar.Cert
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs

local notation "PT" => perpTab ()
local notation "PL" => perpLists (perpTab ())
local notation "LT" => lineTab (perpTab ())
local notation "LL" => lineList (perpTab ()) (lineTab (perpTab ()))
local notation "LI" => lineIdx (lineList (perpTab ()) (lineTab (perpTab ())))

theorem polarLinesFacts : PolarLinesFacts := by
  have h := polarLines_certificate
  unfold polarLinesCertificate polarLinesChecks at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ncard_setOf_perp
    (p : Fin 693) : {q | perp p q}.ncard = 181 := by
  have h := (allIn_eq_true.1 polarLinesFacts.size) p.val (Nat.zero_le _) p.2
  rw [beq_iff_eq] at h
  have : {q | perp p q} = {q : Fin 693 | q.val ∈ PL[p.val]!.toList} := by
    ext q
    simp only [Set.mem_ofPred_eq, Array.mem_toList_iff, mem_perpLists_fin]
  rw [this, ncard_setOf_mem_list (nodup_perpLists p)
    (fun i hi => lt_of_mem_perpLists (Array.mem_toList_iff.1 hi)), Array.length_toList, h]

theorem ncard_perp_ne
    (p : Fin 693) : {q | perp p q ∧ q ≠ p}.ncard = 180 := by
  have h1 : {q | perp p q ∧ q ≠ p} = {q | perp p q} \ {p} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  rw [h1, Set.ncard_sdiff_singleton_of_mem (show p ∈ {q | perp p q} from perp_self p),
    ncard_setOf_perp]

theorem lineC_facts
    {x y : Fin 693} (hlt : x < y) (h : perp x y) :
    distinct5 (lineC x.val y.val) = true ∧ (∀ i ∈ lineC x.val y.val, i < 693) ∧
      ∀ z : Fin 693, z.val ∈ lineC x.val y.val ↔ ∀ w, perp x w → perp w y → perp z w := by
  have h1 := (allIn_eq_true.1 polarLinesFacts.lines) x.val (Nat.zero_le _) x.2
  have h2 := (allIn_eq_true.1 h1) y.val (Nat.zero_le _) y.2
  have hxy : (decide (x.val < y.val) && (PT[x.val]!)[y.val]!) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlt, (perpTab_spec x y).2 h⟩
  rw [hxy] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
  obtain ⟨⟨hall, hd⟩, hz⟩ := h2
  rw [lineTab_get h] at hall hd hz
  refine ⟨hd, fun i hi => of_decide_eq_true (Array.all_eq_true'.1 hall i hi), fun z => ?_⟩
  have hz' := (allIn_eq_true.1 hz) z.val (Nat.zero_le _) z.2
  rw [beq_iff_eq, Bool.eq_iff_iff, Array.contains_iff_mem, Array.all_eq_true'] at hz'
  rw [hz']
  constructor
  · intro H w hxw hwy
    have hw : w.val ∈ (PL[x.val]!).filter fun w => (PT[w]!)[y.val]! := by
      rw [Array.mem_filter]
      exact ⟨mem_perpLists_fin.2 hxw, (perpTab_spec w y).2 hwy⟩
    exact (perpTab_spec z w).1 (H w.val hw)
  · intro H w hw
    rw [Array.mem_filter] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hwlt := lt_of_mem_perpLists hw1
    exact (perpTab_spec' hwlt).2 (H ⟨w, hwlt⟩ (mem_perpLists_fin.1 hw1)
      ((perpTab_spec ⟨w, hwlt⟩ y).1 hw2))

theorem lineThru_eq_perp_of_lt
    {x y : Fin 693} (hlt : x < y) (h : perp x y) :
    lineThru x y = {z | ∀ w, perp w x → perp w y → perp w z} := by
  ext z
  rw [mem_lineThru_iff (ne_of_lt hlt) h, (lineC_facts hlt h).2.2 z]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro H w hwx hwy
    exact perp_comm.1 (H w (perp_comm.1 hwx) hwy)
  · intro H w hxw hwy
    exact perp_comm.1 (H w (perp_comm.1 hxw) hwy)

theorem lineThru_eq_perp
    {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) :
    lineThru x y = {z | ∀ w, perp w x → perp w y → perp w z} := by
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact lineThru_eq_perp_of_lt hlt h
  · rw [lineThru_comm, lineThru_eq_perp_of_lt hlt (perp_comm.1 h)]
    ext z
    exact ⟨fun H w h1 h2 => H w h2 h1, fun H w h1 h2 => H w h2 h1⟩

theorem lineC_nodup
    {x y : Fin 693} (hlt : x < y) (h : perp x y) :
    (lineC x.val y.val).toList.Nodup := by
  obtain ⟨hd, -, -⟩ := lineC_facts hlt h
  unfold distinct5 at hd
  rw [Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨hs, hd⟩ := hd
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro a b hab hb
  rw [Array.length_toList, hs] at hb
  have := (allIn_eq_true.1 ((allIn_eq_true.1 hd) a (Nat.zero_le _) (by omega)))
    b (Nat.zero_le _) hb
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at this
  rcases this with h1 | h1
  · omega
  · rw [Array.getElem?_toList, Array.getElem?_toList,
      Array.getElem?_eq_getElem (by rw [hs]; omega), Array.getElem?_eq_getElem (by rw [hs]; omega)]
    rw [getElem!_pos _ a (by rw [hs]; omega), getElem!_pos _ b (by rw [hs]; omega)] at h1
    exact fun h2 => h1 (Option.some_injective _ h2)

theorem ncard_lineThru
    {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) :
    (lineThru x y).ncard = 5 := by
  wlog hlt : x < y generalizing x y
  · rw [lineThru_comm]
    exact this hxy.symm (perp_comm.1 h) (lt_of_le_of_ne (not_lt.1 hlt) hxy.symm)
  obtain ⟨-, hlt693, -⟩ := lineC_facts hlt h
  rw [lineThru_eq_setOf_lineC hxy h, ncard_setOf_mem_list (lineC_nodup hlt h)
    (fun i hi => hlt693 i (Array.mem_toList_iff.1 hi)), Array.length_toList, lineC_size]

theorem lineList_facts {i : ℕ} (hi : i < 6237) :
    (LL[i]!).size = 5 ∧ (∀ k ∈ LL[i]!, k < 693) ∧ (LL[i]!)[0]! ≠ (LL[i]!)[1]! ∧
      (PT[(LL[i]!)[0]!]!)[(LL[i]!)[1]!]! = true ∧
      (∀ k ∈ LL[i]!, k ∈ LT[(LL[i]!)[0]! * 693 + (LL[i]!)[1]!]!) ∧
      (∀ k ∈ LT[(LL[i]!)[0]! * 693 + (LL[i]!)[1]!]!, k ∈ LL[i]!) ∧
      ∀ a < 5, ∀ b < 5, a ≠ b → LI[(LL[i]!)[a]! * 693 + (LL[i]!)[b]!]! = i := by
  have h := polarLinesFacts.list
  unfold lineListOK at h
  simp only [Bool.and_eq_true] at h
  have h1 := (allIn_eq_true.1 h.1.2) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Array.all_eq_true',
    Array.contains_iff_mem, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨hs, hlt⟩, h01⟩, hp⟩, hm1, hm2⟩, hab⟩ := h1
  refine ⟨hs, hlt, h01, hp, hm1, hm2, fun a ha b hb hne => ?_⟩
  have := (allIn_eq_true.1 ((allIn_eq_true.1 hab) a (Nat.zero_le _) ha)) b (Nat.zero_le _) hb
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h2 | h2
  · exact absurd h2 hne
  · exact h2

theorem lineList_size : (LL).size = 6237 := by
  have h := polarLinesFacts.list
  unfold lineListOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem lineSet_eq
    {i : ℕ} (hi : i < 6237) :
    ∃ x y : Fin 693, x ≠ y ∧ perp x y ∧ lineSet i = lineThru x y := by
  obtain ⟨hs, hlt, h01, hp, hm1, hm2, -⟩ := lineList_facts hi
  have h0 : (LL[i]!)[0]! < 693 :=
    hlt _ (by rw [getElem!_pos _ 0 (by omega)]; exact Array.getElem_mem _)
  have h1 : (LL[i]!)[1]! < 693 :=
    hlt _ (by rw [getElem!_pos _ 1 (by omega)]; exact Array.getElem_mem _)
  set x : Fin 693 := ⟨_, h0⟩
  set y : Fin 693 := ⟨_, h1⟩
  have hxy : x ≠ y := fun h => h01 (congrArg Fin.val h)
  have hperp : perp x y := (perpTab_spec x y).1 hp
  refine ⟨x, y, hxy, hperp, ?_⟩
  ext z
  rw [mem_lineThru_iff hxy hperp]
  have hL : LT[x.val * 693 + y.val]! = lineC x.val y.val := lineTab_get hperp
  simp only [lineSet, Set.mem_ofPred_eq]
  rw [← hL]
  exact ⟨hm1 _, hm2 _⟩

theorem isLine_lineSet
    {i : ℕ} (hi : i < 6237) : IsLine (lineSet i) := by
  obtain ⟨x, y, hxy, h, he⟩ := lineSet_eq hi
  rw [he]
  exact isLine_lineThru hxy h

theorem lineThru_eq_lineSet
    {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) :
    LI[x.val * 693 + y.val]! < 6237 ∧ lineThru x y = lineSet (LI[x.val * 693 + y.val]!) := by
  have hl := polarLinesFacts.list
  unfold lineListOK at hl
  simp only [Bool.and_eq_true] at hl
  have h1 := (allIn_eq_true.1 ((allIn_eq_true.1 hl.2) x.val (Nat.zero_le _) x.2)) y.val
    (Nat.zero_le _) y.2
  have hne : (x.val == y.val) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h' => hxy (Fin.ext h')
  rw [hne, (perpTab_spec x y).2 h] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true', Array.contains_iff_mem] at h1
  obtain ⟨hlt, hm1, hm2⟩ := h1
  refine ⟨hlt, ?_⟩
  ext z
  rw [mem_lineThru_iff hxy h, ← lineTab_get h]
  exact ⟨hm1 _, hm2 _⟩

theorem lineSet_eq_of_mem {i : ℕ} (hi : i < 6237) {a b : Fin 693} (ha : a ∈ lineSet i)
    (hb : b ∈ lineSet i) (hab : a ≠ b) : LI[a.val * 693 + b.val]! = i := by
  obtain ⟨hs, -, -, -, -, -, hidx⟩ := lineList_facts hi
  obtain ⟨α, hα, hαa⟩ := Array.mem_iff_getElem.1 (show a.val ∈ LL[i]! from ha)
  obtain ⟨β, hβ, hβb⟩ := Array.mem_iff_getElem.1 (show b.val ∈ LL[i]! from hb)
  have hne : α ≠ β := by
    rintro rfl
    exact hab (Fin.ext (hαa.symm.trans hβb))
  have := hidx α (by rw [hs] at hα; exact hα) β (by rw [hs] at hβ; exact hβ) hne
  rwa [getElem!_pos _ α hα, getElem!_pos _ β hβ, hαa, hβb] at this

theorem lineSet_injOn :
    Set.InjOn lineSet (Set.Iio 6237) := by
  intro i hi j hj hij
  obtain ⟨x, y, hxy, h, he⟩ := lineSet_eq (Set.mem_Iio.1 hj)
  have hx : x ∈ lineSet j := by rw [he]; exact left_mem_lineThru x y
  have hy : y ∈ lineSet j := by rw [he]; exact right_mem_lineThru x y
  rw [← lineSet_eq_of_mem (Set.mem_Iio.1 hi) (hij ▸ hx) (hij ▸ hy) hxy,
    lineSet_eq_of_mem (Set.mem_Iio.1 hj) hx hy hxy]

theorem IsLine.exists_lineSet
    {L : Set (Fin 693)} (hL : IsLine L) :
    ∃ i < 6237, L = lineSet i := by
  obtain ⟨x, y, hxy, h, rfl⟩ := hL
  obtain ⟨hlt, he⟩ := lineThru_eq_lineSet hxy h
  exact ⟨_, hlt, he⟩

theorem setOf_isLine :
    {L | IsLine L} = lineSet '' Set.Iio 6237 := by
  ext L
  constructor
  · intro hL
    obtain ⟨i, hi, rfl⟩ := IsLine.exists_lineSet hL
    exact ⟨i, Set.mem_Iio.2 hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact isLine_lineSet (Set.mem_Iio.1 hi)

theorem ncard_setOf_isLine :
    {L | IsLine L}.ncard = 6237 := by
  rw [setOf_isLine, lineSet_injOn.ncard_image, Set.ncard_Iio_nat]

theorem IsLine.ncard
    {L : Set (Fin 693)} (hL : IsLine L) : L.ncard = 5 := by
  obtain ⟨x, y, hxy, h, rfl⟩ := hL
  exact ncard_lineThru hxy h

theorem IsLine.perp_of_mem
    {L : Set (Fin 693)} (hL : IsLine L) {a b : Fin 693} (ha : a ∈ L)
    (hb : b ∈ L) : perp a b := by
  obtain ⟨x, y, hxy, h, rfl⟩ := hL
  rw [lineThru_eq_perp hxy h] at ha hb
  have hbx : perp b x := perp_comm.1 (hb x (perp_self x) h)
  have hby : perp b y := perp_comm.1 (hb y (perp_comm.1 h) (perp_self y))
  exact perp_comm.1 (ha b hbx hby)

theorem IsLine.eq_lineThru
    {L : Set (Fin 693)} (hL : IsLine L) {a b : Fin 693} (ha : a ∈ L)
    (hb : b ∈ L) (hab : a ≠ b) : L = lineThru a b := by
  obtain ⟨i, hi, rfl⟩ := IsLine.exists_lineSet hL
  obtain ⟨-, he⟩ := lineThru_eq_lineSet hab (hL.perp_of_mem ha hb)
  rw [he, lineSet_eq_of_mem hi ha hb hab]

theorem existsUnique_line
    {p x : Fin 693} (h : perp p x) (hx : x ≠ p) :
    ∃! L, IsLine L ∧ p ∈ L ∧ x ∈ L :=
  ⟨lineThru p x, ⟨isLine_lineThru hx.symm h, left_mem_lineThru p x, right_mem_lineThru p x⟩,
    fun _ ⟨hL, hp, hx'⟩ => hL.eq_lineThru hp hx' hx.symm⟩

theorem ncard_lines_through
    (p : Fin 693) : {L | IsLine L ∧ p ∈ L}.ncard = 45 := by
  have h := polarLinesFacts.list
  unfold lineListOK at h
  simp only [Bool.and_eq_true] at h
  have hc := (allIn_eq_true.1 h.1.1.2) p.val (Nat.zero_le _) p.2
  rw [beq_iff_eq] at hc
  have hset : {L | IsLine L ∧ p ∈ L} =
      lineSet '' {i : ℕ | i ∈ (List.range 6237).filter fun i => LL[i]!.contains p.val} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_filter, List.mem_range,
      Array.contains_iff_mem]
    constructor
    · rintro ⟨hL, hp⟩
      obtain ⟨i, hi, rfl⟩ := IsLine.exists_lineSet hL
      exact ⟨i, ⟨hi, hp⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
      exact ⟨isLine_lineSet hi, hp⟩
  rw [hset, Set.InjOn.ncard_image (lineSet_injOn.mono fun i hi => ?_)]
  · rw [← hc]
    exact ncard_setOf_mem_list_nat ((List.nodup_range).filter _)
  · simp only [Set.mem_ofPred_eq, List.mem_filter, List.mem_range] at hi
    exact Set.mem_Iio.2 hi.1

theorem image_lineThru
    {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) {x y : Fin 693}
    (hxy : x ≠ y) (h : perp x y) : ⇑g '' lineThru x y = lineThru (g x) (g y) := by
  have hxy' : g x ≠ g y := g.injective.ne hxy
  have h' : perp (g x) (g y) := (hg.map_perp x y).2 h
  rw [lineThru_eq_perp hxy h, lineThru_eq_perp hxy' h']
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z0, hz0, rfl⟩ w hwx hwy
    have := hz0 (g⁻¹ w) (by rw [← hg.map_perp, perm_apply_inv_self]; exact hwx)
      (by rw [← hg.map_perp, perm_apply_inv_self]; exact hwy)
    rwa [← hg.map_perp, perm_apply_inv_self] at this
  · intro hz
    refine ⟨g⁻¹ z, fun w hwx hwy => ?_, perm_apply_inv_self g z⟩
    have := hz (g w) ((hg.map_perp w x).2 hwx) ((hg.map_perp w y).2 hwy)
    rwa [← perm_apply_inv_self g z, hg.map_perp] at this

theorem IsLine.image
    {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) {L : Set (Fin 693)}
    (hL : IsLine L) : IsLine (⇑g '' L) := by
  obtain ⟨x, y, hxy, h, rfl⟩ := hL
  rw [image_lineThru hg hxy h]
  exact isLine_lineThru (g.injective.ne hxy) ((hg.map_perp x y).2 h)

theorem IsLine.image_of_mem
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) {L : Set (Fin 693)}
    (hL : IsLine L) : IsLine (⇑g '' L) :=
  hL.image (isPolarAut_of_mem hg)

theorem IsClosedHyperoval.image
    {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g)
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O) : IsClosedHyperoval (⇑g '' O) := by
  refine ⟨fun L hL => ?_, fun x hx => ?_⟩
  · have hL' : IsLine (⇑g⁻¹ '' L) := hL.image hg.inv
    have heq : L ∩ ⇑g '' O = ⇑g '' (⇑g⁻¹ '' L ∩ O) := by
      rw [Set.image_inter g.injective, Set.image_image]
      simp only [perm_apply_inv_self, Set.image_id']
    rw [heq, Set.ncard_image_of_injective _ g.injective]
    exact hO.inter _ hL'
  · obtain ⟨x0, hx0, rfl⟩ := hx
    rw [Set.image_image]
    have : (fun y => tvP (g x0) (g y)) = (fun y => g (tvP x0 y)) :=
      funext fun y => (hg.map_tvP x0 y).symm
    rw [this, ← Set.image_image (⇑g) (tvP x0), hO.closed x0 hx0]

theorem IsClosedHyperoval.image_of_mem
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46)
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O) : IsClosedHyperoval (⇑g '' O) :=
  hO.image (isPolarAut_of_mem hg)

theorem twins_iff_line_zero
    {x y : Fin 693} (hx : perp 0 x) (hy : perp 0 y) (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) (hxy : x ≠ y) :
    (∀ w, perp 0 w → w ≠ 0 → (perp w x ↔ perp w y)) ↔ y ∈ lineThru 0 x := by
  have h := polarLinesFacts.twins
  unfold twinsOK at h
  rw [Array.all_eq_true'] at h
  have hx' := h x.val (by rw [← perpLists_zero_eq]; exact mem_perpLists_fin.2 hx)
  have hx0' : (x.val == 0) = false := by
    rw [beq_eq_false_iff_ne]; exact fun h' => hx0 (Fin.ext h')
  rw [hx0', Bool.false_or, Array.all_eq_true'] at hx'
  have hy' := hx' y.val (by rw [← perpLists_zero_eq]; exact mem_perpLists_fin.2 hy)
  have hy0' : (y.val == 0) = false := by
    rw [beq_eq_false_iff_ne]; exact fun h' => hy0 (Fin.ext h')
  have hyx' : (y.val == x.val) = false := by
    rw [beq_eq_false_iff_ne]; exact fun h' => hxy (Fin.ext h').symm
  rw [hy0', hyx', Bool.false_or, Bool.false_or, lineTab_zero hx, beq_iff_eq, Bool.eq_iff_iff,
    Array.contains_iff_mem, Array.all_eq_true'] at hy'
  rw [mem_lineThru_iff (Ne.symm hx0) hx, Fin.val_zero, ← hy']
  constructor
  · intro H w hw
    rw [← perpLists_zero_eq] at hw
    have hwlt := lt_of_mem_perpLists hw
    have hw' := mem_perpLists.1 hw
    by_cases hw0 : w = 0
    · rw [hw0]; simp
    · have := H ⟨w, hwlt⟩ hw'.2 (fun h' => hw0 (congrArg Fin.val h'))
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
      right
      rw [Bool.eq_iff_iff, perpTab_spec' hwlt, perpTab_spec' hwlt, perp_comm (p := x),
        perp_comm (p := y)]
      exact this
  · intro H w hw hw0
    have := H w.val (by rw [← perpLists_zero_eq]; exact mem_perpLists_fin.2 hw)
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at this
    rcases this with h1 | h1
    · exact absurd (Fin.ext h1) hw0
    · rw [Bool.eq_iff_iff, perpTab_spec x w, perpTab_spec y w] at h1
      rw [perp_comm, perp_comm (p := w)]
      exact h1

theorem twins_iff_line
    {p x y : Fin 693} (hpx : perp p x) (hpy : perp p y) (hxp : x ≠ p)
    (hyp : y ≠ p) (hxy : x ≠ y) :
    (∀ w, perp p w → w ≠ p → (perp w x ↔ perp w y)) ↔ ∃ L, IsLine L ∧ p ∈ L ∧ x ∈ L ∧ y ∈ L := by
  obtain ⟨g, hg, rfl⟩ := exists_smul_zero p
  have ha := isPolarAut_of_mem hg
  have hx' : perp 0 (g⁻¹ x) := by
    have := (ha.inv.map_perp (g 0) x).2 hpx
    rwa [perm_inv_apply_self] at this
  have hy' : perp 0 (g⁻¹ y) := by
    have := (ha.inv.map_perp (g 0) y).2 hpy
    rwa [perm_inv_apply_self] at this
  have hx0 : g⁻¹ x ≠ 0 := fun h => hxp (by rw [← h, perm_apply_inv_self])
  have hy0 : g⁻¹ y ≠ 0 := fun h => hyp (by rw [← h, perm_apply_inv_self])
  have hxy' : g⁻¹ x ≠ g⁻¹ y := g⁻¹.injective.ne hxy
  have e1 : (∀ w, perp (g 0) w → w ≠ g 0 → (perp w x ↔ perp w y)) ↔
      ∀ w, perp 0 w → w ≠ 0 → (perp w (g⁻¹ x) ↔ perp w (g⁻¹ y)) := by
    constructor
    · intro H w hw hw0
      have := H (g w) ((ha.map_perp 0 w).2 hw) (g.injective.ne hw0)
      rwa [← ha.inv.map_perp (g w) x, ← ha.inv.map_perp (g w) y, perm_inv_apply_self] at this
    · intro H w hw hw0
      have h1 : perp 0 (g⁻¹ w) := by
        have := (ha.inv.map_perp (g 0) w).2 hw
        rwa [perm_inv_apply_self] at this
      have := H (g⁻¹ w) h1 (fun h => hw0 (by rw [← h, perm_apply_inv_self]))
      rwa [ha.inv.map_perp, ha.inv.map_perp] at this
  rw [e1, twins_iff_line_zero hx' hy' hx0 hy0 hxy']
  constructor
  · intro H
    refine ⟨⇑g '' lineThru 0 (g⁻¹ x), (isLine_lineThru hx0.symm hx').image ha,
      ⟨0, left_mem_lineThru _ _, rfl⟩, ⟨g⁻¹ x, right_mem_lineThru _ _, perm_apply_inv_self g x⟩,
      ⟨g⁻¹ y, H, perm_apply_inv_self g y⟩⟩
  · rintro ⟨L, hL, hp, hx, hy⟩
    have hL' : IsLine (⇑g⁻¹ '' L) := hL.image ha.inv
    have h0 : (0 : Fin 693) ∈ ⇑g⁻¹ '' L := ⟨g 0, hp, perm_inv_apply_self g 0⟩
    rw [← hL'.eq_lineThru h0 ⟨x, hx, rfl⟩ hx0.symm]
    exact ⟨y, hy, rfl⟩

theorem twins_of_line
    {p x y : Fin 693} (hpx : perp p x) (hpy : perp p y) (hxp : x ≠ p)
    (hyp : y ≠ p) (hxy : x ≠ y) (h : ∃ L, IsLine L ∧ p ∈ L ∧ x ∈ L ∧ y ∈ L) :
    ∀ w, perp p w → w ≠ p → (perp w x ↔ perp w y) :=
  (twins_iff_line hpx hpy hxp hyp hxy).2 h

end CFSG.Fischer
