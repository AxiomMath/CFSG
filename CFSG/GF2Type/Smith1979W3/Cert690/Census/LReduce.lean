module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.A2
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Induction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.RankThree.OrthogonalInvolutions

variable {minus : Bool}

@[expose] noncomputable def stabO (minus : Bool) : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) where
  carrier := {g | g ∈ O₀ minus ∧ g (Code.vec (b0Of minus)) = Code.vec (b0Of minus)}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haO, ha⟩ ⟨hbO, hb⟩
    refine ⟨mul_mem haO hbO, ?_⟩
    rw [LinearEquiv.mul_apply, hb, ha]
  inv_mem' := by
    rintro a ⟨haO, ha⟩
    refine ⟨inv_mem haO, ?_⟩
    calc a⁻¹ (Code.vec (b0Of minus)) = a⁻¹ (a (Code.vec (b0Of minus))) := by rw [ha]
      _ = Code.vec (b0Of minus) := by simp

theorem mem_stabO_iff {g : V₀ ≃ₗ[ZMod 2] V₀} :
    g ∈ stabO minus ↔ g ∈ O₀ minus ∧ g (Code.vec (b0Of minus)) = Code.vec (b0Of minus) :=
  Iff.rfl

@[expose] def a2Set (minus : Bool) : Set (V₀ ≃ₗ[ZMod 2] V₀) :=
  {t | t ∈ stabO minus ∧ IsTypeA (qModel minus) t 2}

theorem Lam_eq_empty_of_ge {j : ℕ} (hj : ¬ j < (CertL minus).Llist.size) :
    Lam minus j = ∅ := by
  ext x
  constructor
  · rintro ⟨i, hiA, -, -⟩
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?,
      dif_neg hj] at hiA
    have hdef : (default : Array ℕ) = #[] := rfl
    rw [hdef] at hiA
    simp at hiA
  · intro h
    exact absurd h (by simp)

theorem exists_elt_mul (hD : GrpFacts minus (CertD minus)) {i j : ℕ}
    (hi : i < (CertD minus).O.size) (hj : j < (CertD minus).O.size) :
    ∃ z, z < (CertD minus).O.size ∧
      (CertD minus).O[z]! = Code.mul ((CertD minus).O[i]!) ((CertD minus).O[j]!) ∧
      hD.elt z = hD.elt i * hD.elt j ∧
      z = (CertD minus).idx.getD
        (Code.mul ((CertD minus).O[i]!) ((CertD minus).O[j]!)) (CertD minus).O.size := by
  have hmem : hD.elt i * hD.elt j ∈ O₀ minus :=
    mul_mem (hD.elt_mem_O₀ hi) (hD.elt_mem_O₀ hj)
  obtain ⟨hlt, hcode, helt⟩ := hD.idx_spec hmem (hD.hasCode_mul hi hj) (Code.mul_lt _ _)
  exact ⟨_, hlt, hcode, helt, rfl⟩

theorem exists_elt_conj (hD : GrpFacts minus (CertD minus)) {a x : ℕ}
    (ha : a < (CertD minus).O.size) (hx : x < (CertD minus).O.size) :
    ∃ z, z < (CertD minus).O.size ∧
      (CertD minus).O[z]! =
        Code.mul (Code.mul ((CertD minus).O[a]!) ((CertD minus).O[x]!))
          ((CertD minus).O[(CertD minus).invI[a]!]!) ∧
      hD.elt z = hD.elt a * hD.elt x * (hD.elt a)⁻¹ ∧
      z = conjIdxOf (CertD minus) a x := by
  have hmem : hD.elt a * hD.elt x * (hD.elt a)⁻¹ ∈ O₀ minus :=
    mul_mem (mul_mem (hD.elt_mem_O₀ ha) (hD.elt_mem_O₀ hx)) (inv_mem (hD.elt_mem_O₀ ha))
  obtain ⟨hlt, hcode, helt⟩ :=
    hD.idx_spec hmem (hD.hasCode_conj ha hx) (Code.mul_lt _ _)
  exact ⟨_, hlt, hcode, helt, rfl⟩

structure L2Wit (minus : Bool) (i : ℕ) where
  j : ℕ
  c : ℕ
  hj : j < (CertL minus).Llist.size
  hc : c < (CertD minus).O.size
  hact : Code.act (CertD minus).O[c]! (b0Of minus) = b0Of minus
  hsize : ((CertL minus).Llist[j]!).size = 2
  hzero : 0 ∈ (CertL minus).Llist[j]!
  hall : ∀ x, x < ((CertL minus).Llist[j]!).size →
    conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = 0 ∨
      conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = i
  hzero' : ∃ x, x < ((CertL minus).Llist[j]!).size ∧
    conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = 0
  hi' : ∃ x, x < ((CertL minus).Llist[j]!).size ∧
    conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = i

noncomputable def l2OK_wit (h : l2OK (CertD minus) minus (b0Of minus) (CertL minus).Llist
    (a2FixOf (CertD minus) minus (b0Of minus)) (CertL minus).l2wit = true)
    {k : ℕ} (hk : k < (a2FixOf (CertD minus) minus (b0Of minus)).size) :
    L2Wit minus ((a2FixOf (CertD minus) minus (b0Of minus))[k]!) := by
  have h' := h
  unfold l2OK at h'
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  obtain ⟨_, hall⟩ := h'
  have hkall := hall k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc, and_assoc] at hkall
  obtain ⟨hj, hc, hact, hsize, hzero, hbase, hany0, hanyi⟩ := hkall
  rw [Array.contains_iff_mem] at hzero
  rw [Array.all_eq_true] at hbase
  rw [Array.any_eq_true] at hany0
  rw [Array.any_eq_true] at hanyi
  refine
    { j := ((CertL minus).l2wit[k]!).1
      c := ((CertL minus).l2wit[k]!).2
      hj := hj
      hc := hc
      hact := hact
      hsize := hsize
      hzero := hzero
      hall := ?_
      hzero' := ?_
      hi' := ?_ }
  · intro x hx
    have hx' := hbase x hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hx'
    rcases hx' with ⟨_, h0 | ht⟩
    · left
      simpa [conjIdxOf, array_getElem!_eq_getElem hx] using h0
    · right
      simpa [conjIdxOf, array_getElem!_eq_getElem hx] using ht
  · obtain ⟨x, hx, hval⟩ := hany0
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hval
    refine ⟨x, hx, ?_⟩
    simpa [conjIdxOf, array_getElem!_eq_getElem hx] using hval.2
  · obtain ⟨x, hx, hval⟩ := hanyi
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hval
    refine ⟨x, hx, ?_⟩
    simpa [conjIdxOf, array_getElem!_eq_getElem hx] using hval.2

theorem lOK_mem_lt {b : ℕ} {L : Array ℕ}
    (h : lOK (CertD minus) minus b L = true) {i : ℕ} (hi : i ∈ L) :
    i < (CertD minus).O.size := by
  have h' := h
  unfold lOK at h'
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hall⟩, _⟩, _⟩ := h'
  obtain ⟨p, hp, hpi⟩ := exists_pos_of_mem hi
  have hlt := (hall p hp).1.1
  rw [array_getElem!_eq_getElem hp] at hpi
  rw [← hpi]
  exact hlt

theorem lOK_nodup {b : ℕ} {L : Array ℕ}
    (h : lOK (CertD minus) minus b L = true) : L.toList.Nodup := by
  have h' := h
  unfold lOK at h'
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨_, _⟩, hhash⟩, _⟩, _⟩, _⟩ := h'
  exact nodup_toList_of_hashSetOfArray_size hhash

theorem lOK_zero_mem {b : ℕ} {L : Array ℕ}
    (h : lOK (CertD minus) minus b L = true) : 0 ∈ L := by
  have h' := h
  unfold lOK at h'
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨_, hcont⟩, _⟩, _⟩, _⟩, _⟩ := h'
  rw [Array.contains_iff_mem] at hcont
  exact hcont

private theorem elt_mem_stabO_of_act (hD : GrpFacts minus (CertD minus)) {c : ℕ}
    (hc : c < (CertD minus).O.size)
    (hact : Code.act (CertD minus).O[c]! (b0Of minus) = b0Of minus) :
    hD.elt c ∈ stabO minus := by
  rw [mem_stabO_iff]
  exact ⟨hD.elt_mem_O₀ hc, by rw [hD.elt_vec hc (b0Of minus), hact]⟩

private theorem zero_lt_size_O (hD : GrpFacts minus (CertD minus)) :
    0 < (CertD minus).O.size := by
  rw [hD.size_O]
  cases minus <;> norm_num

private theorem elt_conj_eq_elt_conjIdx (hD : GrpFacts minus (CertD minus)) {c m : ℕ}
    (hc : c < (CertD minus).O.size) (hm : m < (CertD minus).O.size) :
    hD.elt c * hD.elt m * (hD.elt c)⁻¹ =
      hD.elt (conjIdxOf (CertD minus) c m) := by
  obtain ⟨z, -, -, hzelt, hzdef⟩ := exists_elt_conj hD hc hm
  rw [← hzelt, hzdef]

private theorem elt_conj_mem_Lam_iff (hD : GrpFacts minus (CertD minus)) {c m kk : ℕ}
    (hc : c < (CertD minus).O.size) (hm : m < (CertD minus).O.size) :
    hD.elt c * hD.elt m * (hD.elt c)⁻¹ ∈ Lam minus kk ↔
      conjIdxOf (CertD minus) c m ∈ (CertL minus).Llist[kk]! := by
  obtain ⟨z, hzlt, -, hzelt, hzdef⟩ := exists_elt_conj hD hc hm
  have hlt : conjIdxOf (CertD minus) c m < (CertD minus).O.size := by
    rw [← hzdef]
    exact hzlt
  rw [← hzelt, hzdef]
  exact elt_mem_Lam_iff hD hlt

private theorem l2_mem_pair_of_mem_image {t : V₀ ≃ₗ[ZMod 2] V₀}
    (hD : GrpFacts minus (CertD minus)) {j c i : ℕ}
    (hc : c < (CertD minus).O.size) (hix : hD.elt i = t)
    (hall : ∀ x, x < ((CertL minus).Llist[j]!).size →
      conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = 0 ∨
        conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = i) :
    (fun x => hD.elt c * x * (hD.elt c)⁻¹) '' Lam minus j ⊆
      ({1, t} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨m, hm, hm_lt, hmy⟩ := hD.inIdx_iff.mp (mem_Lam_iff.mp hx)
  rw [← hmy]
  change hD.elt c * hD.elt m * (hD.elt c)⁻¹ ∈ ({1, t} : Set (V₀ ≃ₗ[ZMod 2] V₀))
  rw [elt_conj_eq_elt_conjIdx hD hc hm_lt]
  obtain ⟨q, hq, hqm⟩ := exists_pos_of_mem hm
  rw [← hqm]
  rcases hall q hq with h0 | hi0
  · rw [h0, hD.elt_zero]
    simp
  · rw [hi0, hix]
    simp

private theorem l2_mem_image_of_mem_pair {t : V₀ ≃ₗ[ZMod 2] V₀}
    (hD : GrpFacts minus (CertD minus)) {j c i : ℕ}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hc : c < (CertD minus).O.size) (hix : hD.elt i = t)
    (hzero' : ∃ x, x < ((CertL minus).Llist[j]!).size ∧
      conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = 0)
    (hi' : ∃ x, x < ((CertL minus).Llist[j]!).size ∧
      conjIdxOf (CertD minus) c (((CertL minus).Llist[j]!)[x]!) = i) :
    ({1, t} : Set (V₀ ≃ₗ[ZMod 2] V₀)) ⊆
      (fun x => hD.elt c * x * (hD.elt c)⁻¹) '' Lam minus j := by
  intro x hx
  rcases hx with h1 | ht'
  · refine ⟨1, ?_, ?_⟩
    · exact mem_Lam_iff.mpr
        (hD.inIdx_iff.mpr ⟨0, lOK_zero_mem hL, zero_lt_size_O hD, hD.elt_zero⟩)
    · rw [h1]
      simp
  · rw [Set.mem_singleton_iff] at ht'
    obtain ⟨q, hq, hqc⟩ := hi'
    have hqmem : ((CertL minus).Llist[j]!)[q]! ∈ (CertL minus).Llist[j]! :=
      Array.mem_toList_iff.mp (array_getElem!_mem_toList hq)
    have hqlt : ((CertL minus).Llist[j]!)[q]! < (CertD minus).O.size :=
      lOK_mem_lt hL hqmem
    refine ⟨hD.elt ((CertL minus).Llist[j]!)[q]!, ?_, ?_⟩
    · exact mem_Lam_iff.mpr (hD.inIdx_iff.mpr ⟨_, hqmem, hqlt, rfl⟩)
    · change hD.elt c * hD.elt ((CertL minus).Llist[j]!)[q]! * (hD.elt c)⁻¹ = x
      rw [elt_conj_eq_elt_conjIdx hD hc hqlt, hqc, hix, ht']

theorem l2_image (hb : censusBase minus () = true)
    {t : V₀ ≃ₗ[ZMod 2] V₀} (ht : t ∈ a2Set minus) :
    ∃ j, ∃ c ∈ stabO minus,
      (fun x => c * x * c⁻¹) '' Lam minus j = ({1, t} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  obtain ⟨hC, hA⟩ := ht
  have hfacts := censusBaseFacts_of hb
  have hD := hfacts.grp
  obtain ⟨i, hi, hix⟩ := hD.exists_elt_eq hC.1
  have hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) ((CertD minus).O[i]!) := by
    rw [← hix]
    exact hD.hasCode_elt hi
  have ha2 : i ∈ a2FixOf (CertD minus) minus (b0Of minus) :=
    a2FixOf_index hb hi hcode hC.2 hA
  obtain ⟨k, hk, hak⟩ := exists_pos_of_mem ha2
  let w := l2OK_wit hfacts.l2OK hk
  obtain ⟨j, c, hj, hc, hact, -, -, hall, hzero', hi'⟩ := w
  rw [hak] at hall hi'
  have hLOK := hfacts.lOK j hj
  have hgcC : hD.elt c ∈ stabO minus := elt_mem_stabO_of_act hD hc hact
  refine ⟨j, hD.elt c, hgcC, ?_⟩
  exact Set.Subset.antisymm
    (l2_mem_pair_of_mem_image hD hc hix hall)
    (l2_mem_image_of_mem_pair hD hLOK hc hix hzero' hi')

@[expose] def l3U (minus : Bool) (L : Array ℕ) (iu : ℕ) : Array ℕ :=
  L ++ L.map (fun x =>
    (CertD minus).idx.getD (Code.mul ((CertD minus).O[x]!) ((CertD minus).O[iu]!))
      (CertD minus).O.size)

@[expose] def l3V (minus : Bool) (c : ℕ) (U : Array ℕ) : Array ℕ :=
  U.map (fun x => conjIdxOf (CertD minus) c x)

structure L3Wit (minus : Bool) (j iu : ℕ) where
  kk : ℕ
  c : ℕ
  hkk : kk < (CertL minus).Llist.size
  hc : c < (CertD minus).O.size
  hact : Code.act (CertD minus).O[c]! (b0Of minus) = b0Of minus
  hUall : ∀ z, z ∈ l3U minus ((CertL minus).Llist[j]!) iu → z < (CertD minus).O.size
  hVall : ∀ y, y ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu) →
    y ∈ (CertL minus).Llist[kk]!
  hVcover : ∀ y, y ∈ (CertL minus).Llist[kk]! →
    y ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu)

noncomputable def l3OK_wit (h : l3OK (CertD minus) (b0Of minus) (CertL minus).Llist
    (CertL minus).l3tasks (CertL minus).l3wit = true)
    {k : ℕ} (hk : k < (CertL minus).l3tasks.size) :
    L3Wit minus ((CertL minus).l3tasks[k]!).1 ((CertL minus).l3tasks[k]!).2 := by
  have h' := h
  unfold l3OK at h'
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at h'
  obtain ⟨_, hall⟩ := h'
  have hkall := hall k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    Array.all_eq_true, and_assoc] at hkall
  obtain ⟨jlt, ult, kklt, clt, hactu, hinv, hnotmem, hcommL, hactc, hUsize, hUall,
    hUhash, hVsize, hVall, hVcover⟩ := hkall
  refine
    { kk := ((CertL minus).l3wit[k]!).1
      c := ((CertL minus).l3wit[k]!).2
      hkk := kklt
      hc := clt
      hact := hactc
      hUall := ?_
      hVall := ?_
      hVcover := ?_ }
  · intro z hz
    obtain ⟨p, hp, hpz⟩ := exists_pos_of_mem hz
    rw [← hpz, array_getElem!_eq_getElem hp]
    exact hUall p hp
  · intro y hy
    obtain ⟨p, hp, hpy⟩ := exists_pos_of_mem hy
    have hcont := hVall p hp
    rw [Array.contains_iff_mem] at hcont
    rw [← hpy, array_getElem!_eq_getElem hp]
    simpa [l3V, l3U] using hcont
  · intro y hy
    obtain ⟨p, hp, hpy⟩ := exists_pos_of_mem hy
    have hcont := hVcover p hp
    rw [Array.contains_iff_mem] at hcont
    rw [← hpy, array_getElem!_eq_getElem hp]
    simpa [l3V, l3U] using hcont

private theorem mem_l3U_left {j iu m : ℕ}
    (hm : m ∈ (CertL minus).Llist[j]!) :
    m ∈ l3U minus ((CertL minus).Llist[j]!) iu := by
  rw [l3U, ← Array.mem_toList_iff, Array.toList_append]
  exact List.mem_append_left _ (Array.mem_toList_iff.mpr hm)

private theorem mem_l3U_right {j iu m : ℕ}
    (hm : m ∈ (CertL minus).Llist[j]!) :
    (CertD minus).idx.getD
      (Code.mul ((CertD minus).O[m]!) ((CertD minus).O[iu]!)) (CertD minus).O.size ∈
        l3U minus ((CertL minus).Llist[j]!) iu := by
  rw [l3U, ← Array.mem_toList_iff, Array.toList_append]
  exact List.mem_append_right _ (by
    rw [Array.toList_map, List.mem_map]
    exact ⟨m, Array.mem_toList_iff.mpr hm, rfl⟩)

private theorem act_b0Of_of_mem_stabO (hD : GrpFacts minus (CertD minus)) {i : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀} (hi : i < (CertD minus).O.size)
    (hu : u ∈ stabO minus) (hueq : u = hD.elt i) :
    Code.act (CertD minus).O[i]! (b0Of minus) = b0Of minus := by
  apply vec_injective_of_lt (Code.act_lt _ _) (b0Of_lt minus)
  have h := hu.2
  rw [hueq, hD.elt_vec hi (b0Of minus)] at h
  exact h

private theorem code_mul_self_eq_one (hD : GrpFacts minus (CertD minus)) {i : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀} (hi : i < (CertD minus).O.size)
    (hueq : u = hD.elt i) (hu2 : u * u = 1) :
    Code.mul ((CertD minus).O[i]!) ((CertD minus).O[i]!) = Code.one := by
  have h2 := hD.hasCode_mul hi hi
  rw [← hueq] at h2
  rw [hu2] at h2
  exact h2.code_eq Code.hasCode_one (Code.mul_lt _ _) Code.one_lt

private theorem code_ne_one_of_not_mem_Lam (hD : GrpFacts minus (CertD minus)) {j i : ℕ}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hi : i < (CertD minus).O.size) (hnot : hD.elt i ∉ Lam minus j) :
    (CertD minus).O[i]! ≠ Code.one := by
  intro hone
  apply hnot
  have h1 : hD.elt i = 1 := by
    have h0 := zero_lt_size_O hD
    have hcode0 : Code.HasCode (hD.elt i : V₀ →ₗ[ZMod 2] V₀) ((CertD minus).O[0]!) := by
      rw [hD.zero]
      have h := hD.hasCode_elt hi
      rwa [hone] at h
    rw [hD.eq_elt_of_hasCode h0 hcode0, hD.elt_zero]
  rw [h1]
  exact mem_Lam_iff.mpr
    (hD.inIdx_iff.mpr ⟨0, lOK_zero_mem hL, zero_lt_size_O hD, hD.elt_zero⟩)

private theorem code_comm_of_comm_Lam (hD : GrpFacts minus (CertD minus)) {j i : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hi : i < (CertD minus).O.size) (hueq : u = hD.elt i)
    (hcomm : ∀ x ∈ Lam minus j, u * x = x * u) :
    ∀ x, x < ((CertL minus).Llist[j]!).size →
      Code.mul ((CertD minus).O[i]!) ((CertD minus).O[((CertL minus).Llist[j]!)[x]!]!) =
        Code.mul ((CertD minus).O[((CertL minus).Llist[j]!)[x]!]!) ((CertD minus).O[i]!) := by
  intro x hx
  have hxmem : ((CertL minus).Llist[j]!)[x]! ∈ (CertL minus).Llist[j]! :=
    Array.mem_toList_iff.mp (array_getElem!_mem_toList hx)
  have hxlt : ((CertL minus).Llist[j]!)[x]! < (CertD minus).O.size :=
    lOK_mem_lt hL hxmem
  have hmemLam : hD.elt ((CertL minus).Llist[j]!)[x]! ∈ Lam minus j :=
    (elt_mem_Lam_iff hD hxlt).mpr hxmem
  have hcx := hcomm (hD.elt ((CertL minus).Llist[j]!)[x]!) hmemLam
  rw [hueq] at hcx
  exact (hD.mul_comm_iff hi hxlt).mpr hcx

private theorem l3TaskValid_of_stabO (hD : GrpFacts minus (CertD minus)) {j iu : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hj : j < (CertL minus).Llist.size) (hiu : iu < (CertD minus).O.size)
    (hu : u ∈ stabO minus) (hueq : u = hD.elt iu) (hnot : u ∉ Lam minus j)
    (hu2 : u * u = 1) (hcomm : ∀ x ∈ Lam minus j, u * x = x * u) :
    l3TaskValid (CertD minus) (b0Of minus) (CertL minus).Llist j iu = true := by
  have hactu := act_b0Of_of_mem_stabO hD hiu hu hueq
  have hnotL : iu ∉ (CertL minus).Llist[j]! := by
    intro hmem
    apply hnot
    rw [hueq]
    exact (elt_mem_Lam_iff hD hiu).mpr hmem
  have hnot' : hD.elt iu ∉ Lam minus j := by
    rwa [hueq] at hnot
  have hnotCode := code_ne_one_of_not_mem_Lam hD hL hiu hnot'
  have hu2code := code_mul_self_eq_one hD hiu hueq hu2
  have hcommCode := code_comm_of_comm_Lam hD hL hiu hueq hcomm
  have hcontainsFalse : ((CertL minus).Llist[j]!).contains iu = false := by
    cases hc : ((CertL minus).Llist[j]!).contains iu
    · rfl
    · exact absurd (Array.contains_iff_mem.mp hc) hnotL
  have hinv : isInvCode ((CertD minus).O[iu]!) = true := by
    unfold isInvCode
    simp [hnotCode, hu2code]
  have hallcomm : ((CertL minus).Llist[j]!).all
      (fun x => Code.mul ((CertD minus).O[iu]!) ((CertD minus).O[x]!) ==
        Code.mul ((CertD minus).O[x]!) ((CertD minus).O[iu]!)) = true := by
    rw [Array.all_eq_true]
    intro x hx
    simpa [array_getElem!_eq_getElem hx] using hcommCode x hx
  unfold l3TaskValid
  simp only [hj, hiu, hactu, hinv, hallcomm, hcontainsFalse, decide_true, Bool.true_and,
    beq_iff_eq, beq_self_eq_true, Bool.not_false]

private theorem exists_l3_wit_of_task (hfacts : CensusBaseFacts minus) {j iu : ℕ}
    (hj : j < (CertL minus).Llist.size) (hiu : iu < (CertD minus).O.size)
    (hvalid : l3TaskValid (CertD minus) (b0Of minus) (CertL minus).Llist j iu = true) :
    ∃ kk c, kk < (CertL minus).Llist.size ∧ c < (CertD minus).O.size ∧
      Code.act (CertD minus).O[c]! (b0Of minus) = b0Of minus ∧
      hfacts.grp.elt c ∈ stabO minus ∧
      (∀ y, y ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu) →
        y ∈ (CertL minus).Llist[kk]!) ∧
      (∀ y, y ∈ (CertL minus).Llist[kk]! →
        y ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu)) := by
  have hcomplete := hfacts.l3Complete
  unfold l3Complete at hcomplete
  simp only [List.all_eq_true] at hcomplete
  have hjall := hcomplete j (List.mem_range.mpr hj)
  have hiuall := hjall iu (List.mem_range.mpr hiu)
  simp only [hvalid, if_true] at hiuall
  rw [Array.contains_iff_mem] at hiuall
  obtain ⟨k, hk, htask⟩ := exists_pos_of_mem hiuall
  let w := l3OK_wit hfacts.l3OK hk
  obtain ⟨kk, c, hkk, hc, hact, -, hVall, hVcover⟩ := w
  have hk1 : ((CertL minus).l3tasks[k]!).1 = j := by rw [htask]
  have hk2 : ((CertL minus).l3tasks[k]!).2 = iu := by rw [htask]
  simp only [hk1, hk2] at hVall hVcover
  exact ⟨kk, c, hkk, hc, hact,
    elt_mem_stabO_of_act hfacts.grp hc hact, hVall, hVcover⟩

private theorem l3_mem_Lam_of_mem_image (hD : GrpFacts minus (CertD minus)) {j iu kk c : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hK : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[kk]!) = true)
    (hc : c < (CertD minus).O.size) (hiu : iu < (CertD minus).O.size)
    (hVall : ∀ y, y ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu) →
      y ∈ (CertL minus).Llist[kk]!)
    (hueq : u = hD.elt iu) :
    (fun x => hD.elt c * x * (hD.elt c)⁻¹) ''
      (Lam minus j ∪ (fun x => x * u) '' Lam minus j) ⊆ Lam minus kk := by
  rintro y ⟨x, hx, rfl⟩
  rcases hx with hx | ⟨z, hz, rfl⟩
  · obtain ⟨m, hm, hm_lt, hmy⟩ := hD.inIdx_iff.mp (mem_Lam_iff.mp hx)
    rw [← hmy]
    change hD.elt c * hD.elt m * (hD.elt c)⁻¹ ∈ Lam minus kk
    have hmU : m ∈ l3U minus ((CertL minus).Llist[j]!) iu := mem_l3U_left hm
    have hmemV : conjIdxOf (CertD minus) c m ∈
        l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu) := by
      rw [l3V]
      exact Array.mem_map.mpr ⟨m, hmU, rfl⟩
    exact (elt_conj_mem_Lam_iff hD hc hm_lt).mpr (hVall _ hmemV)
  · obtain ⟨m, hm, hm_lt, hmy⟩ := hD.inIdx_iff.mp (mem_Lam_iff.mp hz)
    rw [← hmy]
    change hD.elt c * (hD.elt m * u) * (hD.elt c)⁻¹ ∈ Lam minus kk
    rw [hueq]
    obtain ⟨zprod, hzprod_lt, hzprod_code, hzprod_elt, hzprod_def⟩ :=
      exists_elt_mul hD hm_lt hiu
    have hzprod_mem : zprod ∈ l3U minus ((CertL minus).Llist[j]!) iu := by
      rw [hzprod_def]
      exact mem_l3U_right (iu := iu) hm
    have hmemV : conjIdxOf (CertD minus) c zprod ∈
        l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu) := by
      rw [l3V]
      exact Array.mem_map.mpr ⟨zprod, hzprod_mem, rfl⟩
    rw [← hzprod_elt]
    exact (elt_conj_mem_Lam_iff hD hc hzprod_lt).mpr (hVall _ hmemV)

private theorem l3_mem_image_of_mem_Lam (hD : GrpFacts minus (CertD minus)) {j iu kk c : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hc : c < (CertD minus).O.size) (hiu : iu < (CertD minus).O.size)
    (hVcover : ∀ y, y ∈ (CertL minus).Llist[kk]! →
      y ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu))
    (hueq : u = hD.elt iu) :
    Lam minus kk ⊆ (fun x => hD.elt c * x * (hD.elt c)⁻¹) ''
      (Lam minus j ∪ (fun x => x * u) '' Lam minus j) := by
  intro x hx
  obtain ⟨m, hm, hm_lt, hmy⟩ := hD.inIdx_iff.mp (mem_Lam_iff.mp hx)
  rw [← hmy]
  have hmemV : m ∈ l3V minus c (l3U minus ((CertL minus).Llist[j]!) iu) := hVcover m hm
  rw [l3V, Array.mem_map] at hmemV
  obtain ⟨z, hzU, hzc⟩ := hmemV
  rw [l3U, Array.mem_append] at hzU
  rcases hzU with hzL | hzM
  · have hzlt : z < (CertD minus).O.size := lOK_mem_lt hL hzL
    refine ⟨hD.elt z, Or.inl ((elt_mem_Lam_iff hD hzlt).mpr hzL), ?_⟩
    change hD.elt c * hD.elt z * (hD.elt c)⁻¹ = hD.elt m
    rw [elt_conj_eq_elt_conjIdx hD hc hzlt, hzc]
  · rw [Array.mem_map] at hzM
    obtain ⟨a, haL, haz⟩ := hzM
    have halt : a < (CertD minus).O.size := lOK_mem_lt hL haL
    obtain ⟨zprod, hzprod_lt, hzprod_code, hzprod_elt, hzprod_def⟩ :=
      exists_elt_mul hD halt hiu
    have hz_eq : z = zprod := by rw [← haz, ← hzprod_def]
    rw [hz_eq] at hzc
    refine ⟨hD.elt a * u, Or.inr ⟨hD.elt a, (elt_mem_Lam_iff hD halt).mpr haL, rfl⟩, ?_⟩
    change hD.elt c * (hD.elt a * u) * (hD.elt c)⁻¹ = hD.elt m
    rw [hueq, ← hzprod_elt, elt_conj_eq_elt_conjIdx hD hc hzprod_lt, hzc]

theorem l3_image (hb : censusBase minus () = true) {j : ℕ}
    {u : V₀ ≃ₗ[ZMod 2] V₀} (hu : u ∈ stabO minus) (hnot : u ∉ Lam minus j)
    (hu2 : u * u = 1) (hcomm : ∀ x ∈ Lam minus j, u * x = x * u) :
    ∃ k, ∃ c ∈ stabO minus,
      (fun x => c * x * c⁻¹) '' (Lam minus j ∪ (fun x => x * u) '' Lam minus j) =
        Lam minus k := by
  by_cases hj : j < (CertL minus).Llist.size
  · have hfacts := censusBaseFacts_of hb
    have hD := hfacts.grp
    have hLOK := hfacts.lOK j hj
    obtain ⟨iu, hiu, hixu⟩ := hD.exists_elt_eq hu.1
    have hueq : u = hD.elt iu := hixu.symm
    have hvalid := l3TaskValid_of_stabO hD hLOK hj hiu hu hueq hnot hu2 hcomm
    obtain ⟨kk, c, hkk, hc, -, hgcC, hVall, hVcover⟩ :=
      exists_l3_wit_of_task hfacts hj hiu hvalid
    have hKOK := hfacts.lOK kk hkk
    refine ⟨kk, hD.elt c, hgcC, ?_⟩
    exact Set.Subset.antisymm
      (l3_mem_Lam_of_mem_image hD hLOK hKOK hc hiu hVall hueq)
      (l3_mem_image_of_mem_Lam hD hLOK hc hiu hVcover hueq)
  · refine ⟨j, 1, ?_, ?_⟩
    · exact one_mem _
    · rw [Lam_eq_empty_of_ge hj]
      simp

theorem conjSub_eq_image {G : Type*} [Group G] (L : Subgroup G) (c : G) :
    (conjSub L c : Set G) = (fun x => c * x * c⁻¹) '' (L : Set G) := by
  ext x
  rw [show x ∈ (conjSub L c : Set G) ↔ c⁻¹ * x * c ∈ L from mem_conjSub]
  constructor
  · intro hx
    exact ⟨c⁻¹ * x * c, hx, by group⟩
  · rintro ⟨y, hy, rfl⟩
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy

theorem mem_candidatesOf_iff {A : Array (Array ℕ)} {j : ℕ} :
    j ∈ candidatesOf minus A ↔ j < A.size ∧ (A[j]!).size ≥ minCandSize minus := by
  simp [candidatesOf, Array.mem_toList_iff, List.mem_toArray, List.mem_filter, List.mem_range]

theorem natCard_Lam (hD : GrpFacts minus (CertD minus)) {b : ℕ} {j : ℕ}
    (hL : lOK (CertD minus) minus b ((CertL minus).Llist[j]!) = true) :
    Nat.card ↥(Lam minus j) = ((CertL minus).Llist[j]!).size := by
  classical
  set A : Array ℕ := (CertL minus).Llist[j]! with hA
  have hnd : A.toList.Nodup := lOK_nodup hL
  have hset : (Lam minus j : Set (V₀ ≃ₗ[ZMod 2] V₀)) =
      hD.elt '' (↑(A.toList.toFinset) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hiA, hi, hix⟩ := hD.inIdx_iff.mp (mem_Lam_iff.mp hx)
      exact ⟨i, List.mem_toFinset.mpr (Array.mem_toList_iff.mpr hiA), hix⟩
    · rintro ⟨i, hi, rfl⟩
      exact mem_Lam_iff.mpr
        (hD.inIdx_iff.mpr
          ⟨i, Array.mem_toList_iff.mp (List.mem_toFinset.mp hi),
            lOK_mem_lt hL (Array.mem_toList_iff.mp (List.mem_toFinset.mp hi)), rfl⟩)
  have hinj : Set.InjOn hD.elt (↑(A.toList.toFinset) : Set ℕ) := by
    intro i hi j hj hij
    exact hD.elt_injOn
      (lOK_mem_lt hL (Array.mem_toList_iff.mp (List.mem_toFinset.mp hi)))
      (lOK_mem_lt hL (Array.mem_toList_iff.mp (List.mem_toFinset.mp hj))) hij
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]
  change Fintype.card ↥(A.toList.toFinset) = A.size
  rw [Fintype.card_coe, List.toFinset_card_of_nodup hnd, Array.length_toList]

private theorem lam_index_lt_of_one_mem {j : ℕ}
    (h : (1 : V₀ ≃ₗ[ZMod 2] V₀) ∈ Lam minus j) :
    j < (CertL minus).Llist.size := by
  by_contra hge
  rw [Lam_eq_empty_of_ge hge] at h
  exact h

private theorem mem_candidatesOf_of_conj_image (hD : GrpFacts minus (CertD minus))
    {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {j : ℕ} {c : V₀ ≃ₗ[ZMod 2] V₀}
    (hL : lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true)
    (hjlt : j < (CertL minus).Llist.size)
    (himg : (fun x => c * x * c⁻¹) '' (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) = Lam minus j)
    (hcard : (if minus then 8 else 4) ≤ Nat.card L) :
    j ∈ candidatesOf minus (CertL minus).Llist := by
  have hcardLam : Nat.card ↥(Lam minus j) = ((CertL minus).Llist[j]!).size :=
    natCard_Lam hD hL
  have hcardL : Nat.card L = Nat.card ↥(Lam minus j) := by
    have h1 : Nat.card ↥(conjSub L c) = Nat.card L := by
      rw [conjSub]
      exact Subgroup.card_map_of_injective (MulAut.conj c).injective
    have h2 : Nat.card ↥(conjSub L c) = Nat.card ↥(Lam minus j) := by
      have hset : (conjSub L c : Set (V₀ ≃ₗ[ZMod 2] V₀)) =
          (Lam minus j : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
        rw [conjSub_eq_image, himg]
      exact Nat.card_congr
        (Equiv.cast (congrArg (fun S : Set (V₀ ≃ₗ[ZMod 2] V₀) => (↥S : Type _)) hset))
    exact h1.symm.trans h2
  have hsize : (if minus then 8 else 4) ≤ ((CertL minus).Llist[j]!).size := by
    rw [← hcardLam, ← hcardL]
    exact hcard
  exact mem_candidatesOf_iff.mpr ⟨hjlt, by simpa [minCandSize] using hsize⟩

theorem censusBase_L_reduce (hb : censusBase minus () = true)
    (H L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (hH : H ≤ O₀ minus)
    (hc : CensusCond minus H L (Code.vec (b0Of minus)))
    (ht : ∃ t ∈ L, IsTypeA (qModel minus) t 2) :
    ∃ ci < (candidatesOf minus (ldata minus ()).Llist).size, ∃ c ∈ O₀ minus,
      c (Code.vec (b0Of minus)) = Code.vec (b0Of minus) ∧
      ∀ x, x ∈ conjSub L c ↔ InCodeList minus
        ((ldata minus ()).Llist[(candidatesOf minus (ldata minus ()).Llist)[ci]!]!) x := by
  have hfacts := censusBaseFacts_of hb
  have hD := hfacts.grp
  have hC : L ≤ stabO minus := by
    intro x hx
    rw [mem_stabO_iff]
    exact ⟨hH (hc.1 hx), hc.2.1 x hx⟩
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  haveI : Finite L := Subtype.finite
  obtain ⟨t, htL, htA⟩ := ht
  have htA2 : t ∈ a2Set minus := ⟨hC htL, htA⟩
  have hinv : ∀ y ∈ L, y * y = 1 := hc.2.2.1
  obtain ⟨j, c, hcC, himg⟩ :=
    lList_induction (C := stabO minus) (ι := ℕ) (Λ := Lam minus) (A := a2Set minus)
      (fun t ht => l2_image (t := t) hb ht)
      (fun j u hu hnot hu2 hcomm => l3_image (j := j) (u := u) hb hu hnot hu2 hcomm)
      hC inferInstance hinv htA2 htL
  have h1mem : (1 : V₀ ≃ₗ[ZMod 2] V₀) ∈ Lam minus j := by
    rw [← himg]
    exact ⟨1, L.one_mem, by group⟩
  have hjlt : j < (CertL minus).Llist.size := lam_index_lt_of_one_mem h1mem
  have hLOK := hfacts.lOK j hjlt
  have hcand : j ∈ candidatesOf minus (CertL minus).Llist :=
    mem_candidatesOf_of_conj_image hD hLOK hjlt himg hc.2.2.2.1
  obtain ⟨ci, hci, hcij⟩ := exists_pos_of_mem hcand
  refine ⟨ci, hci, c, hcC.1, hcC.2, ?_⟩
  intro x
  change x ∈ (conjSub L c : Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔ InCodeList minus
    ((ldata minus ()).Llist[(candidatesOf minus (ldata minus ()).Llist)[ci]!]!) x
  rw [conjSub_eq_image, himg, hcij]
  rfl

end CFSG.GF2Type.Smith1979W3.Cert690

end
