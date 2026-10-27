module

public import CFSG.LieType.Ree.LargeReeEightBlocks

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

theorem list_prod_map_filter {α G : Type*} [Monoid G] (p : α → Bool) (f : α → G) :
    ∀ l : List α, (∀ a ∈ l, p a = false → f a = 1) →
      (l.map f).prod = ((l.filter p).map f).prod
  | [], _ => rfl
  | a :: l, h => by
    have ih := list_prod_map_filter p f l fun b hb => h b (List.mem_cons_of_mem a hb)
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, ih]
    · rw [List.filter_cons_of_neg ha, List.map_cons, List.prod_cons, ih,
        h a List.mem_cons_self (by simpa using ha), one_mul]

theorem eq_zero_of_list_prod_mem_heightSeries
    {τ : Tag} {K : Type} [Field K]
    {l : List ((Fin τ.rank → ℤ) × K)} (hnd : (l.map Prod.fst).Nodup)
    (hset : {x | x ∈ l.map Prod.fst} = {α | IsRoot τ α ∧ 0 < height α}) {h : ℤ}
    (hmem : (l.map fun p => pinnedX τ K p.1 p.2).prod ∈ heightSeries τ K h)
    {p : (Fin τ.rank → ℤ) × K} (hp : p ∈ l) (hlt : height p.1 < h) : p.2 = 0 := by
  classical
  set L := l.map Prod.fst with hLdef
  let c : (Fin τ.rank → ℤ) → K := fun α => if hα : ∃ q ∈ l, q.1 = α then hα.choose.2 else 0
  have hc : ∀ q ∈ l, c q.1 = q.2 := by
    intro q hq
    have hex : ∃ r ∈ l, r.1 = q.1 := ⟨q, hq, rfl⟩
    simp only [c]
    rw [dite_eq_left hex, List.inj_on_of_nodup_map hnd hex.choose_spec.1 hq hex.choose_spec.2]
  have hprod : (l.map fun q => pinnedX τ K q.1 q.2) = L.map fun α => pinnedX τ K α (c α) := by
    rw [hLdef, List.map_map]
    exact List.map_congr_left fun q hq => by simp only [Function.comp_apply, hc q hq]
  set Lh := L.filter fun α => decide (h ≤ height α) with hLhdef
  have hLhS : {x | x ∈ Lh} = {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α} := by
    ext x
    have hx := Set.ext_iff.1 hset x
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq, hLhdef, List.mem_filter, decide_eq_true_eq, hx, and_assoc]
  have hcl : ∀ α ∈ {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α},
      ∀ β ∈ {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α} := by
    intro α hα β hβ a b ha hb hr
    obtain ⟨hr', hp', hle⟩ := nsmul_add_nsmul_mem_heightSet (k := 1) ⟨hα.2.1, hα.2.2⟩
      ⟨hβ.2.1, hβ.2.1⟩ ha hb hr
    exact ⟨hr', hp', by linarith⟩
  obtain ⟨-, hsurj, -⟩ := list_prod_pinnedX_bijective (K := K) (fun α hα => ⟨hα.1, hα.2.1⟩) hcl
    (hnd.filter _) hLhS
  obtain ⟨c', hc'⟩ := hsurj _ hmem
  let c'' : (Fin τ.rank → ℤ) → K := fun α => if h ≤ height α then c' α else 0
  have h1 : (L.map fun α => pinnedX τ K α (c'' α)).prod =
      (Lh.map fun α => pinnedX τ K α (c' α)).prod := by
    rw [list_prod_map_filter (fun α => decide (h ≤ height α)) _ L fun α _ hα => by
      have hα' : ¬ h ≤ height α := by simpa using hα
      simp only [c'', ite_eq_right hα', pinnedX_zero]]
    refine congrArg List.prod (List.map_congr_left fun α hα => ?_)
    have hα' : h ≤ height α := by simpa using (List.mem_filter.1 hα).2
    simp only [c'', ite_eq_left hα']
  obtain ⟨-, -, huniq⟩ := list_prod_pinnedX_bijective (K := K)
    (S := {α | IsRoot τ α ∧ 0 < height α}) (fun α hα => hα) posRoots_nsmul_add_nsmul_mem hnd hset
  have heq := huniq c c'' (by rw [← hprod, h1, hc'])
  rw [← hc p hp, heq p.1 (List.mem_map_of_mem hp)]
  simp only [c'', ite_eq_right (not_le.2 hlt)]

@[expose] def posBlock
    : Fin 8 → Set (Fin F4.tag.rank → ℤ) :=
  ![twoSet 0, twoSet 1, twoSet 2, twoSet 3, fourSet 0, fourSet 1, fourSet 2, fourSet 3]

@[expose] def posIdx : Fin 8 → Fin 16 :=
  ![0, 4, 6, 12, 1, 3, 9, 11]

@[expose] def posWeyl : Fin 8 → Fin F4.fixedWeylOrder :=
  ![kTwo 0, kTwo 1, kTwo 2, kTwo 3, kFour 0, kFour 1, kFour 2, kFour 3]

@[expose] def posStd : Fin 8 → Fin F4.fixedOrbitCount :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩,
    ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩]

theorem posBlock_eq_image (k : Fin 8) :
    posBlock k = (F4.fixedRelElt (posWeyl k) • ·) '' F4.fixedOrbitRoots (posStd k) := by
  fin_cases k <;> rfl

theorem posBlock_check : ∀ k : Fin 8,
    largeReeBlockImage (posWeyl k) (posStd k) ⊆ largeReeBlockTable (posIdx k) ∧
      largeReeBlockTable (posIdx k) ⊆ largeReeBlockImage (posWeyl k) (posStd k) := by
  decide +kernel

theorem posBlock_eq_table
    (k : Fin 8) :
    posBlock k = {x | x ∈ largeReeBlockTable (posIdx k)} := by
  rw [posBlock_eq_image, image_fixedRelElt_fixedOrbitRoots]
  exact setOf_mem_eq_of_subset (posBlock_check k).1 (posBlock_check k).2

theorem posBlock_injective :
    Function.Injective posBlock := by
  have h : Function.Injective posIdx := by decide
  have e : posBlock = fun k => {x | x ∈ largeReeBlockTable (posIdx k)} := funext posBlock_eq_table
  rw [e]
  exact largeReeBlockSet_injective.comp h

theorem posIdx_check : ∀ k : Fin 8, ∀ x ∈ largeReeBlockTable (posIdx k), 0 < height x := by
  decide +kernel

theorem posIdx_surj_check : ∀ i : Fin 16, (∀ x ∈ largeReeBlockTable i, 0 < height x) →
    ∃ k : Fin 8, posIdx k = i := by
  decide +kernel

theorem range_posBlock :
    Set.range posBlock = largeReePosBlocks := by
  ext Q
  constructor
  · rintro ⟨k, rfl⟩
    rw [posBlock_eq_table]
    exact ⟨largeReeBlockSet_mem _, (largeReeBlockSet_subset_iff _).2 (posIdx_check k)⟩
  · rintro ⟨hQ, hpos⟩
    rw [largeReeBlocks_eq_range] at hQ
    obtain ⟨i, rfl⟩ := hQ
    obtain ⟨k, rfl⟩ := posIdx_surj_check i ((largeReeBlockSet_subset_iff i).1 hpos)
    exact ⟨k, posBlock_eq_table k⟩

variable {K : Type} [Field K]

@[expose] def blockProd
    (s c d : Fin 4 → K) : ModGL F4.tag K :=
  twoCoord 0 (s 0) * twoCoord 1 (s 1) * twoCoord 2 (s 2) * twoCoord 3 (s 3) *
    (fourCoord 0 (c 0) (d 0) * fourCoord 1 (c 1) (d 1) * fourCoord 2 (c 2) (d 2) *
      fourCoord 3 (c 3) (d 3))

@[expose] def blockPairs (s c d : Fin 4 → K) : List ((Fin F4.tag.rank → ℤ) × K) :=
  [(twoRoot 0 0, s 0), (twoRoot 0 1, s 0 ^ 4), (twoRoot 1 0, s 1), (twoRoot 1 1, s 1 ^ 4),
    (twoRoot 2 0, s 2), (twoRoot 2 1, s 2 ^ 4), (twoRoot 3 0, s 3), (twoRoot 3 1, s 3 ^ 4),
    (fourRoot 0 0, c 0), (fourRoot 0 1, c 0 ^ 4), (fourRoot 0 2, d 0),
    (fourRoot 0 3, d 0 ^ 4 + c 0 ^ 6),
    (fourRoot 1 0, c 1), (fourRoot 1 1, c 1 ^ 4), (fourRoot 1 2, d 1),
    (fourRoot 1 3, d 1 ^ 4 + c 1 ^ 6),
    (fourRoot 2 0, c 2), (fourRoot 2 1, c 2 ^ 4), (fourRoot 2 2, d 2),
    (fourRoot 2 3, d 2 ^ 4 + c 2 ^ 6),
    (fourRoot 3 0, c 3), (fourRoot 3 1, c 3 ^ 4), (fourRoot 3 2, d 3),
    (fourRoot 3 3, d 3 ^ 4 + c 3 ^ 6)]

@[expose] def blockRoots : List (Fin F4.tag.rank → ℤ) :=
  [twoRoot 0 0, twoRoot 0 1, twoRoot 1 0, twoRoot 1 1, twoRoot 2 0, twoRoot 2 1, twoRoot 3 0,
    twoRoot 3 1, fourRoot 0 0, fourRoot 0 1, fourRoot 0 2, fourRoot 0 3, fourRoot 1 0,
    fourRoot 1 1, fourRoot 1 2, fourRoot 1 3, fourRoot 2 0, fourRoot 2 1, fourRoot 2 2,
    fourRoot 2 3, fourRoot 3 0, fourRoot 3 1, fourRoot 3 2, fourRoot 3 3]

theorem map_fst_blockPairs (s c d : Fin 4 → K) : (blockPairs s c d).map Prod.fst = blockRoots :=
  rfl

theorem blockRoots_nodup : blockRoots.Nodup := by
  decide +kernel

theorem blockRoots_check : ∀ x ∈ blockRoots,
    ∃ k < F4.tag.rootCertificate.roots.length, F4.tag.rootCertificate.root k = x ∧
      0 < height x := by
  decide +kernel

theorem blockRoots_cover : ∀ k < F4.tag.rootCertificate.roots.length,
    0 < height (F4.tag.rootCertificate.root k) → F4.tag.rootCertificate.root k ∈ blockRoots := by
  decide +kernel

theorem setOf_mem_blockRoots :
    {x | x ∈ blockRoots} = {α : Fin F4.tag.rank → ℤ | IsRoot F4.tag α ∧ 0 < height α} := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl, hpos⟩ := blockRoots_check x hx
    exact ⟨RootCertificate.isRoot_root (Tag.rootCertificate_check F4.tag) k hk, hpos⟩
  · rintro ⟨hx, hpos⟩
    obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check F4.tag)).1 hx
    exact blockRoots_cover k hk hpos

variable [CharP K F4.prime]

theorem list_prod_blockPairs
    (s c d : Fin 4 → K) :
    ((blockPairs s c d).map fun p => pinnedX F4.tag K p.1 p.2).prod = blockProd s c d := by
  simp only [blockPairs, blockProd, twoCoord_eq, fourCoord_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem blockProd_mem_heightSeries
    {s c d : Fin 4 → K} {h : ℤ}
    (hx : blockProd s c d ∈ heightSeries F4.tag K h) :
    (∀ t, height (twoRoot t 0) < h → s t = 0) ∧ (∀ f, height (fourRoot f 0) < h → c f = 0) ∧
      ∀ f, height (fourRoot f 2) < h → d f = 0 := by
  rw [← list_prod_blockPairs] at hx
  have hnd : ((blockPairs s c d).map Prod.fst).Nodup := by
    rw [map_fst_blockPairs]
    exact blockRoots_nodup
  have hset : {x | x ∈ (blockPairs s c d).map Prod.fst} =
      {α | IsRoot F4.tag α ∧ 0 < height α} := by
    rw [map_fst_blockPairs]
    exact setOf_mem_blockRoots
  refine ⟨fun t ht => ?_, fun f hf => ?_, fun f hf => ?_⟩
  · have hp : (twoRoot t 0, s t) ∈ blockPairs s c d := by
      fin_cases t <;> simp [blockPairs]
    exact eq_zero_of_list_prod_mem_heightSeries hnd hset hx hp ht
  · have hp : (fourRoot f 0, c f) ∈ blockPairs s c d := by
      fin_cases f <;> simp [blockPairs]
    exact eq_zero_of_list_prod_mem_heightSeries hnd hset hx hp hf
  · have hp : (fourRoot f 2, d f) ∈ blockPairs s c d := by
      fin_cases f <;> simp [blockPairs]
    exact eq_zero_of_list_prod_mem_heightSeries hnd hset hx hp hf

variable [Finite K]

theorem exists_blockProd_eq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {x : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedPosUnipotent K 1) : ∃ s c d : Fin 4 → K, blockProd s c d = x := by
  obtain ⟨u, hu, rfl⟩ :=
    (bijOn_list_prod_largeReeBlockGroup K 1 posBlock posBlock_injective range_posBlock).2.2 hx
  have hu' : ∀ k, u k ∈ largeReeBlockGroup K 1 (posBlock k) := fun k => hu k (Set.mem_univ k)
  obtain ⟨s0, h0⟩ := exists_twoCoord_eq hK 0 (hu' 0)
  obtain ⟨s1, h1⟩ := exists_twoCoord_eq hK 1 (hu' 1)
  obtain ⟨s2, h2⟩ := exists_twoCoord_eq hK 2 (hu' 2)
  obtain ⟨s3, h3⟩ := exists_twoCoord_eq hK 3 (hu' 3)
  obtain ⟨c0, d0, h4⟩ := exists_fourCoord_eq hK 0 (hu' 4)
  obtain ⟨c1, d1, h5⟩ := exists_fourCoord_eq hK 1 (hu' 5)
  obtain ⟨c2, d2, h6⟩ := exists_fourCoord_eq hK 2 (hu' 6)
  obtain ⟨c3, d3, h7⟩ := exists_fourCoord_eq hK 3 (hu' 7)
  refine ⟨![s0, s1, s2, s3], ![c0, c1, c2, c3], ![d0, d1, d2, d3], ?_⟩
  change _ = (List.ofFn u).prod
  rw [List.ofFn_eq_map, show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, blockProd,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, mul_assoc]

end CFSG.LieType.Ree.LargeReeCover
