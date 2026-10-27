module

public import CFSG.LargeExtraspecial.SMod20AutPlane
public import CFSG.Fischer.T46Simple
import all CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

@[expose] def e4Pts : List ℕ :=
  ((List.range 256).map (16 * ·)).filter fun c => c != 0 && hermC c c == 0 && normC c == c

@[expose] def localCheck : Bool :=
  (List.range 27).all (fun j => (wMask j).testBit 5) &&
  e4Pts.all fun a => e4Pts.all fun b => decide (b ≤ a) || hermC a b != 0 ||
    (List.range 27).any fun j => (wMask j).testBit a && (wMask j).testBit b

theorem localCheck_eq : localCheck = true := by decide +kernel

@[expose] def v0 : W := vecOfCode 5

theorem v0_zero : v0 0 = 1 := by decide

theorem v0_ne_zero : v0 ≠ 0 := fun h => by simpa [h] using v0_zero

theorem hermStd_v0 (x : W) : hermStd x v0 = x 0 + x 1 := by
  have h : ∀ i : Fin 6, v0 i = if i.val < 2 then 1 else 0 := by decide
  simp only [hermStd, Fin.sum_univ_six, h]
  simp

theorem hermStd_v0_v0 : hermStd v0 v0 = 0 := by
  rw [hermStd_v0]
  decide

theorem codeOf_lt_of_coords (w : W) (h0 : w 0 = 0) (h1 : w 1 = 0) : codeOf w % 16 = 0 := by
  have e0 : (w 0).code.val = 0 := by rw [h0]; rfl
  have e1 : (w 1).code.val = 0 := by rw [h1]; rfl
  unfold codeOf
  rw [e0, e1]
  omega

theorem normV_normV {w : W} (hw : w ≠ 0) : normV (normV w) = normV w := by
  obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw
  conv_lhs => rw [hcw]
  rw [normV_smul hc]

theorem normC_mem_e4Pts {w : W} (hw : w ≠ 0) (hiso : hermStd w w = 0) (h0 : w 0 = 0)
    (h1 : w 1 = 0) : normC (codeOf w) ∈ e4Pts := by
  obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw
  have hn0 : normV w ≠ 0 := by rw [hcw]; exact smul_ne_zero hc hw
  have hni : hermStd (normV w) (normV w) = 0 := by
    rw [hcw, hermStd_smul_left, hermStd_smul_right, hiso, mul_zero, mul_zero]
  have hz0 : normV w 0 = 0 := by rw [hcw, Pi.smul_apply, h0, smul_zero]
  have hz1 : normV w 1 = 0 := by rw [hcw, Pi.smul_apply, h1, smul_zero]
  rw [normC_codeOf]
  have hm := codeOf_lt_of_coords _ hz0 hz1
  have hlt := codeOf_lt (normV w)
  unfold e4Pts
  rw [List.mem_filter, List.mem_map]
  refine ⟨⟨codeOf (normV w) / 16, List.mem_range.2 (by omega), by omega⟩, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨fun h => hn0 ((codeOf_eq_zero_iff _).1 h), ?_⟩, ?_⟩
  · rw [hermC_codeOf, hni]
    rfl
  · rw [normC_codeOf, normV_normV hw]

theorem localCheck_parts :
    (∀ j < 27, (wMask j).testBit 5 = true) ∧ ∀ a ∈ e4Pts, ∀ b ∈ e4Pts, a < b → hermC a b = 0 →
      ∃ j < 27, (wMask j).testBit a = true ∧ (wMask j).testBit b = true := by
  have h := localCheck_eq
  unfold localCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq, List.any_eq_true] at h
  refine ⟨h.1, fun a ha b hb hab hh => ?_⟩
  rcases h.2 a ha b hb with (h1 | h1) | ⟨j, hj, h2, h3⟩
  · omega
  · exact absurd hh h1
  · exact ⟨j, hj, h2, h3⟩

theorem mem_planeSub_of_testBit {j c : ℕ} (hc : c < 4096) (h : (wMask j).testBit c = true) :
    vecOfCode c ∈ planeSub j := by
  rw [← testBit_wMask_iff, codeOf_vecOfCode hc]
  exact h

theorem vecOfCode_normC (w : W) : vecOfCode (normC (codeOf w)) = normV w := by
  rw [normC_codeOf, vecOfCode_codeOf]

theorem mem_of_normV_mem {w : W} (hw : w ≠ 0) {S : Submodule F4 W} (h : normV w ∈ S) : w ∈ S := by
  obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw
  rw [hcw] at h
  have := S.smul_mem c⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

@[expose] def hyp0 : Submodule F4 W := LinearMap.ker (LinearMap.proj 0 : W →ₗ[F4] F4)

theorem finrank_hyp0 : finrank F4 hyp0 = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj 0 : W →ₗ[F4] F4)
  have hr : finrank F4 (LinearMap.range (LinearMap.proj 0 : W →ₗ[F4] F4)) = 1 := by
    rw [LinearMap.range_eq_top.2 (fun c => ⟨fun _ => c, rfl⟩), finrank_top, Module.finrank_self]
  rw [hr, Module.finrank_fin_fun] at h
  show finrank F4 (LinearMap.ker (LinearMap.proj 0 : W →ₗ[F4] F4)) = 5
  omega

theorem exists_planeSub_of_v0 {U : Submodule F4 W}
    (hU : IsTIPlane U) (h0 : v0 ∈ U) : ∃ j < 27, planeSub j = U := by
  have hdim : 2 ≤ finrank F4 ↥(U ⊓ hyp0) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U hyp0
    have h2 : finrank F4 ↥(U ⊔ hyp0) ≤ 6 := by
      have := Submodule.finrank_le (U ⊔ hyp0)
      rwa [Module.finrank_fin_fun] at this
    rw [hU.1, finrank_hyp0] at h1
    omega
  have hLE : ∀ x ∈ U ⊓ hyp0, x ∈ U ∧ x 0 = 0 ∧ x 1 = 0 := by
    intro x hx
    obtain ⟨hxU, hx0⟩ := Submodule.mem_inf.1 hx
    have hx0' : x 0 = 0 := hx0
    have horth := hU.2 x hxU v0 h0
    rw [hermStd_v0, hx0', zero_add] at horth
    exact ⟨hxU, hx0', horth⟩
  obtain ⟨a, ha0⟩ : ∃ a : ↥(U ⊓ hyp0), a ≠ 0 := by
    have : 0 < finrank F4 ↥(U ⊓ hyp0) := by omega
    obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.1 this
    exact ⟨a, ha⟩
  obtain ⟨b, hab⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := F4) (by omega) ha0
  have hab' : LinearIndependent F4 ![(a : W), (b : W)] := by
    have := hab.map' (U ⊓ hyp0).subtype (Submodule.ker_subtype _)
    convert this using 1
    funext k
    fin_cases k <;> rfl
  obtain ⟨haU, ha0', ha1'⟩ := hLE a a.2
  obtain ⟨hbU, hb0', hb1'⟩ := hLE b b.2
  have hane : (a : W) ≠ 0 := hab'.ne_zero 0
  have hbne : (b : W) ≠ 0 := hab'.ne_zero 1
  have haiso := hU.2 _ haU _ haU
  have hbiso := hU.2 _ hbU _ hbU
  have hma := normC_mem_e4Pts hane haiso ha0' ha1'
  have hmb := normC_mem_e4Pts hbne hbiso hb0' hb1'
  have hne : normC (codeOf (a : W)) ≠ normC (codeOf (b : W)) := by
    intro h
    rw [normC_codeOf, normC_codeOf] at h
    have h' := codeOf_injective h
    obtain ⟨c, hc, hca⟩ := normV_eq_smul hane
    obtain ⟨d, hd, hdb⟩ := normV_eq_smul hbne
    rw [hca, hdb] at h'
    have := LinearIndependent.pair_iff.1 hab' c (-d) (by rw [h', neg_smul, add_neg_cancel])
    exact hc this.1
  have horth : ∀ (x y : W), x ∈ U → y ∈ U → hermC (normC (codeOf x)) (normC (codeOf y)) = 0 := by
    intro x y hx hy
    rw [normC_codeOf, normC_codeOf, hermC_codeOf]
    have hx' : normV x ∈ U := U.smul_mem _ hx
    have hy' : normV y ∈ U := U.smul_mem _ hy
    rw [hU.2 _ hx' _ hy']
    rfl
  obtain ⟨j, hj, hja, hjb⟩ : ∃ j < 27, (wMask j).testBit (normC (codeOf (a : W))) = true ∧
      (wMask j).testBit (normC (codeOf (b : W))) = true := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact localCheck_parts.2 _ hma _ hmb hlt (horth _ _ haU hbU)
    · obtain ⟨j, hj, h1, h2⟩ := localCheck_parts.2 _ hmb _ hma hlt (horth _ _ hbU haU)
      exact ⟨j, hj, h2, h1⟩
  have hv0j : v0 ∈ planeSub j := mem_planeSub_of_testBit (by norm_num) (localCheck_parts.1 j hj)
  have haj : (a : W) ∈ planeSub j := by
    apply mem_of_normV_mem hane
    rw [← vecOfCode_normC]
    exact mem_planeSub_of_testBit (by rw [normC_codeOf]; exact codeOf_lt _) hja
  have hbj : (b : W) ∈ planeSub j := by
    apply mem_of_normV_mem hbne
    rw [← vecOfCode_normC]
    exact mem_planeSub_of_testBit (by rw [normC_codeOf]; exact codeOf_lt _) hjb
  have hind : LinearIndependent F4 ![v0, (a : W), (b : W)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at hg
    have hg0 : g 0 = 0 := by
      have := congrFun hg 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v0_zero, ha0', hb0',
        mul_zero, add_zero, mul_one] at this
      exact this
    rw [hg0, zero_smul, zero_add] at hg
    have := LinearIndependent.pair_iff.1 hab' (g 1) (g 2) (by simpa using hg)
    intro k
    fin_cases k
    · exact hg0
    · exact this.1
    · exact this.2
  have hspan : finrank F4 (Submodule.span F4 (Set.range ![v0, (a : W), (b : W)])) = 3 := by
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hle : ∀ S : Submodule F4 W, v0 ∈ S → (a : W) ∈ S → (b : W) ∈ S →
      Submodule.span F4 (Set.range ![v0, (a : W), (b : W)]) ≤ S := by
    intro S h1 h2 h3
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact h1
    · exact h2
    · exact h3
  have hU' := Submodule.eq_of_le_of_finrank_eq (hle U h0 haU hbU) (by rw [hspan, hU.1])
  have hj' := Submodule.eq_of_le_of_finrank_eq (hle (planeSub j) hv0j haj hbj)
    (by rw [hspan, finrank_planeSub (by omega)])
  exact ⟨j, hj, hj'.symm.trans hU'⟩

@[expose] noncomputable def gEquiv (g : GL (Fin 6) F4) : W ≃ₗ[F4] W where
  toFun x := (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ x
  invFun x := ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x
  map_add' x y := mulVec_add _ x y
  map_smul' c x := mulVec_smul _ c x
  left_inv x := inv_mulVec_mulVec' g x
  right_inv x := mulVec_inv_mulVec g x

@[expose] noncomputable def mapG (g : GL (Fin 6) F4) (U : Submodule F4 W) : Submodule F4 W :=
  U.map (gEquiv g).toLinearMap

theorem mem_mapG {g : GL (Fin 6) F4} {U : Submodule F4 W} {x : W} :
    x ∈ mapG g U ↔ ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x ∈ U :=
  Submodule.mem_map_equiv U (e := gEquiv g)

theorem isTIPlane_mapG {g : GU0} {U : Submodule F4 W} (hU : IsTIPlane U) :
    IsTIPlane (mapG (g : GL (Fin 6) F4) U) := by
  refine ⟨by rw [mapG, LinearEquiv.finrank_map_eq, hU.1], fun x hx y hy => ?_⟩
  rw [mem_mapG] at hx hy
  rw [← mulVec_inv_mulVec (g : GL (Fin 6) F4) x, ← mulVec_inv_mulVec (g : GL (Fin 6) F4) y,
    hermStd_mulVec]
  exact hU.2 _ hx _ hy

theorem mapG_injective (g : GL (Fin 6) F4) : Function.Injective (mapG g) :=
  Submodule.map_injective_of_injective (gEquiv g).injective

noncomputable def tiPlanes : Finset (Submodule F4 W) :=
  (Set.toFinite {U : Submodule F4 W | IsTIPlane U}).toFinset

theorem mem_tiPlanes {U : Submodule F4 W} : U ∈ tiPlanes ↔ IsTIPlane U :=
  Set.Finite.mem_toFinset _

@[expose] def isoVecs : Finset W := Finset.univ.filter fun v => v ≠ 0 ∧ hermStd v v = 0

theorem mem_isoVecs {v : W} : v ∈ isoVecs ↔ v ≠ 0 ∧ hermStd v v = 0 := by
  simp [isoVecs]

@[expose] def unitsF4 : Finset F4 := Finset.univ.filter fun c => c ≠ 0

theorem card_unitsF4 : unitsF4.card = 3 := by decide

theorem exists_smul_uVec {v : W} (hv0 : v ≠ 0)
    (hvi : hermStd v v = 0) : ∃ p : Fin 693, ∃ c : F4, c ∈ unitsF4 ∧ c • uVec (p : ℕ) = v := by
  obtain ⟨c, hc, hcv⟩ := uVec_ptOf v hv0 hvi
  refine ⟨ptOf v hv0 hvi, c⁻¹, by simp [unitsF4, hc], ?_⟩
  rw [hcv, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem card_isoVecs_le : isoVecs.card ≤ 2079 := by
  have h : isoVecs ⊆ ((Finset.univ : Finset (Fin 693)) ×ˢ unitsF4).image
      (fun pc => pc.2 • uVec (pc.1 : ℕ)) := by
    intro v hv
    rw [Finset.mem_image]
    obtain ⟨p, c, hc, hpc⟩ := exists_smul_uVec (mem_isoVecs.1 hv).1 (mem_isoVecs.1 hv).2
    refine ⟨(p, c), ?_, hpc⟩
    rw [Finset.mem_product]
    exact ⟨Finset.mem_univ _, hc⟩
  calc isoVecs.card ≤ _ := Finset.card_le_card h
    _ ≤ ((Finset.univ : Finset (Fin 693)) ×ˢ unitsF4).card := Finset.card_image_le
    _ = 2079 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, card_unitsF4]

open Classical in
theorem card_isoVecs_inter {U : Submodule F4 W} (hU : IsTIPlane U) :
    (isoVecs.filter (· ∈ U)).card = 63 := by
  classical
  have h1 : isoVecs.filter (· ∈ U) = (Finset.univ.filter (· ∈ U)).erase 0 := by
    ext v
    simp only [Finset.mem_filter, mem_isoVecs, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h0, -⟩, hv⟩
      exact ⟨h0, hv⟩
    · rintro ⟨h0, hv⟩
      exact ⟨⟨h0, hU.2 v hv v hv⟩, hv⟩
  have h2 : (Finset.univ.filter (· ∈ U)).card = 64 := by
    have h3 : Nat.card U = (Finset.univ.filter (· ∈ U)).card :=
      Nat.subtype_card _ (fun x => by simp)
    have h4 := Module.natCard_eq_pow_finrank (K := F4) (V := U)
    rw [hU.1, Nat.card_eq_fintype_card (α := F4), F4.card] at h4
    rw [← h3, h4]
    norm_num
  rw [h1, Finset.card_erase_of_mem (by simp), h2]

open Classical in
theorem card_planes_v0_le :
    (tiPlanes.filter (v0 ∈ ·)).card ≤ 27 := by
  classical
  have h : tiPlanes.filter (v0 ∈ ·) ⊆ (Finset.range 27).image planeSub := by
    intro U hU
    rw [Finset.mem_filter, mem_tiPlanes] at hU
    obtain ⟨j, hj, hjU⟩ := exists_planeSub_of_v0 hU.1 hU.2
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, hjU⟩
  calc _ ≤ _ := Finset.card_le_card h
    _ ≤ (Finset.range 27).card := Finset.card_image_le
    _ = 27 := Finset.card_range 27

theorem exists_SU0_v0 {v : W}
    (hv0 : v ≠ 0) (hvi : hermStd v v = 0) :
    ∃ s : SU0, ∃ c : F4, c ≠ 0 ∧
      ((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v0 = c • v := by
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq T46 (ptOf v0 v0_ne_zero hermStd_v0_v0)
    (ptOf v hv0 hvi)
  have htm : (t : Equiv.Perm (Fin 693)) ∈ piSU.range := by rw [range_piSU]; exact t.2
  obtain ⟨s, hs⟩ := htm
  have hs0 := mulVec_ne_zero (s : GL (Fin 6) F4) v0_ne_zero
  have hsi : hermStd (((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v0)
      (((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v0) = 0 := by
    have := hermStd_mulVec (Subgroup.inclusion SU0_le_GU0 s) v0 v0
    rw [hermStd_v0_v0] at this
    exact this
  have key : ptOf _ hs0 hsi = ptOf v hv0 hvi := by
    rw [← ht]
    apply Fin.ext
    change _ = ((t : Equiv.Perm (Fin 693)) (ptOf v0 v0_ne_zero hermStd_v0_v0)).val
    rw [← hs, piSU_apply, ptOf_val]
    obtain ⟨c, hc, hcv⟩ := uVec_ptOf v0 v0_ne_zero hermStd_v0_v0
    rw [hcv, mulVec_smul, ptIdx_smul hc]
  obtain ⟨c, hc, hcv⟩ := (ptOf_eq_ptOf_iff hs0 hsi hv0 hvi).1 key
  refine ⟨s, c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hcv, smul_smul, inv_mul_cancel₀ hc, one_smul]

open Classical in
theorem card_planes_through_le
    {v : W} (hv : v ∈ isoVecs) :
    (tiPlanes.filter (v ∈ ·)).card ≤ 27 := by
  classical
  obtain ⟨hv0, hvi⟩ := mem_isoVecs.1 hv
  obtain ⟨s, c, hc, hsv⟩ := exists_SU0_v0 hv0 hvi
  set g : GU0 := (Subgroup.inclusion SU0_le_GU0 s)⁻¹
  have hmaps : ∀ U ∈ tiPlanes.filter (v ∈ ·),
      mapG (g : GL (Fin 6) F4) U ∈ tiPlanes.filter (v0 ∈ ·) := by
    intro U hU
    rw [Finset.mem_filter, mem_tiPlanes] at hU ⊢
    refine ⟨isTIPlane_mapG hU.1, ?_⟩
    rw [mem_mapG]
    have hinv : (((g : GL (Fin 6) F4))⁻¹ : GL (Fin 6) F4) = (s : GL (Fin 6) F4) := by
      simp [g]
    rw [hinv, hsv]
    exact U.smul_mem c hU.2
  calc (tiPlanes.filter (v ∈ ·)).card ≤ (tiPlanes.filter (v0 ∈ ·)).card :=
        Finset.card_le_card_of_injOn _ hmaps (fun U _ U' _ h => mapG_injective _ h)
    _ ≤ 27 := card_planes_v0_le

theorem sum_le_mul_card {α : Type*} (s : Finset α) (f : α → ℕ) (n : ℕ)
    (h : ∀ x ∈ s, f x ≤ n) : ∑ x ∈ s, f x ≤ n * s.card := by
  calc ∑ x ∈ s, f x ≤ ∑ _x ∈ s, n := Finset.sum_le_sum h
    _ = n * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem sum_eq_mul_card {α : Type*} (s : Finset α) (f : α → ℕ) (n : ℕ)
    (h : ∀ x ∈ s, f x = n) : ∑ x ∈ s, f x = n * s.card := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
theorem card_tiPlanes_le :
    tiPlanes.card ≤ 891 := by
  have h1 : ∑ U ∈ tiPlanes, (isoVecs.filter (· ∈ U)).card =
      ∑ v ∈ isoVecs, (tiPlanes.filter (v ∈ ·)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 := sum_eq_mul_card tiPlanes (fun U => (isoVecs.filter (· ∈ U)).card) 63
    fun U hU => card_isoVecs_inter (mem_tiPlanes.1 hU)
  have h3 := sum_le_mul_card isoVecs (fun v => (tiPlanes.filter (v ∈ ·)).card) 27
    fun v hv => card_planes_through_le hv
  have h4 := card_isoVecs_le
  rw [← h1, h2] at h3
  generalize isoVecs.card = n at h3 h4
  generalize tiPlanes.card = m at h3
  omega

theorem tiPlanes_eq :
    (Finset.range 891).image planeSub = tiPlanes := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro U hU
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hU
    exact mem_tiPlanes.2 (isTIPlane_planeSub (Finset.mem_range.1 hj))
  · rw [Finset.card_image_of_injOn (fun i hi j hj h => planeSub_injective
      (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h), Finset.card_range]
    exact card_tiPlanes_le

theorem exists_planeSub_eq
    {U : Submodule F4 W} (hU : IsTIPlane U) :
    ∃ j < 891, planeSub j = U := by
  classical
  have h : U ∈ (Finset.range 891).image planeSub := by
    rw [tiPlanes_eq]
    exact mem_tiPlanes.2 hU
  obtain ⟨j, hj, hjU⟩ := Finset.mem_image.1 h
  exact ⟨j, Finset.mem_range.1 hj, hjU⟩

end CFSG.LargeExtraspecial.SMod20.Aut
