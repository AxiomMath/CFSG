module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Y14Check
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3LeviG
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Model
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2U3
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup Matrix CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.UnitarySix.YamadaN2 (SL3 M3 Mat9 gen3 pairOf coefOf pairOf_ne genA
  genABits st3 st3_eq_gen3_or genIdx U3 uEl uMat coe_uEl mem_U3 s01 s01_inv rhoA)

@[expose] def sOne : SL3 :=
  SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1 *
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1 *
    SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1

@[expose] def sTwo : SL3 :=
  SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1 *
    SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) 1 *
    SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1

theorem theta0_sOne : theta0 sOne = yamGen 15 := yamGen15_eq.symm

theorem theta0_sTwo : theta0 sTwo = yamGen 16 := yamGen16_eq.symm

theorem tv01_eq : ∀ c : F4, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) c =
    sOne * SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) c * sOne := by
  decide +kernel

theorem tv12_eq : ∀ c : F4, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) c =
    sTwo * SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) c * sTwo := by
  decide +kernel

theorem tv02_eq : ∀ c : F4, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c =
    sOne * sTwo * SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) c * sTwo *
      sOne := by
  decide +kernel

theorem s01_eq_sOne : s01 = sOne := by
  apply Subtype.ext
  decide +kernel

theorem invTransposeSL_s01 : CFSG.ClassicalInvolution.WeakCT.invTransposeSL 3 s01 = s01 := by
  apply Subtype.ext
  rw [CFSG.ClassicalInvolution.WeakCT.coe_invTransposeSL, s01_inv]
  decide +kernel

theorem uMat_eq : ∀ a b c : F4, uMat a b c =
    Matrix.transvection (0 : Fin 3) 2 (b + a * c) * Matrix.transvection (0 : Fin 3) 1 a *
      Matrix.transvection (1 : Fin 3) 2 c := by
  decide +kernel

theorem uEl_eq (a b c : F4) : uEl a b c = st3 0 2 (b + a * c) * st3 0 1 a * st3 1 2 c := by
  apply Subtype.ext
  rw [st3, st3, st3, stT_eq_transvection _ (by decide : (0 : Fin 3) ≠ 2),
    stT_eq_transvection _ (by decide : (0 : Fin 3) ≠ 1),
    stT_eq_transvection _ (by decide : (1 : Fin 3) ≠ 2), coe_uEl, uMat_eq]
  rfl

theorem transvection_congr3 {a b a' b' : Fin 3} (h : a ≠ b) (h' : a' ≠ b') {c c' : F4}
    (ha : a = a') (hb : b = b') (hc : c = c') :
    SpecialLinearGroup.transvection h c = SpecialLinearGroup.transvection h' c' := by
  subst ha hb hc
  rfl

section Theta

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

variable (e) in
@[expose] noncomputable def theta2G : SL3 →* G :=
  (thetaG e).comp (CFSG.ClassicalInvolution.WeakCT.invTransposeSL 3).toMonoidHom

theorem theta2G_apply (g : SL3) :
    theta2G e g = phiG e (theta0 (CFSG.ClassicalInvolution.WeakCT.invTransposeSL 3 g)) := rfl

variable (e) in
theorem range_theta2G : (theta2G e).range = sK₂ e := by
  rw [theta2G, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
    (CFSG.ClassicalInvolution.WeakCT.invTransposeSL 3).surjective, ← MonoidHom.range_eq_map,
    range_thetaG]

theorem gw_one (k : ℕ) : gw e [k] = phiG e (yamGen k) := by simp [gw, yamWord]

theorem gw_three (a b c : ℕ) :
    gw e [a, b, c] = phiG e (yamGen a) * phiG e (yamGen b) * phiG e (yamGen c) := by
  simp [gw, yamWord, mul_assoc]

theorem gw_five (a b c d f : ℕ) : gw e [a, b, c, d, f] = phiG e (yamGen a) * phiG e (yamGen b) *
    phiG e (yamGen c) * phiG e (yamGen d) * phiG e (yamGen f) := by
  simp [gw, yamWord, mul_assoc]

theorem theta2G_gen3_tv (s : Fin 12) {i j : Fin 3} (hij : i ≠ j) (c : F4)
    (hs : pairOf s = (j, i)) (hc : coefOf s = c) :
    theta2G e (gen3 s) = phiG e (theta0 (SpecialLinearGroup.transvection hij c)) := by
  rw [theta2G_apply, YamadaN2.gen3, stT_eq_transvection _ (pairOf_ne s),
    invTransposeSL_transvectionN]
  exact congrArg (fun x => phiG e (theta0 x)) (transvection_congr3 _ _ (congrArg Prod.snd hs)
    (congrArg Prod.fst hs) (by rw [CharTwo.neg_eq, hc]))

theorem theta2G_gen3_0 : theta2G e (gen3 0) = gw e [0] := by
  rw [theta2G_gen3_tv 0 (i := 1) (j := 0) (by decide) 1 (by decide) (by decide), ← yamGen0_eq,
    gw_one]

theorem theta2G_gen3_1 : theta2G e (gen3 1) = gw e [1] := by
  rw [theta2G_gen3_tv 1 (i := 1) (j := 0) (by decide) F4.ω (by decide) (by decide),
    ← yamGen1_eq, gw_one]

theorem theta2G_gen3_2 : theta2G e (gen3 2) = gw e [5] := by
  rw [theta2G_gen3_tv 2 (i := 2) (j := 0) (by decide) 1 (by decide) (by decide),
    theta0_transvection _ _ (by decide : (2 : Fin 6) ≠ 0) rfl rfl, gw_one]
  rfl

theorem theta2G_gen3_3 : theta2G e (gen3 3) = gw e [6] := by
  rw [theta2G_gen3_tv 3 (i := 2) (j := 0) (by decide) F4.ω (by decide) (by decide),
    theta0_transvection _ _ (by decide : (2 : Fin 6) ≠ 0) rfl rfl, gw_one]
  rfl

theorem theta2G_gen3_4 : theta2G e (gen3 4) = gw e [15, 0, 15] := by
  rw [theta2G_gen3_tv 4 (i := 0) (j := 1) (by decide) 1 (by decide) (by decide), tv01_eq]
  simp only [map_mul]
  rw [theta0_sOne, ← yamGen0_eq, gw_three]

theorem theta2G_gen3_5 : theta2G e (gen3 5) = gw e [15, 1, 15] := by
  rw [theta2G_gen3_tv 5 (i := 0) (j := 1) (by decide) F4.ω (by decide) (by decide), tv01_eq]
  simp only [map_mul]
  rw [theta0_sOne, ← yamGen1_eq, gw_three]

theorem theta2G_gen3_6 : theta2G e (gen3 6) = gw e [2] := by
  rw [theta2G_gen3_tv 6 (i := 2) (j := 1) (by decide) 1 (by decide) (by decide), ← yamGen2_eq,
    gw_one]

theorem theta2G_gen3_7 : theta2G e (gen3 7) = gw e [3] := by
  rw [theta2G_gen3_tv 7 (i := 2) (j := 1) (by decide) F4.ω (by decide) (by decide),
    ← yamGen3_eq, gw_one]

theorem theta2G_gen3_8 : theta2G e (gen3 8) = gw e [15, 16, 2, 16, 15] := by
  rw [theta2G_gen3_tv 8 (i := 0) (j := 2) (by decide) 1 (by decide) (by decide), tv02_eq]
  simp only [map_mul]
  rw [theta0_sOne, theta0_sTwo, ← yamGen2_eq, gw_five]

theorem theta2G_gen3_9 : theta2G e (gen3 9) = gw e [15, 16, 3, 16, 15] := by
  rw [theta2G_gen3_tv 9 (i := 0) (j := 2) (by decide) F4.ω (by decide) (by decide), tv02_eq]
  simp only [map_mul]
  rw [theta0_sOne, theta0_sTwo, ← yamGen3_eq, gw_five]

theorem theta2G_gen3_10 : theta2G e (gen3 10) = gw e [16, 2, 16] := by
  rw [theta2G_gen3_tv 10 (i := 1) (j := 2) (by decide) 1 (by decide) (by decide), tv12_eq]
  simp only [map_mul]
  rw [theta0_sTwo, ← yamGen2_eq, gw_three]

theorem theta2G_gen3_11 : theta2G e (gen3 11) = gw e [16, 3, 16] := by
  rw [theta2G_gen3_tv 11 (i := 1) (j := 2) (by decide) F4.ω (by decide) (by decide), tv12_eq]
  simp only [map_mul]
  rw [theta0_sTwo, ← yamGen3_eq, gw_three]

theorem theta2G_gen3 (s : Fin 12) : theta2G e (gen3 s) = gw e y14V[s.val]! := by
  fin_cases s
  exacts [theta2G_gen3_0, theta2G_gen3_1, theta2G_gen3_2, theta2G_gen3_3, theta2G_gen3_4,
    theta2G_gen3_5, theta2G_gen3_6, theta2G_gen3_7, theta2G_gen3_8, theta2G_gen3_9,
    theta2G_gen3_10, theta2G_gen3_11]

theorem theta2G_s01 : theta2G e s01 = sw e 0 := by
  rw [theta2G_apply, invTransposeSL_s01, s01_eq_sOne, theta0_sOne]
  rfl

end Theta

section Members

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem theta2G_gen3_mem_sA₁ {m : ℕ} (hm : m < 4) : theta2G e (gen3 (Fin.ofNat 12 m)) ∈ sA₁ e := by
  rw [theta2G_gen3]
  exact gw_mem_ch (c := chA1) (by interval_cases m <;> decide)

theorem theta2G_nu_mem_sK₁ {j : ℕ} (hj : j < 4) : theta2G e (gen3 (YamadaN2.nuS j)) ∈ sK₁ e := by
  rw [theta2G_gen3]
  exact gw_mem_ch (c := chK1) (by interval_cases j <;> decide)

theorem gw_mem_sS_letters : ∀ w : List ℕ,
    (∀ k ∈ w, k < 18 ∧ ([k] ∈ chS.gens ∨ [k] ∈ chA1.gens)) → gw e w ∈ sS e
  | [], _ => by rw [gw_nil]; exact one_mem _
  | k :: w, h => by
    rw [show k :: w = [k] ++ w from rfl, gw_append]
    refine mul_mem ?_ (gw_mem_sS_letters w fun j hj => h j (List.mem_cons_of_mem k hj))
    obtain ⟨hk, hk'⟩ := h k List.mem_cons_self
    rcases hk' with hk' | hk'
    · exact gw_mem_ch (c := chS) fun j hj => by rw [List.mem_singleton.1 hj]; exact ⟨hk, hk'⟩
    · exact sA₁_le (gw_mem_ch (c := chA1) fun j hj => by
        rw [List.mem_singleton.1 hj]; exact ⟨hk, hk'⟩)

theorem theta2G_st3_mem {a b : Fin 3} (hab : a ≠ b) (hup : a < b) (c : F4) :
    theta2G e (st3 a b c) ∈ sS e := by
  have hS : ∀ β < 2, theta2G e (gen3 (genIdx a b β)) ∈ sS e := by
    intro β hβ
    rw [theta2G_gen3]
    refine gw_mem_sS_letters _ ?_
    revert a b β
    decide
  rcases st3_eq_gen3_or hab c with h | h | h | h <;> rw [h]
  · rw [map_one]; exact one_mem _
  · exact hS 0 (by norm_num)
  · exact hS 1 (by norm_num)
  · rw [map_mul]; exact mul_mem (hS 0 (by norm_num)) (hS 1 (by norm_num))

theorem theta2G_mem_sS {u : SL3} (hu : u ∈ U3) : theta2G e u ∈ sS e := by
  obtain ⟨a, b, c, rfl⟩ := mem_U3.1 hu
  rw [uEl_eq, map_mul, map_mul]
  exact mul_mem (mul_mem (theta2G_st3_mem (by decide) (by decide) _)
    (theta2G_st3_mem (by decide) (by decide) _)) (theta2G_st3_mem (by decide) (by decide) _)

end Members

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem y14Basis_lt : ∀ i < 9, y14Basis[i]! < 18 := by decide

theorem single_eq_toVec : ∀ i : Fin 9, (Pi.single i 1 : Fin 9 → ZMod 2) = toVec 9 (2 ^ i.val) := by
  decide

theorem iotaWordOf_pow : ∀ i : Fin 9, iotaWordOf (2 ^ i.val) = [y14Basis[i.val]!] := by
  decide

section Iota

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

variable (e) in
@[expose] noncomputable def y14b (i : ℕ) : G := gw e [y14Basis[i]!]

variable (e) in
@[expose] noncomputable def iotaY (u : Fin 9 → ZMod 2) : G :=
  ((List.finRange 9).map fun i => if u i = 1 then y14b e i else 1).prod

theorem y14b_mem {i : ℕ} (hi : i < 9) : y14b e i ∈ sA₂ e :=
  gw_mem_ch (c := chA2) (by interval_cases i <;> decide)

theorem y14b_mul_self {i : ℕ} (hi : i < 9) : y14b e i * y14b e i = 1 := by
  have h := gw_reverse (e := e) (w := [y14Basis[i]!]) (by simpa using y14Basis_lt i hi)
  rw [List.reverse_singleton] at h
  rw [y14b]
  nth_rewrite 2 [h]
  exact mul_inv_cancel _

theorem sA₂_comm {x y : G} (hx : x ∈ sA₂ e) (hy : y ∈ sA₂ e) : x * y = y * x :=
  (mem_centralizer_iff.1 (toG_le_centralizer xComm_spec.1 hx) y hy).symm

theorem prod_map_mul_of_comm {ι : Type*} {A : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (f g : ι → G) (hf : ∀ i, f i ∈ A)
    (hg : ∀ i, g i ∈ A) :
    ∀ l : List ι, (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod
  | [] => by simp
  | i :: l => by
    have hP : (l.map f).prod ∈ A := list_prod_mem fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact hf j
    simp only [List.map_cons, List.prod_cons, mul_assoc]
    rw [prod_map_mul_of_comm hA f g hf hg l]
    congr 1
    rw [← mul_assoc, hA _ (hg i) _ hP, mul_assoc]

theorem ite_add_zmod2 {x : G} (hx : x * x = 1) (a c : ZMod 2) :
    (if a + c = 1 then x else 1) = (if a = 1 then x else 1) * (if c = 1 then x else 1) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    simp [hx, h11, h01]

theorem iotaY_add (u v : Fin 9 → ZMod 2) : iotaY e (u + v) = iotaY e u * iotaY e v := by
  have hm : ∀ (w : Fin 9 → ZMod 2) (i : Fin 9), (if w i = 1 then y14b e i else 1) ∈ sA₂ e := by
    intro w i
    split_ifs
    exacts [y14b_mem i.2, one_mem _]
  rw [iotaY, iotaY, iotaY, ← prod_map_mul_of_comm (fun x hx y hy => sA₂_comm hx hy) _ _ (hm u)
    (hm v)]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [Pi.add_apply]
  exact ite_add_zmod2 (y14b_mul_self i.2) _ _

theorem iotaY_zero : iotaY e 0 = 1 := by
  have h := iotaY_add (e := e) 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem iotaY_mem (u : Fin 9 → ZMod 2) : iotaY e u ∈ sA₂ e :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    split_ifs
    exacts [y14b_mem i.2, one_mem _]

theorem gw_flatMap (F : ℕ → List ℕ) :
    ∀ l : List ℕ, gw e (l.flatMap F) = (l.map fun i => gw e (F i)).prod
  | [] => by simp [gw_nil]
  | a :: l => by rw [List.flatMap_cons, gw_append, gw_flatMap F l, List.map_cons, List.prod_cons]

theorem iotaY_toVec (m : ℕ) : iotaY e (toVec 9 m) = gw e (iotaWordOf m) := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h1 : (fun i : Fin 9 => if toVec 9 m i = 1 then y14b e i else 1) =
      (fun j : ℕ => if m.testBit j then y14b e j else 1) ∘ Fin.val := by
    funext i
    simp only [Function.comp_apply, toVec]
    by_cases hb : m.testBit i = true <;> simp [hb, bz, h01]
  rw [iotaY, h1, ← List.map_map, List.map_coe_finRange_eq_range, iotaWordOf, gw_flatMap]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  split_ifs <;> simp [y14b, gw_nil]

theorem iotaY_single (i : Fin 9) : iotaY e (Pi.single i 1) = y14b e i := by
  rw [single_eq_toVec, iotaY_toVec, iotaWordOf_pow]
  rfl

end Iota

section Inj

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem iotaY_mul_self (u : Fin 9 → ZMod 2) : iotaY e u * iotaY e u = 1 := by
  rw [← iotaY_add, show u + u = 0 from funext fun i => zmod2_add_self (u i), iotaY_zero]

theorem sA₂_subset_range : (sA₂ e : Set G) ⊆ Set.range (iotaY e) := by
  let R : Subgroup G :=
    { carrier := Set.range (iotaY e)
      mul_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u + v, iotaY_add u v⟩
      one_mem' := ⟨0, iotaY_zero⟩
      inv_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u, (inv_eq_of_mul_eq_one_right (iotaY_mul_self u)).symm⟩ }
  have hgens : ∀ w ∈ chA2.gens, ∃ i : Fin 9, [y14Basis[i.val]!] = w := by decide
  have hle : sA₂ e ≤ R := toG_le_of_gens gensOK_chA2 fun w hw => by
    obtain ⟨i, rfl⟩ := hgens w hw
    exact ⟨Pi.single i 1, iotaY_single i⟩
  exact fun x hx => hle hx

theorem iotaY_injective : Function.Injective (iotaY e) := by
  have h1 : Nat.card (sA₂ e) = 512 := by rw [sA₂, card_toG_ch gensOK_chA2, card_chA2]
  have h2 : Nat.card (Fin 9 → ZMod 2) = 512 := by simp [Nat.card_eq_fintype_card]
  have hcard : Nat.card (Fin 9 → ZMod 2) ≤ Nat.card (Set.range (iotaY e)) := by
    rw [h2, ← h1]
    exact Nat.card_mono (Set.finite_range (iotaY e)) sA₂_subset_range
  have hb := (Set.rangeFactorization_surjective (f := iotaY e)).bijective_of_nat_card_le hcard
  intro u v huv
  exact hb.1 (Subtype.ext huv)

theorem iotaY_eq_one {u : Fin 9 → ZMod 2} (h : iotaY e u = 1) : u = 0 :=
  iotaY_injective (h.trans iotaY_zero.symm)

end Inj

theorem y14V_lt : ∀ s : Fin 12, ∀ k ∈ y14V[s.val]!, k < 18 := by decide

theorem iotaWordOf_lt (m : ℕ) : ∀ k ∈ iotaWordOf m, k < 18 := by
  intro k hk
  obtain ⟨i, hi, hk⟩ := List.mem_flatMap.1 hk
  split_ifs at hk
  · rw [List.mem_singleton.1 hk]
    exact y14Basis_lt i (List.mem_range.1 hi)
  · simp at hk

theorem genA_mulVec_single (s : Fin 12) (i : Fin 9) :
    genA s *ᵥ Pi.single i 1 = toVec 9 (colBits s i) := by
  rw [Matrix.mulVec_single_one]
  funext r
  rw [Matrix.col_apply, genA, toMat_apply, toVec, colBits, testBit_bitsOf]
  simp

section Equivariance

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem gw_y14_conj (s : Fin 12) {i : ℕ} (hi : i < 9) :
    gw e (cjW y14V[s.val]! [y14Basis[i]!]) = gw e (iotaWordOf (colBits s i)) := by
  have hc : ∀ k ∈ cjW y14V[s.val]! [y14Basis[i]!], k < 18 := by
    intro k hk
    simp only [cjW, List.mem_append, List.mem_reverse, List.mem_singleton] at hk
    rcases hk with (hk | rfl) | hk
    · exact y14V_lt s k hk
    · exact y14Basis_lt i hi
    · exact y14V_lt s k hk
  refine gw_eq_gw hc (iotaWordOf_lt _) (eq_of_eqA (rep_wA tabs_check _ hc)
    (rep_wA tabs_check _ (iotaWordOf_lt _)) ?_)
  have h := y14_check
  unfold y14Check at h
  simp only [List.all_eq_true, List.mem_finRange, List.mem_range, true_implies] at h
  exact h s i hi

theorem theta2G_conj_single (s : Fin 12) (i : Fin 9) :
    theta2G e (gen3 s) * iotaY e (Pi.single i 1) * (theta2G e (gen3 s))⁻¹ =
      iotaY e (genA s *ᵥ Pi.single i 1) := by
  rw [theta2G_gen3, iotaY_single, y14b, ← gw_cjW (y14V_lt s), gw_y14_conj s i.2,
    genA_mulVec_single, iotaY_toVec]

theorem theta2G_conj_of_single {g : SL3}
    (h : ∀ i : Fin 9, theta2G e g * iotaY e (Pi.single i 1) * (theta2G e g)⁻¹ =
      iotaY e (rhoA g *ᵥ Pi.single i 1)) (u : Fin 9 → ZMod 2) :
    theta2G e g * iotaY e u * (theta2G e g)⁻¹ = iotaY e (rhoA g *ᵥ u) := by
  have key := Finset.sum_induction (s := Finset.univ) (fun i => Pi.single i (u i))
    (fun v => theta2G e g * iotaY e v * (theta2G e g)⁻¹ = iotaY e (rhoA g *ᵥ v))
    (fun a b ha hb => by rw [iotaY_add, mulVec_add, iotaY_add, ← ha, ← hb]; group)
    (by rw [iotaY_zero, mulVec_zero, iotaY_zero]; group)
    (fun i _ => by
      rcases zmod2_cases (u i) with h0 | h1
      · rw [h0, Pi.single_zero, iotaY_zero, mulVec_zero, iotaY_zero]; group
      · rw [h1]; exact h i)
  rwa [Finset.univ_sum_single] at key

theorem theta2G_conj_one (u : Fin 9 → ZMod 2) :
    theta2G e 1 * iotaY e u * (theta2G e 1)⁻¹ = iotaY e (rhoA 1 *ᵥ u) := by
  rw [map_one, map_one, one_mulVec]
  group

theorem theta2G_conj_mul {g h : SL3}
    (hg : ∀ u, theta2G e g * iotaY e u * (theta2G e g)⁻¹ = iotaY e (rhoA g *ᵥ u))
    (hh : ∀ u, theta2G e h * iotaY e u * (theta2G e h)⁻¹ = iotaY e (rhoA h *ᵥ u))
    (u : Fin 9 → ZMod 2) :
    theta2G e (g * h) * iotaY e u * (theta2G e (g * h))⁻¹ = iotaY e (rhoA (g * h) *ᵥ u) := by
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← hg, ← hh]
  group

theorem theta2G_conj_iotaY (g : SL3) (u : Fin 9 → ZMod 2) :
    theta2G e g * iotaY e u * (theta2G e g)⁻¹ = iotaY e (rhoA g *ᵥ u) := by
  have hgen : ∀ s u, theta2G e (gen3 s) * iotaY e u * (theta2G e (gen3 s))⁻¹ =
      iotaY e (rhoA (gen3 s) *ᵥ u) :=
    fun s => theta2G_conj_of_single fun i => by
      rw [YamadaN2.rhoA_gen3]
      exact theta2G_conj_single s i
  have hst : ∀ (a b : Fin 3) (c : F4) u, theta2G e (st3 a b c) * iotaY e u *
      (theta2G e (st3 a b c))⁻¹ = iotaY e (rhoA (st3 a b c) *ᵥ u) := by
    intro a b c
    by_cases hab : a = b
    · subst hab
      rw [st3, stT_diag]
      exact theta2G_conj_one
    · rcases st3_eq_gen3_or hab c with h | h | h | h <;> rw [h]
      · exact theta2G_conj_one
      · exact hgen _
      · exact hgen _
      · exact theta2G_conj_mul (hgen _) (hgen _)
  revert u
  have hg : g ∈ Subgroup.closure (Set.range fun p : Fin 3 × Fin 3 × F4 =>
      stT (F := F4) (m := 2) (by norm_num) p.1 p.2.1 p.2.2) := by
    rw [closure_stT]
    exact Subgroup.mem_top g
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨p, rfl⟩ | ⟨p, hp⟩
    · exact hst _ _ _
    · have : x = st3 p.1 p.2.1 p.2.2 := by
        rw [← inv_inv x, ← hp, YamadaN2.st3_inv]
      rw [this]
      exact hst _ _ _
  | one => exact theta2G_conj_one
  | mul x y _ _ hx hy => exact theta2G_conj_mul hx hy

end Equivariance

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
