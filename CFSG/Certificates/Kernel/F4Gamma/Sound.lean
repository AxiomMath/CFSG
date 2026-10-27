module

public import Certificates.Data.Kernel.F4Gamma
public import CFSG.Certificates.Kernel.F4RankSound
public import CFSG.Certificates.Kernel.F4SaltSound
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Basic
import all CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.KC.F4Gamma

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.KC.F4Rank CFSG.KC.F4Syl3 Module
open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L41
  CFSG.RankThree.PartTwo.Sec21.FF81.F4

theorem allN_true {n : ℕ} {p : ℕ → Bool} (h : allN n p = true) : ∀ m, m < n → p m = true := by
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    simp only [allN, Bool.and_eq_true] at h
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact ih h.2 m hm
    · exact h.1

section Flag

variable {K : Type} [Field K]

variable (K) in
noncomputable def flagE (B j : ℕ) : Submodule K (RootModule ReeTag.F4.tag K) :=
  Submodule.span K ((fun i => bitVec K (col B i)) '' {i | i < j})

theorem flagE_zero (B : ℕ) : flagE K B 0 = ⊥ := by
  simp [flagE]

theorem flagE_mono (B : ℕ) {j j' : ℕ} (h : j ≤ j') : flagE K B j ≤ flagE K B j' :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_flagE (B : ℕ) {i j : ℕ} (h : i < j) : bitVec K (col B i) ∈ flagE K B j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem flagE_top {B : ℕ} (h : basisChk B = true) : flagE K B 52 = ⊤ := by
  have hli := echelon_li (K := K) _ h
  have h1 := finrank_span_eq_card hli
  have hle : Submodule.span K (Set.range fun i : Fin ((List.range 52).map (colR B)).length =>
      bitVec K (((List.range 52).map (colR B)).get i)) ≤ flagE K B 52 := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : (i : ℕ) < 52 := by simpa using i.2
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, colR_eq]
    exact mem_flagE B hi
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  rw [finrank_rootModule_F4]
  have h2 := Submodule.finrank_mono hle
  rw [h1] at h2
  simpa using h2

variable (K) in
def FlagP (B : ℕ) (f : Module.End K (RootModule ReeTag.F4.tag K)) : Prop :=
  ∀ j < 52, ∀ v ∈ flagE K B (j + 1), f v - v ∈ flagE K B j

theorem FlagP.mapsTo {B : ℕ} {f : Module.End K (RootModule ReeTag.F4.tag K)} (hf : FlagP K B f) :
    ∀ j ≤ 52, ∀ v ∈ flagE K B j, f v ∈ flagE K B j
  | 0, _, v, hv => by
    rw [flagE_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    exact Submodule.zero_mem _
  | j + 1, hj, v, hv => by
    have e : f v = (f v - v) + v := by abel
    rw [e]
    exact add_mem (flagE_mono B (Nat.le_succ j) (hf j (by omega) v hv)) hv

theorem flagP_one (B : ℕ) : FlagP K B 1 := by
  intro j _ v _
  rw [Module.End.one_apply, sub_self]
  exact Submodule.zero_mem _

theorem flagP_mul {B : ℕ} {f g : Module.End K (RootModule ReeTag.F4.tag K)} (hf : FlagP K B f)
    (hg : FlagP K B g) : FlagP K B (f * g) := by
  intro j hj v hv
  have e : (f * g) v - v = (f (g v) - g v) + (g v - v) := by
    rw [Module.End.mul_apply]
    abel
  rw [e]
  exact add_mem (hf j hj _ (hg.mapsTo _ (by omega) v hv)) (hg j hj v hv)

theorem flagP_nilp {B : ℕ} {f : Module.End K (RootModule ReeTag.F4.tag K)} (hf : FlagP K B f) :
    ∀ n ≤ 52, ∀ v ∈ flagE K B n, ((f - 1) ^ n) v = 0
  | 0, _, v, hv => by
    rw [flagE_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  | n + 1, hn, v, hv => by
    rw [pow_succ, Module.End.mul_apply]
    refine flagP_nilp hf n (by omega) _ ?_
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact hf n (by omega) v hv

theorem algebraMap_end_injective :
    Function.Injective (algebraMap K (Module.End K (RootModule ReeTag.F4.tag K))) := by
  intro a b hab
  have h := congrArg (fun f => posCoord ReeTag.F4.tag K 0 (f (posVec ReeTag.F4.tag K 0))) hab
  have h0 : (0 : ℕ) < dim ReeTag.F4.tag := by rw [dim_F4]; norm_num
  simpa only [Module.algebraMap_end_apply, map_smul, posCoord_posVec h0, ↓reduceIte,
    smul_eq_mul, mul_one] using h

theorem flagP_pow64 [CharP K 2] {B : ℕ} (hB : basisChk B = true)
    {f : Module.End K (RootModule ReeTag.F4.tag K)} (hf : FlagP K B f) : f ^ 64 = 1 := by
  have : CharP (Module.End K (RootModule ReeTag.F4.tag K)) 2 :=
    charP_of_injective_algebraMap algebraMap_end_injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h52 : (f - 1) ^ 52 = 0 := LinearMap.ext fun v =>
    flagP_nilp hf 52 le_rfl v (by rw [flagE_top hB]; exact Submodule.mem_top)
  have h64 : (f - 1) ^ (2 ^ 6) = 0 := by
    rw [show (2 : ℕ) ^ 6 = 12 + 52 by norm_num, pow_add, h52, mul_zero]
  have h := add_pow_char_pow_of_commute (R := Module.End K (RootModule ReeTag.F4.tag K)) 2 6
    (Commute.one_right (f - 1))
  rw [h64, zero_add, one_pow] at h
  have e : f - 1 + 1 = f := by abel
  rw [e] at h
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
  exact h

theorem toEnd_bitVec_eq (B c : ℕ) :
    toEnd K B (bitVec K c) = ∑ p ∈ Finset.range 52, bitK K (c.testBit p) • bitVec K (col B p) := by
  rw [bitVec, toEnd_sum_smul_posVec]
  exact Finset.sum_congr rfl fun p _ => by rw [colVec_eq]

theorem bitVec_mem_flagE (B : ℕ) {c i : ℕ} (hc : c >>> i = 0) :
    toEnd K B (bitVec K c) ∈ flagE K B i := by
  rw [toEnd_bitVec_eq]
  refine Submodule.sum_mem _ fun p _ => ?_
  by_cases hp : p < i
  · exact Submodule.smul_mem _ _ (mem_flagE B hp)
  · have h0 : c.testBit p = false := by
      have h1 := congrArg (fun n => n.testBit (p - i)) hc
      simp only [Nat.testBit_shiftRight, Nat.zero_testBit] at h1
      rwa [show i + (p - i) = p by omega] at h1
    rw [h0]
    simp [bitK]

theorem flagP_of_flagChk [CharP K 2] {B G C : ℕ} (h : flagChk B G C = true) :
    FlagP K B (toEnd K G) := by
  have hrow := allN_true h
  intro j hj v hv
  suffices hle : flagE K B (j + 1) ≤ (flagE K B j).comap (toEnd K G - 1) by
    have := hle hv
    rwa [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at this
  rw [flagE, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < j + 1 := hi
  have hr := hrow i (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  rw [SetLike.mem_coe, Submodule.mem_comap, toEnd_sub_one_bitVec, ← colR_eq, hr.1,
    ← toEnd_bitVec]
  exact flagE_mono B (by omega) (bitVec_mem_flagE B hr.2)

variable (K) in
noncomputable def formR (r : ℕ) : RootModule ReeTag.F4.tag K →ₗ[K] K :=
  ∑ p ∈ Finset.range 52, bitK K (r.testBit p) • posCoord ReeTag.F4.tag K p

theorem cast_xor [CharP K 2] {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    ((a ^^^ b : ℕ) : K) = a + b := by
  interval_cases a <;> interval_cases b <;> simp [Nat.xor_self, CharTwo.add_self_eq_zero]

theorem dotAux_spec [CharP K 2] (r v : ℕ) : ∀ n, dotAux r v n < 2 ∧
    ((dotAux r v n : ℕ) : K) = ∑ p ∈ Finset.range n, bitK K (r.testBit p && v.testBit p)
  | 0 => ⟨by change (0 : ℕ) < 2; norm_num, by change ((0 : ℕ) : K) = _; simp⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := dotAux_spec r v n
    have e : dotAux r v (n + 1) = (r &&& v) >>> n % 2 ^^^ dotAux r v n := rfl
    have hb : (r &&& v) >>> n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    refine ⟨?_, ?_⟩
    · rw [e]
      have := Nat.xor_lt_two_pow (n := 1) (by simpa using hb) (by simpa using h1)
      simpa using this
    · rw [e, cast_xor hb h1, h2, Finset.sum_range_succ, bit_eq, Nat.testBit_land, add_comm]
      congr 1
      cases r.testBit n && v.testBit n <;> simp [bitK]

theorem formR_bitVec [CharP K 2] (r v : ℕ) : formR K r (bitVec K v) = (dotR r v : K) := by
  rw [dotR, (dotAux_spec r v 52).2, formR, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [LinearMap.smul_apply, posCoord_bitVec (Finset.mem_range.1 hp), smul_eq_mul, bitK_and]

theorem formR_col [CharP K 2] {r B j₀ : ℕ} (h : coordChk r B j₀ = true) {j : ℕ} (hj : j < 52) :
    formR K r (bitVec K (col B j)) = if j = j₀ then 1 else 0 := by
  have hr := beq_iff_eq.1 (allN_true h j hj)
  rw [formR_bitVec, ← colR_eq, hr]
  by_cases e : j = j₀
  · subst e
    simp
  · rw [if_neg e, beq_false_of_ne e]
    simp

theorem formR_kill [CharP K 2] {r B a : ℕ} (h : coordChk r B a = true) (ha : a ≤ 52) :
    ∀ u ∈ flagE K B a, formR K r u = 0 := by
  have hle : flagE K B a ≤ LinearMap.ker (formR K r) := by
    rw [flagE, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < a := hi
    rw [SetLike.mem_coe, LinearMap.mem_ker, formR_col h (by omega), if_neg (by omega)]
  exact fun u hu => hle hu

theorem formR_decomp [CharP K 2] {r B a : ℕ} (h : coordChk r B a = true) (ha : a < 52) :
    ∀ u ∈ flagE K B (a + 1), u - formR K r u • bitVec K (col B a) ∈ flagE K B a := by
  have hle : flagE K B (a + 1) ≤ (flagE K B a).comap
      (LinearMap.id - (formR K r).smulRight (bitVec K (col B a))) := by
    rw [flagE, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < a + 1 := hi
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, formR_col h (by omega)]
    by_cases e : i = a
    · subst e
      rw [if_pos rfl, one_smul, sub_self]
      exact Submodule.zero_mem _
    · rw [if_neg e, zero_smul, sub_zero]
      exact mem_flagE B (by omega)
  intro u hu
  have := hle hu
  rwa [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply] at this

set_option maxRecDepth 20000 in
theorem formR_flag_one [CharP K 2] {r B a : ℕ} (h : coordChk r B a = true) (ha : a < 52)
    {f : Module.End K (RootModule ReeTag.F4.tag K)} (hf : FlagP K B f) :
    formR K r (f (bitVec K (col B a))) = 1 := by
  have hfa : f (bitVec K (col B a)) - bitVec K (col B a) ∈ flagE K B a :=
    hf a ha _ (mem_flagE B (by omega))
  have h0 := formR_kill h ha.le _ hfa
  have e1 := formR_col (K := K) h ha
  rw [if_pos rfl] at e1
  have h0' : formR K r (f (bitVec K (col B a))) - formR K r (bitVec K (col B a)) = 0 :=
    ((formR K r).map_sub _ _).symm.trans h0
  rw [e1] at h0'
  exact sub_eq_zero.1 h0'

theorem form_mul [CharP K 2] {r B a b : ℕ} (h : coordChk r B a = true) (hb : a + 1 = b)
    (ha : a + 1 < 52)
    {f g : Module.End K (RootModule ReeTag.F4.tag K)} (hf : FlagP K B f) (hg : FlagP K B g) :
    formR K r (f (g (bitVec K (col B b)))) =
      formR K r (f (bitVec K (col B b))) + formR K r (g (bitVec K (col B b))) := by
  subst hb
  have hu : g (bitVec K (col B (a + 1))) - bitVec K (col B (a + 1)) ∈ flagE K B (a + 1) :=
    hg (a + 1) ha _ (mem_flagE B (Nat.lt_succ_self _))
  have hw := formR_decomp h (by omega) _ hu
  have h1 := formR_flag_one h (by omega) hf
  have h2 := formR_kill h (by omega) _ (hf.mapsTo a (by omega) _ hw)
  have h3 : formR K r (g (bitVec K (col B (a + 1))) - bitVec K (col B (a + 1))) =
      formR K r (g (bitVec K (col B (a + 1)))) := by
    rw [map_sub, formR_col h ha, if_neg (by omega), sub_zero]
  set u := g (bitVec K (col B (a + 1))) - bitVec K (col B (a + 1)) with hu_def
  set w := u - formR K r u • bitVec K (col B a) with hw_def
  have hgu : g (bitVec K (col B (a + 1))) =
      bitVec K (col B (a + 1)) + (formR K r u • bitVec K (col B a) + w) := by
    rw [hw_def, hu_def]
    abel
  calc formR K r (f (g (bitVec K (col B (a + 1))))) =
        formR K r (f (bitVec K (col B (a + 1)))) +
          (formR K r u * formR K r (f (bitVec K (col B a))) + formR K r (f w)) := by
        conv_lhs => rw [hgu]
        simp only [map_add, map_smul, smul_eq_mul]
    _ = _ := by rw [h1, h2, h3, mul_one, add_zero]

theorem form_sq [CharP K 2] {l m B : ℕ} (hl : coordChk l B 48 = true)
    (hm : coordChk m B 49 = true) {f : Module.End K (RootModule ReeTag.F4.tag K)}
    (hf : FlagP K B f) (h2 : f * f = 1) :
    formR K l (f (bitVec K (col B 49))) * formR K m (f (bitVec K (col B 50))) = 0 := by
  have hu : f (bitVec K (col B 50)) - bitVec K (col B 50) ∈ flagE K B 50 :=
    hf 50 (by norm_num) _ (mem_flagE B (by norm_num))
  have hw := formR_decomp hm (by norm_num) _ hu
  have hw' := formR_decomp hl (by norm_num) _ hw
  have h48 := formR_flag_one hl (by norm_num) hf
  have hz := formR_kill hl (by norm_num) _ (hf.mapsTo 48 (by norm_num) _ hw')
  have hmu : formR K m (f (bitVec K (col B 50)) - bitVec K (col B 50)) =
      formR K m (f (bitVec K (col B 50))) := by
    rw [map_sub, formR_col hm (by norm_num), if_neg (by norm_num), sub_zero]
  set u := f (bitVec K (col B 50)) - bitVec K (col B 50) with hu_def
  set w := u - formR K m u • bitVec K (col B 49) with hw_def
  set w' := w - formR K l w • bitVec K (col B 48) with hw'_def
  have hlw : formR K l w = formR K l (f (bitVec K (col B 50))) := by
    rw [hw_def, hu_def, map_sub, map_sub, map_smul, formR_col hl (by norm_num : 49 < 52),
      formR_col hl (by norm_num : 50 < 52), if_neg (by norm_num), if_neg (by norm_num),
      smul_eq_mul, mul_zero, sub_zero, sub_zero]
  have he : f (bitVec K (col B 50)) = bitVec K (col B 50) +
      (formR K m u • bitVec K (col B 49) + (formR K l w • bitVec K (col B 48) + w')) := by
    rw [hw'_def, hw_def, hu_def]
    abel
  have hff : f (f (bitVec K (col B 50))) = bitVec K (col B 50) := by
    rw [← Module.End.mul_apply, h2, Module.End.one_apply]
  have key : formR K l (f (f (bitVec K (col B 50)))) = formR K l (f (bitVec K (col B 50))) +
      (formR K m u * formR K l (f (bitVec K (col B 49))) +
        (formR K l w * formR K l (f (bitVec K (col B 48))) + formR K l (f w'))) := by
    conv_lhs => rw [he]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hff, formR_col hl (by norm_num), if_neg (by norm_num), h48, hz, hmu, hlw] at key
  have h2A := CharTwo.add_self_eq_zero (formR K l (f (bitVec K (col B 50))))
  linear_combination -key - h2A

noncomputable abbrev endOf (x : adjointGroup ReeTag.F4.tag K) :
    Module.End K (RootModule ReeTag.F4.tag K) :=
  ((x : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K))

theorem endOf_mul (x y : adjointGroup ReeTag.F4.tag K) : endOf (x * y) = endOf x * endOf y := rfl

theorem endOf_one : endOf (1 : adjointGroup ReeTag.F4.tag K) = 1 := rfl

theorem endOf_injective {x y : adjointGroup ReeTag.F4.tag K} (h : endOf x = endOf y) : x = y :=
  Subtype.ext (Units.ext h)

theorem pow64_of_flagP [CharP K 2] {B : ℕ} (hB : basisChk B = true)
    {x : adjointGroup ReeTag.F4.tag K} (hx : FlagP K B (endOf x)) : x ^ 64 = 1 := by
  apply endOf_injective
  change (((x ^ 64 : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) :
    Module.End K (RootModule ReeTag.F4.tag K)) = 1
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  exact flagP_pow64 hB hx

theorem flagP_pow {B : ℕ} {x : adjointGroup ReeTag.F4.tag K} (hx : FlagP K B (endOf x)) :
    ∀ n, FlagP K B (endOf (x ^ n))
  | 0 => by
    rw [pow_zero]
    exact flagP_one B
  | n + 1 => by
    rw [pow_succ, endOf_mul]
    exact flagP_mul (flagP_pow hx n) hx

theorem flagP_closure [CharP K 2] {B : ℕ} (hB : basisChk B = true)
    {S : Set (adjointGroup ReeTag.F4.tag K)} (hS : ∀ s ∈ S, FlagP K B (endOf s)) :
    ∀ x ∈ Subgroup.closure S, FlagP K B (endOf x) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact flagP_one B
  | mul x y _ _ hx hy => exact flagP_mul hx hy
  | inv x _ hx =>
    have e : x⁻¹ = x ^ 63 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact pow64_of_flagP hB hx)
    rw [e]
    exact flagP_pow hx 63

theorem endOf_inv_apply (x : adjointGroup ReeTag.F4.tag K) (v : RootModule ReeTag.F4.tag K) :
    endOf x (endOf x⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← endOf_mul, mul_inv_cancel, endOf_one, Module.End.one_apply]

theorem form_inv [CharP K 2] {r B a b : ℕ} (h : coordChk r B a = true) (hb : a + 1 = b)
    (ha : a + 1 < 52)
    {x : adjointGroup ReeTag.F4.tag K} (hx : FlagP K B (endOf x))
    (hx' : FlagP K B (endOf x⁻¹)) :
    formR K r (endOf x⁻¹ (bitVec K (col B b))) =
      -formR K r (endOf x (bitVec K (col B b))) := by
  subst hb
  have h0 := form_mul h rfl ha hx hx'
  rw [endOf_inv_apply, formR_col h ha, if_neg (by omega)] at h0
  linear_combination h0 + (formR K r (endOf x⁻¹ (bitVec K (col B (a + 1)))) +
    formR K r (endOf x (bitVec K (col B (a + 1))))) * (CharTwo.two_eq_zero : (2 : K) = 0)

set_option maxRecDepth 20000 in
theorem invClosure_ne_of_flag [CharP K 2] {B l m : ℕ} (hB : basisChk B = true)
    (hl : coordChk l B 48 = true) (hm : coordChk m B 49 = true)
    {S : Set (adjointGroup ReeTag.F4.tag K)}
    (hS : ∀ s ∈ S, FlagP K B (endOf s) ∧ formR K l (endOf s (bitVec K (col B 49))) =
      formR K m (endOf s (bitVec K (col B 50))))
    {s₀ : adjointGroup ReeTag.F4.tag K} (hs₀ : s₀ ∈ S)
    (h₁ : formR K l (endOf s₀ (bitVec K (col B 49))) = 1) :
    invClosure (Subgroup.closure S) ≠ Subgroup.closure S := by
  have hF := flagP_closure hB fun s hs => (hS s hs).1
  have hmulχ : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S,
      formR K l (endOf (x * y) (bitVec K (col B 49))) =
        formR K l (endOf x (bitVec K (col B 49))) + formR K l (endOf y (bitVec K (col B 49))) :=
    fun x hx y hy => by
      rw [endOf_mul, Module.End.mul_apply]
      exact form_mul hl (rfl : 48 + 1 = 49) (by norm_num) (hF x hx) (hF y hy)
  have hmulγ : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S,
      formR K m (endOf (x * y) (bitVec K (col B 50))) =
        formR K m (endOf x (bitVec K (col B 50))) + formR K m (endOf y (bitVec K (col B 50))) :=
    fun x hx y hy => by
      rw [endOf_mul, Module.End.mul_apply]
      exact form_mul hm (rfl : 49 + 1 = 50) (by norm_num) (hF x hx) (hF y hy)
  have hχ1 : formR K l (endOf (1 : adjointGroup ReeTag.F4.tag K) (bitVec K (col B 49))) = 0 := by
    rw [endOf_one, Module.End.one_apply, formR_col hl (by norm_num), if_neg (by norm_num)]
  have hγ1 : formR K m (endOf (1 : adjointGroup ReeTag.F4.tag K) (bitVec K (col B 50))) = 0 := by
    rw [endOf_one, Module.End.one_apply, formR_col hm (by norm_num), if_neg (by norm_num)]
  have heq : ∀ x ∈ Subgroup.closure S, formR K l (endOf x (bitVec K (col B 49))) =
      formR K m (endOf x (bitVec K (col B 50))) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact (hS s hs).2
    | one => rw [hχ1, hγ1]
    | mul x y hx hy ihx ihy => rw [hmulχ x hx y hy, hmulγ x hx y hy, ihx, ihy]
    | inv x hx ih =>
      rw [form_inv hl (rfl : 48 + 1 = 49) (by norm_num) (hF x hx) (hF _ (inv_mem hx)),
        form_inv hm (rfl : 49 + 1 = 50) (by norm_num) (hF x hx) (hF _ (inv_mem hx)), ih]
  have hinv : ∀ x ∈ invClosure (Subgroup.closure S), x ∈ Subgroup.closure S ∧
      formR K l (endOf x (bitVec K (col B 49))) = 0 := by
    intro x hx
    unfold invClosure at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxV, hx2⟩ := hx
      refine ⟨hxV, ?_⟩
      have hx2' : x ^ 2 = 1 := by
        rw [← hx2]
        exact pow_orderOf_eq_one x
      have hsq : endOf x * endOf x = 1 := by rw [← endOf_mul, ← pow_two, hx2', endOf_one]
      have h0 := form_sq hl hm (hF x hxV) hsq
      rw [← heq x hxV] at h0
      exact mul_self_eq_zero.1 h0
    | one =>
      refine ⟨one_mem _, ?_⟩
      rw [hχ1]
    | mul x y _ _ hx hy =>
      refine ⟨mul_mem hx.1 hy.1, ?_⟩
      rw [hmulχ x hx.1 y hy.1, hx.2, hy.2, add_zero]
    | inv x _ hx =>
      refine ⟨inv_mem hx.1, ?_⟩
      rw [form_inv hl (rfl : 48 + 1 = 49) (by norm_num) (hF x hx.1) (hF _ (inv_mem hx.1)), hx.2,
        neg_zero]
  intro he
  have hs := hinv s₀ (he.symm ▸ Subgroup.subset_closure hs₀)
  exact one_ne_zero (h₁.symm.trans hs.2)

theorem bitVec_inj {u v : ℕ} (hu : u < 2 ^ 52) (hv : v < 2 ^ 52)
    (h : bitVec K u = bitVec K v) : u = v := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 52
  · have h1 := congrArg (posCoord ReeTag.F4.tag K p) h
    rw [posCoord_bitVec hp, posCoord_bitVec hp] at h1
    exact bitK_injective h1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem orbRow_spec {gs : List ℕ} {w₀ P R i : ℕ} (h : orbRow gs w₀ P R i = true) :
    ((fldW R 32 i / 16384 = 0 ∧ fldW P 64 i = w₀ ∨
      (fldW R 32 (fldW R 32 i % 4096) / 16384 < fldW R 32 i / 16384 ∧
        fldW R 32 i / 4096 % 4 < gs.length) ∧
        vapp (gs.getD (fldW R 32 i / 4096 % 4) 0) (fldW P 64 (fldW R 32 i % 4096)) =
          fldW P 64 i) ∧
    (i = 0 ∨ fldW P 64 (i - 1) < fldW P 64 i)) ∧ fldW P 64 i < 2 ^ 52 := by
  simpa only [orbRow, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq] using h

theorem orbit_points [CharP K 2] {Q : adjointGroup ReeTag.F4.tag K → Prop} (hQ1 : Q 1)
    (hQ : ∀ s y, Q s → Q y → Q (s * y)) {gs : List ℕ} {w₀ P R n : ℕ}
    (hgs : ∀ k < gs.length, ∃ s, Q s ∧ HasBits K s (gs.getD k 0))
    (h : orbChk gs w₀ P R n = true) :
    (∀ i < n, ∃ x, Q x ∧ endOf x (bitVec K w₀) = bitVec K (fldW P 64 i)) ∧
      (∀ j < n, ∀ i < j, fldW P 64 i < fldW P 64 j) ∧ (∀ i < n, fldW P 64 i < 2 ^ 52) := by
  have hrow : ∀ i < n, orbRow gs w₀ P R i = true ∧ fldW R 32 i % 4096 < n := by
    intro i hi
    have h1 := allN_true h i hi
    simp only [Bool.and_eq_true, Nat.blt_eq] at h1
    exact h1
  have reach : ∀ d, ∀ i < n, fldW R 32 i / 16384 = d → ∃ x, Q x ∧
      endOf x (bitVec K w₀) = bitVec K (fldW P 64 i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      rcases (orbRow_spec (hrow i hi).1).1.1 with ⟨-, hv⟩ | ⟨⟨hlt, hk⟩, hv⟩
      · exact ⟨1, hQ1, by rw [endOf_one, Module.End.one_apply, hv]⟩
      · obtain ⟨y, hy, hyv⟩ := ih _ (hd ▸ hlt) _ (hrow i hi).2 rfl
        obtain ⟨s, hs, hsb⟩ := hgs _ hk
        refine ⟨s * y, hQ s y hs hy, ?_⟩
        rw [endOf_mul, Module.End.mul_apply, hyv]
        change ((s : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) _ = _
        rw [hsb, toEnd_bitVec, hv]
  refine ⟨fun i hi => reach _ i hi rfl, ?_, fun i hi => (orbRow_spec (hrow i hi).1).2⟩
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    rcases (orbRow_spec (hrow (j + 1) hj).1).1.2 with h1 | h1
    · omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact lt_trans (ih (by omega) i hi) h1
      · exact h1

theorem eq_of_mono {n : ℕ} {P : ℕ → ℕ} (h : ∀ j < n, ∀ i < j, P i < P j) {i j : ℕ} (hi : i < n)
    (hj : j < n) (e : P i = P j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact absurd e (ne_of_lt (h j hj i hl))
  · exact absurd e (ne_of_gt (h i hi j hl))

theorem card_ge_of_orbits [CharP K 2] [Finite (adjointGroup ReeTag.F4.tag K)]
    {S : Set (adjointGroup ReeTag.F4.tag K)} {gs hs : List ℕ} {w₁ P₁ R₁ n₁ w₂ P₂ R₂ n₂ : ℕ}
    (hgs : ∀ k < gs.length, ∃ s ∈ Subgroup.closure S, HasBits K s (gs.getD k 0))
    (hhs : ∀ k < hs.length, ∃ s, (s ∈ Subgroup.closure S ∧
      endOf s (bitVec K w₁) = bitVec K w₁) ∧ HasBits K s (hs.getD k 0))
    (h₁ : orbChk gs w₁ P₁ R₁ n₁ = true) (h₂ : orbChk hs w₂ P₂ R₂ n₂ = true) :
    n₁ * n₂ ≤ Nat.card (Subgroup.closure S) := by
  obtain ⟨r1, m1, -⟩ := orbit_points (Q := (· ∈ Subgroup.closure S)) (one_mem _)
    (fun _ _ => mul_mem) (fun k hk => by
      obtain ⟨s, hs, hb⟩ := hgs k hk
      exact ⟨s, hs, hb⟩) h₁
  obtain ⟨r2, m2, b2⟩ := orbit_points
    (Q := fun x => x ∈ Subgroup.closure S ∧ endOf x (bitVec K w₁) = bitVec K w₁)
    ⟨one_mem _, by rw [endOf_one, Module.End.one_apply]⟩
    (fun s y hs hy => ⟨mul_mem hs.1 hy.1, by rw [endOf_mul, Module.End.mul_apply, hy.2, hs.2]⟩)
    hhs h₂
  obtain ⟨-, -, b1⟩ := orbit_points (Q := (· ∈ Subgroup.closure S)) (one_mem _)
    (fun _ _ => mul_mem) (fun k hk => by
      obtain ⟨s, hs, hb⟩ := hgs k hk
      exact ⟨s, hs, hb⟩) h₁
  choose x hx hxv using fun i : Fin n₁ => r1 i i.2
  choose y hy hyv using fun j : Fin n₂ => r2 j j.2
  let f : Fin n₁ × Fin n₂ → Subgroup.closure S := fun p =>
    ⟨x p.1 * y p.2, mul_mem (hx p.1) (hy p.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have e : x i * y j = x i' * y j' := congrArg Subtype.val hij
    have e1 := congrArg (fun z => endOf z (bitVec K w₁)) e
    simp only [endOf_mul, Module.End.mul_apply, (hy j).2, (hy j').2, hxv] at e1
    have hi : i = i' := Fin.ext (eq_of_mono m1 i.2 i'.2 (bitVec_inj (b1 _ i.2) (b1 _ i'.2) e1))
    subst hi
    have e2 := congrArg (fun z => endOf z (bitVec K w₂)) (mul_left_cancel e)
    simp only [hyv] at e2
    have hj : j = j' := Fin.ext (eq_of_mono m2 j.2 j'.2 (bitVec_inj (b2 _ j.2) (b2 _ j'.2) e2))
    rw [hj]
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem hasBitsS_prodS [CharP K 2] {gs : List ℕ} {g : ℕ → adjointGroup ReeTag.F4.tag K} :
    ∀ w : List ℕ, (∀ k ∈ w, HasBits K (g k) (gs.getD k 0)) →
      CFSG.KC.F4Salt.HasBitsS K (w.map g).prod (prodS gs w)
  | [], _ => by
    rw [prodS, List.foldr_nil, List.map_nil, List.prod_nil]
    exact CFSG.KC.F4Salt.hasBitsS_one
  | k :: w, h => by
    rw [List.map_cons, List.prod_cons, prodS, List.foldr_cons, ← prodS,
      CFSG.KC.F4Salt.strictN_eq]
    exact (CFSG.KC.F4Salt.hasBitsS_saltOf (h k (List.mem_cons_self ..))).mul
      (hasBitsS_prodS w fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))

end Flag

theorem card_eq_of_pow64 {G : Type*} [Group G] [Finite G] {V Γ : Subgroup G} (hVΓ : V ≤ Γ)
    (hΓ : Nat.card Γ = 2 ^ 12 * 8775) (h64 : ∀ x ∈ V, x ^ 64 = 1) (h4096 : 4096 ≤ Nat.card V) :
    Nat.card V = 4096 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 V := fun x => ⟨6, Subtype.ext (by simpa using h64 x x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hd := Subgroup.card_dvd_of_le hVΓ
  rw [hn, hΓ] at hd
  have hd' : 2 ^ n ∣ 2 ^ 12 :=
    (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 8775)).dvd_of_dvd_mul_right hd
  have hn12 : n ≤ 12 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd'
  have hn12' : 12 ≤ n := by
    by_contra hlt
    have h1 : 2 ^ n ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at h4096
    omega
  rw [hn, show n = 12 by omega]
  norm_num

end CFSG.KC.F4Gamma

end
