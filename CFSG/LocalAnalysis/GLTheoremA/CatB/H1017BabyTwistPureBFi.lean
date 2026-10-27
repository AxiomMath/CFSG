module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import Certificates.Certificate101708

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance

namespace PureBFi

open CFSG.Sporadic.Fi23 CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Th.Native hiding letters

section Words


private noncomputable abbrev wJ (w : List ℕ) : CFSG.Sporadic.Fi23.J := (w.map (pairG gs)).prod

private noncomputable abbrev yJ (j : ℕ) : CFSG.Sporadic.Fi23.J := wJ bD0Words[j]!

private noncomputable abbrev yF (j : Fin 4) : CFSG.Sporadic.Fi23.J := yJ j

private noncomputable abbrev cJ : CFSG.Sporadic.Fi23.J := wJ bD0Conj

private theorem words_lt {j : ℕ} (hj : j < 4) : ∀ l ∈ bD0Words[j]!, l < letters.size := by
  rw [letters_size, chainWords_size]
  interval_cases j <;> decide

private theorem conj_lt : ∀ l ∈ bD0Conj, l < letters.size := by
  rw [letters_size, chainWords_size]
  decide

private theorem applyWPow_spec {w : List ℕ} (hw : ∀ l ∈ w, l < letters.size) :
    ∀ n, ∀ p < 31671, applyWPow letters w n p = idx 31671 (wJ w ^ n) p
  | 0, p, _ => by
    show p = idx 31671 (wJ w ^ 0) p
    rw [pow_zero, idx_one]
  | n + 1, p, hp => by
    show applyW letters w (applyWPow letters w n p) = _
    rw [applyWPow_spec hw n p hp, applyW_spec w hw _ (idx_lt _ hp), pow_succ', idx_mul]

private theorem idx_word {j : ℕ} (hj : j < 4) {p : ℕ} (hp : p < 31671) :
    applyW letters bD0Words[j]! p = idx 31671 (yJ j) p :=
  applyW_spec _ (words_lt hj) p hp

private theorem applyWPow_word {j : ℕ} (hj : j < 4) (n : ℕ) {p : ℕ} (hp : p < 31671) :
    applyWPow letters bD0Words[j]! n p = idx 31671 (yJ j ^ n) p :=
  applyWPow_spec (words_lt hj) n p hp

private theorem vecProd_eq (a : Fin 4 → ZMod 3) :
    Co3T.vecProd yF a =
      yJ 0 ^ (a 0).val * (yJ 1 ^ (a 1).val * (yJ 2 ^ (a 2).val * yJ 3 ^ (a 3).val)) := by
  unfold Co3T.vecProd
  rw [show List.finRange 4 = [0, 1, 2, 3] by decide]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private theorem vecProd_single : Co3T.vecProd yF (Pi.single 0 (1 : ZMod 3)) = yF 0 := by
  rw [vecProd_eq]
  show yJ 0 ^ 1 * (yJ 1 ^ 0 * (yJ 2 ^ 0 * yJ 3 ^ 0)) = yJ 0
  simp only [pow_one, pow_zero, mul_one]

private theorem idx_vecProd (a : Fin 4 → ZMod 3) {t : ℕ} (ht : t < 31671) :
    bD0Img letters (a 0).val (a 1).val (a 2).val (a 3).val t =
      idx 31671 (Co3T.vecProd yF a) t := by
  have h3 := idx_lt (yJ 3 ^ (a 3).val) ht
  have h2 := idx_lt (yJ 2 ^ (a 2).val) h3
  have h1 := idx_lt (yJ 1 ^ (a 1).val) h2
  unfold bD0Img
  rw [applyWPow_word (j := 3) (by norm_num) _ ht, applyWPow_word (j := 2) (by norm_num) _ h3,
    applyWPow_word (j := 1) (by norm_num) _ h2, applyWPow_word (j := 0) (by norm_num) _ h1,
    vecProd_eq, idx_mul, idx_mul, idx_mul]

end Words

section Check


private theorem bD0_check : bD0CheckL orb letters = true := Certificates.certificate101708


private theorem yF_comm (i j : Fin 4) : Commute (yF i) (yF j) := by
  have h := bD0_check
  unfold bD0CheckL at h
  simp only [Bool.and_eq_true] at h
  show yF i * yF j = yF j * yF i
  refine Fi23Sylow.eq_of_base fun t ht => ?_
  have ht' : t < 31671 := by omega
  have hc := beq_iff_eq.1 (allIn_eq_true.1 (allIn_eq_true.1 (allIn_eq_true.1 h.1.1.1.1 i
    (Nat.zero_le _) i.2) j (Nat.zero_le _) j.2) t (Nat.zero_le _) ht)
  rw [idx_word j.2 ht', idx_word i.2 ht', idx_word i.2 (idx_lt (yJ j) ht'),
    idx_word j.2 (idx_lt (yJ i) ht')] at hc
  rw [idx_mul, idx_mul]
  exact hc

private theorem yF_cube (i : Fin 4) : yF i ^ 3 = 1 := by
  have h := bD0_check
  unfold bD0CheckL at h
  simp only [Bool.and_eq_true] at h
  refine Fi23Sylow.eq_of_base fun t ht => ?_
  have hc := beq_iff_eq.1 (allIn_eq_true.1 (allIn_eq_true.1 h.1.1.1.2 i (Nat.zero_le _) i.2) t
    (Nat.zero_le _) ht)
  rw [applyWPow_word i.2 3 (by omega)] at hc
  rw [idx_one]
  exact hc

private theorem yF_mem (i : Fin 4) {k : ℕ} (hk : k < 2) :
    yF i ∈ Subgroup.centralizer ({kleinD k} : Set J) := by
  have h := bD0_check
  unfold bD0CheckL at h
  simp only [Bool.and_eq_true] at h
  have hp := kleinPts_lt (show k < 3 by omega)
  have hc := beq_iff_eq.1 (allIn_eq_true.1 (allIn_eq_true.1 h.1.1.2 i (Nat.zero_le _) i.2) k
    (Nat.zero_le _) hk)
  rw [idx_word i.2 hp] at hc
  exact Subgroup.mem_centralizer_singleton_iff.2
    (commute_of_conj_J ((CFSG.Sporadic.Fi23.idx_eq_iff hp hp).1 hc))

private theorem vecProd_ne_one {a : Fin 4 → ZMod 3} (ha : a ≠ 0) : Co3T.vecProd yF a ≠ 1 := by
  have h := bD0_check
  unfold bD0CheckL at h
  simp only [Bool.and_eq_true] at h
  have hs : (a 0).val + (a 1).val + (a 2).val + (a 3).val ≠ 0 := fun hs => ha <| funext fun i => by
    have h0 : (a 0).val = 0 ∧ (a 1).val = 0 ∧ (a 2).val = 0 ∧ (a 3).val = 0 := by omega
    rw [Pi.zero_apply, ← ZMod.val_eq_zero]
    fin_cases i
    exacts [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
  have hc := allIn_eq_true.1 (allIn_eq_true.1 (allIn_eq_true.1 (allIn_eq_true.1 h.1.2
    (a 0).val (Nat.zero_le _) (ZMod.val_lt _)) (a 1).val (Nat.zero_le _) (ZMod.val_lt _))
    (a 2).val (Nat.zero_le _) (ZMod.val_lt _)) (a 3).val (Nat.zero_le _) (ZMod.val_lt _)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  rcases hc with hc | hc
  · exact absurd hc hs
  · intro h1
    have hfix : (allIn 0 6 fun t =>
        bD0Img letters (a 0).val (a 1).val (a 2).val (a 3).val t == t) = true :=
      allIn_eq_true.2 fun t _ ht => by
        rw [beq_iff_eq, idx_vecProd a (by omega), h1, idx_one]
    rw [hfix] at hc
    exact Bool.noConfusion hc

private noncomputable def vHom :=
  Co3T.vecProdHom (p := 3) yF (by exact yF_comm) (by exact yF_cube)

private theorem vHom_apply (a : Multiplicative (Fin 4 → ZMod 3)) :
    vHom a = Co3T.vecProd yF (Multiplicative.toAdd a) := rfl

private theorem vHom_injective : Function.Injective vHom :=
  (injective_iff_map_eq_one _).2 fun a ha => by
    by_contra hne
    rw [vHom_apply] at ha
    exact vecProd_ne_one (a := Multiplicative.toAdd a) (fun h0 => hne (toAdd_eq_zero.1 h0)) ha

private theorem vHom_mem (a : Multiplicative (Fin 4 → ZMod 3)) {k : ℕ} (hk : k < 2) :
    vHom a ∈ Subgroup.centralizer ({kleinD k} : Set J) := by
  rw [vHom_apply]
  unfold Co3T.vecProd
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.pow_mem _ (yF_mem i hk) _


private theorem isConj_yF_zero : IsConj (yF 0) (t3 0) := by
  have h := bD0_check
  unfold bD0CheckL at h
  simp only [Bool.and_eq_true] at h
  have hT : Rep 31671 (t3Tabs orb letters)[0]! (t3 0) := rep_t3Tabs 0
  have hcy : cJ * yF 0 = t3 0 * cJ := by
    refine Fi23Sylow.eq_of_base fun t ht => ?_
    have ht' : t < 31671 := by omega
    have hc := beq_iff_eq.1 (allIn_eq_true.1 h.2 t (Nat.zero_le _) ht)
    rw [idx_word (j := 0) (by norm_num) ht', applyW_spec _ conj_lt _ (idx_lt (yJ 0) ht'),
      applyW_spec _ conj_lt _ ht', hT _ (idx_lt cJ ht')] at hc
    rw [idx_mul, idx_mul]
    exact hc
  exact isConj_iff.2 ⟨cJ, by rw [hcy, mul_inv_cancel_right]⟩

end Check

end PureBFi

section Main


theorem exists_twoB_d0 : ∃ t₁ : NativeSporadic.B, BabyInv 1 t₁ ∧ ∃ D₀ : Subgroup NativeSporadic.B,
    D₀ ≤ Subgroup.centralizer ({t₁} : Set NativeSporadic.B) ∧ IsElemAbelian 3 D₀ ∧
    Nat.card D₀ = 3 ^ 4 ∧ ∃ y ∈ D₀, IsConj y (BThreeFi23.phiB (BThreeFi23.t3 0)) := by
  haveI : IsMulCommutative (Multiplicative (Fin 4 → ZMod 3)) := ⟨⟨mul_comm⟩⟩
  refine ⟨BThreeFi23.phiB (kleinD 0) * BThreeFi23.phiB (kleinD 1),
    babyInv_one_map_kleinD_mul BThreeFi23.phiB BThreeFi23.phiB_injective (k := 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide),
    (BThreeFi23.phiB.comp PureBFi.vHom).range, ?_, ⟨inferInstance, ?_⟩, ?_,
    BThreeFi23.phiB (PureBFi.yF 0),
    MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (Pi.single 0 1), ?_⟩, ?_⟩
  ·
    rintro _ ⟨a, rfl⟩
    have e0 := congrArg BThreeFi23.phiB
      (Subgroup.mem_centralizer_singleton_iff.1 (PureBFi.vHom_mem a (k := 0) (by norm_num)))
    have e1 := congrArg BThreeFi23.phiB
      (Subgroup.mem_centralizer_singleton_iff.1 (PureBFi.vHom_mem a (k := 1) (by norm_num)))
    rw [map_mul, map_mul] at e0 e1
    rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← mul_assoc, e0,
      mul_assoc, e1, ← mul_assoc]
  · rintro _ ⟨a, rfl⟩
    have ha : a ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    rw [← map_pow, ha, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective (f := BThreeFi23.phiB.comp PureBFi.vHom)
      (BThreeFi23.phiB_injective.comp PureBFi.vHom_injective)).toEquiv, Co3T.card_vec]
  · rw [MonoidHom.comp_apply, PureBFi.vHom_apply, toAdd_ofAdd, PureBFi.vecProd_single]
  · exact BThreeFi23.phiB.map_isConj PureBFi.isConj_yF_zero

end Main

end CFSG.LocalAnalysis.GLTheoremA.H1017
