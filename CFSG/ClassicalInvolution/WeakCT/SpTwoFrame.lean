module

public import CFSG.ClassicalInvolution.WeakCT.SpTwoAgree
import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.ClassicalInvolution.WeakCT.FieldTwo
public import CFSG.ClassicalInvolution.WeakCT.SpPair

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.Timmesfeld
open scoped MatrixGroups

variable {F : Type} [Field F] {X : Type} [Group X]

private def spTwoUp {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨k.val, by have := k.isLt; omega⟩

private theorem exists_frame_sp_two_restrict {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2)
    (hfin : Finite F) {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ ρ : Fin (n - 1) → SL(2, F) →* X,
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U (spTwoUp k)) ∧
      ∀ i j : Fin (n - 1), j.val + 1 = i.val → ∃ ψ : SL(3, F) →* X,
        ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j := by
  classical
  have hcomm' : ∀ i j : Fin (n - 1), i ≠ j → ¬ edgeDown (n - 1) i j →
      ¬ edgeDown (n - 1) j i →
      ∀ x ∈ U (spTwoUp i), ∀ y ∈ U (spTwoUp j), x * y = y * x := by
    intro i j hne h1 h2 x hx y hy
    simp only [edgeDown] at h1 h2
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm (spTwoUp i) (spTwoUp j) (by simp only [spTwoUp]; omega) x hx y hy
    · exact (hcomm (spTwoUp j) (spTwoUp i) (by simp only [spTwoUp]; omega) y hy x hx).symm
  have hpair' : ∀ i j : Fin (n - 1), edgeDown (n - 1) i j →
      ∃ W, LinearBlockStandardPair F W (U (spTwoUp i)) (U (spTwoUp j)) := by
    intro i j hij
    simp only [edgeDown] at hij
    obtain ⟨W, hW⟩ := hpair (spTwoUp j) (spTwoUp i) (by simpa only [spTwoUp] using hij)
      (by simp only [spTwoUp]; have := i.isLt; omega)
    exact ⟨W, hW.symm⟩
  obtain ⟨ρ, hρ, hψ⟩ :=
    @exists_frame_of_tree_two F _ hfin X _ (n - 1) (edgeDown (n - 1)) (parentDown (n - 1))
      (depthDown (n - 1)) _ hF (rootedTree_edgeDown (n := n - 1) (by omega))
      ⟨⟨n - 3, by omega⟩, Or.inl (by simp only [edgeDown]; omega)⟩
      (fun k => U (spTwoUp k)) hcomm' hpair'
  exact ⟨ρ, hρ, hψ⟩

private theorem exists_adjust_sp_two_of_agree (hF : Nat.card F = 2)
    {Ua Ub Uc : Subgroup X} {θd : StatedSp 2 F →* X} {ψ : SL(3, F) →* X}
    {ρb ρc : SL(2, F) →* X}
    (hθd : θd.ker ≤ Subgroup.center (StatedSp 2 F))
    (h1 : (θd.comp (spBlock F 1)).range = Ua)
    (h0 : (θd.comp (spBlock F 0)).range = Ub)
    (hψ0 : ψ.comp (blk F 0) = ρb) (hψ1 : ψ.comp (blk F 1) = ρc)
    (hρb : Function.Injective ρb) (hrb : ρb.range = Ub) (hrc : ρc.range = Uc)
    (hca : ∀ x ∈ Ua, ∀ y ∈ Uc, x * y = y * x) :
    ∃ θ' : StatedSp 2 F →* X, θ'.comp (spBlock F 0) = ρb ∧
      Function.Injective (θ'.comp (spBlock F 1)) ∧ (θ'.comp (spBlock F 1)).range = Ua := by
  have hnt : ∃ g : SL(3, F), ψ g ≠ 1 := by
    refine ⟨blk F 0 (tv 0 1 (1 : F)), fun h => ?_⟩
    have h2 : ρb (tv 0 1 (1 : F)) = 1 := by
      rw [← DFunLike.congr_fun hψ0 (tv 0 1 (1 : F))]
      exact h
    exact tv01_ne_one (hρb (by simpa using h2))
  have hker : ψ.ker ≤ Subgroup.center SL(3, F) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) hnt
  have hM : (θd.comp (spBlock F 0)).range = (Bs F 0).map ψ := by
    rw [map_Bs, hψ0, hrb, h0]
  have hac : ∀ x ∈ (θd.comp (spBlock F (0 : Fin 2).rev)).range,
      ∀ y ∈ (Bs F (0 : Fin 2).rev).map ψ, x * y = y * x := by
    intro x hx y hy
    rw [show (0 : Fin 2).rev = 1 from rfl, h1] at hx
    rw [show (0 : Fin 2).rev = 1 from rfl, map_Bs, hψ1, hrc] at hy
    exact hca x hx y hy
  have hw : ρb (weylTwo F) = θd (spBlock F 0 (weylTwo F)) := by
    rw [← DFunLike.congr_fun hψ0 (weylTwo F)]
    exact (weylTwo_agree_sp_sl3 hF 0 0 hθd hker hM hac).symm
  obtain ⟨θ', -, hθ'0, hθ'⟩ :=
    exists_adjust_sp_two hF 0 hθd hρb (by rw [hrb, h0]) hw
  exact ⟨θ', hθ'0, (hθ' 1).1, (hθ' 1).2.trans h1⟩

private theorem exists_frame_sp_two_assembly {n : ℕ} (hn : 3 ≤ n) {U : Fin n → Subgroup X}
    {ρ' : Fin (n - 1) → SL(2, F) →* X}
    (hρ' : ∀ k, Function.Injective (ρ' k) ∧ (ρ' k).range = U (spTwoUp k))
    (hψ' : ∀ i j : Fin (n - 1), j.val + 1 = i.val → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j)
    {a : Fin n} (ha : a.val + 1 = n) {b' : Fin (n - 1)} (hb' : b'.val + 2 = n)
    {θ' : StatedSp 2 F →* X} (hθ'0 : θ'.comp (spBlock F 0) = ρ' b')
    (hinj : Function.Injective (θ'.comp (spBlock F 1)))
    (hrange : (θ'.comp (spBlock F 1)).range = U a) :
    ∃ ρ : Fin n → SL(2, F) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      (∀ i j : Fin n, j.val + 1 = i.val → i.val + 1 < n → ∃ ψ : SL(3, F) →* X,
        ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) ∧
      ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n → ∃ ψ : StatedSp 2 F →* X,
        ψ.comp (spBlock F 1) = ρ i ∧ ψ.comp (spBlock F 0) = ρ j := by
  classical
  let ρ : Fin n → SL(2, F) →* X :=
    fun k => if h : k.val < n - 1 then ρ' ⟨k.val, h⟩ else θ'.comp (spBlock F 1)
  have hρeq : ∀ k (h : k.val < n - 1), ρ k = ρ' ⟨k.val, h⟩ := fun k h => dif_pos h
  have hρeq' : ∀ k, ¬ k.val < n - 1 → ρ k = θ'.comp (spBlock F 1) := fun k h => dif_neg h
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k.val < n - 1
    · rw [hρeq k hk]
      exact ⟨(hρ' _).1, by rw [(hρ' _).2]; exact congrArg U (Fin.ext rfl)⟩
    · have hka : k = a := Fin.ext (by omega)
      rw [hka, hρeq' a (by omega), hrange]
      exact ⟨hinj, rfl⟩
  · intro i j hij hi
    have hi' : i.val < n - 1 := by omega
    have hj' : j.val < n - 1 := by omega
    obtain ⟨ψ, h0, h1⟩ := hψ' ⟨i.val, hi'⟩ ⟨j.val, hj'⟩ (by
      show (⟨j.val, hj'⟩ : Fin (n - 1)).val + 1 = (⟨i.val, hi'⟩ : Fin (n - 1)).val
      omega)
    exact ⟨ψ, by rw [h0, hρeq i hi'], by rw [h1, hρeq j hj']⟩
  · intro i j hi hj
    have hj' : j.val < n - 1 := by omega
    have hfin : (⟨j.val, hj'⟩ : Fin (n - 1)) = b' := Fin.ext (by
      show j.val = b'.val
      omega)
    exact ⟨θ', by rw [hρeq' i (by omega)],
      by rw [hθ'0, hρeq j hj', hfin]⟩

theorem exists_frame_of_chain_sp_two (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ ρ : Fin n → SL(2, F) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      (∀ i j : Fin n, j.val + 1 = i.val → i.val + 1 < n → ∃ ψ : SL(3, F) →* X,
        ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) ∧
      ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n → ∃ ψ : StatedSp 2 F →* X,
        ψ.comp (spBlock F 1) = ρ i ∧ ψ.comp (spBlock F 0) = ρ j := by
  classical
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨ρ', hρ', hψ'⟩ := exists_frame_sp_two_restrict hn hF hfin hcomm hpair
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val + 1 = n :=
    ⟨⟨n - 1, by omega⟩, by show n - 1 + 1 = n; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val + 2 = n :=
    ⟨⟨n - 2, by omega⟩, by show n - 2 + 2 = n; omega⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c.val + 1 = b.val :=
    ⟨⟨n - 3, by omega⟩, by show n - 3 + 1 = b.val; omega⟩
  let b' : Fin (n - 1) := ⟨b.val, by omega⟩
  let c' : Fin (n - 1) := ⟨c.val, by omega⟩
  have hb'up : spTwoUp b' = b := Fin.ext rfl
  have hc'up : spTwoUp c' = c := Fin.ext rfl
  have hbc' : c'.val + 1 = b'.val := by simp only [b', c']; omega
  have hb'2 : b'.val + 2 = n := by simpa only [b', Fin.val_mk] using hb
  obtain ⟨W, hW⟩ := hsp a b ha hb
  obtain ⟨θd, -, hkerd, -, -, hr1, hr0⟩ := pair_normalize_sp hW
  obtain ⟨ψ, hψ0, hψ1⟩ := hψ' b' c' hbc'
  have hrb : (ρ' b').range = U b := by rw [(hρ' b').2, hb'up]
  have hrc : (ρ' c').range = U c := by rw [(hρ' c').2, hc'up]
  have hca : ∀ x ∈ U a, ∀ y ∈ U c, x * y = y * x := by
    intro x hx y hy
    exact (hcomm c a (by omega) y hy x hx).symm
  obtain ⟨θ', hθ'0, hinj, hrange⟩ := exists_adjust_sp_two_of_agree hF hkerd hr1 hr0
    hψ0 hψ1 (hρ' b').1 hrb hrc hca
  exact exists_frame_sp_two_assembly hn hρ' hψ' ha hb'2 hθ'0 hinj hrange

end CFSG.ClassicalInvolution.WeakCT
