module

public import Certificates.Data.Kernel.W16Pg
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCheck
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.W16Pg

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw

theorem unpack_getElem! {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  unfold unpack
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem pg5_lt (P i : Nat) : pg 5 (mask 5) P i < 32 := by
  have h : mask 5 = 31 := rfl
  unfold pg
  rw [h]
  exact Nat.lt_succ_of_le Nat.and_le_right

@[expose] def BindE (ET : Nat → Nat) : Prop := ∀ a < 32, eTab[a]! = unpack 32 5 (ET a)

theorem mulE0_eq {ET : Nat → Nat} (hb : BindE ET) {a b : Nat} (ha : a < 32) (hb' : b < 32) :
    mulE0 a b = mulEK ET a b := by
  unfold mulE0 mulEK
  rw [hb a ha, unpack_getElem! hb']

theorem mulC_eq {ET : Nat → Nat} (hb : BindE ET) : mulC = mulCK ET := by
  funext a b
  unfold mulC mulCK
  rw [mulE0_eq hb (Nat.mod_lt a (by norm_num)) (Nat.mod_lt b (by norm_num))]
  have hk : mulEK ET (a % 32) (b % 32) < 32 := pg5_lt _ _
  generalize mulEK ET (a % 32) (b % 32) = k at hk ⊢
  generalize dMul (decD a) (decD b) = i
  unfold ixP ixPK redP redPK
  rw [mulE0_eq hb hk (by decide : eT < 32)]

theorem tableCheck_eq {ET : Nat → Nat} (hb : BindE ET) : tableCheck = tableG (mulCK ET) := by
  rw [← mulC_eq hb]
  unfold tableCheck tableG invC invG
  rfl

theorem genCheck_eq {ET : Nat → Nat} (hb : BindE ET) : genCheck = genG (mulCK ET) := by
  rw [← mulC_eq hb]
  unfold genCheck genG
  rfl

theorem candCheck_eq {ET : Nat → Nat} (hb : BindE ET) : candCheck = candG (mulCK ET) := by
  rw [← mulC_eq hb]
  unfold candCheck candG candSet candSetG commC commG invC invG
  rfl

theorem autCheck_of {ET S : Nat → Nat} (hb : BindE ET) (hS : sgsArr.size = 36)
    (hs : ∀ j < 36, sgsArr[j]! = unpack 128 8 (S j))
    (hlt : ∀ a < 128, ∀ b < 128, mulC a b < 128) (h : autK ET S = true) : autCheck = true := by
  unfold autCheck
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 36 := by rw [← hS]; exact hj
  have e : sgsArr[j]'hj = unpack 128 8 (S j) := by
    have h1 := hs j hj'
    rw [getElem!_pos sgsArr j hj] at h1
    exact h1
  rw [e]
  unfold autK at h
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h j hj'
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨by simp [unpack], fun a ha => ?_⟩, fun a ha b hb' => ?_⟩, fun a ha => ?_⟩
  · rw [unpack_getElem! ha]
    exact h1 a ha
  · rw [unpack_getElem! (hlt a ha b hb'), unpack_getElem! ha, unpack_getElem! hb', mulC_eq hb]
    exact h2 a ha b hb'
  · obtain ⟨b, hb', e⟩ := h3 a ha
    exact ⟨b, hb', by rw [unpack_getElem! hb']; exact e⟩

end CFSG.KC.W16Pg

end
