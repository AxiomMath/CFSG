module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltSmall
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv Equiv.Perm
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open CFSG.HardMathSupport.RichardWeiss.Coordinator (ConjSpec)

theorem odd_card_centralizer_alt_five {σ : Perm (Fin 5)} (hodd : Odd (orderOf σ)) (h1 : σ ≠ 1) :
    Odd (Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 5))) := by
  have hc := nat_card_centralizer (g := σ)
  have hk := card_centralizer_inf_alt_cases σ
  have hs := sum_cycleType_le σ
  rw [centralizer_le_alternating_iff] at hk
  generalize Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 5)) = x at hk ⊢
  generalize Nat.card ↥(centralizer {σ}) = C at hk hc
  rw [Nat.odd_iff]
  rcases cycleType_of_odd (by simp) hodd h1 with h | h | h | h | h <;> rw [h] at hk hc hs
  · simp [Nat.factorial] at hc hk
    omega
  · simp [Nat.factorial] at hc
    rcases hk with ⟨-, hk⟩ | ⟨-, hk⟩ <;> omega
  · simp at hs
  · simp at hs
  · simp at hs

variable {A : Type} [Group A] [Finite A]

theorem centralizes_altEight {Y P : Subgroup A} (hPY : P ≤ Y)
    (eY : ↥Y ≃* alternatingGroup (Fin 8)) (eP : ↥P ≃* Perm (Fin 6)) {b : A}
    (hbo : Odd (orderOf b)) (hbY : b ∈ normalizer (Y : Set A))
    (hbP : b ∈ normalizer (P : Set A))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Y, b * y = y * b := by
  obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv_of_bot eP pCore_perm_six_eq_bot
  exact centralizes_alt_eight hPY eY (r := 0) le_rfl (φ.trans (MulEquiv.uniqueProd).symm)
    hbY hbP hbo hW

theorem centralizes_altFive {Y P : Subgroup A} (hPY : P ≤ Y)
    (eY : ↥Y ≃* alternatingGroup (Fin 5)) (eP : ↥P ≃* Perm (Fin 3)) {b : A}
    (hbo : Odd (orderOf b)) (hbY : b ∈ normalizer (Y : Set A))
    (hbP : b ∈ normalizer (P : Set A))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Y, b * y = y * b := by
  classical
  obtain ⟨σ, hσ, -, hσo⟩ := exists_odd_conjSpec (by simp) (by simp) eY hbY hbo
  by_cases hσ1 : σ = 1
  · intro y hy
    have hcm : b * y * b⁻¹ ∈ Y := (mem_normalizer_iff.1 hbY y).1 hy
    have h1 := hσ ⟨y, hy⟩ ⟨_, hcm⟩ rfl
    rw [hσ1, one_mul, inv_one, mul_one] at h1
    have h2 := congrArg Subtype.val (eY.injective (Subtype.ext h1))
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [show b * y * b⁻¹ = y from h2]
  exfalso
  obtain ⟨eP'⟩ := nonempty_quotient_pCore_mulEquiv_of_bot eP pCore_perm_three_eq_bot
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (eP'.symm (swap 0 1))
  have hWtop : (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) ≤ wSup (↥P ⧸ CFSG.pCore 2 ↥P) :=
    le_wSup_of_normal_symThree inferInstance (Subgroup.topEquiv.trans eP')
  obtain ⟨h, hh, hbh⟩ := exists_centralizing_lift hbP hbo w.2 (hW w w.2 (hWtop (mem_top _)))
  have hhτ : eP' (QuotientGroup.mk' (CFSG.pCore 2 ↥P) h) = swap 0 1 := by
    rw [hh]
    show eP' (QuotientGroup.mk w) = _
    rw [hw, MulEquiv.apply_symm_apply]
  have h2 : 2 ∣ orderOf h := by
    have h3 := orderOf_map_dvd (eP'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))) h
    have h4 : orderOf (swap (0 : Fin 3) 1) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq, swap_mul_self]) (by decide)
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at h3
    rwa [hhτ, h4] at h3
  set x : ↥Y := ⟨h, hPY h.2⟩ with hx
  have hbx : (x : A) = b * x * b⁻¹ := by
    show (h : A) = b * h * b⁻¹
    rw [hbh, mul_inv_cancel_right]
  have hxσ := hσ x x hbx
  have hmem : ((eY x : alternatingGroup (Fin 5)) : Perm (Fin 5)) ∈
      centralizer {σ} ⊓ alternatingGroup (Fin 5) := by
    refine ⟨?_, (eY x).2⟩
    show ((eY x : alternatingGroup (Fin 5)) : Perm (Fin 5)) ∈ centralizer {σ}
    rw [mem_centralizer_singleton_iff]
    conv_lhs => rw [hxσ]
    group
  have hodd' : Odd (orderOf ((eY x : alternatingGroup (Fin 5)) : Perm (Fin 5))) := by
    rw [← Subgroup.orderOf_mk _ hmem]
    exact (odd_card_centralizer_alt_five hσo hσ1).of_dvd_nat (orderOf_dvd_natCard _)
  have hord : orderOf ((eY x : alternatingGroup (Fin 5)) : Perm (Fin 5)) = orderOf h := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  rw [hord] at hodd'
  obtain ⟨k, hk⟩ := h2
  obtain ⟨j, hj⟩ := hodd'
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW
