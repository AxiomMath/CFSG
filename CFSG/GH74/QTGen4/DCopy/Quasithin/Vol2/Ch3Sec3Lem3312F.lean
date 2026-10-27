module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3312A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312F

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace L3312

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Hyp3312

variable {T M L D Y : Subgroup G} (H : Hyp3312 G T M L D Y)

include H

theorem j1_case_F4 (h14 : Stmt3_3_14_F4) (h37 : A37ForSQTK) (h128 : Lemma128One)
    (hJ1 : FactJ1Norm3312) {K : Subgroup G} (hK : K ∈ cComp (Y ⊔ T ⊔ D)) (hYK : Y ≤ K)
    (hHK : Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G))
    (hc : A312C15 (modO2Image (Y ⊔ T ⊔ D) Y) (modO2Image (Y ⊔ T ⊔ D) K))
    (htype : Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      InducesInnerOn T Y := by
  set X := Y ⊔ T ⊔ D with hX
  obtain ⟨⟨eY⟩, ⟨eK⟩⟩ := hc
  have hKH : K ≤ X := le_of_mem_cComp hK
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨e⟩ := Hyp3312.modO2_equiv (T := T) (D := D) (Y := Y)
    have hc60 : Nat.card ↥(modO2Image X Y) = 60 := by
      rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hdvd : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣ 60 := by
      rw [← Nat.card_congr e.toEquiv, ← hc60]
      exact Subgroup.card_quotient_dvd_card _
    apply htype.isPSL_two_two_two_of_card
    rcases htype.card with ⟨n, hn, hcn⟩ | hcn | hcn
    · rw [hcn] at hdvd ⊢
      have h4 := Type3312R.three_le_pow hn
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hn2 : n = 2 := by
        by_contra hne
        have h8 : 8 ≤ 2 ^ n :=
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h63 : 8 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Type3312R.le_sq_sub_one h8
        have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by simpa using h63)
        omega
      subst hn2
      norm_num
    · rw [hcn] at hdvd
      norm_num at hdvd
    · rw [hcn] at hdvd
      norm_num at hdvd
  · obtain ⟨f⟩ := modO2_mulEquiv hK
    exact ⟨f.trans eK⟩
  ·
    have : (modO2Image X K).Normal := modO2Image_normal hKH hHK
    let ψ : (↥X ⧸ CFSG.pCore 2 ↥X) →* MulAut ↥(modO2Image X K) := MulAut.conjNormal
    have hInn : (MulAut.conj : ↥(modO2Image X K) →* MulAut ↥(modO2Image X K)).range ≤
        ψ.range := by
      rintro _ ⟨n, rfl⟩
      exact ⟨_, MulAut.conjNormal_val⟩
    have hS := isSylowTwoOf_map_range ψ H.isSylowTwoOf_modO2Image_T
    have hYK' : modO2Image X Y ≤ modO2Image X K := Subgroup.map_mono fun y hy => hYK hy
    have hSB : (modO2Image X T).map ψ ≤ MulAction.stabilizer (MulAut ↥(modO2Image X K))
        ((modO2Image X Y).subgroupOf (modO2Image X K)) := by
      rintro _ ⟨tb, htb, rfl⟩
      obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb
      refine (conjNormal_mem_stabilizer_iff hYK' _).mpr ?_
      exact mk_mem_normalizer_modO2Image htX (H.le_normalizer_Y_F4 h14 h37 h128 ht)
    have hB5 : IsAlt 5 ↥((modO2Image X Y).subgroupOf (modO2Image X K)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hYK').trans eY⟩
    have hJ := (hJ1 _ ⟨eK⟩ ψ.range _ _ hInn hS hB5 hSB).1
    refine Hyp3312.inducesInnerOn_of (D := D) (H.le_normalizer_Y_F4 h14 h37 h128) fun t htX ht => ?_
    obtain ⟨b, hb, hbc⟩ := hJ (ψ (QuotientGroup.mk ⟨t, htX⟩))
      ⟨QuotientGroup.mk ⟨t, htX⟩, ⟨⟨t, htX⟩, ht, rfl⟩, rfl⟩
    have hbY : (b : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ modO2Image X Y := hb
    obtain ⟨⟨y₀, hy₀X⟩, hy₀, hy₀b⟩ := hbY
    refine ⟨y₀, hy₀X, hy₀, fun x hxX hx => ?_⟩
    have hxY : (QuotientGroup.mk ⟨x, hxX⟩ : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ modO2Image X Y :=
      ⟨⟨x, hxX⟩, hx, rfl⟩
    have h1 := congrArg Subtype.val (hbc ⟨_, hYK' hxY⟩ hxY)
    simp only [ψ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1, ← hy₀b]
    rfl

end Hyp3312

end L3312

end CFSG.Quasithin.H13
