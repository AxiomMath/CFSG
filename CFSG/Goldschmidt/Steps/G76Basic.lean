module

import CFSG.Goldschmidt.Steps.StrongEmb
import CFSG.Goldschmidt.Steps.G74Basic
import CFSG.Walter.Bender1970
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.Walter.SimpleCase

public section

namespace CFSG.Goldschmidt

namespace G76

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem not_isStronglyEmbeddedOrder (hG : GoldSetting G S A) (M : Subgroup G) :
    ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  intro hM
  have := hG.isSimpleGroup
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 (even_iff_two_dvd.mp hM.2.1)
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hG.ne_bot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hG.elem.2 a haA) ha1'
  obtain ⟨-, -, hconj⟩ := N9 G M hM
  obtain ⟨x, hx⟩ := isConj_iff.mp (hconj (t : G) a ht2 ha2)
  refine G74.not_forall_centralizer_le hG (H := M.map (MulAut.conj x).toMonoidHom) ?_ ?_
  · intro htop
    apply hM.1
    rw [eq_top_iff]
    intro g _
    have hg : x * g * x⁻¹ ∈ M.map (MulAut.conj x).toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := hg
    have : m = g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmg
      exact mul_left_cancel (mul_right_cancel hmg)
    rwa [← this]
  · intro c hc hc1 g hg
    have hc2 : orderOf c = 2 := orderOf_eq_prime (hG.elem.2 c hc) hc1
    have hac : a * c = c * a :=
      congrArg Subtype.val (hG.elem.1.is_comm.comm (⟨a, haA⟩ : A) ⟨c, hc⟩)
    have htx : (t : G) = x⁻¹ * a * x := by rw [← hx]; group
    have hc'M : x⁻¹ * c * x ∈ M := by
      apply centralizer_le_of_stronglyEmbedded hM ht2 t.2
      rw [Subgroup.mem_centralizer_singleton_iff, htx]
      calc x⁻¹ * c * x * (x⁻¹ * a * x) = x⁻¹ * (c * a) * x := by group
        _ = x⁻¹ * (a * c) * x := by rw [hac]
        _ = x⁻¹ * a * x * (x⁻¹ * c * x) := by group
    have hc'2 : orderOf (x⁻¹ * c * x) = 2 := by
      rw [← hc2]
      exact (SemiconjBy.orderOf_eq x⁻¹ (by
        change x⁻¹ * c = x⁻¹ * c * x * x⁻¹
        group)).symm
    have hgM : x⁻¹ * g * x ∈ M := by
      apply centralizer_le_of_stronglyEmbedded hM hc'2 hc'M
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc x⁻¹ * g * x * (x⁻¹ * c * x) = x⁻¹ * (g * c) * x := by group
        _ = x⁻¹ * (c * g) * x := by rw [hgc]
        _ = x⁻¹ * c * x * (x⁻¹ * g * x) := by group
    refine ⟨x⁻¹ * g * x, hgM, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem three_le_twoRank (hG : GoldSetting G S A) (h8 : Nat.card A = 8) :
    3 ≤ CFSG.Open.twoRank G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨A, le_top, hG.elem, by rw [h8]; norm_num⟩
  rintro k ⟨E, -, -, hE⟩
  calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    _ = Nat.card E := hE.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group E

theorem isTypeJR_of_isMulCommutative
    (hG : GoldSetting G S A) (h8 : Nat.card A = 8)
    (hS : IsMulCommutative (S : Subgroup G)) : CFSG.Walter.IsTypeJR G := by
  have := hG.isSimpleGroup
  have hab : CFSG.Walter.HasAbelianSylowTwo G := CFSG.Walter.hasAbelianSylowTwo_of_sylow S hS
  have hstar : ∀ H : Subgroup G, H ≠ ⊤ → CFSG.Walter.IsAStar H := fun H _ =>
    CFSG.Walter.isAStar_of_hasAbelianSylowTwo
      (CFSG.Walter.simpleCaseHyp_of_benderHyp CFSG.Walter.benderHyp) (hab.subgroup H)
  rcases CFSG.Walter.benderHyp G hG.isSimpleGroup hG.nonabelian hab (three_le_twoRank hG h8)
    hstar with h | ⟨M, hM⟩
  · exact h
  · exact absurd hM (not_isStronglyEmbeddedOrder hG M)

theorem le_centralizer_of_odd_index (hG : GoldSetting G S A)
    (hodd : Odd ((Subgroup.centralizer (A : Set G)).subgroupOf
      (Subgroup.normalizer (A : Set G))).index) :
    (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (A : Set G) with hN
  set C := (Subgroup.centralizer (A : Set G)).subgroupOf N with hC
  have hSN : (S : Subgroup G) ≤ N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hG.le).mp
      (normal_subgroupOf_of_stronglyClosed hG.le hG.closed)
  have hCn : C.Normal := by
    rw [hC]
    exact Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G)) |>.mpr
      (GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup A)
  intro s hs
  set s' : N := ⟨s, hSN hs⟩ with hs'
  have h1 : s' ^ C.index ∈ C := Subgroup.pow_index_mem C s'
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  have hk' : s' ^ 2 ^ k = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa using this)
  have hcop : Nat.Coprime C.index (orderOf s') :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h2 : s' ∈ C := by
    rw [← hm]
    exact C.pow_mem h1 m
  exact h2

end G76

end CFSG.Goldschmidt
