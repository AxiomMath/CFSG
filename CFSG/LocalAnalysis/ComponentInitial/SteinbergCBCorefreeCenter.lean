module

public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly.ComponentType

variable {G : Type*} [Group G]

def centerOddPartIn (L T : Subgroup G) : Subgroup T where
  carrier := {g | (g : G) ∈ L ∧ (∀ l ∈ L, (g : G) * l = l * g) ∧ Odd (orderOf g)}
  one_mem' := ⟨L.one_mem, fun l _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haL, hac, hao⟩ ⟨hbL, hbc, hbo⟩
    refine ⟨L.mul_mem haL hbL, fun l hl => ?_, ?_⟩
    · simp only [Subgroup.coe_mul, mul_assoc, hbc l hl]
      rw [← mul_assoc, hac l hl, mul_assoc]
    · have hab : Commute a b := Subtype.ext (hac b hbL)
      exact Odd.of_dvd_nat (Nat.odd_mul.2 ⟨hao, hbo⟩)
        (hab.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  inv_mem' := by
    rintro a ⟨haL, hac, hao⟩
    refine ⟨L.inv_mem haL, fun l hl => ?_, by rwa [orderOf_inv]⟩
    have h := hac l hl
    simp only [InvMemClass.coe_inv]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]

theorem corefree_standard_center_two_group [Finite G] {L : Subgroup G}
    (hL : IsStandardSubgroup L) {t : G} (ht : t ∈ Subgroup.centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hO : CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) :
    IsPGroup 2 (Subgroup.center L) := by
  set T := Subgroup.centralizer ({t} : Set G)
  obtain ⟨hTN, hLT, -⟩ := standard_involution_centralizer_normality hL ht ht2
  set K := centerOddPartIn L T
  have hKn : K.Normal := by
    refine ⟨fun k ⟨hkL, hkc, hko⟩ g => ⟨?_, fun l hl => ?_, ?_⟩⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hTN g.2) k).1 hkL
    · have hl' : (g : G)⁻¹ * l * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hTN (T.inv_mem g.2)) l).1 hl
        simpa only [inv_inv] using this
      have h := hkc _ hl'
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      calc (g : G) * k * (g : G)⁻¹ * l
          = g * (k * ((g : G)⁻¹ * l * g)) * (g : G)⁻¹ := by group
        _ = g * ((g : G)⁻¹ * l * g * k) * (g : G)⁻¹ := by rw [h]
        _ = l * (g * k * (g : G)⁻¹) := by group
    · rwa [← SemiconjBy.orderOf_eq g (x := k) (by rw [SemiconjBy]; group)]
  have hKo : Odd (Nat.card K) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
    have hxo := (x.2 : (x : T) ∈ K).2.2
    rw [Subgroup.orderOf_coe, hx] at hxo
    exact (Nat.not_even_iff_odd.2 hxo) even_two
  have hKbot : K = ⊥ := le_bot_iff.1 (hO ▸ le_sSup ⟨hKn, hKo⟩)
  intro z
  have hz1 : ((z : L) : G) ∈ L := (z : L).2
  have hzc : ∀ l ∈ L, ((z : L) : G) * l = l * (z : L) := fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩).symm
  obtain ⟨a, m, hm, hzm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos ((z : L) : G)).ne'
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  set y : T := ⟨((z : L) : G) ^ 2 ^ a, T.pow_mem (hLT hz1) _⟩
  have hyK : y ∈ K := by
    refine ⟨L.pow_mem hz1 _, fun l hl => ?_, ?_⟩
    · exact ((Commute.pow_left (hzc l hl) _) : _)
    · rw [← Subgroup.orderOf_coe]
      change Odd (orderOf (((z : L) : G) ^ 2 ^ a))
      rw [orderOf_pow_of_dvd (by positivity) (hzm ▸ dvd_mul_right _ _), hzm,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
  rw [hKbot, Subgroup.mem_bot] at hyK
  simpa [y] using congrArg Subtype.val hyK

end CFSG.LocalAnalysis.ComponentInitial
