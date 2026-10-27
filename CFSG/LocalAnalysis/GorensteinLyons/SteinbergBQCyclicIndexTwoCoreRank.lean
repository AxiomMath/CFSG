module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCIndexTwoDichotomy
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGWidthOneTwoRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped IsMulCommutative

namespace SteinbergBQ

@[expose] def mulAutPermNeOne (Q : Type*) [Group Q] : MulAut Q →* Equiv.Perm {x : Q // x ≠ 1} where
  toFun α := α.toEquiv.subtypeEquiv fun _ => α.map_ne_one_iff.symm
  map_one' := Equiv.ext fun _ => rfl
  map_mul' _ _ := Equiv.ext fun _ => rfl

theorem mulAutPermNeOne_injective (Q : Type*) [Group Q] :
    Function.Injective (mulAutPermNeOne Q) := by
  intro α β h
  ext x
  by_cases hx : x = 1
  · rw [hx, map_one, map_one]
  · exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)

theorem card_mulAut_dvd_six {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) :
    Nat.card (MulAut Q) ∣ 6 := by
  classical
  have h3 : Nat.card {x : Q // x ≠ 1} = 3 := by
    have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : Q))
    rw [Finite.card_option, hQ] at h
    omega
  have h6 : (3 : ℕ).factorial = 6 := rfl
  have h := Subgroup.card_dvd_of_injective (mulAutPermNeOne Q) (mulAutPermNeOne_injective Q)
  rw [Nat.card_perm, h3, h6] at h
  exact h

end SteinbergBQ

theorem characteristic_two_cyclic_index_two_core_rank_bound {H : Type*} [Group H] [Finite H]
    (hH : CFSG.IsCharacteristicP 2 H) (A : Subgroup (CFSG.pCore 2 H)) (hA : IsCyclic A)
    (hAQ : A.index ≤ 2) : CFSG.pRank 2 H ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hC : centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H := hH
  have hrank : (∀ E : Subgroup H, IsElementaryAbelian 2 E → Nat.card E ≤ 4) →
      CFSG.pRank 2 H ≤ 2 := by
    intro h
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    exact h E ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hE)
  have hker : ∀ g : H, MulAut.conjNormal (H := CFSG.pCore 2 H) g = 1 → g ∈ CFSG.pCore 2 H := by
    intro g hg
    refine hC (mem_centralizer_iff.2 fun q hq => ?_)
    have h1 := congrArg (fun α : MulAut (CFSG.pCore 2 H) => ((α ⟨q, hq⟩ : CFSG.pCore 2 H) : H)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc q * g = g * q * g⁻¹ * g := by rw [h1]
      _ = g * q := by group
  by_cases hAut : IsPGroup 2 (MulAut (CFSG.pCore 2 H))
  ·
    have hkerp : IsPGroup 2 (MulAut.conjNormal (H := CFSG.pCore 2 H)).ker :=
      hQ2.to_le fun g hg => hker g (MonoidHom.mem_ker.1 hg)
    have hH2 : IsPGroup 2 H := by
      have h1 := (hAut.to_subgroup ⊤).comap_of_ker_isPGroup _ hkerp
      rw [comap_top] at h1
      exact h1.of_equiv Subgroup.topEquiv
    have hQtop : CFSG.pCore 2 H = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [CFSG.pCore]
      exact le_sSup ⟨inferInstance, hH2.to_subgroup ⊤⟩
    have hQi : (CFSG.pCore 2 H).index = 1 := by rw [hQtop]; exact index_top
    have hcyc : IsCyclic (A.map (CFSG.pCore 2 H).subtype) :=
      isCyclic_of_surjective _ ((CFSG.pCore 2 H).subtype.subgroupMap_surjective A)
    refine CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound hcyc ?_
    rw [index_map_subtype, hQi, mul_one]
    exact hAQ
  obtain ⟨hxor, -⟩ := cyclic_index_two_odd_automorphism_dichotomy hQ2 hAQ hAut
  rcases hxor with ⟨⟨-, h4⟩, -⟩ | ⟨⟨hES, h8, -⟩, -⟩
  swap
  · exact (extraspecial_width_one_two_rank_at_most_two hH hES h8).1
  have hAutdvd : Nat.card (MulAut (CFSG.pCore 2 H)) ∣ 6 := SteinbergBQ.card_mulAut_dvd_six h4
  refine hrank fun E hE => ?_
  have hE2 : IsPGroup 2 E := CFSG.IsElementaryAbelian.isPGroup 2 E
  set ψ : E →* MulAut (CFSG.pCore 2 H) :=
    (MulAut.conjNormal (H := CFSG.pCore 2 H)).comp E.subtype with hψ
  have hrange : Nat.card ψ.range ≤ 2 := by
    have h1 : Nat.card ψ.range ∣ Nat.card (MulAut (CFSG.pCore 2 H)) :=
      Subgroup.card_subgroup_dvd_card _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
      (hE2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
    exact SteinbergCG.le_two_of_dvd_six_of_dvd_two_pow (h1.trans hAutdvd) ⟨1, by rw [hn, mul_one]⟩
  have hcardE : Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  set K : Subgroup H := ψ.ker.map E.subtype with hK
  have hKcard : Nat.card K = Nat.card ψ.ker := card_map_of_injective E.subtype_injective
  have hKQ : K ≤ CFSG.pCore 2 H := by
    rintro _ ⟨e, he, rfl⟩
    exact hker e (MonoidHom.mem_ker.1 he)
  have hKdvd : Nat.card K ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hKQ
  by_cases hK4 : Nat.card K = 4
  ·
    have hKQeq : K = CFSG.pCore 2 H := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hK4, h4])
    have hQE : CFSG.pCore 2 H ≤ E := by
      rw [← hKQeq]
      exact map_subtype_le _
    have hEC : E ≤ centralizer (CFSG.pCore 2 H : Set H) := fun e he =>
      mem_centralizer_iff.2 fun q hq =>
        congrArg Subtype.val (mul_comm (⟨q, hQE hq⟩ : E) ⟨e, he⟩)
    calc Nat.card E ≤ Nat.card (CFSG.pCore 2 H) := Subgroup.card_le_of_le (hEC.trans hC)
      _ = 4 := h4
  · have hK2 : Nat.card K ≤ 2 := by
      have hK3 : Nat.card K ≠ 3 := fun h => by
        rw [h] at hKdvd
        norm_num at hKdvd
      have hK4' : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hKdvd
      omega
    rw [hcardE, ← hKcard]
    calc Nat.card K * Nat.card ψ.range ≤ 2 * 2 := Nat.mul_le_mul hK2 hrange
      _ = 4 := by norm_num

end CFSG.LocalAnalysis.GorensteinLyons
