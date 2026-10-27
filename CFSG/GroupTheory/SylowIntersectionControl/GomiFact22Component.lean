module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCoreComponent
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentClauses
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentIsolated
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentSection
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiParabolicSwapConj
import CFSG.GroupTheory.SylowIntersectionControl.GomiProductSylow

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.SignalizerFunctorTheorem.McBride CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {G : Type} [Group G]

private theorem map_conj_mem_range (L : Subgroup G) (g : G) {J : Subgroup G}
    (hJ : J ∈ Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom) :
    J.map (MulAut.conj g).toMonoidHom ∈
      Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k, rfl⟩ := hJ
  exact ⟨g * k, (map_conj_map_conj L k g).symm⟩

private theorem exists_map_conj_eq (L : Subgroup G) (g₀ : G) {B : Subgroup G}
    (hB : B ∈ Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom) :
    ∃ g : G, (L.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
  obtain ⟨k, rfl⟩ := hB
  exact ⟨k * g₀⁻¹, by rw [map_conj_map_conj, inv_mul_cancel_right]⟩

private theorem not_isGomiParabolicSwap_map_conj_map_conj {S L : Subgroup G} {x : G}
    (h : ¬ IsGomiParabolicSwap S L) :
    ¬ IsGomiParabolicSwap (S.map (MulAut.conj x).toMonoidHom)
      (L.map (MulAut.conj x).toMonoidHom) := by
  intro hc
  refine h ?_
  have h1 := hc.map_conj_map_conj x⁻¹
  have hS : (S.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = S := by
    rw [Subgroup.map_conj_map_conj, inv_mul_cancel, map_one]
    exact Subgroup.map_id S
  have hL : (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = L := by
    rw [Subgroup.map_conj_map_conj, inv_mul_cancel, map_one]
    exact Subgroup.map_id L
  rwa [hS, hL] at h1

private theorem gomiChevHypsAt_map_conj [Finite G] {L N : Subgroup G} [N.Normal]
    (hGN : IsPGroup 2 (G ⧸ N)) {g : G}
    (hNA : N ≤ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (hLc : IsGomiChevTwo ↥L)
    (hexc : ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L)))
    (hswap : (IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) →
      ∃ S : Sylow 2 G, ¬ IsGomiParabolicSwap (S : Subgroup G) L) :
    IsGomiChevTwo ↥(L.map (MulAut.conj g).toMonoidHom) ∧
      (¬ (IsGomiL2 (↥(L.map (MulAut.conj g).toMonoidHom) ⧸
          center ↥(L.map (MulAut.conj g).toMonoidHom)) ∨
        IsGomiU3 (↥(L.map (MulAut.conj g).toMonoidHom) ⧸
          center ↥(L.map (MulAut.conj g).toMonoidHom)) ∨
        IsGomiSz (↥(L.map (MulAut.conj g).toMonoidHom) ⧸
          center ↥(L.map (MulAut.conj g).toMonoidHom)))) ∧
      ((IsGomiL3 (↥(L.map (MulAut.conj g).toMonoidHom) ⧸
          center ↥(L.map (MulAut.conj g).toMonoidHom)) ∨
        IsGomiSp4 (↥(L.map (MulAut.conj g).toMonoidHom) ⧸
          center ↥(L.map (MulAut.conj g).toMonoidHom))) →
        ∃ T : Subgroup G,
          IsSylowTwoOf T (normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) ∧
          ¬ IsGomiParabolicSwap T (L.map (MulAut.conj g).toMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have eZ : (↥(L.map (MulAut.conj g).toMonoidHom) ⧸
      center ↥(L.map (MulAut.conj g).toMonoidHom)) ≃* (↥L ⧸ center ↥L) :=
    QuotientGroup.congr (Subgroup.center ↥(L.map (MulAut.conj g).toMonoidHom))
      (Subgroup.center ↥L) e.symm (Subgroup.map_center_eq e.symm)
  refine ⟨hLc.of_mulEquiv e, ?_, ?_⟩
  · intro h
    exact hexc (h.elim (fun h => Or.inl (h.of_mulEquiv eZ))
      (fun h => h.elim (fun h => Or.inr (Or.inl (h.of_mulEquiv eZ)))
        (fun h => Or.inr (Or.inr (h.of_mulEquiv eZ)))))
  · intro h
    have hL3sp4 : IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L) :=
      h.elim (fun h => Or.inl (h.of_mulEquiv eZ)) (fun h => Or.inr (h.of_mulEquiv eZ))
    obtain ⟨S₀, hS₀⟩ := hswap hL3sp4
    let S₁ : Sylow 2 G := S₀.mapSurjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective
    have hS₁ : ¬ IsGomiParabolicSwap (S₁ : Subgroup G) (L.map (MulAut.conj g).toMonoidHom) :=
      not_isGomiParabolicSwap_map_conj_map_conj hS₀
    refine ⟨(S₁ : Subgroup G) ⊓
      normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
      isSylowTwoOf_sylow_inf_normalizer hGN S₁ hNA, ?_⟩
    exact fun hc => hS₁ (isGomiParabolicSwap_inf_normalizer_iff.mp hc)

private theorem twoResidual_inf_centralizer_eq_bot_of_components [Finite G] {S : Set (Subgroup G)}
    {N M A Q : Subgroup G} [N.Normal] (hN : IsDirectProduct S N)
    (hMN : M ⊓ N = sSup {Y | ∃ B ∈ S, Y = M ⊓ B})
    (hMB : ∀ B ∈ S, ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B ∧
      M ⊓ B = Q.map (MulAut.conj g).toMonoidHom)
    (hQ : twoResidual (Q ⊓ centralizer (pCoreOf 2 Q : Set G)) = ⊥) :
    twoResidual (M ⊓ N ⊓ centralizer (pCoreOf 2 (M ⊓ N) : Set G)) = ⊥ := by
  refine eq_bot_iff.mpr ((twoResidual_inf_centralizer_le_sSup hN hMN (T := fun _ => ⊥) ?_).trans
    (sSup_le ?_))
  · intro B hB
    obtain ⟨g, -, hg⟩ := hMB B hB
    rw [hg, twoResidual_inf_centralizer_map (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hQ, Subgroup.map_bot]
  · rintro _ ⟨B, -, rfl⟩
    exact le_rfl

theorem exists_of_not_isSylowTwoOf_inf_normalClosure (hIso : GomiChevIsolated)
    (hCore : GomiChevCore) {G : Type} [Group G] [Finite G] {L H : Subgroup G}
    (hL : GomiConjugatesCommute L) (hZ : L ⊓ centralizer (L : Set G) = ⊥)
    (hLc : IsGomiChevTwo ↥L)
    (hexc : ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L)))
    (hswap : (IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) →
      ∃ S : Sylow 2 G, ¬ IsGomiParabolicSwap (S : Subgroup G) L)
    (hH : IsPGroup 2 H) (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hJ : ¬ IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G))) :
    ∃ M : Subgroup G, M ≠ ⊤ ∧ Odd M.index ∧
      (∀ a ∈ normalizer (H : Set G), a ^ 2 ∈ H → a ∈ M) ∧
      twoResidual (M ⊓ normalClosure (L : Set G) ⊓
        centralizer (pCoreOf 2 (M ⊓ normalClosure (L : Set G)) : Set G)) = ⊥ := by
  have hN := isDirectProduct_conj hL.commute hZ
  have hSG : ∀ g : G, ∀ J ∈ Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom,
      J.map (MulAut.conj g).toMonoidHom ∈
        Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom :=
    fun g J hJ => map_conj_mem_range L g hJ
  obtain ⟨_, ⟨g₀, rfl⟩, hKA⟩ := exists_two_dvd_relIndex_of_not_isSylowTwoOf hN hH hJ
  obtain ⟨hA, hexcA, hswapA⟩ := gomiChevHypsAt_map_conj hL.isPGroup_quotient
    (hN.le_normalizer ⟨g₀, rfl⟩) hLc hexc hswap
  obtain ⟨Q, hQA, hQne, hQN, hTQ, hIQ, hDQ, hc⟩ := exists_core_of_gomiChevCore hIso hCore
    hA hexcA hswapA inf_le_right (hH.to_le inf_le_left)
    (hiso.normalizer_inf_sup_of_component hN hSG hH ⟨g₀, rfl⟩ hKA)
  have hQ : twoResidual (Q ⊓ centralizer (pCoreOf 2 Q : Set G)) = ⊥ :=
    le_bot_iff.mp (hc.trans (le_of_eq (map_conj_inf_centralizer_eq_bot hZ g₀)))
  obtain ⟨M, hMo, hHM, hMA, hMne, hMN, hMB⟩ := exists_odd_index_inf_eq hN hSG ⟨g₀, rfl⟩
    (fun B hB => exists_map_conj_eq L g₀ hB) hL.isPGroup_quotient hH hQA hQN hTQ hIQ
  refine ⟨M, hMne hQne, hMo, fun a ha ha2 => hiso.mem_of_component hN hSG hH ⟨g₀, rfl⟩ hKA hHM
    (fun d hd hd2 => (hMA.ge (hDQ d hd ⟨hd2, pow_mem (le_normalizer hd.1) 2⟩)).1) ha ha2, ?_⟩
  exact twoResidual_inf_centralizer_eq_bot_of_components hN hMN hMB hQ

end CFSG.GroupTheory

end
