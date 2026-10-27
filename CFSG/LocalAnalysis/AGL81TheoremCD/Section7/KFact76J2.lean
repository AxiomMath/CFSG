module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76J2Max
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76U33
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.RankThree.PartTwo.Sec4.Hering432Basic
import CFSG.Sporadic.Bridge.J2

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Sporadic CFSG.AGLEmbedding


theorem isCoatom_normalizer_of_j2 {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J2).Group))
    (A : Subgroup K) (hA : Nat.card A = 3)
    (hwc : ∀ g : K, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set K) →
      A.map (MulAut.conj g).toMonoidHom = A) :
    IsCoatom (Subgroup.normalizer (A : Set K)) := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hAS, hAC⟩ := Hering432.exists_sylow_le_center_of_weaklyClosed hA hwc
  have hP3 : Nat.card J2.P3 = 3 ^ (Nat.card J2.GJ).factorization 3 := by
    rw [J2.card_P3, J2.card_GJ, CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨e, he⟩ := UnitaryModel.exists_equiv_map_eq
    ((e₁.trans e₂.symm).trans CFSG.ComponentClassification.J2Cover.nativeEquivP) S
    (Sylow.ofCard J2.P3 hP3)
  rw [Sylow.coe_ofCard] at he
  have hAz : A.map e.toMonoidHom = Subgroup.zpowers J2.zJ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : e x ∈ J2.P3 := he ▸ Subgroup.mem_map_of_mem _ (hAS hx)
      have h2 := (UnitaryModel.mem_centralizer_map_iff e (S : Subgroup K) x).2 (hAC hx)
      rw [he] at h2
      have h3 : e x ∈ J2.P3 ⊓ Subgroup.centralizer ((J2.P3 : Subgroup J2.GJ) : Set J2.GJ) :=
        Subgroup.mem_inf.2 ⟨h1, h2⟩
      rwa [J2.inf_centralizer_P3, ← J2.z_eq] at h3
    · rw [Nat.card_zpowers, orderOf_eq_prime J2.z_cube J2.zJ_ne_one,
        Subgroup.card_map_of_injective e.injective, hA]
  refine (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) _).1 ?_
  rw [MulEquiv.coe_mapSubgroup, Subgroup.map_equiv_normalizer_eq, hAz]
  exact isCoatom_normalizer_zJ

theorem kFactU33J2NormalizerMax : KFactU33J2NormalizerMax := by
  intro K _ _ hK A hA hwc
  rcases hK with hK | hK
  · exact isCoatom_normalizer_of_u33 hK A hA hwc
  · exact isCoatom_normalizer_of_j2 hK A hA hwc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
