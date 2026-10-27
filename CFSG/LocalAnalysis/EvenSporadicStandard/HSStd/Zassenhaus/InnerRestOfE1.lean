module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SylowTransfer
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialSpec

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

theorem four_le_pRank_of_isSporadic_hs
    {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsSporadic ↥M .HS) : 4 ≤ CFSG.pRank 2 ↥M := by
  obtain ⟨e₀⟩ := hM
  let σ : ↥M ≃* ↥hs100P := (e₀ : ↥M ≃* NativeSporadic.HS).trans hs100Equiv
  obtain ⟨E, hEP, -, hEab, hE16, -⟩ := zas_special_spec
  let E' : Subgroup ↥hs100P := E.subgroupOf hs100P
  have hE'ab : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have := hEab.1.is_comm.comm ⟨((a : ↥hs100P) : Equiv.Perm (Fin 100)), a.2⟩
        ⟨((b : ↥hs100P) : Equiv.Perm (Fin 100)), b.2⟩
      simpa [Subgroup.coe_mul] using congrArg Subtype.val this
    · have := hEab.2 (x : Equiv.Perm (Fin 100)) hx
      simpa using this
  have hE'card : Nat.card E' = 16 := by
    rw [← hE16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  let F : Subgroup H := (E'.map σ.symm.toMonoidHom).map M.subtype
  have hinj : Function.Injective (M.subtype.comp σ.symm.toMonoidHom) :=
    Subtype.val_injective.comp σ.symm.injective
  have hFab : IsElemAbelian 2 F := by
    have h := isElemAbelian_map (M.subtype.comp σ.symm.toMonoidHom) hinj hE'ab
    rwa [← Subgroup.map_map] at h
  have hFcard : Nat.card F = 2 ^ 4 := by
    have h1 : Nat.card F = Nat.card E' := by
      show Nat.card ((E'.map σ.symm.toMonoidHom).map M.subtype) = _
      rw [Subgroup.map_map]
      exact Subgroup.card_map_of_injective hinj
    rw [h1, hE'card]
    norm_num
  have hFM : F ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two M]
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨F, hFM, hFab, hFcard⟩
  rintro k ⟨B, -, -, hk⟩
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : Nat.card B ≤ Nat.card H := Subgroup.card_le_card_group B
  change k ≤ Nat.card H
  omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
