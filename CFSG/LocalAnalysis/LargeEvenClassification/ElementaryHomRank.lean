module

public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreTwoSubgroups
public import CFSG.LocalAnalysis.LargeEvenClassification.AutomorphismObstruction

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem elementary_hom_rank_add {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime rank : ℕ}
    (hprime : prime.Prime) (Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (homomorphism : Elementary →* Target) :
    pRank prime (homomorphism.ker.map Elementary.subtype) + pRank prime homomorphism.range = rank := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hpgroup : IsPGroup prime Elementary := IsPGroup.of_card hcard
  obtain ⟨kernelRank, hkernelCard⟩ := (hpgroup.to_subgroup homomorphism.ker).exists_card_eq
  have hpimage : IsPGroup prime homomorphism.range := by
    rw [MonoidHom.range_eq_map]
    exact (hpgroup.to_subgroup ⊤).map homomorphism
  obtain ⟨imageRank, himageCard⟩ := hpimage.exists_card_eq
  have hkernelMapCard : Nat.card (homomorphism.ker.map Elementary.subtype) = prime ^ kernelRank :=
    (Nat.card_congr (homomorphism.ker.equivMapOfInjective Elementary.subtype
      Elementary.subtype_injective).toEquiv).symm.trans hkernelCard
  have hkernelElementary : IsElemAbelian prime (homomorphism.ker.map Elementary.subtype) :=
    elementary_subgroup_of_le Elementary _ helementary (Subgroup.map_subtype_le _)
  have hkernelRank := elementary_pRank_card hprime.one_lt _ hkernelElementary hkernelMapCard
  have himageRank := elementary_pRank_card hprime.one_lt _
    (elementary_hom_range Elementary helementary homomorphism) himageCard
  have hquotientCard : Nat.card (Elementary ⧸ homomorphism.ker) = Nat.card homomorphism.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange homomorphism).toEquiv
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup homomorphism.ker
  rw [hquotientCard, hkernelCard, himageCard, hcard, ← pow_add] at hformula
  have hranks : rank = imageRank + kernelRank := le_antisymm
    ((Nat.pow_le_pow_iff_right hprime.one_lt).mp hformula.le)
    ((Nat.pow_le_pow_iff_right hprime.one_lt).mp hformula.ge)
  rw [hkernelRank, himageRank]
  omega

end CFSG.LargeEvenClassification.Helpers
