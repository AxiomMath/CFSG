module

public import CFSG.LocalAnalysis.LargeEvenClassification.GeneratorRank
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalElementary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def normalElementarySquareKernel {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) : Subgroup Ambient := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  exact (powMonoidHom 2 : Normal →* Normal).ker.map Normal.subtype

theorem normalElementarySquareKernel_normal {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal) :
    (normalElementarySquareKernel Normal hcommutative).Normal := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  constructor
  intro element helement conjugator
  obtain ⟨entry, hentry, rfl⟩ := Subgroup.mem_map.mp helement
  refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal conjugator entry, ?_, rfl⟩
  change (MulAut.conjNormal conjugator entry) ^ 2 = 1
  change entry ^ 2 = 1 at hentry
  rw [← map_pow, hentry, map_one]

theorem normalElementarySquareKernel_elementary {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) :
    IsElemAbelian 2 (normalElementarySquareKernel Normal hcommutative) := by
  have hle : normalElementarySquareKernel Normal hcommutative ≤ Normal := Subgroup.map_subtype_le _
  constructor
  · apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    change (first : Ambient) * second = (second : Ambient) * first
    exact congrArg (fun entry : Normal => (entry : Ambient))
      (@mul_comm' Normal _ hcommutative ⟨first, hle first.property⟩ ⟨second, hle second.property⟩)
  · intro element helement
    obtain ⟨entry, hentry, rfl⟩ := Subgroup.mem_map.mp helement
    have hpow : entry ^ 2 = 1 := hentry
    exact congrArg (fun normalElement : Normal => (normalElement : Ambient)) hpow

theorem commutative_frattini_card_le_square_kernel {Ambient : Type groupUniverse}
    [CommGroup Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) :
    Nat.card (Ambient ⧸ frattini Ambient) ≤ Nat.card (powMonoidHom 2 : Ambient →* Ambient).ker := by
  let powerMap := (powMonoidHom 2 : Ambient →* Ambient)
  have hrangeLe : powerMap.range ≤ frattini Ambient := by
    intro element helement
    obtain ⟨source, rfl⟩ := helement
    exact pGroup_pow_mem_frattini Nat.prime_two hpgroup source
  let : powerMap.range.Normal := inferInstance
  let projection := QuotientGroup.map powerMap.range (frattini Ambient) (MonoidHom.id Ambient)
    (by simpa only [Subgroup.comap_id] using hrangeLe)
  have hprojection : Function.Surjective projection := by
    intro coset
    obtain ⟨element, helement⟩ := QuotientGroup.mk'_surjective (frattini Ambient) coset
    refine ⟨QuotientGroup.mk' powerMap.range element, ?_⟩
    change QuotientGroup.map powerMap.range (frattini Ambient) (MonoidHom.id Ambient) _
      (QuotientGroup.mk' powerMap.range element) = coset
    rw [QuotientGroup.map_mk']
    exact helement
  have hquotientCard : Nat.card (Ambient ⧸ powerMap.range) = Nat.card powerMap.ker := by
    have hfirst := Subgroup.card_eq_card_quotient_mul_card_subgroup powerMap.range
    have hsecond := Subgroup.card_eq_card_quotient_mul_card_subgroup powerMap.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange powerMap).toEquiv] at hsecond
    have hpositive : 0 < Nat.card powerMap.range := Nat.card_pos
    nlinarith
  rw [← hquotientCard]
  exact Nat.card_le_card_of_surjective projection hprojection

theorem no_normal_eight_abelian_normal_frattini_card {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (hnoEight : ∀ Elementary : Subgroup Ambient, Elementary.Normal →
      IsElemAbelian 2 Elementary → Nat.card Elementary ≠ 8)
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal) :
    Nat.card (Normal ⧸ frattini Normal) ≤ 4 := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let Elementary := normalElementarySquareKernel Normal hcommutative
  let : Elementary.Normal := normalElementarySquareKernel_normal Normal hcommutative
  have helementary := normalElementarySquareKernel_elementary Normal hcommutative
  have hcardSmall : Nat.card Elementary < 8 := by
    by_contra hlarge
    obtain ⟨Eight, hnormal, _, helementaryEight, hcardEight⟩ :=
      normal_elementary_subgroup_order 3 Nat.prime_two hpgroup Elementary helementary (by omega)
    exact hnoEight Eight hnormal helementaryEight (by norm_num at hcardEight ⊢; exact hcardEight)
  have hpElementary : IsPGroup 2 Elementary := hpgroup.to_subgroup Elementary
  obtain ⟨rank, hcard⟩ := hpElementary.exists_card_eq
  have hrank : rank ≤ 2 := by
    by_contra hlarge
    have hpower : 2 ^ 3 ≤ 2 ^ rank := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hcard] at hpower
    norm_num at hpower
    omega
  have hcardBound : Nat.card Elementary ≤ 4 := by
    rw [hcard]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hrank).trans (by norm_num)
  have hkernelCard : Nat.card (powMonoidHom 2 : Normal →* Normal).ker = Nat.card Elementary := by
    exact (Subgroup.card_map_of_injective Subtype.val_injective).symm
  exact (commutative_frattini_card_le_square_kernel (hpgroup.to_subgroup Normal)).trans
    (hkernelCard ▸ hcardBound)

theorem no_normal_eight_abelian_normal_two_generators {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (hnoEight : ∀ Elementary : Subgroup Ambient, Elementary.Normal →
      IsElemAbelian 2 Elementary → Nat.card Elementary ≠ 8)
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal) :
    ∃ generators : Finset Normal,
      Subgroup.closure (generators : Set Normal) = ⊤ ∧ generators.card ≤ 2 := by
  let hpnormal := hpgroup.to_subgroup Normal
  let : CommGroup (Normal ⧸ frattini Normal) := pGroupFrattiniCommGroup Nat.prime_two hpnormal
  let module : Module (ZMod 2) (Additive (Normal ⧸ frattini Normal)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpnormal)
  obtain ⟨generators, hgenerates, hgeneratorCard⟩ :=
    exists_frattini_basis_generators Nat.prime_two hpnormal module
  have hcard := no_normal_eight_abelian_normal_frattini_card hpgroup hnoEight Normal hcommutative
  have hdimension : Module.finrank (ZMod 2) (Additive (Normal ⧸ frattini Normal)) ≤ 2 := by
    have hlinearCard := Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive (Normal ⧸ frattini Normal))
    have heq : Nat.card (Additive (Normal ⧸ frattini Normal)) =
        Nat.card (Normal ⧸ frattini Normal) := Nat.card_congr Additive.ofMul.symm
    rw [heq] at hlinearCard
    have hfieldCard : Nat.card (ZMod 2) = 2 := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
    rw [hfieldCard] at hlinearCard
    rw [hlinearCard] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  exact ⟨generators, hgenerates, hgeneratorCard.trans hdimension⟩

end CFSG.LargeEvenClassification.Helpers
