module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalOfData

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic

section Certified


theorem not_isPGroup_two_co2 : ¬ IsPGroup 2 Co2 := by
  intro hp
  rw [IsPGroup.iff_card] at hp
  obtain ⟨n, hn⟩ := hp
  have h3 : 3 ∣ 2 ^ n := by
    rw [← hn, CFSG.Sporadic.Co2.card_Co2]
    norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem pCore_eq_of_quotient_co2 {J : Type} [Group J] [Finite J] (W : Subgroup J) [hW : W.Normal]
    (hp : IsPGroup 2 W) (e : J ⧸ W ≃* Carrier .Co2) : CFSG.pCore 2 J = W :=
  pCore_eq_of_quotient_simple hW hp CFSG.Sporadic.Co2.isSimpleGroup_Co2 e not_isPGroup_two_co2

theorem exists_shape_of_surjective {H J : Type} [Group H] [Group J] [Finite J] (ψ : H →* J)
    (hψ : Function.Surjective ψ) (Y₀ : Subgroup H) [Y₀.Normal] (hp : IsPGroup 2 Y₀)
    (e : H ⧸ Y₀ ≃* Carrier .Co2) (hker : ψ.ker ≤ Y₀)
    (hcomm : ∀ a ∈ Y₀, ∀ b ∈ Y₀, ψ a * ψ b = ψ b * ψ a)
    (hcent : ∀ h : H, (∀ y ∈ Y₀, ψ h * ψ y = ψ y * ψ h) → h ∈ Y₀) :
    CFSG.IsCharacteristicP 2 J ∧ IsMulCommutative (CFSG.pCore 2 J) ∧
      Nonempty (J ⧸ CFSG.pCore 2 J ≃* Carrier .Co2) := by
  have hWn : (Y₀.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  have hWp : IsPGroup 2 (Y₀.map ψ) :=
    hp.of_surjective (ψ.subgroupMap Y₀) (ψ.subgroupMap_surjective Y₀)
  have hφ : Function.Surjective ((QuotientGroup.mk' (Y₀.map ψ)).comp ψ) :=
    (QuotientGroup.mk'_surjective _).comp hψ
  have hkerφ : ((QuotientGroup.mk' (Y₀.map ψ)).comp ψ).ker = Y₀ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_map_eq]
    exact sup_eq_left.2 hker
  let e2 : J ⧸ Y₀.map ψ ≃* Carrier .Co2 :=
    ((QuotientGroup.quotientKerEquivOfSurjective _ hφ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerφ)).trans e
  have hcore : CFSG.pCore 2 J = Y₀.map ψ := pCore_eq_of_quotient_co2 _ hWp e2
  refine ⟨?_, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans e2⟩⟩
  · intro j hj
    rw [hcore]
    obtain ⟨h, rfl⟩ := hψ j
    refine ⟨h, hcent h fun y hy => ?_, rfl⟩
    have := mem_centralizer_iff.1 hj (ψ y) (by rw [SetLike.mem_coe, hcore]; exact ⟨y, hy, rfl⟩)
    exact this.symm
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨y, hy, hya⟩ := (hcore ▸ a.2 : (a : J) ∈ Y₀.map ψ)
    obtain ⟨y', hy', hyb⟩ := (hcore ▸ b.2 : (b : J) ∈ Y₀.map ψ)
    show (a : J) * b = b * a
    rw [← hya, ← hyb]
    exact hcomm y hy y' hy'

end Certified

end CFSG.EvenSporadicStandard.TwoB
