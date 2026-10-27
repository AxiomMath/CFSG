module

public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem isSylowOf_mono {R K L : Subgroup G} (hR : IsSylowOf 2 R K) (hRL : R ≤ L) (hLK : L ≤ K) :
    IsSylowOf 2 R L :=
  ⟨hRL, hR.2.1, fun hd => hR.2.2
    (hd.trans ⟨L.relIndex K, (Subgroup.relIndex_mul_relIndex R L K hRL hLK).symm⟩)⟩

theorem mem_normalizer_of_commutator_mem [Finite G] {Y R : Subgroup G}
    (hNo : SubTwo.NoTwoQuotient Y) (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) {g : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) (hcomm : ∀ y ∈ Y, ⁅g, y⁆ ∈ R) :
    g ∈ Subgroup.normalizer (Y : Set G) := by
  have hB : ((Y ⊔ R : Subgroup G) : Set G) = (Y : Set G) * R :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY
  have hconj : ∀ b ∈ Y ⊔ R, g * b * g⁻¹ ∈ Y ⊔ R := by
    intro b hb
    rw [← SetLike.mem_coe, hB] at hb
    obtain ⟨y, hy, r, hr, rfl⟩ := hb
    have e : g * (y * r) * g⁻¹ = (⁅g, y⁆ * y) * (g * r * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Y ⊔ R).mul_mem ((Y ⊔ R).mul_mem (Subgroup.mem_sup_right (hcomm y hy))
      (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgR r).mp hr))
  have hgB : g ∈ Subgroup.normalizer ((Y ⊔ R : Subgroup G) : Set G) := by
    have hmap : (Y ⊔ R).map (MulAut.conj g).toMonoidHom = Y ⊔ R := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨b, hb, rfl⟩
        simpa [MulAut.conj_apply] using hconj b hb
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => hconj b hb, fun hb => ?_⟩
    have hb' : g * b * g⁻¹ ∈ (Y ⊔ R).map (MulAut.conj g).toMonoidHom := by
      rw [hmap]
      exact hb
    obtain ⟨z, hz, hzb⟩ := hb'
    have h2 : g * z * g⁻¹ = g * b * g⁻¹ := by simpa [MulAut.conj_apply] using hzb
    have hzb' : z = b := mul_left_cancel (mul_right_cancel h2)
    rw [← hzb']
    exact hz
  refine SubTwo.mem_normalizer_of_normal_chain (B := Y ⊔ R)
    (B' := Subgroup.normalizer ((Y ⊔ R : Subgroup G) : Set G)) hNo le_sup_left
    (sup_le Subgroup.le_normalizer hRY) le_rfl hR2 ?_ hgB
  intro b hb
  rw [← SetLike.mem_coe, hB] at hb
  obtain ⟨y, hy, r, hr, rfl⟩ := hb
  exact ⟨y, hy, r, hr, Subgroup.mem_sup_right hr, rfl⟩

theorem isCharacteristicP_of_oTwoIn_eq [Finite G] {K R : Subgroup G} (hKR : oTwoIn K = R)
    (hC : K ⊓ Subgroup.centralizer (R : Set G) ≤ R) : IsCharacteristicP 2 ↥K := by
  have hRK : R ≤ K := hKR ▸ SixThree.oTwoIn_le K
  have hp : pCore 2 ↥K = R.subgroupOf K := by
    rw [← hKR]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  intro k hk
  rw [hp] at hk ⊢
  rw [Subgroup.mem_subgroupOf]
  refine hC ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have h := Subgroup.mem_centralizer_iff.mp hk ⟨r, hRK hr⟩
    (show (⟨r, hRK hr⟩ : K) ∈ R.subgroupOf K from hr)
  exact congrArg Subtype.val h

end CFSG.CGT.PushingUpLit.CGT6
