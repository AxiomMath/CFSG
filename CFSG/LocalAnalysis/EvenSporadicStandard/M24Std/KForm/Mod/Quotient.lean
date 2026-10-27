module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Setting
import CFSG.Walter.Cited.OddQuotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardQuotient
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.HSStd.InvCent

private noncomputable def centralizerMk (X : Type) [Group X] (z : X) :
    ↥(centralizer ({z} : Set X)) →*
      ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
        Set (X ⧸ fusionOddCore X))) where
  toFun c := ⟨QuotientGroup.mk' (fusionOddCore X) (c : X), by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 c.2]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private theorem centralizerMk_surjective {X : Type} [Group X] [Finite X] {z : X}
    (hz : orderOf z = 2) : Function.Surjective (centralizerMk X z) := by
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  intro y
  have hy := CFSG.Walter.Suzuki.centralizer_mk_le_map (fusionOddCore X)
    (CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd X) htt y.2
  obtain ⟨c, hc, hcy⟩ := hy
  exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩

theorem modData_of_quotient {G : Type*} [Group G] [Finite G] {B : Type*} [Group B]
    {B₀ : Subgroup B} {t : G} (ht : orderOf t = 2) (hR : RHyp B B₀)
    (ζ : ↥(centralizer ({t} : Set G)) ⧸ fusionOddCore ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × B) :
    ModData t B₀ (ζ.toMonoidHom.comp
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({t} : Set G))))) := by
  have htsq : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hodd : Odd (Nat.card (ζ.toMonoidHom.comp
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({t} : Set G))))).ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ ζ.injective, QuotientGroup.ker_mk']
    exact CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd _
  exact ⟨htsq, ht1, ζ.surjective.comp (QuotientGroup.mk'_surjective _), hodd, hR⟩

theorem nonempty_quotient_equiv_of_odd_ker {C : Type*} [Group C] [Finite C] {B : Type*} [Group B]
    (hB : fusionOddCore (Multiplicative (ZMod 2) × B) = ⊥)
    (ψ : C →* Multiplicative (ZMod 2) × B) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) :
    Nonempty (C ⧸ fusionOddCore C ≃* Multiplicative (ZMod 2) × B) := by
  have hle1 : ψ.ker ≤ fusionOddCore C :=
    CFSG.EvenSporadicStandard.M23Std.le_fusionOddCore_of_odd (N := ψ.ker) hodd
  have hle2 : fusionOddCore C ≤ ψ.ker := by
    haveI : ((fusionOddCore C).map ψ).Normal :=
      (inferInstance : (fusionOddCore C).Normal).map ψ hψ
    have hoddmap : Odd (Nat.card ((fusionOddCore C).map ψ)) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd C)
        (Subgroup.card_map_dvd (H := fusionOddCore C) ψ)
    have hle := CFSG.EvenSporadicStandard.M23Std.le_fusionOddCore_of_odd
      (N := (fusionOddCore C).map ψ) hoddmap
    rw [hB, le_bot_iff] at hle
    intro x hx
    rw [MonoidHom.mem_ker]
    have : ψ x ∈ (fusionOddCore C).map ψ := ⟨x, hx, rfl⟩
    rw [hle, Subgroup.mem_bot] at this
    exact this
  have heq : fusionOddCore C = ψ.ker := le_antisymm hle2 hle1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem exists_hom_quotient {X : Type} [Group X] [Finite X] {z : X} (hz : orderOf z = 2)
    {B : Type} [Group B] (hB : fusionOddCore (Multiplicative (ZMod 2) × B) = ⊥)
    (ψ : ↥(centralizer ({z} : Set X)) →* Multiplicative (ZMod 2) × B)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) :
    ∃ ψ' : ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
        Set (X ⧸ fusionOddCore X))) →* Multiplicative (ZMod 2) × B,
      Function.Surjective ψ' ∧ Odd (Nat.card ψ'.ker) := by
  have hπ : Function.Surjective (centralizerMk X z) := centralizerMk_surjective hz
  let V : Subgroup ↥(centralizer ({z} : Set X)) := (centralizerMk X z).ker
  have hVodd : Odd (Nat.card V) := by
    have hle : V.map (centralizer ({z} : Set X)).subtype ≤ fusionOddCore X := by
      rintro x ⟨v, hv, rfl⟩
      have hv1 : centralizerMk X z v = 1 := hv
      have h1 : QuotientGroup.mk' (fusionOddCore X) (v : X) = 1 := congrArg Subtype.val hv1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd : Nat.card V ∣ Nat.card (fusionOddCore X) := by
      have h2 : Nat.card (V.map (centralizer ({z} : Set X)).subtype) = Nat.card V :=
        Subgroup.card_map_of_injective (centralizer ({z} : Set X)).subtype_injective
      rw [← h2]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat (CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd X) hdvd
  have hVle : V ≤ ψ.ker := by
    haveI : (V.map ψ).Normal := (inferInstance : V.Normal).map ψ hψ
    have hoddmap : Odd (Nat.card (V.map ψ)) :=
      Odd.of_dvd_nat hVodd (Subgroup.card_map_dvd (H := V) ψ)
    have hle := CFSG.EvenSporadicStandard.M23Std.le_fusionOddCore_of_odd (N := V.map ψ) hoddmap
    rw [hB, le_bot_iff] at hle
    intro v hv
    rw [MonoidHom.mem_ker]
    have : ψ v ∈ V.map ψ := ⟨v, hv, rfl⟩
    rw [hle, Subgroup.mem_bot] at this
    exact this
  let ψ' : ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
      Set (X ⧸ fusionOddCore X))) →* Multiplicative (ZMod 2) × B :=
    (QuotientGroup.lift V ψ hVle).comp
      (QuotientGroup.quotientKerEquivOfSurjective (centralizerMk X z) hπ).symm.toMonoidHom
  have hψ'_apply : ∀ c, ψ' (centralizerMk X z c) = ψ c := by
    intro c
    show (QuotientGroup.lift V ψ hVle)
        ((QuotientGroup.quotientKerEquivOfSurjective (centralizerMk X z) hπ).symm
          (centralizerMk X z c)) = ψ c
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective (centralizerMk X z) hπ).symm
        (centralizerMk X z c) = QuotientGroup.mk c := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [h1]
    exact QuotientGroup.lift_mk V hVle c
  have hψ'surj : Function.Surjective ψ' := by
    intro y
    obtain ⟨c, hc⟩ := hψ y
    exact ⟨centralizerMk X z c, by rw [hψ'_apply, hc]⟩
  have hker : ψ'.ker = ψ.ker.map (centralizerMk X z) := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, rfl⟩ := hπ y
      refine ⟨c, ?_, rfl⟩
      change ψ c = 1
      rw [← hψ'_apply c]
      exact MonoidHom.mem_ker.mp hy
    · rintro ⟨c, hc, rfl⟩
      change ψ' (centralizerMk X z c) = 1
      rw [hψ'_apply]
      exact MonoidHom.mem_ker.mp hc
  have hψ'odd : Odd (Nat.card ψ'.ker) := by
    rw [hker]
    exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd (H := ψ.ker) (centralizerMk X z))
  exact ⟨ψ', hψ'surj, hψ'odd⟩

theorem quotient_setting_mod {X : Type} [Group X] [Finite X] (hK : CFSG.SectionRank.IsKGroupCat X)
    {z : X} (hz : orderOf z = 2) {B : Type} [Group B]
    (hB : fusionOddCore (Multiplicative (ZMod 2) × B) = ⊥)
    (ζ : ↥(centralizer ({z} : Set X)) ⧸ fusionOddCore ↥(centralizer ({z} : Set X)) ≃*
      Multiplicative (ZMod 2) × B) :
    fusionOddCore (X ⧸ fusionOddCore X) = ⊥ ∧
      CFSG.SectionRank.IsKGroupCat (X ⧸ fusionOddCore X) ∧
      orderOf (QuotientGroup.mk' (fusionOddCore X) z) = 2 ∧
      Nonempty (↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
          Set (X ⧸ fusionOddCore X))) ⧸
        fusionOddCore ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
          Set (X ⧸ fusionOddCore X))) ≃* Multiplicative (ZMod 2) × B) := by
  have hO : fusionOddCore (X ⧸ fusionOddCore X) = ⊥ :=
    CFSG.EvenSporadicStandard.M24Std.standardComponentOddCore_quotient_fusionOddCore_eq_bot X
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hzO : z ∉ fusionOddCore X := by
    intro hzmem
    have hodd2 : Odd (orderOf z) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd X)
        (Subgroup.orderOf_dvd_natCard _ hzmem)
    have hev2 : Even (orderOf z) := by rw [hz]; exact ⟨1, by norm_num⟩
    exact (Nat.not_even_iff_odd.2 hodd2) hev2
  have hzbar_ne : QuotientGroup.mk' (fusionOddCore X) z ≠ 1 := by
    intro h1
    apply hzO
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hzbar2 : (QuotientGroup.mk' (fusionOddCore X) z) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, htt, map_one]
  have hord : orderOf (QuotientGroup.mk' (fusionOddCore X) z) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hzbar2 hzbar_ne
  refine ⟨hO, hK.quotient (fusionOddCore X), hord, ?_⟩
  let ψ : ↥(centralizer ({z} : Set X)) →* Multiplicative (ZMod 2) × B :=
    ζ.toMonoidHom.comp (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({z} : Set X))))
  have hψ : Function.Surjective ψ :=
    ζ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card ψ.ker) := by
    change Odd (Nat.card (ζ.toMonoidHom.comp
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({z} : Set X))))).ker)
    rw [MonoidHom.ker_comp_of_injective _ _ ζ.injective, QuotientGroup.ker_mk']
    exact CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd _
  obtain ⟨ψ', hψ'surj, hψ'odd⟩ := exists_hom_quotient hz hB ψ hψ hodd
  exact nonempty_quotient_equiv_of_odd_ker hB ψ' hψ'surj hψ'odd

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
