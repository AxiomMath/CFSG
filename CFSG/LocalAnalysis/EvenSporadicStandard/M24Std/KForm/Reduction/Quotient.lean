module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
import CFSG.Walter.Cited.OddQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Reduction

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.HSStd.InvCent

theorem fusionOddCore_prod_eq_bot_of_rhyp {B : Type} [Group B] [Finite B] {B₀ : Subgroup B}
    (hR : RHyp B B₀) (hev : Even (Nat.card ↥B₀)) :
    fusionOddCore (Multiplicative (ZMod 2) × B) = ⊥ := by
  have hodd : Odd (Nat.card (fusionOddCore (Multiplicative (ZMod 2) × B))) :=
    CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd _
  set N := fusionOddCore (Multiplicative (ZMod 2) × B) with hN
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hab
  have hord : Odd (orderOf (a, b)) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hab)
  obtain ⟨k, hk⟩ := hord
  have habk : (a, b) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have ha2 : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  have hak : a ^ (2 * k + 1) = 1 := by simpa [Prod.pow_def] using congrArg Prod.fst habk
  have hbk : b ^ (2 * k + 1) = 1 := by simpa [Prod.pow_def] using congrArg Prod.snd habk
  have ha1 : a = 1 := by
    have : a ^ (2 * k + 1) = a := by
      rw [pow_succ, pow_mul, ha2, one_pow, one_mul]
    rw [← this]; exact hak
  have hb1' : ((1 : Multiplicative (ZMod 2)), b) ∈ N := by
    have h2 : (a, b) ^ 2 ∈ N := pow_mem hab 2
    have h3 : ((1 : Multiplicative (ZMod 2)), b ^ 2) ∈ N := by
      have : (a, b) ^ 2 = ((1 : Multiplicative (ZMod 2)), b ^ 2) := by
        rw [Prod.pow_def]; simp [ha2]
      rwa [this] at h2
    have h4 := pow_mem h3 (k + 1)
    have : ((1 : Multiplicative (ZMod 2)), b ^ 2) ^ (k + 1) = (1, b) := by
      rw [Prod.pow_def]
      simp only [one_pow, Prod.mk.injEq, true_and]
      calc (b ^ 2) ^ (k + 1) = b ^ (2 * k + 1) * b := by rw [← pow_mul, ← pow_succ]; ring_nf
        _ = b := by rw [hbk, one_mul]
    rwa [this] at h4
  have hNn : N.Normal := inferInstance
  set M : Subgroup B := N.comap (MonoidHom.inr (Multiplicative (ZMod 2)) B)
  have hMn : M.Normal := hNn.comap _
  have hModd : Odd (Nat.card M) := by
    have hle : M.map (MonoidHom.inr (Multiplicative (ZMod 2)) B) ≤ N := by
      rintro _ ⟨m, hm, rfl⟩
      exact hm
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (fun x y h => by
      simpa using congrArg Prod.snd h)] at h1
    exact Odd.of_dvd_nat hodd h1
  have hbM : b ∈ M := hb1'
  by_cases h : M = ⊥
  · rw [h, mem_bot] at hbM
    rw [mem_bot, ha1, hbM]
    rfl
  · have hle := hR.min M hMn h
    have hdvd : Nat.card ↥B₀ ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hle
    exact absurd hev (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hModd hdvd))

theorem inf_fusionOddCore_centralizer_eq_bot_of_equiv {X : Type} [Group X] [Finite X] {z : X}
    {B : Type} [Group B] (hB : fusionOddCore (Multiplicative (ZMod 2) × B) = ⊥)
    (ζ : ↥(centralizer ({z} : Set X)) ≃* Multiplicative (ZMod 2) × B) :
    fusionOddCore X ⊓ centralizer ({z} : Set X) = ⊥ := by
  have hcen : fusionOddCore ↥(centralizer ({z} : Set X)) = ⊥ :=
    CFSG.EvenSporadicStandard.M23Std.fusionOddCore_eq_bot_of_equiv ζ hB
  haveI hn : ((fusionOddCore X ⊓ centralizer ({z} : Set X)).subgroupOf
      (centralizer ({z} : Set X))).Normal :=
    CFSG.EvenSporadicStandard.M24Std.inf_centralizer_subgroupOf_normal inferInstance z
  have hodd : Odd (Nat.card ((fusionOddCore X ⊓ centralizer ({z} : Set X)).subgroupOf
      (centralizer ({z} : Set X)))) := by
    have h1 : Nat.card ((fusionOddCore X ⊓ centralizer ({z} : Set X)).subgroupOf
        (centralizer ({z} : Set X))) = Nat.card (fusionOddCore X ⊓ centralizer ({z} : Set X) :
          Subgroup X) := by
      rw [← Subgroup.card_map_of_injective (centralizer ({z} : Set X)).subtype_injective
        (K := (fusionOddCore X ⊓ centralizer ({z} : Set X)).subgroupOf
          (centralizer ({z} : Set X))), Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    rw [h1]
    exact Odd.of_dvd_nat (CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd X)
      (Subgroup.card_dvd_of_le inf_le_left)
  have hle := CFSG.EvenSporadicStandard.M23Std.le_fusionOddCore_of_odd
    (X := ↥(centralizer ({z} : Set X))) hodd
  rw [hcen, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, (mem_inf.1 hx).2⟩ : ↥(centralizer ({z} : Set X))) ∈
      (fusionOddCore X ⊓ centralizer ({z} : Set X)).subgroupOf (centralizer ({z} : Set X)) :=
    mem_subgroupOf.2 hx
  rw [hle, mem_bot] at hx'
  exact mem_bot.2 (congrArg Subtype.val hx')

private noncomputable def centralizerMk (X : Type) [Group X] (z : X) :
    ↥(centralizer ({z} : Set X)) →*
      ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
        Set (X ⧸ fusionOddCore X))) where
  toFun c := ⟨QuotientGroup.mk' (fusionOddCore X) (c : X), by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 c.2]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private theorem centralizerMk_bijective {X : Type} [Group X] [Finite X] {z : X}
    (hz : orderOf z = 2) (h : fusionOddCore X ⊓ centralizer ({z} : Set X) = ⊥) :
    Function.Bijective (centralizerMk X z) := by
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  constructor
  · rw [injective_iff_map_eq_one]
    intro c hc
    have h1 : QuotientGroup.mk' (fusionOddCore X) (c : X) = 1 := congrArg Subtype.val hc
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have : (c : X) ∈ fusionOddCore X ⊓ centralizer ({z} : Set X) := mem_inf.2 ⟨h1, c.2⟩
    rw [h, mem_bot] at this
    exact Subtype.ext this
  · intro y
    have hy := CFSG.Walter.Suzuki.centralizer_mk_le_map (fusionOddCore X)
      (CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd X) htt y.2
    obtain ⟨c, hc, hcy⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩

private noncomputable def centralizerMkEquiv {X : Type} [Group X] [Finite X] {z : X}
    (hz : orderOf z = 2) (h : fusionOddCore X ⊓ centralizer ({z} : Set X) = ⊥) :
    ↥(centralizer ({z} : Set X)) ≃*
      ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
        Set (X ⧸ fusionOddCore X))) :=
  MulEquiv.ofBijective (centralizerMk X z) (centralizerMk_bijective hz h)

theorem nonempty_centralizer_mk_equiv {X : Type} [Group X] [Finite X] {z : X}
    (hz : orderOf z = 2) (h : fusionOddCore X ⊓ centralizer ({z} : Set X) = ⊥) :
    Nonempty (↥(centralizer ({z} : Set X)) ≃*
      ↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
        Set (X ⧸ fusionOddCore X)))) := by
  exact ⟨centralizerMkEquiv hz h⟩

theorem quotient_setting {X : Type} [Group X] [Finite X] (hK : CFSG.SectionRank.IsKGroupCat X)
    {z : X} (hz : orderOf z = 2) {B : Type} [Group B]
    (hB : fusionOddCore (Multiplicative (ZMod 2) × B) = ⊥)
    (ζ : ↥(centralizer ({z} : Set X)) ≃* Multiplicative (ZMod 2) × B) :
    fusionOddCore (X ⧸ fusionOddCore X) = ⊥ ∧
      CFSG.SectionRank.IsKGroupCat (X ⧸ fusionOddCore X) ∧
      orderOf (QuotientGroup.mk' (fusionOddCore X) z) = 2 ∧
      Nonempty (↥(centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
          Set (X ⧸ fusionOddCore X))) ≃* Multiplicative (ZMod 2) × B) := by
  have hO : fusionOddCore (X ⧸ fusionOddCore X) = ⊥ :=
    CFSG.EvenSporadicStandard.M24Std.standardComponentOddCore_quotient_fusionOddCore_eq_bot X
  have hker := inf_fusionOddCore_centralizer_eq_bot_of_equiv hB ζ
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
  exact ⟨hO, hK.quotient (fusionOddCore X), hord,
    ⟨(nonempty_centralizer_mk_equiv hz hker).some.symm.trans ζ⟩⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Reduction
