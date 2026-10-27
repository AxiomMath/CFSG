module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Group
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.McLStd

theorem pPrimeCore_eq_bot_of_standardComponentOddCore_eq_bot {X : Type*} [Group X]
    (hO : CFSG.Open.standardComponentOddCore X = ⊥) : CFSG.pPrimeCore 2 X = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN => ?_
  rw [← hO]
  exact le_sSup ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩

theorem pPrimeCore_eq_bot_of_isSubnormal {G : Type} [Group G] [Finite G] {K H : Subgroup G}
    (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal) (hH : CFSG.pPrimeCore 2 ↥H = ⊥) :
    CFSG.pPrimeCore 2 ↥K = ⊥ := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hsub
  rw [hH, le_bot_iff] at h1
  have h2 := CFSG.pPrimeCore_map_subgroupOf 2 K H hKH
  rw [h1, Subgroup.map_bot] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h2.symm

theorem isQuasisimple_of_pPrimeCore_eq_bot {G : Type} [Group G] {K : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.oddCore ↥K)) (hO : CFSG.pPrimeCore 2 ↥K = ⊥) :
    CFSG.IsQuasisimple ↥K := by
  have hO' : CFSG.oddCore ↥K = ⊥ := by
    rw [Solomon78.oddCore_eq_pPrimeCore_two']
    exact hO
  let e : ↥K ⧸ CFSG.oddCore ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

theorem isPGroup_center_of_pPrimeCore_eq_bot {K : Type*} [Group K] [Finite K]
    (hO : CFSG.pPrimeCore 2 K = ⊥) : IsPGroup 2 ↥(center K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro z
  have hz0 : orderOf (z : K) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨a, m, hm, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hz0
  refine ⟨a, ?_⟩
  set w : K := (z : K) ^ (2 ^ a) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hdecomp⟩, hdecomp]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
  have hwc : w ∈ center K := Subgroup.pow_mem _ z.2 _
  have hnorm : (zpowers w).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : Commute g w := Subgroup.mem_center_iff.1 hwc g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact mem_zpowers_iff.2 ⟨k, rfl⟩
  have hcop : Nat.Coprime 2 (Nat.card (zpowers w)) := by
    rw [Nat.card_zpowers, hwo]
    exact Nat.coprime_two_left.2 hm
  have hle : zpowers w ≤ CFSG.pPrimeCore 2 K := le_sSup ⟨hnorm, hcop⟩
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have hm1 : m = 1 := by rw [← hwo, hle, orderOf_one]
  rw [← Subgroup.orderOf_coe, hdecomp, hm1, mul_one]

theorem catalog_center_quotient_of_kProper {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {K : Subgroup G} (hKtop : K ≠ ⊤)
    (hq : CFSG.IsQuasisimple ↥K) : CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) := by
  set Z : Subgroup G := (center ↥K).map K.subtype with hZ
  have hZK : Z ≤ K := Subgroup.map_subtype_le _
  have hsub : Z.subgroupOf K = center ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hnormZ : (Z.subgroupOf K).Normal := by
    rw [hsub]
    infer_instance
  let e : ↥K ⧸ Z.subgroupOf K ≃* ↥K ⧸ center ↥K := QuotientGroup.quotientMulEquivOfEq hsub
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  have hsimple' : IsSimpleGroup (↥K ⧸ Z.subgroupOf K) := e.isSimpleGroup
  have hcat := hK K Z hKtop hZK hsimple'
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact CFSG.SectionRank.catalog_of_mulEquiv e.symm hcat

variable {G : Type} [Group G] {L : Subgroup G}

theorem normal_subgroupOf_inf_centralizer [Finite G] (h : StdHyp G L) {t u : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) {K : Subgroup G}
    (hK : K ≤ centralizer ({u} : Set G)) :
    ((centralizer ({u} : Set G) ⊓ L).subgroupOf (K ⊓ centralizer ({t} : Set G))).Normal := by
  refine ⟨fun b hb g => ?_⟩
  have hb' : (b : G) ∈ centralizer ({u} : Set G) ⊓ L := hb
  have hgK : (g : G) ∈ K := g.2.1
  have hgt : (g : G) ∈ centralizer ({t} : Set G) := g.2.2
  have hgL : (g : G) ∈ normalizer (L : Set G) := h.centralizer_le_normalizer ht ht2 hgt
  have hgu : (g : G) ∈ centralizer ({u} : Set G) := hK hgK
  show (g : G) * (b : G) * (g : G)⁻¹ ∈ centralizer ({u} : Set G) ⊓ L
  refine ⟨?_, (mem_normalizer_iff.1 hgL (b : G)).1 hb'.2⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgu hb'.1) (Subgroup.inv_mem _ hgu)

theorem eq_one_or_eq_of_center_card_two {B : Subgroup G} {u z : G} (hB : Nat.card (center ↥B) = 2)
    (huB : u ∈ B) (hu1 : u ≠ 1) (hucomm : ∀ b ∈ B, u * b = b * u) (hzB : z ∈ B)
    (hz : ∀ b ∈ B, z * b = b * z) : z = 1 ∨ z = u := by
  have hu : (⟨u, huB⟩ : ↥B) ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hucomm b b.2).symm
  have hz' : (⟨z, hzB⟩ : ↥B) ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hz b b.2).symm
  by_cases hz1 : z = 1
  · exact Or.inl hz1
  · refine Or.inr ?_
    have h1 : (⟨⟨z, hzB⟩, hz'⟩ : ↥(center ↥B)) ≠ 1 := fun h => hz1 (by
      have := congrArg (fun x : ↥(center ↥B) => ((x : ↥B) : G)) h
      simpa using this)
    have h2 : (⟨⟨u, huB⟩, hu⟩ : ↥(center ↥B)) ≠ 1 := fun h => hu1 (by
      have := congrArg (fun x : ↥(center ↥B) => ((x : ↥B) : G)) h
      simpa using this)
    have := congrArg (fun x : ↥(center ↥B) => ((x : ↥B) : G)) (eq_of_card_two hB h1 h2)
    simpa using this

end CFSG.EvenSporadicStandard.Induction.Balance
