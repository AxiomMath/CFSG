module

public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.Steps.Ppp
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec8Comp
import CFSG.Goldschmidt.Steps.Sec88a
import CFSG.Goldschmidt.Steps.Sec88b
import CFSG.Goldschmidt.Steps.Sec88c
import CFSG.Goldschmidt.Steps.Sec88d
import CFSG.Goldschmidt.Steps.G36Setup
import CFSG.Goldschmidt.Steps.G310Bar
import CFSG.Goldschmidt.Steps.G76L2
import CFSG.Goldschmidt.Steps.G76U34

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem direct_factor_of_not_isGood
    (h81 : S_G81) (h86 : S_G86) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) (hS : ¬ IsMulCommutative (S : Subgroup G)) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx1 : x ≠ 1) (hx : ¬ Ppp.IsGood A x) :
    ∃ B : Subgroup G, B ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) ∧ A ⊓ B = ⊥ ∧
      A ⊔ B = (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hset.le
  set M := Subgroup.centralizer ({x} : Set G) with hM
  have hAM : A ≤ M := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (le_centralizer hset h4 hxS) a ha)
  have hSM : IsSStarIn M A := sstar_of_le hset (centralizer_ne_top hset hx1) hAM
  have hπodd : Odd (Nat.card (QuotientGroup.mk' (goldschmidtOddCore M)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact SStarTransport.odd_card_goldschmidtOddCore M
  have hinjA := injOn_of_isPGroup (QuotientGroup.mk' (goldschmidtOddCore M)) hπodd
    (P := A.subgroupOf M) hA2.comap_subtype
  have hO := goldschmidtOddCore_quotient_eq_bot M
  have hQS : IsSStarIn ⊤ (barOf M A) := SStarTransport.isSStarIn_barOf hSM
  have hAb : IsElemAbelian 2 (barOf M A) :=
    SStarTransport.isElemAbelian_map (SStarTransport.isElemAbelian_subgroupOf hset.elem M) _
  have hAb4 : Nat.card (barOf M A) = 4 := by
    rw [barOf, G76.card_map_eq_of_injOn _ hinjA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, h4]
  have hK : ¬ normalClosureIn ⊤ (barOf M A) ≤ barOf M A := by
    intro hle
    refine hx (Ppp.isGood_of_le_preOf (P := barOf M A) (hA2.comap_subtype.map _) ?_)
    refine (Ppp.commutator_le_normalClosureIn hAM).trans fun y hy => ?_
    have hyM : y ∈ M := normalClosureIn_le_self M A hy
    have h1 : QuotientGroup.mk' (goldschmidtOddCore M) (⟨y, hyM⟩ : M) ∈
        barOf M (normalClosureIn M A) := ⟨⟨y, hyM⟩, hy, rfl⟩
    rw [G310.barOf_normalClosureIn] at h1
    exact ⟨⟨y, hyM⟩, hle h1, rfl⟩
  obtain ⟨L, hL⟩ := exists_isComponentOf hO hQS hK
  have hAL := le_of_isComponentOf G31 hQS hAb hAb4 hL
  have hCN := centralizer_le_normalizer hQS hAb hAb4 hL
  obtain ⟨-, T₀, hT₀, htype⟩ := exists_g36Hyp G31 hQS hAb hL
  rcases htype with hI | hII
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_psu34 hT₀ hI (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hAb4])
    have hZ2 := G76.center_two_eq_one_of_psu3 hT₀.quasisimple e
    obtain ⟨R, r, hR2, hAR, hR64, hARR, hrR, hrA, hX⟩ := exists_u34_data hset h4 hAM
      (QuotientGroup.mk' (goldschmidtOddCore M)) (QuotientGroup.mk'_surjective _) hπodd
      hT₀.quasisimple e hZ2 hAL hCN
    obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
    obtain ⟨hH, -, -, -⟩ := facts81 h81 hset h4 ha ha1
    obtain ⟨p, hp, hp2, hinv, hrank, huniqH⟩ := h86 G S A hset h4 hS a ha ha1 _ hH
    obtain ⟨b, hb, hbz⟩ : ∃ b ∈ A, b ∉ Subgroup.zpowers a := by
      by_contra hall
      push Not at hall
      have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers a from hall)
      rw [Nat.card_zpowers, h4] at h1
      have h2 := orderOf_le_of_pow_eq_one two_pos (hset.elem.2 a ha)
      omega
    have hRA := pGroup_le_centralizer hset h4 hR2 hAR
    have hCH : Subgroup.centralizer (A : Set G) ≤
        Subgroup.normalizer (qCoreOf (Subgroup.centralizer ({a} : Set G)) p : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans
        (le_normalizer_of_isNormalIn (qCoreOf_normal_in _ p))
    have h32 := card_le_32 hset.elem h4 ha hb hp hp2 (qCoreOf_isPGroup _ p)
      (hinv b hb hbz) hrank hR2 hAR hRA (hRA.trans hCH) hARR
      (fun t ht ht2 => huniqH t ⟨Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
        (hRA ht.1), ht.2⟩ ht2) hrR hrA (hCH hrA) hX
    omega
  obtain ⟨hAC, hacts⟩ := typeII_facts hQS hAb hAb4 hL hT₀ hII
  set B := (S : Subgroup G) ⊓ ((Subgroup.centralizer
    (L : Set (M ⧸ goldschmidtOddCore M))).comap (QuotientGroup.mk' (goldschmidtOddCore M))).map
      M.subtype with hB
  have hBle : B ≤ (S : Subgroup G) ⊓ M := le_inf inf_le_left (inf_le_right.trans
    (Subgroup.map_subtype_le _))
  refine ⟨B, hBle, ?_, le_antisymm (sup_le (le_inf hset.le hAM) hBle) fun s hs => ?_⟩
  · rw [eq_bot_iff]
    rintro c ⟨hcA, -, ⟨y, hy, rfl⟩⟩
    have h1 : QuotientGroup.mk' (goldschmidtOddCore M) y ∈
        barOf M A ⊓ Subgroup.centralizer (L : Set (M ⧸ goldschmidtOddCore M)) :=
      ⟨⟨y, hcA, rfl⟩, hy⟩
    rw [hAC, Subgroup.mem_bot, ← map_one (QuotientGroup.mk' (goldschmidtOddCore M))] at h1
    rw [hinjA y hcA 1 (Subgroup.one_mem _) h1]
    exact Subgroup.one_mem _
  · obtain ⟨hsS, hsM⟩ := hs
    set w := QuotientGroup.mk' (goldschmidtOddCore M) (⟨s, hsM⟩ : M) with hw
    have hwA : w ∈ Subgroup.centralizer (barOf M A : Set (M ⧸ goldschmidtOddCore M)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hw, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (le_centralizer hset h4 hsS) a ha))
    have hw2 : IsPGroup 2 (Subgroup.zpowers w) := by
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hsS⟩
      refine G76.isPGroup_zpowers_of_pow_eq_one (e := k) ?_
      rw [hw, ← map_pow]
      have : (⟨s, hsM⟩ : M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    obtain ⟨c, ⟨a, ha, rfl⟩, hcw⟩ := hacts w hwA hw2
    have hasB : (a : G)⁻¹ * s ∈ B := by
      refine ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hset.le ha)) hsS,
        ⟨a⁻¹ * ⟨s, hsM⟩, ?_, rfl⟩⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
      exact hcw
    have e : s = (a : G) * ((a : G)⁻¹ * s) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hasB)

end CFSG.Goldschmidt.Sec8
