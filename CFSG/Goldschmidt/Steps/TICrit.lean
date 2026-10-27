module

import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace TICrit

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_fusionIsSylowIn {U X : Subgroup G} (hU : IsPGroup 2 U) (hUX : U ≤ X) :
    ∃ T : Subgroup G, U ≤ T ∧ fusionIsSylowIn 2 T X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hU.comap_subtype (K := X)).exists_le_sylow
  refine ⟨(P : Subgroup X).map X.subtype,
    fun u hu => ⟨⟨u, hUX hu⟩, hP (show (⟨u, hUX hu⟩ : X) ∈ U.comap X.subtype from hu), rfl⟩,
    Subgroup.map_subtype_le _, P.isPGroup'.map _, fun Q hQX hQ hPQ => ?_⟩
  have h1 := P.is_maximal' (Q := Q.subgroupOf X) hQ.comap_subtype
    (fun x hx => hPQ ⟨x, hx, rfl⟩)
  refine le_antisymm (fun q hq => ⟨⟨q, hQX hq⟩, ?_, rfl⟩) hPQ
  rw [← h1]
  exact hq

theorem card_centralizer_lt [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {u : G}
    (hu1 : u ≠ 1) : Nat.card (Subgroup.centralizer ({u} : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer ({u} : Set G) ≠ ⊤ := by
    intro htop
    have hZ : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({u} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [PropHSetup.center_eq_bot hnab] at hZ
    exact hu1 (Subgroup.mem_bot.mp hZ)
  rw [← Subgroup.card_top (G := G)]
  exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)

omit [Finite G] in
theorem normalClosureIn_le_of_le_normalizer {U X : Subgroup G} (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) : normalClosureIn X U ≤ U := by
  have : (U.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).mpr hXU
  have h := Subgroup.map_mono (f := X.subtype)
    (Subgroup.normalClosure_le_normal (N := U.subgroupOf X) subset_rfl)
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.trans inf_le_left

theorem goldschmidtOddCore_eq_bot_of_isPGroup {M : Subgroup G} (hM : IsPGroup 2 M) :
    goldschmidtOddCore M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hM.exists_card_eq
  have hdvd : Nat.card (goldschmidtOddCore M) ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd : Odd (Nat.card (goldschmidtOddCore M)) :=
    CFSG.ComponentClassification.OddCore.odd_card M
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact Subgroup.card_eq_one.mp hj
  · rw [hj] at hodd
    exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩)
      (Nat.not_even_iff_odd.mpr hodd)

theorem goldschmidtLayer_eq_bot_of_comm {Q : Type*} [Group Q] (h : ∀ a b : Q, a * b = b * a) :
    goldschmidtLayer Q = ⊥ := by
  refine sSup_eq_bot.mpr fun K hK => ?_
  obtain ⟨-, -, -, hs⟩ := hK
  obtain ⟨x, hx⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact absurd ((QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (h y g))) hx

end TICrit

open TICrit in
theorem N32 :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IH (Nat.card G) → ∀ (S : Sylow 2 G) (U : Subgroup G), U ≤ S → IsMulCommutative U →
      fusionStronglyClosed (U : Set G) (S : Subgroup G) →
      (fusionIsTI U ↔ ∀ u ∈ U, u ≠ 1 →
        let M := normalClosureIn (Subgroup.centralizer ({u} : Set G)) U
        goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥ ∧ ⁅oddCoreOf M, U⁆ = ⊥) := by
  intro G _ _ _ hnab hIH S U hUS hUab hcl
  have hU2 : IsPGroup 2 U := S.isPGroup'.to_le hUS
  rw [isTI_iff_centralizer_le_normalizer S hUS hcl hUab]
  refine forall₂_congr fun u hu => imp_congr_right fun hu1 => ?_
  dsimp only
  set X := Subgroup.centralizer ({u} : Set G) with hXdef
  set M := normalClosureIn X U with hMdef
  have hUX : U ≤ X := fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hUab.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩))
  obtain ⟨T, hUT, hTX⟩ := exists_fusionIsSylowIn hU2 hUX
  obtain ⟨-, -, -, -, hC4⟩ := N16_of N1 (Nat.card G) hIH G S U X T hUS hUab hcl hUT hTX
    (card_centralizer_lt hnab hu1)
  constructor
  · intro hXN
    have hMU : M ≤ U := normalClosureIn_le_of_le_normalizer hUX hXN
    have hO : goldschmidtOddCore M = ⊥ := goldschmidtOddCore_eq_bot_of_isPGroup (hU2.to_le hMU)
    refine ⟨goldschmidtLayer_eq_bot_of_comm fun a b => ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have h := hUab.is_comm.comm (⟨a, hMU a.2⟩ : U) ⟨b, hMU b.2⟩
      exact Subtype.ext (congrArg Subtype.val h : (a : G) * b = b * a)
    · rw [oddCoreOf, hO, Subgroup.map_bot, Subgroup.commutator_bot_left]
  · rintro ⟨hK1, hK2⟩
    exact (hC4 hK1).2 hK2

end CFSG.Goldschmidt
