module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {K L : Subgroup G} {n : ℕ}

section Order

theorem two_pow_dvd_card_K [Finite G] (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥)
    (hLK : L ≤ K) : 2 ^ (3 * n) ∣ Nat.card K := by
  have hU : Nat.card (blockU L) = 2 ^ (2 * n) := card_blockU hl hZ
  have h1 : 2 ^ (2 * n) ∣ Nat.card (pCoreOf 2 L) :=
    hU ▸ Subgroup.card_dvd_of_le (C1.blockU_le_blockQ hs)
  have h2 := lin2_card_L hl
  have h3 : 2 ^ (3 * n) ∣ Nat.card L := by
    rw [h2, show 3 * n = 2 * n + n by ring, pow_add]
    exact mul_dvd_mul h1 (dvd_mul_right _ _)
  exact h3.trans (Subgroup.card_dvd_of_le hLK)

end Order

section InK

theorem isElemAbelian_subgroupOf {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem card_blockU_subgroupOf [Finite G] (hl : IsLin2Type L n) (hZ : blockZ L = ⊥)
    (hs : IsShort2 L) (hLK : L ≤ K) : Nat.card ((blockU L).subgroupOf K) = 2 ^ (2 * n) := by
  have hUK : blockU L ≤ K := (blockU_le_L hs).trans hLK
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
  exact card_blockU hl hZ

theorem subgroupOf_le_normalizer [Finite G] :
    L.subgroupOf K ≤ Subgroup.normalizer (((blockU L).subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hl' : (l : G) ∈ L := hl
  have h := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L hl') (u : G))
  simpa [Subgroup.mem_subgroupOf] using h

theorem not_isSolvable_subgroupOf (hl : IsLin2Type L n) (hn : 2 ≤ n) (hLK : L ≤ K) :
    ¬ Group.IsSolvable ↥(L.subgroupOf K) := by
  intro h
  have : Group.IsSolvable ↥L := by
    have e := Subgroup.subgroupOfEquivOfLe hLK
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  exact not_isSolvable hl hn this

theorem blockU_subgroupOf_ne_bot [Finite G] (hs : IsShort2 L) (hl : IsLin2Type L n)
    (hZ : blockZ L = ⊥) (hn : 2 ≤ n) (hLK : L ≤ K) : (blockU L).subgroupOf K ≠ ⊥ := by
  have hcard := card_blockU_subgroupOf hl hZ hs hLK
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
  omega

theorem exists_blockU_K [Finite G] (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥)
    (hn : 2 ≤ n) (hLK : L ≤ K) :
    ∃ Ub : Subgroup ↥K, Ub ≠ ⊥ ∧ IsElemAbelian 2 Ub ∧ Nat.card Ub = 2 ^ (2 * n) ∧
      L.subgroupOf K ≤ Subgroup.normalizer (Ub : Set ↥K) ∧ ¬ Group.IsSolvable ↥(L.subgroupOf K) :=
  ⟨(blockU L).subgroupOf K, blockU_subgroupOf_ne_bot hs hl hZ hn hLK,
    isElemAbelian_subgroupOf (isElemAbelian_blockU hs),
    card_blockU_subgroupOf hl hZ hs hLK, subgroupOf_le_normalizer,
    not_isSolvable_subgroupOf hl hn hLK⟩

theorem exists_norm_elem_K [Finite G] (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥)
    (hn : 2 ≤ n) (hLK : L ≤ K) {ℓ : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ∣ 2 ^ (2 * n) - 1) :
    ∃ (x : ↥K) (Ub : Subgroup ↥K), orderOf x = ℓ ∧ Ub ≠ ⊥ ∧ IsElemAbelian 2 Ub ∧
      x ∈ Subgroup.normalizer (Ub : Set ↥K) := by
  obtain ⟨Ub, hU1, hUe, -, hnorm, -⟩ := exists_blockU_K hs hl hZ hn hLK
  obtain ⟨x, hxL, hx⟩ := exists_orderOf_eq_prime hl hℓ hdvd
  refine ⟨⟨x, hLK hxL⟩, Ub, ?_, hU1, hUe, hnorm ?_⟩
  · exact ((Subgroup.orderOf_coe (⟨x, hLK hxL⟩ : ↥K)).symm).trans hx
  · exact hxL

end InK

section Quotient

theorem pCore_le_center {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) :
    CFSG.pCore 2 X ≤ Subgroup.center X := by
  have hq' : CFSG.Open.IsQuasisimple X := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup X) := h ▸ CFSG.pCore_isPGroup (p := 2) (G := X)
    have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect X := hq.1
    have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hq'
    exact Group.IsPerfect.not_isSolvable X inferInstance

theorem blockU_inf_pCore [Finite G] (hq : CFSG.IsQuasisimple ↥K) (hZ : blockZ L = ⊥) (hLK : L ≤ K) :
    ∀ u ∈ (blockU L).subgroupOf K, u ∈ CFSG.pCore 2 ↥K → u = 1 := by
  intro u hu hN
  have hc : u ∈ Subgroup.center ↥K := pCore_le_center hq hN
  have hc2 : (u : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hLK hl⟩)
  have hZ' : (u : G) ∈ blockZ L := ⟨hu, hc2⟩
  rw [hZ, Subgroup.mem_bot] at hZ'
  exact Subtype.ext hZ'

theorem exists_blockU_quot [Finite G] (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥)
    (hq : CFSG.IsQuasisimple ↥K) (hLK : L ≤ K) :
    ∃ Ub : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), IsElemAbelian 2 Ub ∧ Nat.card Ub = 2 ^ (2 * n) := by
  have hUK : blockU L ≤ K := (blockU_le_L hs).trans hLK
  refine ⟨((blockU L).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)),
    isElemAbelian_map' (isElemAbelian_subgroupOf (isElemAbelian_blockU hs)) _, ?_⟩
  rw [card_map_of_inf_ker_eq_bot _ _ ?_]
  · exact card_blockU_subgroupOf hl hZ hs hLK
  · intro x hx hx1
    exact blockU_inf_pCore hq hZ hLK x hx ((QuotientGroup.eq_one_iff x).mp hx1)

theorem exists_norm_elem_quot [Finite G] (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥)
    (hn : 2 ≤ n) (hq : CFSG.IsQuasisimple ↥K) (hLK : L ≤ K) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hdvd : ℓ ∣ 2 ^ (2 * n) - 1) :
    ∃ (x : ↥K ⧸ CFSG.pCore 2 ↥K) (Ub : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)), orderOf x = ℓ ∧
      Ub ≠ ⊥ ∧ IsElemAbelian 2 Ub ∧ x ∈ Subgroup.normalizer (Ub : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hUK : blockU L ≤ K := (blockU_le_L hs).trans hLK
  have hU1 := blockU_subgroupOf_ne_bot hs hl hZ hn hLK
  have hUe := isElemAbelian_subgroupOf (K := K) (isElemAbelian_blockU hs)
  obtain ⟨x, hxL, hx⟩ := exists_orderOf_eq_prime hl hℓ hdvd
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set x' : ↥K := ⟨x, hLK hxL⟩ with hx'
  have hx'ord : orderOf x' = ℓ := ((Subgroup.orderOf_coe x').symm).trans hx
  have hker : ∀ y ∈ (blockU L).subgroupOf K, π y = 1 → y = 1 := fun y hy hy1 =>
    blockU_inf_pCore hq hZ hLK y hy ((QuotientGroup.eq_one_iff y).mp hy1)
  refine ⟨π x', ((blockU L).subgroupOf K).map π, ?_, ?_, isElemAbelian_map' hUe π, ?_⟩
  · have hpow : (π x') ^ ℓ = 1 := by rw [← map_pow, ← hx'ord, pow_orderOf_eq_one, map_one]
    have hne : π x' ≠ 1 := by
      intro h1
      have hxN : x' ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff x').mp h1
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨x', hxN⟩
      have hdvd2 : orderOf x' ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      rw [hx'ord] at hdvd2
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow hdvd2))
    exact orderOf_eq_prime hpow hne
  · intro hbot
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
    have hmem : π u.1 ∈ ((blockU L).subgroupOf K).map π := Subgroup.mem_map_of_mem π u.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 (Subtype.ext (hker u.1 u.2 hmem))
  · exact Subgroup.le_normalizer_map π
      (Subgroup.mem_map_of_mem π (subgroupOf_le_normalizer (show x' ∈ L.subgroupOf K from hxL)))

end Quotient

end CFSG.QuasithinUnique.Lin2.OddRank
