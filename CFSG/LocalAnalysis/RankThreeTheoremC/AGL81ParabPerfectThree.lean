module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreePerfectProof
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeTypes
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

namespace ParabPerfectThree

theorem eq_one_of_conj_eq_inv {X : Type*} [Group X] [Finite X] (hX : ¬ 2 ∣ Nat.card X)
    {g a : X} (h : g * a * g⁻¹ = a⁻¹) : a = 1 := by
  have h' : g * a⁻¹ * g⁻¹ = a := by
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group, h, inv_inv]
  have hk : ∀ k : ℕ, g ^ (2 * k + 1) * a * (g ^ (2 * k + 1))⁻¹ = a⁻¹ := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have e : g ^ (2 * (k + 1) + 1) = g * (g * g ^ (2 * k + 1)) := by
        rw [← mul_assoc, ← pow_two, ← pow_add]
        ring_nf
      calc g ^ (2 * (k + 1) + 1) * a * (g ^ (2 * (k + 1) + 1))⁻¹
          = g * (g * (g ^ (2 * k + 1) * a * (g ^ (2 * k + 1))⁻¹) * g⁻¹) * g⁻¹ := by
            rw [e]
            group
        _ = a⁻¹ := by rw [ih, h', h]
  have hodd : Odd (orderOf g) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => hX (h2.trans (orderOf_dvd_natCard g)))
  obtain ⟨k, hkg⟩ := hodd
  have hinv := hk k
  rw [← hkg, pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hinv
  have ha2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]
    nth_rewrite 2 [hinv]
    exact mul_inv_cancel a)
  rcases (Nat.dvd_prime Nat.prime_two).mp ha2 with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h2 ▸ orderOf_dvd_natCard a) hX

theorem false_of_invThree_normal {X : Type*} [Group X] [Finite X] {N B T : Subgroup X}
    [hN : N.Normal] (hNB : N ⊔ B = ⊤) (hTB : T ≤ B) (hBT : B ≤ normalizer (T : Set X))
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.relIndex B) (h3 : ¬ 3 ∣ Nat.card N)
    (hinv : InvThree (⊤ : Subgroup X)) : False := by
  classical
  set K : Subgroup X := N ⊔ T with hK
  have hKn : K.Normal := by
    constructor
    intro k hk g
    have hg : g ∈ N ⊔ B := hNB ▸ Subgroup.mem_top g
    obtain ⟨n, hn, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨m, hm, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    have hbm : b * m * b⁻¹ ∈ N := hN.conj_mem m hm b
    have hbt : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
    have e : n * b * (m * t) * (n * b)⁻¹ =
        (n * (b * m * b⁻¹) * n⁻¹) * ((n * ((b * t * b⁻¹) * n⁻¹ * (b * t * b⁻¹)⁻¹)) *
          (b * t * b⁻¹)) := by group
    rw [e]
    refine K.mul_mem (Subgroup.mem_sup_left (hN.conj_mem _ hbm n)) (K.mul_mem ?_
      (Subgroup.mem_sup_right hbt))
    exact Subgroup.mem_sup_left (N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) _))
  have hKidx : ¬ 2 ∣ K.index := by
    have htop : B ⊔ K = ⊤ := top_le_iff.mp (hNB ▸ sup_le
      ((le_sup_left : N ≤ K).trans le_sup_right) le_sup_left)
    have h1 : K.index = K.relIndex B := by
      rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
    rw [h1]
    exact fun h2 => hodd (h2.trans (Subgroup.relIndex_dvd_of_le_left B le_sup_right))
  obtain ⟨a, -, g, -, ha3, hga⟩ := hinv
  have haK : a ∈ K := by
    set π := QuotientGroup.mk' K
    have hπ : π g * π a * (π g)⁻¹ = (π a)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul, hga, map_inv]
    have := eq_one_of_conj_eq_inv (X := X ⧸ K) hKidx hπ
    exact (QuotientGroup.eq_one_iff a).mp this
  obtain ⟨n, hn, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp haK
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have ht' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set ρ := QuotientGroup.mk' N
  have hρ : ρ (n * t) = ρ t := by
    have hρn : ρ n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, hρn, one_mul]
  have h1 : orderOf (ρ (n * t)) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
    rw [← map_pow, ← ha3, pow_orderOf_eq_one, map_one])
  have h2 : orderOf (ρ (n * t)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [hρ, ← map_pow, ht', map_one])
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hρ1 : ρ (n * t) = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hntN : n * t ∈ N := (QuotientGroup.eq_one_iff _).mp hρ1
  exact h3 (ha3 ▸ Subgroup.orderOf_dvd_natCard N hntN)

theorem false_of_invThree {X : Type*} [Group X] [Finite X] {N B T : Subgroup X}
    (hBN : B ≤ normalizer (N : Set X)) (hTB : T ≤ B) (hBT : B ≤ normalizer (T : Set X))
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.relIndex B) (h3 : ¬ 3 ∣ Nat.card N)
    (hinv : InvThree (N ⊔ B)) : False := by
  set J := N ⊔ B
  have hNJ : N ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  haveI : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr (sup_le Subgroup.le_normalizer hBN)
  refine false_of_invThree_normal (N := N.subgroupOf J) (B := B.subgroupOf J)
    (T := T.subgroupOf J) ?_ (fun x hx => hTB hx) ?_ hT.comap_subtype ?_ ?_ ?_
  · rw [← Subgroup.subgroupOf_sup hNJ hBJ, Subgroup.subgroupOf_self]
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hBT hx) y
  · rwa [Subgroup.relIndex_subgroupOf hBJ]
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv]
  · obtain ⟨a, ha, g, hg, ha3, hga⟩ := hinv
    exact ⟨⟨a, ha⟩, Subgroup.mem_top _, ⟨g, hg⟩, Subgroup.mem_top _,
      (Subgroup.orderOf_coe (⟨a, ha⟩ : J)).symm.trans ha3, Subtype.ext (by simpa using hga)⟩

theorem eq_bot_of_perfect_of_le {X : Type*} [Group X] [Finite X] {C B T : Subgroup X}
    (hCB : C ≤ B) (hTB : T ≤ B) (hBT : B ≤ normalizer (T : Set X)) (hT : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ T.relIndex B) (hC : ⁅C, C⁆ = C) : C = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup ↥C := T.subgroupOf C
  haveI hT'n : T'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hBT (hCB g.2)) x).mp hx⟩
  have hidx : ¬ 2 ∣ Nat.card (↥C ⧸ T') := by
    change ¬ 2 ∣ T'.index
    haveI : (T.subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).mpr hBT
    have h1 : T'.index = (T.subgroupOf B).relIndex (C.subgroupOf B) :=
      (Subgroup.relIndex_subgroupOf hCB).symm
    rw [h1]
    exact fun h2 => hodd (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
  haveI : Group.IsSolvable (↥C ⧸ T') :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx))
  set π := QuotientGroup.mk' T'
  have hCt : ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hC]
  have hQt : ⁅(⊤ : Subgroup (↥C ⧸ T')), (⊤ : Subgroup (↥C ⧸ T'))⁆ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective T'),
      ← Subgroup.map_commutator, hCt]
  have hbot := CZeroThreePerfect.eq_bot_of_perfect_of_isSolvable hQt
  have hCT : C ≤ T := by
    intro x hx
    have hm : π ⟨x, hx⟩ ∈ (⊤ : Subgroup (↥C ⧸ T')) := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at hm
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hm)
  exact CZeroThreePerfect.eq_bot_of_perfect_of_isPGroup (hT.to_le hCT) hC

end ParabPerfectThree

open ParabPerfectThree

theorem kFactParabolicPerfectThree_of (hPI : KFactParabolicThreeInv) :
    KFactParabolicPerfectThree := by
  intro A _ _ Y P _ _ hcl hP C hCP hC1 hCperf hCsn
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h3C
  obtain ⟨hPY, T, hT, hNT⟩ := hP
  set N : Subgroup A := (CFSG.pPrimeCore 3 ↥P).map P.subtype with hN
  have hNP : N ≤ P := Subgroup.map_subtype_le _
  have hNY : N ≤ Y := hNP.trans hPY
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hN, Subgroup.card_map_of_injective P.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hCN : C ≤ N := by
    have hcop : Nat.Coprime 3 (Nat.card (C.subgroupOf P)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3C
    have h := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hCsn hcop
    intro x hx
    exact ⟨⟨x, hCP hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hPN : P ≤ normalizer (N : Set A) := by
    haveI : (N.subgroupOf P).Normal := by
      change (N.comap P.subtype).Normal
      rw [hN, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
      exact CFSG.pPrimeCore_normal
    exact Subgroup.le_normalizer_of_normal_subgroupOf hNP
  set q := QuotientGroup.mk' (center ↥Y)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hTy : IsSylowTwoOf (T.subgroupOf Y) ⊤ := isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  set Tb := (T.subgroupOf Y).map q
  have hTb : IsSylowTwoOf Tb ⊤ := isSylowTwoOf_map_top_of_surjective hTy hq
  set Nb := (N.subgroupOf Y).map q
  set Bb := normalizer (Tb : Set (↥Y ⧸ center ↥Y))
  have hlift : ∀ z : ↥Y, q z ∈ Bb → (z : A) ∈ Y ⊓ normalizer (T : Set A) := fun z hz =>
    ⟨z.2, coe_mem_normalizer_of_subgroupOf hT.1
      (mem_normalizer_of_mk_center_mem_normalizer hTy hz)⟩
  have hBN : Bb ≤ normalizer (Nb : Set (↥Y ⧸ center ↥Y)) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hq y
    have hzN : (z : A) ∈ normalizer (N : Set A) := hPN (hNT (hlift z hy))
    have hz' : z ∈ normalizer ((N.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
      rw [Subgroup.mem_normalizer_iff] at hzN ⊢
      intro w
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using hzN w
    exact Subgroup.le_normalizer_map q ⟨z, hz', rfl⟩
  have hTB : T ≤ Y ⊓ normalizer (T : Set A) := fun t ht => ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hoddB : ¬ 2 ∣ T.relIndex (Y ⊓ normalizer (T : Set A)) := fun h2 =>
    hT.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T _ Y hTB inf_le_left)))
  by_cases hJ : Nb ⊔ Bb = Bb
  ·
    have hNB : N ≤ Y ⊓ normalizer (T : Set A) := fun x hx =>
      hlift ⟨x, hNY hx⟩ (hJ ▸ Subgroup.mem_sup_left
        (Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hx)))
    exact hC1 (eq_bot_of_perfect_of_le (hCN.trans hNB) hTB inf_le_right hT.2.1 hoddB hCperf)
  ·
    have hinv := hPI (↥Y ⧸ center ↥Y) hcl Tb (Nb ⊔ Bb) hTb le_sup_right hJ
    refine false_of_invThree hBN Subgroup.le_normalizer le_rfl hTb.2.1 ?_ ?_ hinv
    · have h : ¬ 2 ∣ Tb.relIndex ⊤ := hTb.2.2
      rw [Subgroup.relIndex_top_right] at h
      exact fun h2 => h (h2.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
    · intro h3
      apply hN3
      refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv]

end CFSG.LocalAnalysis.RankThreeTheoremC
