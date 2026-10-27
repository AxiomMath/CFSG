module

import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.Quasithin.Background.A1cA133
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Data

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem exists_pElem_inf_component_pow {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {L B E : Subgroup Y} (hEp : IsPGroup p E) (hEc : IsMulCommutative E)
    (hE3 : 3 ≤ CFSG.Open.pRank p E) (hB : CFSG.Open.pRank p B ≤ 3) (hEB : E ≤ B)
    (hEL : E ≤ Subgroup.normalizer (L : Set Y))
    (hcop : ∀ w ∈ L ⊓ B, w ∈ Subgroup.centralizer (L : Set Y) → w ^ p = 1 → w = 1)
    {z : Y} (hzE : z ∈ E) (hzp : z ^ p = 1) (hzL : z ∉ Subgroup.centralizer (L : Set Y))
    {j : Y} (hj : j ∈ L ⊓ B) (hzj : z * j⁻¹ ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ y ∈ E, y ∈ L ∧ y ≠ 1 ∧ y ^ p = 1 ∧ ∃ k : ℕ,
      y * (z ^ k)⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hcLB, hcE, hzc⟩ := exists_fixed_inner_of_coprime hEp hEc hEB hEL hcop hzE hj hzj
  set C := Subgroup.centralizer (L : Set Y) with hC
  set d := z * c⁻¹ with hd
  have hzdc : z = d * c := by rw [hd, inv_mul_cancel_right]
  have hdc : d * c = c * d := (Subgroup.mem_centralizer_iff.mp hzc c hcLB.1).symm
  have hdvd : p ∣ orderOf c := by
    by_contra hnd
    have hzn : z ^ orderOf c = d ^ orderOf c := by
      rw [hzdc, (Commute.mul_pow hdc), pow_orderOf_eq_one, mul_one]
    have hznC : z ^ orderOf c ∈ C := hzn ▸ C.pow_mem hzc _
    have hcopn : Nat.Coprime (orderOf c) p :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopn hp.one_lt
    have hzm : (z ^ orderOf c) ^ m = z := by
      rw [← pow_mul, ← Nat.div_add_mod (orderOf c * m) p, hm, pow_add, pow_mul, hzp, one_pow,
        one_mul, pow_one]
    exact hzL (hzm ▸ C.pow_mem hznC m)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers c) p
    (by rw [Nat.card_zpowers]; exact hdvd)
  have hyp : orderOf (y : Y) = p := by rw [Subgroup.orderOf_coe, hy]
  have hyc : (y : Y) ∈ Subgroup.zpowers c := y.2
  have hyLB : (y : Y) ∈ L ⊓ B := (Subgroup.zpowers_le.mpr hcLB) hyc
  have hyC : (y : Y) ∈ Subgroup.centralizer (E : Set Y) :=
    (Subgroup.zpowers_le.mpr hcE) hyc
  have hy1 : (y : Y) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyp
    exact hp.one_lt.ne hyp
  have hyp' : (y : Y) ^ p = 1 := hyp ▸ pow_orderOf_eq_one _
  have hyE : (y : Y) ∈ E := by
    by_contra hyE
    have h1 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers E hyp' hy1 hyC
      (zpowers_inf_eq_bot_of_not_mem' hp hyp hyE)
    have h2 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (sup_le hEB (Subgroup.zpowers_le.mpr hyLB.2))
    omega
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr hyc
  refine ⟨y, hyE, hyLB.1, hy1, hyp', k, ?_⟩
  have hzk : z ^ k = d ^ k * c ^ k := by rw [hzdc, Commute.mul_pow hdc]
  rw [← hk, hzk, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact C.inv_mem (C.pow_mem hzc k)

theorem card_rbar_inf_of_unitary (hSTO : KFactSmallThreeOrders) (hU : IsSmallUnitary 3 K)
    (T : Sylow 3 K) (hT : (T : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K) :
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, T.card_eq_multiplicity,
    (hSTO K).1 hU, show (6048 : ℕ) = 3 ^ 3 * 224 by norm_num,
    Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 224)]
  simp

theorem D1OneSmallData.exists_ne_comm_of_cube (hShape : KFactSmallSylowShape)
    (hd : D1OneSmallData 3 P M H R Rbar K)
    (hcT : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 3 ^ 3) :
    ∃ a ∈ d1LiftX 3 H R K, ∃ b ∈ d1LiftX 3 H R K, a * b ≠ b * a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨T₁, hT₁, hs, hnab, hcat, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  have hT₁card : Nat.card T₁ = 3 ^ 3 := by
    rw [← hcT, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  rcases hShape K hs hnab hcat 3 hp (by norm_num) T₁ hT₁nc hΓ hd.small with h | ⟨-, hZ⟩
  · rw [hT₁card] at h
    norm_num at h
  have hnc : ∃ a b : (T₁ : Subgroup K), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center (T₁ : Subgroup K) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hcon y x
    rw [htop, Subgroup.card_top, hT₁card] at hZ
    norm_num at hZ
  obtain ⟨a, b, hab⟩ := hnc
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hlift : ∀ c : (T₁ : Subgroup K), ∃ t : H, t ∈ R.subgroupOf H ∧ π t ∈ K ∧
      π t = ((c : K) : H ⧸ primeComplementCore (G := H) 3) := by
    intro c
    have hc' : ((c : K) : H ⧸ primeComplementCore (G := H) 3) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K := by
      rw [← hT₁]
      exact ⟨c, c.2, rfl⟩
    obtain ⟨hcR, hcK⟩ := hc'
    rw [hd.cfg.rbar] at hcR
    obtain ⟨t, ht, hteq⟩ := hcR
    exact ⟨t, ht, hteq ▸ hcK, hteq⟩
  obtain ⟨s, hsR, hsK, hseq⟩ := hlift a
  obtain ⟨t, htR, htK, hteq⟩ := hlift b
  refine ⟨s, ⟨s, ⟨hsR, hsK⟩, rfl⟩, t, ⟨t, ⟨htR, htK⟩, rfl⟩, fun hst => hab ?_⟩
  have h1 : π (s * t) = π (t * s) := by
    congr 1
    exact Subtype.ext hst
  rw [map_mul, map_mul, hseq, hteq] at h1
  exact Subtype.ext (Subtype.ext h1)

theorem D1OneSmallData.centerOf_le_commutator_of_cube (hShape : KFactSmallSylowShape)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hcT : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 3 ^ 3) :
    d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G) ≤
      ⁅d1LiftX 3 H R K, d1LiftX 3 H R K⁆ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set X := d1LiftX 3 H R K with hXdef
  have hXcard : Nat.card X = 3 ^ 3 := (hd.d1LiftX_facts hz).2.trans hcT
  have hnab := hd.exists_ne_comm_of_cube hShape hcT
  have hTp : IsPGroup 3 ↥X := IsPGroup.of_card hXcard
  have : Group.IsNilpotent ↥X := hTp.isNilpotent
  set N : Subgroup ↥X := ⁅(⊤ : Subgroup ↥X), ⊤⁆
  have hN : N ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have h1 : _ ∈ N := Subgroup.commutator_mem_commutator (G := ↥X)
      (Subgroup.mem_top (⟨a, ha⟩ : ↥X)) (Subgroup.mem_top (⟨b, hb⟩ : ↥X))
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab (congrArg Subtype.val h1)
  have hNZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  have hZcard : Nat.card (Subgroup.center ↥X) = 3 := by
    rw [← card_centerOf_of_nonabelian hXcard hnab, A1c.centerOf_eq_map_center,
      Subgroup.card_map_of_injective X.subtype_injective]
  have hZle : Subgroup.center ↥X ≤ N := by
    have h1 : Nat.card (N ⊓ Subgroup.center ↥X : Subgroup ↥X) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hNZ
    · have := Subgroup.eq_of_le_of_card_ge (inf_le_right : N ⊓ Subgroup.center ↥X ≤ _)
        (by rw [hZcard, h])
      exact this ▸ inf_le_left
  rw [show X ⊓ Subgroup.centralizer (X : Set G) = centerOf X from rfl,
    A1c.centerOf_eq_map_center]
  calc (Subgroup.center ↥X).map X.subtype ≤ N.map X.subtype := Subgroup.map_mono hZle
    _ = ⁅X, X⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem not_mem_normalizer_line_barM {M X : Subgroup G}
    (hX3 : ∀ x ∈ X, x ^ 3 = 1) {t : G} (htM : t ∈ M)
    (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hline : ∀ F : Subgroup G, F ≤ X → Nat.card F = 3 → t ∉ Subgroup.normalizer (F : Set G))
    (F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hFX : F ≤ barM M X) (hF3 : Nat.card F = 3) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ∉
      Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro htF
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hcop2 : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by decide)).pow_right k
  have hinj : ∀ a b : M, (a : G) ∈ X → (b : G) ∈ X → mk a = mk b → a = b := by
    intro a b ha hb hab
    have h1 : mk (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : (a⁻¹ * b) ^ 3 ^ 1 = 1 :=
      Subtype.ext (by simpa using hX3 _ (X.mul_mem (X.inv_mem ha) hb))
    exact inv_mul_eq_one.mp (eq_one_of_mk_eq_one_of_coprime _ hcop2 h2 h1)
  obtain ⟨f, hfF, hf1⟩ : ∃ f ∈ F, f ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall F).mpr h, Subgroup.card_bot] at hF3
    norm_num at hF3
  obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := hFX hfF
  have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hx1 : x ≠ 1 := fun h => hf1 (by
    have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext h
    rw [this, map_one])
  have hxo : orderOf x = 3 := orderOf_eq_prime (hX3 x hxX') hx1
  have hfo : orderOf (mk ⟨x, hxM⟩) = 3 := by
    refine orderOf_eq_prime ?_ hf1
    rw [← map_pow]
    have : (⟨x, hxM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hX3 x hxX')
    rw [this, map_one]
  have hFz : Subgroup.zpowers (mk ⟨x, hxM⟩) = F :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfF)
      (by rw [Nat.card_zpowers, hfo, hF3])
  have hconj := (Subgroup.mem_normalizer_iff.mp htF (mk ⟨x, hxM⟩)).mp hfF
  rw [← hFz, Subgroup.mem_zpowers_iff] at hconj
  obtain ⟨k, hk⟩ := hconj
  have htxX : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htX x).mp hxX'
  have heq : (⟨t, htM⟩ : M) * ⟨x, hxM⟩ * (⟨t, htM⟩ : M)⁻¹ = (⟨x, hxM⟩ : M) ^ k := by
    refine hinj _ _ htxX ?_ ?_
    · simpa using X.zpow_mem hxX' k
    · rw [map_mul, map_mul, map_inv, map_zpow, hk]
  have htx : t * x * t⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using (congrArg Subtype.val heq).symm⟩
  refine hline (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxX')
    (by rw [Nat.card_zpowers, hxo]) (Subgroup.mem_normalizer_fintype fun n hn => ?_)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ htx j

end CFSG.AGLEmbedding
