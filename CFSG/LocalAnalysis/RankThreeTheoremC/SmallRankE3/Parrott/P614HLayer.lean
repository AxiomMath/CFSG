module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HBasic
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open Subgroup

theorem mulAut_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (σ τ : MulAut C) :
    σ * τ = τ * σ :=
  (IsCyclic.mulAutMulEquiv C).injective (by rw [map_mul, map_mul, mul_comm])

theorem commutator_le_centralizer_of_isCyclic {Y : Type*} [Group Y] (E : Subgroup Y) [E.Normal]
    [IsCyclic E] : commutator Y ≤ centralizer (E : Set Y) := by
  haveI : IsMulCommutative (MulAut E) := ⟨⟨mulAut_comm_of_isCyclic⟩⟩
  intro g hg
  have h := Abelianization.commutator_subset_ker (MulAut.conjNormal (H := E)) hg
  rw [MonoidHom.mem_ker] at h
  rw [mem_centralizer_iff]
  intro e he
  have h1 := congrArg (fun φ : MulAut E => ((φ ⟨e, he⟩ : E) : Y)) h
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc e * g = g * e * g⁻¹ * g := by rw [h1]
    _ = g * e := by group

theorem false_of_isComponent {Y : Type*} [Group Y] [Finite Y] (hcore : CFSG.pPrimeCore 3 Y = ⊥)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) {E : Subgroup Y} [E.Normal]
    (hE : IsPGroup 3 E) {w : Y} (hwE : w ∈ E) (hw : orderOf w = 3) {L : Subgroup Y}
    (hL : CFSG.IsComponent L) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw3 : w ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw] at h
  haveI hEc : IsCyclic E := isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hE
    ((CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hrank)
  have hcomm := commutator_le_centralizer_of_isCyclic E
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL.1.1
  have hLY : L ≤ commutator Y := by
    rw [commutator_def]
    nth_rewrite 1 [← hLperf]
    exact commutator_mono le_top le_top
  have hLW : L ≤ normalClosure (L : Set Y) := subset_normalClosure
  have hWY : normalClosure (L : Set Y) ≤ commutator Y := normalClosure_le_normal hLY
  have hWcent : normalClosure (L : Set Y) ≤ centralizer (E : Set Y) := hWY.trans hcomm
  have hWperf : ⁅normalClosure (L : Set Y), normalClosure (L : Set Y)⁆ =
      normalClosure (L : Set Y) := by
    refine le_antisymm (commutator_le_left _ _) (normalClosure_le_normal ?_)
    nth_rewrite 1 [← hLperf]
    exact commutator_mono hLW hLW
  have hLne : L ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext (mem_bot.1 (hbot.le a.2))
    have hb : b = 1 := Subtype.ext (mem_bot.1 (hbot.le b.2))
    apply hab
    rw [ha, hb]
  have h3 : 3 ∣ Nat.card (normalClosure (L : Set Y)) := by
    by_contra h
    have hle : normalClosure (L : Set Y) ≤ CFSG.pPrimeCore 3 Y :=
      le_sSup (s := {N : Subgroup Y | N.Normal ∧ Nat.Coprime 3 (Nat.card N)})
        ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h⟩
    rw [hcore, le_bot_iff] at hle
    exact hLne (le_bot_iff.1 (hle ▸ hLW))
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := normalClosure (L : Set Y)) 3 h3
  have hu' : orderOf (u : Y) = 3 := by rw [Subgroup.orderOf_coe, hu]
  have hu3 : (u : Y) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (u : Y)
    rwa [hu'] at h
  have huw : w * (u : Y) = u * w := mem_centralizer_iff.mp (hWcent u.2) w hwE
  have hwW : w ∈ normalClosure (L : Set Y) := by
    by_contra hnot
    have hwu : w ∉ zpowers (u : Y) := fun h => hnot (zpowers_le.mpr u.2 h)
    have hc : ∀ a ∈ zpowers (u : Y), ∀ b ∈ zpowers w, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow (show Commute (u : Y) w from huw.symm) i j).eq
    have hel : IsElemAbelian 3 (zpowers (u : Y) ⊔ zpowers w) :=
      (CFSG.Open.isElemAbelian_zpowers hu3).sup_of_commute (CFSG.Open.isElemAbelian_zpowers hw3)
        hc
    have hnorm : zpowers w ≤ normalizer (zpowers (u : Y) : Set Y) := by
      rw [zpowers_le]
      exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => hc a ha w
        (mem_zpowers w))
    have hdisj : Disjoint (zpowers (u : Y)) (zpowers w) := by
      rw [Subgroup.disjoint_def]
      intro y hyu hyw
      have : Fact (Nat.card (zpowers w)).Prime := ⟨by rw [Nat.card_zpowers, hw]; norm_num⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((zpowers (u : Y)).subgroupOf (zpowers w))
        with h | h
      · have hy : (⟨y, hyw⟩ : zpowers w) ∈ (zpowers (u : Y)).subgroupOf (zpowers w) := hyu
        rw [h] at hy
        exact congrArg Subtype.val (Subgroup.mem_bot.1 hy)
      · exfalso
        have hf : (⟨w, mem_zpowers w⟩ : zpowers w) ∈ (zpowers (u : Y)).subgroupOf (zpowers w) := by
          rw [h]
          trivial
        exact hwu hf
    have hcard : Nat.card (zpowers (u : Y) ⊔ zpowers w : Subgroup Y) = 3 ^ 2 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
        Nat.card_zpowers, Nat.card_zpowers, hu', hw]
      norm_num
    have := CFSG.SectionRank.le_pRank (by norm_num) le_top hel hcard
    omega
  have hperfW : commutator (normalClosure (L : Set Y)) = ⊤ := by
    apply map_injective (normalClosure (L : Set Y)).subtype_injective
    rw [map_subtype_commutator, hWperf, ← MonoidHom.range_eq_map, range_subtype]
  set w' : normalClosure (L : Set Y) := ⟨w, hwW⟩ with hw'def
  have hw'c : w' ∈ center (normalClosure (L : Set Y)) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp (hWcent g.2) w hwE).symm
  have hw'3 : w' ^ 3 = 1 := Subtype.ext (by simpa [hw'def] using hw3)
  obtain ⟨S₃, hS₃⟩ := ((CFSG.Open.isElemAbelian_zpowers hw'3).isPGroup).exists_le_sylow
  have hS₃c : IsCyclic ((S₃ : Subgroup (normalClosure (L : Set Y))).map
      (normalClosure (L : Set Y)).subtype) :=
    isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) (S₃.isPGroup'.map _)
      ((CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hrank)
  haveI : IsCyclic (S₃ : Subgroup (normalClosure (L : Set Y))) :=
    isCyclic_of_injective ((normalClosure (L : Set Y)).subtype.subgroupMap
      (S₃ : Subgroup (normalClosure (L : Set Y))))
      (fun a b h => Subtype.ext (Subtype.ext (by
        have := congrArg Subtype.val h
        simpa using this)))
  have hw'1 := eq_one_of_mem_center_of_perfect hperfW S₃ inferInstance hw'c
    (hS₃ (mem_zpowers w'))
  have : w = 1 := congrArg Subtype.val hw'1
  rw [this, orderOf_one] at hw
  norm_num at hw

theorem pLayer_eq_bot {X : Type*} [Group X] [Finite X]
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {D E : Subgroup X} [D.Normal] [E.Normal]
    (hD : Nat.Coprime 3 (Nat.card D)) (hDE : ∀ e ∈ E, ∃ n : ℕ, e ^ 3 ^ n ∈ D) {w : X}
    (hwE : w ∈ E) (hw : orderOf w = 3) : CFSG.pLayer X 3 = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  apply sSup_le
  rintro L ⟨K₁, hK₁, -, -, -⟩
  exfalso
  have hDO : D ≤ CFSG.pPrimeCore 3 X :=
    le_sSup (s := {N : Subgroup X | N.Normal ∧ Nat.Coprime 3 (Nat.card N)}) ⟨inferInstance, hD⟩
  have hcore := CFSG.pPrimeCore_quotient_eq_bot (G := X) Nat.prime_three
  have hrank' : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)))]
    exact hrank
  haveI : (E.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hE' : IsPGroup 3 (E.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
    rintro ⟨_, ⟨e, he, rfl⟩⟩
    obtain ⟨n, hn⟩ := hDE e he
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hDO hn)
  have hw3 : w ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw] at h
  have hw' : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) w) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hw3, map_one]
    · intro h
      have hwO : w ∈ CFSG.pPrimeCore 3 X := (QuotientGroup.eq_one_iff w).mp h
      have h1 := Subgroup.orderOf_dvd_natCard _ hwO
      rw [hw] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)) h1
  exact false_of_isComponent hcore hrank' hE' ⟨w, hwE, rfl⟩ hw' hK₁

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H
