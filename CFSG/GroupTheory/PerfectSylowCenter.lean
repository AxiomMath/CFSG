module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.GroupTheory

open Subgroup

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]

theorem center_subgroupOf_sylow_le_frattini [Group.IsPerfect Q] (P : Sylow p Q) :
    (Subgroup.center Q).subgroupOf (P : Subgroup Q) ≤
      frattini ↥(P : Subgroup Q) := by
  classical
  intro z hz
  rw [frattini, Order.radical]
  simp only [Subgroup.mem_iInf]
  intro K hK
  by_contra hzK
  haveI hPg : Fact (IsPGroup p ↥(P : Subgroup Q)) := ⟨P.isPGroup'⟩
  haveI hnil : Group.IsNilpotent ↥(P : Subgroup Q) := IsPGroup.isNilpotent P.isPGroup'
  haveI hKn : K.Normal := CFSG.coatom_normal_of_isPGroup (p := p) hK
  let π : ↥(P : Subgroup Q) →* (↥(P : Subgroup Q) ⧸ K) := QuotientGroup.mk' K
  have hindex : K.index = p :=
    (IsPGroup.isCoatom_iff_index_eq_prime (p := p) P.isPGroup' (H := K)).mp hK
  have hcard : Nat.card (↥(P : Subgroup Q) ⧸ K) = p := by
    rw [← Subgroup.index_eq_card, hindex]
  haveI hcyc : IsCyclic (↥(P : Subgroup Q) ⧸ K) := isCyclic_of_prime_card hcard
  letI : CommGroup (↥(P : Subgroup Q) ⧸ K) := IsCyclic.commGroup
  let zP : ↥(P : Subgroup Q) := ⟨(z : Q), z.2⟩
  have hzcenter : (z : Q) ∈ Subgroup.center Q := hz
  have hπz : π zP ≠ 1 := by
    intro h
    exact hzK ((QuotientGroup.eq_one_iff (N := K) (x := zP)).mp h)
  have key : ∀ k : ℕ, ∀ g₀ : Q,
      g₀⁻¹ * (z : Q) ^ k * g₀ ∈ (P : Subgroup Q) →
        g₀⁻¹ * (z : Q) ^ k * g₀ = (z : Q) ^ k := by
    intro k g₀ _
    have hc : (z : Q) ^ k ∈ Subgroup.center Q := (Subgroup.center Q).pow_mem hzcenter k
    calc g₀⁻¹ * (z : Q) ^ k * g₀ = g₀⁻¹ * ((z : Q) ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * (z : Q) ^ k) := by rw [Subgroup.mem_center_iff.mp hc g₀]
      _ = (z : Q) ^ k := by group
  have htr := MonoidHom.transfer_eq_pow π (z : Q) key
  have hval : π.transfer (z : Q) = (π zP) ^ (P : Subgroup Q).index := by
    rw [htr]
    congr 1
  have hker : π.transfer (z : Q) = 1 := by
    refine Abelianization.commutator_subset_ker π.transfer ?_
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top _
  have hpow : (π zP) ^ (P : Subgroup Q).index = 1 := hval ▸ hker
  have horder : orderOf (π zP) = p := by
    have hdvd : orderOf (π zP) ∣ p := by
      simpa [hcard] using orderOf_dvd_natCard (π zP)
    exact (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd |>.resolve_left fun h1 =>
      hπz (orderOf_eq_one_iff.mp h1)
  let i := (P : Subgroup Q).index
  have hpdvd : p ∣ i := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hpow
  exact Sylow.not_dvd_index P (by simpa [i] using hpdvd)

theorem not_isCyclic_sylow_quotient_of_center [Group.IsPerfect Q]
    (P : Sylow p Q) (hPnc : ¬ IsCyclic ↥(P : Subgroup Q)) (Z₀ : Subgroup Q) [Z₀.Normal]
    (hZ₀ : Z₀ ≤ Subgroup.center Q) :
    ∀ S : Sylow p (Q ⧸ Z₀), ¬ IsCyclic ↥(S : Subgroup (Q ⧸ Z₀)) := by
  classical
  let π : Q →* (Q ⧸ Z₀) := QuotientGroup.mk' Z₀
  let S₀ : Sylow p (Q ⧸ Z₀) := Sylow.mapSurjective (QuotientGroup.mk'_surjective Z₀) P
  have hS₀coe : (S₀ : Subgroup (Q ⧸ Z₀)) = (P : Subgroup Q).map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Z₀) P
  have hS₀nc : ¬ IsCyclic ↥(S₀ : Subgroup (Q ⧸ Z₀)) := by
    intro hcyc
    obtain ⟨g, hgS⟩ :=
      (Subgroup.isCyclic_iff_exists_zpowers_eq_top (S₀ : Subgroup (Q ⧸ Z₀))).mp hcyc
    have hg_mem : g ∈ (P : Subgroup Q).map π := by
      rw [← hS₀coe, ← hgS]
      exact Subgroup.mem_zpowers g
    obtain ⟨x, hxP, hxg⟩ := Subgroup.mem_map.mp hg_mem
    let xP : ↥(P : Subgroup Q) := ⟨x, hxP⟩
    have hZ₀P : Z₀.subgroupOf (P : Subgroup Q) ≤ frattini ↥(P : Subgroup Q) :=
      (Subgroup.subgroupOf_mono (P : Subgroup Q) hZ₀).trans
        (center_subgroupOf_sylow_le_frattini P)
    have hsup : Subgroup.zpowers xP ⊔ frattini ↥(P : Subgroup Q) = ⊤ := by
      rw [eq_top_iff]
      intro pP _
      have hπp : π (pP : Q) ∈ Subgroup.zpowers g := by
        rw [hgS]
        exact Subgroup.mem_map_of_mem π pP.2
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hπp
      have hker : pP * (xP ^ i)⁻¹ ∈ Z₀.subgroupOf (P : Subgroup Q) := by
        refine Subgroup.mem_subgroupOf.mpr ?_
        refine (QuotientGroup.eq_one_iff (x := (pP : Q) * ((xP : Q) ^ i)⁻¹)).mp ?_
        have hmap : π ((pP : Q) * ((xP : Q) ^ i)⁻¹) = π (pP : Q) * (g ^ i)⁻¹ := by
          rw [map_mul, map_inv, map_zpow, hxg]
        show π ((pP : Q) * ((xP : Q) ^ i)⁻¹) = 1
        rw [hmap, ← hi]
        exact mul_inv_cancel _
      have hdec : pP = (pP * (xP ^ i)⁻¹) * xP ^ i := by group
      have hmem : pP ∈ Z₀.subgroupOf (P : Subgroup Q) ⊔ Subgroup.zpowers xP := by
        rw [hdec]
        exact Subgroup.mul_mem_sup hker (Subgroup.zpow_mem_zpowers xP i)
      rw [sup_comm] at hmem
      exact (sup_le_sup_left hZ₀P (Subgroup.zpowers xP)) hmem
    have hxPtop : Subgroup.zpowers xP = ⊤ := by
      haveI : IsCoatomic (Subgroup ↥(P : Subgroup Q)) := Finite.to_isCoatomic
      exact frattini_nongenerating hsup
    have hcycTop : IsCyclic ↥(⊤ : Subgroup ↥(P : Subgroup Q)) :=
      (Subgroup.isCyclic_iff_exists_zpowers_eq_top
        (⊤ : Subgroup ↥(P : Subgroup Q))).mpr ⟨xP, hxPtop⟩
    exact hPnc (Subgroup.topEquiv.isCyclic.mp hcycTop)
  intro S hScyc
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (Q ⧸ Z₀) S₀ S
  have hcyc_smul : IsCyclic ↥(y • S₀ : Sylow p (Q ⧸ Z₀)) := by
    rw [hy]
    exact hScyc
  exact hS₀nc ((Sylow.equivSMul S₀ y).isCyclic.mpr hcyc_smul)

theorem exists_elemAbelian_card_prime_sq_quotient_center [Group.IsPerfect Q] (hp2 : p ≠ 2)
    (P : Sylow p Q) (hPnc : ¬ IsCyclic ↥(P : Subgroup Q)) (Z₀ : Subgroup Q) [Z₀.Normal]
    (hZ₀ : Z₀ ≤ Subgroup.center Q) :
    ∃ E : Subgroup (Q ⧸ Z₀), CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  let S₀ : Sylow p (Q ⧸ Z₀) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective Z₀) P
  have hS₀nc : ¬ IsCyclic ↥(S₀ : Subgroup (Q ⧸ Z₀)) :=
    not_isCyclic_sylow_quotient_of_center P hPnc Z₀ hZ₀ S₀
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨B, hBelem, hBcard⟩ :=
    SteinbergBK.odd_noncyclic_pgroup_rank_two (p := p) hodd
      (P := ↥(S₀ : Subgroup (Q ⧸ Z₀))) S₀.isPGroup' hS₀nc
  letI : IsElementaryAbelian p B := hBelem
  let E : Subgroup (Q ⧸ Z₀) := B.map (S₀ : Subgroup (Q ⧸ Z₀)).subtype
  refine ⟨E, ?_, ?_⟩
  · exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (IsElementaryAbelian.map (S₀ : Subgroup (Q ⧸ Z₀)).subtype)
  · rw [show E = B.map (S₀ : Subgroup (Q ⧸ Z₀)).subtype from rfl,
      Subgroup.card_map_of_injective (S₀ : Subgroup (Q ⧸ Z₀)).subtype_injective, hBcard]

end CFSG.GroupTheory

end
