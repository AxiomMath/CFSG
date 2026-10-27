module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ}

theorem card_le_of_isElemAbelian_of_isCyclic {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime)
    {B : Subgroup Y} (hB : IsElemAbelian p B) (hc : IsCyclic B) : Nat.card B ≤ p := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hord : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hB.2 g g.2)
  rw [← hord]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)

theorem pRank_le_one_of_le_of_inf_eq_bot {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime)
    {D E : Subgroup Y} [E.Normal] [(D.subgroupOf E).Normal] [IsCyclic (E ⧸ D.subgroupOf E)]
    (hD : Nat.Coprime (Nat.card D) p) (hE : Nat.Coprime E.index p) :
    pRank p (⊤ : Subgroup Y) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, -, hB, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup Y)
  have hBp : IsPGroup p B := IsPGroup.of_card hcard
  have hBE : B ≤ E := by
    have himg : IsPGroup p (B.map (QuotientGroup.mk' E)) := hBp.map _
    have hcop : Nat.Coprime (Nat.card (B.map (QuotientGroup.mk' E))) p := by
      refine Nat.Coprime.coprime_dvd_left ?_ hE
      rw [Subgroup.index_eq_card]
      exact Subgroup.card_subgroup_dvd_card _
    have hbot : B.map (QuotientGroup.mk' E) = ⊥ := by
      obtain ⟨k, hk⟩ := himg.exists_card_eq
      rw [hk] at hcop
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq _ hk
      · have h1 : Nat.Coprime p p := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hpos.ne') hcop
        rw [Nat.coprime_self] at h1
        exact absurd h1 hp.one_lt.ne'
    intro b hb
    have : (QuotientGroup.mk' E) b = 1 := by
      have hmem : (QuotientGroup.mk' E) b ∈ B.map (QuotientGroup.mk' E) := ⟨b, hb, rfl⟩
      rw [hbot] at hmem
      exact hmem
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hBD : B ⊓ D = ⊥ := CFSG.RankThree.Automorphisms.inf_eq_bot_of_isPGroup_of_coprime hBp hD
  have hcyc : IsCyclic B := CFSG.RankThree.Automorphisms.isCyclic_of_le_of_inf_eq_bot hBE hBD
  have hle := card_le_of_isElemAbelian_of_isCyclic hp hB hcyc
  rw [hcard] at hle
  by_contra h
  have : p ^ 2 ≤ p ^ pRank p (⊤ : Subgroup Y) := Nat.pow_le_pow_right hp.pos (by omega)
  have : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

noncomputable abbrev outerMk (K : Type*) [Group K] : MulAut K →* Outer K :=
  QuotientGroup.mk' (inner K)

theorem pRank_outer_le_one_of_chain {K : Type*} [Group K] [Finite K] (hp : p.Prime)
    {D E : Subgroup (MulAut K)} [hDn : D.Normal] [hEn : E.Normal] (hID : inner K ≤ D)
    (hDE : D ≤ E) (hcyc : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D)
    (hDI : Nat.Coprime ((inner K).relIndex D) p) (hE : Nat.Coprime E.index p) :
    pRank p (⊤ : Subgroup (Outer K)) ≤ 1 := by
  have hsurj : Function.Surjective (outerMk K) := QuotientGroup.mk'_surjective _
  have hker : (outerMk K).ker = inner K := QuotientGroup.ker_mk' _
  set D' := D.map (outerMk K) with hD'
  set E' := E.map (outerMk K) with hE'
  have : D'.Normal := hDn.map _ hsurj
  have : E'.Normal := hEn.map _ hsurj
  have hD'E' : D' ≤ E' := Subgroup.map_mono hDE
  have : (D'.subgroupOf E').Normal := Subgroup.normal_subgroupOf
  obtain ⟨g, hgE, hg⟩ := hcyc
  have : IsCyclic (E' ⧸ D'.subgroupOf E') := by
    refine ⟨⟨QuotientGroup.mk ⟨outerMk K g, ⟨g, hgE, rfl⟩⟩, fun y => ?_⟩⟩
    obtain ⟨⟨_, ⟨x, hxE, rfl⟩⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x hxE
    refine ⟨-k, ?_⟩
    beta_reduce
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : outerMk K (g ^ k * x) ∈ D' := ⟨_, hk, rfl⟩
    simpa [zpow_neg, inv_inv, map_mul, map_zpow] using this
  have hcardD' :
      Nat.card D' = (CFSG.ComponentClassification.OuterAutomorphisms.inner K).relIndex D := by
    have h1 := Subgroup.relIndex_mul_card (outerMk K).ker D
    rw [Subgroup.relIndex_ker, hker] at h1
    have h2 := Subgroup.relIndex_mul_card (CFSG.ComponentClassification.OuterAutomorphisms.inner K) D
    have hpos :
        0 < Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊓ D) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hindex : E'.index = E.index := by
    rw [hE']
    exact Subgroup.index_map_eq _ hsurj (by rw [hker]; exact hID.trans hDE)
  exact pRank_le_one_of_le_of_inf_eq_bot (D := D') (E := E') hp (by rwa [hcardD'])
    (by rwa [hindex])

end GL83.I713
