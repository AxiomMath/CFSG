module

import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.Uniqueness.Section6ZJ

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section ProductCore

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_quotient_sup_of_le_normalizer {p : ℕ} (B R : Subgroup G)
    [(B.subgroupOf (B ⊔ R)).Normal] (hRp : IsPGroup p R) :
    IsPGroup p (↥(B ⊔ R) ⧸ B.subgroupOf (B ⊔ R)) := by
  let H : Subgroup G := B ⊔ R
  let Bsub : Subgroup H := B.subgroupOf H
  let Rsub : Subgroup H := R.subgroupOf H
  have hBH : B ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  let : Bsub.Normal := by
    dsimp [Bsub, H]
    infer_instance
  have hsup : Bsub ⊔ Rsub = ⊤ := by
    apply top_unique
    intro h _hh
    have hxH : (h : G) ∈ H := h.property
    have hmapSup : (Bsub ⊔ Rsub).map H.subtype = H := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBH,
        Subgroup.map_subgroupOf_eq_of_le hRH]
    have hxMap : (h : G) ∈ (Bsub ⊔ Rsub).map H.subtype := by
      rw [hmapSup]
      exact hxH
    rcases Subgroup.mem_map.mp hxMap with ⟨k, hk, hkEq⟩
    have : k = h := Subtype.ext hkEq
    rwa [this] at hk
  let qH : H →* H ⧸ Bsub := QuotientGroup.mk' Bsub
  let rToH : R →* H := Subgroup.inclusion hRH
  let f : R →* H ⧸ Bsub := qH.comp rToH
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Bsub y
    have hh : h ∈ Bsub ⊔ Rsub := by
      rw [hsup]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hh with ⟨b, hb, r, hr, hbr⟩
    let rr : R := ⟨((r : H) : G), hr⟩
    refine ⟨rr, ?_⟩
    change qH r = qH h
    have hqb : qH b = 1 := (QuotientGroup.eq_one_iff b).2 hb
    rw [← hbr, map_mul, hqb, one_mul]
  exact IsPGroup.of_surjective hRp f hf

theorem pPrimeCore_map_sup_eq_of_le_normalizer {p : ℕ} [Fact p.Prime] (B R : Subgroup G)
    (hRnorm : R ≤ normalizer (B : Set G)) (hRp : IsPGroup p R) :
    (pPrimeCore p (↥(B ⊔ R))).map (B ⊔ R).subtype = (pPrimeCore p B).map B.subtype := by
  classical
  let H : Subgroup G := B ⊔ R
  have hBH : B ≤ H := le_sup_left
  have hHnormB : H ≤ normalizer (B : Set G) := sup_le Subgroup.le_normalizer hRnorm
  have hBnorm : (B.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2 hHnormB
  let : (B.subgroupOf H).Normal := hBnorm
  have hquotP : IsPGroup p (↥H ⧸ B.subgroupOf H) := isPGroup_quotient_sup_of_le_normalizer B R hRp
  let qH : H →* H ⧸ B.subgroupOf H := QuotientGroup.mk' (B.subgroupOf H)
  let OH : Subgroup H := pPrimeCore p H
  have hmapP : IsPGroup p (OH.map qH) := hquotP.to_subgroup (OH.map qH)
  have hmapCop : Nat.Coprime p (Nat.card (OH.map qH)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := OH) qH)
      (pPrimeCore_coprime_card (p := p) (G := H))
  have hmapCard : Nat.card (OH.map qH) = 1 := by
    rcases hmapP.card_eq_or_dvd with hcard | hpDvd
    · exact hcard
    · exact False.elim (((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hmapCop) hpDvd)
  have hmapBot : OH.map qH = ⊥ := (Subgroup.card_eq_one (H := OH.map qH)).1 hmapCard
  have hOHleB : OH ≤ B.subgroupOf H := by
    have hker : OH ≤ qH.ker := (Subgroup.map_eq_bot_iff (f := qH) (H := OH)).1 hmapBot
    simpa [qH, QuotientGroup.ker_mk'] using hker
  let OHX : Subgroup G := OH.map H.subtype
  let OBX : Subgroup G := (pPrimeCore p B).map B.subtype
  have hOHXleB : OHX ≤ B := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hOHleB hy
  have hHnormOHX : H ≤ normalizer (OHX : Set G) :=
    Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic (H := H) (K := OH))
  have : (OHX.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOHXleB).2 (hBH.trans hHnormOHX)
  have hOHXcop : Nat.Coprime p (Nat.card OHX) := by
    rw [show Nat.card OHX = Nat.card OH from
      Subgroup.card_map_of_injective (K := OH) (f := H.subtype) H.subtype_injective]
    exact pPrimeCore_coprime_card (p := p) (G := H)
  have hfirst : OHX ≤ OBX := CFSG.subgroupOf_le_pPrimeCore_map (p := p) hOHXleB hOHXcop
  have hOBXleH : OBX ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hBH y.property
  have hHnormOBX : H ≤ normalizer (OBX : Set G) :=
    hHnormB.trans
      (section8_normalizer_map_subtype_le_of_characteristic (H := B) (K := pPrimeCore p B))
  have : (OBX.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOBXleH).2 hHnormOBX
  have hOBXcop : Nat.Coprime p (Nat.card OBX) := by
    rw [show Nat.card OBX = Nat.card (pPrimeCore p B) from
      Subgroup.card_map_of_injective (K := pPrimeCore p B) (f := B.subtype) B.subtype_injective]
    exact pPrimeCore_coprime_card (p := p) (G := B)
  have hsecond : OBX ≤ OHX := CFSG.subgroupOf_le_pPrimeCore_map (p := p) hOBXleH hOBXcop
  exact le_antisymm hfirst hsecond

end ProductCore

section ZJ

theorem zjSubgroup_map_of_injective {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) (p : ℕ) (R : Subgroup X) :
    (zjSubgroup p R).map f = zjSubgroup p (R.map f) := by
  rw [zjSubgroup_eq_closure, zjSubgroup_eq_closure, MonoidHom.map_closure,
    ← thompsonCenter_map_of_injective' f hf]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, hxp, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hyp⟩
    refine ⟨x, ⟨hx, hf ?_⟩, rfl⟩
    rw [map_pow, hyp, map_one]

theorem pPrimeCore_sup_normalizer_zjSubgroup_eq_top {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (P : Sylow p G)
    (hnorm : (thompsonCenter (G := G) (P : Subgroup G) ⊔ pPrimeCore p G).Normal) :
    pPrimeCore p G ⊔ normalizer (zjSubgroup p (P : Subgroup G) : Set G) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let J : Subgroup G := thompsonCenter (G := G) (P : Subgroup G)
  let O : Subgroup G := pPrimeCore p G
  let K : Subgroup G := J ⊔ O
  have : O.Normal := pPrimeCore_normal
  have : K.Normal := hnorm
  have hJP : J ≤ (P : Subgroup G) := thompsonCenter_le (P : Subgroup G)
  have hPOcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card O) := by
    rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := (Subgroup.disjoint_of_coprime_natCard hPOcop).eq_bot
  have hPK : (P : Subgroup G) ⊓ K = J := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_sup_of_normal_right.mp hx.2 with ⟨j, hj, o, ho, hjo⟩
      have hjP : j ∈ (P : Subgroup G) := hJP hj
      have hoP : o ∈ (P : Subgroup G) := by
        have hoeq : o = j⁻¹ * x := by
          rw [← hjo]
          simp
        rw [hoeq]
        exact P.mul_mem (P.inv_mem hjP) hx.1
      have hoBot : o ∈ (⊥ : Subgroup G) := by
        rw [← hPO]
        exact ⟨hoP, ho⟩
      have hoOne : o = 1 := by simpa using hoBot
      rw [← hjo, hoOne]
      simpa using hj
    · exact le_inf hJP le_sup_left
  let PK : Sylow p K := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal P K
  have hPKmap : (PK : Subgroup K).map K.subtype = J := by
    rw [show (PK : Subgroup K) = (P : Subgroup G).comap K.subtype from
      CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe P K]
    rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]
    simpa [inf_comm] using hPK
  have hfrattini : normalizer (J : Set G) ⊔ K = ⊤ := by
    simpa [hPKmap] using (Sylow.normalizer_sup_eq_top (G := G) (N := K) PK)
  have hnormJZ : normalizer (J : Set G) ≤ normalizer (zjSubgroup p (P : Subgroup G) : Set G) :=
    normalizer_thompsonCenter_le_normalizer_zjSubgroup p (P : Subgroup G)
  apply top_unique
  rw [← hfrattini]
  apply sup_le
  · exact hnormJZ.trans le_sup_right
  · apply sup_le
    · exact Subgroup.le_normalizer.trans (hnormJZ.trans le_sup_right)
    · exact le_sup_left

theorem exists_mul_mem_normalizer_zjSubgroup_of_solvable {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H R : Subgroup X} (hsolv : Group.IsSolvable ↥H)
    (hab : CFSG.BenderSuzuki.HasAbelianSylow 2 ↥H) (hR : ABGLocalTools.IsSylowOf p R H)
    (hcore : pCore p ↥H ≠ ⊥) {h : X} (hh : h ∈ H) :
    ∃ a ∈ (pPrimeCore p ↥H).map H.subtype, ∃ n ∈ H ⊓ normalizer (zjSubgroup p R : Set X),
      h = a * n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := hR
  have hstable : PStableGroup' (G := ↥H) p :=
    CFSG.BenderSuzuki.pStableGroup'_of_solvable_abelianSylowTwo hsolv hab (hp.odd_of_ne_two hp2)
  have hconstr : PConstrainedGroup (G := ↥H) p :=
    CFSG.BenderSuzuki.theorem4b_pConstrainedGroup_of_solvable hsolv p
  have hnormal := G_theorem_8_2_11 p hp2 hcore hconstr hstable P
  have hfac := pPrimeCore_sup_normalizer_zjSubgroup_eq_top hp P hnormal
  have hmem : (⟨h, hh⟩ : ↥H) ∈ pPrimeCore p ↥H ⊔
      normalizer (zjSubgroup p (P : Subgroup ↥H) : Set ↥H) := by
    rw [hfac]
    exact Subgroup.mem_top _
  have : (pPrimeCore p ↥H).Normal := pPrimeCore_normal
  obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hzj : (zjSubgroup p (P : Subgroup ↥H)).map H.subtype = zjSubgroup p R := by
    rw [zjSubgroup_map_of_injective H.subtype H.subtype_injective, hP]
  have hnX : (n : X) ∈ normalizer (zjSubgroup p R : Set X) := by
    rw [← hzj]
    exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem H.subtype hn)
  refine ⟨(a : X), Subgroup.mem_map_of_mem H.subtype ha, (n : X),
    Subgroup.mem_inf.mpr ⟨n.2, hnX⟩, ?_⟩
  have := congrArg Subtype.val han
  simpa using this.symm

end ZJ

section Misc

theorem commute_of_mem_normalizer_sylow_of_isBenderGroup
    {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (T : Sylow 2 K) {a b : K}
    (ha : a ∈ normalizer ((T : Subgroup K) : Set K))
    (hb : b ∈ normalizer ((T : Subgroup K) : Set K)) (ha2 : a * a = 1) (hb2 : b * b = 1) :
    a * b = b * a := by
  obtain ⟨n, i, e, h⟩ := Bender.isBenderGroup_iff_exists_benderType.mp hK
  obtain ⟨t, hc⟩ := h.exists_benderCore T
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have ha' := (hc.involution_iff.mp ⟨ha, hao⟩).1
  have hb' := (hc.involution_iff.mp ⟨hb, hbo⟩).1
  exact ((Bender.mem_rootCenter_iff.mp ha').2 b (Bender.rootCenter_le _ hb')).symm

theorem two_le_twoRank_of_two_le_pRank {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (h : 2 ≤ Open.pRank 2 L) : 2 ≤ Open.twoRank ↥L := by
  have e := CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 one_lt_two L
  unfold Open.twoRank
  rw [← e]
  exact h

theorem mem_normalizer_zHull_of_mem_normalizer {X : Type*} [Group X] {Z : Set X}
    (hZ : IsInvariantInvolutionSet Z) {H : Subgroup X} {g : X} (hg : g ∈ normalizer (H : Set X)) :
    g ∈ normalizer (zHull Z H : Set X) := by
  have key : ∀ k ∈ normalizer (H : Set X), ∀ x ∈ zHull Z H, k * x * k⁻¹ ∈ zHull Z H := by
    intro k hk x hx
    have hle : zHull Z H ≤ (zHull Z H).comap (MulAut.conj k).toMonoidHom := by
      rw [zHull, Subgroup.closure_le]
      rintro y ⟨hyZ, hyH⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj k).toMonoidHom y = k * y * k⁻¹ := by simp
      rw [e]
      have hyZ' : k * y * k⁻¹ ∈ Z := by
        have := hZ.2 y hyZ k⁻¹
        simpa using this
      have hyH' : k * y * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hk y).mp hyH
      exact Subgroup.subset_closure ⟨hyZ', hyH'⟩
    have := hle hx
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ ((normalizer (H : Set X)).inv_mem hg) _ hx
    simpa [mul_assoc] using this

end Misc

end CFSG.GH74.Uniqueness
