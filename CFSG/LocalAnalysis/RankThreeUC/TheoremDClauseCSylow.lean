module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

variable {G : Type*} [Group G]

theorem noRankTwoThree_of_pRank_le_one [Finite G] {K : Subgroup G}
    (h : CFSG.Open.pRank 3 K ≤ 1) : NoRankTwoThree K := by
  intro c₁ h₁ c₂ h₂ hcomm hc₁ hc₂ hne₁ hne₂ hne₃ hne₄
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E : Subgroup G := Subgroup.closure {c₁, c₂} with hE
  have hEK : E ≤ K := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl) <;> assumption
  have hpair : ({c₁, c₂} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hcomm
    · exact hcomm.symm
    · exact absurd rfl hxy
  have : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => rcases hy with rfl | rfl <;> assumption
    | one => simp
    | mul y z hy hz ihy ihz =>
      have hyz : Commute y z := congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : E) ⟨z, hz⟩)
      rw [hyz.mul_pow, ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have hpg : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hE3 g g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  have hn1 : n ≤ 1 :=
    (CFSG.SectionRank.le_pRank (by norm_num) hEK ⟨inferInstance, hE3⟩ hn).trans h
  have hord : orderOf c₁ = 3 := orderOf_eq_prime hc₁ hne₁
  have hZE : zpowers c₁ ≤ E := Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hdvd : Nat.card (zpowers c₁) ∣ Nat.card E := Subgroup.card_dvd_of_le hZE
  rw [Nat.card_zpowers, hord, hn] at hdvd
  have hn_eq : n = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hdvd
    · omega
  subst hn_eq
  have hZ : zpowers c₁ = E := by
    apply Subgroup.eq_of_le_of_card_ge hZE
    rw [Nat.card_zpowers, hord, hn]; simp
  have hc₂E : c₂ ∈ zpowers c₁ := hZ ▸ Subgroup.subset_closure (by simp)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc₂E
  have hk' : c₂ = c₁ ^ (k % 3) := by
    rw [← hk]
    have := zpow_mod_orderOf c₁ k
    rw [hord] at this
    exact_mod_cast this.symm
  have hc₁3 : c₁ ^ (3 : ℤ) = 1 := by exact_mod_cast hc₁
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h0 | h0
  · rw [h0] at hk'; simp at hk'; exact hne₂ hk'
  · rw [h0] at hk'; simp at hk'; exact hne₃ hk'
  · rw [h0] at hk'
    apply hne₄
    rw [hk']
    have : c₁ ^ (2 : ℤ) * c₁ = 1 := by rw [← zpow_add_one]; exact hc₁3
    exact eq_inv_of_mul_eq_one_left this

theorem exists_conj_le_map_of_isPGroup {M Ω : Type*} [Group M] [Finite M] [Group Ω]
    (ρ : M →* Ω) {p : ℕ} [Fact p.Prime] (S : Sylow p M) (D : Subgroup Ω) (hD : D ≤ ρ.range)
    (hDp : IsPGroup p D) :
    ∃ x ∈ ρ.range, ∀ d ∈ D, x⁻¹ * d * x ∈ (S : Subgroup M).map ρ := by
  have hf : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have : Finite ρ.range := Finite.of_surjective _ hf
  let S' : Sylow p ρ.range := S.mapSurjective hf
  have hDp' : IsPGroup p (D.subgroupOf ρ.range) := hDp.comap_subtype
  obtain ⟨Q, hQ⟩ := hDp'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ρ.range S' Q
  refine ⟨x, x.2, fun d hd => ?_⟩
  have hdQ : (⟨d, hD hd⟩ : ρ.range) ∈ (Q : Subgroup ρ.range) := hQ hd
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hdQ
  obtain ⟨s, hs, hsd⟩ := hdQ
  have hsd' : (x : Ω)⁻¹ * d * x = s := by
    have : (x : Ω) * s * (x : Ω)⁻¹ = d := congrArg Subtype.val hsd
    rw [← this]
    group
  rw [hsd']
  obtain ⟨m, hm, hms⟩ := hs
  exact ⟨m, hm, congrArg Subtype.val hms⟩

theorem card_le_and_commute_of_isPGroup {M Ω : Type*} [Group M] [Finite M] [Group Ω]
    (ρ : M →* Ω) {p : ℕ} [Fact p.Prime] (S : Sylow p M) (D : Subgroup Ω) (hD : D ≤ ρ.range)
    (hDp : IsPGroup p D) (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    Nat.card D ≤ Nat.card ((S : Subgroup M).map ρ) ∧
      (Nat.card ((S : Subgroup M).map ρ) ≤ Nat.card D →
        ∀ a ∈ (S : Subgroup M), ∀ b ∈ (S : Subgroup M), ρ a * ρ b = ρ b * ρ a) := by
  obtain ⟨x, -, hconj⟩ := exists_conj_le_map_of_isPGroup ρ S D hD hDp
  let φ : D → (S : Subgroup M).map ρ := fun d => ⟨(x : Ω)⁻¹ * d * x, hconj d d.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [φ, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have : Finite ((S : Subgroup M).map ρ) :=
    Finite.of_surjective _ (ρ.subgroupMap_surjective (S : Subgroup M))
  refine ⟨Nat.card_le_card_of_injective φ hφ, fun hle a ha b hb => ?_⟩
  obtain ⟨d, hd⟩ := (hφ.bijective_of_nat_card_le hle).2 ⟨ρ a, mem_map_of_mem ρ ha⟩
  obtain ⟨d', hd'⟩ := (hφ.bijective_of_nat_card_le hle).2 ⟨ρ b, mem_map_of_mem ρ hb⟩
  have h1 : ρ a = (x : Ω)⁻¹ * d * x := (congrArg Subtype.val hd).symm
  have h2 : ρ b = (x : Ω)⁻¹ * d' * x := (congrArg Subtype.val hd').symm
  rw [h1, h2]
  calc (x : Ω)⁻¹ * d * x * ((x : Ω)⁻¹ * d' * x) = (x : Ω)⁻¹ * (d * d') * x := by group
    _ = (x : Ω)⁻¹ * (d' * d) * x := by rw [hDab d d.2 d' d'.2]
    _ = (x : Ω)⁻¹ * d' * x * ((x : Ω)⁻¹ * d * x) := by group

private theorem isCyclic_sylow_three_of_pRank_le_one [Finite G] {N : Subgroup G}
    (hrank : CFSG.Open.pRank 3 N ≤ 1) (S₁ : Sylow 3 N) : IsCyclic (S₁ : Subgroup N) := by
  by_contra hnc
  have : Fact (IsPGroup 3 (S₁ : Subgroup N)) := ⟨S₁.isPGroup'⟩
  obtain ⟨T, -, hTcard, hTel⟩ :=
    CFSG.lemma_4_5_a (R := (S₁ : Subgroup N)) (p := 3) (by norm_num) hnc
  let f : (S₁ : Subgroup N) →* G := N.subtype.comp (S₁ : Subgroup N).subtype
  have hf : Function.Injective f := N.subtype_injective.comp (S₁ : Subgroup N).subtype_injective
  have hEl : CFSG.IsElementaryAbelian 3 (T.map f) := hTel.map f
  have hEN : T.map f ≤ N := by
    rintro _ ⟨t, -, rfl⟩
    exact (t : N).2
  have hcard : Nat.card (T.map f) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hf, hTcard]
  have hElem : CFSG.Open.IsElemAbelian 3 (T.map f) :=
    ⟨hEl.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEN hElem hcard
  omega

private theorem surjective_quotient_inclusion {M J N : Subgroup G}
    [(J.subgroupOf M).Normal] (hJM : J ≤ M) (hNM : N ≤ M) (hNJ : N ≤ normalizer (J : Set G))
    (hMN : M ≤ J ⊔ N) :
    Function.Surjective ((QuotientGroup.mk' (J.subgroupOf M)).comp (Subgroup.inclusion hNM)) := by
  intro y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  have hm : (m : G) ∈ (↑(N ⊔ J) : Set G) := by
    rw [sup_comm]; exact hMN m.2
  rw [coe_mul_of_left_le_normalizer_right N J hNJ] at hm
  obtain ⟨n, hn, j, hj, hnj⟩ := hm
  refine ⟨⟨n, hn⟩, ?_⟩
  change ((⟨n, hNM hn⟩ : M) : M ⧸ J.subgroupOf M) = m
  rw [QuotientGroup.eq]
  have : (⟨n, hNM hn⟩ : M)⁻¹ * m = ⟨j, hJM hj⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hnj]
    group
  rw [this]
  exact hj

theorem cyclicMod_of_le_sup [Finite G] {M J N P : Subgroup G} (hJM : J ≤ M)
    (hMJ : M ≤ normalizer (J : Set G)) (hNM : N ≤ M) (hMN : M ≤ J ⊔ N)
    (hrank : CFSG.Open.pRank 3 N ≤ 1) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M) :
    CyclicMod P (P ⊓ J) := by
  have hnorm : (J.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hJM).mpr hMJ
  let q : M →* M ⧸ J.subgroupOf M := QuotientGroup.mk' (J.subgroupOf M)
  let ρ : N →* M ⧸ J.subgroupOf M := q.comp (Subgroup.inclusion hNM)
  have hρ : Function.Surjective ρ := surjective_quotient_inclusion hJM hNM (hNM.trans hMJ) hMN
  obtain ⟨S₁⟩ := (inferInstance : Nonempty (Sylow 3 N))
  have hcycS : IsCyclic (S₁ : Subgroup N) := isCyclic_sylow_three_of_pRank_le_one hrank S₁
  obtain ⟨SP, hSP⟩ := hP.exists_sylow_eq_subgroupOf
  let D : Subgroup (M ⧸ J.subgroupOf M) := (SP : Subgroup M).map q
  have hDle : D ≤ ρ.range := by rw [MonoidHom.range_eq_top.2 hρ]; exact le_top
  have hDp : IsPGroup 3 D := SP.isPGroup'.map q
  obtain ⟨x, -, hx⟩ := exists_conj_le_map_of_isPGroup ρ S₁ D hDle hDp
  have hCcyc : IsCyclic ((S₁ : Subgroup N).map ρ) :=
    isCyclic_of_surjective (ρ.subgroupMap (S₁ : Subgroup N)) (ρ.subgroupMap_surjective _)
  let ψ : D →* (S₁ : Subgroup N).map ρ :=
    ((MulAut.conj (x : M ⧸ J.subgroupOf M)⁻¹).toMonoidHom.comp D.subtype).codRestrict _
      (fun d => by
        show (x : M ⧸ J.subgroupOf M)⁻¹ * (d : M ⧸ J.subgroupOf M) *
          (x : M ⧸ J.subgroupOf M)⁻¹⁻¹ ∈ _
        rw [inv_inv]
        exact hx d d.2)
  have hψ : Function.Injective ψ := fun a b hab =>
    Subtype.ext ((MulAut.conj (x : M ⧸ J.subgroupOf M)⁻¹).injective (congrArg Subtype.val hab))
  have hDcyc : IsCyclic D := isCyclic_of_injective ψ hψ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  obtain ⟨g₀, hg₀, hg₀g⟩ := g.2
  have hg₀P : (g₀ : G) ∈ P := by
    have : g₀ ∈ (SP : Subgroup M) := hg₀
    rw [hSP] at this
    exact this
  refine ⟨(g₀ : G), hg₀P, fun γ hγ => ?_⟩
  have hγM : γ ∈ M := hP.le hγ
  have hγSP : (⟨γ, hγM⟩ : M) ∈ (SP : Subgroup M) := by rw [hSP]; exact hγ
  have hmem : (⟨q ⟨γ, hγM⟩, mem_map_of_mem q hγSP⟩ : D) ∈ zpowers g := hg _
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hqk : q (g₀ ^ k) = q ⟨γ, hγM⟩ := by
    have := congrArg Subtype.val hk
    simpa [← hg₀g] using this
  have hJ : (g₀ ^ k)⁻¹ * ⟨γ, hγM⟩ ∈ J.subgroupOf M := QuotientGroup.eq.1 hqk
  exact ⟨k, ((g₀ : G) ^ k)⁻¹ * γ, ⟨P.mul_mem (P.inv_mem (P.pow_mem hg₀P k)) hγ, hJ⟩,
    (mul_inv_cancel_left _ _).symm⟩

end CFSG.LocalAnalysis.RankThreeUC
