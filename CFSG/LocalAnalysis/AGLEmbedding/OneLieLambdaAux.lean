module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideCore
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ}

omit [Finite Y] in
theorem mem_of_conj_eq_inv_of_mem_sup (hp : p.Prime) (hp2 : p ≠ 2) {T C : Subgroup Y}
    [C.Normal] (hT : IsPGroup p T) (hTC : T ⊓ C = ⊥) (hcomm : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t)
    {x y : Y} (hx : x ∈ T ⊔ C) (hy : y ∈ T ⊔ C) (hyx : y * x * y⁻¹ = x⁻¹) : x ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx hy
  obtain ⟨t, ht, c, hc, rfl⟩ := hx
  obtain ⟨s, hs, d, hd, rfl⟩ := hy
  have hc' : d * c * d⁻¹ ∈ C := Subgroup.Normal.conj_mem inferInstance c hc d
  have h1 : s * d * (t * c) * (s * d)⁻¹ = s * t * s⁻¹ * (d * c * d⁻¹) := by
    have e1 : d * t = t * d := (hcomm t ht d hd).symm
    have e2 : s * (d * c * d⁻¹) = d * c * d⁻¹ * s := hcomm s hs _ hc'
    calc s * d * (t * c) * (s * d)⁻¹ = s * (d * t) * c * d⁻¹ * s⁻¹ := by group
      _ = s * t * (s⁻¹ * (s * (d * c * d⁻¹))) * s⁻¹ := by rw [e1]; group
      _ = s * t * s⁻¹ * (d * c * d⁻¹) := by rw [e2]; group
  have h2 : (t * c)⁻¹ = t⁻¹ * c⁻¹ := by
    rw [mul_inv_rev]
    exact (hcomm _ (T.inv_mem ht) _ (C.inv_mem hc)).symm
  have hst : s * t * s⁻¹ = t⁻¹ := by
    rw [h1, h2] at hyx
    have hmem : t * (s * t * s⁻¹) ∈ T ⊓ C := by
      refine ⟨T.mul_mem ht (T.mul_mem (T.mul_mem hs ht) (T.inv_mem hs)), ?_⟩
      have e : t * (s * t * s⁻¹) = c⁻¹ * (d * c * d⁻¹)⁻¹ := by
        calc t * (s * t * s⁻¹) = t * (s * t * s⁻¹ * (d * c * d⁻¹)) * (d * c * d⁻¹)⁻¹ := by
              group
          _ = c⁻¹ * (d * c * d⁻¹)⁻¹ := by rw [hyx]; group
      rw [e]
      exact C.mul_mem (C.inv_mem hc) (C.inv_mem hc')
    rw [hTC, Subgroup.mem_bot] at hmem
    calc s * t * s⁻¹ = t⁻¹ * (t * (s * t * s⁻¹)) := by group
      _ = t⁻¹ := by rw [hmem, mul_one]
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  obtain ⟨k, hk⟩ := hT ⟨s, hs⟩
  have hsk : s ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 2 (orderOf s) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hsk) (Nat.Coprime.pow_right k hcop2)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hs2 : Commute (s ^ 2) t := by
    have e : s * s * t * (s * s)⁻¹ = t := by
      calc s * s * t * (s * s)⁻¹ = s * (s * t * s⁻¹) * s⁻¹ := by group
        _ = s * t⁻¹ * s⁻¹ := by rw [hst]
        _ = (s * t * s⁻¹)⁻¹ := by group
        _ = t := by rw [hst, inv_inv]
    rw [sq]
    exact (mul_inv_eq_iff_eq_mul.mp e)
  have hsc : Commute s t := hm ▸ hs2.pow_left m
  have htt : t⁻¹ = t := by rw [← hst, hsc.eq, mul_inv_cancel_right]
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have htj : t ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have ht2 : t ^ 2 = 1 := by rw [sq]; nth_rw 1 [← htt]; exact inv_mul_cancel t
  have h1' : orderOf t = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right j hcop2)
    (orderOf_dvd_of_pow_eq_one ht2) (orderOf_dvd_of_pow_eq_one htj)
  show t * c ∈ C
  rw [orderOf_eq_one_iff.mp h1', one_mul]
  exact hc

theorem le_of_perfect_of_le_sup (hp : p.Prime) {T C U : Subgroup Y} [C.Normal]
    (hT : IsPGroup p T) (hU : ⁅U, U⁆ = U) (hUTC : U ≤ T ⊔ C) : U ≤ C := by
  have := Fact.mk hp
  set φ := QuotientGroup.mk' C with hφ
  have hUT : U.map φ ≤ T.map φ := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' := hUTC hu
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hu'
    obtain ⟨t, ht, c, hc, rfl⟩ := hu'
    refine ⟨t, ht, ?_⟩
    have hc1 : φ c = 1 := by
      rw [← MonoidHom.mem_ker, hφ, QuotientGroup.ker_mk']
      exact hc
    rw [map_mul, hc1, mul_one]
  have hUp : IsPGroup p (U.map φ) := (hT.map φ).to_le hUT
  have hperf : ⁅U.map φ, U.map φ⁆ = U.map φ := by rw [← Subgroup.map_commutator, hU]
  have hbot : U.map φ = ⊥ := by
    by_contra hne
    have : Nontrivial (U.map φ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsNilpotent (U.map φ) := hUp.isNilpotent
    have h1 : commutator (U.map φ) = ⊤ :=
      Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (U.map φ)).ne h1
  rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem exists_conj_zpowers_eq_of_isCyclic [Fact p.Prime] {C : Subgroup Y} [C.Normal]
    (S : Sylow p Y) (hSC : IsCyclic ((S : Subgroup Y) ⊓ C : Subgroup Y)) {a z : Y}
    (haC : a ∈ C) (hap : orderOf a = p) (hzS : z ∈ (S : Subgroup Y)) (hzC : z ∈ C)
    (hzp : orderOf z = p) :
    ∃ c ∈ C, Subgroup.zpowers (c * a * c⁻¹) = Subgroup.zpowers z := by
  obtain ⟨P₀, hP₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (inferInstance : C.Normal).isSubnormal
  set a' : C := ⟨a, haC⟩ with ha'
  have ha'p : orderOf a' = p := by rw [ha', Subgroup.orderOf_mk, hap]
  have hap' : IsPGroup p (Subgroup.zpowers a') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha'p, pow_one])
  obtain ⟨P₁, hP₁⟩ := hap'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P₁ P₀
  have hca : c * a' * c⁻¹ ∈ (P₀ : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul a' (MulAut.conj c) (P₁ : Subgroup C)
      (hP₁ (Subgroup.mem_zpowers a'))
    simpa only [MulAut.smul_def, MulAut.conj_apply] using this
  set w : Y := ((c * a' * c⁻¹ : C) : Y) with hw
  have hwS : w ∈ (S : Subgroup Y) ⊓ C := hP₀ ▸ Subgroup.mem_map_of_mem C.subtype hca
  have hwp : orderOf w = p := by
    have hsc : SemiconjBy (c : Y) a w := by
      simp only [SemiconjBy, hw, ha', Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← hsc.orderOf_eq, hap]
  have hzSC : z ∈ (S : Subgroup Y) ⊓ C := ⟨hzS, hzC⟩
  have := hSC
  have heq : Subgroup.zpowers (⟨w, hwS⟩ : ((S : Subgroup Y) ⊓ C : Subgroup Y)) =
      Subgroup.zpowers ⟨z, hzSC⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzp, hwp]
  have hmap := congrArg (Subgroup.map ((S : Subgroup Y) ⊓ C).subtype) heq
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  refine ⟨c, c.2, ?_⟩
  simpa [hw] using hmap

end Abstract

section Bar

variable {G : Type} [Group G] [Finite G]

theorem IsTwoPrimeComponent.le_pCoreCentralizerPreimage {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (p : ℕ) [Fact p.Prime] :
    L ≤ pCoreCentralizerPreimage p M := by
  intro l hl
  refine ⟨⟨l, hL.le hl⟩, ?_, rfl⟩
  have h := Subgroup.le_centralizer_iff.mp (pCore_le_centralizer_component p hL.component)
  exact h ⟨⟨l, hL.le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩

theorem exists_perfect_le_of_le_barM {M W : Subgroup G} (hWM : W ≤ M)
    {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVW : V ≤ barM M W) (hV : ⁅V, V⁆ = V) :
    ∃ V' : Subgroup G, V' ≤ W ∧ ⁅V', V'⁆ = V' ∧ barM M V' = V := by
  set ψ₀ : ↥W →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hWM) with hψ₀
  have hr : ψ₀.range = barM M W := by
    rw [hψ₀, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hVr : V ≤ ψ₀.range := hr ▸ hVW
  set B := V.subgroupOf ψ₀.range with hB
  have hBp : Group.IsPerfect B := by
    apply Subgroup.isPerfect_iff.mpr
    apply Subgroup.map_injective ψ₀.range.subtype_injective
    rw [Subgroup.map_commutator, hB, Subgroup.map_subgroupOf_eq_of_le hVr, hV]
  set R₀ := perfectResidualOf (B.comap ψ₀.rangeRestrict) with hR₀def
  have hR₀ : R₀.map ψ₀.rangeRestrict = B :=
    finite_canonical_perfect_preimage_image_eq _ ψ₀.rangeRestrict_surjective B hBp
  have hR₀p : ⁅R₀, R₀⁆ = R₀ :=
    Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect _)
  refine ⟨R₀.map W.subtype, Subgroup.map_subtype_le _,
    by rw [← Subgroup.map_commutator, hR₀p], ?_⟩
  have hsub : (R₀.map W.subtype).subgroupOf M = R₀.map (Subgroup.inclusion hWM) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, hwx⟩
      exact ⟨w, hw, Subtype.ext hwx⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [barM, hsub, Subgroup.map_map, ← hψ₀, ← MonoidHom.subtype_comp_rangeRestrict ψ₀,
    ← Subgroup.map_map, hR₀, hB, Subgroup.map_subgroupOf_eq_of_le hVr]

end Bar

theorem not_isCyclic_of_isElemAbelian {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime)
    {E : Subgroup Y} (hE : IsElemAbelian p E) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = p ^ n) :
    ¬ IsCyclic E := by
  intro hc
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero n hp.ne_zero)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hle : Nat.card E ≤ p := by
    rw [← hg]
    exact Nat.le_of_dvd hp.pos
      (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2)))
  rw [hcard] at hle
  have h1 : p ^ 1 < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by omega)
  rw [pow_one] at h1
  omega

end CFSG.AGLEmbedding
