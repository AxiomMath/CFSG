module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnConcl53
public import CFSG.GH74.GLS.Stage1.Thm4.L98c
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIMain

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

theorem four_map_of_injective {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {U : Subgroup G} (hU : IVK.IsFourSubgroup U) :
    IVK.IsFourSubgroup (U.map f) := by
  refine ⟨?_, ?_⟩
  · exact Transport.isElementaryAbelian_of_mulEquiv (Subgroup.equivMapOfInjective U f hf) hU.1
  · rw [Subgroup.card_map_of_injective hf]; exact hU.2

theorem four_subgroupOf_of_le {G : Type} [Group G] {C U : Subgroup G} (hUC : U ≤ C)
    (hU : IVK.IsFourSubgroup U) : IVK.IsFourSubgroup (U.subgroupOf C) := by
  refine ⟨?_, ?_⟩
  · exact Transport.isElementaryAbelian_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUC).symm hU.1
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv]; exact hU.2


theorem four_sq_eq_one {G : Type} [Group G] {U : Subgroup G} (hU : IVK.IsFourSubgroup U)
    {a : G} (ha : a ∈ U) : a * a = 1 := by
  have := hU.1
  have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := U) a ha
  simpa [pow_two] using h2

theorem lemma29b_of_mem {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {n : ℕ}
    (hn8 : 8 ≤ n) (hn11 : n ≤ 11) (hsp : Stage1Sporadic G z S n) (hz : orderOf z = 2)
    (U : Subgroup G) (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) : Lemma29b U := by
  have : IsMulCommutative ↥U := hU.1.toIsMulCommutative
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)
  have hUC : U ≤ Cen z := by
    intro u hu
    show u ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hUcomm u hu z hzU
  have hcent : centralizer (U : Set G) ≤ Cen z := by
    intro g hg
    show g ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg z hzU).symm
  apply lemma29b_of_subgroupOf (Cen z) U hUC hcent
  have hH : Stage1.Thm4.Hyp5B (CentralizerBar z) ⊤ n :=
    ⟨inferInstance, hn8, hn11,
      Stage1.Thm4.isDoubleCoverOfAlt_congr Subgroup.topEquiv.symm hsp.cover,
      fun h _ => Subgroup.mem_top h⟩

  set N := pPrimeCore 2 ↥(Cen z) with hN
  set π := QuotientGroup.mk' N with hπ
  have hNodd : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have hU₀ : IVK.IsFourSubgroup (U.subgroupOf (Cen z)) := four_subgroupOf_of_le hUC hU
  have hU₀2 : IsPGroup 2 ↥(U.subgroupOf (Cen z)) := IsPGroup.of_card (n := 2) (by rw [hU₀.2]; norm_num)
  have hU₀N : U.subgroupOf (Cen z) ⊓ N = ⊥ := isPGroup_two_inf_eq_bot_of_odd _ N hU₀2 hNodd
  have hŪ : IVK.IsFourSubgroup ((U.subgroupOf (Cen z)).map π) := by
    refine ⟨?_, ?_⟩
    · refine isElementaryAbelian_two_of_forall ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        have h1 : a * b = b * a := by
          have := hUcomm (a : G) ha b hb
          exact Subtype.ext this
        rw [← map_mul, ← map_mul, h1]
      · rintro _ ⟨a, ha, rfl⟩
        have h1 : a * a = 1 := Subtype.ext (four_sq_eq_one hU ha)
        rw [← map_mul, h1, map_one]
    · rw [card_map_of_inf_eq_bot N hU₀N, hU₀.2]

  have hzC : z ∈ Cen z := by
    show z ∈ centralizer ({z} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set zb : CentralizerBar z := π ⟨z, hzC⟩ with hzb
  have hzbU : zb ∈ (U.subgroupOf (Cen z)).map π := ⟨⟨z, hzC⟩, hzU, rfl⟩
  have hzbcen : zb ∈ IVK.Proofs2.Ivk5An.ZK (⊤ : Subgroup (CentralizerBar z)) := by
    refine ⟨⟨zb, Subgroup.mem_top _⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    rintro ⟨y, -⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    apply Subtype.ext
    show π c * zb = zb * π c
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hzb1 : zb ≠ 1 := by
    intro h
    have h1 : (⟨z, hzC⟩ : ↥(Cen z)) ∈ N := (QuotientGroup.eq_one_iff _).mp h
    have h2 : orderOf (⟨z, hzC⟩ : ↥(Cen z)) ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨_, h1⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    rw [Subgroup.orderOf_mk, hz] at h2
    exact absurd (Odd.of_dvd_nat hNodd h2) (by decide)
  have hzbord : orderOf zb = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, hzb, ← map_mul]
      have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Cen z)) = 1 := Subtype.ext (by
        have := orderOf_dvd_iff_pow_eq_one.mp (hz ▸ dvd_rfl : orderOf z ∣ 2)
        simpa [pow_two] using this)
      rw [this, map_one]
    · exact hzb1
  have hZKcard : Nat.card ↥(IVK.Proofs2.Ivk5An.ZK (⊤ : Subgroup (CentralizerBar z))) = 2 := by
    unfold IVK.Proofs2.Ivk5An.ZK
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hH.cover.2.1
  have hZKeq : zpowers zb = IVK.Proofs2.Ivk5An.ZK (⊤ : Subgroup (CentralizerBar z)) := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzbcen)
    rw [Nat.card_zpowers, hzbord, hZKcard]
  have hZKle : IVK.Proofs2.Ivk5An.ZK (⊤ : Subgroup (CentralizerBar z)) ≤ (U.subgroupOf (Cen z)).map π := by
    rw [← hZKeq]
    exact zpowers_le.mpr hzbU
  obtain ⟨hab, hc, hd, he, hf⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk5An.ivk_5_3 _ ⊤ n hH _ le_top hŪ hZKle
  exact lemma29b_core n (U.subgroupOf (Cen z)) hU₀ hab hc hd he hf

theorem lemma29b_of_sporadic {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {n : ℕ}
    (hn8 : 8 ≤ n) (hn11 : n ≤ 11) (hsp : Stage1Sporadic G z S n) (hz : orderOf z = 2)
    (U : Subgroup G) (hU : IVK.IsFourSubgroup U) : Lemma29b U := by
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h4 := hU.2
    rw [this, Subgroup.card_bot] at h4
    omega
  have hu2 : u * u = 1 := four_sq_eq_one hU huU
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hsp.one_class z u hz huo)
  set U' : Subgroup G := U.map (MulAut.conj c⁻¹).toMonoidHom with hU'
  have hU'4 : IVK.IsFourSubgroup U' := four_map_of_injective _ (MulAut.conj c⁻¹).injective hU
  have hzU' : z ∈ U' := by
    refine ⟨u, huU, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hc]
    group
  have h := lemma29b_of_mem hn8 hn11 hsp hz U' hU'4 hzU'
  have h2 := lemma29b_conj U' c h
  have hUU : U'.map (MulAut.conj c).toMonoidHom = U := by
    rw [hU', Subgroup.map_map]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hx
    · intro hy
      exact ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  rwa [hUU] at h2

theorem lemma29FirstAt_of_mclly {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (ctx : Stage2Ctx G z k S) (hk : k = Kind.mcl ∨ k = Kind.ly) :
    Lemma29FirstAt z k := by
  intro U hU
  have hz : orderOf z = 2 := ctx.central.1
  obtain ⟨n, hn, hsp⟩ : ∃ n : ℕ, (8 ≤ n ∧ n ≤ 11) ∧ Stage1Sporadic G z S n := by
    have hd := ctx.data
    rcases hk with rfl | rfl
    · cases hd with
      | mcl h =>
        obtain ⟨n, hn, hsp⟩ := h
        exact ⟨n, ⟨by omega, by omega⟩, hsp⟩
    · cases hd with
      | ly h =>
        obtain ⟨n, hn, hsp⟩ := h
        exact ⟨n, ⟨by omega, by omega⟩, hsp⟩
  exact Or.inr (Or.inr ⟨hk, lemma29b_of_sporadic hn.1 hn.2 hsp hz U hU⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
