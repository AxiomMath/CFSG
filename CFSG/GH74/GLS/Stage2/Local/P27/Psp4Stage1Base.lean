module

public import CFSG.GH74.GLS.Stage2.Local.P27.PairData
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
public import CFSG.GH74.GLS.Stage1.Main.NoFAutProof
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIAMain
public import CFSG.GH74.GLS.Stage1.Main.BrG2Quat

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem S_le_Cen (hS : IsSylowOf 2 S (Cen z)) : S ≤ Cen z := by
  obtain ⟨Q, hQ⟩ := hS
  rw [← hQ]
  exact Subgroup.map_subtype_le _

theorem sylow_barS (hS : IsSylowOf 2 S (Cen z)) : IsSylowOf 2 (barOf z S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS
  have h1 : barOf z S = (Q : Subgroup ↥(Cen z)).map (toBar z) := by
    unfold barOf
    rw [← hQ, show ((Q : Subgroup ↥(Cen z)).map (Cen z).subtype).subgroupOf (Cen z) = Q from
      Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _]
  rw [h1, ← Sylow.coe_mapSurjective (toBar_surjective z) Q]
  rw [isSylowOf_iff]
  refine ⟨le_top, (Sylow.mapSurjective (toBar_surjective z) Q).isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact Sylow.not_dvd_index _

theorem LBar_normal (z : G) : (LBar z).Normal := Stage1.Thm6.Prod.LBar_isNormal z

omit [Finite G] in
theorem le_normalizer_of_commute {A B : Subgroup (CentralizerBar z)}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ≤ Subgroup.normalizer (B : Set (CentralizerBar z)) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have : a * b * a⁻¹ = b := by rw [h a ha b hb]; group
    rw [this]; exact hb
  · intro hb
    have h1 := h a⁻¹ (A.inv_mem ha) _ hb
    have : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
        _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h1]
        _ = a * b * a⁻¹ := by group
    rw [this]
    exact hb

theorem bar_sylow_structure (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂) :
    IsSylowOf 2 (barOf z S ⊓ LBar z) (LBar z) ∧
    IsSylowOf 2 (barOf z S ⊓ L₁) L₁ ∧ IsSylowOf 2 (barOf z S ⊓ L₂) L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSB := sylow_barS hS
  have hLn := LBar_normal z
  have hR : IsSylowOf 2 (barOf z S ⊓ LBar z) (LBar z) :=
    hSB.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top]) 
  have hL1 : L₁ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_left
  have hL2 : L₂ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_right
  have hn1 : LBar z ≤ Subgroup.normalizer (L₁ : Set (CentralizerBar z)) := by
    rw [← hP.prod.1]
    exact sup_le Subgroup.le_normalizer
      (le_normalizer_of_commute (fun b hb a ha => (hP.prod.2.1 a ha b hb).symm))
  have hn2 : LBar z ≤ Subgroup.normalizer (L₂ : Set (CentralizerBar z)) := by
    rw [← hP.prod.1]
    exact sup_le (le_normalizer_of_commute (fun b hb a ha => hP.prod.2.1 b hb a ha))
      Subgroup.le_normalizer
  have h1 := hR.inf_of_le_normalizer hL1 hn1
  have h2 := hR.inf_of_le_normalizer hL2 hn2
  rw [inf_assoc, inf_of_le_right hL1] at h1
  rw [inf_assoc, inf_of_le_right hL2] at h2
  exact ⟨hR, h1, h2⟩

theorem zbar_ne_one_of_central (hz : IsCentralInvolution z) :
    toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
  intro h
  have h1 : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]; exact h
  have hd : orderOf (⟨⟨z, mem_Cen_self z⟩, h1⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
      Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz.1] at hd
  have hodd := Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)

theorem central_mem_sylow {H : Type*} [Group H] [Finite H] (Q : Sylow 2 H) {c : H}
    (hc : c ∈ Subgroup.center H) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    c ∈ (Q : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q', hQ'⟩ := hc2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q' Q
  have h0 : c ∈ (Q' : Subgroup H) := hQ' (Subgroup.mem_zpowers c)
  have h1 : c ∈ ((g • Q' : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.smul_def]
    have := Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) (Q' : Subgroup H) h0
    have hcc : (MulAut.conj g) • c = c := by
      show g * c * g⁻¹ = c
      rw [(Subgroup.mem_center_iff.1 hc g)]
      group
    rwa [hcc] at this
  rwa [hg] at h1

theorem z_mem_of_sylow (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z)) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  let z' : ↥(Cen z) := ⟨z, mem_Cen_self z⟩
  have hcen : z' ∈ Subgroup.center ↥(Cen z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 g.2 z (by simp)).symm
  have hz'2 : orderOf z' = 2 := by
    rw [← hz.1]; exact (Subgroup.orderOf_mk z _)
  have hp : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2]; norm_num)
  have := central_mem_sylow Q hcen hp
  rw [← hQ]
  exact ⟨z', this, rfl⟩

theorem bar_sup_eq (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂) :
    barOf z S ⊓ LBar z = (barOf z S ⊓ L₁) ⊔ (barOf z S ⊓ L₂) ∧
      (barOf z S ⊓ L₁) ⊓ (barOf z S ⊓ L₂) = L₁ ⊓ L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR, h1, h2⟩ := bar_sylow_structure hS hP
  have hzS := z_mem_of_sylow hz hS
  have hL1 : L₁ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_left
  have hL2 : L₂ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_right
  set zb : CentralizerBar z := toBar z ⟨z, mem_Cen_self z⟩ with hzb
  have hzbS : zb ∈ barOf z S := ⟨⟨z, mem_Cen_self z⟩, (Subgroup.mem_subgroupOf).2 hzS, rfl⟩
  have hzb12 : zb ∈ L₁ ⊓ L₂ := IVK.Proofs2.Ivk93Adapt.zbarC_mem_inf hP
  have hzb1 : zb ≠ 1 := zbar_ne_one_of_central hz
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have hzb2 : orderOf zb = 2 := by
    apply orderOf_eq_prime _ hzb1
    rw [pow_two, hzb, ← map_mul]
    have : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hN : Nat.card ↥L₁ = Nat.card ↥L₂ := by
    obtain ⟨ht, hc, -⟩ := hsw
    rw [← hc]
    exact (Subgroup.card_map_of_injective (MulAut.conj (toBar z ⟨t, ht⟩)⁻¹).injective).symm
  have hA12 : (barOf z S ⊓ L₁) ⊓ (barOf z S ⊓ L₂) = L₁ ⊓ L₂ := by
    have hle : (barOf z S ⊓ L₁) ⊓ (barOf z S ⊓ L₂) ≤ L₁ ⊓ L₂ :=
      inf_le_inf inf_le_right inf_le_right
    apply Subgroup.eq_of_le_of_card_ge hle
    have h2c : Nat.card ↥(L₁ ⊓ L₂) = 2 := hP.prod.2.2
    rw [h2c]
    have hzp : Subgroup.zpowers zb ≤ (barOf z S ⊓ L₁) ⊓ (barOf z S ⊓ L₂) := by
      rw [Subgroup.zpowers_le]
      exact ⟨⟨hzbS, hzb12.1⟩, hzbS, hzb12.2⟩
    have := Subgroup.card_le_of_le hzp
    rwa [Nat.card_zpowers, hzb2] at this
  refine ⟨?_, hA12⟩
  have hcomm : ∀ x ∈ barOf z S ⊓ L₁, ∀ y ∈ barOf z S ⊓ L₂, x * y = y * x :=
    fun x hx y hy => hP.prod.2.1 x hx.2 y hy.2
  have hprodA := RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm
  have hprodL := RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hP.prod.2.1
  rw [hP.prod.1, hP.prod.2.2] at hprodL
  rw [hA12, hP.prod.2.2] at hprodA
  have hc1 := h1.card_eq
  have hc2 := h2.card_eq
  have hcR := hR.card_eq
  rw [← hN] at hc2
  have hNpos : 0 < Nat.card ↥L₁ := Nat.card_pos
  have hLpos : 0 < Nat.card ↥(LBar z) := Nat.card_pos
  set k := (Nat.card ↥L₁).factorization 2 with hk
  rw [← hN] at hprodL
  have hfact : (Nat.card ↥(LBar z)).factorization 2 + 1 = 2 * k := by
    have h := congrArg (fun n => n.factorization 2) hprodL
    rw [Nat.factorization_mul hLpos.ne' (by norm_num), Finsupp.add_apply,
      Nat.factorization_mul hNpos.ne' hNpos.ne', Finsupp.add_apply] at h
    have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
    rw [h2] at h
    omega
  have hRk : Nat.card ↥(barOf z S ⊓ LBar z) = 2 ^ (2 * k - 1) := by
    rw [hcR]; congr 1; omega
  have hAk : Nat.card ↥((barOf z S ⊓ L₁) ⊔ (barOf z S ⊓ L₂)) = 2 ^ (2 * k - 1) := by
    rw [hc1, hc2] at hprodA
    have h22 : 2 ^ (2 * k) = 2 ^ (2 * k - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have : Nat.card ↥((barOf z S ⊓ L₁) ⊔ (barOf z S ⊓ L₂)) * 2 = 2 ^ (2 * k - 1) * 2 := by
      rw [hprodA, ← pow_add, ← h22]; congr 1; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact sup_le (inf_le_inf_left _ hL1) (inf_le_inf_left _ hL2)
  · rw [hAk, hRk]

@[expose] def rhoS (hS : IsSylowOf 2 S (Cen z)) : ↥S →* CentralizerBar z :=
  (toBar z).comp (Subgroup.inclusion (S_le_Cen hS))

omit [Finite G] in
theorem S_isPGroup (hS : IsSylowOf 2 S (Cen z)) : IsPGroup 2 ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS
  rw [← hQ]
  exact Q.isPGroup'.map (Cen z).subtype

theorem rhoS_injective (hS : IsSylowOf 2 S (Cen z)) : Function.Injective (rhoS hS) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro s hs
  have h1 : Subgroup.inclusion (S_le_Cen hS) s ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]; exact hs
  have hd : orderOf (⟨Subgroup.inclusion (S_le_Cen hS) s, h1⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
      Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hd
  have hodd : Odd (orderOf (Subgroup.inclusion (S_le_Cen hS) s)) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))) hd
  rw [orderOf_injective _ (Subgroup.inclusion_injective _)] at hodd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (S_isPGroup hS)) s
  rw [hk] at hodd
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    exact orderOf_eq_one_iff.1 (by simpa using hk)
  · exact absurd hodd (by
      rw [Nat.not_odd_iff_even]
      exact (Nat.even_pow.2 ⟨by norm_num, by omega⟩))

theorem isSL2Or2A7_of_pair (hz : IsCentralInvolution z) (hP : Stage1Pair G z S q L₁ L₂) :
    Stage1.Thm2.Recip.IsSL2Or2A7 ↥L₁ ∧ Stage1.Thm2.Recip.IsSL2Or2A7 ↥L₂ := by
  have h5 : 5 ≤ q := by
    obtain ⟨m, hm⟩ := hP.odd
    have := hP.gt3
    omega
  have hzb12 := IVK.Proofs2.Ivk93Adapt.zbarC_mem_inf hP
  have hzb1 := zbar_ne_one_of_central hz
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have hzb2 : orderOf (toBar z ⟨z, mem_Cen_self z⟩) = 2 := by
    apply orderOf_eq_prime _ hzb1
    rw [pow_two, ← map_mul]
    have : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hcen := toBar_z_mem_center z
  obtain ⟨F₁, iF₁, fF₁, hq₁, ⟨e₁⟩⟩ := hP.sl₁
  obtain ⟨F₂, iF₂, fF₂, hq₂, ⟨e₂⟩⟩ := hP.sl₂
  refine ⟨⟨Or.inl ⟨F₁, iF₁, fF₁, ⟨by rw [hq₁]; exact hP.odd, by rw [hq₁]; exact h5⟩, ⟨e₁⟩⟩, ?_⟩,
    ⟨Or.inl ⟨F₂, iF₂, fF₂, ⟨by rw [hq₂]; exact hP.odd, by rw [hq₂]; exact h5⟩, ⟨e₂⟩⟩, ?_⟩⟩
  · refine Stage1.Main.g2_card_center_two (by rw [hq₁]; exact hP.odd) e₁
      (ζ := ⟨toBar z ⟨z, mem_Cen_self z⟩, hzb12.1⟩) ?_ ?_
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.1 hcen g.1))
    · rw [Subgroup.orderOf_mk]; exact hzb2
  · refine Stage1.Main.g2_card_center_two (by rw [hq₂]; exact hP.odd) e₂
      (ζ := ⟨toBar z ⟨z, mem_Cen_self z⟩, hzb12.2⟩) ?_ ?_
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.1 hcen g.1))
    · rw [Subgroup.orderOf_mk]; exact hzb2

theorem isQuat_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IVK.IsQuaternionTwoGroup A n) : IVK.IsQuaternionTwoGroup B n :=
  ⟨h.1, ⟨e.symm.trans h.2.some⟩⟩

theorem psp4_quat (hz : IsCentralInvolution z)
    (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂) :
    ∃ a : ℕ, IVK.IsQuaternionTwoGroup ↥(barOf z S ⊓ L₁) a ∧
      IVK.IsQuaternionTwoGroup ↥(barOf z S ⊓ L₂) a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h1, h2⟩ := bar_sylow_structure hS hP
  obtain ⟨hQ1, hQ2⟩ := isSL2Or2A7_of_pair hz hP
  obtain ⟨Q₁, hQ₁⟩ := h1.exists_sylow_eq_subgroupOf
  obtain ⟨Q₂, hQ₂⟩ := h2.exists_sylow_eq_subgroupOf
  obtain ⟨n₁, hn₁⟩ := IVK.Lifted.sylow_quat_of_sl2or2a7 hQ1 Q₁
  obtain ⟨n₂, hn₂⟩ := IVK.Lifted.sylow_quat_of_sl2or2a7 hQ2 Q₂
  have e₁ : ↥(Q₁ : Subgroup ↥L₁) ≃* ↥(barOf z S ⊓ L₁) :=
    (MulEquiv.subgroupCongr hQ₁).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have e₂ : ↥(Q₂ : Subgroup ↥L₂) ≃* ↥(barOf z S ⊓ L₂) :=
    (MulEquiv.subgroupCongr hQ₂).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have hq₁ := isQuat_of_mulEquiv e₁ hn₁
  have hq₂ := isQuat_of_mulEquiv e₂ hn₂
  have hN : Nat.card ↥L₁ = Nat.card ↥L₂ := by
    obtain ⟨ht, hc, -⟩ := hsw
    rw [← hc]
    exact (Subgroup.card_map_of_injective (MulAut.conj (toBar z ⟨t, ht⟩)⁻¹).injective).symm
  have hc1 := h1.card_eq
  have hc2 := h2.card_eq
  rw [← hN] at hc2
  have hc1' := Stage1.Thm3.Sec6.card_of_isQuaternionTwoGroup hq₁
  have hc2' := Stage1.Thm3.Sec6.card_of_isQuaternionTwoGroup hq₂
  have : n₁ = n₂ := Nat.pow_right_injective (le_refl 2) (by show 2 ^ n₁ = 2 ^ n₂; rw [← hc1', ← hc2', hc1, hc2])
  subst this
  exact ⟨n₁, hq₁, hq₂⟩

omit [Finite G] in
theorem mem_barOf_S_iff (hS : IsSylowOf 2 S (Cen z)) (x : CentralizerBar z) :
    x ∈ barOf z S ↔ ∃ s : ↥S, rhoS hS s = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, S_le_Cen hS s.2⟩, s.2, rfl⟩

theorem pair_data_of_stage1_t (hz : IsCentralInvolution z)
    (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S)
    (htc : IsConj z t) (hsw : Swaps z t L₁ L₂) :
    ∃ (P₁ P₂ : Subgroup G) (a : ℕ), Psp4.PairData S P₁ P₂ z t a ∧ P₁ ⊔ P₂ = RC S z ∧
      barOf z P₁ ≤ L₁ ∧ barOf z P₂ ≤ L₂ ∧ Nat.card ↥P₁ = 2 ^ a ∧
      P₁ = (L₁.comap (rhoS hS)).map S.subtype ∧ P₂ = (L₂.comap (rhoS hS)).map S.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC := S_le_Cen hS
  have hzS := z_mem_of_sylow hz hS
  have hS2 := S_isPGroup hS
  have hρ := rhoS_injective hS
  obtain ⟨a, hq₁, hq₂⟩ := psp4_quat hz hS hP hsw
  obtain ⟨hAeq, hAinf⟩ := bar_sup_eq hz hS hP hsw
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  set ρ := rhoS hS with hρdef
  let P₁ : Subgroup G := (L₁.comap ρ).map S.subtype
  let P₂ : Subgroup G := (L₂.comap ρ).map S.subtype
  have hmem : ∀ (L : Subgroup (CentralizerBar z)) (g : G),
      g ∈ (L.comap ρ).map S.subtype ↔ ∃ hg : g ∈ S, ρ ⟨g, hg⟩ ∈ L := by
    intro L g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hρmul : ∀ s s' : ↥S, ρ (s * s') = ρ s * ρ s' := fun s s' => map_mul ρ s s'
  have hρz : ρ ⟨z, hzS⟩ = toBar z ⟨z, mem_Cen_self z⟩ := rfl
  have hzb12 := IVK.Proofs2.Ivk93Adapt.zbarC_mem_inf hP
  have hzP₁ : z ∈ P₁ := (hmem L₁ z).2 ⟨hzS, by rw [hρz]; exact hzb12.1⟩
  have hzP₂ : z ∈ P₂ := (hmem L₂ z).2 ⟨hzS, by rw [hρz]; exact hzb12.2⟩
  have hP₁S : P₁ ≤ S := Subgroup.map_subtype_le _
  have hP₂S : P₂ ≤ S := Subgroup.map_subtype_le _
  have hct : t * t = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hzb2 : orderOf (toBar z ⟨z, mem_Cen_self z⟩) = 2 := by
    apply orderOf_eq_prime _ (zbar_ne_one_of_central hz)
    rw [pow_two, ← map_mul]
    have : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hL12 : Subgroup.zpowers (toBar z ⟨z, mem_Cen_self z⟩) = L₁ ⊓ L₂ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzb12)
    rw [Nat.card_zpowers, hzb2]
    exact (le_of_eq hP.prod.2.2)
  have hρmem : ∀ (g : G) (hg : g ∈ S), ρ ⟨g, hg⟩ = toBar z ⟨g, hSC hg⟩ := fun _ _ => rfl
  have hbar : ∀ s : ↥S, ρ s ∈ barOf z S := fun s => (mem_barOf_S_iff hS _).2 ⟨s, rfl⟩
  have hinter : P₁ ⊓ P₂ = Subgroup.zpowers z := by
    apply le_antisymm
    · rintro g ⟨hg1, hg2⟩
      obtain ⟨hgS, hgL1⟩ := (hmem L₁ g).1 hg1
      obtain ⟨hgS2, hgL2⟩ := (hmem L₂ g).1 hg2
      have h12 : ρ ⟨g, hgS⟩ ∈ L₁ ⊓ L₂ := ⟨hgL1, hgL2⟩
      rw [← hL12] at h12
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h12
      have : ρ (⟨z, hzS⟩ ^ k) = ρ ⟨g, hgS⟩ := by rw [map_zpow, hρz]; exact hk
      have h3 := hρ this
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      exact congrArg Subtype.val h3
    · rw [Subgroup.zpowers_le]
      exact ⟨hzP₁, hzP₂⟩
  have hcomm : ∀ p ∈ P₁, ∀ r ∈ P₂, p * r = r * p := by
    intro p hp r hr
    obtain ⟨hpS, hpL⟩ := (hmem L₁ p).1 hp
    obtain ⟨hrS, hrL⟩ := (hmem L₂ r).1 hr
    have h1 := hP.prod.2.1 _ hpL _ hrL
    have h2 : ρ (⟨p, hpS⟩ * ⟨r, hrS⟩) = ρ (⟨r, hrS⟩ * ⟨p, hpS⟩) := by
      rw [hρmul, hρmul]; exact h1
    exact congrArg Subtype.val (hρ h2)
  obtain ⟨htC', hc1, hc2⟩ := hsw
  set tb : CentralizerBar z := toBar z ⟨t, htC'⟩ with htb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have : (⟨t, htC'⟩ : ↥(Cen z)) * ⟨t, htC'⟩ = 1 := Subtype.ext hct
    rw [this, map_one]
  have hconj : ∀ (Y : Subgroup (CentralizerBar z)) (x : CentralizerBar z),
      x ∈ conjugate Y tb ↔ tb * x * tb⁻¹ ∈ Y := fun Y x => by
    unfold conjugate
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hρt : ρ ⟨t, ht⟩ = tb := rfl
  have hswap : ∀ p ∈ P₁, t * p * t⁻¹ ∈ P₂ := by
    intro p hp
    obtain ⟨hpS, hpL⟩ := (hmem L₁ p).1 hp
    have hsS : t * p * t⁻¹ ∈ S := S.mul_mem (S.mul_mem ht hpS) (S.inv_mem ht)
    refine (hmem L₂ _).2 ⟨hsS, ?_⟩
    have h1 : ρ ⟨t * p * t⁻¹, hsS⟩ = tb * ρ ⟨p, hpS⟩ * tb⁻¹ := by
      have : (⟨t * p * t⁻¹, hsS⟩ : ↥S) = ⟨t, ht⟩ * ⟨p, hpS⟩ * ⟨t, ht⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hρt]
    rw [h1]
    exact (hconj L₂ _).1 (by rw [hc2]; exact hpL)
  have hL1 : L₁ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_left
  have hL2 : L₂ ≤ LBar z := by rw [← hP.prod.1]; exact le_sup_right
  have h2pow : ∀ g : ↥S, ∃ k : ℕ, (⟨(g : G), hSC g.2⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS2) g
    refine ⟨k, ?_⟩
    have : g ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hPL : ∀ L : Subgroup (CentralizerBar z), L ≤ LBar z →
      (L.comap ρ).map S.subtype ≤ RC S z := by
    intro L hL g hg
    obtain ⟨hgS, hgL⟩ := (hmem L g).1 hg
    refine ⟨hgS, ?_⟩
    obtain ⟨k, hk⟩ := h2pow ⟨g, hgS⟩
    exact (Stage1.Thm6.Prod.mem_LC_iff_of_pElt (z := z) ⟨g, hSC hgS⟩ hk).2 (hL hgL)
  have hsup : P₁ ⊔ P₂ = RC S z := by
    apply le_antisymm (sup_le (hPL L₁ hL1) (hPL L₂ hL2))
    intro r hr
    obtain ⟨hrS, hrL⟩ := hr
    have hrbar : ρ ⟨r, hrS⟩ ∈ barOf z S ⊓ LBar z := by
      refine ⟨hbar _, ?_⟩
      obtain ⟨k, hk⟩ := h2pow ⟨r, hrS⟩
      exact (Stage1.Thm6.Prod.mem_LC_iff_of_pElt (z := z) ⟨r, hSC hrS⟩ hk).1 hrL
    rw [hAeq] at hrbar
    obtain ⟨a₁, ha₁, a₂, ha₂, hprod⟩ :=
      Stage1.Main.exists_mul_of_mem_sup_of_commute'
        (A := barOf z S ⊓ L₁) (B := barOf z S ⊓ L₂)
        (fun x hx y hy => hP.prod.2.1 x hx.2 y hy.2) hrbar
    obtain ⟨s₁, hs₁⟩ := (mem_barOf_S_iff hS _).1 ha₁.1
    obtain ⟨s₂, hs₂⟩ := (mem_barOf_S_iff hS _).1 ha₂.1
    have hs₁P : (s₁ : G) ∈ P₁ := (hmem L₁ s₁).2 ⟨s₁.2, by rw [hs₁]; exact ha₁.2⟩
    have hs₂P : (s₂ : G) ∈ P₂ := (hmem L₂ s₂).2 ⟨s₂.2, by rw [hs₂]; exact ha₂.2⟩
    have h3 : ρ ⟨r, hrS⟩ = ρ (s₁ * s₂) := by rw [hρmul, hs₁, hs₂]; exact hprod
    have h4' : (⟨r, hrS⟩ : ↥S) = s₁ * s₂ := hρ h3
    have : r = (s₁ : G) * (s₂ : G) := congrArg Subtype.val h4'
    rw [this]
    exact Subgroup.mul_mem_sup hs₁P hs₂P
  have htnot : t ∉ P₁ ⊔ P₂ := by
    intro htm
    rw [hsup] at htm
    obtain ⟨-, htL⟩ := htm
    have htbL : tb ∈ LBar z := by
      obtain ⟨k, hk⟩ := h2pow ⟨t, ht⟩
      exact (Stage1.Thm6.Prod.mem_LC_iff_of_pElt (z := z) ⟨t, hSC ht⟩ hk).1 htL
    have hn1 : LBar z ≤ Subgroup.normalizer (L₁ : Set (CentralizerBar z)) := by
      rw [← hP.prod.1]
      exact sup_le Subgroup.le_normalizer
        (le_normalizer_of_commute (fun b hb a ha => (hP.prod.2.1 a ha b hb).symm))
    have hcj : conjugate L₁ tb = L₁ := by
      ext x
      rw [hconj]
      have := Subgroup.mem_normalizer_iff.1 (hn1 htbL) x
      exact this.symm
    exact hP.ne (by rw [← hc1, hcj])
  have hiso : ∀ L : Subgroup (CentralizerBar z),
      Nonempty (↥((L.comap ρ).map S.subtype) ≃* ↥(barOf z S ⊓ L)) := by
    intro L
    let f : ↥(L.comap ρ) →* ↥(barOf z S ⊓ L) :=
      (ρ.comp (L.comap ρ).subtype).codRestrict (barOf z S ⊓ L) (fun s => ⟨hbar s.1, s.2⟩)
    have hfinj : Function.Injective f := fun x y h =>
      Subtype.ext (hρ (congrArg Subtype.val h))
    have hfsurj : Function.Surjective f := by
      rintro ⟨x, hx1, hx2⟩
      obtain ⟨s, hs⟩ := (mem_barOf_S_iff hS x).1 hx1
      exact ⟨⟨s, by show ρ s ∈ L; rw [hs]; exact hx2⟩, Subtype.ext hs⟩
    exact ⟨((L.comap ρ).equivMapOfInjective S.subtype S.subtype_injective).symm.trans
      (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩)⟩
  have hq₁' : IVK.IsQuaternionTwoGroup ↥P₁ a := isQuat_of_mulEquiv (hiso L₁).some.symm hq₁
  have hq₂' : IVK.IsQuaternionTwoGroup ↥P₂ a := isQuat_of_mulEquiv (hiso L₂).some.symm hq₂
  have hbarle : ∀ (L : Subgroup (CentralizerBar z)), barOf z ((L.comap ρ).map S.subtype) ≤ L := by
    rintro L _ ⟨c, hc, rfl⟩
    obtain ⟨hcS, hcL⟩ := (hmem L c).1 hc
    exact hcL
  exact ⟨P₁, P₂, a, ⟨hzS, hz.1, fun s hs => (Subgroup.mem_centralizer_iff.1 (hSC hs) z
    (by simp)).symm, hP₁S, hP₂S, hq₁', hq₂', hinter, hcomm, ht, hct, htnot, hswap⟩, hsup,
    hbarle L₁, hbarle L₂, Stage1.Thm3.Sec6.card_of_isQuaternionTwoGroup hq₁', rfl, rfl⟩

theorem psp4_data_of_stage1_t (hz : IsCentralInvolution z)
    (hS : IsSylowOf 2 S (Cen z)) (h4 : Stage1PSp4 G z S q L₁ L₂) {t : G} (ht : t ∈ S)
    (htc : IsConj z t) (hsw : Swaps z t L₁ L₂) :
    ∃ (P₁ P₂ : Subgroup G) (a : ℕ), Psp4.Data S P₁ P₂ z t a ∧ P₁ ⊔ P₂ = RC S z ∧
      barOf z P₁ ≤ L₁ ∧ barOf z P₂ ≤ L₂ ∧ Nat.card ↥P₁ = 2 ^ a ∧
      P₁ = (L₁.comap (rhoS hS)).map S.subtype ∧ P₂ = (L₂.comap (rhoS hS)).map S.subtype := by
  obtain ⟨P₁, P₂, a, hd, hsup, hb1, hb2, hc, e1, e2⟩ :=
    pair_data_of_stage1_t hz hS h4.pair ht htc hsw
  exact ⟨P₁, P₂, a, hd.toData (by rw [hsup]; exact h4.index), hsup, hb1, hb2, hc, e1, e2⟩

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
