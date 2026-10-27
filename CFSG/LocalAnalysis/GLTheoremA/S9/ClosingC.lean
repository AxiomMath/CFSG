module

public import CFSG.LocalAnalysis.GLTheoremA.S9.ClosingB
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Step10

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9.Cl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.LocalBalance (autBar barAut barOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem closingC_top_eq_bot {Y : Type} [Group Y] (hO : GLAPPrimeCore 3 Y = ⊥) :
    GLAPPrimeCoreOf 3 (⊤ : Subgroup Y) = ⊥ := by
  have h5 := glaPPrimeCore_map_iso 3 (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
  rw [hO] at h5
  have h6 : GLAPPrimeCore 3 ↥(⊤ : Subgroup Y) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).injective).1 h5
  unfold GLAPPrimeCoreOf
  rw [h6, Subgroup.map_bot]

private theorem closingC_fixed_mul_pow {H : Type*} [Group H] {N : Subgroup H} {σ : H →* H}
    (hσ : ∀ g, σ (σ g) = g) {k : ℕ} (hk : Nat.card N = 2 * k + 1) {g : H}
    (hg : g⁻¹ * σ g ∈ N) :
    σ (g * (g⁻¹ * σ g) ^ (k + 1)) = g * (g⁻¹ * σ g) ^ (k + 1) := by
  have hnN : (g⁻¹ * σ g) ^ (2 * k + 1) = 1 := by
    have h := pow_card_eq_one' (G := N) (x := ⟨g⁻¹ * σ g, hg⟩)
    rw [hk] at h
    simpa using congrArg Subtype.val h
  have hσn : σ (g⁻¹ * σ g) = (g⁻¹ * σ g)⁻¹ := by
    rw [map_mul, map_inv, hσ, mul_inv_rev, inv_inv]
  have hσg : σ g = g * (g⁻¹ * σ g) := by group
  generalize g⁻¹ * σ g = n at hnN hσn hσg ⊢
  have key : n ^ (k + 1) * n ^ (k + 1) = n := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by omega, pow_succ, hnN, one_mul]
  rw [map_mul, map_pow, hσn, hσg, inv_pow, mul_assoc]
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  exact key.symm

private theorem closingC_exists_fixed_lift {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    (hodd : Odd (Nat.card N)) {σ : H →* H} (hσ : ∀ g, σ (σ g) = g) (hN : N ≤ N.comap σ) {x : H ⧸ N}
    (hx : QuotientGroup.map N N σ hN x = x) : ∃ g : H, σ g = g ∧ (g : H ⧸ N) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hodd
  have hg : g⁻¹ * σ g ∈ N := by
    rw [QuotientGroup.map_mk] at hx
    exact QuotientGroup.eq.mp hx.symm
  refine ⟨g * (g⁻¹ * σ g) ^ (k + 1), closingC_fixed_mul_pow hσ hk hg, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (N.pow_mem hg _), mul_one]

theorem normalizes_of_cent_involution {X K : Subgroup G} {z : G} (hK : GLAPComponent 3 X K)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 X))) (hzK : z ∈ K) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    X ⊓ cx z ≤ Subgroup.normalizer (K : Set G) := by
  rintro g ⟨hgX, hgz⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hzX : z ∈ X := hK.1 hzK
  have hgz' : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hgz
  rw [mem_normalizer_iff_gLBConj_eq]
  have hK₂ : GLAPComponent 3 X (GLBConj g K) := by
    have h := glaPComponent_gLBConj hK g
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hgX)] at h
  have hzK₂ : z ∈ GLBConj g K := by
    rw [mem_gLBConj, hgz', mul_inv_cancel_right]
    exact hzK
  by_contra hne
  have hbar : barX 3 X K ≠ barX 3 X (GLBConj g K) :=
    fun h => hne (glaPComponent_unique hK hK₂ h).symm
  have hc1 : CFSG.IsComponent (barX 3 X K) := (CFSG.isComponent_iff_open _).2 hK.2.2.1
  have hc2 : CFSG.IsComponent (barX 3 X (GLBConj g K)) :=
    (CFSG.isComponent_iff_open _).2 hK₂.2.2.1
  have hcomm : ⁅barX 3 X K, barX 3 X (GLBConj g K)⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hc1 hc2 with h | h
    · exact absurd h hbar
    · exact h
  set zb : ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨z, hzX⟩ : ↥X)
    with hzb
  have hzb1 : zb ∈ barX 3 X K := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hzK)
  have hzb2 : zb ∈ barX 3 X (GLBConj g K) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hzK₂)
  have hcentr : ∀ k ∈ barX 3 X K, k * zb = zb * k := by
    intro k hk
    have hk2 : k ∈ Subgroup.centralizer (barX 3 X (GLBConj g K) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hk
    exact (Subgroup.mem_centralizer_iff.1 hk2 zb hzb2).symm
  have hzb_sq : zb ^ 2 = 1 := by
    have h1 : (⟨z, hzX⟩ : ↥X) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    rw [hzb, ← map_pow, h1, map_one]
  have hMle : Subgroup.zpowers zb ≤ barX 3 X K := Subgroup.zpowers_le.2 hzb1
  have hMc : Subgroup.zpowers zb ≤
      Subgroup.centralizer (barX 3 X K : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun k hk => hcentr k hk)
  have hKle : barX 3 X K ≤
      Subgroup.normalizer ((Subgroup.zpowers zb : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    (Subgroup.le_centralizer_iff.1 hMc).trans (Subgroup.centralizer_le_normalizer _)
  have hMn : ((Subgroup.zpowers zb).subgroupOf (barX 3 X K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMle).2 hKle
  have hcop : Nat.Coprime 3 (Nat.card ((Subgroup.zpowers zb).subgroupOf (barX 3 X K))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMle).toEquiv, Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hzb_sq) (by norm_num)
  have hsub : (Subgroup.zpowers zb).subgroupOf (barX 3 X K) ≤ GLAPPrimeCore 3 ↥(barX 3 X K) :=
    le_sSup ⟨hMn, hcop⟩
  have hMO : Subgroup.zpowers zb ≤ GLAPPrimeCoreOf 3 (barX 3 X K) := by
    calc Subgroup.zpowers zb
        = ((Subgroup.zpowers zb).subgroupOf (barX 3 X K)).map (barX 3 X K).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hMle).symm
      _ ≤ (GLAPPrimeCore 3 ↥(barX 3 X K)).map (barX 3 X K).subtype := Subgroup.map_mono hsub
  have hKO : GLAPPrimeCoreOf 3 (barX 3 X K) ≤
      GLAPPrimeCoreOf 3 (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp3 hK.2.2.1.2.1
  have hY : GLAPPrimeCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hzb_one : zb = 1 := by
    have h := hMO.trans (hKO.trans (le_of_eq (closingC_top_eq_bot hY)))
    exact Subgroup.mem_bot.1 (h (Subgroup.mem_zpowers zb))
  have hzO : (⟨z, hzX⟩ : ↥X) ∈ GLAPPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 hzb_one
  have hzO' : z ∈ GLAPPrimeCoreOf 3 X := ⟨⟨z, hzX⟩, hzO, rfl⟩
  have hdvd : orderOf z ∣ Nat.card (GLAPPrimeCoreOf 3 X) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hzO')
    rwa [Nat.card_zpowers] at h
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
  · exact hz1 (orderOf_eq_one_iff.1 h1)
  · rw [h1] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem barX_pCoreOf_two_le {X : Subgroup G} {z : G} (hzX : z ∈ X) (hz2 : z ^ 2 = 1)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 X))) :
    barX 3 X (pCoreOf 2 (cx z) ⊓ X) ≤
      pCoreOf 2 (Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨z, hzX⟩} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddO : Odd (Nat.card (GLAPPrimeCore 3 ↥X)) := by
    have h := hodd
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective X)] at h
  set z' : ↥X := ⟨z, hzX⟩ with hz'
  have hz'2 : z' * z' = 1 := by
    apply Subtype.ext
    show z * z = 1
    rw [← pow_two]
    exact hz2
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  let σ : ↥X →* ↥X := (MulAut.conj z').toMonoidHom
  have hσ : ∀ g, σ (σ g) = g := by
    intro g
    show z' * (z' * g * z'⁻¹) * z'⁻¹ = g
    rw [hz'inv]
    calc z' * (z' * g * z') * z' = (z' * z') * g * (z' * z') := by group
      _ = g := by rw [hz'2]; group
  have hN : GLAPPrimeCore 3 ↥X ≤ (GLAPPrimeCore 3 ↥X).comap σ := by
    intro o ho
    rw [Subgroup.mem_comap]
    exact (GLAPPrimeCore.normal 3 ↥X).conj_mem o ho z'
  have hlift : ∀ h ∈ Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) z'} :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)),
      ∃ g : ↥X, (g : G) ∈ cx z ∧ QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g = h := by
    intro h hh
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective h
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    have hxmem : (x * z')⁻¹ * (z' * x) ∈ GLAPPrimeCore 3 ↥X := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hh
    have hfix : QuotientGroup.map (GLAPPrimeCore 3 ↥X) (GLAPPrimeCore 3 ↥X) σ hN
        (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) = (x : ↥X ⧸ GLAPPrimeCore 3 ↥X) := by
      rw [QuotientGroup.map_mk]
      apply QuotientGroup.eq.2
      have e : (σ x)⁻¹ * x = (x * z')⁻¹ * (z' * x) := by
        show (z' * x * z'⁻¹)⁻¹ * x = (x * z')⁻¹ * (z' * x)
        simp only [mul_inv_rev, hz'inv, mul_assoc]
      rw [e]
      exact hxmem
    obtain ⟨g, hgσ, hgx⟩ := closingC_exists_fixed_lift hoddO hσ hN hfix
    refine ⟨g, ?_, hgx⟩
    have h1 : z' * g * z'⁻¹ = g := hgσ
    rw [hz'inv] at h1
    have h2 : z' * g = g * z' := by
      have h3 := congrArg (· * z') h1
      simpa only [mul_assoc, hz'2, mul_one] using h3
    have h4 : z * (g : G) = (g : G) * z := congrArg Subtype.val h2
    exact Subgroup.mem_centralizer_singleton_iff.2 h4.symm
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (cx z) ⊓ X) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cx z)).to_le inf_le_left
  have hbar2 : IsPGroup 2 (barX 3 X (pCoreOf 2 (cx z) ⊓ X)) :=
    (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      pCoreOf 2 (cx z) ⊓ X ≤ X)).symm).map _
  have hle : barX 3 X (pCoreOf 2 (cx z) ⊓ X) ≤
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) z'} :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' := Subgroup.mem_subgroupOf.1 hq
    have hqc : (q : G) ∈ cx z :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 (cx z) (Subgroup.mem_inf.1 hq').1
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (q : G) * z = z * (q : G)
    exact Subgroup.mem_centralizer_singleton_iff.1 hqc
  have hnorm : Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) z'} :
      Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≤
      Subgroup.normalizer ((barX 3 X (pCoreOf 2 (cx z) ⊓ X) :
        Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro h hh
    obtain ⟨g, hgC, rfl⟩ := hlift h hh
    have key : ∀ g' : ↥X, (g' : G) ∈ cx z → ∀ m ∈ barX 3 X (pCoreOf 2 (cx z) ⊓ X),
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g' * m *
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g')⁻¹ ∈
            barX 3 X (pCoreOf 2 (cx z) ⊓ X) := by
      intro g' hg' m hm
      obtain ⟨q, hq, rfl⟩ := hm
      have hq' := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)
      have hconj : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g' *
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) q *
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g')⁻¹ =
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (g' * q * g'⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [hconj]
      refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
      have hnq : (g' : G) * (q : G) * (g' : G)⁻¹ ∈ pCoreOf 2 (cx z) :=
        (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (cx z) hg') _).1 hq'.1
      show (g' : G) * (q : G) * (g' : G)⁻¹ ∈ pCoreOf 2 (cx z) ⊓ X
      exact Subgroup.mem_inf.2 ⟨hnq, X.mul_mem (X.mul_mem g'.2 hq'.2) (X.inv_mem g'.2)⟩
    refine Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn => key g hgC n hn, fun hn => ?_⟩
    have h1 := key g⁻¹ (by rw [Subgroup.coe_inv]; exact (cx z).inv_mem hgC) _ hn
    rw [map_inv] at h1
    have e : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g)⁻¹ *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g * n *
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g)⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) g)⁻¹)⁻¹ = n := by
      group
    rwa [e] at h1
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hnorm) hbar2

theorem no_two_group_centralizing_component {Y : Type} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore 3 Y = ⊥) {K : Subgroup Y} (hK : IsComponentOf K ⊤) {z : Y} (hzK : z ∈ K)
    {S : Subgroup Y} (hS2 : IsPGroup 2 S)
    (hSz : S ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set Y)))
    (hSK : S ≤ Subgroup.centralizer (K : Set Y)) : S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm2 : ∀ M : Subgroup Y, M.Normal → IsPGroup 2 M → M = ⊥ := by
    intro M hMn hM2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hM2
    have hcop : Nat.Coprime 3 (Nat.card M) := by
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    have hle : M ≤ GLAPPrimeCore 3 Y := le_sSup ⟨hMn, hcop⟩
    rw [hO] at hle
    exact le_bot_iff.1 hle
  have hKc : CFSG.IsComponent K := (CFSG.isComponent_iff_open K).2 hK
  have hcompN : ∀ K' : Subgroup Y, CFSG.IsComponent K' → K' ≤ Subgroup.normalizer (K : Set Y) := by
    intro K' hK'
    rcases CFSG.LocalCores.distinct_components_commute hKc hK' with h | h
    · rw [← h]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((Subgroup.commutator_comm K' K).trans h)).trans (Subgroup.centralizer_le_normalizer _)
  have hKlayer : K ≤ CFSG.layer Y := by
    rw [CFSG.layer.eq_sSup]
    exact le_sSup hKc
  have hlayerN : CFSG.layer Y ≤ Subgroup.normalizer (K : Set Y) := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun K' hK' => hcompN K' hK'
  have hFN : CFSG.generalizedFitting Y ≤ Subgroup.normalizer (K : Set Y) := by
    rw [CFSG.generalizedFitting.eq_sup]
    refine sup_le ?_ hlayerN
    have h1 : CFSG.fittingSubgroup Y ≤ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (CFSG.LocalCores.fitting_layer_commute (G := Y))
    exact (h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hKlayer))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hFnorm : (CFSG.generalizedFitting Y).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  have hRN_aux : ∀ n ∈ Subgroup.normalizer (K : Set Y), ∀ r ∈ Subgroup.centralizer (K : Set Y),
      n * r * n⁻¹ ∈ Subgroup.centralizer (K : Set Y) := by
    intro n hn r hr
    rw [Subgroup.mem_centralizer_iff] at hr ⊢
    intro k hk
    have hk' : n⁻¹ * k * n ∈ K := by
      apply (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * k * n)).2
      have e : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
      rw [e]
      exact hk
    have h := hr (n⁻¹ * k * n) hk'
    calc k * (n * r * n⁻¹) = n * ((n⁻¹ * k * n) * r) * n⁻¹ := by group
      _ = n * (r * (n⁻¹ * k * n)) * n⁻¹ := by rw [h]
      _ = n * r * n⁻¹ * k := by group
  have hNR : Subgroup.normalizer (K : Set Y) ≤
      Subgroup.normalizer ((Subgroup.centralizer (K : Set Y) : Subgroup Y) : Set Y) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hRN_aux n hn r hr
    · intro hr
      have h := hRN_aux n⁻¹ (inv_mem hn) _ hr
      have e : n⁻¹ * (n * r * n⁻¹) * n⁻¹⁻¹ = r := by group
      rwa [e] at h
  have hcR : ∀ r ∈ Subgroup.centralizer (K : Set Y), r ∈ Subgroup.centralizer ({z} : Set Y) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hr z hzK).symm
  have hpcR : pCoreOf 2 (Subgroup.centralizer (K : Set Y)) ≤
      pCoreOf 2 (Subgroup.normalizer (K : Set Y)) := by
    have hle : pCoreOf 2 (Subgroup.centralizer (K : Set Y)) ≤ Subgroup.normalizer (K : Set Y) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.centralizer_le_normalizer _)
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
        (hNR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hpcN : pCoreOf 2 (Subgroup.normalizer (K : Set Y)) = ⊥ := by
    have hyF : ∀ y : Y, y ∈ Subgroup.normalizer ((CFSG.generalizedFitting Y : Subgroup Y) : Set Y) := by
      intro y
      rw [Subgroup.normalizer_eq_top_iff.2 hFnorm]
      exact Subgroup.mem_top y
    have hP0 : pCoreOf 2 (CFSG.generalizedFitting Y) = ⊥ := by
      have hPn : (pCoreOf 2 (CFSG.generalizedFitting Y)).Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
        intro y _
        exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hyF y)
      exact hnorm2 _ hPn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    have hTN : Subgroup.normalizer (K : Set Y) ≤
        Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (K : Set Y)) : Subgroup Y) : Set Y) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hTF : pCoreOf 2 (Subgroup.normalizer (K : Set Y)) ⊓ CFSG.generalizedFitting Y = ⊥ := by
      have hle : pCoreOf 2 (Subgroup.normalizer (K : Set Y)) ⊓ CFSG.generalizedFitting Y ≤
          pCoreOf 2 (CFSG.generalizedFitting Y) := by
        refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
            (Subgroup.normalizer (K : Set Y))).to_le inf_le_left)
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 ?_
        intro f hf
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp only [SetLike.mem_coe, Subgroup.mem_inf]
        exact and_congr (Subgroup.mem_normalizer_iff.1 (hTN (hFN hf)) x)
          (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hf) x)
      rw [hP0] at hle
      exact le_bot_iff.1 hle
    have hcomm : ⁅pCoreOf 2 (Subgroup.normalizer (K : Set Y)), CFSG.generalizedFitting Y⁆ = ⊥ := by
      refine le_antisymm ?_ bot_le
      rw [← hTF]
      refine Subgroup.commutator_le.2 fun t ht f hf => ?_
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : f * t⁻¹ * f⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (K : Set Y)) :=
          (Subgroup.mem_normalizer_iff.1 (hTN (hFN hf)) t⁻¹).1
            ((pCoreOf 2 (Subgroup.normalizer (K : Set Y))).inv_mem ht)
        simpa only [mul_assoc] using (pCoreOf 2 (Subgroup.normalizer (K : Set Y))).mul_mem ht h1
      · rw [commutatorElement_def]
        exact (CFSG.generalizedFitting Y).mul_mem (hFnorm.conj_mem f hf t)
          ((CFSG.generalizedFitting Y).inv_mem hf)
    have hTle : pCoreOf 2 (Subgroup.normalizer (K : Set Y)) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set Y)) ⊓ CFSG.generalizedFitting Y :=
      le_inf le_rfl ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans
        (CFSG.centralizer_generalizedFitting_le Y))
    rw [hTF] at hTle
    exact le_bot_iff.1 hTle
  have hSR : S ≤ pCoreOf 2 (Subgroup.centralizer (K : Set Y)) := by
    have hPR : pCoreOf 2 (Subgroup.centralizer ({z} : Set Y)) ⊓ Subgroup.centralizer (K : Set Y) ≤
        pCoreOf 2 (Subgroup.centralizer (K : Set Y)) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer ({z} : Set Y))).to_le
          inf_le_left)
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 ?_
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [SetLike.mem_coe, Subgroup.mem_inf]
      exact and_congr
        (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hcR r hr)) x)
        (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hr) x)
    exact (le_inf hSz hSK).trans hPR
  exact le_bot_iff.1 (hSR.trans (hpcR.trans hpcN.le))

theorem not_le_centMod_of_two_core {X K S : Subgroup G} {z : G} (hK : GLAPComponent 3 X K)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 X))) (hzK : z ∈ K) (hz2 : z ^ 2 = 1)
    (hSX : S ≤ X) (hS2 : IsPGroup 2 S) (hSz : S ≤ pCoreOf 2 (cx z)) (hS1 : S ≠ ⊥) :
    ¬ S ≤ centModSubgroup 3 K := by
  intro hSCM
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzX : z ∈ X := hK.1 hzK
  have hY : GLAPPrimeCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hKbar : IsComponentOf (barX 3 X K) ⊤ := hK.2.2.1
  have hzbK : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨z, hzX⟩ ∈ barX 3 X K :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hzK)
  have hSb2 : IsPGroup 2 (barX 3 X S) :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm).map _
  have hSbz : barX 3 X S ≤ pCoreOf 2 (Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨z, hzX⟩} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) :=
    (barX_mono 3 (le_inf hSz hSX)).trans (barX_pCoreOf_two_le hzX hz2 hodd)
  have hSbK : barX 3 X S ≤ Subgroup.centralizer (barX 3 X K : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have h1 : ⁅t, s⁆ ∈ GLAPPrimeCoreOf 3 K := (hSCM hs).2 t ht
    have h3 : ⁅t, s⁆ ∈ GLAPPrimeCoreOf 3 X :=
      glaPPrimeCoreOf_le_of_isSubnormal hp3 hK.2.1 h1
    have h4 := Subgroup.inv_mem _ h3
    rwa [commutatorElement_inv] at h4
  have hSb : barX 3 X S = ⊥ := no_two_group_centralizing_component hY hKbar hzbK hSb2 hSbz hSbK
  have hSle : S ≤ GLAPPrimeCoreOf 3 X := by
    intro s hs
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨s, hSX hs⟩ ∈ barX 3 X S :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
    rw [hSb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨s, hSX hs⟩, h1, rfl⟩
  rcases hS2.card_eq_or_dvd with h | h
  · exact hS1 (Subgroup.card_eq_one.1 h)
  · have h2 : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 X) := h.trans (Subgroup.card_dvd_of_le hSle)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem Z_not_le_centMod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X K Z T : Subgroup G} {z : G}
    (hK : GLAPComponent 3 X K) (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 X))) (hzK : z ∈ K)
    (hz2 : z ^ 2 = 1) (hZX : Z ≤ X) (hTX : T ≤ X) (hZq : IsPGroup q Z) (hT2 : IsPGroup 2 T)
    (hTz : T ≤ pCoreOf 2 (cx z)) (hZN : Z ≤ Subgroup.normalizer (K : Set G))
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) (hZT : Z ≤ Subgroup.normalizer (T : Set G))
    (hST : (⁅Z, T⁆ : Subgroup G) ≠ ⊥) : ¬ Z ≤ centModSubgroup 3 K := by
  intro hZ
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := ⁅Z, T⁆ with hSdef
  have hSle : S ≤ T := by
    rw [hSdef, Subgroup.commutator_le]
    intro u hu t ht
    have h := (Subgroup.mem_normalizer_iff.1 (hZT hu) t).1 ht
    rw [commutatorElement_def]
    exact T.mul_mem h (T.inv_mem ht)
  have hSN : S ≤ Subgroup.normalizer (K : Set G) := hSle.trans hTN
  have hcop : Nat.Coprime (Nat.card Z) (Nat.card T) :=
    IsPGroup.coprime_card_of_ne q 2 hq2 Z T hZq hT2
  have hsolv : Group.IsSolvable ↥T := by
    haveI := hT2.isNilpotent
    infer_instance
  have hdbl : (⁅⁅T, Z⁆, Z⁆ : Subgroup G) = ⁅T, Z⁆ := GL83.commutator_double_eq_self Z T hZT hcop hsolv
  have hSS : (⁅S, Z⁆ : Subgroup G) = S := by
    rw [hSdef, Subgroup.commutator_comm Z T, hdbl]
  have hSCM : S ≤ centModSubgroup 3 K := S3.le_centModSubgroup_of_comm hZ hSN hSS.ge
  exact not_le_centMod_of_two_core hK hodd hzK hz2 (hSle.trans hTX) (hT2.to_le hSle)
    (hSle.trans hTz) hST hSCM

theorem pCoreOf_le_glaPPrimeCoreOf_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (X : Subgroup G) : pCoreOf q X ≤ GLAPPrimeCoreOf p X := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  refine Subgroup.map_mono (le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal q, ?_⟩)
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) q).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hq).2 hqp.symm)

theorem K_type (hc : S9Ctx G 3) (h1431 : I1431ClAt G) (hrank : GLATwoLocalRank 3 G = 4) {a x : G}
    {K J : Subgroup G} (ha3 : orderOf a = 3) (hxa : x ∈ cx a) (hx3 : orderOf x = 3)
    (hxna : x ∉ Subgroup.zpowers a) (hK : GLAPComponent 3 (cx a) K)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hJ : GLAPComponent 3 (K ⊓ cx x) J)
    (hJt : catalogIs (PSimple 3 J) isU4two) (ha1 : a ≠ 1) : catalogIs (PSimple 3 K) isTableU4 := by
  have hp3 : Nat.Prime 3 := by norm_num
  by_cases hcov : K ≤ J ⊔ GLAPPrimeCoreOf 3 K
  · have hJK : J ≤ K := hJ.1.trans inf_le_left
    have hsup : J ⊔ GLAPPrimeCoreOf 3 K = K :=
      le_antisymm (sup_le hJK (Subgroup.map_subtype_le _)) hcov
    obtain ⟨-, ⟨e⟩⟩ := cover_facts hp3 hJK hsup
    obtain ⟨f⟩ := nonempty_pSimple_congr e
    exact catalogIs_mono (fun i hi => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi)))))
      ((catalogIs_congr f).1 hJt)
  · have h := h1431 a x K J ha3 (isKGroup_cx hc ha1) hxa hx3 hxna hK hxK hJ hJt hcov hrank.le
    obtain ⟨i, hi, e⟩ := h
    rcases hi with hi | hi | hi | hi | hi | hi
    · exact absurd ⟨i, hi, e⟩ (hc.stage8.2 rfl hrank a K ha3 hK)
    · exact ⟨i, Or.inr (Or.inl hi), e⟩
    · exact ⟨i, Or.inl hi, e⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inl hi))), e⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi)))), e⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inl hi)), e⟩

theorem Z_le_centMod_of_table (htab : U4TableAt G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {K Bs S Z J X : Subgroup G} {x : G} (hK : GLAPComponent 3 X K)
    (hBN : Bs ≤ Subgroup.normalizer (K : Set G)) (hSZN : S ⊔ Z ≤ Subgroup.normalizer (K : Set G))
    (hxBs : x ∈ Bs) (hx3 : x ^ 3 = 1) (hZq : IsPGroup q Z)
    (hZx : Z ≤ GLAPPrimeCoreOf 3 (cx x)) (hJ : GLAPComponent 3 (K ⊓ cx x) J)
    (hJt : catalogIs (PSimple 3 J) isU4two) (hKt : catalogIs (PSimple 3 K) isTableU4) :
    Z ≤ centModSubgroup 3 K := by
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZN : Z ≤ Subgroup.normalizer (K : Set G) := le_sup_right.trans hSZN
  have hW : Bs ⊔ (S ⊔ Z) ⊔ K ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le hBN hSZN) Subgroup.le_normalizer
  have himg := image_le_core hp3 hBN hSZN hxBs hx3 (le_sup_right : Z ≤ S ⊔ Z) hZx
  have hxW : x ∈ Bs ⊔ (S ⊔ Z) ⊔ K := Subgroup.mem_sup_left (Subgroup.mem_sup_left hxBs)
  have h2 := htab K (Bs ⊔ (S ⊔ Z) ⊔ K) x hW hxW ⟨X, hK⟩ le_sup_right hx3 hKt ⟨J, hJ, hJt⟩
  have hZ2 : IsPGroup 2 (autBar 3 Z K) := h2.to_le himg
  have hZq' : IsPGroup q (autBar 3 Z K) := isPGroup_autBar hZq
  have hbot : autBar 3 Z K = ⊥ :=
    disjoint_self.1 (IsPGroup.disjoint_of_ne q 2 hq2 _ _ hZq' hZ2)
  intro w hw
  have hmem := barAut_mem_autBar (p := 3) hZN hw
  rw [hbot, Subgroup.mem_bot] at hmem
  exact centMod_iff.1 (centMod_of_barAut_eq_one (hZN hw) hmem)

theorem orderOf_eq_three {D : Subgroup G} (hD : IsElemAbelian 3 D) {a : G} (haD : a ∈ D)
    (ha1 : a ≠ 1) : orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (hD.2 a haD) ha1

theorem not_mem_zpowers_symm {a x : G} (ha3 : orderOf a = 3) (hx3 : orderOf x = 3)
    (hax : a ∉ Subgroup.zpowers x) : x ∉ Subgroup.zpowers a := by
  intro hxa
  apply hax
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hxa
  have hcard : Nat.card (Subgroup.zpowers a) ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hx3]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact Subgroup.mem_zpowers a

theorem final_contra (hc : S9Ctx G 3) (hrank : GLATwoLocalRank 3 G = 4) (h183 : Input18_3_4)
    (h112 : I112RkAt G) (h1431 : I1431ClAt G) (htab : U4TableAt G) {B : Subgroup G} {x : G}
    {L Q₁ : Subgroup G} {q : ℕ} (hC : Contra92 3 B x L q Q₁)
    (hZc : Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ Subgroup.centralizer (L : Set G))
    {y z : G} {Bs D J E₀ : Subgroup G} (hcfg : Cfg x y z L Bs D J E₀) : False := by
  have hp3 : Nat.Prime 3 := hc.ctx.prime
  have hx1 : x ≠ 1 := hC.h.ne_one
  have hq : q.Prime := hC.setup.prime
  have hq2 : q ≠ 2 := hC.setup.ne_two
  have hq3 : q ≠ 3 := hC.setup.ne_p
  set Z : Subgroup G := Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G) with hZdef
  have hQ₁q : IsPGroup q Q₁ := by
    haveI : Fact q.Prime := ⟨hq⟩
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup q L).to_le hC.setup.le_core
  have hZne : Z ≠ ⊥ := center_ne_bot_of_isPGroup hq hQ₁q hC.setup.ne_bot
  have hZq : IsPGroup q Z := hQ₁q.to_le inf_le_left
  have hZQ : Z ≤ Q₁ := inf_le_left
  have hZL : Z ≤ L := hZQ.trans hC.le_L
  have hZcL : Z ≤ Subgroup.centralizer (L : Set G) := hZc
  have hZcx : Z ≤ cx x := hZL.trans hC.h.comp.1
  have hZO : Z ≤ pCoreOf q (cx x) := hZQ.trans hC.le_pCoreOf_cx
  have hzL : z ∈ L := hcfg.J_L hcfg.z_J
  have hZz : Z ≤ cx z := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hZcL hu) z hzL).symm
  have hxD : x ∈ D := by
    rw [hcfg.D_gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) := by
    rw [hcfg.D_gen]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (hZcx hu)
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      exact (Subgroup.mem_centralizer_iff.1 (hZcL hu) y hcfg.y_L).symm
  have hZD : Z ≤ Subgroup.centralizer (D : Set G) := Subgroup.le_centralizer_iff.1 hDZ
  obtain ⟨a, haD, ha1, hDa, hax, hS⟩ := exists_a_S hc hq hq2 hcfg hx1 hZne hZq hZz hZD hZO
  have hrk4 : GLATwoLocalRank 3 G ≤ 4 := hrank.le
  have hodd := odd_core_ca hc hrank hcfg haD
  have ha3 : orderOf a = 3 := orderOf_eq_three hcfg.D_el haD ha1
  have hx3 : orderOf x = 3 := orderOf_eq_three hcfg.D_el hxD hx1
  have hxna : x ∉ Subgroup.zpowers a := not_mem_zpowers_symm ha3 hx3 hax
  have hxa : x ∈ cx a := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    exact isElemAbelian_commute hcfg.D_el hxD haD
  have hDa' : Subgroup.centralizer (D : Set G) = cx a ⊓ cx x := by
    rw [centralizer_eq_inf_of_gen (D := D) (u := a) (v := x) (by rw [← hDa, sup_comm])]
  have hKc := ja_single_cl hc h183 h112 hcfg.bs_bmax hcfg.D_le hcfg.D_el hcfg.D_card haD ha1
    hcfg.J_comp ⟨E₀, hcfg.E₀_le, hcfg.E₀_el, hcfg.E₀_card.ge⟩
  set K : Subgroup G := closureIn J (GLAPLayer 3 (cx a)) with hKdef
  have hJK : J ≤ K := le_closureIn_self J _
  have hzK : z ∈ K := hJK hcfg.z_J
  have hnorm : cx a ⊓ cx z ≤ Subgroup.normalizer (K : Set G) :=
    normalizes_of_cent_involution hKc hodd hzK hcfg.z_sq hcfg.z_ne
  set T : Subgroup G := pCoreOf 2 (cx z) ⊓ cx a with hTdef
  have hZa : Z ≤ cx a := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hZD hu) a haD).symm
  have hZN : Z ≤ Subgroup.normalizer (K : Set G) := fun u hu => hnorm ⟨hZa hu, hZz hu⟩
  have hTcz : T ≤ cx z := inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 (cx z))
  have hTa : T ≤ cx a := inf_le_right
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := fun u hu => hnorm ⟨hTa hu, hTcz hu⟩
  have hT2 : IsPGroup 2 T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cx z)).to_le inf_le_left
  have hZT : Z ≤ Subgroup.normalizer (T : Set G) := by
    intro u hu
    have h1 : u ∈ Subgroup.normalizer (pCoreOf 2 (cx z) : Set G) :=
      le_normalizer_pCoreOf 2 (cx z) (hZz hu)
    have h2 : u ∈ Subgroup.normalizer ((cx a : Subgroup G) : Set G) := Subgroup.le_normalizer (hZa hu)
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (h1 h) (h2 h)
  have hZnc : ¬ Z ≤ centModSubgroup 3 K :=
    Z_not_le_centMod hq hq2 hKc hodd hzK hcfg.z_sq hZa hTa hZq hT2 inf_le_left hZN hTN hZT hS
  have hxz : x ∈ cx z := hcfg.Bs_z (hcfg.D_le hxD)
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hnorm ⟨hxa, hxz⟩
  have hJcD : J ≤ Subgroup.centralizer (D : Set G) := Subgroup.le_centralizer_iff.1 hcfg.D_cJ
  have hJKx : GLAPComponent 3 (K ⊓ cx x) J := by
    refine glaPComponent_of_le hp3 (A := Subgroup.centralizer (D : Set G)) hcfg.J_comp
      (le_inf hJK (hJcD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD)))) ?_
    rw [hDa']
    exact inf_le_inf_right _ hKc.1
  have hKt : catalogIs (PSimple 3 K) isTableU4 :=
    K_type hc h1431 hrank ha3 hxa hx3 hxna hKc hxK hJKx hcfg.J_type ha1
  have hBsa : Bs ≤ cx a := isElemAbelian_le_centralizer hcfg.bs_bmax.1 (hcfg.D_le haD)
  have hBN : Bs ≤ Subgroup.normalizer (K : Set G) := fun u hu => hnorm ⟨hBsa hu, hcfg.Bs_z hu⟩
  have hST : (⁅Z, T⁆ : Subgroup G) ≤ T := by
    rw [Subgroup.commutator_le]
    intro u hu t ht
    have h := (Subgroup.mem_normalizer_iff.1 (hZT hu) t).1 ht
    rw [commutatorElement_def]
    exact T.mul_mem h (T.inv_mem ht)
  have hSZN : (⁅Z, T⁆ : Subgroup G) ⊔ Z ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (hST.trans hTN) hZN
  have hx3' : x ^ 3 = 1 := hcfg.D_el.2 x hxD
  have hZx : Z ≤ GLAPPrimeCoreOf 3 (cx x) :=
    hZO.trans (pCoreOf_le_glaPPrimeCoreOf_of_ne hp3 hq hq3 (cx x))
  have hZcm : Z ≤ centModSubgroup 3 K :=
    Z_le_centMod_of_table htab hq hq2 (X := cx a) hKc hBN hSZN (hcfg.D_le hxD) hx3' hZq hZx hJKx
      hcfg.J_type hKt
  exact hZnc hZcm

end CFSG.LocalAnalysis.GLTheoremA.S9.Cl
