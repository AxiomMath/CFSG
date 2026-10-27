module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseFuse
public import CFSG.GH74.QTGen4.Recog.Ku.NStruct
public import Certificates.Data.A5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open CFSG.Quasithin.L34Amalgam

variable {G : Type} [Group G]

theorem exists_conj_into_two_sylow [Finite G] {H S : Subgroup G} (hSH : S ≤ H)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ (S.subgroupOf H).index) {u : G} (hu : u ∈ H)
    (hu2 : u * u = 1) : ∃ s ∈ H, s⁻¹ * u * s ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : IsPGroup 2 ↥(S.subgroupOf H) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  let K : Sylow 2 ↥H := hK2.toSylow hSidx
  let u' : ↥H := ⟨u, hu⟩
  have hu'2 : u' * u' = 1 := Subtype.ext hu2
  have hord : orderOf u' ∣ 2 ^ 1 := by
    rw [pow_one]; exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu'2)
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers u') := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm'])
  obtain ⟨P', hP'⟩ := hz2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) K P'
  have hmem : u' ∈ ((g • K : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [hg]; exact hP' (Subgroup.mem_zpowers u')
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hmem
  obtain ⟨k, hk, hku⟩ := Subgroup.mem_map.mp hmem
  have hkS : (k : G) ∈ S := by
    have : k ∈ (K : Subgroup ↥H) := hk
    have h2 : (K : Subgroup ↥H) = S.subgroupOf H := rfl
    rw [h2] at this
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨(g : G), g.2, ?_⟩
  have e : u = (g : G) * (k : G) * (g : G)⁻¹ := by
    have := congrArg Subtype.val hku
    simpa [MulAut.conj_apply] using this.symm
  rw [e]
  have : (g : G)⁻¹ * ((g : G) * (k : G) * (g : G)⁻¹) * (g : G) = (k : G) := by group
  rw [this]; exact hkS

theorem conj_zpowers_of_factorization [Finite G] {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hfac : (Nat.card K).factorization p = 1) {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K)
    (ok : orderOf k = p) (ok' : orderOf k' = p) :
    ∃ g ∈ K, Subgroup.zpowers k = Subgroup.zpowers (g * k' * g⁻¹) := by
  have okK : orderOf (⟨k, hk⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact ok
  have okK' : orderOf (⟨k', hk'⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact ok'
  let P : Sylow p K := Sylow.ofCard (Subgroup.zpowers ⟨k, hk⟩) (by
    rw [Nat.card_zpowers, okK, hfac, pow_one])
  let P' : Sylow p K := Sylow.ofCard (Subgroup.zpowers ⟨k', hk'⟩) (by
    rw [Nat.card_zpowers, okK', hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P' P
  have hPP : Subgroup.zpowers (⟨k, hk⟩ : K) =
      (Subgroup.zpowers (⟨k', hk'⟩ : K)).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hg
    simp only [Sylow.coe_subgroup_smul, P, P', Sylow.coe_ofCard] at this
    rw [← this]
    rfl
  refine ⟨g, g.2, ?_⟩
  have h1 := congrArg (Subgroup.map K.subtype) hPP
  rw [Subgroup.map_map, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1
  exact h1

theorem perm_five_three_commute :
    ∀ g : Equiv.Perm (Fin 5), g ^ 3 = 1 → g ≠ 1 →
      ∃ t : Equiv.Perm (Fin 5), t * t = 1 ∧ t ≠ 1 ∧ t * g = g * t := by
  decide +kernel

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem fpf_pCore_of_order_three [KuLeaf LeafExistsIsParabolicL1]
    (h : KuHyp G T M H P z) {y : G} (hy : y ∈ oTwoUpper M)
    (hy3 : orderOf y = 3) : ∀ v ∈ pCoreOf 2 M, y * v = v * y → v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, b, hP⟩ := h.exists_isParabolic_L1
  have hb1 : b ≠ 1 := by
    intro hb
    have hnt : Nontrivial ↥(pCoreOf 2 M) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h.vCard]; norm_num)
    obtain ⟨e, he1⟩ := exists_ne (1 : ↥(pCoreOf 2 M))
    have he : (e : G) = 1 := hP.fpf (e : G) e.2 (by rw [hb, one_mul, mul_one])
    exact he1 (Subtype.ext he)
  have hb3 : orderOf b = 3 := orderOf_eq_prime hP.hb hb1
  have hfac : (Nat.card (oTwoUpper M)).factorization 3 = 1 := by
    rw [hP.card, Nat.factorization_def _ Nat.prime_three]
    rw [show (960 : ℕ) = 3 * 320 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
  intro v hv hvy
  obtain ⟨g, hgK, hgz⟩ := conj_zpowers_of_factorization hfac hy hP.mem_b hy3 hb3
  have hvb : Commute v (g * b * g⁻¹) := by
    have hmem : g * b * g⁻¹ ∈ Subgroup.zpowers y := by
      rw [hgz]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk]
    exact (show Commute v y from hvy.symm).zpow_right k
  have hwV : g⁻¹ * v * g ∈ pCoreOf 2 M := by
    have := hP.normal g⁻¹ ((oTwoUpper M).inv_mem hgK) v hv
    rwa [inv_inv] at this
  have hwb : (g⁻¹ * v * g) * b = b * (g⁻¹ * v * g) := by
    calc (g⁻¹ * v * g) * b = g⁻¹ * (v * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * v) * g := by rw [hvb.eq]
      _ = b * (g⁻¹ * v * g) := by group
  have h1 : g⁻¹ * v * g = 1 := hP.fpf _ hwV hwb.symm
  calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_invol_commute (h : KuHyp G T M H P z) {y : G} (hyM : y ∈ M) (hy3 : orderOf y = 3)
    (hfpf : ∀ v ∈ pCoreOf 2 M, y * v = v * y → v = 1) :
    ∃ t' : G, t' ∈ M ∧ t' * t' = 1 ∧ t' ≠ 1 ∧ t' * y = y * t' := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨φ, hφs, hφk⟩ := h.mQuot
  have hker : ∀ x : M, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
    intro x
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  let y' : M := ⟨y, hyM⟩
  have hy'3 : orderOf y' = 3 := by rw [Subgroup.orderOf_mk]; exact hy3
  have hy'pow : y' ^ 3 = 1 := by rw [← hy'3]; exact pow_orderOf_eq_one y'
  have hg3 : (φ y') ^ 3 = 1 := by rw [← map_pow, hy'pow, map_one]
  have hg1 : φ y' ≠ 1 := by
    intro hc
    have hyV : y ∈ pCoreOf 2 M := (hker y').mp hc
    have hy1 : y = 1 := hfpf y hyV rfl
    rw [hy1, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  obtain ⟨t₀, ht₀2, ht₀1, ht₀c⟩ := perm_five_three_commute (φ y') hg3 hg1
  obtain ⟨m, hm⟩ := hφs t₀
  have hXcard : Nat.card {x : M // φ x = t₀} = 16 := by
    have e : {x : M // φ x = t₀} ≃ ↥φ.ker :=
      { toFun := fun x => ⟨m⁻¹ * x.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hm, x.2, inv_mul_cancel]⟩
        invFun := fun v => ⟨m * v.1, by
          rw [map_mul, hm, MonoidHom.mem_ker.mp v.2, mul_one]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
    rw [Nat.card_congr e, hφk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.pCore_le_T.trans h.tM)).toEquiv, h.vCard]
  have hcomm : ∀ g : M, g ∈ Subgroup.zpowers y' → ∀ x : M, φ x = t₀ →
      φ (g * x * g⁻¹) = t₀ := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc0 : Commute (φ y') t₀ := ht₀c.symm
    have hc : Commute (φ (y' ^ k)) t₀ := by
      rw [map_zpow]; exact hc0.zpow_left k
    rw [map_mul, map_mul, map_inv, hx, hc.eq, mul_inv_cancel_right]
  let act : MulAction ↥(Subgroup.zpowers y') {x : M // φ x = t₀} :=
    { smul := fun g x => ⟨(g : M) * x.1 * (g : M)⁻¹, hcomm (g : M) g.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by
        show (1 : M) * x.1 * (1 : M)⁻¹ = x.1
        simp)
      mul_smul := fun g g' x => Subtype.ext (by
        show ((g * g' : ↥(Subgroup.zpowers y')) : M) * x.1 * ((g * g' : ↥(Subgroup.zpowers y')) : M)⁻¹ =
          (g : M) * ((g' : M) * x.1 * (g' : M)⁻¹) * (g : M)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hPg : IsPGroup 3 ↥(Subgroup.zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'3]; norm_num)
  have hmod := hPg.card_modEq_card_fixedPoints (α := {x : M // φ x = t₀})
  rw [hXcard] at hmod
  unfold Nat.ModEq at hmod
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers y')
      {x : M // φ x = t₀}) := by
    omega
  obtain ⟨⟨x0⟩, -⟩ := Nat.card_pos_iff.mp hpos
  have hcy : y' * x0.1.1 * y'⁻¹ = x0.1.1 :=
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp x0.2 ⟨y', Subgroup.mem_zpowers y'⟩)
  obtain ⟨c, hc⟩ : ∃ c : M, x0.1.1 = c := ⟨_, rfl⟩
  rw [hc] at hcy
  have hcφ : φ c = t₀ := by rw [← hc]; exact x0.1.2
  have hcG : y * (c : G) = (c : G) * y := by
    have h1 : y * (c : G) * y⁻¹ = (c : G) := congrArg Subtype.val hcy
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hccV : (c : G) * c ∈ pCoreOf 2 M := by
    refine (hker (c * c)).mp ?_
    rw [map_mul, hcφ, ht₀2]
  have hcc1 : (c : G) * c = 1 := by
    apply hfpf _ hccV
    rw [← mul_assoc, hcG, mul_assoc, hcG, ← mul_assoc]
  refine ⟨(c : G), c.2, hcc1, ?_, hcG.symm⟩
  intro h1
  apply ht₀1
  rw [← hcφ]
  have hc1 : c = 1 := Subtype.ext h1
  rw [hc1, map_one]

theorem invol_M_conj_z [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA]
    [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {i : G} (hiM : i ∈ M)
    (hi : i * i = 1) (hi1 : i ≠ 1) : ∃ g : G, g * z * g⁻¹ = i := by
  have hodd : ¬ 2 ∣ (T.subgroupOf M).index := by
    intro hd
    apply h.sylow.2
    rw [← Subgroup.relIndex_mul_index h.tM]
    exact Dvd.dvd.mul_right hd _
  obtain ⟨s, -, hs⟩ := exists_conj_into_two_sylow h.tM h.sylow.1 hodd hiM hi
  obtain ⟨i', hi'def⟩ : ∃ i' : G, i' = s⁻¹ * i * s := ⟨_, rfl⟩
  rw [← hi'def] at hs
  have hi'2 : i' * i' = 1 := by
    have e : i' * i' = s⁻¹ * (i * i) * s := by rw [hi'def]; group
    rw [e, hi, mul_one, inv_mul_cancel]
  have hi'1 : i' ≠ 1 := by
    intro h1
    apply hi1
    calc i = s * (s⁻¹ * i * s) * s⁻¹ := by group
      _ = 1 := by rw [← hi'def, h1, mul_one, mul_inv_cancel]
  have hVnot : ∃ v ∈ pCoreOf 2 M, v ∉ kuA P H := by
    by_contra hcon
    have hVA : pCoreOf 2 M ≤ kuA P H := fun x hx => Classical.byContradiction fun hx' => hcon ⟨x, hx, hx'⟩
    have heq : kuA P H ⊓ pCoreOf 2 M = pCoreOf 2 M := inf_eq_right.mpr hVA
    have hk := h.kuA_inf_pCore_M
    rw [heq] at hk
    have hc := h.card_kuV2
    rw [← hk, h.vCard] at hc
    omega
  obtain ⟨v₀, hv₀V, hv₀A⟩ := hVnot
  have hv₀1 : v₀ ≠ 1 := by
    rintro rfl
    exact hv₀A (one_mem _)
  have hv₀2 : v₀ * v₀ = 1 := by
    rw [← pow_two]; exact h.vElem.2 v₀ hv₀V
  have hv₀N : v₀ ∈ kuN P H := h.T_le_kuN (h.pCore_le_T hv₀V)
  obtain ⟨m, -, hm⟩ := h.transitive_V v₀ hv₀V hv₀1
  obtain ⟨g, hg⟩ := Ψ.invol_conj_z hv₀N hv₀A hv₀2 ⟨m, hm⟩ (h.T_le_kuN hs) hi'2 hi'1
  refine ⟨s * g, ?_⟩
  have hi_eq : i = s * i' * s⁻¹ := by rw [hi'def]; group
  rw [hi_eq, ← hg]
  group

end KuHyp

end CFSG.GH74.QTGen4.Ku
