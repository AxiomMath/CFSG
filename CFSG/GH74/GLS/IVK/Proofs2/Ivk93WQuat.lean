module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Pointwise commutatorElement

theorem three_le_twoRank_of_involutions {G : Type*} [Group G] [Finite G] {a b c : G}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (habc : c ≠ a * b) : 3 ≤ CFSG.Assembly.twoRank G := by
  classical
  set S : Set G := {a, b, c} with hS
  have haS : a ∈ S := by simp [hS]
  have hbS : b ∈ S := by simp [hS]
  have hcS : c ∈ S := by simp [hS]
  have hpair : S.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | exact hab | exact hab.symm | exact hac | exact hac.symm |
        exact hbc | exact hbc.symm
  have hE := isMulCommutative_closure hpair
  have hcomm : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ g ∈ closure S, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl | rfl <;> assumption
    | one => simp
    | mul x y hx hy hx2 hy2 =>
      have h := hcomm x hx y hy
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← h]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x hx hx2 =>
      rw [← mul_inv_rev, hx2, inv_one]
  have hel : CFSG.Assembly.IsElemAbelian 2 (closure S) :=
    ⟨hE, fun x hx => by rw [pow_two]; exact hsq x hx⟩
  have hP : IsPGroup 2 (closure S) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa [pow_two] using hsq g g.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hP)
  have h5 : 5 ≤ Nat.card (closure S) := by
    have hsub : ({1, a, b, c, a * b} : Set G) ⊆ (closure S : Set G) := by
      intro g hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact subset_closure haS
      · exact subset_closure hbS
      · exact subset_closure hcS
      · exact mul_mem (subset_closure haS) (subset_closure hbS)
    have hcard : ({1, a, b, c, a * b} : Set G).ncard = 5 := by
      have e1 : (1 : G) ≠ a := fun h => ha1 h.symm
      have e2 : (1 : G) ≠ b := fun h => hb1 h.symm
      have e3 : (1 : G) ≠ c := fun h => hc1 h.symm
      have e4 : (1 : G) ≠ a * b := by
        intro h
        apply hab'
        have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h.symm
        rw [h1, inv_eq_of_mul_eq_one_right ha]
      have e7 : a ≠ a * b := by
        intro h
        apply hb1
        exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
      have e9 : b ≠ a * b := by
        intro h
        apply ha1
        exact mul_right_cancel (b := b) (by rw [one_mul]; exact h.symm)
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
        Set.ncard_pair habc]
      · simp [e9, hbc']
      · simp [e7, hac', hab']
      · simp [e1, e2, e3, e4]
    calc 5 = _ := hcard.symm
      _ ≤ (closure S : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (closure S) := Nat.card_coe_set_eq _
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle : k ≤ CFSG.Assembly.twoRank G := by
    unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨closure S, le_top, hel, hk⟩
    rintro m ⟨E, -, -, hE'⟩
    calc m ≤ 2 ^ m := Nat.lt_two_pow_self.le
      _ = Nat.card E := hE'.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E
  omega

theorem ivk93w_quat_commutator {J : Type} [Group J] [Finite J] {x a b : J} {Q : Subgroup J}
    (hQ8 : Nat.card ↥Q = 8) (haQ : a ∈ Q) (hbQ : b ∈ Q) (hax : a * a = x) (hbx : b * b = x)
    (hx1 : x ≠ 1) (hx2 : x * x = 1) (hab : a * b ≠ b * a) : a * b = x * (b * a) := by
  classical
  have ha2 : a ^ 2 = x := by rw [pow_two]; exact hax
  have ha4 : a ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2, pow_two]; exact hx2
  have hord : orderOf a = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a) (by rw [pow_one, ha2]; exact hx1)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact ha4)
    simpa using this
  have hAQ : zpowers a ≤ Q := (zpowers_le).2 haQ
  have hcardA : Nat.card (zpowers a) = 4 := by rw [Nat.card_zpowers, hord]
  have hidx : ((zpowers a).subgroupOf Q).index = 2 := by
    have h1 := Subgroup.index_mul_card ((zpowers a).subgroupOf Q)
    have h2 : Nat.card ((zpowers a).subgroupOf Q) = 4 := by
      rw [← hcardA]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv
    rw [h2, hQ8] at h1
    omega
  have hN := Subgroup.normal_of_index_eq_two hidx
  have hcm : b * a * b⁻¹ ∈ zpowers a := by
    have := hN.conj_mem (⟨a, haQ⟩ : Q) (by
      rw [Subgroup.mem_subgroupOf]; exact mem_zpowers a) (⟨b, hbQ⟩ : Q)
    exact (Subgroup.mem_subgroupOf).1 this
  obtain ⟨r, hr, hrc⟩ : ∃ r < 4, a ^ r = b * a * b⁻¹ := by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hcm)
    refine ⟨n % 4, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← hord, pow_mod_orderOf]
    exact hn
  have hbx' : b * x = x * b := by rw [← hbx]; group
  interval_cases r
  · exfalso
    simp only [pow_zero] at hrc
    have h1 : b * a = b := by
      have := congrArg (· * b) hrc
      simpa [mul_assoc] using this.symm
    have : a = 1 := mul_left_cancel (a := b) (by rw [mul_one]; exact h1)
    apply hx1
    rw [← hax, this, mul_one]
  · exfalso
    simp only [pow_one] at hrc
    apply hab
    have := congrArg (· * b) hrc.symm
    simpa [mul_assoc] using this.symm
  · exfalso
    rw [ha2] at hrc
    have h1 : b * a = b * x := by
      have := congrArg (· * b) hrc
      simp only [inv_mul_cancel_right] at this
      rw [hbx']
      simpa [mul_assoc] using this.symm
    have h2 : a = x := mul_left_cancel h1
    apply hx1
    rw [h2] at hax
    calc x = x * x := hax.symm
      _ = 1 := hx2
  · have h1 : b * a = a ^ 3 * b := by
      have := congrArg (· * b) hrc
      simpa [mul_assoc] using this.symm
    calc a * b = a ^ 5 * b := by
          have : a ^ 5 = a := by rw [show 5 = 4 + 1 by rfl, pow_add, ha4, one_mul, pow_one]
          rw [this]
      _ = a ^ 2 * (a ^ 3 * b) := by group
      _ = x * (b * a) := by rw [ha2, h1]

theorem exists_invariant_sylow {J : Type} [Group J] [Finite J] {B Q : Subgroup J}
    (hQN : Q ≤ normalizer (B : Set J)) (hQ : IsPGroup 2 Q) :
    ∃ P : Sylow 2 ↥B, ∀ a ∈ Q, ∀ b ∈ (P : Subgroup ↥B),
      ∃ b' ∈ (P : Subgroup ↥B), (b' : J) = a * (b : J) * a⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction ↥Q ↥B := MulDistribMulAction.compHom ↥B (Subgroup.inclusion hQN)
  obtain ⟨P, hP⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥B)
    (not_dvd_card_sylow 2 ↥B)
  refine ⟨P, fun a ha b hb => ?_⟩
  have h1 : (⟨a, ha⟩ : ↥Q) • P = P := hP ⟨a, ha⟩
  have h2 : ((⟨a, ha⟩ : ↥Q) • P : Sylow 2 ↥B) = (⟨a, ha⟩ : ↥Q) • (P : Subgroup ↥B) :=
    Sylow.pointwise_smul_def
  have h3 := Subgroup.smul_mem_pointwise_smul b (⟨a, ha⟩ : ↥Q) (P : Subgroup ↥B) hb
  rw [← h2, h1] at h3
  exact ⟨_, h3, rfl⟩

theorem ivk93w_neg_one_comm {F : Type} [Field F] (g : SL(2, F)) : g * (-1) = (-1) * g := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem ivk93w_sl2_sylow_quat_pair {F : Type} [Field F] [Finite F] (hk : ringChar F ≠ 2)
    (S : Sylow 2 SL(2, F)) :
    ∃ u ∈ (S : Subgroup SL(2, F)), ∃ v ∈ (S : Subgroup SL(2, F)),
      u ^ 2 = -1 ∧ v ^ 2 = -1 ∧ u * v = -1 * (v * u) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hab⟩ := finite_odd_field_two_squares hk (-1)
  obtain ⟨x₀, y₀, -, -, hx, hy, hxy⟩ := sl2_exists_anticommuting_pair hab
  have hz : (-1 : SL(2, F)) ≠ 1 := sl2_neg_one_ne_one hk
  have hz2 : (-1 : SL(2, F)) ^ 2 = 1 := by rw [sq, neg_mul_neg, mul_one]
  obtain ⟨H, hxH, hyH, ⟨eH⟩⟩ := exists_quaternion_subgroup_of_anticommuting hz hz2 hx hy hxy
  have hH : IsPGroup 2 H := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [← Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) S' S
  have hmem : ∀ y ∈ H, g * y * g⁻¹ ∈ (S : Subgroup SL(2, F)) := by
    intro y hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hS' hy, by simp [MulAut.conj_apply]⟩
  refine ⟨g * x₀ * g⁻¹, hmem x₀ hxH, g * y₀ * g⁻¹, hmem y₀ hyH, ?_, ?_, ?_⟩
  · calc (g * x₀ * g⁻¹) ^ 2 = g * x₀ ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = -1 := by rw [hx, ivk93w_neg_one_comm g]; group
  · calc (g * y₀ * g⁻¹) ^ 2 = g * y₀ ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = -1 := by rw [hy, ivk93w_neg_one_comm g]; group
  · calc g * x₀ * g⁻¹ * (g * y₀ * g⁻¹) = g * (x₀ * y₀) * g⁻¹ := by group
      _ = g * (-1 * (y₀ * x₀)) * g⁻¹ := by rw [hxy]
      _ = -1 * (g * y₀ * g⁻¹ * (g * x₀ * g⁻¹)) := by
        rw [← mul_assoc g, ivk93w_neg_one_comm g]
        group

theorem ivk93w_eq_one_of_mem_pPrimeCore {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) {g : G} (hg : g ∈ P) (hgO : g ∈ pPrimeCore 2 G) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  have h2 : orderOf g ∣ Nat.card (pPrimeCore 2 G) := by
    have := orderOf_dvd_natCard (⟨g, hgO⟩ : ↥(pPrimeCore 2 G))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
  have : Nat.Coprime (orderOf g) (Nat.card (pPrimeCore 2 G)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k hcop
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd this h2)

namespace Ivk93W

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {B : Subgroup J}

theorem exists_quat_pair (h : Ivk93W x q B) (P : Sylow 2 ↥B) :
    ∃ u ∈ (P : Subgroup ↥B), ∃ v ∈ (P : Subgroup ↥B),
      (u : J) * u = x ∧ (v : J) * v = x ∧ (u : J) * v = x * ((v : J) * u) := by
  classical
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd
  have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hk : ringChar F ≠ 2 := by
    intro h2
    apply h2F
    have := (ringChar.spec F 2).2 (by rw [h2])
    simpa using this
  have hneg : (-1 : SL(2, F)) ≠ 1 := sl2_neg_one_ne_one hk
  let ε : ↥B →* SL(2, F) := e.symm.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥B))
  have hε : Function.Surjective ε := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ g : ↥B, ε g = 1 → g ∈ pPrimeCore 2 ↥B := by
    intro g hg
    have : QuotientGroup.mk' (pPrimeCore 2 ↥B) g = 1 := by
      apply e.symm.injective
      rw [map_one]
      exact hg
    exact (QuotientGroup.eq_one_iff g).1 this
  obtain ⟨ub, hub, vb, hvb, hub2, hvb2, hubvb⟩ :=
    ivk93w_sl2_sylow_quat_pair hk (P.mapSurjective hε)
  rw [Sylow.coe_mapSurjective] at hub hvb
  obtain ⟨u, hu, rfl⟩ := hub
  obtain ⟨v, hv, rfl⟩ := hvb
  have hP2 : IsPGroup 2 (P : Subgroup ↥B) := P.isPGroup'
  have hPO : ∀ g ∈ (P : Subgroup ↥B), ε g = 1 → g = 1 := fun g hg hεg =>
    ivk93w_eq_one_of_mem_pPrimeCore hP2 hg (hker g hεg)
  have hsq : ∀ w ∈ (P : Subgroup ↥B), ε w ^ 2 = -1 → (w : J) * w = x := by
    intro w hw hεw
    have h4 : w ^ 2 * w ^ 2 = 1 := by
      apply hPO _ (mul_mem (pow_mem hw 2) (pow_mem hw 2))
      rw [map_mul, map_pow, hεw, neg_mul_neg, mul_one]
    have h1 : w ^ 2 ≠ 1 := by
      intro h1
      apply hneg
      rw [← hεw, ← map_pow, h1, map_one]
    have := h.unique_involution (u := ((w ^ 2 : ↥B) : J)) (w ^ 2).2
      (by rw [← Subgroup.coe_mul, h4]; rfl) (fun h' => h1 (Subtype.ext h'))
    rw [← this, pow_two]
    rfl
  refine ⟨u, hu, v, hv, hsq u hu hub2, hsq v hv hvb2, ?_⟩
  have hw : u * v * u⁻¹ * v⁻¹ = ⟨x, h.mem⟩ := by
    have hwP : u * v * u⁻¹ * v⁻¹ ∈ (P : Subgroup ↥B) :=
      mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    have hεw : ε (u * v * u⁻¹ * v⁻¹) = -1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hubvb]
      group
    have h4 : (u * v * u⁻¹ * v⁻¹) * (u * v * u⁻¹ * v⁻¹) = 1 := by
      apply hPO _ (mul_mem hwP hwP)
      rw [map_mul, hεw, neg_mul_neg, mul_one]
    have h1 : u * v * u⁻¹ * v⁻¹ ≠ 1 := by
      intro h1
      apply hneg
      rw [← hεw, h1, map_one]
    have := h.unique_involution (u := ((u * v * u⁻¹ * v⁻¹ : ↥B) : J)) (u * v * u⁻¹ * v⁻¹).2
      (by rw [← Subgroup.coe_mul, h4]; rfl) (fun h' => h1 (Subtype.ext h'))
    exact Subtype.ext this
  have hw' := congrArg Subtype.val hw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hw'
  calc (u : J) * v = ((u : J) * v * (u : J)⁻¹ * (v : J)⁻¹) * ((v : J) * u) := by group
    _ = x * ((v : J) * u) := by rw [hw']

theorem three_le_twoRank (h : Ivk93W x q B) (hQ : Ivk93WQuat x B) :
    3 ≤ CFSG.Assembly.twoRank J := by
  classical
  obtain ⟨Q, hQC, hxQ, hQ8, ⟨α, hαQ, β, hβQ, hαx, hβx, hαβ⟩, hcomm⟩ := hQ
  have hx1 : x ≠ 1 := h.ne_one
  have hx2 : x * x = 1 := h.mul_self_eq_one
  have hQN : Q ≤ normalizer (B : Set J) := fun a ha =>
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le).1 h.normal_in) (hQC ha)
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQ8]; norm_num)
  obtain ⟨P, hP⟩ := exists_invariant_sylow hQN hQ2
  have hP2 : IsPGroup 2 (P : Subgroup ↥B) := P.isPGroup'
  have hQP : ∀ a ∈ Q, ∀ b ∈ (P : Subgroup ↥B), a * (b : J) = (b : J) * a := by
    intro a ha b hb
    obtain ⟨b', hb', hb'e⟩ := hP a ha b hb
    obtain ⟨o, ho, hoe⟩ := hcomm a ha (b : J) b.2
    have hoe' : (o : J) = ⁅a, (b : J)⁆ := hoe
    have h1 : o = b' * b⁻¹ := by
      apply Subtype.ext
      rw [hoe', Subgroup.coe_mul, Subgroup.coe_inv, hb'e]
      simp [commutatorElement_def]
    have h2 : b' * b⁻¹ = 1 :=
      ivk93w_eq_one_of_mem_pPrimeCore hP2 (mul_mem hb' (inv_mem hb)) (h1 ▸ ho)
    have h3 : b' = b := mul_inv_eq_one.1 h2
    rw [h3] at hb'e
    calc a * (b : J) = a * b * a⁻¹ * a := by group
      _ = (b : J) * a := by rw [← hb'e]
  obtain ⟨u, hu, v, hv, hu2, hv2, huv⟩ := h.exists_quat_pair P
  have hαβ' : α * β = x * (β * α) := ivk93w_quat_commutator hQ8 hαQ hβQ hαx hβx hx1 hx2 hαβ
  have cx : ∀ g ∈ centralizer ({x} : Set J), x * g = g * x := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have cαx : x * α = α * x := cx α (hQC hαQ)
  have cβx : x * β = β * x := cx β (hQC hβQ)
  have cux : x * (u : J) = (u : J) * x := cx u (h.le u.2)
  have cvx : x * (v : J) = (v : J) * x := cx v (h.le v.2)
  have cαu : α * (u : J) = (u : J) * α := hQP α hαQ u hu
  have cαv : α * (v : J) = (v : J) * α := hQP α hαQ v hv
  have cβu : β * (u : J) = (u : J) * β := hQP β hβQ u hu
  have cβv : β * (v : J) = (v : J) * β := hQP β hβQ v hv
  have hnc : (u : J) * v ≠ (v : J) * u := by
    intro hc
    rw [hc] at huv
    apply hx1
    have : (v : J) * u = x * ((v : J) * u) := huv
    exact (mul_eq_right.1 this.symm)
  have hnα : α * β ≠ β * α := hαβ
  obtain ⟨y₁, hy₁⟩ : ∃ y : J, y = α * u := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : J, y = β * v := ⟨_, rfl⟩
  have hy₁sq : y₁ * y₁ = 1 := by
    rw [hy₁]
    calc α * u * (α * u) = α * (u * α) * u := by group
      _ = α * (α * u) * u := by rw [← cαu]
      _ = (α * α) * ((u : J) * u) := by group
      _ = 1 := by rw [hαx, hu2, hx2]
  have hy₂sq : y₂ * y₂ = 1 := by
    rw [hy₂]
    calc β * v * (β * v) = β * (v * β) * v := by group
      _ = β * (β * v) * v := by rw [← cβv]
      _ = (β * β) * ((v : J) * v) := by group
      _ = 1 := by rw [hβx, hv2, hx2]
  have hy₁₂ : y₁ * y₂ = y₂ * y₁ := by
    have e1 : y₁ * y₂ = (α * β) * ((u : J) * v) := by
      rw [hy₁, hy₂]
      calc α * u * (β * v) = α * (u * β) * v := by group
        _ = α * (β * u) * v := by rw [← cβu]
        _ = (α * β) * ((u : J) * v) := by group
    have e2 : y₂ * y₁ = (β * α) * ((v : J) * u) := by
      rw [hy₁, hy₂]
      calc β * v * (α * u) = β * (v * α) * u := by group
        _ = β * (α * v) * u := by rw [← cαv]
        _ = (β * α) * ((v : J) * u) := by group
    have cxβα : x * (β * α) = (β * α) * x := by
      rw [← mul_assoc, cβx, mul_assoc, cαx, mul_assoc]
    rw [e1, e2, hαβ', huv]
    calc x * (β * α) * (x * ((v : J) * u)) = (x * (β * α) * x) * ((v : J) * u) := by group
      _ = ((β * α) * x * x) * ((v : J) * u) := by rw [cxβα]
      _ = (β * α) * ((v : J) * u) := by rw [mul_assoc (β * α), hx2, mul_one]
  have hxy₁ : x * y₁ = y₁ * x := by
    rw [hy₁]
    calc x * (α * u) = (x * α) * u := by group
      _ = α * x * u := by rw [cαx]
      _ = α * (x * u) := by group
      _ = α * (u * x) := by rw [cux]
      _ = α * u * x := by group
  have hxy₂ : x * y₂ = y₂ * x := by
    rw [hy₂]
    calc x * (β * v) = (x * β) * v := by group
      _ = β * x * v := by rw [cβx]
      _ = β * (x * v) := by group
      _ = β * (v * x) := by rw [cvx]
      _ = β * v * x := by group
  have cα_u : Commute α (u : J) := cαu
  have cα_v : Commute α (v : J) := cαv
  have cα_x : Commute α x := cαx.symm
  have cβ_u : Commute β (u : J) := cβu
  have cu_x : Commute (u : J) x := cux.symm
  have cv_x : Commute (v : J) x := cvx.symm
  refine three_le_twoRank_of_involutions (a := x) (b := y₁) (c := y₂) hx2 hy₁sq hy₂sq hxy₁ hxy₂
    hy₁₂ hx1 ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro h1
    rw [hy₁] at h1
    have h1' : α = (u : J)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have : Commute (u : J) (v : J) := by
      have hc : Commute α (v : J) := cα_v
      rw [h1'] at hc
      exact Commute.inv_left_iff.1 hc
    exact hnc this
  ·
    intro h1
    rw [hy₂] at h1
    have h1' : β = (v : J)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have : Commute (v : J) (u : J) := by
      have hc : Commute β (u : J) := cβ_u
      rw [h1'] at hc
      exact Commute.inv_left_iff.1 hc
    exact hnc this.symm
  ·
    intro h1
    rw [hy₁] at h1
    have h1' : (u : J) = α⁻¹ * x := by
      calc (u : J) = α⁻¹ * (α * u) := by group
        _ = α⁻¹ * x := by rw [← h1]
    have : Commute (u : J) (v : J) := by
      rw [h1']
      exact Commute.mul_left cα_v.inv_left cv_x.symm
    exact hnc this
  ·
    intro h1
    rw [hy₂] at h1
    have h1' : (v : J) = β⁻¹ * x := by
      calc (v : J) = β⁻¹ * (β * v) := by group
        _ = β⁻¹ * x := by rw [← h1]
    have : Commute (v : J) (u : J) := by
      rw [h1']
      exact Commute.mul_left cβ_u.inv_left cu_x.symm
    exact hnc this.symm
  ·
    intro h1
    rw [hy₁, hy₂] at h1
    have hβe : β = α * ((u : J) * (v : J)⁻¹) := by
      calc β = β * (v : J) * (v : J)⁻¹ := by group
        _ = α * (u : J) * (v : J)⁻¹ := by rw [← h1]
        _ = α * ((u : J) * (v : J)⁻¹) := by group
    apply hnα
    have : Commute α β := by
      rw [hβe]
      exact (Commute.refl α).mul_right (cα_u.mul_right cα_v.inv_right)
    exact this.eq
  ·
    intro h1
    rw [hy₁, hy₂] at h1
    have hβe : β = x * α * ((u : J) * (v : J)⁻¹) := by
      calc β = β * (v : J) * (v : J)⁻¹ := by group
        _ = x * (α * (u : J)) * (v : J)⁻¹ := by rw [h1]
        _ = x * α * ((u : J) * (v : J)⁻¹) := by group
    apply hnα
    have : Commute α β := by
      rw [hβe]
      exact (cα_x.mul_right (Commute.refl α)).mul_right (cα_u.mul_right cα_v.inv_right)
    exact this.eq

end Ivk93W

end CFSG.GH74.GLS.IVK.Proofs2
