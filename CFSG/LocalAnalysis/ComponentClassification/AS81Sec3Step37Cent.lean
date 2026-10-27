module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Sporadic.SuzOddCore
open scoped commutatorElement

namespace Sec3

section Actions

variable {G : Type} [Group G]

@[expose] noncomputable def normalizerConjAut (C : Subgroup G) :
    normalizer (C : Set G) →* MulAut ↥C where
  toFun n :=
    { toFun := fun c => ⟨n * c * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 c).mp c.2⟩
      invFun := fun c => ⟨(n : G)⁻¹ * c * n, by
        simpa using (mem_normalizer_iff.mp (inv_mem n.2) c).mp c.2⟩
      left_inv := fun c => Subtype.ext (by simp [mul_assoc])
      right_inv := fun c => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
  map_one' := MulEquiv.ext fun c => Subtype.ext (by simp)
  map_mul' a b := MulEquiv.ext fun c => Subtype.ext (by simp [mul_assoc])

variable {A H : Type*} [Group A] [Group H]

theorem map_eq_of_forall_mem_act (α : A →* MulAut H) (N : Subgroup H)
    (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) (a : A) : N.map ((α a : H ≃* H) : H →* H) = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact hN a n hn
  · intro n hn
    refine ⟨α a⁻¹ n, hN a⁻¹ n hn, ?_⟩
    change α a (α a⁻¹ n) = n
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

@[expose] noncomputable def quotientConjAction (α : A →* MulAut H) (N : Subgroup H) [N.Normal]
    (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) : A →* MulAut (H ⧸ N) where
  toFun a := QuotientGroup.congr N N (α a) (map_eq_of_forall_mem_act α N hN a)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change ((α 1 x : H) : H ⧸ N) = (x : H ⧸ N)
      rw [map_one]
      rfl
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change ((α (a * b) x : H) : H ⧸ N) = ((α a (α b x) : H) : H ⧸ N)
      rw [map_mul]
      rfl

@[expose] noncomputable def restrictInvariantAction (α : A →* MulAut H) (L : Subgroup H)
    (hL : ∀ a : A, ∀ l ∈ L, α a l ∈ L) : A →* MulAut ↥L where
  toFun a :=
    { toFun := fun l => ⟨α a (l : H), hL a l l.2⟩
      invFun := fun l => ⟨α a⁻¹ (l : H), hL a⁻¹ l l.2⟩
      left_inv := fun l => Subtype.ext (by
        change α a⁻¹ (α a l) = l
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun l => Subtype.ext (by
        change α a (α a⁻¹ l) = l
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun l l' => Subtype.ext (map_mul (α a) (l : H) (l' : H)) }
  map_one' := MulEquiv.ext fun l => Subtype.ext (by
    change α 1 l = l
    rw [map_one, MulAut.one_apply])
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext (by
    change α (a * b) l = α a (α b l)
    rw [map_mul, MulAut.mul_apply])

end Actions

section General

variable {G : Type} [Group G]

theorem commute_of_commutator_commute [Finite G] {W : Subgroup G} (hW : Odd (Nat.card W))
    {q : G} {m : ℕ} (hqm : q ^ 2 ^ m = 1) (hqW : q ∈ normalizer (W : Set G)) {w : G}
    (hw : w ∈ W) (hc : (w * q * w⁻¹ * q⁻¹) * q = q * (w * q * w⁻¹ * q⁻¹)) : w * q = q * w := by
  set c := w * q * w⁻¹ * q⁻¹ with hcdef
  have hcW : c ∈ W := by
    have h1 : q * w⁻¹ * q⁻¹ ∈ W := (mem_normalizer_iff.mp hqW _).mp (inv_mem hw)
    have h2 := mul_mem hw h1
    rwa [show w * (q * w⁻¹ * q⁻¹) = c by rw [hcdef]; group] at h2
  have hqw : q * w⁻¹ = w⁻¹ * c * q := by rw [hcdef]; group
  have key : ∀ n : ℕ, q ^ n * w⁻¹ = w⁻¹ * c ^ n * q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : q * c ^ n = c ^ n * q := ((Commute.pow_right hc.symm n)).eq
      calc q ^ (n + 1) * w⁻¹ = q * (q ^ n * w⁻¹) := by rw [pow_succ']; group
        _ = q * w⁻¹ * c ^ n * q ^ n := by rw [ih]; group
        _ = w⁻¹ * c * (q * c ^ n) * q ^ n := by rw [hqw]; group
        _ = w⁻¹ * c * (c ^ n * q) * q ^ n := by rw [hcn]
        _ = w⁻¹ * c ^ (n + 1) * q ^ (n + 1) := by rw [pow_succ', pow_succ']; group
  have h1 : c ^ 2 ^ m = 1 := by
    have := key (2 ^ m)
    rw [hqm, mul_one, one_mul] at this
    exact mul_left_cancel (this.symm.trans (mul_one w⁻¹).symm)
  have hc1 : c = 1 := by
    have h2 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf c ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hcW
    have hcop : Nat.Coprime (2 ^ m) (Nat.card W) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hW)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h3))
  calc w * q = c * (q * w) := by rw [hcdef]; group
    _ = q * w := by rw [hc1, one_mul]

theorem le_pPrimeCore_sup_zpowers {H : Type*} [Group H] [Finite H] {z : H}
    (hzc : z ∈ center H) (hz2 : orderOf z = 2) {Y : Subgroup H} (hY : Y.Normal) (hzY : z ∈ Y)
    {m : ℕ} (hm : Odd m) (hYm : Nat.card Y = 2 * m) : Y ≤ pPrimeCore 2 H ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z' : ↥Y := ⟨z, hzY⟩ with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [← hz2, hz']
    exact (orderOf_injective Y.subtype Y.subtype_injective ⟨z, hzY⟩).symm
  have hNc : zpowers z' ≤ center ↥Y := zpowers_le.mpr (mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp hzc (y : H)))
  have : (zpowers z').Normal := normal_of_le_center hNc
  have hN2 : Nat.card (zpowers z') = 2 := by rw [Nat.card_zpowers, hz'2]
  have hNidx : (zpowers z').index = m := by
    have h := (zpowers z').index_mul_card
    rw [hN2, hYm] at h
    omega
  have hcop : Nat.Coprime (Nat.card (zpowers z')) (zpowers z').index := by
    rw [hN2, hNidx]
    exact Nat.coprime_two_left.mpr hm
  obtain ⟨M, hM⟩ := exists_right_complement'_of_coprime hcop
  have hMcard : Nat.card M = m := by
    have h := hM.card_mul_card
    rw [hN2, hYm] at h
    omega
  have hMiff : ∀ y : ↥Y, y ∈ M ↔ Odd (orderOf y) := by
    intro y
    constructor
    · intro hy
      exact (hMcard ▸ hm).of_dvd_nat (Subgroup.orderOf_dvd_natCard M hy)
    · intro hy
      obtain ⟨⟨⟨n, hn⟩, ⟨w, hw⟩⟩, hnw⟩ := hM.2 y
      change n * w = y at hnw
      have hnc : Commute n w := (mem_center_iff.mp (hNc hn) w).symm
      have hpow : (n * w) ^ orderOf y = 1 := by rw [hnw]; exact pow_orderOf_eq_one y
      rw [hnc.mul_pow] at hpow
      have hnM : n ^ orderOf y ∈ M := by
        rw [eq_inv_of_mul_eq_one_left hpow]
        exact inv_mem (pow_mem hw _)
      have hn1 : n ^ orderOf y = 1 := by
        have h := hM.disjoint
        rw [disjoint_iff] at h
        have h2 : n ^ orderOf y ∈ zpowers z' ⊓ M := ⟨pow_mem hn _, hnM⟩
        rw [h, mem_bot] at h2
        exact h2
      have hn' : n = 1 := by
        have h1 : orderOf n ∣ orderOf y := orderOf_dvd_of_pow_eq_one hn1
        have h2 : orderOf n ∣ 2 := hN2 ▸ Subgroup.orderOf_dvd_natCard _ hn
        have hcop' : Nat.Coprime 2 (orderOf y) := Nat.coprime_two_left.mpr hy
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop'.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))
      rw [← hnw, hn', one_mul]
      exact hw
  have hMn : (M.map Y.subtype).Normal := by
    refine ⟨fun a ha h => ?_⟩
    obtain ⟨y, hy, rfl⟩ := ha
    have hyY : h * (y : H) * h⁻¹ ∈ Y := hY.conj_mem _ y.2 h
    refine ⟨⟨_, hyY⟩, (hMiff _).mpr ?_, rfl⟩
    have h1 : orderOf (⟨_, hyY⟩ : ↥Y) = orderOf (y : H) := by
      rw [← orderOf_injective Y.subtype Y.subtype_injective ⟨_, hyY⟩]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective (y : H)
    rw [h1, show orderOf (y : H) = orderOf y from
      orderOf_injective Y.subtype Y.subtype_injective y]
    exact (hMiff y).mp hy
  have hMO : M.map Y.subtype ≤ pPrimeCore 2 H := by
    rw [← AS76b.assemblyOddCore_eq_pPrimeCore]
    refine AS76b.le_assemblyOddCore hMn ?_
    rw [card_map_of_injective Y.subtype_injective, hMcard]
    exact hm
  intro y hy
  obtain ⟨⟨⟨n, hn⟩, ⟨w, hw⟩⟩, hnw⟩ := hM.2 ⟨y, hy⟩
  change n * w = ⟨y, hy⟩ at hnw
  have hy' : y = (n : H) * (w : H) := (congrArg Subtype.val hnw).symm
  rw [hy']
  refine mul_mem (mem_sup_right ?_) (mem_sup_left (hMO ⟨w, hw, rfl⟩))
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
  exact ⟨k, by simp [hz']⟩

end General

section B0

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G}

theorem commutatorElement_mul_central_central {M : Type*} [Group M] {a b u v : M}
    (hu : ∀ m : M, u * m = m * u) (hv : ∀ m : M, v * m = m * v) : ⁅a * u, b * v⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ = a * (u * b) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by
        group
    _ = a * (b * u) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by rw [hu b]
    _ = a * b * (u * v) * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = a * b * (v * u) * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by rw [hu v]
    _ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * v) * v⁻¹ * b⁻¹ := by rw [hv a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem perfect_B₀_and_T_le_of_hom
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y)
    {K : Subgroup G} (hK : K = sec3B A₁ x ⊓ centralizer ({z} : Set G)) {π : ↥K →* ↥(invE 1)}
    (hπs : Function.Surjective π) (hπk : ∀ k, π k = 1 ↔ (k : G) ∈ zpowers x) :
    commutator ↥B₀ = ⊤ ∧ T ≤ B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzT : z ∈ T := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).1
  have hzc : z ∈ centralizer (T : Set G) := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).2
  have hTK : T ≤ K := fun t ht => hK ▸ mem_inf.mpr ⟨hS.T_le ht,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc t ht)⟩
  have hKB : K ≤ sec3B A₁ x := hK ▸ inf_le_left
  have hzB : z ∈ sec3B A₁ x := hS.T_le hzT
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hxc : ∀ b ∈ sec3B A₁ x, b * x = x * b := fun b hb =>
    mem_centralizer_iff.mp (mem_inf.mp hxZ).2 b hb
  have hxK : x ∈ K := hK ▸ mem_inf.mpr ⟨hxB, mem_centralizer_singleton_iff.mpr (hxc z hzB).symm⟩
  have hx3 : orderOf x = 3 := hS.setting.order_x
  set N := π.ker with hNdef
  have hNx : ∀ k : ↥K, k ∈ N ↔ (k : G) ∈ zpowers x := fun k => MonoidHom.mem_ker.trans (hπk k)
  have hN3 : Nat.card N = 3 := by
    have hNeq : N = (zpowers x).subgroupOf K := by
      ext k
      rw [hNx, mem_subgroupOf]
    rw [hNeq, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hxK)).toEquiv, Nat.card_zpowers,
      hx3]
  have hNo : Odd (Nat.card N) := by rw [hN3]; decide
  have hNc : N ≤ center ↥K := by
    intro n hn
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp ((hNx n).mp hn)
    change (k : G) * (n : G) = (n : G) * (k : G)
    rw [← hj]
    exact ((Commute.zpow_right (hxc k (hKB k.2) : Commute (k : G) x) j)).eq
  have : N.Normal := normal_of_le_center hNc
  set D := commutator ↥K with hDdef
  have hmap : D.map π = (⊤ : Subgroup ↥K).map π := by
    rw [hDdef, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← _root_.commutator_def, SuzB0.invE_one_perfect]
  have hDN : D ⊔ N = ⊤ := by
    have h := map_eq_map_iff.mp hmap
    rwa [top_sup_eq] at h
  have hB₀D : B₀ = D.map K.subtype := by
    rw [hS.B₀_eq, ← hK, hDdef, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      range_subtype]
  refine ⟨?_, ?_⟩
  ·
    have hDD : D ≤ ⁅D, D⁆ := by
      rw [hDdef, _root_.commutator_def, commutator_le]
      intro a _ b _
      obtain ⟨d₁, hd₁, n₁, hn₁, rfl⟩ := mem_sup_of_normal_right.mp (hDN ▸ mem_top a : a ∈ D ⊔ N)
      obtain ⟨d₂, hd₂, n₂, hn₂, rfl⟩ := mem_sup_of_normal_right.mp (hDN ▸ mem_top b : b ∈ D ⊔ N)
      rw [commutatorElement_mul_central_central (fun m => (mem_center_iff.mp (hNc hn₁) m).symm)
        (fun m => (mem_center_iff.mp (hNc hn₂) m).symm)]
      exact commutator_mem_commutator hd₁ hd₂
    have h1 : (commutator ↥B₀).map B₀.subtype = (⊤ : Subgroup ↥B₀).map B₀.subtype := by
      rw [map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype]
      refine le_antisymm (commutator_le_self B₀) ?_
      conv_lhs => rw [hB₀D]
      calc D.map K.subtype ≤ (⁅D, D⁆).map K.subtype := map_mono hDD
        _ = ⁅D.map K.subtype, D.map K.subtype⁆ := map_commutator _ _ _
        _ = ⁅B₀, B₀⁆ := by rw [← hB₀D]
    exact map_injective B₀.subtype_injective h1
  ·
    have hT2 : IsPGroup 2 (T.subgroupOf K) := hS.T_two.comap_subtype
    by_cases hND : N ⊓ D = ⊥
    · have h := le_of_isPGroup_of_sup_eq_top hDN hND hNc hNo hT2
      intro t ht
      rw [hB₀D]
      exact ⟨⟨t, hTK ht⟩, h (mem_subgroupOf.mpr ht), rfl⟩
    · have hNle : N ≤ D := by
        have hdvd : Nat.card ↥(N ⊓ D) ∣ 3 := hN3 ▸ card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd ((card_eq_one).mp h1) hND
        · have := eq_of_le_of_card_ge (inf_le_left : N ⊓ D ≤ N) (by rw [h3, hN3])
          rw [← this]
          exact inf_le_right
      have hDtop : D = ⊤ := by rw [← hDN, sup_eq_left.mpr hNle]
      intro t ht
      rw [hB₀D, hDtop]
      exact ⟨⟨t, hTK ht⟩, mem_top _, rfl⟩

theorem perfect_B₀_and_T_le
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) : commutator ↥B₀ = ⊤ ∧ T ≤ B₀ := by
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨-, -, π, hπs, hπk, -⟩ := exists_hom_invE hS e₀
  exact perfect_B₀_and_T_le_of_hom hS rfl hπs hπk

theorem eq_of_normal_of_not_le
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {N : Subgroup G} (hNB : N ≤ B₀)
    (hBN : B₀ ≤ normalizer (N : Set G)) (hNQ : ¬ N ≤ Q) : N = B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, φ, hφs, hφk⟩ := sec3B0_proof G A A₁ R g E F x Zs P T Q B₀ z y hS
  have hsimp := (SuzB0.omega_facts SuzB0.b0_parts.2.2.2.2.2.2).2.2.1
  have hperf := (perfect_B₀_and_T_le hS).1
  set N' := N.subgroupOf B₀ with hN'
  have hN'n : N'.Normal := ⟨fun n hn b => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (hBN b.2) n).mp (mem_subgroupOf.mp hn))⟩
  have : (N'.map φ).Normal := hN'n.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map φ) with h | h
  · exfalso
    apply hNQ
    intro n hn
    have h1 : φ ⟨n, hNB hn⟩ ∈ N'.map φ := ⟨⟨n, hNB hn⟩, mem_subgroupOf.mpr hn, rfl⟩
    rw [h, mem_bot] at h1
    have h2 : (⟨n, hNB hn⟩ : ↥B₀) ∈ φ.ker := h1
    rw [hφk, mem_subgroupOf] at h2
    exact h2
  · have hsup : φ.ker ⊔ N' = ⊤ := by
      have h1 : N'.map φ = (⊤ : Subgroup ↥B₀).map φ := by
        rw [h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hφs]
      have h2 := map_eq_map_iff.mp h1
      rwa [top_sup_eq, sup_comm] at h2
    have hQ2 : IsPGroup 2 ↥(Q.subgroupOf B₀) := hS.q8.1.1.comap_subtype
    have h2grp : IsPGroup 2 (↥B₀ ⧸ N') := by
      refine hQ2.of_surjective ((QuotientGroup.mk' N').comp (Q.subgroupOf B₀).subtype) ?_
      intro q
      induction q using QuotientGroup.induction_on with
      | H b =>
        obtain ⟨k, hk, n, hn, rfl⟩ := mem_sup_of_normal_right.mp (hsup ▸ mem_top b : b ∈ φ.ker ⊔ N')
        rw [hφk] at hk
        refine ⟨⟨k, hk⟩, ?_⟩
        change (k : ↥B₀ ⧸ N') = ((k * n : ↥B₀) : ↥B₀ ⧸ N')
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
    have hqperf : commutator (↥B₀ ⧸ N') = ⊤ := by
      have h1 := map_commutator (⊤ : Subgroup ↥B₀) ⊤ (QuotientGroup.mk' N')
      rw [← _root_.commutator_def, hperf, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N')] at h1
      rw [_root_.commutator_def]
      exact h1.symm
    have hsub : Subsingleton (↥B₀ ⧸ N') := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      have : Group.IsNilpotent (↥B₀ ⧸ N') := h2grp.isNilpotent
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥B₀ ⧸ N')
      rw [hqperf] at hlt
      exact lt_irrefl _ hlt
    refine le_antisymm hNB fun b hb => ?_
    have h1 : ((⟨b, hb⟩ : ↥B₀) : ↥B₀ ⧸ N') = 1 := Subsingleton.elim _ _
    exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

end B0

section OddCore

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem oddCoreIn_le_centralizer_Q₀
    (h17 : Step17G24Odd) (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    AS76b.oddCoreIn (centralizer (Q : Set G)) ≤ centralizer (Q₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.dData
  have hSz := hD.suz
  have hS := hSz.setting
  have hstd := hS.base.hyp.standard
  have hNK := AS76b.normalizer_centralizer_eq hstd
  set C := centralizer (Q : Set G) with hCdef
  set O := AS76b.oddCoreIn C with hOdef
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn C
  have hCO : C ≤ normalizer (O : Set G) := AS76b.le_normalizer_oddCoreIn C
  have hQ₀C : Q₀ ≤ C := le_centralizer_iff.mpr (hSz.Q_le.trans (step37_i hQ))
  have hEP : E ≤ P := hSz.P_cE.symm.le.trans inf_le_left
  have hEO : E ≤ normalizer (O : Set G) := fun e he =>
    AS76b.normalizer_le_normalizer_oddCoreIn C
      (mem_normalizer_centralizer (hSz.T_Q (hSz.P_le (hEP he))))
  obtain ⟨X, hOX, hX⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) ⟨hOodd, hEO⟩
  obtain ⟨hXsyl, hXeq⟩ := h17 G A A₁ R g E F x hS X hX
  obtain ⟨Kf, _, _, _, -, f, -, l, -, hDf, hQ₀⟩ := exists_sec3Model_Q₀ hQ
  have hQ₀D : Q₀ ≤ D := by
    rw [hQ₀, hDf]
    exact tr_mono
      ((G2.g2Q0_le_g2V l).trans (G2.g2V_le_g2V0.trans G2.g2V0_le_g2ShortParabolicRadical))
  have hDA : D ≤ A := by
    rw [hD.D_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hD2 : IsPGroup 2 D := by
    rw [hD.D_eq]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXAD : X ⊓ A ≤ normalizer (D : Set G) := by
    intro a ha
    have h1 := hXsyl.le ha
    have h2 : a ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
      ⟨h1.1, centralizer_le_normalizer _ h1.2⟩
    rw [hD.D_eq]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer h2)
  have hZ : ∀ a ∈ O, a ∈ A → ∀ q ∈ Q₀, a * q = q * a := by
    intro a haO haA q hq
    have hc1 : q * a * q⁻¹ * a⁻¹ ∈ D := by
      have h1 : a * q⁻¹ * a⁻¹ ∈ D :=
        (mem_normalizer_iff.mp (hXAD ⟨hOX haO, haA⟩) _).mp (inv_mem (hQ₀D hq))
      have h2 := mul_mem (hQ₀D hq) h1
      rwa [show q * (a * q⁻¹ * a⁻¹) = q * a * q⁻¹ * a⁻¹ by group] at h2
    have hc2 : q * a * q⁻¹ * a⁻¹ ∈ O :=
      mul_mem ((mem_normalizer_iff.mp (hCO (hQ₀C hq)) _).mp haO) (inv_mem haO)
    have hc3 : q * a * q⁻¹ * a⁻¹ = 1 := by
      have h2 : q * a * q⁻¹ * a⁻¹ ∈ O ⊓ D := ⟨hc2, hc1⟩
      rw [AS76b.oddCoreIn_inf_eq_bot hD2, mem_bot] at h2
      exact h2
    calc a * q = (q * a * q⁻¹ * a⁻¹)⁻¹ * (q * a) := by group
      _ = q * a := by rw [hc3, inv_one, one_mul]
  have hAN : A ≤ normalizer (AS76b.oddCoreIn (centralizer (A : Set G)) : Set G) := fun a ha =>
    AS76b.normalizer_le_normalizer_oddCoreIn _ (by rw [hNK]; exact le_normalizer ha)
  obtain ⟨eQ⟩ := hQ.Q₀_iso
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num)
  intro w hw
  rw [mem_centralizer_iff]
  intro q hq
  have hwX : w ∈ ((X : Subgroup G) : Set G) := hOX hw
  rw [hXeq, coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans hAN), Set.mem_mul] at hwX
  obtain ⟨a, ha, k, hk, hak⟩ := hwX
  have hkA : k ∈ centralizer (A : Set G) := AS76b.oddCoreIn_le _ hk
  have hqA : q ∈ A := hDA (hQ₀D hq)
  have hcA : w * q * w⁻¹ * q⁻¹ ∈ A := by
    have hkq : k * q * k⁻¹ = q := by
      rw [← mem_centralizer_iff.mp hkA q hqA, mul_inv_cancel_right]
    have e1 : w * q * w⁻¹ * q⁻¹ = a * (k * q * k⁻¹) * a⁻¹ * q⁻¹ := by rw [← hak]; group
    rw [e1, hkq]
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp ha).2 hqA) (inv_mem (mem_inf.mp ha).2))
      (inv_mem hqA)
  have hcO : w * q * w⁻¹ * q⁻¹ ∈ O := by
    have h1 : q * w⁻¹ * q⁻¹ ∈ O := (mem_normalizer_iff.mp (hCO (hQ₀C hq)) _).mp (inv_mem hw)
    have h2 := mul_mem hw h1
    rwa [show w * (q * w⁻¹ * q⁻¹) = w * q * w⁻¹ * q⁻¹ by group] at h2
  obtain ⟨m, hm⟩ := hQ₀2 ⟨q, hq⟩
  have hqm : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  exact (commute_of_commutator_commute hOodd hqm (hCO (hQ₀C hq)) hw
    (hZ _ hcO hcA q hq)).symm

end OddCore

section GW

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem mem_of_two_pow_eq_one_of_odd_index {L : Subgroup H} [L.Normal] (hL : Odd L.index)
    {h : H} {n : ℕ} (hh : h ^ 2 ^ n = 1) : h ∈ L := by
  have h1 : (QuotientGroup.mk' L h) ^ 2 ^ n = 1 := by rw [← map_pow, hh, map_one]
  have h2 : orderOf (QuotientGroup.mk' L h) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk' L h) ∣ Nat.card (H ⧸ L) := orderOf_dvd_natCard _
  rw [← index_eq_card] at h3
  have hcop : Nat.Coprime (2 ^ n) L.index := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hL)
  have h4 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h3))
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4

theorem map_mem_of_perfect_action
    {S : Subgroup H} (hS4 : Nat.card S = 4) (hSexp : ∀ s ∈ S, s * s = 1) {j : ℕ} (hj : Odd j)
    (hH : Nat.card H = 4 * j) (hcore : pPrimeCore 2 H = ⊥) {B : Type} [Group B] [Finite B]
    [Group.IsPerfect B] (Φ : B →* MulAut H) {T₁ : Subgroup B} (hT₁ : IsPGroup 2 T₁)
    (hB : ∀ N : Subgroup B, N.Normal → N.relIndex T₁ ≤ 4 → N = ⊤) :
    ∀ b : B, ∀ s ∈ S, Φ b s ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot8 : ¬ 8 ∣ Nat.card H := fun ⟨u, hu⟩ => by
    rw [hH] at hu
    obtain ⟨t, rfl⟩ := hj
    omega
  have hfac : (Nat.card H).factorization 2 = 2 := by
    rw [hH, Nat.factorization_mul (by norm_num) (by rintro rfl; exact absurd hj (by decide)),
      Finsupp.add_apply, show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hj ∘ even_iff_two_dvd.mpr)]
  let P₀ : Sylow 2 H := Sylow.ofCard S (by rw [hS4, hfac]; norm_num)
  have hP₀ : (P₀ : Subgroup H) = S := Sylow.coe_ofCard _ _
  have : Nontrivial ↥S := by
    rw [← Finite.one_lt_card_iff_nontrivial, hS4]
    norm_num
  have : IsKleinFour ↥S := by
    refine ⟨hS4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (hSexp g g.2)) hg
  obtain ⟨eK⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥S) (G₂ := DihedralGroup 2)
  have hDih : CFSG.GorensteinWalter.HasDihedralSylowTwo H := fun S' =>
    ⟨1, le_rfl, ⟨(P₀.equiv S').symm.trans ((MulEquiv.subgroupCongr hP₀).trans eK)⟩⟩
  set L₂ : Subgroup H := normalClosure {h : H | ∃ n : ℕ, h ^ 2 ^ n = 1} with hL₂def
  have hL₂inv : ∀ b : B, ∀ l ∈ L₂, Φ b l ∈ L₂ := by
    intro b
    have : (L₂.comap ((Φ b : H ≃* H) : H →* H)).Normal := Normal.comap inferInstance _
    have h : L₂ ≤ L₂.comap ((Φ b : H ≃* H) : H →* H) := by
      refine normalClosure_le_normal fun h hh => ?_
      obtain ⟨n, hn⟩ := hh
      refine subset_normalClosure ⟨n, ?_⟩
      change (Φ b h) ^ 2 ^ n = 1
      rw [← map_pow, hn, map_one]
    exact fun l hl => h hl
  have hSL₂ : S ≤ L₂ := fun s hs => subset_normalClosure ⟨2, by
    have h1 : (⟨s, hs⟩ : ↥S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hS4] at h1
    simpa using congrArg Subtype.val h1⟩
  have hD := CFSG.GorensteinWalter.gorensteinWalter H hDih
  let ε : H ⧸ pPrimeCore 2 H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  rcases hD with ⟨_, h2⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, K, hK, L, hLn, hLi, hLm⟩
  ·
    have h2' : IsPGroup 2 H := h2.of_equiv ε
    obtain ⟨k, hk⟩ := h2'.exists_card_eq
    have hj1 : j = 1 := by
      have hdvd : j ∣ 2 ^ k := ⟨4, by rw [← hk, hH]; ring⟩
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hj)) hdvd
    have hStop : S = ⊤ := eq_top_of_card_eq S (by rw [hS4, hH, hj1])
    intro b s _
    rw [hStop]
    exact mem_top _
  ·
    exfalso
    have h1 : Nat.card H = 2520 := by
      rw [← Nat.card_congr ε.toEquiv, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [hH] at h1
    obtain ⟨t, rfl⟩ := hj
    omega
  ·
    set L' : Subgroup H := L.map (ε : H ⧸ pPrimeCore 2 H →* H) with hL'def
    have hL'n : L'.Normal := hLn.map _ ε.surjective
    have hL'i : Odd L'.index := by rw [hL'def, index_map_equiv]; exact hLi
    let eL'L : ↥L' ≃* ↥L := (L.equivMapOfInjective (ε : H ⧸ pPrimeCore 2 H →* H) ε.injective).symm
    have hcardL' : Nat.card L' * L'.index = 4 * j := by rw [card_mul_index, hH]
    have hnot8L : ¬ 8 ∣ Nat.card L' := fun ⟨u, hu⟩ => by
      rw [hu] at hcardL'
      have hj2 : j = 2 * (u * L'.index) := by linarith
      rw [hj2] at hj
      exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) hj
    have hSL' : S ≤ L' := fun s hs => mem_of_two_pow_eq_one_of_odd_index hL'i (n := 2) (by
      have h1 : (⟨s, hs⟩ : ↥S) ^ Nat.card S = 1 := pow_card_eq_one'
      rw [hS4] at h1
      simpa using congrArg Subtype.val h1)
    have hL₂L' : L₂ ≤ L' := normalClosure_le_normal fun h ⟨n, hn⟩ =>
      mem_of_two_pow_eq_one_of_odd_index hL'i hn
    have hqodd : Odd (Nat.card K) := by
      obtain ⟨p', n', -, hpodd, -, hq⟩ := hK
      rw [hq]
      exact hpodd.pow
    rcases hLm with hP | hP
    ·
      obtain ⟨eP⟩ := hP
      let eL' : ↥L' ≃* CFSG.GorensteinWalter.PSL2 K := eL'L.trans eP
      have hcardPSL : Nat.card L' = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
        rw [Nat.card_congr eL'.toEquiv]
        exact CFSG.GorensteinWalter.psl2_card_formula K hK
      have hdich : L₂ = S ∨ L₂ = L' := by
        by_cases hq4 : 4 ≤ Nat.card K
        · have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 K) :=
            Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
          have : IsSimpleGroup ↥L' := eL'.isSimpleGroup
          have : (L₂.subgroupOf L').Normal := Normal.subgroupOf inferInstance L'
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L₂.subgroupOf L') with h | h
          · exfalso
            have hSbot : S = ⊥ := eq_bot_iff.mpr fun s hs => by
              have h1 : (⟨s, hSL' hs⟩ : ↥L') ∈ L₂.subgroupOf L' := mem_subgroupOf.mpr (hSL₂ hs)
              rw [h, mem_bot] at h1
              exact mem_bot.mpr (congrArg Subtype.val h1)
            rw [hSbot, card_bot] at hS4
            norm_num at hS4
          · right
            refine le_antisymm hL₂L' fun l hl => ?_
            have h1 : (⟨l, hl⟩ : ↥L') ∈ L₂.subgroupOf L' := by rw [h]; exact mem_top _
            exact mem_subgroupOf.mp h1
        · have hq3 : Nat.card K = 3 := by
            obtain ⟨p', n', hp', hpodd, hn', hq⟩ := hK
            have h3 : 3 ≤ p' := by
              have h2 := hp'.two_le
              rcases hpodd with ⟨t, rfl⟩
              omega
            have h3' : 3 ≤ Nat.card K := by
              rw [hq]
              exact h3.trans (Nat.le_self_pow (by omega) p')
            obtain ⟨t, ht⟩ := hqodd
            omega
          have h12 : Nat.card L' = 12 := by
            rw [hcardPSL, hq3]
            norm_num
          have hdvd : Nat.card L₂ ∣ 12 := h12 ▸ card_dvd_of_le hL₂L'
          have h4 : 4 ∣ Nat.card L₂ := hS4 ▸ card_dvd_of_le hSL₂
          have hle : Nat.card L₂ ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
          have hcases : Nat.card L₂ = 4 ∨ Nat.card L₂ = 12 := by
            interval_cases h : Nat.card L₂ <;> simp_all
          rcases hcases with h | h
          · exact Or.inl (eq_of_le_of_card_ge hSL₂ (by rw [h, hS4])).symm
          · exact Or.inr (eq_of_le_of_card_ge hL₂L' (by rw [h, h12]))
      rcases hdich with hL₂S | hL₂L'eq
      · intro b s hs
        rw [← hL₂S] at hs ⊢
        exact hL₂inv b s hs
      ·
        set ΦL := restrictInvariantAction Φ L₂ hL₂inv with hΦLdef
        let eL₂ : ↥L₂ ≃* CFSG.GorensteinWalter.PSL2 K := (MulEquiv.subgroupCongr hL₂L'eq).trans eL'
        let ψ : B →* OuterAutomorphisms.Outer (CFSG.GorensteinWalter.PSL2 K) :=
          (QuotientGroup.mk' (OuterAutomorphisms.inner (CFSG.GorensteinWalter.PSL2 K))).comp
            ((MulAut.congr eL₂).toMonoidHom.comp ΦL)
        have : IsMulCommutative (OuterAutomorphisms.Outer (CFSG.GorensteinWalter.PSL2 K)) :=
          ⟨⟨CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K⟩⟩
        have hψ : ψ = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative ψ
        have hinner : ∀ b, ΦL b ∈ (MulAut.conj : ↥L₂ →* MulAut ↥L₂).range := by
          intro b
          have h1 : ψ b = 1 := by rw [hψ, MonoidHom.one_apply]
          have h2 : MulAut.congr eL₂ (ΦL b) ∈
              OuterAutomorphisms.inner (CFSG.GorensteinWalter.PSL2 K) :=
            (QuotientGroup.eq_one_iff _).mp h1
          obtain ⟨y, hy⟩ := h2
          refine ⟨eL₂.symm y, ?_⟩
          apply (MulAut.congr eL₂).injective
          rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
          exact hy
        have hT₁map : T₁.map ΦL ≤ (MulAut.conj : ↥L₂ →* MulAut ↥L₂).range := by
          rintro _ ⟨t, -, rfl⟩
          exact hinner t
        obtain ⟨k, hk⟩ := hT₁.exists_card_eq
        obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ card_map_dvd (H := T₁) ΦL)
        have hdvd : 2 ^ a ∣ Nat.card L' := by
          rw [← ha, ← hL₂L'eq]
          exact (card_dvd_of_le hT₁map).trans (card_range_dvd _)
        have ha2 : a ≤ 2 := by
          by_contra h
          push Not at h
          exact hnot8L ((pow_dvd_pow 2 h).trans hdvd)
        have hrel : ΦL.ker.relIndex T₁ ≤ 4 := by
          rw [Subgroup.relIndex, ← MonoidHom.ker_domRestrict, index_ker,
            MonoidHom.domRestrict_range, ha]
          calc 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
            _ = 4 := by norm_num
        have hker : ΦL.ker = ⊤ := hB _ inferInstance hrel
        intro b s hs
        have h1 : ΦL b = 1 := MonoidHom.mem_ker.mp (hker ▸ mem_top b)
        have h2 : ΦL b ⟨s, hSL₂ hs⟩ = ⟨s, hSL₂ hs⟩ := by rw [h1]; rfl
        have h3 : Φ b s = s := congrArg Subtype.val h2
        rw [h3]
        exact hs
    ·
      obtain ⟨eP⟩ := hP
      exfalso
      apply hnot8L
      rw [Nat.card_congr (eL'L.trans eP).toEquiv, CFSG.GorensteinWalter.pgl2_card_formula K]
      exact (Nat.eight_dvd_sq_sub_one_of_odd hqodd).mul_left _

end GW

end Sec3

section Step37iv

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

open Sec3 in
theorem step37_iv
    (h17 : Step17G24Odd) (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    B₀ ≤ centralizer (Q₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz := hQ.dData.suz
  obtain ⟨-, hBQ, -⟩ := sec3B0_proof G A A₁ R g E F x Zs P T Q B₀ z y hSz
  obtain ⟨hBperf, hTB⟩ := perfect_B₀_and_T_le hSz
  have hOQ₀ := oddCoreIn_le_centralizer_Q₀ h17 hQ
  set C := centralizer (Q : Set G) with hCdef
  have hQ₀C : Q₀ ≤ C := le_centralizer_iff.mpr (hSz.Q_le.trans (step37_i hQ))
  have hsyl := step37_iii hQ
  obtain ⟨eQ⟩ := hQ.Q₀_iso
  have hQ₀8 : Nat.card Q₀ = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [hQ₀8]; norm_num)
  have hzZQ : z ∈ centerIn Q := by rw [hSz.Q_center]; exact mem_zpowers z
  have hzQ : z ∈ Q := (mem_inf.mp hzZQ).1
  have hz2 : orderOf z = 2 := by
    have h1 := hSz.q8.1.2.2.2
    rw [← card_centerIn, hSz.Q_center, Nat.card_zpowers] at h1
    exact h1
  have hzQ₀ : z ∈ Q₀ := by
    have h : z ∈ centerIn Q₀ := by rw [hQ.center_Q₀]; exact hzZQ
    exact (mem_inf.mp h).1
  have hzC : z ∈ C := hQ₀C hzQ₀
  have hsq : ∀ q ∈ Q₀, q * q ∈ zpowers z := by
    intro q hq
    have h : q * q ∈ centerIn Q₀ := by
      refine mem_inf.mpr ⟨mul_mem hq hq, mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := quaternion_facts.2.1 (eQ ⟨q, hq⟩) (eQ ⟨w, hw⟩)
      rw [← map_pow, ← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (eQ.injective h1)
      simp only [coe_mul, pow_two] at h2
      exact h2.symm
    rwa [hQ.center_Q₀, hSz.Q_center] at h
  have hBC : B₀ ≤ normalizer (C : Set G) := fun b hb => mem_normalizer_centralizer (hBQ hb)
  have hBz : B₀ ≤ centralizer ({z} : Set G) := by
    rw [hSz.B₀_eq]
    exact (commutator_le_self _).trans inf_le_right
  set z' : ↥C := ⟨z, hzC⟩ with hz'
  have hz'c : z' ∈ center ↥C := mem_center_iff.mpr fun c =>
    Subtype.ext (mem_centralizer_iff.mp c.2 z hzQ).symm
  have hz'2 : orderOf z' = 2 := by
    rw [← hz2]
    exact (orderOf_injective C.subtype C.subtype_injective z').symm
  set Oc : Subgroup ↥C := pPrimeCore 2 ↥C with hOcdef
  have hOcodd : Odd (Nat.card Oc) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have : (zpowers z').Normal := normal_of_le_center (zpowers_le.mpr hz'c)
  have : Oc.Normal := pPrimeCore_normal
  set N₀ : Subgroup ↥C := Oc ⊔ zpowers z' with hN₀def
  have hOcz : Oc ⊓ zpowers z' = ⊥ := by
    refine eq_bot_iff.mpr fun n hn => mem_bot.mpr ?_
    have h1 : orderOf n ∣ Nat.card Oc := Subgroup.orderOf_dvd_natCard Oc (mem_inf.mp hn).1
    have h2 : orderOf n ∣ 2 := by
      have h := Subgroup.orderOf_dvd_natCard _ (mem_inf.mp hn).2
      rwa [Nat.card_zpowers, hz'2] at h
    have hcop : Nat.Coprime 2 (Nat.card Oc) := Nat.coprime_two_left.mpr hOcodd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))
  have hN₀card : Nat.card N₀ = 2 * Nat.card Oc := by
    have h := card_sup_mul_card_inf (H := Oc) (R := zpowers z')
      (fun w _ => Sec3.mem_normalizer_of_normal inferInstance w)
    rw [hOcz, card_bot, mul_one, Nat.card_zpowers, hz'2] at h
    rw [h, mul_comm]
  have hN₀2 : ∀ n ∈ N₀, ∀ m : ℕ, n ^ 2 ^ m = 1 → n ∈ zpowers z' := by
    intro n hn m hm
    obtain ⟨o, ho, w, hw, rfl⟩ := mem_sup_of_normal_right.mp hn
    have hwc : Commute o w := (mem_center_iff.mp
      ((zpowers_le.mpr hz'c) hw) o)
    rw [hwc.mul_pow] at hm
    have ho2 : o ^ 2 ^ m ∈ Oc ⊓ zpowers z' := by
      refine mem_inf.mpr ⟨pow_mem ho _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hm]
      exact inv_mem (pow_mem hw _)
    rw [hOcz, mem_bot] at ho2
    have ho1 : o = 1 := by
      have h1 : orderOf o ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one ho2
      have h2 : orderOf o ∣ Nat.card Oc := Subgroup.orderOf_dvd_natCard Oc ho
      have hcop : Nat.Coprime (2 ^ m) (Nat.card Oc) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hOcodd)
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
    rw [ho1, one_mul]
    exact hw
  set α : ↥B₀ →* MulAut ↥C := (normalizerConjAut C).comp (inclusion hBC) with hαdef
  have hα : ∀ b : ↥B₀, ∀ c : ↥C, ((α b c : ↥C) : G) = b * c * (b : G)⁻¹ := fun b c => rfl
  have hαz : ∀ b : ↥B₀, α b z' = z' := fun b => Subtype.ext (by
    rw [hα, mem_centralizer_singleton_iff.mp (hBz b.2), mul_inv_cancel_right])
  have hαN : ∀ b : ↥B₀, ∀ n ∈ N₀, α b n ∈ N₀ := by
    intro b n hn
    obtain ⟨o, ho, w, hw, rfl⟩ := mem_sup_of_normal_right.mp hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [map_mul, map_zpow, hαz]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right (zpow_mem (mem_zpowers z') k))
    have h1 : Oc.map ((α b : ↥C ≃* ↥C) : ↥C →* ↥C) = Oc :=
      characteristic_iff_map_eq.mp inferInstance (α b)
    rw [← h1]
    exact mem_map_of_mem _ ho
  set Φ := quotientConjAction α N₀ hαN with hΦdef
  set Q₀' : Subgroup ↥C := Q₀.subgroupOf C with hQ₀'def
  have hQ₀'8 : Nat.card Q₀' = 8 := by
    rw [hQ₀'def, Nat.card_congr (subgroupOfEquivOfLe hQ₀C).toEquiv, hQ₀8]
  set St : Subgroup (↥C ⧸ N₀) := Q₀'.map (QuotientGroup.mk' N₀) with hStdef
  have hSt4 : Nat.card St = 4 := by
    have hker : N₀ ⊓ Q₀' = zpowers z' := by
      refine le_antisymm (fun n hn => ?_) (zpowers_le.mpr ⟨mem_sup_right (mem_zpowers z'),
        mem_subgroupOf.mpr hzQ₀⟩)
      obtain ⟨m, hm⟩ := hQ₀2 ⟨(n : G), (mem_inf.mp hn).2⟩
      exact hN₀2 n (mem_inf.mp hn).1 m (Subtype.ext (by simpa using congrArg Subtype.val hm))
    have h := card_ker_mul_card_range ((QuotientGroup.mk' N₀).domRestrict Q₀')
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', MonoidHom.domRestrict_range,
      ← card_map_of_injective Q₀'.subtype_injective, subgroupOf_map_subtype, hker,
      Nat.card_zpowers, hz'2, hQ₀'8] at h
    rw [hStdef]
    omega
  have hStexp : ∀ s ∈ St, s * s = 1 := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hsq (q : G) (mem_subgroupOf.mp hq))
    refine mem_sup_right ⟨k, Subtype.ext ?_⟩
    simpa [hz'] using hk
  obtain ⟨i, hi, hCi⟩ : ∃ i, Odd i ∧ Nat.card C = 8 * i := by
    obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.mp hsyl
    refine ⟨Q₀.relIndex C, Nat.not_even_iff_odd.mp (fun h => hdvd (even_iff_two_dvd.mp h)), ?_⟩
    have h := relIndex_mul_card Q₀ C
    rw [inf_eq_left.mpr hQ₀C, hQ₀8] at h
    rw [← h, mul_comm]
  obtain ⟨j, hj⟩ : 4 ∣ Nat.card (↥C ⧸ N₀) := hSt4 ▸ card_subgroup_dvd_card St
  have hjodd : Odd j := by
    have h := card_eq_card_quotient_mul_card_subgroup N₀
    rw [hj, hN₀card, hCi] at h
    have h2 : i = j * Nat.card Oc := by linarith
    exact hi.of_dvd_nat ⟨Nat.card Oc, h2⟩
  have hcore : pPrimeCore 2 (↥C ⧸ N₀) = ⊥ := by
    refine pPrimeCore_eq_bot_iff.mpr fun Kt hKt hcop => ?_
    set Y := Kt.comap (QuotientGroup.mk' N₀) with hYdef
    have : Y.Normal := hKt.comap _
    have hN₀Y : N₀ ≤ Y := fun n hn => by
      change QuotientGroup.mk' N₀ n ∈ Kt
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact one_mem _
    have hYcard : Nat.card Y = 2 * (Nat.card Oc * Nat.card Kt) := by
      have h := card_ker_mul_card_range ((QuotientGroup.mk' N₀).domRestrict Y)
      rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', MonoidHom.domRestrict_range,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N₀),
        ← card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr hN₀Y, hN₀card] at h
      rw [← h]
      ring
    have hodd : Odd (Nat.card Oc * Nat.card Kt) := hOcodd.mul (Nat.coprime_two_left.mp hcop)
    have hYle := le_pPrimeCore_sup_zpowers hz'c hz'2 this (hN₀Y (mem_sup_right (mem_zpowers z')))
      hodd hYcard
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N₀) Kt, ← hYdef]
    exact eq_bot_iff.mpr ((map_mono hYle).trans (QuotientGroup.map_mk'_self N₀).le)
  have : Group.IsPerfect ↥B₀ := Group.isPerfect_def.2 hBperf
  have hT₁ : IsPGroup 2 (T.subgroupOf B₀) := hSz.T_two.comap_subtype
  have hT₁card : Nat.card (T.subgroupOf B₀) = 2 ^ 13 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTB).toEquiv, hSz.T_card]
  have hB : ∀ N : Subgroup ↥B₀, N.Normal → N.relIndex (T.subgroupOf B₀) ≤ 4 → N = ⊤ := by
    intro N hN hrel
    have h1 := relIndex_mul_card N (T.subgroupOf B₀)
    rw [hT₁card] at h1
    have hbig : 2 ^ 11 ≤ Nat.card (N ⊓ T.subgroupOf B₀ : Subgroup ↥B₀) := by
      by_contra h
      push Not at h
      have : N.relIndex (T.subgroupOf B₀) * Nat.card (N ⊓ T.subgroupOf B₀ : Subgroup ↥B₀) <
          4 * 2 ^ 11 := Nat.mul_lt_mul_of_le_of_lt hrel h (by norm_num)
      omega
    have hNQ : ¬ N.map B₀.subtype ≤ Q := by
      intro hle
      have h2 : (N ⊓ T.subgroupOf B₀).map B₀.subtype ≤ Q :=
        (map_mono inf_le_left).trans hle
      have h3 := card_le_of_le h2
      rw [card_map_of_injective B₀.subtype_injective, hSz.q8.2.1] at h3
      omega
    have h4 := eq_of_normal_of_not_le hSz (map_subtype_le N)
      (AS76b.le_normalizer_map_subtype_of_normal B₀ N) hNQ
    exact map_injective B₀.subtype_injective (by rw [h4, ← MonoidHom.range_eq_map, range_subtype])
  have hinv := map_mem_of_perfect_action hSt4 hStexp hjodd hj hcore Φ hT₁ hB
  have hconj : ∀ b ∈ B₀, ∀ q ∈ Q₀, b * q * b⁻¹ ∈ Q₀ := by
    intro b hb q hq
    have hq' : (QuotientGroup.mk' N₀ ⟨q, hQ₀C hq⟩ : ↥C ⧸ N₀) ∈ St :=
      ⟨⟨q, hQ₀C hq⟩, mem_subgroupOf.mpr hq, rfl⟩
    obtain ⟨q₁, hq₁, hq₁e⟩ := hinv ⟨b, hb⟩ _ hq'
    have h1 : (QuotientGroup.mk' N₀ q₁ : ↥C ⧸ N₀) =
        QuotientGroup.mk' N₀ (α ⟨b, hb⟩ ⟨q, hQ₀C hq⟩) := hq₁e
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    obtain ⟨o, ho, w, hw, how⟩ := mem_sup_of_normal_right.mp h1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have he : b * q * b⁻¹ = ((q₁ : G) * z ^ k) * (o : G) := by
      have h1 := congrArg Subtype.val how
      simp only [coe_mul, coe_inv, SubgroupClass.coe_zpow, hα] at h1
      have hzo : (o : G) * z ^ k = z ^ k * o :=
        ((Commute.zpow_right (mem_centralizer_iff.mp o.2 z hzQ).symm k)).eq
      calc b * q * b⁻¹ = (q₁ : G) * ((q₁ : G)⁻¹ * (b * q * b⁻¹)) := by group
        _ = (q₁ : G) * ((o : G) * z ^ k) := by rw [h1]
        _ = ((q₁ : G) * z ^ k) * (o : G) := by rw [hzo]; group
    have hq₂ : (q₁ : G) * z ^ k ∈ Q₀ := mul_mem (mem_subgroupOf.mp hq₁) (zpow_mem hzQ₀ k)
    have hoO : (o : G) ∈ AS76b.oddCoreIn C := by
      show (o : G) ∈ (CFSG.Assembly.oddCore ↥C).map C.subtype
      rw [AS76b.assemblyOddCore_eq_pPrimeCore]
      exact ⟨o, ho, rfl⟩
    obtain ⟨m, hm⟩ := hQ₀2 ⟨q, hq⟩
    have hqm : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hbm : (b * q * b⁻¹) ^ 2 ^ m = 1 := by
      rw [show b * q * b⁻¹ = MulAut.conj b q from rfl, ← map_pow, hqm, map_one]
    rw [he, (Commute.mul_pow ((mem_centralizer_iff.mp (hOQ₀ hoO) _ hq₂)) _)] at hbm
    have ho1 : (o : G) ^ 2 ^ m = 1 := by
      have h1 : (o : G) ^ 2 ^ m ∈ AS76b.oddCoreIn C ⊓ Q₀ := by
        refine mem_inf.mpr ⟨pow_mem hoO _, ?_⟩
        rw [eq_inv_of_mul_eq_one_right hbm]
        exact inv_mem (pow_mem hq₂ _)
      rw [AS76b.oddCoreIn_inf_eq_bot hQ₀2, mem_bot] at h1
      exact h1
    have ho' : (o : G) = 1 := by
      have h1 : orderOf (o : G) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one ho1
      have h2 : orderOf (o : G) ∣ Nat.card (AS76b.oddCoreIn C) :=
        Subgroup.orderOf_dvd_natCard _ hoO
      have hcop : Nat.Coprime (2 ^ m) (Nat.card (AS76b.oddCoreIn C)) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (AS76b.odd_card_oddCoreIn C))
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
    rw [he, ho', mul_one]
    exact hq₂
  have hBN : B₀ ≤ normalizer (Q₀ : Set G) := fun b hb =>
    G2.mem_normalizer_of_conj (hconj b hb) fun q hq => by
      simpa using hconj b⁻¹ (inv_mem hb) q hq
  have hTQ : ¬ T ≤ Q := fun h => by
    have h1 := card_le_of_le h
    rw [hSz.T_card, hSz.q8.2.1] at h1
    norm_num at h1
  have hNB : B₀ ⊓ centralizer (Q₀ : Set G) = B₀ :=
    eq_of_normal_of_not_le hSz inf_le_left
      (fun b hb => mem_normalizer_inf (le_normalizer hb) (mem_normalizer_centralizer (hBN hb)))
      (fun h => hTQ ((le_inf hTB (step37_i hQ)).trans h))
  rw [← hNB]
  exact inf_le_right

theorem step37_of
    (h17 : Step17G24Odd) : Step37 := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  obtain ⟨h1, h2⟩ := step37_ii hQ
  exact ⟨step37_i hQ, h1, h2, step37_iii hQ, step37_iv h17 hQ⟩

end Step37iv

end CFSG.ComponentClassification.AS81
