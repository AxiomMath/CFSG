module

public import CFSG.LocalAnalysis.SteinbergBXGMSNormalRootDichotomy
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Perm
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.ABGLocalTools

namespace GMS28

variable {D : Type*} [Group D]

section Generic

theorem exists_mul_of_mem_sup {W N : Subgroup D} (hWN : W ≤ normalizer (N : Set D)) {x : D}
    (hx : x ∈ W ⊔ N) : ∃ w ∈ W, ∃ k ∈ N, w * k = x := by
  have hx' : x ∈ ((W ⊔ N : Subgroup D) : Set D) := hx
  rw [coe_mul_of_left_le_normalizer_right W N hWN] at hx'
  obtain ⟨w, hw, k, hk, rfl⟩ := hx'
  exact ⟨w, hw, k, hk, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers {a r : D} (ha : a * a = 1) (hr : r ∈ zpowers a) :
    r = 1 ∨ r = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.emod_add_mul_ediv k 2, zpow_add, hk, zpow_zero, one_mul, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, zpow_add, hk, zpow_one, zpow_mul, h2, one_zpow, mul_one]

theorem conj_eq_of_mem_normalizer_zpowers {a l : D} (ha : a * a = 1) (ha1 : a ≠ 1)
    (hl : l ∈ normalizer ((zpowers a : Subgroup D) : Set D)) : l * a * l⁻¹ = a := by
  have hmem : l * a * l⁻¹ ∈ zpowers a := (mem_normalizer_iff.mp hl a).mp (mem_zpowers a)
  rcases eq_one_or_eq_of_mem_zpowers ha hmem with h1 | h1
  · exfalso
    apply ha1
    calc a = l⁻¹ * (l * a * l⁻¹) * l := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem conj_eq_of_odd_of_eq_mul {x b a : D} (hx : Odd (orderOf x))
    (hxa : x * a = a * x) (ha : a * a = 1) (hxb : x * b * x⁻¹ = b * a) : x * b * x⁻¹ = b := by
  have hpow : ∀ k : ℕ, x ^ k * b * (x ^ k)⁻¹ = b * a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxak : x * a ^ k * x⁻¹ = a ^ k := by
        rw [(Commute.pow_right hxa k).eq]
        group
      calc x ^ (k + 1) * b * (x ^ (k + 1))⁻¹ = x * (x ^ k * b * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * b * x⁻¹ * (x * a ^ k * x⁻¹) := by rw [ih]; group
        _ = b * a ^ (k + 1) := by rw [hxb, hxak, pow_succ']; group
  obtain ⟨m, hm⟩ := hx
  have h1 := hpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hm] at h1
  have h2 : a ^ (2 * m + 1) = a := by
    rw [pow_succ, pow_mul, sq, ha, one_pow, one_mul]
  rw [h2] at h1
  rw [hxb]
  exact h1.symm

theorem pow_conj_eq_of_conj_eq {W : Subgroup D} {x : D} (hx : ∀ w ∈ W, x * w * x⁻¹ = w)
    (k : ℕ) : ∀ w ∈ W, x ^ k * w * (x ^ k)⁻¹ = w := by
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    calc x ^ (k + 1) * w * (x ^ (k + 1))⁻¹ = x * (x ^ k * w * (x ^ k)⁻¹) * x⁻¹ := by group
      _ = w := by rw [ih w hw, hx w hw]

variable [Finite D]

theorem exists_odd_of_pow_conj_eq {W : Subgroup D} {g : D} {m : ℕ} (hm : Odd m)
    (hgm : ∀ w ∈ W, g ^ m * w * (g ^ m)⁻¹ = w) :
    ∃ d ∈ zpowers g, Odd (orderOf d) ∧ ∀ w ∈ W, d * w * d⁻¹ = g * w * g⁻¹ := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ a * c = 1 + m * s := ⟨2 ^ a * c / m, by
      have := Nat.mod_add_div (2 ^ a * c) m
      rw [hc] at this
      exact this.symm⟩
    refine ⟨g ^ (2 ^ a * c), ⟨(2 ^ a * c : ℕ), zpow_natCast g _⟩, ?_, fun w hw => ?_⟩
    · apply hb.of_dvd_nat
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_right_comm, pow_mul, ← hab, pow_orderOf_eq_one, one_pow]
    · have hs' := pow_conj_eq_of_conj_eq hgm s w hw
      rw [hs, pow_add, pow_one, pow_mul]
      calc g * (g ^ m) ^ s * w * (g * (g ^ m) ^ s)⁻¹ =
          g * ((g ^ m) ^ s * w * ((g ^ m) ^ s)⁻¹) * g⁻¹ := by group
        _ = g * w * g⁻¹ := by rw [hs']
  · have hm1 : m = 1 := le_antisymm h1 (Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hm))
    subst hm1
    refine ⟨1, one_mem _, by rw [orderOf_one]; exact odd_one, fun w hw => ?_⟩
    have := hgm w hw
    rw [pow_one] at this
    rw [this]
    group

omit [Finite D] in
theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {Q K : Subgroup D} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ S : Subgroup D, IsSylowOf p S K ∧ Q ≤ S := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hS hx, rfl⟩

theorem sup_eq_of_isSylowOf {S H K : Subgroup D} (hS : IsSylowOf 2 S H) (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set D)) (hpow : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ K) :
    S ⊔ K = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSKH : S ⊔ K ≤ H := sup_le hS.le hKH
  have : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hQ : IsPGroup 2 (H ⧸ K.subgroupOf H) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      simpa using hk
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ
  have hKidx : K.relIndex H = 2 ^ m := hm
  have h1 := Subgroup.relIndex_mul_relIndex K (S ⊔ K) H le_sup_right hSKH
  have h2 := Subgroup.relIndex_mul_relIndex S (S ⊔ K) H le_sup_left hSKH
  have hdvd : (S ⊔ K).relIndex H ∣ 2 ^ m := by
    rw [← hKidx, ← h1]
    exact dvd_mul_left _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd : ¬ 2 ∣ S.relIndex H := (isSylowOf_iff.mp hS).2.2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hodd
    rw [← h2, hj]
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 hj0) _
  rw [hj0, pow_zero] at hj
  exact le_antisymm hSKH (Subgroup.relIndex_eq_one.mp hj)

theorem IsSylowOf.exists_map_conj {p : ℕ} [Fact p.Prime] {S S' K : Subgroup D}
    (h : IsSylowOf p S K) (h' : IsSylowOf p S' K) :
    ∃ k ∈ K, S' = S.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨k, k.2, ?_⟩
  rw [← hk]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    refine ⟨K.subtype ((MulAut.conj k)⁻¹ • y), ⟨_, hy, rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨MulAut.conj k s, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
    · simp [MulAut.conj_apply]

theorem IsSylowOf.map_conj {p : ℕ} [Fact p.Prime] {S K : Subgroup D} (h : IsSylowOf p S K)
    {g : D} (hg : g ∈ normalizer (K : Set D)) :
    IsSylowOf p (S.map (MulAut.conj g).toMonoidHom) K := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hSK, hS, hdvd⟩ := h
  have hKg : K.map (MulAut.conj g).toMonoidHom = K := map_conj_eq_self_iff.mpr hg
  refine ⟨?_, hS.map _, ?_⟩
  · rw [← hKg]
    exact (map_conj_le_map_conj_iff g).mpr hSK
  · rwa [← hKg, Subgroup.relIndex_map_map,
      (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective, sup_bot_eq, sup_bot_eq]

theorem commute_of_isPGroup_of_transitive {U S : Subgroup D} {y : D}
    (hSU : S ≤ normalizer (U : Set D)) (hyU : y ∈ normalizer (U : Set D))
    (hyS : y ∈ normalizer (S : Set D))
    (htrans : ∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = b)
    (h2 : ∀ s ∈ S, ∃ k : ℕ, ∀ a ∈ U, s ^ 2 ^ k * a * (s ^ 2 ^ k)⁻¹ = a)
    (hU : 2 ∣ Nat.card U) : ∀ s ∈ S, ∀ a ∈ U, s * a * s⁻¹ = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (U : Set D) with hNdef
  set θ := U.normalizerMonoidHom with hθ
  set A : Subgroup (MulAut U) := (S.subgroupOf N).map θ with hAdef
  have hθa : ∀ (s : N) (b : U), ((θ s b : U) : D) = s * b * (s : D)⁻¹ := fun s b =>
    normalizerMonoidHom_apply_apply_coe _ s b
  have hθpow : ∀ (k : ℕ) (b : U), ((θ ⟨y, hyU⟩ ^ k) b : D) = y ^ k * b * (y ^ k)⁻¹ := by
    intro k b
    rw [← map_pow, hθa]
    rfl
  have hAp : IsPGroup 2 A := by
    rintro ⟨σ, hσ⟩
    obtain ⟨s, hsS, rfl⟩ := mem_map.mp hσ
    obtain ⟨k, hk⟩ := h2 s (mem_subgroupOf.mp hsS)
    refine ⟨k, Subtype.ext ?_⟩
    change θ s ^ 2 ^ k = 1
    rw [← map_pow]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hθa, coe_pow]
    exact hk b b.2
  have hyA : θ ⟨y, hyU⟩ ∈ normalizer (A : Set (MulAut U)) := by
    refine SteinbergBV.mem_normalizer_of_conj_mem (fun σ hσ => ?_) (fun σ hσ => ?_)
    · obtain ⟨s, hsS, rfl⟩ := mem_map.mp hσ
      refine mem_map.mpr ⟨⟨y, hyU⟩ * s * ⟨y, hyU⟩⁻¹, mem_subgroupOf.mpr ?_, ?_⟩
      · exact (mem_normalizer_iff.mp hyS s).mp (mem_subgroupOf.mp hsS)
      · rw [map_mul, map_mul, map_inv]
    · obtain ⟨s, hsS, rfl⟩ := mem_map.mp hσ
      refine mem_map.mpr ⟨⟨y, hyU⟩⁻¹ * s * ⟨y, hyU⟩, mem_subgroupOf.mpr ?_, ?_⟩
      · have := (mem_normalizer_iff.mp (inv_mem hyS) s).mp (mem_subgroupOf.mp hsS)
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv]
  have hfix1 : ∀ σ ∈ A, σ • (1 : U) = 1 := fun σ _ => by
    rw [MulAut.smul_def, map_one]
  have htrans' : ∀ β γ : U, β ≠ 1 → γ ≠ 1 → ∃ k : ℤ, θ ⟨y, hyU⟩ ^ k • β = γ := by
    intro β γ hβ hγ
    obtain ⟨m, hm⟩ := htrans β β.2 γ γ.2 (fun h1 => hβ (Subtype.ext h1))
      (fun h1 => hγ (Subtype.ext h1))
    refine ⟨(m : ℤ), Subtype.ext ?_⟩
    rw [MulAut.smul_def, zpow_natCast, hθpow, hm]
  have key := CFSG.ComponentClassification.GMS78.smul_eq_of_isPGroup hAp hyA hfix1 htrans' hU
  intro s hs a ha
  have h1 := key (θ ⟨s, hSU hs⟩) (mem_map.mpr ⟨_, mem_subgroupOf.mpr hs, rfl⟩) ⟨a, ha⟩
  rw [MulAut.smul_def] at h1
  have h2 := congrArg Subtype.val h1
  rw [hθa] at h2
  exact h2

end Generic

structure Setup (J R X U P : Subgroup D) (n : ℕ) (t : D) : Prop where
  data : GMSNormalRootData J R X U P n
  mem : t ∈ R
  ne_one : t ≠ 1
  card : Nat.card R = 2
  three_le : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard

namespace Setup

variable {J R X U P : Subgroup D} {n : ℕ} {t : D}

theorem t_mem_V (hS : Setup J R X U P n t) : t ∈ U ⊔ R := mem_sup_right hS.mem

theorem mul_self_t (hS : Setup J R X U P n t) : t * t = 1 := by
  rw [← sq]
  exact gms_sq_V hS.data t hS.t_mem_V

theorem inv_t (hS : Setup J R X U P n t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right hS.mul_self_t

theorem orderOf_t (hS : Setup J R X U P n t) : orderOf t = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hS.mul_self_t) hS.ne_one

theorem eq_zpowers [Finite D] (hS : Setup J R X U P n t) : R = zpowers t :=
  (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hS.mem)
    (by rw [hS.card, Nat.card_zpowers, hS.orderOf_t])).symm

theorem eq_one_or_eq_t [Finite D] (hS : Setup J R X U P n t) {r : D} (hr : r ∈ R) : r = 1 ∨ r = t := by
  rw [hS.eq_zpowers] at hr
  exact eq_one_or_eq_of_mem_zpowers hS.mul_self_t hr

theorem inf_eq_bot (hS : Setup J R X U P n t) : U ⊓ R = ⊥ := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, hUR, -, -⟩⟩ := hS.data
  exact hUR

theorem t_notMem_U (hS : Setup J R X U P n t) : t ∉ U := fun htU => by
  have h1 : t ∈ U ⊓ R := mem_inf.mpr ⟨htU, hS.mem⟩
  rw [hS.inf_eq_bot, mem_bot] at h1
  exact hS.ne_one h1

theorem commute_t (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) : u * t = t * u :=
  mem_centralizer_iff.mp (gms_R_le_centralizer_U hS.data hS.mem) u hu

theorem commute_V (hS : Setup J R X U P n t) {a b : D} (ha : a ∈ U ⊔ R) (hb : b ∈ U ⊔ R) :
    a * b = b * a :=
  gms_comm_V hS.data a ha b hb

theorem mul_self_U (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) : u * u = 1 := by
  rw [← sq]
  exact gms_sq_V hS.data u (mem_sup_left hu)

theorem mem_or_mul_mem [Finite D] (hS : Setup J R X U P n t) {v : D} (hv : v ∈ U ⊔ R) :
    v ∈ U ∨ v * t ∈ U := by
  obtain ⟨u, hu, r, hr, rfl⟩ :=
    SteinbergBT.exists_mul_eq_of_mem_sup (gms_R_le_centralizer_U hS.data) hv
  rcases hS.eq_one_or_eq_t hr with rfl | rfl
  · left
    rwa [mul_one]
  · right
    rwa [mul_assoc, hS.mul_self_t, mul_one]

theorem mul_t_mem_V (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) : u * t ∈ U ⊔ R :=
  mul_mem (mem_sup_left hu) hS.t_mem_V

theorem mul_t_notMem_U (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) : u * t ∉ U := by
  intro hut
  apply hS.t_notMem_U
  have := mul_mem (inv_mem hu) hut
  rwa [inv_mul_cancel_left] at this

theorem mul_t_mul_self (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) :
    u * t * (u * t) = 1 := by
  rw [← sq]
  exact gms_sq_V hS.data _ (hS.mul_t_mem_V hu)

theorem mul_t_ne_one (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) : u * t ≠ 1 := fun h1 =>
  hS.mul_t_notMem_U hu (h1 ▸ one_mem U)

theorem normalizer_V_le [Finite D] (hS : Setup J R X U P n t) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤ normalizer (U : Set D) :=
  (gms_normal_root_partition_and_two_transitivity hS.data hS.three_le).1

theorem conj_t_mul_mem [Finite D] (hS : Setup J R X U P n t) {g : D}
    (hg : g ∈ normalizer ((U ⊔ R : Subgroup D) : Set D)) : g * t * g⁻¹ * t ∈ U := by
  have hgV : g * t * g⁻¹ ∈ U ⊔ R := (mem_normalizer_iff.mp hg t).mp hS.t_mem_V
  rcases hS.mem_or_mul_mem hgV with h1 | h1
  · exfalso
    apply hS.t_notMem_U
    have h2 := (mem_normalizer_iff.mp (inv_mem (hS.normalizer_V_le hg)) _).mp h1
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h2
  · exact h1

theorem zpowers_mul_t_mem [Finite D] (hS : Setup J R X U P n t) {u : D} (hu : u ∈ U) :
    zpowers (u * t) ∈ gmsRootConjugates (U ⊔ R) R := by
  obtain ⟨-, -, -, hpart, -⟩ := gms_normal_root_partition_and_two_transitivity hS.data hS.three_le
  obtain ⟨Q, ⟨hQΔ, hutQ⟩, -⟩ := hpart (u * t) (hS.mul_t_mem_V hu) (hS.mul_t_notMem_U hu)
  have hQcard : Nat.card Q = 2 := (gms_card_of_mem hQΔ).trans hS.card
  have hord : orderOf (u * t) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hS.mul_t_mul_self hu) (hS.mul_t_ne_one hu)
  have heq : zpowers (u * t) = Q :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hutQ) (by rw [hQcard, Nat.card_zpowers, hord])
  rw [heq]
  exact hQΔ

theorem conj_eq_of_action_eq_one [Finite D] (hS : Setup J R X U P n t)
    (l : normalizer ((U ⊔ R : Subgroup D) : Set D))
    (hl : gmsRootConjugateAction (U ⊔ R) R l = 1) :
    ∀ v ∈ U ⊔ R, (l : D) * v * (l : D)⁻¹ = v := by
  have hfix : ∀ Q (hQ : Q ∈ gmsRootConjugates (U ⊔ R) R),
      (l : D) ∈ normalizer (Q : Set D) := by
    intro Q hQ
    rw [← map_conj_eq_self_iff]
    have h1 := congrArg Subtype.val (Equiv.ext_iff.mp hl ⟨Q, hQ⟩)
    rw [gmsRootConjugateAction_apply] at h1
    exact h1
  have hlt : (l : D) * t * (l : D)⁻¹ = t := by
    have hmem : (l : D) * t * (l : D)⁻¹ ∈ R :=
      (mem_normalizer_iff.mp (hfix R gms_R_mem) t).mp hS.mem
    rcases hS.eq_one_or_eq_t hmem with h1 | h1
    · exfalso
      apply hS.ne_one
      calc t = (l : D)⁻¹ * ((l : D) * t * (l : D)⁻¹) * (l : D) := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hlU : ∀ u ∈ U, (l : D) * u * (l : D)⁻¹ = u := by
    intro u hu
    have h1 := conj_eq_of_mem_normalizer_zpowers (hS.mul_t_mul_self hu) (hS.mul_t_ne_one hu)
      (hfix _ (hS.zpowers_mul_t_mem hu))
    calc (l : D) * u * (l : D)⁻¹ =
        ((l : D) * (u * t) * (l : D)⁻¹) * ((l : D) * t * (l : D)⁻¹)⁻¹ := by group
      _ = u := by rw [h1, hlt, hS.inv_t, mul_assoc, hS.mul_self_t, mul_one]
  intro v hv
  rcases hS.mem_or_mul_mem hv with h1 | h1
  · exact hlU v h1
  · have h2 := hlU _ h1
    calc (l : D) * v * (l : D)⁻¹ =
        ((l : D) * (v * t) * (l : D)⁻¹) * ((l : D) * t * (l : D)⁻¹)⁻¹ := by group
      _ = v := by rw [h2, hlt, mul_inv_cancel_right]

theorem conj_mem_tr [Finite D] (hS : Setup J R X U P n t) {g τ : D}
    (hg : g ∈ normalizer ((U ⊔ R : Subgroup D) : Set D))
    (hτ : τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) :
    g * τ * g⁻¹ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) := by
  obtain ⟨hτV, hτU⟩ := mem_inf.mp hτ
  refine mem_inf.mpr ⟨mul_mem (mul_mem hg hτV) (inv_mem hg), mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (mem_normalizer_iff.mp (inv_mem (hS.normalizer_V_le hg)) u).mp hu
    rwa [inv_inv] at this
  have h1 : g⁻¹ * u * g * τ = τ * (g⁻¹ * u * g) := mem_centralizer_iff.mp hτU _ hu'
  calc u * (g * τ * g⁻¹) = g * (g⁻¹ * u * g * τ) * g⁻¹ := by group
    _ = g * (τ * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
    _ = g * τ * g⁻¹ * u := by group

theorem comm_mem [Finite D] (hS : Setup J R X U P n t) {τ : D}
    (hτ : τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) :
    τ * t * τ⁻¹ * t ∈ U :=
  hS.conj_t_mul_mem (mem_inf.mp hτ).1

theorem comm_mul [Finite D] (hS : Setup J R X U P n t) {σ τ : D}
    (hσ : σ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
    (hτ : τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) :
    σ * τ * t * (σ * τ)⁻¹ * t = (σ * t * σ⁻¹ * t) * (τ * t * τ⁻¹ * t) := by
  have hc := hS.comm_mem hτ
  have hc' := hS.comm_mem hσ
  have hσc : (τ * t * τ⁻¹ * t) * σ = σ * (τ * t * τ⁻¹ * t) :=
    mem_centralizer_iff.mp (mem_inf.mp hσ).2 _ hc
  have e1 : σ * τ * t * (σ * τ)⁻¹ * t =
      σ * (τ * t * τ⁻¹ * t) * σ⁻¹ * (σ * (t * t)⁻¹ * σ⁻¹) * (σ * t * σ⁻¹ * t) := by group
  rw [e1, hS.mul_self_t, inv_one, mul_one, mul_inv_cancel, mul_one, ← hσc, mul_inv_cancel_right]
  exact hS.commute_V (mem_sup_left hc) (mem_sup_left hc')

theorem comm_eq_one_iff (hS : Setup J R X U P n t) {τ : D} :
    τ * t * τ⁻¹ * t = 1 ↔ τ * t = t * τ := by
  constructor
  · intro h1
    calc τ * t = (τ * t * τ⁻¹ * t) * (t⁻¹ * τ) := by group
      _ = t * τ := by rw [h1, one_mul, hS.inv_t]
  · intro h1
    rw [h1, mul_inv_cancel_right, hS.mul_self_t]

theorem P_le_normalizer_V (hS : Setup J R X U P n t) :
    P ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hUP, hRP, -, -, -, hVn⟩⟩ := hS.data
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUP hRP)).mp hVn

theorem V_le_P (hS : Setup J R X U P n t) : U ⊔ R ≤ P := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hUP, hRP, -, -, -, -⟩⟩ := hS.data
  exact sup_le hUP hRP

theorem isSylowOf_P (hS : Setup J R X U P n t) : IsSylowOf 2 P (normalizer (R : Set D)) := by
  obtain ⟨-, -, -, -, -, -, ⟨hPN, ⟨TP, hTP⟩, -⟩⟩ := hS.data
  exact ⟨TP, by rw [hTP, subgroupOf_map_subtype, inf_eq_left.mpr hPN]⟩

theorem inf_centralizer_U (hS : Setup J R X U P n t) : P ⊓ centralizer (U : Set D) = U ⊔ R := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, hCPU, -⟩⟩ := hS.data
  exact hCPU

theorem V_le_tr (hS : Setup J R X U P n t) :
    U ⊔ R ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) :=
  le_inf le_normalizer fun _ hv => mem_centralizer_iff.mpr fun _ hu =>
    hS.commute_V (mem_sup_left hu) hv

theorem normalizer_V_le_normalizer_tr [Finite D] (hS : Setup J R X U P n t) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤
      normalizer (((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) :
        Subgroup D)) : Set D) := fun g hg =>
  SteinbergBV.mem_normalizer_of_conj_mem (fun _ hτ => hS.conj_mem_tr hg hτ) fun _ hτ => by
    simpa using hS.conj_mem_tr (inv_mem hg) hτ

theorem exists_tr_conj_eq [Finite D] (hS : Setup J R X U P n t)
    (E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)))
    (hEN : E ≤ (gmsRootConjugateAction (U ⊔ R) R).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal)
    (hreg : ∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
      (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) :
    ∀ u ∈ U, ∃ τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      τ * t * τ⁻¹ = u * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEel := (GMSDichotomy.affine_branch hS.data hS.three_le E hEN hEn hreg).1
  have hE2 : ∀ σ ∈ E, σ ^ 2 = 1 := fun σ hσ => elemPow_eq_one_of_isElementaryAbelian σ hσ
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup D, S = (E.comap (gmsRootConjugateAction (U ⊔ R) R)).map
      (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype := ⟨_, rfl⟩
  have hSmem : ∀ s : D, s ∈ S ↔ ∃ hs : s ∈ normalizer ((U ⊔ R : Subgroup D) : Set D),
      gmsRootConjugateAction (U ⊔ R) R ⟨s, hs⟩ ∈ E := by
    intro s
    rw [hSdef]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.2, hl⟩
    · rintro ⟨hs, hsE⟩
      exact ⟨⟨s, hs⟩, hsE, rfl⟩
  have hSU : S ≤ normalizer (U : Set D) := fun s hs =>
    hS.normalizer_V_le ((hSmem s).mp hs).1
  obtain ⟨hn3, -, -, -, ⟨-, -, -, hUcard⟩, ⟨hcyc, -, hregU⟩, -⟩ := hS.data
  obtain ⟨g₀, -, htr₀⟩ := SteinbergBT.exists_gms_singer_generator hcyc hregU
  have hg₀V : (g₀ : D) ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := gms_NXU_le_L hS.data g₀.2
  have hg₀U : (g₀ : D) ∈ normalizer (U : Set D) := (mem_inf.mp g₀.2).2
  have hconjE : ∀ l m : normalizer ((U ⊔ R : Subgroup D) : Set D),
      gmsRootConjugateAction (U ⊔ R) R l ∈ E →
        gmsRootConjugateAction (U ⊔ R) R (m * l * m⁻¹) ∈ E := by
    intro l m hl
    have h1 := hEn.conj_mem ⟨_, hEN hl⟩ (mem_subgroupOf.mpr hl) ⟨_, m, rfl⟩
    rw [mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hyS : (g₀ : D) ∈ normalizer (S : Set D) := by
    refine SteinbergBV.mem_normalizer_of_conj_mem (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨hsV, hsE⟩ := (hSmem s).mp hs
      refine (hSmem _).mpr ⟨mul_mem (mul_mem hg₀V hsV) (inv_mem hg₀V), ?_⟩
      exact hconjE ⟨s, hsV⟩ ⟨g₀, hg₀V⟩ hsE
    · obtain ⟨hsV, hsE⟩ := (hSmem s).mp hs
      refine (hSmem _).mpr ⟨mul_mem (mul_mem (inv_mem hg₀V) hsV) hg₀V, ?_⟩
      have h1 := hconjE ⟨s, hsV⟩ ⟨g₀, hg₀V⟩⁻¹ hsE
      have h2 : (⟨(g₀ : D)⁻¹ * s * g₀, mul_mem (mul_mem (inv_mem hg₀V) hsV) hg₀V⟩ :
          normalizer ((U ⊔ R : Subgroup D) : Set D)) =
          ⟨g₀, hg₀V⟩⁻¹ * ⟨s, hsV⟩ * (⟨g₀, hg₀V⟩⁻¹)⁻¹ := by
        rw [inv_inv]
        rfl
      rw [h2]
      exact h1
  have htrans : ∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 →
      ∃ k : ℕ, (g₀ : D) ^ k * a * ((g₀ : D) ^ k)⁻¹ = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨j, hj⟩ := htr₀ ⟨a, ha⟩ ⟨b, hb⟩ (fun h1 => ha1 (congrArg Subtype.val h1))
      (fun h1 => hb1 (congrArg Subtype.val h1))
    refine ⟨j, ?_⟩
    have h1 := congrArg Subtype.val hj
    rw [← map_pow, SteinbergBT.gmsConjAct_coe_apply] at h1
    simpa using h1
  have h2 : ∀ s ∈ S, ∃ k : ℕ, ∀ a ∈ U, s ^ 2 ^ k * a * (s ^ 2 ^ k)⁻¹ = a := by
    intro s hs
    obtain ⟨hsV, hsE⟩ := (hSmem s).mp hs
    refine ⟨1, fun a ha => ?_⟩
    have h1 : gmsRootConjugateAction (U ⊔ R) R (⟨s, hsV⟩ ^ 2) = 1 := by
      rw [map_pow]
      exact hE2 _ hsE
    have h3 := hS.conj_eq_of_action_eq_one (⟨s, hsV⟩ ^ 2) h1 a (mem_sup_left ha)
    simpa using h3
  have hU2 : 2 ∣ Nat.card U := by
    rw [hUcard]
    exact dvd_pow_self 2 (by omega)
  have hcomm := commute_of_isPGroup_of_transitive hSU hg₀U hyS htrans h2 hU2
  intro u hu
  obtain ⟨⟨σ, hσE⟩, hσ, -⟩ := hreg ⟨R, gms_R_mem⟩ ⟨zpowers (u * t), hS.zpowers_mul_t_mem hu⟩
  obtain ⟨l, hl⟩ := hEN hσE
  have hlS : (l : D) ∈ S := (hSmem _).mpr ⟨l.2, by
    change gmsRootConjugateAction (U ⊔ R) R l ∈ E
    rw [hl]
    exact hσE⟩
  have hlR : R.map (MulAut.conj (l : D)).toMonoidHom = zpowers (u * t) := by
    have h1 : ((gmsRootConjugateAction (U ⊔ R) R l ⟨R, gms_R_mem⟩ :
        gmsRootConjugates (U ⊔ R) R) : Subgroup D) = zpowers (u * t) := by
      rw [hl]
      exact congrArg Subtype.val hσ
    rwa [gmsRootConjugateAction_apply] at h1
  have hlt : (l : D) * t * (l : D)⁻¹ = u * t := by
    have hmem : (l : D) * t * (l : D)⁻¹ ∈ zpowers (u * t) := by
      rw [← hlR]
      exact ⟨t, hS.mem, by simp [MulAut.conj_apply]⟩
    rcases eq_one_or_eq_of_mem_zpowers (hS.mul_t_mul_self hu) hmem with h1 | h1
    · exfalso
      apply hS.ne_one
      calc t = (l : D)⁻¹ * ((l : D) * t * (l : D)⁻¹) * (l : D) := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  refine ⟨l, mem_inf.mpr ⟨l.2, mem_centralizer_iff.mpr fun a ha => ?_⟩, hlt⟩
  have h1 := hcomm _ hlS a ha
  calc a * (l : D) = (l : D) * a * (l : D)⁻¹ * (l : D) := by rw [h1]
    _ = (l : D) * a := by group

theorem exists_singer [Finite D] (hS : Setup J R X U P n t) :
    ∃ y ∈ X ⊓ normalizer (U : Set D), Odd (orderOf y) ∧
      (∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = b) ∧
      ∀ g ∈ X ⊓ normalizer (U : Set D), ∃ k : ℕ,
        ∀ v ∈ U ⊔ R, g * v * g⁻¹ = y ^ k * v * (y ^ k)⁻¹ := by
  obtain ⟨hn3, -, -, ⟨-, -, hXC⟩, -, ⟨hcyc, hcard, hregU⟩, -⟩ := hS.data
  obtain ⟨g₀, hgen, htr₀⟩ := SteinbergBT.exists_gms_singer_generator hcyc hregU
  have hact : ∀ g, gmsQuotConjAct X U (QuotientGroup.mk g) = gmsConjAct X U g := fun _ => rfl
  have hcoe : ∀ (g : (X ⊓ normalizer (U : Set D) : Subgroup D)) (j : ℕ) (u : U),
      (((gmsConjAct X U g ^ j) u : U) : D) = (g : D) ^ j * u * ((g : D) ^ j)⁻¹ := by
    intro g j u
    rw [← map_pow, SteinbergBT.gmsConjAct_coe_apply]
    simp
  have hq : gmsConjAct X U g₀ ^ (2 ^ n - 1) = 1 := by
    have h1 : (QuotientGroup.mk g₀ : GMSNormalizerQuotient X U) ^ (2 ^ n - 1) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    rw [← hact, ← map_pow, h1, map_one]
  have hg₀m : ∀ w ∈ U, (g₀ : D) ^ (2 ^ n - 1) * w * ((g₀ : D) ^ (2 ^ n - 1))⁻¹ = w := by
    intro w hw
    have h1 := congrArg (fun φ : MulAut U => ((φ ⟨w, hw⟩ : U) : D)) hq
    simp only [hcoe, MulAut.one_apply] at h1
    exact h1
  have hodd : Odd (2 ^ n - 1) := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    exact Nat.odd_iff.mpr (by omega)
  obtain ⟨y, hy, hyodd, hyact⟩ := exists_odd_of_pow_conj_eq (W := U) hodd hg₀m
  have hyX : y ∈ X ⊓ normalizer (U : Set D) := zpowers_le.mpr g₀.2 hy
  have hg₀U : (g₀ : D) ∈ normalizer (U : Set D) := (mem_inf.mp g₀.2).2
  have hyU : y ∈ normalizer (U : Set D) := (mem_inf.mp hyX).2
  have hpowy : ∀ k : ℕ, ∀ u ∈ U, y ^ k * u * (y ^ k)⁻¹ = (g₀ : D) ^ k * u * ((g₀ : D) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      have hku : (g₀ : D) ^ k * u * ((g₀ : D) ^ k)⁻¹ ∈ U :=
        (mem_normalizer_iff.mp (pow_mem hg₀U k) u).mp hu
      calc y ^ (k + 1) * u * (y ^ (k + 1))⁻¹ = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = (g₀ : D) * ((g₀ : D) ^ k * u * ((g₀ : D) ^ k)⁻¹) * (g₀ : D)⁻¹ := by
          rw [ih u hu, hyact _ hku]
        _ = (g₀ : D) ^ (k + 1) * u * ((g₀ : D) ^ (k + 1))⁻¹ := by group
  refine ⟨y, hyX, hyodd, fun a ha b hb ha1 hb1 => ?_, fun g hg => ?_⟩
  · obtain ⟨j, hj⟩ := htr₀ ⟨a, ha⟩ ⟨b, hb⟩ (fun h1 => ha1 (congrArg Subtype.val h1))
      (fun h1 => hb1 (congrArg Subtype.val h1))
    refine ⟨j, ?_⟩
    have h1 := congrArg Subtype.val hj
    rw [hcoe] at h1
    rw [hpowy j a ha]
    exact h1
  · obtain ⟨j, hj⟩ := hgen ⟨g, hg⟩
    refine ⟨j, fun v hv => ?_⟩
    obtain ⟨u, hu, r, hr, rfl⟩ :=
      SteinbergBT.exists_mul_eq_of_mem_sup (gms_R_le_centralizer_U hS.data) hv
    have hgu : g * u * g⁻¹ = (g₀ : D) ^ j * u * ((g₀ : D) ^ j)⁻¹ := by
      have h1 := congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : D)) hj
      simp only [SteinbergBT.gmsConjAct_coe_apply, hcoe] at h1
      exact h1
    have hgr : r * g = g * r := mem_centralizer_iff.mp (hXC (mem_inf.mp hg).1) r hr
    have hyr : r * y ^ j = y ^ j * r :=
      mem_centralizer_iff.mp (pow_mem (hXC (mem_inf.mp hyX).1) j) r hr
    calc g * (u * r) * g⁻¹ = (g * u * g⁻¹) * (g * r * g⁻¹) := by group
      _ = (g * u * g⁻¹) * r := by rw [← hgr, mul_inv_cancel_right]
      _ = (y ^ j * u * (y ^ j)⁻¹) * r := by rw [hgu, hpowy j u hu]
      _ = (y ^ j * u * (y ^ j)⁻¹) * (y ^ j * r * (y ^ j)⁻¹) := by
          rw [← hyr, mul_inv_cancel_right]
      _ = y ^ j * (u * r) * (y ^ j)⁻¹ := by group

end Setup

structure IsV₁ (U R P V₁ : Subgroup D) : Prop where
  sylow : IsSylowOf 2 V₁ (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
  le : U ⊔ R ≤ V₁
  le_normalizer : P ≤ normalizer (V₁ : Set D)

variable {J R X U P : Subgroup D} {n : ℕ} {t : D}

theorem Setup.exists_isV₁ [Finite D] (hS : Setup J R X U P n t) : ∃ V₁, IsV₁ U R P V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tr := normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) with hTr
  have hPV := hS.P_le_normalizer_V
  have hTrN := hS.normalizer_V_le_normalizer_tr
  have hMN : Tr ⊔ P ≤ normalizer (Tr : Set D) := sup_le (inf_le_left.trans hTrN) (hPV.trans hTrN)
  obtain ⟨S₁, hS₁, hPS₁⟩ := exists_isSylowOf_ge (le_sup_right : P ≤ Tr ⊔ P)
    (gms_isPGroup_P hS.data)
  have hV₁ := hS₁.inf_of_le_normalizer (le_sup_left : Tr ≤ Tr ⊔ P) hMN
  refine ⟨S₁ ⊓ Tr, ⟨hV₁, le_inf (hS.V_le_P.trans hPS₁) hS.V_le_tr, fun p hp => ?_⟩⟩
  have hpS₁ : p ∈ normalizer (S₁ : Set D) := Subgroup.le_normalizer (hPS₁ hp)
  have hpTr : p ∈ normalizer (Tr : Set D) := hTrN (hPV hp)
  rw [mem_normalizer_iff] at hpS₁ hpTr ⊢
  intro x
  exact ⟨fun hx => mem_inf.mpr ⟨(hpS₁ x).mp (mem_inf.mp hx).1, (hpTr x).mp (mem_inf.mp hx).2⟩,
    fun hx => mem_inf.mpr ⟨(hpS₁ x).mpr (mem_inf.mp hx).1, (hpTr x).mpr (mem_inf.mp hx).2⟩⟩

namespace IsV₁

variable {V₁ : Subgroup D}

theorem le_tr (hV₁ : IsV₁ U R P V₁) :
    V₁ ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) :=
  hV₁.sylow.le

theorem le_normalizer_V (hV₁ : IsV₁ U R P V₁) :
    V₁ ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
  hV₁.le_tr.trans inf_le_left

theorem commute_U (hV₁ : IsV₁ U R P V₁) {x u : D} (hx : x ∈ V₁) (hu : u ∈ U) :
    u * x = x * u :=
  mem_centralizer_iff.mp (mem_inf.mp (hV₁.le_tr hx)).2 u hu

theorem isPGroup (hV₁ : IsV₁ U R P V₁) : IsPGroup 2 V₁ := hV₁.sylow.isPGroup

theorem mem_V_of_commute [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) {x : D}
    (hx : x ∈ V₁) (hxt : x * t = t * x) : x ∈ U ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, ⟨hPN, -⟩⟩ := hS.data
  set W := V₁ ⊓ normalizer (R : Set D) with hW
  have hxR : x ∈ normalizer (R : Set D) := by
    rw [hS.eq_zpowers]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
    exact ((Commute.zpow_right (show Commute x t from hxt) k).eq).symm
  have hPW : P ≤ normalizer (W : Set D) := by
    intro p hp
    have h1 : p ∈ normalizer (V₁ : Set D) := hV₁.le_normalizer hp
    have h2 : p ∈ normalizer ((normalizer (R : Set D) : Subgroup D) : Set D) :=
      Subgroup.le_normalizer (hPN hp)
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro y
    exact ⟨fun hy => mem_inf.mpr ⟨(h1 y).mp (mem_inf.mp hy).1, (h2 y).mp (mem_inf.mp hy).2⟩,
      fun hy => mem_inf.mpr ⟨(h1 y).mpr (mem_inf.mp hy).1, (h2 y).mpr (mem_inf.mp hy).2⟩⟩
  have hWp : IsPGroup 2 W := hV₁.isPGroup.to_le inf_le_left
  have hp := (gms_isPGroup_P hS.data).to_sup_of_normal_right' hWp hPW
  have heq := hS.isSylowOf_P.eq_of_le (le_sup_left : P ≤ P ⊔ W)
    (sup_le hPN inf_le_right) hp
  have hxP : x ∈ P := heq ▸ (mem_sup_right (mem_inf.mpr ⟨hx, hxR⟩) : x ∈ P ⊔ W)
  rw [← hS.inf_centralizer_U]
  exact mem_inf.mpr ⟨hxP, (mem_inf.mp (hV₁.le_tr hx)).2⟩

theorem exists_conj_eq [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      τ * t * τ⁻¹ = u * t) :
    ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup D, K =
      (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊓
        centralizer ({t} : Set D) := ⟨_, rfl⟩
  have hmemK : ∀ k, k ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) →
      k * t * k⁻¹ * t = 1 → k ∈ K := fun k hk h1 => by
    rw [hKdef]
    exact mem_inf.mpr ⟨hk, mem_centralizer_singleton_iff.mpr (hS.comm_eq_one_iff.mp h1)⟩
  have hKTr : K ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) := by
    rw [hKdef]
    exact inf_le_left
  have hKcomm : ∀ k ∈ K, k * t * k⁻¹ * t = 1 := fun k hk => by
    rw [hKdef] at hk
    exact hS.comm_eq_one_iff.mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp hk).2)
  have hconjK : ∀ τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      ∀ k ∈ K, τ * k * τ⁻¹ ∈ K := by
    intro τ hτ k hk
    have hkT := hKTr hk
    have hmem := mul_mem (mul_mem hτ hkT) (inv_mem hτ)
    refine hmemK _ hmem ?_
    have h1 := hS.comm_mul (mul_mem hτ hkT) (inv_mem hτ)
    have h2 := hS.comm_mul hτ hkT
    have h3 := hS.comm_mul hτ (inv_mem hτ)
    rw [mul_inv_cancel, one_mul, inv_one, mul_one, hS.mul_self_t] at h3
    rw [h1, h2, hKcomm k hk, mul_one, ← h3]
  have hTrK : normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) ≤
      normalizer (K : Set D) := fun τ hτ =>
    SteinbergBV.mem_normalizer_of_conj_mem (hconjK τ hτ) fun k hk => by
      simpa using hconjK τ⁻¹ (inv_mem hτ) k hk
  have hpow : ∀ τ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      ∃ k : ℕ, τ ^ 2 ^ k ∈ K := by
    intro τ hτ
    refine ⟨1, hmemK _ (pow_mem hτ _) ?_⟩
    rw [pow_one, sq, hS.comm_mul hτ hτ]
    exact hS.mul_self_U (hS.comm_mem hτ)
  have hsup := sup_eq_of_isSylowOf hV₁.sylow hKTr hTrK hpow
  intro u hu
  obtain ⟨τ, hτ, hτt⟩ := htr u hu
  have hτ' : τ ∈ V₁ ⊔ K := by
    rw [hsup]
    exact hτ
  obtain ⟨x, hx, k, hk, hxk⟩ := exists_mul_of_mem_sup (hV₁.sylow.le.trans hTrK) hτ'
  refine ⟨x, hx, ?_⟩
  have hkt : k * t * k⁻¹ = t := by
    have h1 := hKcomm k hk
    calc k * t * k⁻¹ = (k * t * k⁻¹ * t) * t⁻¹ := by group
      _ = t := by rw [h1, one_mul, hS.inv_t]
  rw [← hxk] at hτt
  calc x * t * x⁻¹ = x * (k * t * k⁻¹) * x⁻¹ := by rw [hkt]
    _ = x * k * t * (x * k)⁻¹ := by group
    _ = u * t := hτt

theorem isSylowOf_sup [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t) :
    IsSylowOf 2 (V₁ ⊔ P) (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, ⟨hPN, -⟩⟩ := hS.data
  have hle : V₁ ⊔ P ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
    sup_le hV₁.le_normalizer_V hS.P_le_normalizer_V
  have hp : IsPGroup 2 (V₁ ⊔ P : Subgroup D) :=
    hV₁.isPGroup.to_sup_of_normal_left' (gms_isPGroup_P hS.data) hV₁.le_normalizer
  obtain ⟨S, hS', hVS⟩ := exists_isSylowOf_ge hle hp
  have hSle : S ≤ V₁ ⊔ P := by
    intro s hs
    have hsV : s ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := hS'.le hs
    have hc := hS.conj_t_mul_mem hsV
    obtain ⟨x, hx, hxt⟩ := htr _ hc
    have hxs : x⁻¹ * s ∈ normalizer (R : Set D) := by
      rw [hS.eq_zpowers]
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => ?_)
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
      refine ((Commute.zpow_right (show Commute (x⁻¹ * s) t from ?_) k).eq).symm
      have h1 : s * t * s⁻¹ = x * t * x⁻¹ := by
        rw [hxt, mul_assoc _ t t, hS.mul_self_t, mul_one]
      show x⁻¹ * s * t = t * (x⁻¹ * s)
      calc x⁻¹ * s * t = x⁻¹ * (s * t * s⁻¹) * s := by group
        _ = x⁻¹ * (x * t * x⁻¹) * s := by rw [h1]
        _ = t * (x⁻¹ * s) := by group
    have hxsS : x⁻¹ * s ∈ S := mul_mem (inv_mem (hVS (mem_sup_left hx))) hs
    have hW : IsPGroup 2 (S ⊓ normalizer (R : Set D) : Subgroup D) := hS'.isPGroup.to_le inf_le_left
    have heq := hS.isSylowOf_P.eq_of_le (le_inf ((le_sup_right : P ≤ V₁ ⊔ P).trans hVS) hPN)
      inf_le_right hW
    have hxsP : x⁻¹ * s ∈ P := heq ▸ mem_inf.mpr ⟨hxsS, hxs⟩
    have e : s = x * (x⁻¹ * s) := by group
    rw [e]
    exact mul_mem (mem_sup_left hx) (mem_sup_right hxsP)
  rwa [le_antisymm hSle hVS] at hS'

theorem exists_torus [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t) :
    ∃ y ∈ X ⊓ normalizer (U : Set D), Odd (orderOf y) ∧
      (∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = b) ∧
      (∀ g ∈ X ⊓ normalizer (U : Set D), ∃ k : ℕ,
        ∀ v ∈ U ⊔ R, g * v * g⁻¹ = y ^ k * v * (y ^ k)⁻¹) ∧
      ∃ d : D, d ∈ normalizer (V₁ : Set D) ∧ d ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ∧
        d * t = t * d ∧ Odd (orderOf d) ∧ ∀ v ∈ U ⊔ R, d * v * d⁻¹ = y * v * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyX, hyodd, hytr, hygen⟩ := hS.exists_singer
  refine ⟨y, hyX, hyodd, hytr, hygen, ?_⟩
  obtain ⟨-, -, -, ⟨-, -, hXC⟩, -⟩ := hS.data
  set Tr := normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) with hTr
  have hyV : y ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := gms_NXU_le_L hS.data hyX
  have hyt : y * t = t * y := (mem_centralizer_iff.mp (hXC (mem_inf.mp hyX).1) t hS.mem).symm
  have hyU : y ∈ normalizer (U : Set D) := (mem_inf.mp hyX).2
  have hyTr : y ∈ normalizer (Tr : Set D) := hS.normalizer_V_le_normalizer_tr hyV
  obtain ⟨k, hk, hkV₁⟩ := IsSylowOf.exists_map_conj hV₁.sylow (IsSylowOf.map_conj hV₁.sylow hyTr)
  have hkyN : k⁻¹ * y ∈ normalizer (V₁ : Set D) := by
    rw [← map_conj_eq_self_iff, map_conj_mul, hkV₁, ← map_conj_mul, inv_mul_cancel, map_conj_one]
  have hc := hS.comm_mem (inv_mem hk)
  obtain ⟨x, hx, hxt⟩ := htr _ hc
  set m := x⁻¹ * k⁻¹ * y with hm
  have hmV₁ : m ∈ normalizer (V₁ : Set D) := by
    rw [hm, mul_assoc]
    exact mul_mem (inv_mem (Subgroup.le_normalizer hx)) hkyN
  have hmV : m ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
    mul_mem (mul_mem (inv_mem (hV₁.le_normalizer_V hx)) (inv_mem (mem_inf.mp hk).1)) hyV
  have hmt : m * t = t * m := by
    have h1 : k⁻¹ * t * k = x * t * x⁻¹ := by
      rw [hxt, inv_inv, mul_assoc _ t t, hS.mul_self_t, mul_one]
    have h2 : m * t * m⁻¹ = t := by
      calc m * t * m⁻¹ = x⁻¹ * (k⁻¹ * (y * t * y⁻¹) * k) * x := by rw [hm]; group
        _ = x⁻¹ * (k⁻¹ * t * k) * x := by rw [hyt, mul_inv_cancel_right]
        _ = t := by rw [h1]; group
    calc m * t = m * t * m⁻¹ * m := by group
      _ = t * m := by rw [h2]
  have hxk : x⁻¹ * k⁻¹ ∈ centralizer (U : Set D) :=
    mul_mem (inv_mem (mem_inf.mp (hV₁.le_tr hx)).2) (inv_mem (mem_inf.mp hk).2)
  have hmact : ∀ v ∈ U ⊔ R, m * v * m⁻¹ = y * v * y⁻¹ := by
    intro v hv
    obtain ⟨u, hu, r, hr, rfl⟩ :=
      SteinbergBT.exists_mul_eq_of_mem_sup (gms_R_le_centralizer_U hS.data) hv
    have hyu : y * u * y⁻¹ ∈ U := (mem_normalizer_iff.mp hyU u).mp hu
    have hmu : m * u * m⁻¹ = y * u * y⁻¹ := by
      have h1 := mem_centralizer_iff.mp hxk _ hyu
      calc m * u * m⁻¹ = (x⁻¹ * k⁻¹) * (y * u * y⁻¹) * (x⁻¹ * k⁻¹)⁻¹ := by rw [hm]; group
        _ = y * u * y⁻¹ := by rw [← h1, mul_inv_cancel_right]
    have hmr : m * r * m⁻¹ = r := by
      rcases hS.eq_one_or_eq_t hr with h1 | h1
      · rw [h1]
        group
      · rw [h1, hmt, mul_inv_cancel_right]
    have hyr : y * r * y⁻¹ = r := by
      rw [← mem_centralizer_iff.mp (hXC (mem_inf.mp hyX).1) r hr, mul_inv_cancel_right]
    calc m * (u * r) * m⁻¹ = (m * u * m⁻¹) * (m * r * m⁻¹) := by group
      _ = (y * u * y⁻¹) * (y * r * y⁻¹) := by rw [hmu, hmr, hyr]
      _ = y * (u * r) * y⁻¹ := by group
  have hmpow : ∀ j : ℕ, ∀ v ∈ U ⊔ R, m ^ j * v * (m ^ j)⁻¹ = y ^ j * v * (y ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro v _; simp
    | succ j ih =>
      intro v hv
      have hjv : y ^ j * v * (y ^ j)⁻¹ ∈ U ⊔ R := (mem_normalizer_iff.mp (pow_mem hyV j) v).mp hv
      calc m ^ (j + 1) * v * (m ^ (j + 1))⁻¹ = m * (m ^ j * v * (m ^ j)⁻¹) * m⁻¹ := by group
        _ = y * (y ^ j * v * (y ^ j)⁻¹) * y⁻¹ := by rw [ih v hv, hmact _ hjv]
        _ = y ^ (j + 1) * v * (y ^ (j + 1))⁻¹ := by group
  have hmy : ∀ v ∈ U ⊔ R, m ^ orderOf y * v * (m ^ orderOf y)⁻¹ = v := fun v hv => by
    rw [hmpow _ v hv, pow_orderOf_eq_one]
    group
  obtain ⟨d, hd, hdodd, hdact⟩ := exists_odd_of_pow_conj_eq hyodd hmy
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hd
  refine ⟨m ^ j, zpow_mem hmV₁ j, zpow_mem hmV j, (Commute.zpow_left (show Commute m t from hmt) j).eq,
    hdodd, fun v hv => ?_⟩
  rw [hdact v hv, hmact v hv]

end IsV₁

end GMS28

end CFSG.SeitzReduction.RankOne
