module

public import CFSG.ClassicalInvolution.AschTight.TzConj

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem pow_half_mul_self {a : G} (ha : Even (orderOf a)) :
    a ^ (orderOf a / 2) * a ^ (orderOf a / 2) = 1 := by
  rw [← pow_add, ← two_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp ha), pow_orderOf_eq_one]

theorem pow_half_ne_one {a : G} (ha : 2 ≤ orderOf a) : a ^ (orderOf a / 2) ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by omega) (by omega)

theorem eq_one_or_eq_of_mem_zpowers {a c : G} (ha : Even (orderOf a)) (ha2 : 2 ≤ orderOf a)
    (hc : c ∈ Subgroup.zpowers a) (hc2 : c * c = 1) :
    c = 1 ∨ c = a ^ (orderOf a / 2) := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h := zpow_eq_zpow_of_mul_self_eq_one (i := i) (j := ((orderOf a / 2 : ℕ) : ℤ)) hc2
    (by rw [zpow_natCast]; exact pow_half_mul_self ha) hc1
    (by rw [zpow_natCast]; exact pow_half_ne_one ha2)
  rwa [zpow_natCast] at h

theorem eq_zpowers_of_generator {C : Subgroup G} {a : C} (ha : ∀ x : C, x ∈ Subgroup.zpowers a) :
    C = Subgroup.zpowers (a : G) := by
  refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr a.2)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (ha ⟨x, hx⟩)
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  have := congrArg Subtype.val hi
  simpa using this

theorem mem_zpowers_of_isPGroup {V : Subgroup G} (hV2 : IsPGroup 2 V) {t : G}
    (hunique : ∀ y ∈ V, y * y = 1 → y = 1 ∨ y = t) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    t ∈ Subgroup.zpowers v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨v, hv⟩
  have hk' : orderOf v = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk'
    exact hv1 hk'
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 : v ^ (2 ^ (k - 1)) * v ^ (2 ^ (k - 1)) = 1 := by
    rw [← pow_add, ← two_mul, ← hpow, ← hk', pow_orderOf_eq_one]
  have h2 : v ^ (2 ^ (k - 1)) ≠ 1 := by
    have h3 := Nat.one_le_two_pow (n := k - 1)
    exact pow_ne_one_of_lt_orderOf (by positivity) (by rw [hk', hpow]; omega)
  rcases hunique _ (V.pow_mem hv _) h1 with h | h
  · exact absurd h h2
  · rw [← h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _


@[expose] def twistHom {W V C : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hVW : V ≤ W) {p : G} (hpN : p ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ w ∈ W, p * w * p⁻¹ * w⁻¹ ∈ C) : V →* C where
  toFun v := ⟨(v : G)⁻¹ * (p * v * p⁻¹), by
    have hvW := hVW v.2
    have hpv : p * v * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hpN v).mp hvW
    rw [← hWab _ hpv _ (W.inv_mem hvW)]
    exact hcomm v hvW⟩
  map_one' := by ext; simp
  map_mul' v v' := by
    ext
    have hvW := hVW v.2
    have hv'W := hVW v'.2
    have hpv : p * v * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hpN v).mp hvW
    have h1 : (v' : G)⁻¹ * ((v : G)⁻¹ * (p * v * p⁻¹)) =
        ((v : G)⁻¹ * (p * v * p⁻¹)) * (v' : G)⁻¹ :=
      hWab _ (W.inv_mem hv'W) _ (W.mul_mem (W.inv_mem hvW) hpv)
    simp only [Subgroup.coe_mul, mul_inv_rev]
    calc (v' : G)⁻¹ * (v : G)⁻¹ * (p * (v * v') * p⁻¹) =
        ((v' : G)⁻¹ * ((v : G)⁻¹ * (p * v * p⁻¹))) * (p * v' * p⁻¹) := by group
      _ = ((v : G)⁻¹ * (p * v * p⁻¹)) * (v' : G)⁻¹ * (p * v' * p⁻¹) := by rw [h1]
      _ = (v : G)⁻¹ * (p * v * p⁻¹) * ((v' : G)⁻¹ * (p * v' * p⁻¹)) := by group

theorem twistHom_apply {W V C : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hVW : V ≤ W) {p : G} (hpN : p ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ w ∈ W, p * w * p⁻¹ * w⁻¹ ∈ C) (v : V) :
    (twistHom hWab hVW hpN hcomm v : G) = (v : G)⁻¹ * (p * v * p⁻¹) := rfl

theorem exists_swap_of_not_le [Finite G] {W V C P : Subgroup G} {t : G}
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hVW : V ≤ W) (hCW : C ≤ W)
    (hCcyc : IsCyclic C) (hVcyc : IsCyclic V) (hcard : Nat.card V = Nat.card C)
    (h4 : 4 ≤ Nat.card C) (hC2 : IsPGroup 2 C) (hV2 : IsPGroup 2 V)
    (htV : t ∈ V) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hCP : C ≤ P) (hPN : P ≤ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ C)
    (hstar : ∀ x ∈ P, x * t = t * x → x ∈ C) (hPC : ¬ P ≤ C) :
    ∃ p ∈ P, p ∉ C ∧ ∃ zc ∈ C, zc ≠ 1 ∧ zc * zc = 1 ∧ (∀ c ∈ C, c * c = 1 → c = 1 ∨ c = zc) ∧
      p * t * p⁻¹ = zc * t ∧ (∀ c ∈ C, p * c * p⁻¹ = c⁻¹) ∧ p * p ∈ C ∧
      (p * p = 1 ∨ p * p = zc) ∧ (∀ x ∈ P, x ∉ C → p⁻¹ * x ∈ C) ∧
      Nat.card P = 2 * Nat.card C ∧ ∀ c ∈ C, ∃ v ∈ V, (v : G)⁻¹ * (p * v * p⁻¹) = c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a₀, ha₀⟩ := hCcyc.exists_generator
  have hCa : C = Subgroup.zpowers (a₀ : G) := eq_zpowers_of_generator ha₀
  have hao : orderOf (a₀ : G) = Nat.card C := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ha₀]
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hae : Even (orderOf (a₀ : G)) := by
    rw [hao, hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk, pow_zero] at h4
      omega
    exact Nat.even_pow.mpr ⟨even_two, hk0⟩
  have ha2 : 2 ≤ orderOf (a₀ : G) := by omega
  set zc : G := (a₀ : G) ^ (orderOf (a₀ : G) / 2) with hzc
  have hzc2 : zc * zc = 1 := pow_half_mul_self hae
  have hzc1 : zc ≠ 1 := pow_half_ne_one ha2
  have hzcC : zc ∈ C := hCa ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hinvC : ∀ c ∈ C, c * c = 1 → c = 1 ∨ c = zc := fun c hc hc2 =>
    eq_one_or_eq_of_mem_zpowers hae ha2 (hCa ▸ hc) hc2
  obtain ⟨v₀, hv₀⟩ := hVcyc.exists_generator
  have hVv : V = Subgroup.zpowers (v₀ : G) := eq_zpowers_of_generator hv₀
  have hinvV : ∀ y ∈ V, y * y = 1 → y = 1 ∨ y = t := by
    intro y hy hy2
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    right
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hVv ▸ hy)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hVv ▸ htV)
    rw [← hj] at ht2 ht1 ⊢
    exact zpow_eq_zpow_of_mul_self_eq_one hy2 ht2 hy1 ht1
  have htW : t ∈ W := hVW htV
  have hmove : ∀ x ∈ P, x * t * x⁻¹ = t ∨ x * t * x⁻¹ = zc * t := by
    intro x hx
    have hcC : x * t * x⁻¹ * t⁻¹ ∈ C := hcomm x hx t htW
    have hcW := hCW hcC
    have hct : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
    have hc2 : (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) = 1 := by
      have h1 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
        calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      have h3 := hWab _ hcW t htW
      rw [hct] at h1
      calc (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) =
          (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) * (t * t) := by rw [ht2, mul_one]
        _ = (x * t * x⁻¹ * t⁻¹) * ((x * t * x⁻¹ * t⁻¹) * t) * t := by group
        _ = (x * t * x⁻¹ * t⁻¹) * (t * (x * t * x⁻¹ * t⁻¹)) * t := by rw [h3]
        _ = ((x * t * x⁻¹ * t⁻¹) * t) * ((x * t * x⁻¹ * t⁻¹) * t) := by group
        _ = 1 := h1
    rcases hinvC _ hcC hc2 with h | h
    · left
      rw [hct, h, one_mul]
    · right
      rw [hct, h]
  obtain ⟨p, hpP, hpC⟩ := Set.not_subset.mp hPC
  have hpN := hPN hpP
  have hfix : ∀ x ∈ P, x * t * x⁻¹ = t → x ∈ C := fun x hx h => hstar x hx (by
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h])
  have hpt : p * t * p⁻¹ = zc * t :=
    (hmove p hpP).resolve_left fun h => hpC (hfix p hpP h)
  have hnC : ∀ x ∈ P, ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx c hc
    have e : x * c * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact C.mul_mem (hcomm x hx c (hCW hc)) hc
  have hzcfix : ∀ x ∈ P, x * zc * x⁻¹ = zc := by
    intro x hx
    have h2 : (x * zc * x⁻¹) * (x * zc * x⁻¹) = 1 := by
      calc (x * zc * x⁻¹) * (x * zc * x⁻¹) = x * (zc * zc) * x⁻¹ := by group
        _ = 1 := by rw [hzc2]; group
    refine (hinvC _ (hnC x hx zc hzcC) h2).resolve_left fun h => hzc1 ?_
    calc zc = x⁻¹ * (x * zc * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hcoset : ∀ x ∈ P, x ∉ C → p⁻¹ * x ∈ C := by
    intro x hx hxC
    have hxt : x * t * x⁻¹ = zc * t := (hmove x hx).resolve_left fun h => hxC (hfix x hx h)
    refine hfix _ (P.mul_mem (P.inv_mem hpP) hx) ?_
    calc (p⁻¹ * x) * t * (p⁻¹ * x)⁻¹ = p⁻¹ * (x * t * x⁻¹) * p := by group
      _ = p⁻¹ * (p * t * p⁻¹) * p := by rw [hxt, hpt]
      _ = t := by group
  have hp2C : p * p ∈ C := by
    refine hfix _ (P.mul_mem hpP hpP) ?_
    calc p * p * t * (p * p)⁻¹ = p * (p * t * p⁻¹) * p⁻¹ := by group
      _ = p * (zc * t) * p⁻¹ := by rw [hpt]
      _ = (p * zc * p⁻¹) * (p * t * p⁻¹) := by group
      _ = zc * (zc * t) := by rw [hzcfix p hpP, hpt]
      _ = t := by rw [← mul_assoc, hzc2, one_mul]
  set γ := twistHom hWab hVW hpN (hcomm p hpP) with hγ
  have hγt : (γ ⟨t, htV⟩ : G) = zc := by
    rw [twistHom_apply]
    show t⁻¹ * (p * t * p⁻¹) = zc
    rw [hpt]
    have := hWab zc (hCW hzcC) t htW
    calc t⁻¹ * (zc * t) = t⁻¹ * (t * zc) := by rw [this]
      _ = zc := by group
  have hγinj : Function.Injective γ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    by_contra hv1
    have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have htv := mem_zpowers_of_isPGroup hV2 hinvV v.2 hv1'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp htv
    have hti : (⟨t, htV⟩ : V) = v ^ i := Subtype.ext (by
      show t = ((v ^ i : V) : G)
      rw [Subgroup.coe_zpow]
      exact hi.symm)
    have h1 : γ ⟨t, htV⟩ = 1 := by
      rw [hti, map_zpow, MonoidHom.mem_ker.mp hv, one_zpow]
    apply hzc1
    rw [← hγt, h1]
    rfl
  have hγsurj : Function.Surjective γ :=
    (hγinj.bijective_of_nat_card_le hcard.symm.le).2
  have hpinv : ∀ c ∈ C, p * c * p⁻¹ = c⁻¹ := by
    intro c hc
    obtain ⟨v, hv⟩ := hγsurj ⟨c, hc⟩
    have hvc : (v : G)⁻¹ * (p * v * p⁻¹) = c := by
      have := congrArg Subtype.val hv
      rwa [twistHom_apply] at this
    have hpv : p * v * p⁻¹ = v * c := by rw [← hvc]; group
    have hvW := hVW v.2
    have hp2v : (p * p) * v * (p * p)⁻¹ = v := by
      rw [hWab _ (hCW hp2C) _ hvW]
      group
    have h1 : (p * p) * v * (p * p)⁻¹ = v * c * (p * c * p⁻¹) := by
      calc (p * p) * v * (p * p)⁻¹ = p * (p * v * p⁻¹) * p⁻¹ := by group
        _ = p * (v * c) * p⁻¹ := by rw [hpv]
        _ = (p * v * p⁻¹) * (p * c * p⁻¹) := by group
        _ = v * c * (p * c * p⁻¹) := by rw [hpv]
    rw [hp2v] at h1
    calc p * c * p⁻¹ = (v * c)⁻¹ * (v * c * (p * c * p⁻¹)) := by group
      _ = (v * c)⁻¹ * v := by rw [← h1]
      _ = c⁻¹ := by group
  have hp2 : p * p = 1 ∨ p * p = zc := by
    refine hinvC _ hp2C ?_
    have h1 := hpinv _ hp2C
    have h2 : p * (p * p) * p⁻¹ = p * p := by group
    rw [h2] at h1
    calc p * p * (p * p) = p * p * (p * p)⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel _
  have hidx : (C.subgroupOf P).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨p, hpP⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ C
    · refine Or.inr ⟨hb, fun hbp => hpC ?_⟩
      have e : p = (b : G)⁻¹ * (b * p) := by group
      rw [e]
      exact C.mul_mem (C.inv_mem hb) hbp
    · refine Or.inl ⟨?_, hb⟩
      have h1 := hcoset b b.2 hb
      have e : (b : G) * p = p * (p⁻¹ * b) * p⁻¹ * (p * p) := by group
      rw [e]
      exact C.mul_mem (hnC p hpP _ h1) hp2C
  have hcardP : Nat.card P = 2 * orderOf (a₀ : G) := by
    rw [hao, ← Subgroup.card_mul_index (C.subgroupOf P), hidx, mul_comm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv]
  refine ⟨p, hpP, hpC, zc, hzcC, hzc1, hzc2, hinvC, hpt, hpinv, hp2C, hp2, hcoset, ?_, ?_⟩
  · rw [hcardP, hao]
  · intro c hc
    obtain ⟨v, hv⟩ := hγsurj ⟨c, hc⟩
    refine ⟨v, v.2, ?_⟩
    have := congrArg Subtype.val hv
    rwa [twistHom_apply] at this

theorem isQuaternionSub_of_swap [Finite G] {C P : Subgroup G} {p zc : G} (hCcyc : IsCyclic C)
    (h4 : 4 ≤ Nat.card C) (hC2 : IsPGroup 2 C) (hCP : C ≤ P) (hpP : p ∈ P) (hzcC : zc ∈ C)
    (hzc1 : zc ≠ 1) (hzc2 : zc * zc = 1) (hpinv : ∀ c ∈ C, p * c * p⁻¹ = c⁻¹)
    (hcoset : ∀ x ∈ P, x ∉ C → p⁻¹ * x ∈ C) (hcardP : Nat.card P = 2 * Nat.card C) :
    (p * p = zc → IsQuaternionSub P) ∧
      (p * p = 1 → ∃ a b : G, 4 ≤ orderOf a ∧ Nat.card P = 2 * orderOf a ∧
        b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧ Subgroup.closure {a, b} = P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a₀, ha₀⟩ := hCcyc.exists_generator
  have hCa : C = Subgroup.zpowers (a₀ : G) := eq_zpowers_of_generator ha₀
  have hao : orderOf (a₀ : G) = Nat.card C := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ha₀]
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hae : Even (orderOf (a₀ : G)) := by
    rw [hao, hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk, pow_zero] at h4
      omega
    exact Nat.even_pow.mpr ⟨even_two, hk0⟩
  have ha2 : 2 ≤ orderOf (a₀ : G) := by omega
  have hzc' : zc = (a₀ : G) ^ (orderOf (a₀ : G) / 2) :=
    (eq_one_or_eq_of_mem_zpowers hae ha2 (hCa ▸ hzcC) hzc2).resolve_left hzc1
  have hcl : Subgroup.closure {(a₀ : G), p} = P := by
    refine le_antisymm ((Subgroup.closure_le P).mpr ?_) fun x hx => ?_
    · rintro y (rfl | rfl)
      · exact hCP a₀.2
      · exact hpP
    · have ha : Subgroup.zpowers (a₀ : G) ≤ Subgroup.closure {(a₀ : G), p} :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
      have hpcl : p ∈ Subgroup.closure {(a₀ : G), p} :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      by_cases hxC : x ∈ C
      · exact ha (hCa ▸ hxC)
      · have h1 := hcoset x hx hxC
        have e : x = p * (p⁻¹ * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ hpcl (ha (hCa ▸ h1))
  have hpa : p * (a₀ : G) * p⁻¹ = (a₀ : G)⁻¹ := hpinv _ a₀.2
  have hcardP' : Nat.card P = 2 * orderOf (a₀ : G) := by rw [hcardP, hao]
  exact ⟨fun h => ⟨a₀, p, by omega, hcardP', h.trans hzc', hpa, hcl⟩,
    fun h => ⟨a₀, p, by omega, hcardP', h, hpa, hcl⟩⟩

theorem eq_or_isQuaternionSub_or_isDihedralSub [Finite G] {W V C P : Subgroup G} {t : G}
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hVW : V ≤ W) (hCW : C ≤ W)
    (hCcyc : IsCyclic C) (hVcyc : IsCyclic V) (hcard : Nat.card V = Nat.card C)
    (h4 : 4 ≤ Nat.card C) (hC2 : IsPGroup 2 C) (hV2 : IsPGroup 2 V)
    (htV : t ∈ V) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hCP : C ≤ P) (hPN : P ≤ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ C)
    (hstar : ∀ x ∈ P, x * t = t * x → x ∈ C) :
    P = C ∨ IsQuaternionSub P ∨ ∃ a b : G, 4 ≤ orderOf a ∧ Nat.card P = 2 * orderOf a ∧
      b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧ Subgroup.closure {a, b} = P := by
  classical
  by_cases hPC : P ≤ C
  · exact Or.inl (le_antisymm hPC hCP)
  obtain ⟨p, hpP, hpC, zc, hzcC, hzc1, hzc2, -, -, hpinv, -, hp2, hcoset, hcardP, -⟩ :=
    exists_swap_of_not_le hWab hVW hCW hCcyc hVcyc hcard h4 hC2 hV2 htV ht1 ht2 hCP hPN hcomm
      hstar hPC
  have hpk := isQuaternionSub_of_swap hCcyc h4 hC2 hCP hpP hzcC hzc1 hzc2 hpinv hcoset hcardP
  rcases hp2 with h | h
  · exact Or.inr (Or.inr (hpk.2 h))
  · exact Or.inr (Or.inl (hpk.1 h))

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
