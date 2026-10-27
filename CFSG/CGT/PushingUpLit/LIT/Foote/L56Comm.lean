module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_of_le {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) : ⁅A, B⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hA ha) (hB hb)) (H.inv_mem (hA ha)))
      (H.inv_mem (hB hb))

theorem commutator_subgroupOf {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    (⁅A, B⁆).subgroupOf H = ⁅A.subgroupOf H, B.subgroupOf H⁆ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA, inf_eq_left.2 hB,
    inf_eq_left.2 (commutator_le_of_le hA hB)]

theorem commutator_commutator_le_of_rotate {H H₁ H₂ H₃ N : Subgroup G} (h₁ : H₁ ≤ H)
    (h₂ : H₂ ≤ H) (h₃ : H₃ ≤ H) (hN : N ≤ H) (hNn : H ≤ Subgroup.normalizer (N : Set G))
    (hA : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (hB : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hnorm : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).2 hNn
  let π : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' _
  have hker : π.ker = N.subgroupOf H := QuotientGroup.ker_mk' _
  have key : ∀ A B C : Subgroup G, A ≤ H → B ≤ H → C ≤ H → ⁅⁅A, B⁆, C⁆ ≤ N →
      (⁅⁅A.subgroupOf H, B.subgroupOf H⁆, C.subgroupOf H⁆).map π = ⊥ := by
    intro A B C hAH hBH hCH hABC
    rw [← commutator_subgroupOf hAH hBH,
      ← commutator_subgroupOf (commutator_le_of_le hAH hBH) hCH, Subgroup.map_eq_bot_iff, hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hABC hx
  have e : ∀ A B C : Subgroup G, (⁅⁅A.subgroupOf H, B.subgroupOf H⁆, C.subgroupOf H⁆).map π =
      ⁅⁅(A.subgroupOf H).map π, (B.subgroupOf H).map π⁆, (C.subgroupOf H).map π⁆ :=
    fun A B C => by rw [Subgroup.map_commutator, Subgroup.map_commutator]
  have h1 : ⁅⁅(H₂.subgroupOf H).map π, (H₃.subgroupOf H).map π⁆, (H₁.subgroupOf H).map π⁆ = ⊥ := by
    rw [← e]
    exact key _ _ _ h₂ h₃ h₁ hA
  have h2 : ⁅⁅(H₃.subgroupOf H).map π, (H₁.subgroupOf H).map π⁆, (H₂.subgroupOf H).map π⁆ = ⊥ := by
    rw [← e]
    exact key _ _ _ h₃ h₁ h₂ hB
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [← e, Subgroup.map_eq_bot_iff, hker] at h3
  intro x hx
  have hxH : x ∈ H := commutator_le_of_le (commutator_le_of_le h₁ h₂) h₃ hx
  have hx' : (⟨x, hxH⟩ : ↥H) ∈ (⁅⁅H₁, H₂⁆, H₃⁆).subgroupOf H := hx
  rw [commutator_subgroupOf (commutator_le_of_le h₁ h₂) h₃, commutator_subgroupOf h₁ h₂] at hx'
  exact Subgroup.mem_subgroupOf.1 (h3 hx')

theorem exists_div_apply_of_prod_eq_one {V : Type*} [CommGroup V] (α : V →* V) {m : ℕ}
    (hm : Odd m) (hexp : ∀ v : V, v * v = 1) {d : V}
    (hd : ∏ i ∈ Finset.range m, (α^[i]) d = 1) : ∃ w : V, w * (α w)⁻¹ = d := by
  set a : ℕ → V := fun i => (α^[i]) d with ha
  let γ : V →* V := MonoidHom.mk' (fun w => w * (α w)⁻¹) (fun x y => by
    simp only [map_mul, mul_inv]
    ac_rfl)
  have htel : ∀ i, d * (a i)⁻¹ = γ (∏ j ∈ Finset.range i, a j) := by
    intro i
    induction i with
    | zero => simp [ha, γ]
    | succ i ih =>
      rw [Finset.prod_range_succ, map_mul, ← ih]
      have h1 : a (i + 1) = α (a i) := by simp [ha, Function.iterate_succ_apply']
      show d * (a (i + 1))⁻¹ = d * (a i)⁻¹ * (a i * (α (a i))⁻¹)
      rw [h1]
      group
  have hdm : d ^ m = d := by
    obtain ⟨k, rfl⟩ := hm
    have hd2 : d ^ 2 = 1 := by rw [pow_two]; exact hexp d
    rw [pow_succ, pow_mul, hd2, one_pow, one_mul]
  have h1 : ∏ i ∈ Finset.range m, (d * (a i)⁻¹) = d := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const, Finset.card_range,
      hdm]
    have : ∏ i ∈ Finset.range m, a i = 1 := hd
    rw [this, inv_one, mul_one]
  refine ⟨∏ i ∈ Finset.range m, ∏ j ∈ Finset.range i, a j, ?_⟩
  calc (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range i, a j) *
        (α (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range i, a j))⁻¹
      = γ (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range i, a j) := rfl
    _ = ∏ i ∈ Finset.range m, γ (∏ j ∈ Finset.range i, a j) := map_prod γ _ _
    _ = ∏ i ∈ Finset.range m, (d * (a i)⁻¹) := Finset.prod_congr rfl fun i _ => (htel i).symm
    _ = d := h1

theorem exists_comm_eq_of_pow_eq_one {V : Subgroup G} {x d : G} {m : ℕ} (hm : Odd m)
    (hx : x ^ m = 1) (hdx : (d * x) ^ m = 1) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hVs : ∀ a ∈ V, a * a = 1) (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hdV : d ∈ V) :
    ∃ w ∈ V, w * x * w⁻¹ * x⁻¹ = d := by
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  let α : ↥V →* ↥V := MonoidHom.mk' (fun v => ⟨x * v * x⁻¹, hxV v v.2⟩) (fun a b => by
    apply Subtype.ext
    show x * ((a : G) * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
    group)
  have hαi : ∀ (i : ℕ) (v : ↥V), (((α^[i]) v : ↥V) : G) = x ^ i * v * (x ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [Function.iterate_succ_apply']
      show x * (((α^[i]) v : ↥V) : G) * x⁻¹ = x ^ (i + 1) * v * (x ^ (i + 1))⁻¹
      rw [ih, pow_succ', mul_inv_rev]
      simp only [mul_assoc]
  let d' : ↥V := ⟨d, hdV⟩
  have hd'c : (d' : G) = d := rfl
  have hprod : ∀ k : ℕ, ((∏ i ∈ Finset.range k, (α^[i]) d' : ↥V) : G) * x ^ k = (d * x) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Subgroup.coe_mul, pow_succ x k, pow_succ (d * x) k, ← ih, hαi,
        hd'c]
      group
  have hP : (∏ i ∈ Finset.range m, (α^[i]) d' : ↥V) = 1 := by
    apply Subtype.ext
    have h := hprod m
    rw [hdx, hx, mul_one] at h
    simpa using h
  obtain ⟨w, hw⟩ := exists_div_apply_of_prod_eq_one α hm
    (fun v => Subtype.ext (hVs v v.2)) hP
  refine ⟨w, w.2, ?_⟩
  have hw' : (w : G) * (x * w * x⁻¹)⁻¹ = d := congrArg Subtype.val hw
  calc (w : G) * x * (w : G)⁻¹ * x⁻¹ = (w : G) * (x * w * x⁻¹)⁻¹ := by group
    _ = d := hw'

theorem commutator_mul_left_of_commute {t t' x : G} (h1 : t * ⁅t', x⁆ = ⁅t', x⁆ * t)
    (h2 : ⁅t', x⁆ * ⁅t, x⁆ = ⁅t, x⁆ * ⁅t', x⁆) : ⁅t * t', x⁆ = ⁅t, x⁆ * ⁅t', x⁆ := by
  calc ⁅t * t', x⁆ = t * ⁅t', x⁆ * t⁻¹ * ⁅t, x⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅t', x⁆ * ⁅t, x⁆ := by rw [h1]; group
    _ = ⁅t, x⁆ * ⁅t', x⁆ := h2

variable [Finite G]

theorem exists_centralizes_of_card {T V : Subgroup G} {x : G} {m : ℕ} (hm : Odd m)
    (hx : x ^ m = 1) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVs : ∀ a ∈ V, a * a = 1)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hTV : ∀ t ∈ T, ∀ v ∈ V, t * v = v * t)
    (hTx : ∀ t ∈ T, ⁅t, x⁆ ∈ V) (hC : ∃ c ∈ V, c ≠ 1 ∧ c * x = x * c)
    (hcard : Nat.card V ≤ Nat.card T) : ∃ t ∈ T, t ≠ 1 ∧ t * x = x * t := by
  by_contra hcon
  push Not at hcon
  have hVx : ∀ v ∈ V, ⁅v, x⁆ ∈ V := fun v hv => by
    have : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact V.mul_mem hv (hxV v⁻¹ (V.inv_mem hv))
  let β : ↥T →* ↥V := MonoidHom.mk' (fun t => ⟨⁅(t : G), x⁆, hTx t t.2⟩) (fun t t' => by
    apply Subtype.ext
    show ⁅(t : G) * t', x⁆ = ⁅(t : G), x⁆ * ⁅(t' : G), x⁆
    exact commutator_mul_left_of_commute (hTV t t.2 _ (hTx t' t'.2))
      (hVc _ (hTx t' t'.2) _ (hTx t t.2)))
  let γ : ↥V →* ↥V := MonoidHom.mk' (fun v => ⟨⁅(v : G), x⁆, hVx v v.2⟩) (fun v v' => by
    apply Subtype.ext
    show ⁅(v : G) * v', x⁆ = ⁅(v : G), x⁆ * ⁅(v' : G), x⁆
    exact commutator_mul_left_of_commute (hVc _ v.2 _ (hVx v' v'.2))
      (hVc _ (hVx v' v'.2) _ (hVx v v.2)))
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro t ht
    by_contra ht1
    have ht' : (⟨⁅(t : G), x⁆, hTx t t.2⟩ : ↥V) = 1 := ht
    have h1 : ⁅(t : G), x⁆ = 1 := congrArg Subtype.val ht'
    exact hcon t t.2 (fun h => ht1 (Subtype.ext h)) (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hrange : β.range ≤ γ.range := by
    rintro _ ⟨t, rfl⟩
    have hdx : (⁅(t : G), x⁆ * x) ^ m = 1 := by
      have e : ⁅(t : G), x⁆ * x = (t : G) * x * (t : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, conj_pow, hx]
      group
    obtain ⟨w, hwV, hw⟩ := exists_comm_eq_of_pow_eq_one hm hx hdx hVc hVs hxV (hTx t t.2)
    refine ⟨⟨w, hwV⟩, Subtype.ext ?_⟩
    show ⁅w, x⁆ = ⁅(t : G), x⁆
    rw [← hw, commutatorElement_def]
  have h1 : Nat.card ↥T = Nat.card β.range := Nat.card_congr (MonoidHom.ofInjective hβinj).toEquiv
  have h2 : Nat.card β.range ≤ Nat.card γ.range := Subgroup.card_le_of_le hrange
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup γ.ker
  have h4 : Nat.card (↥V ⧸ γ.ker) = Nat.card γ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange γ).toEquiv
  have h5 : 2 ≤ Nat.card γ.ker := by
    obtain ⟨c, hcV, hc1, hcx⟩ := hC
    have hne : γ.ker ≠ ⊥ := by
      intro hbot
      have hmem : (⟨c, hcV⟩ : ↥V) ∈ γ.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        show ⁅c, x⁆ = 1
        exact commutatorElement_eq_one_iff_mul_comm.2 hcx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hc1 (congrArg Subtype.val hmem)
    have := (Subgroup.one_lt_card_iff_ne_bot γ.ker).2 hne
    omega
  have hq : 0 < Nat.card γ.range := Nat.card_pos
  have key : Nat.card ↥V = Nat.card γ.range * Nat.card γ.ker := by rw [h3, h4]
  have h6 : Nat.card γ.range * 2 ≤ Nat.card ↥V := by
    rw [key]
    exact Nat.mul_le_mul_left _ h5
  omega

namespace QBlock

variable {K : Subgroup G}

theorem le_closure_odd (h : QBlock K) : K ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} := by
  set S : Set G := {x | x ∈ K ∧ Odd (orderOf x)} with hS
  have hconj : ∀ g ∈ K, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    rintro g hg x ⟨hxK, hxo⟩
    refine ⟨K.mul_mem (K.mul_mem hg hxK) (K.inv_mem hg), ?_⟩
    have := (MulAut.conj g).orderOf_eq x
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hxo
  refine noTwoQuot_of_short h.short (Subgroup.closure S) ?_ ?_
  · intro g hg n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hconj g hg x hx)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  · intro g hg
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have hdvd : 2 ^ a ∣ orderOf g := ⟨m, hord⟩
    have hord' : orderOf (g ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num)) hdvd, hord]
      exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) a)
    exact ⟨a, Subgroup.subset_closure ⟨K.pow_mem hg _, by rw [hord']; exact hm⟩⟩

end QBlock

end CFSG.CGT.PushingUpLit.LIT.Foote
