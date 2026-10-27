module

public import CFSG.GH74.E2.Q8OuterAut
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.E2.Local
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.E2

open Subgroup Pointwise



theorem inn_index_two {K : Type} [Group K] [Finite K] (hcen : Subgroup.center K = ⊥)
    (hOut2 : Nat.card (MulAut K) = 2 * Nat.card K) :
    (MulAut.conj : K →* MulAut K).range.index = 2 := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut K => σ g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * x = (x * g * x⁻¹) * x := by rw [this]
        _ = x * g := by group
    rw [hcen] at this
    exact this
  have hcard : Nat.card (MulAut.conj : K →* MulAut K).range = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h1 := Subgroup.index_mul_card (MulAut.conj : K →* MulAut K).range
  rw [hcard, hOut2] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])

theorem conjNormal_surjective {C : Type} [Group C] [Finite C] {K : Subgroup C} [K.Normal]
    (hcen : Subgroup.center ↥K = ⊥) (hOut2 : Nat.card (MulAut ↥K) = 2 * Nat.card ↥K) {u : C}
    (hu : ¬ ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹) :
    Function.Surjective (MulAut.conjNormal : C →* MulAut ↥K) := by
  classical
  have hidx := inn_index_two hcen hOut2
  set Inn : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range with hInn
  set R : Subgroup (MulAut ↥K) := (MulAut.conjNormal : C →* MulAut ↥K).range with hR
  have hInnR : Inn ≤ R := by
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : C), by rw [MulAut.conjNormal_val]⟩
  have huR : (MulAut.conjNormal u : MulAut ↥K) ∈ R := ⟨u, rfl⟩
  have huInn : (MulAut.conjNormal u : MulAut ↥K) ∉ Inn := by
    rintro ⟨k, hk⟩
    apply hu
    refine ⟨(k : C), k.2, fun x hx => ?_⟩
    have := congrArg (fun σ : MulAut ↥K => (σ ⟨x, hx⟩ : C)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at this
    exact this.symm
  have h1 : Inn.relIndex R * R.index = Inn.index := Subgroup.relIndex_mul_index hInnR
  rw [hidx] at h1
  have hRidx : R.index = 1 := by
    have hd : R.index ∣ 2 := ⟨Inn.relIndex R, by rw [← h1, mul_comm]⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact h
    · exfalso
      rw [h] at h1
      have : Inn.relIndex R = 1 := by omega
      rw [Subgroup.relIndex_eq_one] at this
      exact huInn (this huR)
  have hRtop : R = ⊤ := Subgroup.index_eq_one.1 hRidx
  exact MonoidHom.range_eq_top.1 hRtop

theorem zpowers_involution {X : Type*} [Group X] {x : X} (hx2 : x * x = 1) :
    ∀ y ∈ Subgroup.zpowers x, y = 1 ∨ y = x := by
  intro y hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 2 * k ∨ m = 2 * k + 1 := by
    rcases Int.even_or_odd' m with ⟨k, hk | hk⟩
    · exact ⟨k, Or.inl hk⟩
    · exact ⟨k, Or.inr hk⟩
  rcases hk with hk | hk
  · left
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem card_sup_zpowers_of_normal {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    {x : X} (hx2 : x * x = 1) (hxN : x ∉ N) :
    Nat.card ↥(N ⊔ Subgroup.zpowers x) = 2 * Nat.card ↥N := by
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ N.one_mem)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hzp := zpowers_involution hx2
  have hinf : N ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyN, hyZ⟩
    rcases hzp y hyZ with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hyN) hxN
  have h1 : N.relIndex (N ⊔ Subgroup.zpowers x) = N.relIndex (Subgroup.zpowers x) :=
    Subgroup.relIndex_sup_left (Subgroup.zpowers x) N
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := Subgroup.zpowers x)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hxo, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card (H := N) (K := N ⊔ Subgroup.zpowers x)
  rw [inf_eq_left.2 le_sup_left, h1, h2] at h3
  exact h3.symm

theorem exists_conj_of_card {X : Type} [Group X] [Finite X] {P₁ P₂ : Subgroup X} {n : ℕ}
    (h1 : Nat.card ↥P₁ = 2 ^ n) (h2 : Nat.card ↥P₂ = 2 ^ n)
    (hn : (Nat.card X).factorization 2 = n) :
    ∃ g : X, ∀ y ∈ P₁, g * y * g⁻¹ ∈ P₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S₁ : Sylow 2 X := Sylow.ofCard P₁ (by rw [hn]; exact h1)
  let S₂ : Sylow 2 X := Sylow.ofCard P₂ (by rw [hn]; exact h2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₁ S₂
  refine ⟨g, fun y hy => ?_⟩
  have h3 : (MulAut.conj g) • y ∈ (MulAut.conj g) • (S₁ : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ hy
  have h4 : ((g • S₁ : Sylow 2 X) : Subgroup X) = (MulAut.conj g) • (S₁ : Subgroup X) := rfl
  rw [hg] at h4
  have h5 : y ∈ (S₁ : Subgroup X) := hy
  have h6 : ((S₂ : Subgroup X)) = P₂ := rfl
  rw [h6] at h4
  rw [h4]
  simpa using h3


theorem outer_invs_conj
    {C : Type} [Group C] [Finite C] {Q K : Subgroup C}
    (hloc : LocalK C Q K) (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2))
    (hcen : Subgroup.center ↥K = ⊥) (hOut2 : Nat.card (MulAut ↥K) = 2 * Nat.card ↥K)
    (hA1 : ∀ φ ψ : MulAut ↥K, φ ^ 2 = 1 → ψ ^ 2 = 1 →
      (¬ ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹) → (¬ ∃ k : ↥K, ∀ x : ↥K, ψ x = k * x * k⁻¹) →
      ∃ α : MulAut ↥K, α * φ * α⁻¹ = ψ)
    (hD24 : Nat.card ↥(Subgroup.centralizer (K : Set C)) = 24)
    {u v : C} (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu : ¬ ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹)
    (hv : ¬ ∃ k ∈ K, ∀ x ∈ K, v * x * v⁻¹ = k * x * k⁻¹)
    (huQ : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹)
    (hvQ : ¬ ∃ q ∈ Q, ∀ y ∈ Q, v * y * v⁻¹ = q * y * q⁻¹) :
    ∃ c : C, c * u * c⁻¹ = v := by
  classical
  have hKn := hloc.K_normal
  have hQn := hloc.Q_normal
  obtain ⟨eQ⟩ := hQ8
  set D : Subgroup C := Subgroup.centralizer (K : Set C) with hD
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hQD : Q ≤ D := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (hloc.commute q hq k hk).symm
  have hQcard : Nat.card ↥Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  let θ : C →* MulAut ↥K := MulAut.conjNormal
  have hθ : ∀ (m : C) (x : ↥K), ((θ m x : ↥K) : C) = m * x * m⁻¹ := fun m x =>
    MulAut.conjNormal_apply m x
  have hu2' : u ^ 2 = 1 := by rw [sq]; exact hu2
  have hv2' : v ^ 2 = 1 := by rw [sq]; exact hv2
  have hφ2 : (θ u) ^ 2 = 1 := by rw [← map_pow, hu2', map_one]
  have hψ2 : (θ v) ^ 2 = 1 := by rw [← map_pow, hv2', map_one]
  have hφo : ¬ ∃ k : ↥K, ∀ x : ↥K, θ u x = k * x * k⁻¹ := by
    rintro ⟨k, hk⟩
    apply hu
    refine ⟨(k : C), k.2, fun x hx => ?_⟩
    have := congrArg (fun y : ↥K => (y : C)) (hk ⟨x, hx⟩)
    simp only [hθ, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  have hψo : ¬ ∃ k : ↥K, ∀ x : ↥K, θ v x = k * x * k⁻¹ := by
    rintro ⟨k, hk⟩
    apply hv
    refine ⟨(k : C), k.2, fun x hx => ?_⟩
    have := congrArg (fun y : ↥K => (y : C)) (hk ⟨x, hx⟩)
    simp only [hθ, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  obtain ⟨α, hα⟩ := hA1 (θ u) (θ v) hφ2 hψ2 hφo hψo
  obtain ⟨c₁, hc₁⟩ := conjNormal_surjective hcen hOut2 hu α
  set u₁ : C := c₁ * u * c₁⁻¹ with hu₁
  have hθu₁ : θ u₁ = θ v := by
    rw [hu₁, map_mul, map_mul, map_inv]
    have : θ c₁ = α := hc₁
    rw [this, ← hα]
  have hu₁2 : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = c₁ * (u * u) * c₁⁻¹ := by rw [hu₁]; group
      _ = 1 := by rw [hu2]; group
  have hu₁out : ¬ ∃ k ∈ K, ∀ x ∈ K, u₁ * x * u₁⁻¹ = k * x * k⁻¹ := by
    rintro ⟨k, hk, hk2⟩
    apply hv
    refine ⟨k, hk, fun x hx => ?_⟩
    have := congrArg (fun σ : MulAut ↥K => ((σ ⟨x, hx⟩ : ↥K) : C)) hθu₁
    simp only [hθ] at this
    rw [← this]
    exact hk2 x hx
  have hu₁Q : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u₁ * y * u₁⁻¹ = q * y * q⁻¹ := by
    rintro ⟨q, hq, hq2⟩
    apply huQ
    refine ⟨c₁⁻¹ * q * c₁, by simpa using hQn.conj_mem q hq c₁⁻¹, fun y hy => ?_⟩
    have hcy : c₁ * y * c₁⁻¹ ∈ Q := hQn.conj_mem y hy c₁
    have := hq2 _ hcy
    calc u * y * u⁻¹ = c₁⁻¹ * (c₁ * u * c₁⁻¹ * (c₁ * y * c₁⁻¹) * (c₁ * u * c₁⁻¹)⁻¹) * c₁ := by
          group
      _ = c₁⁻¹ * (q * (c₁ * y * c₁⁻¹) * q⁻¹) * c₁ := by rw [← hu₁, this]
      _ = (c₁⁻¹ * q * c₁) * y * (c₁⁻¹ * q * c₁)⁻¹ := by group
  have hu₁i : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁2
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hwD : v * u₁⁻¹ ∈ D := by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun σ : MulAut ↥K => ((σ ⟨x, hx⟩ : ↥K) : C)) hθu₁
    simp only [hθ] at h1
    have h2' : u₁⁻¹ * x * u₁ = v * x * v⁻¹ := by
      rw [hu₁i]
      rw [hu₁i] at h1
      exact h1
    have h3 : (v * u₁⁻¹) * x * (v * u₁⁻¹)⁻¹ = x := by
      calc (v * u₁⁻¹) * x * (v * u₁⁻¹)⁻¹ = v * (u₁⁻¹ * x * u₁) * v⁻¹ := by group
        _ = v * (v * x * v⁻¹) * v⁻¹ := by rw [h2']
        _ = (v * v) * x * (v * v)⁻¹ := by group
        _ = x := by rw [hv2]; group
    calc x * (v * u₁⁻¹) = ((v * u₁⁻¹) * x * (v * u₁⁻¹)⁻¹) * (v * u₁⁻¹) := by rw [h3]
      _ = (v * u₁⁻¹) * x := by group
  have hu₁D : u₁ ∉ D := by
    intro h
    apply hu₁out
    refine ⟨1, K.one_mem, fun x hx => ?_⟩
    have := Subgroup.mem_centralizer_iff.1 h x hx
    calc u₁ * x * u₁⁻¹ = x * u₁ * u₁⁻¹ := by rw [← this]
      _ = 1 * x * 1⁻¹ := by group
  have hvD : v ∉ D := by
    intro h
    apply hv
    refine ⟨1, K.one_mem, fun x hx => ?_⟩
    have := Subgroup.mem_centralizer_iff.1 h x hx
    calc v * x * v⁻¹ = x * v * v⁻¹ := by rw [← this]
      _ = 1 * x * 1⁻¹ := by group
  have hu₁Q' : u₁ ∉ Q := fun h => hu₁D (hQD h)
  have hvQ' : v ∉ Q := fun h => hvD (hQD h)
  set H : Subgroup C := D ⊔ Subgroup.zpowers u₁ with hH
  set T₁ : Subgroup C := Q ⊔ Subgroup.zpowers u₁ with hT₁
  set T₂ : Subgroup C := Q ⊔ Subgroup.zpowers v with hT₂
  have hHcard : Nat.card ↥H = 48 := by
    have := card_sup_zpowers_of_normal D hu₁2 hu₁D
    rw [hD24] at this
    omega
  have hT₁card : Nat.card ↥T₁ = 16 := by
    have := card_sup_zpowers_of_normal Q hu₁2 hu₁Q'
    rw [hQcard] at this
    omega
  have hT₂card : Nat.card ↥T₂ = 16 := by
    have := card_sup_zpowers_of_normal Q hv2 hvQ'
    rw [hQcard] at this
    omega
  have hu₁H : u₁ ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u₁)
  have hvH : v ∈ H := by
    have : v = (v * u₁⁻¹) * u₁ := by group
    rw [this]
    exact H.mul_mem (Subgroup.mem_sup_left hwD) hu₁H
  have hT₁H : T₁ ≤ H :=
    sup_le (hQD.trans le_sup_left) ((Subgroup.zpowers_le).2 hu₁H)
  have hT₂H : T₂ ≤ H :=
    sup_le (hQD.trans le_sup_left) ((Subgroup.zpowers_le).2 hvH)
  have hfac : (Nat.card ↥H).factorization 2 = 4 := by
    rw [hHcard, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
    simp
  have hcard1 : Nat.card ↥(T₁.subgroupOf H) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁H).toEquiv, hT₁card]
    norm_num
  have hcard2 : Nat.card ↥(T₂.subgroupOf H) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₂H).toEquiv, hT₂card]
    norm_num
  obtain ⟨h, hh⟩ := exists_conj_of_card hcard1 hcard2 hfac
  have hu₁T₁ : u₁ ∈ T₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers u₁)
  have hmem2 := hh ⟨u₁, hu₁H⟩ (Subgroup.mem_subgroupOf.2 hu₁T₁)
  have hmem3 : (h : C) * u₁ * (h : C)⁻¹ ∈ T₂ := Subgroup.mem_subgroupOf.1 hmem2
  obtain ⟨q, hq, z, hz, hqz⟩ := (Subgroup.mem_sup_of_normal_left (s := Q)
    (t := Subgroup.zpowers v)).1 hmem3
  rcases zpowers_involution hv2 z hz with hz1 | hz1
  · exfalso
    rw [hz1, mul_one] at hqz
    apply hu₁Q'
    have : u₁ = (h : C)⁻¹ * q * (h : C) := by rw [hqz]; group
    rw [this]
    simpa using hQn.conj_mem q hq (h : C)⁻¹
  · rw [hz1] at hqz
    have hsq : q * (v * q * v⁻¹) = 1 := by
      have h1 : (q * v) * (q * v) = 1 := by
        rw [hqz]
        calc (h : C) * u₁ * (h : C)⁻¹ * ((h : C) * u₁ * (h : C)⁻¹)
            = (h : C) * (u₁ * u₁) * (h : C)⁻¹ := by group
          _ = 1 := by rw [hu₁2]; group
      calc q * (v * q * v⁻¹) = (q * v) * (q * v) := by rw [hvi]; group
        _ = 1 := h1
    obtain ⟨d, hd, hqd⟩ := q8_twisted_conj Q eQ hv2 hvQ q hq hsq
    refine ⟨d⁻¹ * (h : C) * c₁, ?_⟩
    have hhu : (h : C) * u₁ * (h : C)⁻¹ = d * v * d⁻¹ := by
      rw [← hqz, hqd]; group
    calc d⁻¹ * (h : C) * c₁ * u * (d⁻¹ * (h : C) * c₁)⁻¹
        = d⁻¹ * ((h : C) * (c₁ * u * c₁⁻¹) * (h : C)⁻¹) * d := by group
      _ = d⁻¹ * ((h : C) * u₁ * (h : C)⁻¹) * d := by rw [← hu₁]
      _ = d⁻¹ * (d * v * d⁻¹) * d := by rw [hhu]
      _ = v := by group





theorem centralizer_D_of_outer {C : Type} [Group C]
    [Finite C] {Q K : Subgroup C} (hloc : LocalK C Q K)
    (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2)) {t : C} (ht : orderOf t = 2) (htQ : t ∈ Q)
    (hD24 : Nat.card ↥(Subgroup.centralizer (K : Set C)) = 24)
    {u : C} (hu2 : u * u = 1) (huQ : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹) :
    ∀ d ∈ Subgroup.centralizer (K : Set C), u * d = d * u → d = 1 ∨ d = t := by
  classical
  intro d hdD hud
  have hQn := hloc.Q_normal
  obtain ⟨eQ⟩ := hQ8
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  set D : Subgroup C := Subgroup.centralizer (K : Set C) with hD
  have hQD : Q ≤ D := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (hloc.commute q hq k hk).symm
  by_cases hdQ : d ∈ Q
  ·
    have hd : u * d * u⁻¹ = d := by rw [hud]; group
    exact q8_fixed_pts Q eQ hu2 huQ htQ ht2 ht1 d hdQ hd
  · exfalso
    have hQcard : Nat.card ↥Q = 8 := by
      rw [Nat.card_congr eQ.toEquiv]
      simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
    let Q' : Subgroup ↥D := Q.subgroupOf D
    have : Q'.Normal := hQn.subgroupOf D
    have hQ'card : Nat.card ↥Q' = 8 := by
      rw [← hQcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv
    have hidx : Q'.index = 3 := by
      have h1 := Subgroup.index_mul_card Q'
      rw [hQ'card, hD24] at h1
      omega
    let d' : ↥D := ⟨d, hdD⟩
    have hd'Q : d' ∉ Q' := fun h => hdQ (Subgroup.mem_subgroupOf.1 h)
    have hx1 : (QuotientGroup.mk d' : ↥D ⧸ Q') ≠ 1 := by
      intro h
      exact hd'Q ((QuotientGroup.eq_one_iff d').1 h)
    have hordx : orderOf (QuotientGroup.mk d' : ↥D ⧸ Q') = 3 := by
      have hdvd : orderOf (QuotientGroup.mk d' : ↥D ⧸ Q') ∣ 3 := by
        rw [← hidx]
        exact orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx1
      · exact h
    have h3dvd : 3 ∣ orderOf d := by
      have h1 : orderOf (QuotientGroup.mk d' : ↥D ⧸ Q') ∣ orderOf d' := by
        have := orderOf_map_dvd (QuotientGroup.mk' Q') d'
        simpa using this
      rw [hordx] at h1
      have h2 : orderOf d' = orderOf d := (Subgroup.orderOf_coe d').symm
      rwa [h2] at h1
    have hord0 : orderOf d ≠ 0 := (orderOf_pos d).ne'
    set d₃ : C := d ^ (orderOf d / 3) with hd₃
    have hd₃ord : orderOf d₃ = 3 := orderOf_pow_orderOf_div hord0 h3dvd
    have hd₃3 : d₃ ^ 3 = 1 := by rw [← hd₃ord]; exact pow_orderOf_eq_one d₃
    have hd₃D : d₃ ∈ D := D.pow_mem hdD _
    have hd₃u : u * d₃ = d₃ * u := by
      have : Commute u d := hud
      exact (this.pow_right _).eq
    have hd₃Q : d₃ ∉ Q := by
      intro h
      have : orderOf (⟨d₃, h⟩ : ↥Q) ∣ 8 := by
        rw [← hQcard]
        exact orderOf_dvd_natCard _
      have h2 : orderOf (⟨d₃, h⟩ : ↥Q) = 3 := by rw [← Subgroup.orderOf_coe]; exact hd₃ord
      rw [h2] at this
      omega
    have hdn : ∃ q ∈ Q, d₃ * q * d₃⁻¹ ≠ q := by
      by_contra hcon
      push Not at hcon
      apply hd₃Q
      refine hloc.self_centralizing d₃ (fun q hq => ?_) (fun k hk => ?_)
      · have := hcon q hq
        calc d₃ * q = d₃ * q * d₃⁻¹ * d₃ := by group
          _ = q * d₃ := by rw [this]
      · exact (Subgroup.mem_centralizer_iff.1 hd₃D k hk).symm
    exact q8_no_comm_order3 Q eQ hu2 huQ hd₃3 hdn hd₃u


theorem comm_aux1 {C : Type*} [Group C] (a b w : C) (h : w * b = b * w) :
    a * w * b * (a * w)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h' : w * b * w⁻¹ = b := by rw [h]; group
  calc a * w * b * (a * w)⁻¹ * b⁻¹ = a * (w * b * w⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h']

theorem comm_aux2 {C : Type*} [Group C] (a b w : C) (h : w * a = a * w) :
    a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h' : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    have : w * a * w⁻¹ = a := by rw [h]; group
    calc w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [this]
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h']

theorem commutator_centralizer_in_K {C : Type} [Group C] [Finite C] {Q K : Subgroup C}
    (hloc : LocalK C Q K) (hcen : Subgroup.center ↥K = ⊥)
    (hOut2 : Nat.card (MulAut ↥K) = 2 * Nat.card ↥K) {t : C} (htc : ∀ g : C, g * t = t * g)
    {u : C} (hu2 : u * u = 1) (hu : ¬ ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹)
    (hDu : ∀ d ∈ Subgroup.centralizer (K : Set C), u * d = d * u → d = 1 ∨ d = t) :
    ∀ m₁ m₂ : C, m₁ * u = u * m₁ → m₂ * u = u * m₂ → m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ K := by
  classical
  have hKn := hloc.K_normal
  set D : Subgroup C := Subgroup.centralizer (K : Set C) with hD
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hdisj : K ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxD⟩
    have hxz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxD y y.2)
    rw [hcen, Subgroup.mem_bot] at hxz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxz
  let P : C → Prop := fun m => ∃ k ∈ K, ∀ x ∈ K, m * x * m⁻¹ = k * x * k⁻¹
  have hPiff : ∀ m : C, P m ↔ (MulAut.conjNormal m : MulAut ↥K) ∈
      (MulAut.conj : ↥K →* MulAut ↥K).range := by
    intro m
    constructor
    · rintro ⟨k, hk, hk2⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      ext ⟨x, hx⟩
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply]
      exact (hk2 x hx).symm
    · rintro ⟨k, hk⟩
      refine ⟨(k : C), k.2, fun x hx => ?_⟩
      have := congrArg (fun σ : MulAut ↥K => (σ ⟨x, hx⟩ : C)) hk
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at this
      exact this.symm
  have hidx := inn_index_two hcen hOut2
  have hkey : ∀ m : C, P m ∨ P (m * u) := by
    intro m
    by_cases hm : P m
    · exact Or.inl hm
    · right
      rw [hPiff]
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two hidx]
      constructor
      · intro h; exact absurd ((hPiff m).2 h) hm
      · intro h; exact absurd ((hPiff u).2 h) hu
  have hmain : ∀ n₁ n₂ : C, P n₁ → P n₂ → n₁ * u = u * n₁ → n₂ * u = u * n₂ →
      n₁ * n₂ * n₁⁻¹ * n₂⁻¹ ∈ K := by
    have hdec : ∀ n : C, P n → n * u = u * n → ∃ k ∈ K, ∃ d, d ∈ D ∧ n = k * d ∧
        (d = 1 ∨ d = t) := by
      intro n ⟨k, hk, hk2⟩ hnu
      have hdD : k⁻¹ * n ∈ D := by
        rw [hD, Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := hk2 x hx
        calc x * (k⁻¹ * n) = k⁻¹ * (k * x * k⁻¹) * n := by group
          _ = k⁻¹ * (n * x * n⁻¹) * n := by rw [h1]
          _ = (k⁻¹ * n) * x := by group
      have hak : u * k * u⁻¹ ∈ K := hKn.conj_mem k hk u
      have hbD : u * (k⁻¹ * n) * u⁻¹ ∈ D := hDn.conj_mem _ hdD u
      have hprod : (u * k * u⁻¹) * (u * (k⁻¹ * n) * u⁻¹) = k * (k⁻¹ * n) := by
        calc (u * k * u⁻¹) * (u * (k⁻¹ * n) * u⁻¹) = u * (k * (k⁻¹ * n)) * u⁻¹ := by group
          _ = u * n * u⁻¹ := by rw [mul_inv_cancel_left]
          _ = n := by rw [← hnu]; group
          _ = k * (k⁻¹ * n) := by group
      have hmem : k⁻¹ * (u * k * u⁻¹) ∈ K ⊓ D := by
        refine ⟨K.mul_mem (K.inv_mem hk) hak, ?_⟩
        have e1 : k⁻¹ * (u * k * u⁻¹) = (k⁻¹ * n) * (u * (k⁻¹ * n) * u⁻¹)⁻¹ := by
          have : u * k * u⁻¹ = k * (k⁻¹ * n) * (u * (k⁻¹ * n) * u⁻¹)⁻¹ := by
            rw [← hprod]; group
          rw [this]; group
        rw [e1]
        exact D.mul_mem hdD (D.inv_mem hbD)
      rw [hdisj, Subgroup.mem_bot] at hmem
      have hu1 : u * k * u⁻¹ = k := by
        calc u * k * u⁻¹ = k * (k⁻¹ * (u * k * u⁻¹)) := by group
          _ = k := by rw [hmem]; group
      have hu2' : u * (k⁻¹ * n) * u⁻¹ = k⁻¹ * n := by
        have h3 := hprod
        rw [hu1] at h3
        exact mul_left_cancel h3
      have hdu : u * (k⁻¹ * n) = (k⁻¹ * n) * u := by
        calc u * (k⁻¹ * n) = (u * (k⁻¹ * n) * u⁻¹) * u := by group
          _ = (k⁻¹ * n) * u := by rw [hu2']
      exact ⟨k, hk, k⁻¹ * n, hdD, by group, hDu _ hdD hdu⟩
    intro n₁ n₂ h₁ h₂ hu₁ hu₂
    obtain ⟨k₁, hk₁, d₁, hd₁D, rfl, hd₁⟩ := hdec n₁ h₁ hu₁
    obtain ⟨k₂, hk₂, d₂, hd₂D, rfl, hd₂⟩ := hdec n₂ h₂ hu₂
    have hd12 : d₁ * d₂ = d₂ * d₁ := by
      rcases hd₁ with rfl | rfl
      · simp
      · rcases hd₂ with rfl | rfl
        · simp
        · rfl
    have hd1k2 : d₁ * (k₂ * d₂) = (k₂ * d₂) * d₁ := by
      have : d₁ * k₂ = k₂ * d₁ := (Subgroup.mem_centralizer_iff.1 hd₁D k₂ hk₂).symm
      calc d₁ * (k₂ * d₂) = (d₁ * k₂) * d₂ := by group
        _ = (k₂ * d₁) * d₂ := by rw [this]
        _ = k₂ * (d₁ * d₂) := by group
        _ = k₂ * (d₂ * d₁) := by rw [hd12]
        _ = (k₂ * d₂) * d₁ := by group
    have hd2k1 : d₂ * k₁ = k₁ * d₂ := (Subgroup.mem_centralizer_iff.1 hd₂D k₁ hk₁).symm
    rw [comm_aux1 k₁ (k₂ * d₂) d₁ hd1k2, comm_aux2 k₁ k₂ d₂ hd2k1]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  have hred : ∀ m : C, m * u = u * m →
      ∃ n w : C, (w = 1 ∨ w = u) ∧ m = n * w ∧ n * u = u * n ∧ P n := by
    intro m hm
    rcases hkey m with h | h
    · exact ⟨m, 1, Or.inl rfl, by simp, hm, h⟩
    · refine ⟨m * u, u, Or.inr rfl, ?_, ?_, h⟩
      · rw [mul_assoc, hu2, mul_one]
      · have h1 : m * u * u = m := by rw [mul_assoc, hu2, mul_one]
        have h2 : u * (m * u) = m := by
          calc u * (m * u) = u * m * u := by rw [mul_assoc]
            _ = m * u * u := by rw [← hm]
            _ = m := h1
        rw [h1, h2]
  intro m₁ m₂ hm₁ hm₂
  obtain ⟨n₁, w₁, hw₁, rfl, hn₁, hP₁⟩ := hred m₁ hm₁
  obtain ⟨n₂, w₂, hw₂, rfl, hn₂, hP₂⟩ := hred m₂ hm₂
  have hw1n2 : w₁ * n₂ = n₂ * w₁ := by
    rcases hw₁ with rfl | rfl
    · simp
    · exact hn₂.symm
  have hw2n1 : w₂ * n₁ = n₁ * w₂ := by
    rcases hw₂ with rfl | rfl
    · simp
    · exact hn₁.symm
  have hw12 : w₁ * w₂ = w₂ * w₁ := by
    rcases hw₁ with rfl | rfl
    · simp
    · rcases hw₂ with rfl | rfl
      · simp
      · rfl
  have hw1c : w₁ * (n₂ * w₂) = (n₂ * w₂) * w₁ := by
    calc w₁ * (n₂ * w₂) = (w₁ * n₂) * w₂ := by group
      _ = (n₂ * w₁) * w₂ := by rw [hw1n2]
      _ = n₂ * (w₁ * w₂) := by group
      _ = n₂ * (w₂ * w₁) := by rw [hw12]
      _ = (n₂ * w₂) * w₁ := by group
  rw [comm_aux1 n₁ (n₂ * w₂) w₁ hw1c, comm_aux2 n₁ n₂ w₂ hw2n1]
  exact hmain n₁ n₂ hP₁ hP₂ hn₁ hn₂


end CFSG.GH74.E2
