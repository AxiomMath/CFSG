module

public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Generic.DeltaClosure

section Alpha

variable {G : Type} [Group G]

theorem alphaCore_eq_bot_iff_of_deltaCore_eq_bot {F : Subgroup G} (hΔ : deltaCore F = ⊥) :
    alphaCore F = ⊥ ↔ uCore F ≤ Subgroup.centralizer (F : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h
    exact le_bot_iff.mp (commutator_le_alphaCore.trans h.le)
  · intro h
    unfold alphaCore
    rw [h, hΔ, sup_bot_eq]
    unfold normalClosureIn
    simp

theorem uCore_closure_pair {x u : G} (hx : x * x = 1) (hu : u * u = 1) (hxu : x * u = u * x)
    (hx1 : x ≠ 1) (hu1 : u ≠ 1) (hne : x ≠ u) :
    uCore (Subgroup.closure ({x, u} : Set G)) =
      involutionOddCore x ⊔ involutionOddCore u ⊔ involutionOddCore (x * u) := by
  have hxF : x ∈ Subgroup.closure ({x, u} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have huF : u ∈ Subgroup.closure ({x, u} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hxuF : x * u ∈ Subgroup.closure ({x, u} : Set G) := Subgroup.mul_mem _ hxF huF
  have hxu1 : x * u ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hu])
  apply le_antisymm
  · refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    rcases mem_closure_pair_cases hx hu hxu hf with h | h | h | h
    · exact absurd h hf1
    · rw [h]
      exact le_sup_of_le_left le_sup_left
    · rw [h]
      exact le_sup_of_le_left le_sup_right
    · rw [h]
      exact le_sup_right
  · exact sup_le (sup_le (involutionOddCore_le_uCore hxF hx1) (involutionOddCore_le_uCore huF hu1))
      (involutionOddCore_le_uCore hxuF hxu1)

theorem alphaCore_pair_eq_bot_iff {x u : G} (hx : x * x = 1) (hu : u * u = 1)
    (hxu : x * u = u * x) (hx1 : x ≠ 1) (hu1 : u ≠ 1) (hne : x ≠ u)
    (hP : involutionOddCore u = ⊥) :
    alphaCore (Subgroup.closure ({x, u} : Set G)) = ⊥ ↔
      (∀ p ∈ involutionOddCore x, u * p = p * u) ∧
        (∀ p ∈ involutionOddCore (x * u), u * p = p * u) := by
  have huF : u ∈ Subgroup.closure ({x, u} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hΔ : deltaCore (Subgroup.closure ({x, u} : Set G)) = ⊥ :=
    le_bot_iff.mp ((deltaCore_le_involutionOddCore huF hu1).trans hP.le)
  rw [alphaCore_eq_bot_iff_of_deltaCore_eq_bot hΔ, uCore_closure_pair hx hu hxu hx1 hu1 hne, hP,
    sup_bot_eq, Subgroup.centralizer_closure]
  have hcx : ∀ p ∈ involutionOddCore x, x * p = p * x := fun p hp =>
    (Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer x hp)).symm
  have hcxu : ∀ p ∈ involutionOddCore (x * u), x * u * p = p * (x * u) := fun p hp =>
    (Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer (x * u) hp)).symm
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_sup_left hp)) u
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_sup_right hp)) u
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · rintro ⟨h1, h2⟩
    refine sup_le (fun p hp => ?_) (fun p hp => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rcases ht with h | h
      · rw [h]
        exact hcx p hp
      · rw [Set.mem_singleton_iff.mp h]
        exact h1 p hp
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rcases ht with h | h
      · rw [h]
        have h3 := h2 p hp
        have h4 := hcxu p hp
        calc x * p = (x * u) * (u * p) := by rw [← mul_assoc, mul_assoc x u u, hu, mul_one]
          _ = (x * u) * (p * u) := by rw [h3]
          _ = ((x * u) * p) * u := (mul_assoc _ _ _).symm
          _ = (p * (x * u)) * u := by rw [h4]
          _ = p * x := by rw [mul_assoc, mul_assoc, hu, mul_one]
      · rw [Set.mem_singleton_iff.mp h]
        exact h2 p hp

theorem mul_comm_iff_of_mul_comm {a b p : G} (ha : a * a = 1) (hb : b * b = 1)
    (hp : p * (a * b) = (a * b) * p) : a * p = p * a ↔ b * p = p * b := by
  constructor
  · intro h
    calc b * p = a * ((a * b) * p) := by rw [← mul_assoc, ← mul_assoc, ha, one_mul]
      _ = a * (p * (a * b)) := by rw [hp]
      _ = (a * p) * (a * b) := by rw [← mul_assoc]
      _ = (p * a) * (a * b) := by rw [h]
      _ = p * b := by rw [mul_assoc, ← mul_assoc a a b, ha, one_mul]
  · intro h
    calc a * p = ((a * b) * b) * p := by rw [mul_assoc a b b, hb, mul_one]
      _ = (a * b) * (b * p) := by rw [mul_assoc]
      _ = (a * b) * (p * b) := by rw [h]
      _ = ((a * b) * p) * b := (mul_assoc _ _ _).symm
      _ = (p * (a * b)) * b := by rw [hp]
      _ = p * a := by rw [mul_assoc, mul_assoc, hb, mul_one]

theorem alphaCore_edge_eq_bot_iff {z₁ z₂ : G} (h1 : z₁ * z₁ = 1) (h2 : z₂ * z₂ = 1)
    (h12 : z₁ * z₂ = z₂ * z₁) (hz1 : z₁ ≠ 1) (hz2 : z₂ ≠ 1) (hne : z₁ ≠ z₂)
    (hP₁ : involutionOddCore z₁ = ⊥) (hP₂ : involutionOddCore z₂ = ⊥) :
    alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ ↔
      ∀ p ∈ involutionOddCore (z₁ * z₂), z₁ * p = p * z₁ := by
  rw [alphaCore_pair_eq_bot_iff h1 h2 h12 hz1 hz2 hne hP₂, hP₁]
  have hc : ∀ p ∈ involutionOddCore (z₁ * z₂), p * (z₁ * z₂) = (z₁ * z₂) * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer (z₁ * z₂) hp)
  constructor
  · rintro ⟨-, h⟩ p hp
    exact (mul_comm_iff_of_mul_comm h1 h2 (hc p hp)).mpr (h p hp)
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [Subgroup.mem_bot.mp hp]
      simp
    · exact (mul_comm_iff_of_mul_comm h1 h2 (hc p hp)).mp (h p hp)

end Alpha

section Layer

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_oddCoreIn_layer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x p v : G}
    (hp : p ∈ involutionOddCore x) (hv : v ∈ centralizingLayer Ω {x}) :
    p * v * p⁻¹ * v⁻¹ ∈ oddCoreIn (centralizingLayer Ω {x}) := by
  have hvC : v ∈ Subgroup.centralizer ({x} : Set G) := centralizingLayer_le_centralizer Ω {x} hv
  have hpC : p ∈ Subgroup.centralizer ({x} : Set G) := involutionOddCore_le_centralizer x hp
  have hS : involutionOddCore x ⊓ centralizingLayer Ω {x} ≤
      oddCoreIn (centralizingLayer Ω {x}) := by
    refine le_oddCoreIn_of_normalizes inf_le_right (fun n hn => ?_) ?_
    · have hnC : n ∈ Subgroup.centralizer ({x} : Set G) :=
        centralizingLayer_le_centralizer Ω {x} hn
      have h1 : n ∈ Subgroup.normalizer (involutionOddCore x : Set G) := normalizer_oddCoreIn _ hnC
      have h2 : n ∈ Subgroup.normalizer (centralizingLayer Ω {x} : Set G) :=
        mem_normalizer_centralizingLayer hΩ hnC
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro h
      exact ⟨fun ⟨a, b⟩ => ⟨(h1 h).mp a, (h2 h).mp b⟩,
        fun ⟨a, b⟩ => ⟨(h1 h).mpr a, (h2 h).mpr b⟩⟩
    · exact (odd_card_oddCoreIn (Subgroup.centralizer ({x} : Set G))).of_dvd_nat
        (Subgroup.card_dvd_of_le inf_le_left)
  apply hS
  refine ⟨?_, ?_⟩
  · have := conj_mem_oddCoreIn hvC ((involutionOddCore x).inv_mem hp)
    have h2 : p * (v * p⁻¹ * v⁻¹) ∈ involutionOddCore x := (involutionOddCore x).mul_mem hp this
    simpa [mul_assoc] using h2
  · exact (centralizingLayer Ω {x}).mul_mem
      (conj_mem_centralizingLayer hΩ hpC hv) ((centralizingLayer Ω {x}).inv_mem hv)

omit [Finite G] in
theorem eq_one_of_mul_self_eq_one_of_mem_odd {O : Subgroup G} (hodd : Odd (Nat.card O)) {t : G}
    (ht : t ∈ O) (h : t * t = 1) : t = 1 := by
  have h1 : orderOf t ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨t, ht⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · rw [h3] at h1
    have := Nat.odd_iff.mp hodd
    omega

theorem commute_involutionOddCore_of_commute_oddCoreIn_layer {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) {x v : G} (hv : v ∈ centralizingLayer Ω {x}) (hvv : v * v = 1)
    (hcomm : ∀ q ∈ oddCoreIn (centralizingLayer Ω {x}), v * q = q * v) :
    ∀ p ∈ involutionOddCore x, v * p = p * v := by
  intro p hp
  have htQ := commutator_mem_oddCoreIn_layer hΩ hp hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  rw [hvinv] at htQ
  set u : G := p * v * p⁻¹ with hu
  have huu : u * u = 1 := by
    calc u * u = p * (v * v) * p⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hvv]; group
  have h1 : v * (u * v) = (u * v) * v := hcomm (u * v) htQ
  have huv : u * v = v * u := by
    calc u * v = u * v * (v * v) := by rw [hvv, mul_one]
      _ = (u * v * v) * v := by rw [mul_assoc (u * v) v v]
      _ = (v * (u * v)) * v := by rw [h1]
      _ = v * u * (v * v) := by simp only [mul_assoc]
      _ = v * u := by rw [hvv, mul_one]
  have htt : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
      _ = u * (u * v) * v := by rw [← huv]
      _ = (u * u) * (v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [huu, hvv, one_mul]
  have hodd : Odd (Nat.card (oddCoreIn (centralizingLayer Ω {x}))) :=
    odd_card_oddCoreIn _
  have h5 : u * v = 1 := eq_one_of_mul_self_eq_one_of_mem_odd hodd htQ htt
  have h6 : u = v := by
    have := eq_inv_of_mul_eq_one_left h5
    rw [this, hvinv]
  rw [hu] at h6
  have h7 : p * v = v * p := by
    calc p * v = (p * v * p⁻¹) * p := by group
      _ = v * p := by rw [h6]
  exact h7.symm

end Layer

section Setup

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem involutionOddCore_eq_bot_of_member (hR : RouteD3Setup K z) {β : Subgroup G} {t : G}
    (hβ : β ∈ conjClass3 K) (ht : IsClassicalMember3 β t) : involutionOddCore t = ⊥ := by
  have hint := (Q3TC.RouteD3Setup.of_mem_conjClass3 hR hβ ht).intr
  have hβt : β ≤ Subgroup.centralizer ({t} : Set G) := isSubnormal_le ht.subnormal
  have h1 : oddCoreIn (Subgroup.centralizer ({t} : Set G)) ≤ oddCoreIn β :=
    le_oddCoreIn_of_normalizes hint (fun n hn => normalizer_oddCoreIn _ (hβt hn))
      (odd_card_oddCoreIn _)
  have h2 : oddCoreIn β = ⊥ := by
    show Subgroup.map _ (classicalInvolutionOddCore ↥β) = ⊥
    rw [hR.setup.1 β hβ, Subgroup.map_bot]
  exact le_bot_iff.mp (h1.trans h2.le)

theorem alphaCore_pair_eq_bot_iff_layer (hR : RouteD3Setup K z) {K₁ L : Subgroup G} {z₁ w : G}
    (hK₁ : K₁ ∈ conjClass3 K) (hL : L ∈ conjClass3 K) (hz₁ : IsClassicalMember3 K₁ z₁)
    (hw : IsClassicalMember3 L w) (hne : z₁ ≠ w) (hLz : L ≤ Subgroup.centralizer ({z₁} : Set G)) :
    alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥ ↔
      ∀ q ∈ oddCoreIn (locLayer (conjClass3 K) (z₁ * w)), w * q = q * w := by
  have hΩ := hR.inClass.conjInvariant
  have h1 : z₁ * z₁ = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hz₁.orderOf_eq_two
  have h2 : w * w = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two
  have h12 : z₁ * w = w * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp (hLz hw.mem)).symm
  have hLw : L ≤ Subgroup.centralizer ({w} : Set G) := isSubnormal_le hw.subnormal
  have hLx : L ≤ Subgroup.centralizer ({z₁ * w} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have a1 : y * z₁ = z₁ * y := Subgroup.mem_centralizer_singleton_iff.mp (hLz hy)
    have a2 : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp (hLw hy)
    calc y * (z₁ * w) = (y * z₁) * w := by rw [mul_assoc]
      _ = z₁ * (y * w) := by rw [a1, mul_assoc]
      _ = z₁ * (w * y) := by rw [a2]
      _ = (z₁ * w) * y := by rw [mul_assoc]
  have hwY : w ∈ locLayer (conjClass3 K) (z₁ * w) :=
    le_centralizingLayer ⟨hL, hLx⟩ hw.mem
  have hP₁ := involutionOddCore_eq_bot_of_member hR hK₁ hz₁
  have hP₂ := involutionOddCore_eq_bot_of_member hR hL hw
  rw [alphaCore_edge_eq_bot_iff h1 h2 h12 hz₁.ne_one hw.ne_one hne hP₁ hP₂]
  have hc : ∀ p ∈ involutionOddCore (z₁ * w), z₁ * p = p * z₁ ↔ w * p = p * w := fun p hp =>
    mul_comm_iff_of_mul_comm h1 h2
      (Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer (z₁ * w) hp))
  constructor
  · intro h q hq
    exact (hc q (oddCoreIn_centralizingLayer_le hΩ _ hq)).mp
      (h q (oddCoreIn_centralizingLayer_le hΩ _ hq))
  · intro h p hp
    exact (hc p hp).mpr
      (commute_involutionOddCore_of_commute_oddCoreIn_layer hΩ hwY h2 h p hp)

end Setup

end CFSG.ClassicalInvolution.Q3.Q3OF
