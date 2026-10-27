module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.ClaimA

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Act55

theorem commutatorElement_mul_left_eq {a b c : G} (h : b * c = c * b) : ⁅a * b, c⁆ = ⁅a, c⁆ := by
  have h' : b * c * b⁻¹ = c := by rw [h]; group
  simp only [commutatorElement_def]
  calc a * b * c * (a * b)⁻¹ * c⁻¹ = a * (b * c * b⁻¹) * a⁻¹ * c⁻¹ := by group
    _ = a * c * a⁻¹ * c⁻¹ := by rw [h']

theorem commutatorElement_mul_right_eq {a b c : G} (h : b * a = a * b) : ⁅a, c * b⁆ = ⁅a, c⁆ := by
  have h' : b * a⁻¹ * b⁻¹ = a⁻¹ := by
    have : b * a⁻¹ = a⁻¹ * b := by
      calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
        _ = a⁻¹ * (b * a) * a⁻¹ := by rw [h]
        _ = a⁻¹ * b := by group
    rw [this]; group
  simp only [commutatorElement_def]
  calc a * (c * b) * a⁻¹ * (c * b)⁻¹ = a * c * (b * a⁻¹ * b⁻¹) * c⁻¹ := by group
    _ = a * c * a⁻¹ * c⁻¹ := by rw [h']

theorem exists_subgroup_comm_mem (R Z : Subgroup G) (x : G)
    (hRZ : ∀ r ∈ R, ∀ w ∈ Z, r * w = w * r) :
    ∃ W : Subgroup G, ∀ r, r ∈ W ↔ r ∈ R ∧ x * r * x⁻¹ * r⁻¹ ∈ Z := by
  refine ⟨{ carrier := {r | r ∈ R ∧ x * r * x⁻¹ * r⁻¹ ∈ Z}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun r => Iff.rfl⟩
  · rintro r r' ⟨hr, hrZ⟩ ⟨hr', hr'Z⟩
    refine ⟨mul_mem hr hr', ?_⟩
    have e : x * (r * r') * x⁻¹ * (r * r')⁻¹ =
        (x * r * x⁻¹ * r⁻¹) * (r * (x * r' * x⁻¹ * r'⁻¹) * r⁻¹) := by group
    have h2 : r * (x * r' * x⁻¹ * r'⁻¹) * r⁻¹ = x * r' * x⁻¹ * r'⁻¹ := by
      rw [hRZ r hr _ hr'Z]; group
    rw [e, h2]
    exact mul_mem hrZ hr'Z
  · exact ⟨one_mem R, by simp⟩
  · rintro r ⟨hr, hrZ⟩
    refine ⟨inv_mem hr, ?_⟩
    have e : x * r⁻¹ * x⁻¹ * (r⁻¹)⁻¹ = r⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * r := by group
    have h2 : r⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * r = (x * r * x⁻¹ * r⁻¹)⁻¹ := by
      have := hRZ r hr _ (inv_mem hrZ)
      calc r⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * r = r⁻¹ * ((x * r * x⁻¹ * r⁻¹)⁻¹ * r) := by group
        _ = r⁻¹ * (r * (x * r * x⁻¹ * r⁻¹)⁻¹) := by rw [← this]
        _ = (x * r * x⁻¹ * r⁻¹)⁻¹ := by group
    show x * r⁻¹ * x⁻¹ * (r⁻¹)⁻¹ ∈ Z
    rw [e, h2]
    exact inv_mem hrZ

theorem comm_mul_eq {x r r' : G}
    (h : r * (x * r' * x⁻¹ * r'⁻¹) = (x * r' * x⁻¹ * r'⁻¹) * r) :
    x * (r * r') * x⁻¹ * (r * r')⁻¹ = (x * r * x⁻¹ * r⁻¹) * (x * r' * x⁻¹ * r'⁻¹) := by
  calc x * (r * r') * x⁻¹ * (r * r')⁻¹
      = (x * r * x⁻¹ * r⁻¹) * (r * (x * r' * x⁻¹ * r'⁻¹) * r⁻¹) := by group
    _ = (x * r * x⁻¹ * r⁻¹) * ((x * r' * x⁻¹ * r'⁻¹) * r * r⁻¹) := by rw [h]
    _ = (x * r * x⁻¹ * r⁻¹) * (x * r' * x⁻¹ * r'⁻¹) := by group

theorem comm_comm_eq (x r : G) :
    x * (x * r * x⁻¹ * r⁻¹) * x⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ =
      ⁅x ^ 2, r⁆ * ((x * r * x⁻¹ * r⁻¹) ^ 2)⁻¹ := by
  simp only [commutatorElement_def, pow_two]
  group

theorem comm_conj_eq {x k r : G}
    (huk : (x * r * x⁻¹ * r⁻¹) * k = k * (x * r * x⁻¹ * r⁻¹))
    (huρ : (x * r * x⁻¹ * r⁻¹) * (x * k * x⁻¹ * k⁻¹) = (x * k * x⁻¹ * k⁻¹) * (x * r * x⁻¹ * r⁻¹)) :
    x * (k * r * k⁻¹) * x⁻¹ * (k * r * k⁻¹)⁻¹ =
      (x * r * x⁻¹ * r⁻¹) * ⁅x * k * x⁻¹ * k⁻¹, k * r * k⁻¹⁆ := by
  have h1 : k * (x * r * x⁻¹ * r⁻¹) * k⁻¹ = x * r * x⁻¹ * r⁻¹ := by
    rw [← huk]; group
  calc x * (k * r * k⁻¹) * x⁻¹ * (k * r * k⁻¹)⁻¹
      = (x * k * x⁻¹ * k⁻¹) * (k * (x * r * x⁻¹ * r⁻¹) * k⁻¹) * (k * r * k⁻¹) *
          (x * k * x⁻¹ * k⁻¹)⁻¹ * (k * r * k⁻¹)⁻¹ := by group
    _ = (x * k * x⁻¹ * k⁻¹) * (x * r * x⁻¹ * r⁻¹) * (k * r * k⁻¹) *
          (x * k * x⁻¹ * k⁻¹)⁻¹ * (k * r * k⁻¹)⁻¹ := by rw [h1]
    _ = (x * r * x⁻¹ * r⁻¹) * (x * k * x⁻¹ * k⁻¹) * (k * r * k⁻¹) *
          (x * k * x⁻¹ * k⁻¹)⁻¹ * (k * r * k⁻¹)⁻¹ := by rw [huρ]
    _ = (x * r * x⁻¹ * r⁻¹) * ⁅x * k * x⁻¹ * k⁻¹, k * r * k⁻¹⁆ := by
      rw [commutatorElement_def]; group

theorem O2In_centPair_comm {t z a r : G} (ha : a ∈ pair z t) (hr : r ∈ O2In (centPair z t)) :
    a * r = r * a :=
  mem_centralizer_iff.1 (O2In_le _ hr) a ha

end Act55

open Act55

section Main

variable [Finite G] {t z : G}

theorem Level55.decomp_O2K (d : Level55 G t z) {r : G} (hr : r ∈ O2In (centPair z t)) :
    ∃ a ∈ d.R0, ∃ b ∈ zpowers t, r = a * b := by
  rw [d.O2K] at hr
  refine exists_mul_of_mem_sup_of_le_centralizer ?_ hr
  rw [zpowers_le, mem_centralizer_iff]
  intro a ha
  exact (mem_centPair_iff.1 (d.R0_le ha)).2.symm

theorem Level55.R0_commutator_mem_zpowers (d : Level55 G t z) {a a' : G} (ha : a ∈ d.R0)
    (ha' : a' ∈ d.R0) : ⁅a, a'⁆ ∈ zpowers z := by
  have h := d.R0_ext.commutator_mem_center ⟨a, ha⟩ ⟨a', ha'⟩
  have h' : ((⁅(⟨a, ha⟩ : ↥d.R0), ⟨a', ha'⟩⁆ : ↥d.R0) : G) ∈ (center ↥d.R0).map d.R0.subtype :=
    ⟨_, h, rfl⟩
  rw [d.R0_center] at h'
  exact h'

theorem Level55.R0_sq_mem_zpowers (d : Level55 G t z) {a : G} (ha : a ∈ d.R0) :
    a ^ 2 ∈ zpowers z := by
  have h := d.R0_ext.sq_mem_center ⟨a, ha⟩
  have h' : (((⟨a, ha⟩ : ↥d.R0) ^ 2 : ↥d.R0) : G) ∈ (center ↥d.R0).map d.R0.subtype := ⟨_, h, rfl⟩
  rw [d.R0_center] at h'
  exact h'

theorem Level55.O2K_sq_mem_zpowers (d : Level55 G t z) {r : G} (hr : r ∈ O2In (centPair z t)) :
    r ^ 2 ∈ zpowers z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.decomp_O2K hr
  have hab : Commute a b := (O2In_centPair_comm (mem_sup_right hb) (d.R0_le_O2K ha)).symm
  rw [hab.mul_pow]
  rcases eq_one_or_eq_of_mem_zpowers_two d.t_ord hb with rfl | rfl
  · rw [one_pow, mul_one]
    exact d.R0_sq_mem_zpowers ha
  · have h2 : b ^ 2 = 1 := by
      have := pow_orderOf_eq_one b
      rwa [d.t_ord] at this
    rw [h2, mul_one]
    exact d.R0_sq_mem_zpowers ha

theorem Level55.O2K_commutator_mem_zpowers (d : Level55 G t z) {r r' : G}
    (hr : r ∈ O2In (centPair z t)) (hr' : r' ∈ O2In (centPair z t)) : ⁅r, r'⁆ ∈ zpowers z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.decomp_O2K hr
  obtain ⟨a', ha', b', hb', rfl⟩ := d.decomp_O2K hr'
  rw [commutatorElement_mul_left_eq (O2In_centPair_comm (mem_sup_right hb) hr'),
    commutatorElement_mul_right_eq (O2In_centPair_comm (mem_sup_right hb') (d.R0_le_O2K ha))]
  exact d.R0_commutator_mem_zpowers ha ha'

theorem Level55.commutator_conj_mem_zpowers (d : Level55 G t z) {x k r : G}
    (hk : k ∈ centPair z t) (hr : r ∈ O2In (centPair z t))
    (hρ : x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t)) (hu : x * r * x⁻¹ * r⁻¹ ∈ zpowers z) :
    x * (k * r * k⁻¹) * x⁻¹ * (k * r * k⁻¹)⁻¹ ∈ zpowers z := by
  have hs : k * r * k⁻¹ ∈ O2In (centPair z t) :=
    (normal_subgroupOf_O2In (centPair z t)).conj_mem ⟨r, O2In_le _ hr⟩
      (by rw [mem_subgroupOf]; exact hr) ⟨k, hk⟩
  rw [comm_conj_eq (mem_centralizer_iff.1 hk _ (mem_sup_left hu))
    (O2In_centPair_comm (mem_sup_left hu) hρ)]
  exact mul_mem hu (d.O2K_commutator_mem_zpowers hρ hs)

theorem Level55.comm_mem_zpowers (d : Level55 G t z) {x : G} (hxz : x * z = z * x)
    (hxt : x * t * x⁻¹ = t * z)
    (hxN : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G))
    (hxK : ∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t))
    (hx2 : x ^ 2 ∈ O2In (centPair z t)) :
    ∀ r ∈ O2In (centPair z t), x * r * x⁻¹ * r⁻¹ ∈ zpowers z := by
  have hxR : ∀ r ∈ O2In (centPair z t), x * r * x⁻¹ ∈ O2In (centPair z t) := fun r hr =>
    (mem_normalizer_iff.1 hxN r).1 hr
  obtain ⟨W, hW⟩ := exists_subgroup_comm_mem (O2In (centPair z t)) (zpowers z) x
    fun r hr w hw => (O2In_centPair_comm (mem_sup_left hw) hr).symm
  have hAW : pair z t ≤ W := by
    refine sup_le (zpowers_le.2 ((hW z).2 ⟨d.pair_le_O2K (z_mem_pair z t), ?_⟩))
      (zpowers_le.2 ((hW t).2 ⟨d.pair_le_O2K (t_mem_pair z t), ?_⟩))
    · rw [hxz]
      simp
    · rw [hxt, ← d.zt_comm, mul_inv_cancel_right]
      exact mem_zpowers z
  have hWK : ∀ k ∈ centPair z t, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    intro k hk w hw
    obtain ⟨hwR, hwc⟩ := (hW w).1 hw
    refine (hW _).2 ⟨?_, d.commutator_conj_mem_zpowers hk hwR (hxK k hk) hwc⟩
    exact (normal_subgroupOf_O2In (centPair z t)).conj_mem ⟨w, O2In_le _ hwR⟩
      (by rw [mem_subgroupOf]; exact hwR) ⟨k, hk⟩
  rcases d.irred W hAW (fun w hw => ((hW w).1 hw).1) hWK with hWA | hWR
  · exfalso
    have hc1 : ∀ r ∈ O2In (centPair z t), x * r * x⁻¹ * r⁻¹ ∈ pair z t := by
      intro r hr
      have hu : x * r * x⁻¹ * r⁻¹ ∈ O2In (centPair z t) := mul_mem (hxR r hr) (inv_mem hr)
      have hmem : x * r * x⁻¹ * r⁻¹ ∈ W := by
        refine (hW _).2 ⟨hu, ?_⟩
        rw [comm_comm_eq x r]
        exact mul_mem (d.O2K_commutator_mem_zpowers hx2 hr) (inv_mem (d.O2K_sq_mem_zpowers hu))
      rwa [hWA] at hmem
    let ψ : ↥(O2In (centPair z t)) →* G :=
      { toFun := fun r => x * (r : G) * x⁻¹ * (r : G)⁻¹
        map_one' := by simp
        map_mul' := fun r r' =>
          comm_mul_eq (O2In_centPair_comm (hc1 r' r'.2) r.2).symm }
    have hker : ψ.ker.map (O2In (centPair z t)).subtype ≤ pair z t := by
      rintro _ ⟨r, hr, rfl⟩
      have h1 : x * (r : G) * x⁻¹ * (r : G)⁻¹ = 1 := hr
      have hmem : (r : G) ∈ W := (hW _).2 ⟨r.2, by rw [h1]; exact one_mem _⟩
      rwa [hWA] at hmem
    have hrange : ψ.range ≤ pair z t := by
      rintro _ ⟨r, rfl⟩
      exact hc1 r r.2
    have h4 := card_pair_le d.z_ord d.t_ord d.zt_comm
    have hk : Nat.card ψ.ker ≤ 4 :=
      calc Nat.card ψ.ker = Nat.card (ψ.ker.map (O2In (centPair z t)).subtype) :=
            (Subgroup.card_map_of_injective (O2In (centPair z t)).subtype_injective).symm
        _ ≤ Nat.card (pair z t) := Subgroup.card_le_of_le hker
        _ ≤ 4 := h4
    have hr : Nat.card ψ.range ≤ 4 := (Subgroup.card_le_of_le hrange).trans h4
    have h23 : 2 ^ 23 ≤ Nat.card ↥(O2In (centPair z t)) := by
      have := Subgroup.card_le_of_le d.R0_le_O2K
      rwa [d.R0_card] at this
    have hmul := Subgroup.card_ker_mul_card_range ψ
    have hle : Nat.card ψ.ker * Nat.card ψ.range ≤ 4 * 4 := Nat.mul_le_mul hk hr
    norm_num at h23
    omega
  · intro r hr
    have hrW : r ∈ W := by rw [hWR]; exact hr
    exact ((hW r).1 hrW).2

end Main

end CFSG.EvenSporadicStandard.TwoB
