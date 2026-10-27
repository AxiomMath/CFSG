module

public import CFSG.GH74.Uniqueness.SU.SU13TC3W

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem W_le_of_acts_trivially (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {g : G} (hg : g ∈ f.F)
    (hg1 : g ≠ 1)
    (hgW : ∀ u ∈ oc (centralizer ({e.s₁} : Set G)), g * u * g⁻¹ * u⁻¹ ∈ zpowers e.s₁) :
    oc (centralizer ({e.s₁} : Set G)) ≤ zpowers e.s₁ := by
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hFW : ∀ k ∈ f.F, ∀ u ∈ W, k * u * k⁻¹ ∈ W := fun k hk u hu =>
    conj_mem_oc (F_le_centralizerF e f hk) hu
  have hFW' : ∀ k ∈ f.F, ∀ u ∈ W, k⁻¹ * u * k ∈ W := fun k hk u hu => by
    have := hFW k⁻¹ (f.F.inv_mem hk) u hu
    simpa using this
  have hcomm : ∀ k ∈ f.F, ∀ c ∈ zpowers e.s₁, k * c * k⁻¹ = c := fun k hk c hc => by
    have : c * k = k * c := zpowers_comm_of_mem_centralizer (F_le_centralizerF e f hk) hc
    rw [← this]; group
  let K0 : Subgroup G :=
    { carrier := {k | k ∈ f.F ∧ ∀ u ∈ W, k * u * k⁻¹ * u⁻¹ ∈ zpowers e.s₁}
      one_mem' := ⟨f.F.one_mem, fun u _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haF, ha⟩ ⟨hbF, hb⟩
        refine ⟨f.F.mul_mem haF hbF, fun u hu => ?_⟩
        have h1 : a * b * u * (a * b)⁻¹ * u⁻¹ =
            (a * (b * u * b⁻¹ * u⁻¹) * a⁻¹) * (a * u * a⁻¹ * u⁻¹) := by group
        rw [h1, hcomm a haF _ (hb u hu)]
        exact (zpowers e.s₁).mul_mem (hb u hu) (ha u hu)
      inv_mem' := by
        rintro a ⟨haF, ha⟩
        refine ⟨f.F.inv_mem haF, fun u hu => ?_⟩
        have h1 := ha (a⁻¹ * u * a) (hFW' a haF u hu)
        have h2 : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ = (a * (a⁻¹ * u * a) * a⁻¹ * (a⁻¹ * u * a)⁻¹)⁻¹ := by group
        rw [h2]
        exact (zpowers e.s₁).inv_mem h1 }
  have hgK : g ∈ K0 := ⟨hg, hgW⟩
  have hK0F : K0 ≤ f.F := fun k hk => hk.1
  have hnorm : ∀ k ∈ f.F, ∀ n ∈ K0, k * n * k⁻¹ ∈ K0 := by
    rintro k hk n ⟨hnF, hn⟩
    refine ⟨f.F.mul_mem (f.F.mul_mem hk hnF) (f.F.inv_mem hk), fun u hu => ?_⟩
    have h1 := hn (k⁻¹ * u * k) (hFW' k hk u hu)
    have h2 : k * n * k⁻¹ * u * (k * n * k⁻¹)⁻¹ * u⁻¹ =
        k * (n * (k⁻¹ * u * k) * n⁻¹ * (k⁻¹ * u * k)⁻¹) * k⁻¹ := by group
    rw [h2, hcomm k hk _ h1]
    exact h1
  have hKne : K0 ≠ ⊥ := fun h => hg1 (mem_bot.mp (h ▸ hgK))
  have hzK : z ∈ K0 := f.F_socle K0 hK0F hnorm hKne
  intro w hw
  obtain ⟨c, hc, h1⟩ := z_inv_modF hz e f hw
  have h2 := hzK.2 w hw
  rw [h1] at h2
  have hsq : w⁻¹ * w⁻¹ ∈ zpowers e.s₁ := by
    have : w⁻¹ * w⁻¹ = (c * c)⁻¹ * (c * c * w⁻¹ * w⁻¹) := by group
    rw [this]
    exact (zpowers e.s₁).mul_mem ((zpowers e.s₁).inv_mem ((zpowers e.s₁).mul_mem hc hc)) h2
  have hww : w * w ∈ zpowers e.s₁ := by
    have : w * w = (w⁻¹ * w⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [this]
    exact (zpowers e.s₁).inv_mem hsq
  have hodd : Odd (orderOf w) :=
    Odd.of_dvd_nat (odd_card_oc _) (Subgroup.orderOf_dvd_natCard _ hw)
  obtain ⟨m, hm⟩ := hodd
  have hu1 : w = (w * w) ^ (m + 1) := by
    have : (w * w) ^ (m + 1) = w := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf w + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    exact this.symm
  rw [hu1]
  exact pow_mem hww _

end CFSG.GH74.Uniqueness.SU.SU13
