module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Frame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec113_conj_zpowers {z c w : G} (hc : c * z = z * c) (hw : w ∈ zpowers z) :
    c * w * c⁻¹ = w := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h : Commute c (z ^ n) := (Commute.zpow_right (show Commute c z from hc) n)
  rw [h.eq]
  group

namespace Sec113Frame

variable {z : G} {K0 N K1 K2 Q1 Q2 : Subgroup G} (F : Sec113Frame z K0 N K1 K2 Q1 Q2)

include F

theorem q_acts_triv {q w : G} (hq : q ∈ Q1 ⊔ Q2) (hw : w ∈ Q1) :
    q * w * q⁻¹ * w⁻¹ ∈ zpowers z := by
  obtain ⟨q1, hq1, q2, hq2, rfl⟩ := F.pair.exists_mul_of_mem_sup hq
  have h1 : q2 * w = w * q2 := (F.pair.comm w hw q2 hq2).symm
  have h2 : q1 * q2 * w * (q1 * q2)⁻¹ * w⁻¹ = q1 * w * q1⁻¹ * w⁻¹ := by
    calc q1 * q2 * w * (q1 * q2)⁻¹ * w⁻¹ = q1 * (q2 * w) * q2⁻¹ * q1⁻¹ * w⁻¹ := by group
      _ = q1 * (w * q2) * q2⁻¹ * q1⁻¹ * w⁻¹ := by rw [h1]
      _ = q1 * w * q1⁻¹ * w⁻¹ := by group
  rw [h2]
  exact (F.pair.elem1 q1 hq1 w hw).1

theorem normalizes {x : G} (hx2 : x * x = 1) (hxK0 : x ∈ normalizer (K0 : Set G))
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxQ2 : ∀ q ∈ Q2, x * q * x⁻¹ ∈ Q2) :
    x ∈ normalizer ((K1 ⊔ N : Subgroup G) : Set G) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have key : ∀ k ∈ K1 ⊔ N, x * k * x⁻¹ ∈ K1 ⊔ N := by
    intro k hk
    obtain ⟨hk0, hkq⟩ := F.mem_sup_iff.mp hk
    refine F.mem_sup_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hxK0 k).mp hk0, fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x ∈ Q2 := by
      have := hxQ2 q hq
      rwa [hxinv] at this ⊢
    have h1 := hxN _ (hkq _ hq')
    have h2 : x * (k * (x⁻¹ * q * x) * k⁻¹ * (x⁻¹ * q * x)⁻¹) * x⁻¹ =
        x * k * x⁻¹ * q * (x * k * x⁻¹)⁻¹ * q⁻¹ := by group
    rwa [h2] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key k, fun hk => ?_⟩
  have h := key _ hk
  have e : x * (x * k * x⁻¹) * x⁻¹ = k := by
    calc x * (x * k * x⁻¹) * x⁻¹ = (x * x) * k * (x * x)⁻¹ := by group
      _ = k := by rw [hx2]; group
  rwa [e] at h

theorem isOuterOn {x : G} (hx2 : x * x = 1) (hxK0 : x ∈ normalizer (K0 : Set G))
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxQ1 : ∀ q ∈ Q1, x * q * x⁻¹ ∈ Q1)
    (hxQ2 : ∀ q ∈ Q2, x * q * x⁻¹ ∈ Q2) (hnt : ¬ ActsTrivModZ z x Q1) :
    IsOuterOn x (K1 ⊔ N) N := by
  refine ⟨F.normalizes hx2 hxK0 hxN hxQ2, ?_⟩
  rintro ⟨k, hk, hall⟩
  obtain ⟨n, hn, k1, hk1, rfl⟩ := F.exists_of_mem_sup hk
  apply hnt
  have hact : ∀ y ∈ Q1, x * y * x⁻¹ = k1 * y * k1⁻¹ := by
    intro y hy
    have hyK1 : y ∈ K1 := F.Q1_le hy
    have hu : x * y * x⁻¹ ∈ Q1 := hxQ1 y hy
    have hv : k1 * y * k1⁻¹ ∈ Q1 := F.Q1_norm k1 hk1 y hy
    have hvK0 : k1 * y * k1⁻¹ ∈ K0 := F.K1_le (F.Q1_le hv)
    have h1 := hall y (Subgroup.mem_sup_left hyK1)
    have h2 : (n * k1) * y * (n * k1)⁻¹ * (k1 * y * k1⁻¹)⁻¹ ∈ N := by
      have h3 := F.N_norm _ hvK0 n⁻¹ (N.inv_mem hn)
      have h4 := N.mul_mem hn h3
      have e : (n * k1) * y * (n * k1)⁻¹ * (k1 * y * k1⁻¹)⁻¹ =
          n * ((k1 * y * k1⁻¹) * n⁻¹ * (k1 * y * k1⁻¹)⁻¹) := by group
      rw [e]
      exact h4
    have h5 : x * y * x⁻¹ * (k1 * y * k1⁻¹)⁻¹ ∈ N := by
      have h6 := N.mul_mem h1 h2
      have e : x * y * x⁻¹ * ((n * k1) * y * (n * k1)⁻¹)⁻¹ *
          ((n * k1) * y * (n * k1)⁻¹ * (k1 * y * k1⁻¹)⁻¹) =
          x * y * x⁻¹ * (k1 * y * k1⁻¹)⁻¹ := by group
      rw [← e]
      exact h6
    have h7 : x * y * x⁻¹ * (k1 * y * k1⁻¹)⁻¹ ∈ Q1 ⊔ Q2 :=
      Subgroup.mem_sup_left (Q1.mul_mem hu (Q1.inv_mem hv))
    exact mul_inv_eq_one.mp (F.Q_inf_N _ h7 h5)
  obtain ⟨q, hq, c, hc, hc3, rfl⟩ := F.pocket1 k1 hk1
  have hcz : c * z = z * c := F.z_comm1 c hc
  have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have hcE : ∀ u v : G, u * v⁻¹ ∈ zpowers z → (c * u * c⁻¹) * (c * v * c⁻¹)⁻¹ ∈ zpowers z := by
    intro u v h
    have e : (c * u * c⁻¹) * (c * v * c⁻¹)⁻¹ = c * (u * v⁻¹) * c⁻¹ := by group
    rw [e, sec113_conj_zpowers hcz h]
    exact h
  have hH1 : ∀ y ∈ Q1, (x * y * x⁻¹) * (c * y * c⁻¹)⁻¹ ∈ zpowers z := by
    intro y hy
    have hw : c * y * c⁻¹ ∈ Q1 := F.Q1_norm c hc y hy
    have h1 := F.q_acts_triv hq hw
    rw [hact y hy]
    have e : q * c * y * (q * c)⁻¹ * (c * y * c⁻¹)⁻¹ =
        q * (c * y * c⁻¹) * q⁻¹ * (c * y * c⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  intro y hy
  set y1 := x * y * x⁻¹ with hy1
  have hy1Q : y1 ∈ Q1 := hxQ1 y hy
  have hxy1 : x * y1 * x⁻¹ = y := by
    rw [hy1]
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hx2]; group
  have hbyQ : c * y * c⁻¹ ∈ Q1 := F.Q1_norm c hc y hy
  have e1 : y1 * (c * y * c⁻¹)⁻¹ ∈ zpowers z := hH1 y hy
  have e2 : y * (c * y1 * c⁻¹)⁻¹ ∈ zpowers z := by
    have := hH1 y1 hy1Q
    rwa [hxy1] at this
  have e3 : (c * y1 * c⁻¹) * (c * (c * y * c⁻¹) * c⁻¹)⁻¹ ∈ zpowers z := hcE _ _ e1
  have e4 : y * (c * (c * y * c⁻¹) * c⁻¹)⁻¹ ∈ zpowers z := by
    have := (zpowers z).mul_mem e2 e3
    have e : y * (c * y1 * c⁻¹)⁻¹ * ((c * y1 * c⁻¹) * (c * (c * y * c⁻¹) * c⁻¹)⁻¹) =
        y * (c * (c * y * c⁻¹) * c⁻¹)⁻¹ := by group
    rwa [e] at this
  have e5 : (c * y * c⁻¹) * (c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹)⁻¹ ∈ zpowers z := hcE _ _ e4
  have e6 : c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ = y := by
    calc c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * y * (c * c * c)⁻¹ := by group
      _ = y := by rw [hc3']; group
  rw [e6] at e5
  have e7 : y1 * y⁻¹ ∈ zpowers z := by
    have := (zpowers z).mul_mem e1 e5
    have e : y1 * (c * y * c⁻¹)⁻¹ * ((c * y * c⁻¹) * y⁻¹) = y1 * y⁻¹ := by group
    rwa [e] at this
  exact e7

end Sec113Frame

end CFSG.OddStandard.SmallF3.Omega
