module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Cop
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S8
public import Certificates.Certificate2007
public import Certificates.Certificate2013

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.GH74.KGroups
open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}

theorem conj_c_mem_normalizer (d : H₁.Data) {u : H}
    (hu : u ∈ centralizer ({h.a * d.sigma} : Set H)) :
    h.x * d.g * u * (h.x * d.g)⁻¹ ∈ normalizer (h.K : Set H) := by
  set c := h.x * d.g with hc
  have hb : c * u * c⁻¹ * d.b = d.b * (c * u * c⁻¹) := by
    rw [← d.conj_c_asigma, ← hc]
    have h1 := mem_centralizer_singleton_iff.mp hu
    calc c * u * c⁻¹ * (c * (h.a * d.sigma) * c⁻¹) = c * (u * (h.a * d.sigma)) * c⁻¹ := by group
      _ = c * ((h.a * d.sigma) * u) * c⁻¹ := by rw [h1]
      _ = c * (h.a * d.sigma) * c⁻¹ * (c * u * c⁻¹) := by group
  have hB : c * u * c⁻¹ ∈ normalizer (h.B : Set H) := by
    rw [d.B_eq]
    refine Eight.le_normalizer_of_commute₂ (A := zpowers d.b) (B := zpowers (c * u * c⁻¹))
      (fun x hx y hy => ?_) (mem_zpowers _)
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hb.symm i j).eq
  exact H₁.kloc.normalizer_le_normalizer_K hB

noncomputable abbrev psiC (M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8) (d : H₁.Data) (u : H)
    (hu : u ∈ centralizer ({h.a * d.sigma} : Set H)) : P8 :=
  psi M ⟨h.x * d.g * u * (h.x * d.g)⁻¹, conj_c_mem_normalizer d hu⟩

variable {M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8} {d : H₁.Data}

theorem psiC_mul {u v : H} (hu : u ∈ centralizer ({h.a * d.sigma} : Set H))
    (hv : v ∈ centralizer ({h.a * d.sigma} : Set H)) :
    psiC M d (u * v) (mul_mem hu hv) = psiC M d u hu * psiC M d v hv := by
  have he : (⟨h.x * d.g * (u * v) * (h.x * d.g)⁻¹, conj_c_mem_normalizer d (mul_mem hu hv)⟩ :
      normalizer (h.K : Set H)) = ⟨h.x * d.g * u * (h.x * d.g)⁻¹, conj_c_mem_normalizer d hu⟩ *
        ⟨h.x * d.g * v * (h.x * d.g)⁻¹, conj_c_mem_normalizer d hv⟩ := by
    apply Subtype.ext
    change h.x * d.g * (u * v) * (h.x * d.g)⁻¹ =
      h.x * d.g * u * (h.x * d.g)⁻¹ * (h.x * d.g * v * (h.x * d.g)⁻¹)
    group
  change psi M _ = psi M _ * psi M _
  rw [he, map_mul]

theorem psiC_inv {u : H} (hu : u ∈ centralizer ({h.a * d.sigma} : Set H)) :
    psiC M d u⁻¹ (inv_mem hu) = (psiC M d u hu)⁻¹ := by
  have he : (⟨h.x * d.g * u⁻¹ * (h.x * d.g)⁻¹, conj_c_mem_normalizer d (inv_mem hu)⟩ :
      normalizer (h.K : Set H)) =
        (⟨h.x * d.g * u * (h.x * d.g)⁻¹, conj_c_mem_normalizer d hu⟩)⁻¹ := by
    apply Subtype.ext
    change h.x * d.g * u⁻¹ * (h.x * d.g)⁻¹ = (h.x * d.g * u * (h.x * d.g)⁻¹)⁻¹
    group
  change psi M _ = (psi M _)⁻¹
  rw [he, map_inv]

theorem psiC_eq_one_iff {u : H} (hu : u ∈ centralizer ({h.a * d.sigma} : Set H)) :
    psiC M d u hu = 1 ↔ h.x * d.g * u * (h.x * d.g)⁻¹ ∈ coreActionKernel h.K :=
  psi_eq_one_iff _

theorem card_le_two_of_psiC {X : Subgroup H} (hX : IsPGroup 2 X)
    (hXC : X ≤ centralizer ({h.a * d.sigma} : Set H))
    (hX1 : ∀ u (hu : u ∈ X), psiC M d u (hXC hu) = 1) : Nat.card X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, R, hR⟩ := H₁.B_sylow_kernel
  have hle : conjugate X (h.x * d.g)⁻¹ ≤ coreActionKernel h.V := by
    rw [H₁.kloc.V_eq_K]
    intro w hw
    rw [mem_conjugate_iff, inv_inv] at hw
    have h1 := (psiC_eq_one_iff (M := M) (hXC hw)).mp (hX1 _ hw)
    rwa [show h.x * d.g * ((h.x * d.g)⁻¹ * w * (h.x * d.g)) * (h.x * d.g)⁻¹ = w by group]
      at h1
  have h2 := card_le_of_sylow_subgroupOf ⟨R, hR⟩ hle (hX.map _)
  have hB2 : Nat.card h.B = 2 := by rw [d.B_eq, Nat.card_zpowers, d.b_ord]
  rw [Eight.card_conjugate_eq] at h2
  exact h2.trans hB2.le

theorem mem_C_of_comm {w : H} (ha : w * h.a = h.a * w) (hσ : w * d.sigma = d.sigma * w) :
    w ∈ centralizer ({h.a * d.sigma} : Set H) := by
  rw [mem_centralizer_singleton_iff]
  calc w * (h.a * d.sigma) = (w * h.a) * d.sigma := (mul_assoc _ _ _).symm
    _ = h.a * (w * d.sigma) := by rw [ha, mul_assoc]
    _ = h.a * d.sigma * w := by rw [hσ, ← mul_assoc]

theorem a_mem_C : h.a ∈ centralizer ({h.a * d.sigma} : Set H) :=
  mem_C_of_comm rfl (h.toHyp52.comm_a d.sigma_mem_S).symm

theorem b_mem_C : d.b ∈ centralizer ({h.a * d.sigma} : Set H) :=
  mem_C_of_comm d.a_comm_b.symm d.sigma_comm_b.symm

theorem mem_C_of_mem_P (I : In81) (F : d.Facts)
    (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma) {π : H} (hπ : π ∈ h.P) :
    π ∈ centralizer ({h.a * d.sigma} : Set H) :=
  mem_C_of_comm (h.toHyp52.comm_a (mem_inf.mp hπ).1)
    (Hyp59.L81Hyp.Data.sigma_comm_P I F h3 hπ).symm

theorem mem_C_of_mem_D (F : d.Facts) {e : H} (he : e ∈ h.D) :
    e ∈ centralizer ({h.a * d.sigma} : Set H) :=
  mem_C_of_comm (h.toHyp52.comm_a (h.toHyp52.D_le_S he))
    (Hyp59.L81Hyp.Data.D_comm_sigma F e he d.sigma (mem_zpowers _))

theorem psiC_a (I : In81) (F : d.Facts) :
    psiC M d h.a a_mem_C = psi M ⟨d.tau, le_normalizer d.tau_K⟩ := by
  have he : (⟨h.x * d.g * h.a * (h.x * d.g)⁻¹, conj_c_mem_normalizer d a_mem_C⟩ :
      normalizer (h.K : Set H)) = ⟨d.tau, le_normalizer d.tau_K⟩ :=
    Subtype.ext (d.conj_c_a I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F)
  change psi M _ = _
  rw [he]

theorem psi_b :
    psi M ⟨d.b, H₁.kloc.normalizer_le_normalizer_K (le_normalizer d.b_mem_B)⟩ = 1 := by
  rw [psi_eq_one_iff]
  have h1 := H₁.B_sylow_kernel.1 d.b_mem_B
  rw [H₁.kloc.V_eq_K] at h1
  exact h1

theorem psiC_b (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) : psiC M d d.b b_mem_C = s8 := by
  have he : (⟨h.x * d.g * d.b * (h.x * d.g)⁻¹, conj_c_mem_normalizer d b_mem_C⟩ :
      normalizer (h.K : Set H)) = ⟨h.a, H₁.kloc.a_mem_normalizer_K⟩ *
        ⟨d.b, H₁.kloc.normalizer_le_normalizer_K (le_normalizer d.b_mem_B)⟩ := by
    apply Subtype.ext
    change h.x * d.g * d.b * (h.x * d.g)⁻¹ = h.a * d.b
    rw [show h.x * d.g * d.b * (h.x * d.g)⁻¹ = h.x * (d.g * d.b * d.g⁻¹) * h.x⁻¹ by group,
      d.comm_b_of_mem_M3 d.g_M, mul_inv_cancel_right, d.x_b_x_inv]
  change psi M _ = _
  rw [he, map_mul, psi_a H₁ hΦ, psi_b, mul_one]

theorem conj_mem_coreActionKernel {w n : H} (hw : w ∈ normalizer (h.K : Set H))
    (hn : n ∈ coreActionKernel h.K) : w * n * w⁻¹ ∈ coreActionKernel h.K := by
  have hnN : n ∈ normalizer (h.K : Set H) := (mem_coreActionKernel.mp hn).1
  have h1 : (⟨n, hnN⟩ : normalizer (h.K : Set H)) ∈ (Eight.oddBarAction h.K).ker :=
    Eight.mem_ker_oddBarAction.mpr hn
  exact Eight.mem_ker_oddBarAction.mp
    ((Eight.oddBarAction h.K).normal_ker.conj_mem _ h1 ⟨w, hw⟩)

theorem fused_of_psiC (I : In81) (F : d.Facts) (hP : M.P = QA8.originalSubgroup)
    (hA : M.A = QS8.originalSubgroup) {u : H}
    (hu : u ∈ centralizer ({h.a * d.sigma} : Set H)) (hu2 : u * u = 1) {π : Equiv.Perm (Fin 8)}
    (hπ : π ∈ QA8.originalSubgroup)
    (heq : psiC M d u hu = π * psi M ⟨d.tau, le_normalizer d.tau_K⟩ * π⁻¹) :
    (∃ w : H, w⁻¹ * h.a * w = u) ∨ (∃ w : H, w⁻¹ * d.sigma * w = u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := h.x * d.g with hc
  obtain ⟨k, hk, hkπ⟩ := exists_K_of_mem_A8 hP hA hπ
  have hkb : k * d.b = d.b * k := d.comm_b_of_mem_M3 (mem_sup_left hk)
  have hτb : d.tau * d.b = d.b * d.tau := d.tau_comm_b
  set u' := k * d.tau * k⁻¹ with hu'
  have hu'K : u' ∈ h.K := mul_mem (mul_mem hk d.tau_K) (inv_mem hk)
  have hu'ψ : psi M ⟨u', le_normalizer hu'K⟩ = π * psi M ⟨d.tau, le_normalizer d.tau_K⟩ * π⁻¹ := by
    rw [show (⟨u', le_normalizer hu'K⟩ : normalizer (h.K : Set H)) = ⟨k, le_normalizer hk⟩ *
      ⟨d.tau, le_normalizer d.tau_K⟩ * ⟨k, le_normalizer hk⟩⁻¹ from rfl, map_mul, map_mul,
      map_inv, hkπ]
  set U := c * u * c⁻¹ with hU
  have hUN : U ∈ normalizer (h.K : Set H) := conj_c_mem_normalizer d hu
  have hUψ : psi M ⟨U, hUN⟩ = π * psi M ⟨d.tau, le_normalizer d.tau_K⟩ * π⁻¹ := heq
  have hτ1 := psi_tau_ne_one (M := M) I.cf1 I.cf2 F
  have hne1 : π * psi M ⟨d.tau, le_normalizer d.tau_K⟩ * π⁻¹ ≠ 1 := fun h1 => hτ1 (by
    calc psi M ⟨d.tau, le_normalizer d.tau_K⟩ =
        π⁻¹ * (π * psi M ⟨d.tau, le_normalizer d.tau_K⟩ * π⁻¹) * π := by group
      _ = 1 := by rw [h1]; group)
  set N : Subgroup H := centralizer ({d.b} : Set H) ⊓ coreActionKernel h.K with hN
  obtain ⟨-, R, hR⟩ := H₁.B_sylow_kernel
  have hB2 : Nat.card h.B = 2 := by rw [d.B_eq, Nat.card_zpowers, d.b_ord]
  have hNle : ∀ X : Subgroup H, X ≤ N → IsPGroup 2 X → Nat.card X ≤ 2 := by
    intro X hXN hX
    have hle : X ≤ coreActionKernel h.V := by
      rw [H₁.kloc.V_eq_K]
      exact hXN.trans inf_le_right
    exact (card_le_of_sylow_subgroupOf ⟨R, hR⟩ hle hX).trans hB2.le
  have hbK : d.b ∈ coreActionKernel h.K :=
    (psi_eq_one_iff _).mp (psi_b (M := M))
  have hk'b : k⁻¹ * d.b = d.b * k⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hkb, mul_inv_cancel_right]
  have hu'C : u' ∈ centralizer ({d.b} : Set H) := mem_centralizer_singleton_iff.mpr (by
    calc u' * d.b = k * d.tau * (k⁻¹ * d.b) := by rw [hu']; group
      _ = k * d.tau * (d.b * k⁻¹) := by rw [hk'b]
      _ = k * (d.tau * d.b) * k⁻¹ := by group
      _ = k * (d.b * d.tau) * k⁻¹ := by rw [hτb]
      _ = (k * d.b) * d.tau * k⁻¹ := by group
      _ = d.b * u' := by rw [hkb, hu']; group)
  have hUC : U ∈ centralizer ({d.b} : Set H) := mem_centralizer_singleton_iff.mpr (by
    rw [hU, ← d.conj_c_asigma, ← hc]
    have h1 := mem_centralizer_singleton_iff.mp hu
    calc c * u * c⁻¹ * (c * (h.a * d.sigma) * c⁻¹) = c * (u * (h.a * d.sigma)) * c⁻¹ := by
          group
      _ = c * ((h.a * d.sigma) * u) * c⁻¹ := by rw [h1]
      _ = c * (h.a * d.sigma) * c⁻¹ * (c * u * c⁻¹) := by group)
  have hu'N : u' ∈ normalizer (N : Set H) := by
    refine Eight.mem_normalizer_of_conj_mem fun w hw => mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem hu'C) hw.1) hu'C
    · have := conj_mem_coreActionKernel (inv_mem (le_normalizer hu'K)) hw.2
      rwa [inv_inv] at this
  have hmem : u'⁻¹ * U ∈ N := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hu'C) hUC, ?_⟩
    have h1 : psi M ⟨u'⁻¹ * U, mul_mem (inv_mem (le_normalizer hu'K)) hUN⟩ = 1 := by
      rw [show (⟨u'⁻¹ * U, mul_mem (inv_mem (le_normalizer hu'K)) hUN⟩ :
          normalizer (h.K : Set H)) = (⟨u', le_normalizer hu'K⟩)⁻¹ * ⟨U, hUN⟩ from rfl,
        map_mul, map_inv, hu'ψ, hUψ, inv_mul_cancel]
    exact (psi_eq_one_iff _).mp h1
  have hu'n : u' ∉ N := fun h1 => hne1 (by rw [← hu'ψ]; exact (psi_eq_one_iff _).mpr h1.2)
  have hU1 : U ≠ 1 := fun h1 => hne1 (by
    rw [← hUψ, psi_eq_one_iff]
    change U ∈ coreActionKernel h.K
    rw [h1]
    exact one_mem _)
  have hUb : U ≠ d.b := fun h1 => hne1 (by
    rw [← hUψ, psi_eq_one_iff]
    change U ∈ coreActionKernel h.K
    rw [h1]
    exact hbK)
  have hU2 : U * U = 1 := by
    rw [hU, show c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ by group, hu2]
    group
  have hu'2 : u' * u' = 1 := by
    rw [hu', show k * d.tau * k⁻¹ * (k * d.tau * k⁻¹) = k * (d.tau * d.tau) * k⁻¹ by group,
      d.tau_sq]
    group
  have hb1 : d.b ≠ 1 := fun h1 => by
    have := d.b_ord
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨y, hy | hy⟩ := exists_conj_of_mul_mem d.b_mul_self hb1
    (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hbK⟩) hNle
    (fun n hn => mem_centralizer_singleton_iff.mp hn.1) hU2 hu'2 hu'N
    (mem_centralizer_singleton_iff.mp hu'C) hmem hu'n hU1 hUb
  · left
    refine ⟨c⁻¹ * k⁻¹ * y * c, ?_⟩
    have hca := d.conj_c_a I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
    rw [← hc] at hca
    calc (c⁻¹ * k⁻¹ * y * c)⁻¹ * h.a * (c⁻¹ * k⁻¹ * y * c) =
        c⁻¹ * y⁻¹ * (k * (c * h.a * c⁻¹) * k⁻¹) * y * c := by group
      _ = c⁻¹ * y⁻¹ * (y * U * y⁻¹) * y * c := by rw [hca, ← hu', hy]
      _ = u := by rw [hU]; group
  · right
    refine ⟨c⁻¹ * k⁻¹ * y * c, ?_⟩
    have hcs := d.conj_c_sigma I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
    rw [← hc] at hcs
    have hσ : k * d.sigma * k⁻¹ = u' * d.b := by
      show k * (d.tau * d.b) * k⁻¹ = k * d.tau * k⁻¹ * d.b
      rw [show k * d.tau * k⁻¹ * d.b = k * d.tau * (k⁻¹ * d.b) by group, hk'b]
      group
    calc (c⁻¹ * k⁻¹ * y * c)⁻¹ * d.sigma * (c⁻¹ * k⁻¹ * y * c) =
        c⁻¹ * y⁻¹ * (k * (c * d.sigma * c⁻¹) * k⁻¹) * y * c := by group
      _ = c⁻¹ * y⁻¹ * (u' * d.b) * y * c := by rw [hcs, hσ]
      _ = c⁻¹ * y⁻¹ * (y * U * y⁻¹) * y * c := by rw [hy]
      _ = u := by rw [hU]; group

end CFSG.ComponentClassification.GSThmB.A8
