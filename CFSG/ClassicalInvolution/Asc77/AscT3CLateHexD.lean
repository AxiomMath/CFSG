module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexC
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Key

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem late_key (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {M₁ M₂ L T₁ : Subgroup G} {e a z s : G} (hM₁ : M₁ ∈ Ω) (hM₂ : M₂ ∈ Ω) (hne : M₁ ≠ M₂)
    (he₁ : IsUniqueInvolution M₁ e) (he₂ : IsUniqueInvolution M₂ e) (hL : L ∈ Ω)
    (ha : IsUniqueInvolution L a) (hea : e ≠ a) (hT : IsSylow2In T₁ L)
    (hTe : T₁ ≤ Subgroup.centralizer ({e} : Set G)) (hzM : z ∈ M₁ ⊔ M₂) (hs : s ∈ T₁)
    (hsz : s * z * s⁻¹ = z * a) (hza : z * a = a * z) : False := by
  have hΩg := hypOmegaGen_of_mod hp hq hΩ
  have hTR : T₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hL hT
  have hT8 := hΩ.eight_le_of_mem_RSet hp hTR
  have hTc := Sec71.not_isCyclic_of_mem_RSet hp hΩ hTR
  have h₁ := Sec71.comm_le_oddCore_of_centralizes hp hq hΩ hM₁ hL he₁ ha hea hT hTe hT8 hTc
  have h₂ := Sec71.comm_le_oddCore_of_centralizes hp hq hΩ hM₂ hL he₂ ha hea hT hTe hT8 hTc
  have hM₁N : M₁ ≤ Subgroup.normalizer (M₂ : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩg hM₁ hM₂ hne he₁ he₂
  have hM₂N : M₂ ≤ Subgroup.normalizer (M₁ : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩg hM₂ hM₁ hne.symm he₂ he₁
  rw [sup_comm] at hzM
  obtain ⟨y₂, hy₂, y₁, hy₁, hzy⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hM₁N hzM
  have hc₁ : ⁅s, y₁⁆ ∈ oddCoreOf M₁ := h₁ (Subgroup.commutator_mem_commutator hs hy₁)
  have hc₂ : ⁅s, y₂⁆ ∈ oddCoreOf M₂ := h₂ (Subgroup.commutator_mem_commutator hs hy₂)
  have hc₁' : y₂ * ⁅s, y₁⁆ * y₂⁻¹ ∈ oddCoreOf M₁ :=
    CFSG.ClassicalInvolution.Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer (hM₂N hy₂) hc₁
  have hconj : ∀ y : G, s * y * s⁻¹ = ⁅s, y⁆ * y := fun y => by
    rw [commutatorElement_def]; group
  have hszc : s * z * s⁻¹ = (⁅s, y₂⁆ * (y₂ * ⁅s, y₁⁆ * y₂⁻¹)) * z := by
    calc s * z * s⁻¹ = (s * y₂ * s⁻¹) * (s * y₁ * s⁻¹) := by rw [hzy]; group
      _ = (⁅s, y₂⁆ * y₂) * (⁅s, y₁⁆ * y₁) := by rw [hconj, hconj]
      _ = (⁅s, y₂⁆ * (y₂ * ⁅s, y₁⁆ * y₂⁻¹)) * (y₂ * y₁) := by group
      _ = _ := by rw [← hzy]
  have hac : a = ⁅s, y₂⁆ * (y₂ * ⁅s, y₁⁆ * y₂⁻¹) := by
    have h1 : a * z = (⁅s, y₂⁆ * (y₂ * ⁅s, y₁⁆ * y₂⁻¹)) * z := by
      rw [← hza, ← hsz, hszc]
    exact mul_right_cancel h1
  have hoddA : Odd (Nat.card ↥(oddCoreOf M₁)) := oddCoreOf_odd_natCard M₁
  have hoddB : Odd (Nat.card ↥(oddCoreOf M₂)) := oddCoreOf_odd_natCard M₂
  have hle : oddCoreOf M₁ ≤ Subgroup.normalizer (oddCoreOf M₂ : Set G) := fun g hg =>
    Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer
      (hM₁N (oddCoreOf_le_self M₁ hg))
  have hcard := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hle
  have hQ : Odd (Nat.card ↥(oddCoreOf M₁ ⊔ oddCoreOf M₂)) := by
    have : Odd (Nat.card ↥(oddCoreOf M₁ ⊔ oddCoreOf M₂) *
        Nat.card ↥(oddCoreOf M₁ ⊓ oddCoreOf M₂)) := by
      rw [hcard]
      exact hoddA.mul hoddB
    exact (Nat.odd_mul.mp this).1
  have haQ : a ∈ oddCoreOf M₁ ⊔ oddCoreOf M₂ := by
    rw [hac]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc₂) (Subgroup.mem_sup_left hc₁')
  exact ha.ne_one (eq_one_of_isPGroup_of_mem_odd hQ haQ
    (isPGroup_zpowers_of_mul_self_eq_one ha.sq ha.ne_one))

end Key

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace HexData

variable {d : Std20 p f K K' J S R R' W V z t} {u r v t₀ : G} {T : Subgroup G}
  (hh : HexData d u r v t₀ T)
include hh

theorem hrz' : r⁻¹ * z * r = z := by
  have h2 : r * z = z * r := by
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [hh.hrz]
  calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
    _ = r⁻¹ * (r * z) := by rw [h2]
    _ = z := by group

theorem hrt' : r⁻¹ * t * r = t * z := by
  have h1 : r⁻¹ * (t * z) * r = t := by rw [← hh.hrt]; group
  have h2 : r⁻¹ * (t * z) * r = (r⁻¹ * t * r) * (r⁻¹ * z * r) := by group
  rw [h2, hh.hrz'] at h1
  calc r⁻¹ * t * r = ((r⁻¹ * t * r) * z) * z := by
        rw [mul_assoc (r⁻¹ * t * r) z z, d.viol.hzK.sq, mul_one]
    _ = t * z := by rw [h1]

theorem hw_t : (r * t₀ * r⁻¹) * t * (r * t₀ * r⁻¹)⁻¹ = z := by
  calc (r * t₀ * r⁻¹) * t * (r * t₀ * r⁻¹)⁻¹ = r * t₀ * (r⁻¹ * t * r) * t₀⁻¹ * r⁻¹ := by group
    _ = r * t₀ * (t * z) * t₀⁻¹ * r⁻¹ := by rw [hh.hrt']
    _ = r * ((t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹)) * r⁻¹ := by group
    _ = r * (t * (z * t)) * r⁻¹ := by rw [hh.ht₀t, hh.htz]
    _ = r * z * r⁻¹ := by rw [d.late_zt_comm, ← mul_assoc t t z, d.viol.hzJ.sq, one_mul]
    _ = z := hh.hrz

theorem hw_z : (r * t₀ * r⁻¹) * z * (r * t₀ * r⁻¹)⁻¹ = t := by
  calc (r * t₀ * r⁻¹) * z * (r * t₀ * r⁻¹)⁻¹ = r * t₀ * (r⁻¹ * z * r) * t₀⁻¹ * r⁻¹ := by group
    _ = r * (t₀ * z * t₀⁻¹) * r⁻¹ := by rw [hh.hrz']; group
    _ = r * (z * t) * r⁻¹ := by rw [hh.htz]
    _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
    _ = z * (t * z) := by rw [hh.hrz, hh.hrt]
    _ = t := by rw [← d.late_zt_comm, ← mul_assoc, d.viol.hzK.sq, one_mul]

end HexData

theorem Std20.late_a_mem_Z (d : Std20 p f K K' J S R R' W V z t) {u r v t₀ : G}
    {T : Subgroup G} (hh : HexData d u r v t₀ T) {L₁ T₁ : Subgroup G} {a w₁ s₁ : G}
    (hL₁ : L₁ ∈ CoreAssembly.conjClass K) (ha : IsUniqueInvolution L₁ a) (haW : a ∈ W)
    (hd₁ : Sec71.DData (CoreAssembly.conjClass K) W T₁ L₁ w₁ s₁ a) :
    a = z ∨ a = t ∨ a = z * t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨haz, hat, hazt⟩ := hcon
  have hp := d.branch.odd
  have hq := d.branch.five
  have hΩ := d.hyp
  have hWc := d.late_hWc
  have hzW := d.late_z_mem_W
  have htW := d.late_t_mem_W
  have hKL : K ≠ L₁ := by
    intro h
    exact haz (d.viol.hzK.eq (h ▸ ha)).symm
  have hnot : L₁ ∉ omegaNbr (CoreAssembly.conjClass K) K := by
    intro h
    obtain ⟨-, z', hz', hz'L⟩ := d.late_nbr L₁ h
    exact haz ((ha.eq hz'L).trans (d.viol.hzK.eq hz').symm)
  obtain ⟨i₁, k₁, hio, hko, hi, hk, hra, hsz⟩ := late_pair hp hq hΩ hWc hh.hd hd₁ hKL
    (Ne.symm haz) hnot
  have hza : z * a = a * z := hWc z hzW a haW
  have hta : t * a = a * t := hWc t htW a haW
  obtain ⟨k₂, hk₂⟩ := hd₁.exists_rel hh.hd'.u_memW (hd₁.le_normalizer hh.hd'.u_memW)
  have hst := Sec71.conj_z_eq hΩ hh.hd' hd₁ hWc hk₂
  have hLsyl : IsSylow2In T₁ L₁ := hd₁.sylow
  have hT₁s : s₁ ∈ T₁ := hd₁.r_mem
  have hΩg := d.late_hΩ
  rcases Int.even_or_odd k₂ with hke | hko₂
  ·
    rw [Sec71.zpow_eq_one_of_even ha.sq hke, mul_one] at hst
    have hTt : T₁ ≤ Subgroup.centralizer ({t} : Set G) := hd₁.le_centralizer hWc htW hst
    set w : G := r * t₀ * r⁻¹ with hwdef
    have hwz : w * z * w⁻¹ = t := hh.hw_z
    have hwt : w * t * w⁻¹ = z := hh.hw_t
    have h1 : IsUniqueInvolution (conjSub w K) t := hwz ▸ d.viol.hzK.conj w
    have h2 : IsUniqueInvolution (conjSub w K') t := hwz ▸ d.late_hzK'.conj w
    have hzM : z ∈ conjSub w K ⊔ conjSub w K' := by
      rw [← late_conjSub_sup, mem_conjSub_iff]
      have : w⁻¹ * z * w = t := by
        calc w⁻¹ * z * w = w⁻¹ * (w * t * w⁻¹) * w := by rw [hwt]
          _ = t := by group
      rw [this]
      exact d.htKK
    exact late_key hp hq hΩ (d.hyp.conjInvariant w K d.late_mem_K)
      (d.hyp.conjInvariant w K' d.late_mem_K') (fun h => d.ne (conjSub_injective w h).symm) h1 h2
      hL₁ ha (Ne.symm hat) hLsyl hTt hzM hT₁s hsz hza
  ·
    rw [Sec71.zpow_eq_self_of_odd ha.sq hko₂] at hst
    have hszt : s₁ * (z * t) * s₁⁻¹ = z * t := by
      calc s₁ * (z * t) * s₁⁻¹ = (s₁ * z * s₁⁻¹) * (s₁ * t * s₁⁻¹) := by group
        _ = (z * a) * (t * a) := by rw [hsz, hst]
        _ = z * (a * t) * a := by group
        _ = z * (t * a) * a := by rw [hta]
        _ = z * t := by rw [mul_assoc, mul_assoc, ha.sq, mul_one]
    have hTzt : T₁ ≤ Subgroup.centralizer ({z * t} : Set G) :=
      hd₁.le_centralizer hWc (W.mul_mem hzW htW) hszt
    have hwz : t₀ * (z * t) * t₀⁻¹ = z := by
      calc t₀ * (z * t) * t₀⁻¹ = (t₀ * z * t₀⁻¹) * (t₀ * t * t₀⁻¹) := by group
        _ = (z * t) * t := by rw [hh.htz, hh.ht₀t]
        _ = z := by rw [mul_assoc, d.viol.hzJ.sq, mul_one]
    have h1 : IsUniqueInvolution (conjSub t₀ K) (z * t) := hh.htz ▸ d.viol.hzK.conj t₀
    have h2 : IsUniqueInvolution (conjSub t₀ K') (z * t) := hh.htz ▸ d.late_hzK'.conj t₀
    have hzM : z ∈ conjSub t₀ K ⊔ conjSub t₀ K' := by
      rw [← late_conjSub_sup, mem_conjSub_iff]
      have : t₀⁻¹ * z * t₀ = z * t := by
        calc t₀⁻¹ * z * t₀ = t₀⁻¹ * (t₀ * (z * t) * t₀⁻¹) * t₀ := by rw [hwz]
          _ = z * t := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left d.viol.hzK.mem) d.htKK
    exact late_key hp hq hΩ (d.hyp.conjInvariant t₀ K d.late_mem_K)
      (d.hyp.conjInvariant t₀ K' d.late_mem_K') (fun h => d.ne (conjSub_injective t₀ h).symm)
      h1 h2 hL₁ ha (Ne.symm hazt) hLsyl hTzt hzM hT₁s hsz hza

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
