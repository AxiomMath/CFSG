module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Step
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Core8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Main

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem Std20Frame.exists_inZ_of_mem_M
    (hcore : ∀ {b g : G}, b ∈ R ⊔ R' → b * b = 1 → g * z * g⁻¹ = b → InZ z t b) {c g : G}
    (hcM : c ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K'))
    (hc2 : c * c = 1) (hg : g * z * g⁻¹ = c) :
    ∃ y : G, InZ z t y ∧ y⁻¹ * c ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') := by
  obtain ⟨r, hr, o, ho, rfl⟩ := d.exists_mul_oddCore_of_mem_M hcM
  have hrS : r ∈ (S : Subgroup G) := (sup_le d.hRS d.hR'S) hr
  have hrX : r ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) hr
  have hr2 : r * r = 1 := by
    have h1 : r * r ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') := by
      have e1 : r * r = ((r⁻¹ * o * r) * o)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc r * r * (r⁻¹ * o * r * o) = (r * o) * (r * o) := by group
          _ = 1 := hc2
      rw [e1]
      have h2 := mem_normalizer_oddCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer (Subgroup.inv_mem _ hrX)) ho
      rw [inv_inv] at h2
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ h2 ho)
    exact eq_one_of_mem_oddCoreOf_of_mem S.isPGroup' h1 (Subgroup.mul_mem _ hrS hrS)
  obtain ⟨q, hq⟩ := exists_conj_of_mul_odd hr2 (TwinExact.odd_orderOf_of_mem_oddCoreOf ho) hc2
  have hrg : (q * g) * z * (q * g)⁻¹ = r := by
    calc (q * g) * z * (q * g)⁻¹ = q * (g * z * g⁻¹) * q⁻¹ := by group
      _ = q * (q⁻¹ * r * q) * q⁻¹ := by rw [hg, hq]
      _ = r := by group
  refine ⟨r, hcore hr hr2 hrg, ?_⟩
  rw [inv_mul_cancel_left]
  exact ho

theorem Std20Frame.conj_not_mem_M
    (hcore : ∀ {b g : G}, b ∈ R ⊔ R' → b * b = 1 → g * z * g⁻¹ = b → InZ z t b) {h g : G}
    (hS : h⁻¹ * z * h ∈ (S : Subgroup G)) (hsZ : ¬ InZ z t (h⁻¹ * z * h))
    (hgZ : ∀ y, InZ z t y → InZ z t (g * y * g⁻¹)) :
    g⁻¹ * (h⁻¹ * z * h) * g ∉
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') := by
  intro hM
  have hs2 : (g⁻¹ * (h⁻¹ * z * h) * g) * (g⁻¹ * (h⁻¹ * z * h) * g) = 1 := by
    calc (g⁻¹ * (h⁻¹ * z * h) * g) * (g⁻¹ * (h⁻¹ * z * h) * g) =
          g⁻¹ * h⁻¹ * (z * z) * h * g := by group
      _ = 1 := by rw [d.viol.hzK.sq]; group
  obtain ⟨y, hy, hyo⟩ := d.exists_inZ_of_mem_M hcore hM hs2 (g := g⁻¹ * h⁻¹) (by group)
  have hgy := hgZ y hy
  have e1 : g * (y⁻¹ * (g⁻¹ * (h⁻¹ * z * h) * g)) * g⁻¹ = (g * y * g⁻¹)⁻¹ * (h⁻¹ * z * h) := by
    group
  have h1 : g * (y⁻¹ * (g⁻¹ * (h⁻¹ * z * h) * g)) * g⁻¹ ∈ (S : Subgroup G) := by
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (d.mem_S_of_inZ hgy)) hS
  have h2 : g * (y⁻¹ * (g⁻¹ * (h⁻¹ * z * h) * g)) * g⁻¹ ∈
      oddCoreOf (conjSub g (sec20X (CoreAssembly.conjClass K) z K K')) := by
    rw [Thompson.oddCoreOf_conjSub_eq]
    exact conj_mem_conjSub hyo
  have h3 := eq_one_of_mem_oddCoreOf_of_mem S.isPGroup' h2 h1
  rw [e1] at h3
  apply hsZ
  rw [← inv_mul_eq_one.mp h3]
  exact hgy

theorem Std20Frame.closed_of_concl203_of_core (c8 : Concl20_8 S K' R) (c3 : Concl20_3 K K' V z)
    (hcore : ∀ {b g : G}, b ∈ R ⊔ R' → b * b = 1 → g * z * g⁻¹ = b → InZ z t b) {h : G}
    (hS : h⁻¹ * z * h ∈ (S : Subgroup G)) : h⁻¹ * z * h ∈ Subgroup.closure ({t, z} : Set G) := by
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzt : z * t = t * z := d.late_zt_comm
  rw [mem_closure_pair_iff_inZ hz2 d.viol.hzJ.sq hzt]
  by_contra hsZ
  have hs2 : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz2]; group
  have hsM := d.conj_not_mem_M hcore hS hsZ (g := 1) (fun y hy => by simpa using hy)
  simp only [inv_one, one_mul, mul_one] at hsM
  have hst := d.comm_t_of_not_mem_M c8 c3 hS hs2 (g := h⁻¹) (by rw [inv_inv]) hsM
  have hsz : (h⁻¹ * z * h) * z = z * (h⁻¹ * z * h) :=
    Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hS)
  have hcomm : ∀ y, InZ z t y → (h⁻¹ * z * h) * y = y * (h⁻¹ * z * h) := by
    rintro y (rfl | rfl | rfl | rfl)
    · simp
    · exact hsz
    · exact hst
    · calc (h⁻¹ * z * h) * (z * t) = ((h⁻¹ * z * h) * z) * t := by group
        _ = z * ((h⁻¹ * z * h) * t) := by rw [hsz]; group
        _ = z * (t * (h⁻¹ * z * h)) := by rw [hst]
        _ = (z * t) * (h⁻¹ * z * h) := by group
  obtain ⟨ρ, hρz, hρt⟩ := d.exists_hex_rho
  have hρzt : ρ * (z * t) * ρ⁻¹ = t := by
    calc ρ * (z * t) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * t * ρ⁻¹) := by group
      _ = t := by rw [hρz, hρt, mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
  have hρZ : ∀ y, InZ z t y → InZ z t (ρ * y * ρ⁻¹) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inl (by group)
    · exact Or.inr (Or.inr (Or.inr hρz))
    · exact Or.inr (Or.inl hρt)
    · exact Or.inr (Or.inr (Or.inl hρzt))
  have hρρZ : ∀ y, InZ z t y → InZ z t ((ρ * ρ) * y * (ρ * ρ)⁻¹) := fun y hy => by
    have := hρZ _ (hρZ y hy)
    rwa [show ρ * (ρ * y * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * y * (ρ * ρ)⁻¹ by group] at this
  have hρρz : (ρ * ρ) * z * (ρ * ρ)⁻¹ = t := by
    calc (ρ * ρ) * z * (ρ * ρ)⁻¹ = ρ * (ρ * z * ρ⁻¹) * ρ⁻¹ := by group
      _ = t := by rw [hρz, hρzt]
  have hn1 : ¬ InnerOn (conjSub h⁻¹ K) z := by
    have := d.not_innerOn_conj c8 c3 (g := 1) hsZ hcomm (by simp [InZ]) (by simpa using hsM)
    simpa using this
  have hn2 : ¬ InnerOn (conjSub h⁻¹ K) t := by
    have := d.not_innerOn_conj c8 c3 (g := ρ * ρ) hsZ hcomm
      (by rw [hρρz]; exact Or.inr (Or.inr (Or.inl rfl))) (d.conj_not_mem_M hcore hS hsZ hρρZ)
    rwa [hρρz] at this
  have hn3 : ¬ InnerOn (conjSub h⁻¹ K) (z * t) := by
    have := d.not_innerOn_conj c8 c3 (g := ρ) hsZ hcomm
      (by rw [hρz]; exact Or.inr (Or.inr (Or.inr rfl))) (d.conj_not_mem_M hcore hS hsZ hρZ)
    rwa [hρz] at this
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨eB⟩ := nonempty_kbar_conj_equiv h⁻¹ e
  have hTS : Subgroup.closure ({t, z} : Set G) ≤ (S : Subgroup G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact d.t_mem_S
    · exact d.z_mem_S
  have hTN : Subgroup.closure ({t, z} : Set G) ≤
      Subgroup.normalizer ((conjSub h⁻¹ K : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact d.mem_normalizer_conj c8 hρρz hst
    · exact d.mem_normalizer_conj c8 (g := 1) (by group) hsz
  have hzT : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htT : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  rcases inner_or_inner_mul eB (S.isPGroup'.to_le hTS) hTN hzT hn1 htT with h' | h'
  · exact hn2 h'
  · rw [inv_eq_of_mul_eq_one_right hz2, ← hzt] at h'
    exact hn3 h'

theorem Std20Frame.closed_of_concl203 (c8 : Concl20_8 S K' R) (c3 : Concl20_3 K K' V z) {h : G}
    (hS : h⁻¹ * z * h ∈ (S : Subgroup G)) : h⁻¹ * z * h ∈ Subgroup.closure ({t, z} : Set G) :=
  d.closed_of_concl203_of_core c8 c3 (d.inZ_of_mem_sup_of_conj c3) hS

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
