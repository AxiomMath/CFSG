module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf36Outer
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII207Cent
public import CFSG.ClassicalInvolution.Q3.Q3T6DExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

open Out


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Inv

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem le_sec20X_of_USet {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K))
    (hUC : U ≤ Subgroup.centralizer ({z} : Set G)) :
    U ≤ sec20X (CoreAssembly.conjClass K) z K K' :=
  (le_iSup₂ (f := fun U' (_ : U' ∈ {U' : Subgroup G | U' ∈ USet (CoreAssembly.conjClass K) ∧
    U' ≤ Subgroup.centralizer ({z} : Set G)}) => U') U ⟨hU, hUC⟩).trans
      (le_sup_left.trans le_sup_left)

theorem sec20X_le_centralizer_z :
    sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (sup_le (iSup₂_le fun _ hU => hU.2) (le_trans le_sup_left d.sup_le_centralizer_z))
    (le_trans le_sup_right d.sup_le_centralizer_z)

theorem twinSet_K' : twinSet (CoreAssembly.conjClass K) K' = {K', K} := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by
    rw [d.twins]; exact Or.inr rfl
  rw [twinSet_eq_of_mem_twinSet d.viol.hzK h, d.twins, Set.pair_comm]

theorem exists_sq_of_aviol {B L : Subgroup G} {zB s : G} (hB : B ∈ CoreAssembly.conjClass K)
    (hBz : IsUniqueInvolution B z) (h : AViol (CoreAssembly.conjClass K) B L zB s) :
    ∃ u ∈ sec20X (CoreAssembly.conjClass K) z K K', u * u = s ∧ u ^ 4 = 1 ∧ u * u ≠ 1 := by
  obtain ⟨-, -, U, hU, hUL, hUN⟩ := h.star
  have hUX := le_sec20X_of_USet d hU (le_centralizer_of_le_normalizer' hBz hUN)
  have hc := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU d.late_mem_K d.hR
  have hU4 : Nat.card U = 4 := by rw [d.card8] at hc; omega
  have hcyc : IsCyclic U := by
    obtain ⟨-, -, -, hc', -⟩ := hU
    exact hc'
  obtain ⟨v, hv⟩ := hcyc.exists_generator
  have hord : orderOf (v : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv, hU4]
  have h4 : (v : G) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hne : (v : G) * (v : G) ≠ 1 := by
    rw [← pow_two]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
  have hmemL : (v : G) * (v : G) ∈ L := L.mul_mem (hUL v.2) (hUL v.2)
  have hsq : ((v : G) * (v : G)) * ((v : G) * (v : G)) = 1 := by
    have e4 : ((v : G) * (v : G)) * ((v : G) * (v : G)) = (v : G) ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e4, h4]
  rcases h.hzJ.unique _ hmemL hsq with h1 | h1
  · exact absurd h1 hne
  · exact ⟨(v : G), hUX v.2, h1, h4, hne⟩

theorem aviol_involution_mem {B B' L : Subgroup G} {zB s : G}
    (hB : B ∈ CoreAssembly.conjClass K) (hBz : IsUniqueInvolution B z)
    (htw : twinSet (CoreAssembly.conjClass K) B = {B, B'})
    (h : AViol (CoreAssembly.conjClass K) B L zB s) :
    s ∈ B ⊔ B' ∧ s ≠ z := by
  refine ⟨t_mem_sup_of_aviolGen d.hyp hB h htw, fun hsz => ?_⟩
  exact AViol.ne_involution_gen d.hyp hB h (hsz.trans (hBz.eq h.hzK))

theorem not_innerOn_of_sq {x : G} (hx : x ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (hs : x * x ∈ K ⊔ K') (hs2 : (x * x) * (x * x) = 1) (hs1 : x * x ≠ 1) (hsz : x * x ≠ z) :
    ¬ InnerOn K x ∧ ¬ InnerOn K' x := by
  obtain ⟨g, hg, hgK⟩ := d.swap
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := sq_mem_trivialOnQuot_of_innerOn d (frameX_le_N d hx) h
    exact not_trivialOnQuot_of_invol d hs hs2 hs1 hsz this
  · rw [← hgK] at h
    have h' := innerOn_swap' h
    have hw' : g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G) :=
      conj_swap_mem_normalizer d hg hgK ((sec20X_le_normalizers_frame d hx).2)
    have hsq := sq_mem_trivialOnQuot_of_innerOn d hw' h'
    have e : (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [e] at hsq
    refine not_trivialOnQuot_of_invol d (conj_swap_sup d hg hgK hs) ?_ ?_ ?_ hsq
    · calc g⁻¹ * (x * x) * g * (g⁻¹ * (x * x) * g) = g⁻¹ * ((x * x) * (x * x)) * g := by group
        _ = 1 := by rw [hs2]; group
    · intro h1
      apply hs1
      have : x * x = g * 1 * g⁻¹ := by rw [← h1]; group
      simpa using this
    · intro h1
      apply hsz
      have hgz : g * z = z * g := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm.symm
      have : x * x = g * z * g⁻¹ := by rw [← h1]; group
      rw [this, hgz]; group

theorem mem_trivialOnQuot_of_rhoK_eq_one {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (h : rhoK K ⟨x, hx⟩ = 1) : x ∈ trivialOnQuot K := by
  refine Balance.Bootstrap.mem_trivialOnQuot_iff.mpr ⟨hx, fun y hy => ?_⟩
  have h1 : rhoK K ⟨x, hx⟩ = MulAut.conj (QuotientGroup.mk (1 : ↥K) : Kbar K) := by
    rw [h, QuotientGroup.mk_one, map_one]
  have h2 := (rhoK_eq_conj_iff K ⟨x, hx⟩ 1).mp h1 ⟨y, hy⟩
  simpa [commutatorElement_def, oddCoreIn_eq_oddCoreOf] using h2

theorem exists_central_mul_oddCore_sup {w : G} (hw : w ∈ K ⊔ K')
    (hwK : w ∈ trivialOnQuot K) (hwK' : w ∈ trivialOnQuot K') :
    ∃ c : G, (c = 1 ∨ c = z) ∧ ∃ n ∈ oddCoreOf (K ⊔ K'), w = c * n := by
  have hw' : w ∈ ((K ⊔ K' : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K K' d.late_K_le] at hw'
  obtain ⟨k₁, hk₁, k₂, hk₂, hwk⟩ := hw'
  have hwk' : k₁ * k₂ = w := hwk
  have hk₂K : k₂ ∈ trivialOnQuot K := le_trivialOnQuot_K d hk₂
  have hk₁K : k₁ ∈ trivialOnQuot K := by
    have e : k₁ = w * k₂⁻¹ := by rw [← hwk']; group
    rw [e]
    exact (trivialOnQuot K).mul_mem hwK ((trivialOnQuot K).inv_mem hk₂K)
  obtain ⟨c₁, hc₁, n₁, hn₁, hk₁e⟩ := exists_central_mul_oddCore d hk₁ hk₁K
  have hc₁K : c₁ ∈ K := by
    rcases hc₁ with h | h
    · rw [h]; exact K.one_mem
    · rw [h]; exact d.viol.hzK.mem
  have hn₁K : n₁ ∈ K := oddCoreOf_le_self K hn₁
  have hk₂tr : k₂ ∈ trivialOnQuot K' := by
    have hcn : c₁ * n₁ ∈ trivialOnQuot K' :=
      le_trivialOnQuot_K' d (K.mul_mem hc₁K hn₁K)
    have e : k₂ = (c₁ * n₁)⁻¹ * w := by rw [← hwk', hk₁e]; group
    rw [e]
    exact (trivialOnQuot K').mul_mem ((trivialOnQuot K').inv_mem hcn) hwK'
  obtain ⟨c₂, hc₂, n₂, hn₂, hk₂e⟩ := exists_central_mul_oddCore' d hk₂ hk₂tr
  have hO₁ : oddCoreOf K ≤ oddCoreOf (K ⊔ K') :=
    le_oddCoreOf_of_normalizes ((oddCoreOf_le_self K).trans le_sup_left)
      (sup_le (fun k hk => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hk))
        (fun k hk => mem_normalizer_oddCore_of_mem_normalizer (d.late_K'_le hk)))
      (oddCoreOf_odd_natCard K)
  have hO₂ : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') :=
    le_oddCoreOf_of_normalizes ((oddCoreOf_le_self K').trans le_sup_right)
      (sup_le (fun k hk => mem_normalizer_oddCore_of_mem_normalizer (d.late_K_le hk))
        (fun k hk => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hk)))
      (oddCoreOf_odd_natCard K')
  have hn : n₁ * n₂ ∈ oddCoreOf (K ⊔ K') :=
    (oddCoreOf (K ⊔ K')).mul_mem (hO₁ hn₁) (hO₂ hn₂)
  have hw_eq : w = c₁ * n₁ * (c₂ * n₂) := by rw [← hk₁e, ← hk₂e, hwk']
  rcases hc₂ with h₂ | h₂
  · refine ⟨c₁, hc₁, n₁ * n₂, hn, ?_⟩
    rw [hw_eq, h₂, one_mul, mul_assoc]
  · refine ⟨c₁ * z, ?_, n₁ * n₂, hn, ?_⟩
    · rcases hc₁ with h₁ | h₁
      · right; rw [h₁, one_mul]
      · left; rw [h₁]; exact d.viol.hzK.sq
    · have hzn : z * n₁ = n₁ * z := z_comm_sup d (Subgroup.mem_sup_left hn₁K)
      rw [hw_eq, h₂]
      calc c₁ * n₁ * (z * n₂) = c₁ * (n₁ * z) * n₂ := by group
        _ = c₁ * (z * n₁) * n₂ := by rw [hzn]
        _ = c₁ * z * (n₁ * n₂) := by group

end Inv

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
