module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf32Psi

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


@[expose] def Frame203TwoPart : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      padicValNat 2 ((oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')).subgroupOf
        (sec20X (CoreAssembly.conjClass K) z K K')).index ≤ 1

@[expose] def FrameCentOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      padicValNat 2 ((oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')).subgroupOf
        (sec20X (CoreAssembly.conjClass K) z K K')).index ≤ 1 →
      ∀ x ∈ sec20X (CoreAssembly.conjClass K) z K K', x ∈ trivialOnQuot K →
        x ∈ trivialOnQuot K' →
          x ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers z

theorem inv_mul_mem_trivialOnQuot {G : Type} [Group G] [Finite G] {J : Subgroup G} {w x : G}
    (hw : w ∈ J) (hx : x ∈ Subgroup.normalizer (J : Set G))
    (h : ∀ y ∈ J, (x * y * x⁻¹) * (w * y * w⁻¹)⁻¹ ∈ oddCoreOf J) :
    w⁻¹ * x ∈ trivialOnQuot J := by
  have hwN : w⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normalizer (J : Set G)).inv_mem (Subgroup.le_normalizer hw)
  refine ⟨(Subgroup.normalizer (J : Set G)).mul_mem hwN hx, fun y hy => ?_⟩
  have e : ⁅w⁻¹ * x, y⁆ = w⁻¹ * ((x * y * x⁻¹) * (w * y * w⁻¹)⁻¹) * w⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, oddCoreIn_eq_oddCoreOf]
  exact mem_normalizer_oddCoreOf_of_mem_normalizer hwN (h y hy)

theorem conj_mem_trivialOnQuot {G : Type} [Group G] [Finite G] {J : Subgroup G} {n a : G}
    (hn : n ∈ Subgroup.normalizer (J : Set G)) (ha : a ∈ trivialOnQuot J) :
    n * a * n⁻¹ ∈ trivialOnQuot J := by
  obtain ⟨haN, hac⟩ := ha
  have hninv : n⁻¹ ∈ Subgroup.normalizer (J : Set G) := (Subgroup.normalizer _).inv_mem hn
  refine ⟨(Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hn haN) hninv,
    fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hninv y).mp hy
  have e : ⁅n * a * n⁻¹, y⁆ = n * ⁅a, n⁻¹ * y * n⁻¹⁻¹⁆ * n⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact conj_mem_oddCoreIn_of_mem_normalizer hn (hac _ hy')

theorem frame203Cent_of_twoPart (h2 : Frame203TwoPart) (hC : FrameCentOdd) : Frame203Cent := by
  intro G _ _ _ K K' J S R R' W V z t d x hx hK hK'
  obtain ⟨k, hk, hkx⟩ := hK
  obtain ⟨k', hk', hk'x⟩ := hK'
  have hXN := frameX_le_N d
  have hXN' : x ∈ Subgroup.normalizer (K' : Set G) := ((sec20X_le_normalizers_frame d) hx).2
  have hkX : k ∈ sec20X (CoreAssembly.conjClass K) z K K' := le_sec20X_left hk
  have hk'X : k' ∈ sec20X (CoreAssembly.conjClass K) z K K' := le_sec20X_right hk'
  set c : G := k'⁻¹ * (k⁻¹ * x) with hc
  have hcX : c ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk'X) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkX) hx)
  have h1 : k⁻¹ * x ∈ trivialOnQuot K := inv_mul_mem_trivialOnQuot hk (hXN hx) hkx
  have h2' : k'⁻¹ ∈ trivialOnQuot K :=
    (trivialOnQuot K).inv_mem (le_trivialOnQuot_K d hk')
  have hcK : c ∈ trivialOnQuot K := (trivialOnQuot K).mul_mem h2' h1
  have h3 : k'⁻¹ * x ∈ trivialOnQuot K' := inv_mul_mem_trivialOnQuot hk' hXN' hk'x
  have hk'N : k'⁻¹ ∈ Subgroup.normalizer (K' : Set G) :=
    (Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hk')
  have h4 : k'⁻¹ * k⁻¹ * k'⁻¹⁻¹ ∈ trivialOnQuot K' :=
    conj_mem_trivialOnQuot hk'N ((trivialOnQuot K').inv_mem (le_trivialOnQuot_K' d hk))
  have hcK' : c ∈ trivialOnQuot K' := by
    have e : c = (k'⁻¹ * k⁻¹ * k'⁻¹⁻¹) * (k'⁻¹ * x) := by rw [hc]; group
    rw [e]
    exact (trivialOnQuot K').mul_mem h4 h3
  have hcO := hC G K K' J S R R' W V z t d (h2 G K K' J S R R' W V z t d) c hcX hcK hcK'
  have hzK : z ∈ K := d.viol.hzK.mem
  have hle : oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers z ≤
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') :=
    sup_le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hzK)) _
  have ex : x = (k * k') * c := by rw [hc]; group
  rw [ex]
  refine Subgroup.mul_mem _ ?_ (hle hcO)
  exact Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right hk'))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
