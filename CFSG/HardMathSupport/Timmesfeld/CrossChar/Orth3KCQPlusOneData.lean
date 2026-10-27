module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneData

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal
open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical
section Unpack
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem qplus_data3 [Nontrivial V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) : ∃ Ã : Subgroup (orthDerived Q), QPlusData Q p A Ã := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨Ã, hle, -, e, he, -, hint, horth, hnd, hline, hex2, hact, -, -, -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp (by omega) hpl Q hQ A hA hAc
  refine ⟨Ã, ?_⟩
  have : IsMulCommutative A := hA.1
  have hcomm : ∀ x y : Ã, x * y = y * x := fun x y =>
    e.injective (by rw [map_mul, map_mul]; exact mul_comm' _ _)
  have hexp : ∀ x : Ã, x ^ p = 1 := fun x => e.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hA.2 _ (e x).2))
  have hΓ : Nat.card Ã = p ^ 2 := (Nat.card_congr e.toEquiv).trans hAc
  have hmemline : ∀ (M : Subgroup Ã) (w : V), w ∈ lineFixSpace M ↔
      ∀ x ∈ M, (((x : Ã) : orthDerived Q) : V ≃ₗ[K] V) w = w := fun M w => by
    rw [lineFixSpace_eq_fixSub, mem_fixSub]
    exact Iff.rfl
  have hmemplane : ∀ w : V, w ∈ planeFixSpace Ã ↔
      ∀ x : Ã, (((x : Ã) : orthDerived Q) : V ≃ₗ[K] V) w = w := fun w => by
    rw [planeFixSpace_eq_fixSub, mem_fixSub]
    exact ⟨fun h x => h x trivial, fun h x _ => h x⟩
  have hexM : ∀ M : Subgroup Ã, Nat.card M = p → ∃ a ∈ M, a ≠ 1 := fun M hM => by
    have hMne : M ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hM
      exact hp.one_lt.ne hM
    obtain ⟨x0, hx0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
    exact ⟨x0, x0.2, fun h => hx0 (Subtype.ext h)⟩
  have hpolar : ∀ (y : Ã) (u w : V),
      polar Q ((((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) u)
        ((((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w) = polar Q u w := fun y u w => by
    have := polar_orthRep Ã y u w
    simp only [polarBilin_apply_apply] at this
    exact this
  have : IsMulCommutative Ã := ⟨⟨fun x y => hcomm x y⟩⟩
  refine ⟨⟨inferInstance, fun x hx => congrArg Subtype.val (hexp ⟨x, hx⟩)⟩, hΓ,
    fun x hx => Subgroup.mem_comap.mp (hle hx), fun x hx h1 => ?_,
    fun M hM a ha ha1 => (hline M hM a ha ha1).1, fun M hM => ?_, fun M hM y hy w hw =>
      (hmemline M w).mp (Submodule.mem_inf.mp hw).1 y hy, fun M hM y w hw => ?_,
    fun M hM w hw hfix => ?_, fun M hM => ?_, fun M hM => ?_, fun M N hM hN hMN u hu v hv => ?_,
    fun M hM hMne => ?_, hex2, fun F c h0 hM' => ?_⟩
  · have h2 : e ⟨x, hx⟩ = 1 := Subtype.ext ((he ⟨x, hx⟩).trans h1)
    exact congrArg Subtype.val (e.injective (h2.trans (map_one e).symm))
  ·
    have hrestr := hnd (some ⟨M, hM⟩)
    refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
    refine hrestr.1 v fun w => ?_
    have h1 : polar Q (v : V) (w : V) = 0 := by
      rw [← polar_comp_subtype_eq (Q := Q) (lineSpace M) v w]
      exact hv w
    change polarBilin Q (v : V) (w : V) = 0
    rw [polarBilin_apply_apply]
    exact h1
  ·
    obtain ⟨hwl, hwp⟩ := Submodule.mem_inf.mp hw
    refine Submodule.mem_inf.mpr ⟨(hmemline M _).mpr fun x hx => ?_, ?_⟩
    · have h1 : (((x : Ã) : orthDerived Q) : V ≃ₗ[K] V)
          ((((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w) =
          (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) ((((x : Ã) : orthDerived Q) : V ≃ₗ[K] V) w) := by
        have := congrArg (fun z : Ã => (((z : Ã) : orthDerived Q) : V ≃ₗ[K] V) w)
          (hcomm (x : Ã) y)
        exact this
      rw [h1, (hmemline M w).mp hwl x hx]
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have hu' := (hmemplane u).mp hu
      have hw' : polarBilin Q u w = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hwp) u hu
      rw [polarBilin_apply_apply] at hw'
      show polarBilin Q u ((((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w) = 0
      rw [polarBilin_apply_apply, ← hu' y, hpolar]
      exact hw'
  ·
    obtain ⟨hwl, hwp⟩ := Submodule.mem_inf.mp hw
    have hw0 : w ∈ planeFixSpace Ã := (hmemplane w).mpr hfix
    have hreg0 := (hnd none).1
    have : (⟨w, hw0⟩ : planeFixSpace Ã) = 0 := by
      refine hreg0 _ fun u => ?_
      have h1 : polarBilin Q u w = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hwp) u u.2
      rw [polarBilin_apply_apply] at h1
      change polarBilin Q w u = 0
      rw [polarBilin_apply_apply]
      show polar Q w u = 0
      rw [polar_comm]
      exact h1
    exact congrArg Subtype.val this
  · obtain ⟨a, ha, ha1⟩ := hexM M hM
    exact (hline M hM a ha ha1).2
  · exact hint.submodule_iSupIndep.pairwiseDisjoint (i := none) (j := some ⟨M, hM⟩)
      (by simp)
  · have hne : (some ⟨M, hM⟩ : Option {M : Subgroup Ã // Nat.card M = p}) ≠ some ⟨N, hN⟩ := by
      intro h
      exact hMN (congrArg Subtype.val (Option.some.inj h))
    have := horth _ _ hne u hu v hv
    rwa [polarBilin_apply_apply] at this
  · obtain ⟨hpos, hdvd⟩ := hact M hM hMne
    exact Nat.le_of_dvd hpos ((Nat.dvd_lcm_right _ 2).trans hdvd)
  · refine eq_smul_of_iSup_eq_top hint.submodule_iSup_eq_top ?_
    intro i v hv
    rcases i with _ | ⟨M, hM⟩
    · exact h0 v hv
    · exact hM' M hM v hv
end Unpack
end CFSG.RankThree.PartOne.KCOrthogonal