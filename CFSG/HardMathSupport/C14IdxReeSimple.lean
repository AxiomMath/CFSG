module

public import CFSG.LieType.Ree.Duality
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups

private lemma quadForm_pos_of_isRoot
    {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) :
    0 < ReeTag.F4.quadForm α := by
  rcases ReeTag.quadForm_eq hα with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num [ReeTag.prime]

private lemma quadForm_smul_dualRoot
    {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) :
    ReeTag.F4.quadForm α • ReeTag.F4.dualRoot α =
      (2 : ℤ) • ReeTag.F4.dualMapInt α := by
  funext j
  have hd : ReeTag.F4.quadForm α ∣ 2 * ReeTag.F4.dualMapInt α j :=
    Int.dvd_of_emod_eq_zero ((ReeTag.rootDualityCheck_spec hα).2.1 j)
  simp only [ReeTag.dualRoot, Pi.smul_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel' hd

private lemma smul_quadForm_dualRoot
    {w : WeylGroup ReeTag.F4.tag} {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) :
    ReeTag.F4.quadForm α • (w • ReeTag.F4.dualRoot α) =
      (2 : ℤ) • (w • ReeTag.F4.dualMapInt α) := by
  calc
    ReeTag.F4.quadForm α • (w • ReeTag.F4.dualRoot α) =
        w • (ReeTag.F4.quadForm α • ReeTag.F4.dualRoot α) :=
      smul_comm (ReeTag.F4.quadForm α) w (ReeTag.F4.dualRoot α)
    _ = w • ((2 : ℤ) • ReeTag.F4.dualMapInt α) := by rw [quadForm_smul_dualRoot hα]
    _ = (2 : ℤ) • (w • ReeTag.F4.dualMapInt α) := by
      rw [smul_comm (2 : ℤ) w (ReeTag.F4.dualMapInt α)]

private lemma dualMapInt_add (α β : Fin ReeTag.F4.tag.rank → ℤ) :
    ReeTag.F4.dualMapInt (α + β) =
      ReeTag.F4.dualMapInt α + ReeTag.F4.dualMapInt β := by
  funext j
  simp only [ReeTag.dualMapInt, Pi.add_apply, mul_add]

private lemma scale_F4_pos (i : Fin ReeTag.F4.tag.rank) :
    0 < (ReeTag.F4.scale i : ℤ) := by
  fin_cases i <;> decide

private lemma dualMapInt_injective :
    Function.Injective (ReeTag.F4.dualMapInt : (Fin ReeTag.F4.tag.rank → ℤ) →
      (Fin ReeTag.F4.tag.rank → ℤ)) := by
  intro α β h
  funext i
  have hi := congrFun h (ReeTag.F4.perm i)
  simp only [ReeTag.dualMapInt, Equiv.symm_apply_apply] at hi
  exact mul_left_cancel₀ (scale_F4_pos i).ne' hi

private lemma two_smul_smul (c : ℤ) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    (2 : ℤ) • (c • v) = c • ((2 : ℤ) • v) := by
  rw [smul_smul, mul_comm, ← smul_smul]

private lemma reeTwist_smul_relation
    {w : WeylGroup ReeTag.F4.tag} {β γ δ : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : IsRoot ReeTag.F4.tag β) (hγ : IsRoot ReeTag.F4.tag γ)
    (hδ : IsRoot ReeTag.F4.tag δ)
    (h : w • ReeTag.F4.dualRoot β =
      w • ReeTag.F4.dualRoot γ + w • ReeTag.F4.dualRoot δ) :
    (ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • β =
      (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • γ +
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • δ := by
  let T : (Fin ReeTag.F4.tag.rank → ℤ) →+ (Fin ReeTag.F4.tag.rank → ℤ) :=
    { toFun := fun v => w • ReeTag.F4.dualMapInt v
      map_zero' := by
        change w • ReeTag.F4.dualMapInt (0 : Fin ReeTag.F4.tag.rank → ℤ) = 0
        have h : ReeTag.F4.dualMapInt (0 : Fin ReeTag.F4.tag.rank → ℤ) = 0 := by
          funext j
          simp [ReeTag.dualMapInt]
        rw [h, smul_zero]
      map_add' := fun a b => by
        rw [dualMapInt_add]
        simp }
  have hTinj : Function.Injective T := by
    intro a b hab
    change w • ReeTag.F4.dualMapInt a = w • ReeTag.F4.dualMapInt b at hab
    exact dualMapInt_injective (MulAction.injective w hab)
  have hTβ : ReeTag.F4.quadForm β • (w • ReeTag.F4.dualRoot β) = (2 : ℤ) • T β := by
    simpa [T] using smul_quadForm_dualRoot hβ
  have hTγ : ReeTag.F4.quadForm γ • (w • ReeTag.F4.dualRoot γ) = (2 : ℤ) • T γ := by
    simpa [T] using smul_quadForm_dualRoot hγ
  have hTδ : ReeTag.F4.quadForm δ • (w • ReeTag.F4.dualRoot δ) = (2 : ℤ) • T δ := by
    simpa [T] using smul_quadForm_dualRoot hδ
  have hL : (2 : ℤ) •
      ((ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • T β) =
      (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
        (w • ReeTag.F4.dualRoot β) := by
    calc
      (2 : ℤ) • ((ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • T β) =
          (ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • ((2 : ℤ) • T β) :=
        two_smul_smul _ _
      _ = (ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
            (ReeTag.F4.quadForm β • (w • ReeTag.F4.dualRoot β)) := by rw [← hTβ]
      _ = ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
            (w • ReeTag.F4.dualRoot β)) := by
        rw [smul_smul]
        congr 1
        ring
  have hR : (2 : ℤ) •
      ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • T γ +
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • T δ) =
      (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
          (w • ReeTag.F4.dualRoot γ) +
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
          (w • ReeTag.F4.dualRoot δ) := by
    calc
      (2 : ℤ) • ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • T γ +
            (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • T δ) =
          (2 : ℤ) • ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • T γ) +
            (2 : ℤ) • ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • T δ) := smul_add _ _ _
      _ = (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • ((2 : ℤ) • T γ) +
            (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • ((2 : ℤ) • T δ) := by
            rw [two_smul_smul, two_smul_smul]
      _ = (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) •
            (ReeTag.F4.quadForm γ • (w • ReeTag.F4.dualRoot γ)) +
            (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) •
              (ReeTag.F4.quadForm δ • (w • ReeTag.F4.dualRoot δ)) := by
            rw [← hTγ, ← hTδ]
      _ = ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
            (w • ReeTag.F4.dualRoot γ) +
          (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) •
            (w • ReeTag.F4.dualRoot δ)) := by
        rw [smul_smul, smul_smul]
        congr 1
        all_goals congr 1
        all_goals ring
  have h2 : (2 : ℤ) •
      ((ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • T β) =
      (2 : ℤ) •
        ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • T γ +
          (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • T δ) := by
    rw [hL, hR, h, smul_add]
  have h1 : (ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • T β =
      (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • T γ +
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • T δ :=
    zsmul_right_injective (G := Fin ReeTag.F4.tag.rank → ℤ) (n := (2 : ℤ))
      (by norm_num) h2
  have h1' : T ((ReeTag.F4.quadForm γ * ReeTag.F4.quadForm δ) • β) =
      T ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ) • γ +
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ) • δ) := by
    rw [T.map_zsmul, T.map_add, T.map_zsmul, T.map_zsmul]
    exact h1
  exact hTinj h1'

theorem bijOn_simpleRoots_of_reeTwist
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M}
    {w : WeylGroup ReeTag.F4.tag}
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΨp : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (posRoots (kernelRoots χ))
      (posRoots (kernelRoots χ))) :
    Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
  classical
  let θ : (Fin ReeTag.F4.tag.rank → ℤ) → (Fin ReeTag.F4.tag.rank → ℤ) :=
    fun α => w • ReeTag.F4.dualRoot α
  let Δ : Finset (Fin ReeTag.F4.tag.rank → ℤ) := simpleRoots (kernelRoots χ)
  have hMaps : Set.MapsTo θ (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
    intro β hβ
    have hβ' : β ∈ simpleRoots (kernelRoots χ) := hβ
    obtain ⟨hβroot, hβpos, -⟩ := mem_simpleRoots.1 hβ'
    have hθroot : IsRoot ReeTag.F4.tag (θ β) :=
      (hΨ.mapsTo (simpleRoots_subset hβ')).1
    have hθpos : θ β ∈ posRoots (kernelRoots χ) := hΨp.mapsTo hβpos
    refine mem_simpleRoots.2 ⟨hθroot, hθpos, ?_⟩
    intro γ hγ δ hδ hsum
    obtain ⟨γ', hγ'pos, hγ'eq⟩ := hΨp.surjOn hγ
    obtain ⟨δ', hδ'pos, hδ'eq⟩ := hΨp.surjOn hδ
    have hγ'root : IsRoot ReeTag.F4.tag γ' := hγ'pos.1.1
    have hδ'root : IsRoot ReeTag.F4.tag δ' := hδ'pos.1.1
    have hθsum : θ β = θ γ' + θ δ' := by
      have h := hsum
      rw [← hγ'eq, ← hδ'eq] at h
      simpa [θ] using h
    have hrel := reeTwist_smul_relation hβroot hγ'root hδ'root hθsum
    obtain ⟨c, hc, hcγ⟩ := exists_nonneg_coords_kernel hγ'pos
    obtain ⟨d, hd, hdδ⟩ := exists_nonneg_coords_kernel hδ'pos
    change γ' = ∑ ε ∈ Δ, c ε • ε at hcγ
    change δ' = ∑ ε ∈ Δ, d ε • ε at hdδ
    let coeff : (Fin ReeTag.F4.tag.rank → ℤ) → ℤ := fun ε =>
      ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε +
        ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε -
          ReeTag.F4.quadForm γ' * ReeTag.F4.quadForm δ' * unitCoords β ε
    have hβΔ : β ∈ Δ := hβ'
    have hA : ∑ ε ∈ Δ, (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε) • ε =
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ') • γ' := by
      rw [hcγ, Finset.smul_sum]
      simp only [← smul_smul]
    have hB : ∑ ε ∈ Δ, (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε) • ε =
        (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ') • δ' := by
      rw [hdδ, Finset.smul_sum]
      simp only [← smul_smul]
    have hC : ∑ ε ∈ Δ,
        (ReeTag.F4.quadForm γ' * ReeTag.F4.quadForm δ' * unitCoords β ε) • ε =
        (ReeTag.F4.quadForm γ' * ReeTag.F4.quadForm δ') • β := by
      simp only [← smul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, sum_unitCoords hβΔ]
    have hsum0 : ∑ ε ∈ Δ, coeff ε • ε = 0 := by
      calc ∑ ε ∈ Δ, coeff ε • ε
          = ∑ ε ∈ Δ, ((ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε) • ε +
              (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε) • ε -
                (ReeTag.F4.quadForm γ' * ReeTag.F4.quadForm δ' * unitCoords β ε) • ε) := by
            apply Finset.sum_congr rfl
            intro ε _
            simp only [coeff, add_smul, sub_smul]
        _ = (∑ ε ∈ Δ, (ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε) • ε +
              ∑ ε ∈ Δ, (ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε) • ε) -
              ∑ ε ∈ Δ,
                (ReeTag.F4.quadForm γ' * ReeTag.F4.quadForm δ' * unitCoords β ε) • ε := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        _ = 0 := by
            rw [hA, hB, hC, hrel]
            abel
    have hreal : ∑ ε ∈ Δ, (coeff ε : ℝ) • toReal ε = 0 := by
      have h := congrArg toReal hsum0
      rw [toReal_sum_smul] at h
      have h0 : toReal (0 : Fin ReeTag.F4.tag.rank → ℤ) = 0 := by
        ext j
        simp [toReal]
      rw [h0] at h
      exact h
    have hcoeff : ∀ ε ∈ Δ, coeff ε = 0 := by
      intro ε hε
      have hzero := eq_zero_of_sum_smul_toReal_eq_zero
        (fun δ hδ => simpleRoots_height_pos hδ)
        (fun δ hδ η hη hne => iform_nonpos_of_mem_simpleRoots_kernelRoots hδ hη hne)
        hreal ε hε
      exact_mod_cast hzero
    have hc0 : ∀ ε ∈ Δ, ε ≠ β → c ε = 0 := by
      intro ε hε hne
      have hzero := hcoeff ε hε
      have hu : unitCoords β ε = 0 := unitCoords_of_ne hne
      have hzero' : ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε +
          ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε = 0 := by
        simpa [coeff, hu] using hzero
      have hqβ : 0 < ReeTag.F4.quadForm β := quadForm_pos_of_isRoot hβroot
      have hqγ : 0 < ReeTag.F4.quadForm γ' := quadForm_pos_of_isRoot hγ'root
      have hqδ : 0 < ReeTag.F4.quadForm δ' := quadForm_pos_of_isRoot hδ'root
      have h1 : 0 ≤ ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε :=
        mul_nonneg (mul_pos hqβ hqδ).le (hc ε hε)
      have h2 : 0 ≤ ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε :=
        mul_nonneg (mul_pos hqβ hqγ).le (hd ε hε)
      have hzero'' : ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε = 0 :=
        ((add_eq_zero_iff_of_nonneg h1 h2).1 hzero').1
      exact (mul_eq_zero.1 hzero'').resolve_left (mul_pos hqβ hqδ).ne'
    have hd0 : ∀ ε ∈ Δ, ε ≠ β → d ε = 0 := by
      intro ε hε hne
      have hzero := hcoeff ε hε
      have hu : unitCoords β ε = 0 := unitCoords_of_ne hne
      have hzero' : ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε +
          ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε = 0 := by
        simpa [coeff, hu] using hzero
      have hqβ : 0 < ReeTag.F4.quadForm β := quadForm_pos_of_isRoot hβroot
      have hqγ : 0 < ReeTag.F4.quadForm γ' := quadForm_pos_of_isRoot hγ'root
      have hqδ : 0 < ReeTag.F4.quadForm δ' := quadForm_pos_of_isRoot hδ'root
      have h1 : 0 ≤ ReeTag.F4.quadForm β * ReeTag.F4.quadForm δ' * c ε :=
        mul_nonneg (mul_pos hqβ hqδ).le (hc ε hε)
      have h2 : 0 ≤ ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε :=
        mul_nonneg (mul_pos hqβ hqγ).le (hd ε hε)
      have hzero'' : ReeTag.F4.quadForm β * ReeTag.F4.quadForm γ' * d ε = 0 :=
        ((add_eq_zero_iff_of_nonneg h1 h2).1 hzero').2
      exact (mul_eq_zero.1 hzero'').resolve_left (mul_pos hqβ hqγ).ne'
    have hγβ : γ' = c β • β := by
      rw [hcγ]
      rw [Finset.sum_eq_single β (fun ε hε hne => by rw [hc0 ε hε hne, zero_smul])
        (fun h => absurd hβΔ h)]
    have hδβ : δ' = d β • β := by
      rw [hdδ]
      rw [Finset.sum_eq_single β (fun ε hε hne => by rw [hd0 ε hε hne, zero_smul])
        (fun h => absurd hβΔ h)]
    have hcβpos : 0 < c β := by
      refine lt_of_le_of_ne (hc β hβΔ) (Ne.symm ?_)
      intro hzero
      have hγ0 : γ' = 0 := by rw [hγβ, hzero, zero_smul]
      exact hγ'root.ne_zero hγ0
    have hdβpos : 0 < d β := by
      refine lt_of_le_of_ne (hd β hβΔ) (Ne.symm ?_)
      intro hzero
      have hδ0 : δ' = 0 := by rw [hδβ, hzero, zero_smul]
      exact hδ'root.ne_zero hδ0
    have hcβ1 : c β = 1 := by
      rcases hγ'root.eq_one_or_neg_one_of_eq_smul hγβ with h | h
      · exact h
      · omega
    have hdβ1 : d β = 1 := by
      rcases hδ'root.eq_one_or_neg_one_of_eq_smul hδβ with h | h
      · exact h
      · omega
    have hγ'β : γ' = β := by rw [hγβ, hcβ1, one_smul]
    have hδ'β : δ' = β := by rw [hδβ, hdβ1, one_smul]
    have hγeq : γ = θ β := by rw [← hγ'eq, hγ'β]
    have hδeq : δ = θ β := by rw [← hδ'eq, hδ'β]
    have hzero : θ β = 0 := by
      rw [hγeq, hδeq] at hsum
      have h2 : θ β + 0 = θ β + θ β := by simpa using hsum
      exact (add_left_cancel h2).symm
    exact hθroot.ne_zero hzero
  have hInj : Set.InjOn θ (Δ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
    intro α hα β hβ hab
    have hα' : α ∈ simpleRoots (kernelRoots χ) := hα
    have hβ' : β ∈ simpleRoots (kernelRoots χ) := hβ
    have hαroot : IsRoot ReeTag.F4.tag α := simpleRoots_isRoot hα'
    have hβroot : IsRoot ReeTag.F4.tag β := simpleRoots_isRoot hβ'
    have hD : ReeTag.F4.dualRoot α = ReeTag.F4.dualRoot β :=
      MulAction.injective w hab
    calc α = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot α) :=
          (ReeTag.dualRoot_dualRoot hαroot).symm
      _ = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot β) := by rw [hD]
      _ = β := ReeTag.dualRoot_dualRoot hβroot
  exact (Δ.finite_toSet.injOn_iff_bijOn_of_mapsTo hMaps).1 hInj

end CFSG.HardMathSupport.C14Idx
