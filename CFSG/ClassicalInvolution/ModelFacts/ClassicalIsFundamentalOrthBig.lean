module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthExt
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthFrame4
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.OrthogonalPairs
  QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {i : V ≃ₗ[F] V}

theorem polarNondegOn_minusSp (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hii : i * i = 1) :
    PolarNondegOn Q (minusSp i) := by
  intro x hx hxW
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii y
  rw [polar_add_right, hxW v hv, polar_comm, polar_plusSp_minusSp h2 hi hu hx, add_zero]

theorem false_of_finrank_minus_ge_eight [Finite F] [FiniteDimensional F V]
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hii : i * i = 1)
    (hdim : 8 ≤ Module.finrank F (minusSp i)) {A T : Subgroup (V ≃ₗ[F] V)}
    (hsub : IsSubnormal A T) (hA : ⁅A, A⁆ = A) (hAn : A ≤ nM Q i) (hiA : i ∈ A)
    (hi2 : orderOf i = 2)
    (hT : ∀ N : Subgroup (V ≃ₗ[F] V), N ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      N ≤ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) → ⁅N, N⁆ = N → N ≤ T)
    (huniq : ∀ a ∈ A, ∀ b ∈ A, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b) :
    False := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  set W := minusSp i with hW
  have hQ' : (polarBilin (Q.restrict W)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_minusSp h2 hQ hi hii)
  obtain ⟨T₃, hT₃d, hT₃Q⟩ :=
    exists_totallySingular_of_two_mul_add_one_le hodd 3 (Q.restrict W) hQ' (by omega)
  have hT₃ : 3 ≤ Module.finrank F T₃ := hT₃d.ge
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ' hT₃ hT₃Q
  set E' := elementaryGroup (Q.restrict W) with hE'
  set O' := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W) with hO'
  have hE'perf : ⁅E', E'⁆ = E' :=
    Subgroup.isPerfect_iff.mp ⟨commutator_elementaryGroup_eq_top' hQ' hT₃ hT₃Q⟩
  have hOE : ⁅O', O'⁆ = E' :=
    commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hQ' h₁₂ h₁₃ h₂₃
  have hE'O : E' ≤ O' := elementaryGroup_le_orthogonalGroup _
  set ext := extGrp h2 hii with hext
  have hinj : Function.Injective ext := extGrp_injective h2 hii
  have hnM : nM Q i = O'.map ext := nM_eq_map_extGrp h2 hii hi
  set B := E'.map ext with hB
  have hBn : B ≤ nM Q i := by
    rw [hnM]
    exact Subgroup.map_mono hE'O
  have hBperf : ⁅B, B⁆ = B := by
    rw [hB, ← Subgroup.map_commutator, hE'perf]
  have hBT : B ≤ T := hT B (hBn.trans nM_le_orthogonalGroup) (hBn.trans nM_le_centralizer) hBperf
  have hAB : A ≤ B := by
    calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅nM Q i, nM Q i⁆ := Subgroup.commutator_mono hAn hAn
      _ = ⁅O'.map ext, O'.map ext⁆ := by rw [hnM]
      _ = (⁅O', O'⁆).map ext := (Subgroup.map_commutator _ _ _).symm
      _ = B := by rw [hOE]
  have hAsub : IsSubnormal A B := by
    have := isSubnormal_inf hsub hBT
    rwa [inf_eq_left.mpr hAB] at this
  set A₀ := A.comap ext with hA₀
  have hA₀sub : IsSubnormal A₀ E' := by
    have := isSubnormal_comap ext hAsub
    rwa [hB, Subgroup.comap_map_eq_self_of_injective hinj] at this
  have hperfE' : Group.IsPerfect E' := ⟨commutator_elementaryGroup_eq_top' hQ' hT₃ hT₃Q⟩
  have hqE' : CFSG.IsQuasisimple E' := by
    have hsimple := isSimpleGroup_projElementary hQ' hT₃ hT₃Q
    have hZ : (scalars F W).subgroupOf E' ≤ Subgroup.center E' := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (commute_of_mem_scalars hx y).symm
    have hnc : ∃ a b : ProjElementary (Q.restrict W), a * b ≠ b * a := by
      by_contra h
      push Not at h
      have : IsMulCommutative (ProjElementary (Q.restrict W)) := ⟨⟨h⟩⟩
      have : Group.IsPerfect (ProjElementary (Q.restrict W)) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.not_isMulCommutative _ ‹_›
    exact CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient _ hZ hperfE' hsimple hnc
  have hA₀map : A₀.map ext = A := by
    rw [hA₀]
    refine Subgroup.map_comap_eq_self ?_
    intro x hx
    have := hAn hx
    rw [hnM] at this
    obtain ⟨g, -, rfl⟩ := this
    exact ⟨g, rfl⟩
  have hA₀perf : ⁅A₀, A₀⁆ = A₀ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hA₀map, hA]
  have hi1 : i ≠ 1 := fun h => by
    rw [h, orderOf_one] at hi2
    exact absurd hi2 (by norm_num)
  rcases eq_or_le_center_of_isSubnormal hA₀sub hqE' with hE | hZ
  ·
    have hAeq : A = B := by rw [← hA₀map, hE]
    let F' : Frame (Q.restrict W) := ⟨P₁, P₂, h₁₂⟩
    set j' := F'.La (-1) with hj'
    have hj'E : j' ∈ E' := F'.La_mem_elementaryGroup (-1)
    let negW : ↥W ≃ₗ[F] ↥W := LinearEquiv.neg F
    have hiext : ext negW = i := by
      refine LinearEquiv.ext fun x => ?_
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
      rw [hext, extGrp_apply_add h2 hii negW hu hv, map_add, mem_plusSp.mp hu,
        mem_minusSp.mp hv, add_comm]
      rfl
    have hjA : ext j' ∈ A := by rw [hAeq]; exact ⟨j', hj'E, rfl⟩
    have hjj : ext j' * ext j' = 1 := by
      rw [← map_mul, hj', F'.La_neg_one_mul_self, map_one]
    have hj'1 : j' ≠ 1 := fun h => by
      have := F'.La_injective (h.trans F'.La.map_one.symm)
      exact sl2_neg_one_ne_one hodd this
    have hj1 : ext j' ≠ 1 := fun h => hj'1 (hinj (h.trans (map_one ext).symm))
    have hjne : ext j' ≠ i := by
      intro h
      have hj'neg : j' = negW := hinj (h.trans hiext.symm)
      have hperp : P₃.e ∈ F'.perp := by
        rw [Frame.mem_perp_iff]
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Frame.coords_apply, F', polar_comm (Q.restrict W) P₃.e, h₁₃.fe, h₂₃.fe,
            h₁₃.ee, h₂₃.ee]
      have hfix := (Frame.mem_perp_iff_fix F' h2).mp hperp
      rw [← hj', hj'neg] at hfix
      have : (2 : F) • P₃.e = 0 := by
        have h' : -P₃.e = P₃.e := hfix
        rw [two_smul]
        nth_rewrite 1 [← h']
        exact neg_add_cancel _
      exact P₃.e_ne_zero (smul_eq_zero.mp this |>.resolve_left h2)
    have hjc : ext j' * i = i * ext j' := by
      have h : ext j' * ext negW = ext negW * ext j' := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact LinearEquiv.ext fun x => map_neg j' x
      rwa [hiext] at h
    exact hjne (huniq _ hjA i hiA (orderOf_eq_prime (by rw [pow_two]; exact hjj) hj1) hi2 hjc)
  · have hbot : A₀ = ⊥ := Frame4.eq_bot_of_le_center_of_isPerfect hZ hA₀perf
    have : A = ⊥ := by rw [← hA₀map, hbot, Subgroup.map_bot]
    exact hi1 (by simpa [this] using hiA)

end CFSG.ClassicalInvolution.ModelFacts
