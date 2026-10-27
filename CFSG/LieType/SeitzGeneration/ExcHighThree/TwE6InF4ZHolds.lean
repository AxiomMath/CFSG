module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Two
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZLang
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZComm

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false


theorem exists_unit_pow_succ_eq_one (K : Type) [Field K] [Finite K] (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hq : 5 ≤ q) :
    ∃ t : Kˣ, (t : K) ^ (q + 1) = 1 ∧ (t : K) ^ 4 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
    ring
  have hdvd : (q - 1) ∣ orderOf g := by
    rw [hord, hfac]
    exact dvd_mul_right _ _
  have hto : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hfac]
    exact Nat.mul_div_cancel_left _ (by omega)
  refine ⟨g ^ (q - 1), ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one (g ^ (q - 1))
    rw [hto] at h1
    have h2 := congrArg Units.val h1
    simpa using h2
  · intro h4
    have h5 : (g ^ (q - 1)) ^ 4 = 1 := Units.ext (by simpa using h4)
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hto] at h6
    have h7 := Nat.le_of_dvd (by norm_num) h6
    omega

theorem twistedZClosing_two_holds : TwistedZClosing_two := by
  intro k K _ _ _ _ _ σ hσ hfix hK hq h3 D₁ ω hω z hz hz1
  set ι : adjointGroup Tag.F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hι
  have hq5 : 5 ≤ Nat.card k := by omega
  obtain ⟨t, ht, ht4⟩ := exists_unit_pow_succ_eq_one K (Nat.card k) hK hq5
  obtain ⟨f, hf⟩ := twisted_z_conj_f4Z k hq D₁ ω hω z hz
  have hcomm : Commute (ι ⟨f4Z k, f4Z_mem_adjointGroup⟩) (torusWord σ hσ hK t) :=
    commute_iota_f4Z σ hσ hfix hK t ht
  set H : Subgroup (twistedE6RootGroup K σ) := Subgroup.closure
    ((ι.range : Set (twistedE6RootGroup K σ)) ∪
      (Subgroup.centralizer ({ι z} : Set (twistedE6RootGroup K σ)) :
        Set (twistedE6RootGroup K σ))) with hH
  have hF : (phiG σ hfix).range ≤ H := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.subset_closure (Or.inl ⟨e6FixedF4EquivAll k g, ?_⟩)
    simp [hι]
  have hιf : ι f ∈ H := Subgroup.subset_closure (Or.inl ⟨f, rfl⟩)
  have hd : torusWord σ hσ hK t ∈ H := by
    have hzι : ι z = ι f * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * (ι f)⁻¹ := by
      rw [← hf, map_mul, map_mul, map_inv]
    have hcent : ι f * torusWord σ hσ hK t * (ι f)⁻¹ ∈
        Subgroup.centralizer ({ι z} : Set (twistedE6RootGroup K σ)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hzι]
      calc ι f * torusWord σ hσ hK t * (ι f)⁻¹ * (ι f * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * (ι f)⁻¹)
          = ι f * (torusWord σ hσ hK t * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩) * (ι f)⁻¹ := by group
        _ = ι f * (ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * torusWord σ hσ hK t) * (ι f)⁻¹ := by
          rw [hcomm.eq]
        _ = ι f * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * (ι f)⁻¹ * (ι f * torusWord σ hσ hK t * (ι f)⁻¹) := by
          group
    have h1 : ι f * torusWord σ hσ hK t * (ι f)⁻¹ ∈ H := Subgroup.subset_closure (Or.inr hcent)
    have h2 : torusWord σ hσ hK t =
        (ι f)⁻¹ * (ι f * torusWord σ hσ hK t * (ι f)⁻¹) * ι f := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem hιf) h1) hιf
  exact closure_top_of_torusWord σ hσ hfix hK H hF t ht ht4 hd

end CFSG.LieType.SeitzGeneration.ExcHighThree
