module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCover
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Aux
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement

theorem eq_of_central_displacement_hom {G H : Type*} [Group G] [Group H] [Group.IsPerfect G] (f g : G →* H)
    (h : ∀ x, (g x)⁻¹ * f x ∈ Subgroup.center H) : f = g := by
  have hfg : ∀ x, f x = g x * ((g x)⁻¹ * f x) := fun x => by group
  have hle : commutator G ≤ MonoidHom.eqLocus f g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hfg a, hfg b]
    exact commutatorElement_mul_central_mul_central (h a) (h b)
  rw [Group.IsPerfect.commutator_eq_top] at hle
  ext x
  exact hle (Subgroup.mem_top x)

variable {Cov K X : Type} [Group Cov] [Group K] [Group X]

theorem exists_surjective_lift [Finite Cov] [Finite K]
    (ρC : Cov →* X) (ρK : K →* X) (hC : Function.Surjective ρC) (hK : Function.Surjective ρK)
    (hcK : ρK.ker ≤ Subgroup.center K) (hperf : Group.IsPerfect K)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* Cov), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : Cov →* E, ∀ g, π (s g) = g) :
    ∃ φ : Cov →* K, (∀ g, ρK (φ g) = ρC g) ∧ Function.Surjective φ := by
  classical
  let E : Subgroup (K × Cov) := fibreProduct ρK ρC
  let π : E →* Cov := (MonoidHom.snd K Cov).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := hK (ρC g)
    exact ⟨⟨(l, g), hl⟩, rfl⟩
  have hπc : π.ker ≤ Subgroup.center E := by
    intro x hx
    obtain ⟨⟨l, s⟩, hxm⟩ := x
    have hs : s = 1 := hx
    subst hs
    have hl : l ∈ Subgroup.center K :=
      hcK (by rw [MonoidHom.mem_ker]; exact (show ρK l = ρC 1 from hxm).trans (map_one ρC))
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨l', s'⟩, hy⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Subgroup.mem_center_iff.1 hl l'
    · exact (mul_one s').trans (one_mul s').symm
  obtain ⟨s, hs⟩ := hsec E π hπ hπc
  let φ : Cov →* K := (MonoidHom.fst K Cov).comp (E.subtype.comp s)
  have hφ : ∀ g, ρK (φ g) = ρC g := by
    intro g
    calc ρK (φ g) = ρC (π (s g)) := (s g).2
      _ = ρC g := by rw [hs g]
  have hdec : ∀ x : K, ∃ g : Cov, ∃ z ∈ Subgroup.center K, x = φ g * z := by
    intro x
    obtain ⟨g, hg⟩ := hC (ρK x)
    refine ⟨g, (φ g)⁻¹ * x, ?_, by group⟩
    apply hcK
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hg, inv_mul_cancel]
  have hcomm : ∀ x y : K, ⁅x, y⁆ ∈ φ.range := by
    intro x y
    obtain ⟨g, z, hz, rfl⟩ := hdec x
    obtain ⟨g', z', hz', rfl⟩ := hdec y
    rw [commutatorElement_mul_central_mul_central hz hz']
    exact ⟨⁅g, g'⁆, by simp [commutatorElement_def]⟩
  refine ⟨φ, hφ, ?_⟩
  have h1 : commutator K ≤ φ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    exact fun x _ y _ => hcomm x y
  rw [hperf.commutator_eq_top] at h1
  intro x
  exact h1 (Subgroup.mem_top x)

theorem exists_automorphism_lift [Finite Cov] (ρ : Cov →* X) (hρ : Function.Surjective ρ)
    (hc : ρ.ker ≤ Subgroup.center Cov) (hperf : Group.IsPerfect Cov)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* Cov), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : Cov →* E, ∀ g, π (s g) = g) (γ : MulAut X) :
    ∃ βL : MulAut Cov, ∀ x, ρ (βL x) = γ (ρ x) := by
  obtain ⟨φ, hφ, hsurj⟩ := exists_surjective_lift (γ.toMonoidHom.comp ρ) ρ (γ.surjective.comp hρ) hρ hc hperf hsec
  exact ⟨MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le le_rfl), fun x => hφ x⟩

theorem exists_cover_lift [Finite Cov] [Finite K]
    (ρC : Cov →* X) (ρK : K →* X) (hC : Function.Surjective ρC) (hK : Function.Surjective ρK)
    (hcK : ρK.ker ≤ Subgroup.center K) (hcC : ρC.ker ≤ Subgroup.center Cov)
    (hperfK : Group.IsPerfect K) (hperfC : Group.IsPerfect Cov)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* Cov), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : Cov →* E, ∀ g, π (s g) = g)
    (β : MulAut K) (γ : MulAut X) (hcomm : ∀ k, ρK (β k) = γ (ρK k)) (hγ3 : γ ^ 3 = 1) :
    ∃ (π : Cov →* K) (βL : MulAut Cov), Function.Surjective π ∧ (∀ x, π x = 1 → x ∈ Subgroup.center Cov) ∧
      (∀ x, ρK (π x) = ρC x) ∧ βL ^ 3 = 1 ∧ ∀ x, π (βL x) = β (π x) := by
  haveI := hperfC
  obtain ⟨π, hπ, hπsurj⟩ := exists_surjective_lift ρC ρK hC hK hcK hperfK hsec
  obtain ⟨βL, hβL⟩ := exists_automorphism_lift ρC hC hcC hperfC hsec γ
  have hpow : ∀ n : ℕ, ∀ x, ρC ((βL ^ n) x) = (γ ^ n) (ρC x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hβL, pow_succ, MulAut.mul_apply]
  refine ⟨π, βL, hπsurj, ?_, hπ, ?_, ?_⟩
  · intro x hx
    apply hcC
    rw [MonoidHom.mem_ker, ← hπ x, hx, map_one]
  · have h3 : (βL ^ 3).toMonoidHom = MonoidHom.id Cov := by
      refine eq_of_central_displacement (βL ^ 3).toMonoidHom (MonoidHom.id Cov) fun x => ?_
      apply hcC
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (ρC x)⁻¹ * ρC ((βL ^ 3) x) = 1
      rw [hpow, hγ3]
      simp
    ext x
    exact congrArg (fun f : Cov →* Cov => f x) h3
  · have hh : π.comp βL.toMonoidHom = β.toMonoidHom.comp π := by
      refine eq_of_central_displacement_hom _ _ fun x => ?_
      apply hcK
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (ρK (β (π x)))⁻¹ * ρK (π (βL x)) = 1
      rw [hcomm, hπ, hπ, hβL, inv_mul_cancel]
    intro x
    exact congrArg (fun f : Cov →* K => f x) hh

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem exists_cover_lift_of_equiv [Finite Cov] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hperfC : Group.IsPerfect Cov) (ι : Cov ⧸ Subgroup.center Cov ≃* K ⧸ Subgroup.center K)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* Cov), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : Cov →* E, ∀ g, π (s g) = g)
    (β : MulAut K) (hβ3 : β ^ 3 = 1) :
    ∃ (π : Cov →* K) (βL : MulAut Cov), Function.Surjective π ∧ (∀ x, π x = 1 → x ∈ Subgroup.center Cov) ∧
      βL ^ 3 = 1 ∧ ∀ x, π (βL x) = β (π x) := by
  have hγ3 : onCenterQuotient β ^ 3 = 1 := by
    have := congrArg (centerQuotientHom K) hβ3
    rwa [map_pow, map_one] at this
  obtain ⟨π, βL, hπ, hπc, -, hβL3, hβL⟩ := exists_cover_lift
    (ι.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Cov))) (QuotientGroup.mk' (Subgroup.center K))
    (ι.surjective.comp (QuotientGroup.mk'_surjective _)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ ι.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact hx)
    (Group.isPerfect_def.2 hK.1) hperfC hsec β (onCenterQuotient β)
    (fun k => (onCenterQuotient_apply_mk β k).symm) hγ3
  exact ⟨π, βL, hπ, hπc, hβL3, hβL⟩

end CFSG.LieType.SemisimpleCentralizers.HeldLang
