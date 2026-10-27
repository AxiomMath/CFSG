module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Iso
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Blocks

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)}

theorem l154td4_three_blocks_absurd (hΨ : IsRootComponent Ψ) (hr : compRank Ψ = 4)
    (ρ₀ : Equiv.Perm (Fin τ.rank → ℤ)) (hiso : ∀ γ δ, iform (ρ₀ γ) (ρ₀ δ) = iform γ δ)
    (horth : ∀ k l : Fin 3, k ≠ l → ∀ γ ∈ Ψ, ∀ δ ∈ Ψ,
      iform ((ρ₀ : (Fin τ.rank → ℤ) → _)^[k] γ) ((ρ₀ : (Fin τ.rank → ℤ) → _)^[l] δ) = 0) :
    False := by
  classical
  set f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) := ⇑ρ₀ with hf
  have hisok : ∀ (k : ℕ) (γ δ : Fin τ.rank → ℤ), iform (f^[k] γ) (f^[k] δ) = iform γ δ := by
    intro k
    induction k with
    | zero => exact fun γ δ => rfl
    | succ k ih =>
      intro γ δ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hiso _ _).trans (ih γ δ)
  let v : Fin 3 × simpleRoots Ψ → (Fin τ.rank → ℤ) := fun p => f^[p.1] (p.2 : Fin τ.rank → ℤ)
  have hindep : LinearIndependent ℚ
      (fun p : Fin 3 × simpleRoots Ψ => (fun j => ((v p j : ℤ) : ℚ) : Fin τ.rank → ℚ)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ, Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ p, g p • v p = 0 := by
      funext j
      have h1 := congrFun hg j
      rw [Finset.sum_apply] at h1 ⊢
      simp only [Pi.smul_apply, Pi.zero_apply] at h1 ⊢
      have h2 : ((∑ p, g p * v p j : ℤ) : ℚ) = 0 := by
        push_cast
        simpa only [zsmul_eq_mul] using h1
      simpa only [smul_eq_mul] using Int.cast_eq_zero.1 h2
    set X : Fin 3 → (Fin τ.rank → ℤ) :=
      fun k => ∑ β : simpleRoots Ψ, g (k, β) • f^[k] (β : Fin τ.rank → ℤ) with hX
    have hsum : ∑ k, X k = 0 := by
      rw [← hg']
      simp only [hX, Fintype.sum_prod_type, v]
    have hXorth : ∀ k l : Fin 3, k ≠ l → iform (X k) (X l) = 0 := by
      intro k l hkl
      simp only [hX]
      rw [iform_sum_smul_left]
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [iform_sum_smul_right]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun β' _ => ?_)
      rw [horth k l hkl β (simpleRoots_subset β.2) β' (simpleRoots_subset β'.2), mul_zero]
    have hXzero : ∀ k, X k = 0 := by
      intro k
      have h1 : iform (X k) (∑ l, X l) = 0 := by rw [hsum]; simp [iform]
      rw [iform_finset_sum_right, Finset.sum_eq_single k
        (fun l _ hl => hXorth k l (Ne.symm hl)) (by simp)] at h1
      exact eq_zero_of_iform_self_eq_zero h1
    have hYzero : ∀ k : Fin 3, ∑ β : simpleRoots Ψ, g (k, β) • (β : Fin τ.rank → ℤ) = 0 := by
      intro k
      have e1 := iform_sum_smul_sum_smul (Finset.univ : Finset (simpleRoots Ψ))
        (fun β => g (k, β)) (fun β => f^[k] (β : Fin τ.rank → ℤ))
      have e2 := iform_sum_smul_sum_smul (Finset.univ : Finset (simpleRoots Ψ))
        (fun β => g (k, β)) (fun β : simpleRoots Ψ => (β : Fin τ.rank → ℤ))
      simp only [hisok k] at e1
      have h3 : iform (X k) (X k) = 0 := by rw [hXzero k]; simp [iform]
      have h4 : iform (∑ β : simpleRoots Ψ, g (k, β) • f^[k] (β : Fin τ.rank → ℤ))
          (∑ β : simpleRoots Ψ, g (k, β) • f^[k] (β : Fin τ.rank → ℤ)) = 0 := h3
      rw [e1, ← e2] at h4
      exact eq_zero_of_iform_self_eq_zero h4
    intro p
    obtain ⟨k, β⟩ := p
    set cfun : (Fin τ.rank → ℤ) → ℤ :=
      fun γ => if h : γ ∈ simpleRoots Ψ then g (k, ⟨γ, h⟩) else 0 with hcfun
    have hsumc : ∑ γ ∈ simpleRoots Ψ, cfun γ • γ =
        ∑ γ ∈ simpleRoots Ψ, (fun _ => (0 : ℤ)) γ • γ := by
      rw [← Finset.sum_coe_sort (simpleRoots Ψ) (fun γ => cfun γ • γ)]
      have : ∀ x : simpleRoots Ψ, cfun (x : Fin τ.rank → ℤ) = g (k, x) := fun x => by
        simp only [hcfun, dif_pos x.2]
      simp only [this, zero_smul, Finset.sum_const_zero]
      exact hYzero k
    have := coords_unique hΨ hsumc β β.2
    simpa only [hcfun, dif_pos β.2] using this
  have hcard := hindep.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, ← compRank_eq_card hΨ, hr,
    Module.finrank_fin_fun] at hcard
  have := rank_le_eight τ
  omega

end Blocks

section Periods

variable {α : Type*}

theorem l154td4_image_period_mul {f : α → α} {Ψ : Set α} {m : ℕ} (hm : f^[m] '' Ψ = Ψ)
    (q : ℕ) : f^[m * q] '' Ψ = Ψ := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add, Set.image_comp, hm, ih]

theorem l154td4_image_ne_of_lt {f : α → α} (hf : Function.Injective f) {Ψ : Set α} {m : ℕ}
    (hmin : ∀ k, 0 < k → k < m → f^[k] '' Ψ ≠ Ψ) {k l : ℕ} (hkl : k < l) (hl : l < m) :
    f^[k] '' Ψ ≠ f^[l] '' Ψ := by
  intro h
  have h1 : f^[k] '' (f^[l - k] '' Ψ) = f^[k] '' Ψ := by
    rw [← Set.image_comp, ← Function.iterate_add, Nat.add_sub_cancel' hkl.le]
    exact h.symm
  have h2 : f^[l - k] '' Ψ = Ψ :=
    Set.image_injective.2 (hf.iterate k) h1
  exact hmin (l - k) (by omega) (by omega) h2

end Periods

section Orbit

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem l154td4_iform_eq_zero_of_ne {j j' : KernelComponent χ} (hjj' : j ≠ j')
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ j) (hβ : β ∈ componentRoots χ j') :
    iform α β = 0 := by
  obtain ⟨hα1, hαj⟩ := hα
  obtain ⟨hβ1, hβj⟩ := hβ
  exact iform_eq_zero_of_mk_ne (α := ⟨α, hα1⟩) (β := ⟨β, hβ1⟩) (by rw [hαj, hβj]; exact hjj')

end Orbit

section Roots

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p p' : ℕ}

theorem l154td4_iterate_isRoot (S₀ : LangSetup τ L p') (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : IsRoot τ ((S₀.ρ : (Fin τ.rank → ℤ) → _)^[k] γ) := by
  induction k with
  | zero => exact hγ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (S₀.frob.isRoot_iff _).2 ih

theorem l154td4_rho_iterate_eq (S : LangSetup τ L p) (S₀ : LangSetup τ L p')
    (hcube : ∀ γ, IsRoot τ γ → S₀.ρ (S₀.ρ (S₀.ρ γ)) = S.ρ γ) (k : ℕ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ = (S₀.ρ : (Fin τ.rank → ℤ) → _)^[3 * k] γ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hr := l154td4_iterate_isRoot S₀ (3 * k) hγ
    rw [← hcube _ hr, show 3 * (k + 1) = 3 + 3 * k by ring, Function.iterate_add_apply]
    rfl

theorem l154td4_isIsometry_of_period (S₀ : LangSetup τ L p') {Ψ : Set (Fin τ.rank → ℤ)} {m : ℕ}
    (hm : (S₀.ρ : (Fin τ.rank → ℤ) → _)^[m] '' Ψ = Ψ) :
    IsIsometry Ψ ((S₀.ρ : (Fin τ.rank → ℤ) → _)^[m]) := by
  have hform : ∀ (k : ℕ) (γ δ : Fin τ.rank → ℤ),
      iform ((S₀.ρ : (Fin τ.rank → ℤ) → _)^[k] γ) ((S₀.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) =
        iform γ δ := by
    intro k
    induction k with
    | zero => exact fun γ δ => rfl
    | succ k ih =>
      intro γ δ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (S₀.frob.iform_eq _ _).trans (ih γ δ)
  have hneg : ∀ (k : ℕ) (γ : Fin τ.rank → ℤ),
      (S₀.ρ : (Fin τ.rank → ℤ) → _)^[k] (-γ) = -(S₀.ρ : (Fin τ.rank → ℤ) → _)^[k] γ := by
    intro k
    induction k with
    | zero => exact fun γ => rfl
    | succ k ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S₀.frob.neg_eq]
  refine ⟨⟨fun x hx => ?_, (S₀.ρ.injective.iterate m).injOn, fun y hy => ?_⟩,
    fun γ _ δ _ => hform m γ δ, fun γ _ => hneg m γ⟩
  · rw [← hm]
    exact Set.mem_image_of_mem _ hx
  · rw [← hm] at hy
    exact hy

end Roots

section Cube

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p p' : ℕ}

theorem l154td4_twistInner_of_cube (S : LangSetup τ L p) (S₀ : LangSetup τ L p')
    (hcube : ∀ γ, IsRoot τ γ → S₀.ρ (S₀.ρ (S₀.ρ γ)) = S.ρ γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hT₀ : rootDiagUnit τ a ∈ S₀.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hne : Ψ.Nonempty := by
    obtain ⟨⟨γ, hγ⟩, hγi⟩ := Quotient.exists_rep i
    exact ⟨γ, hγ, hγi⟩
  obtain ⟨hs0, hsΨ, hsmin⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨hm0, hmΨ, hmmin⟩ := outer_componentOrbitLength_spec S₀ hT₀ i
  set s := componentOrbitLength S.ρ Ψ with hs
  set m := componentOrbitLength S₀.ρ Ψ with hm
  have hroot : ∀ γ ∈ Ψ, IsRoot τ γ := hΨ.isRoot
  have himg : ∀ k, (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ =
      (S₀.ρ : (Fin τ.rank → ℤ) → _)^[3 * k] '' Ψ := by
    intro k
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, (l154td4_rho_iterate_eq S S₀ hcube k (hroot γ hγ)).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, l154td4_rho_iterate_eq S S₀ hcube k (hroot γ hγ)⟩
  have hdvd : m ∣ 3 * s := by
    have h1 : (S₀.ρ : (Fin τ.rank → ℤ) → _)^[3 * s] '' Ψ = Ψ := by rw [← himg]; exact hsΨ
    have h2 := iterate_image_period S₀ hmΨ (3 * s)
    rw [h1] at h2
    by_contra hnd
    have hpos : 0 < 3 * s % m := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    exact hmmin _ hpos (Nat.mod_lt _ hm0) h2.symm
  by_cases h3 : 3 ∣ m
  · exfalso
    have hm3 : 3 ≤ m := Nat.le_of_dvd hm0 h3
    choose j hj using fun k : Fin 3 => outer_iterate_image_component S₀ hT₀ i (k : ℕ)
    have hjne : ∀ k l : Fin 3, k ≠ l → j k ≠ j l := by
      intro k l hkl hjkl
      have hk3 : (k : ℕ) < 3 := k.isLt
      have hl3 : (l : ℕ) < 3 := l.isLt
      have hsets : (S₀.ρ : (Fin τ.rank → ℤ) → _)^[(k : ℕ)] '' Ψ =
          (S₀.ρ : (Fin τ.rank → ℤ) → _)^[(l : ℕ)] '' Ψ := by
        rw [← hj k, ← hj l, hjkl]
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with hlt | hlt
      · exact l154td4_image_ne_of_lt S₀.ρ.injective hmmin hlt (by omega) hsets
      · exact l154td4_image_ne_of_lt S₀.ρ.injective hmmin hlt (by omega) hsets.symm
    refine l154td4_three_blocks_absurd hΨ hr S₀.ρ S₀.frob.iform_eq
      fun k l hkl γ hγ δ hδ => ?_
    refine l154td4_iform_eq_zero_of_ne (hjne k l hkl) ?_ ?_
    · rw [hj k]
      exact ⟨γ, hγ, rfl⟩
    · rw [hj l]
      exact ⟨δ, hδ, rfl⟩
  · have hcop : Nat.Coprime m 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    have hms : m ∣ s := hcop.dvd_of_dvd_mul_left hdvd
    have hsm : s ∣ m := by
      have h1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] '' Ψ = Ψ := by
        rw [himg, mul_comm]
        exact l154td4_image_period_mul hmΨ 3
      have h2 := iterate_image_period S hsΨ m
      rw [h1] at h2
      by_contra hnd
      have hpos : 0 < m % s := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      exact hsmin _ hpos (Nat.mod_lt _ hs0) h2.symm
    have hsm' : s = m := Nat.dvd_antisymm hsm hms
    obtain ⟨u, hu, huγ⟩ := l154td4_twistInner_iterate_six hΨ hne hr
      (l154td4_isIsometry_of_period S₀ hmΨ)
    refine ⟨u, hu, fun γ hγ => ?_⟩
    rw [← huγ γ hγ, l154td4_rho_iterate_eq S S₀ hcube _ (hroot γ hγ), ← Function.iterate_mul, hsm',
      show 3 * (2 * m) = m * 6 by ring]

end Cube

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
