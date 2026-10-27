module

public import CFSG.RankThree.GF2n.Stroth80.KSSec95Eig

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

theorem twisted_pow_apply_of_apply_eq_smul {K A : Type*} [Field K] [AddCommGroup A] [Module K A]
    (R : Module.End K A) (u : A) (c : K) (hu : R u = c • u) (n : ℕ) :
    (R ^ n) u = c ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hu, smul_smul, pow_succ]

theorem twisted_apply_exists_smul {K A : Type*} [Field K] [AddCommGroup A] [Module K A]
    (f : K →+* Module.End K A) (α : K) (hα : ∀ a : K, a ≠ 0 → ∃ n : ℕ, α ^ n = a)
    (u : A) (c : K) (hu : f α u = c • u) (ν : K) : ∃ a : K, f ν u = a • u := by
  by_cases hν : ν = 0
  · exact ⟨0, by simp [hν]⟩
  · obtain ⟨n, rfl⟩ := hα ν hν
    exact ⟨c ^ n, by rw [map_pow, twisted_pow_apply_of_apply_eq_smul (f α) u c hu n]⟩

theorem twisted_ringEquiv_of_common {K A : Type*} [Field K] [Finite K] [AddCommGroup A]
    [Module K A] (f : K →+* Module.End K A) (u : A) (hu : u ≠ 0)
    (h : ∀ ν : K, ∃ a : K, f ν u = a • u) : ∃ σ : K ≃+* K, ∀ ν : K, f ν u = σ ν • u := by
  classical
  choose s hs using h
  have huniq : ∀ x y : K, x • u = y • u → x = y := fun x y hxy => smul_left_injective K hu hxy
  let sHom : K →+* K :=
    { toFun := s
      map_one' := huniq _ _ (by rw [← hs 1, map_one, Module.End.one_apply, one_smul])
      map_mul' := fun a b => huniq _ _ (by
        rw [← hs (a * b), map_mul, Module.End.mul_apply, hs b, map_smul, hs a, smul_smul,
          mul_comm])
      map_zero' := huniq _ _ (by rw [← hs 0, map_zero, LinearMap.zero_apply, zero_smul])
      map_add' := fun a b => huniq _ _ (by
        rw [← hs (a + b), map_add, LinearMap.add_apply, hs a, hs b, add_smul]) }
  have hbij : Function.Bijective sHom :=
    ⟨sHom.injective, Finite.surjective_of_injective sHom.injective⟩
  refine ⟨RingEquiv.ofBijective sHom hbij, fun ν => ?_⟩
  rw [hs ν]
  rfl

theorem exists_twisted_eigenbasis {K A : Type*} [Field K] [Finite K] [AddCommGroup A]
    [Module K A] (hA : Module.finrank K A = 2) (f : K →+* Module.End K A) :
    ∃ (u₁ u₂ : A) (σ₁ σ₂ : K ≃+* K), LinearIndependent K ![u₁, u₂] ∧
      ∀ ν : K, f ν u₁ = σ₁ ν • u₁ ∧ f ν u₂ = σ₂ ν • u₂ := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  set α : K := (g : K) with hαdef
  have hpowα : ∀ a : K, a ≠ 0 → ∃ n : ℕ, α ^ n = a := by
    intro a ha
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 a ha))
    exact ⟨n, by rw [hαdef, ← Units.val_pow_eq_pow_val, hn, Units.val_mk0]⟩
  have hR : (f α) ^ Fintype.card K = f α := by
    rw [← map_pow, FiniteField.pow_card]
  have htop := CFSG.RankThree.GF2n.Stroth80.KS95.iSup_eigenspace_eq_top_of_pow_card (f α) hR
  have hnt : Nontrivial A := Module.nontrivial_of_finrank_eq_succ hA
  obtain ⟨c₁, hc₁⟩ : ∃ c : K, (f α).eigenspace c ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have h0 : ⨆ c : K, (f α).eigenspace c = ⊥ := iSup_eq_bot.2 hcon
    rw [htop] at h0
    exact top_ne_bot h0
  obtain ⟨u₁, hu₁E, hu₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc₁
  have hu₁' : f α u₁ = c₁ • u₁ := Module.End.mem_eigenspace_iff.1 hu₁E
  obtain ⟨u₂, c₂, hu₂', hu₂span⟩ :
      ∃ u₂ : A, ∃ c : K, f α u₂ = c • u₂ ∧ u₂ ∉ Submodule.span K {u₁} := by
    by_contra hcon
    push Not at hcon
    have hle : (⨆ c : K, (f α).eigenspace c) ≤ Submodule.span K {u₁} := by
      refine iSup_le fun c => ?_
      intro v hv
      exact hcon v c (Module.End.mem_eigenspace_iff.1 hv)
    rw [htop] at hle
    have htopspan : Submodule.span K {u₁} = ⊤ := top_le_iff.1 hle
    have h1 : Module.finrank K (Submodule.span K {u₁}) = 1 := finrank_span_singleton hu₁
    have h2 := congrArg (fun S : Submodule K A => Module.finrank K ↥S) htopspan
    simp only [finrank_top, hA] at h2
    omega
  have hu₂ : u₂ ≠ 0 := by
    rintro rfl
    exact hu₂span (Submodule.zero_mem _)
  have hli : LinearIndependent K ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hu₁, rfl⟩
    · exfalso
      apply hu₂span
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      have h3 : t • u₂ = -(s • u₁) := eq_neg_of_add_eq_zero_right hst
      calc (-(t⁻¹ * s)) • u₁ = t⁻¹ • -(s • u₁) := by rw [smul_neg, smul_smul, neg_smul]
        _ = t⁻¹ • t • u₂ := by rw [h3]
        _ = u₂ := inv_smul_smul₀ ht u₂
  obtain ⟨σ₁, hσ₁⟩ := twisted_ringEquiv_of_common f u₁ hu₁
    (twisted_apply_exists_smul f α hpowα u₁ c₁ hu₁')
  obtain ⟨σ₂, hσ₂⟩ := twisted_ringEquiv_of_common f u₂ hu₂
    (twisted_apply_exists_smul f α hpowα u₂ c₂ hu₂')
  exact ⟨u₁, u₂, σ₁, σ₂, hli, fun ν => ⟨hσ₁ ν, hσ₂ ν⟩⟩

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
