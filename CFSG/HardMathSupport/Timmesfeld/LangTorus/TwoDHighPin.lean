module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighGraph

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut

set_option linter.unusedSectionVars false


section RankOne

variable {τ : Tag} {L : Type} [Field L]

theorem map_eq_self_of_mul_self_eq_one (σ : L →+* L) {η : L} (h : η * η = 1) : σ η = η := by
  have h1 : (η - 1) * (η + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · rw [sub_eq_zero.1 h2, map_one]
  · rw [eq_neg_of_add_eq_zero_left h2, map_neg, map_one]

theorem pinnedSign_mul_self (β : Fin τ.rank → ℤ) :
    (((pinnedData τ β).2.2 : ℤ) : L) * ((pinnedData τ β).2.2 : ℤ) = 1 := by
  rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp

theorem pinnedX_eq_rootSL2_uSL (β : Fin τ.rank → ℤ) (d : L) :
    pinnedX τ L β d = rootSL2 τ L β (uSL ((((pinnedData τ β).2.2 : ℤ) : L) * d)) := by
  rw [rootSL2_uSL_eq, zsmul_eq_mul, ← mul_assoc, pinnedSign_mul_self, one_mul]

end RankOne

section Pin

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem LangSetup.exists_twoD_pin {r e : ℕ} [Fact r.Prime] [CharP L r] (hq : S.D.q = r ^ e)
    (i : KernelComponent (rootCharHom a)) {v : WeylGroup τ}
    (hv : v ∈ componentWeylGroup (componentRoots (rootCharHom a) i))
    (hΔ : ∀ β ∈ simpleRoots (componentRoots (rootCharHom a) i),
      S.rhoTwist v β ∈ simpleRoots (componentRoots (rootCharHom a) i)) :
    ∃ y ∈ torusGroup τ L ⊔ rootSpan τ L (componentRoots (rootCharHom a) i),
      y ∈ monomialSubgroup τ L ∧ MapsRootLines y v ∧
      ∀ β ∈ simpleRoots (componentRoots (rootCharHom a) i), ∀ A : SL2 L,
        y * S.D.step (rootSL2 τ L β A) * y⁻¹ =
          rootSL2 τ L (S.rhoTwist v β)
            (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  set σ : L →+* L := iterateFrobenius L r e with hσdef
  have hσq : ∀ c, σ c = c ^ S.D.q := fun c => by rw [hσdef, iterateFrobenius_def, hq]
  obtain ⟨g, hgS, hgM, hgv⟩ := exists_lift_mem_closure_reflections (L := L) i
    (componentWeylGroup_le Ψ hv)
  have hπ : weylQuotientHom τ L ⟨g, hgM⟩ = v := weylQuotientHom_eq hgv
  set φ : ModGL τ L →* ModGL τ L := (MulAut.conj g).toMonoidHom.comp S.D.step with hφdef
  have hφ : ∀ x, φ x = g * S.D.step x * g⁻¹ := fun x => rfl
  have hφX : ∀ γ, IsRoot τ γ → ∃ m : L, m ≠ 0 ∧ ∀ c,
      φ (pinnedX τ L γ c) = pinnedX τ L (S.rhoTwist v γ) (m * σ c) := by
    intro γ hγ
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S hγ
    obtain ⟨ν, hν⟩ := monomial_conj_pinnedX hgM ((S.frob.isRoot_iff γ).2 hγ)
    refine ⟨ν * μ, mul_ne_zero ν.ne_zero hμ0, fun c => ?_⟩
    rw [hφ, hμ, hν, hπ, hσq, S.rhoTwist_apply, mul_assoc]
  have hscal : ∀ β ∈ simpleRoots Ψ, ∃ A B : L, A ≠ 0 ∧ A * B = 1 ∧ ∀ c,
      φ (rootSL2 τ L β (uSL c)) = rootSL2 τ L (S.rhoTwist v β) (uSL (A * σ c)) ∧
      φ (rootSL2 τ L β (vSL c)) = rootSL2 τ L (S.rhoTwist v β) (vSL (B * σ c)) := by
    intro β hβ
    have hβr := simpleRoots_isRoot hβ
    have hδr : IsRoot τ (S.rhoTwist v β) := simpleRoots_isRoot (hΔ β hβ)
    obtain ⟨m, hm0, hm⟩ := hφX β hβr
    obtain ⟨m', -, hm'⟩ := hφX (-β) (IsRoot.neg hβr)
    obtain ⟨η, hη, hvβ⟩ := exists_rootSL2_vSL_eq (K := L) hβr
    obtain ⟨η', hη', hvδ⟩ := exists_rootSL2_vSL_eq (K := L) hδr
    set ε : L := (((pinnedData τ β).2.2 : ℤ) : L) with hε
    set ε' : L := (((pinnedData τ (S.rhoTwist v β)).2.2 : ℤ) : L) with hε'
    have hεε : ε * ε = 1 := pinnedSign_mul_self β
    have hεε' : ε' * ε' = 1 := pinnedSign_mul_self (S.rhoTwist v β)
    have hε0 : ε ≠ 0 := fun h => by rw [h, zero_mul] at hεε; exact zero_ne_one hεε
    have hε'0 : ε' ≠ 0 := fun h => by rw [h, zero_mul] at hεε'; exact zero_ne_one hεε'
    have hu : ∀ c, φ (rootSL2 τ L β (uSL c)) =
        rootSL2 τ L (S.rhoTwist v β) (uSL ((ε' * m * ε) * σ c)) := by
      intro c
      rw [rootSL2_uSL_eq, zsmul_eq_mul, hm, pinnedX_eq_rootSL2_uSL, map_mul,
        map_eq_self_of_mul_self_eq_one σ hεε]
      congr 2
      ring
    have hvv : ∀ c, φ (rootSL2 τ L β (vSL c)) =
        rootSL2 τ L (S.rhoTwist v β) (vSL ((η' * m' * η) * σ c)) := by
      intro c
      rw [hvβ, hm', map_neg, hvδ, map_mul, map_eq_self_of_mul_self_eq_one σ hη]
      congr 1
      linear_combination (-(m' * η * σ c)) * hη'
    exact ⟨_, _, mul_ne_zero (mul_ne_zero hε'0 hm0) hε0,
      rank_one_scalar_compat_root hδr φ σ (mul_ne_zero (mul_ne_zero hε'0 hm0) hε0) hu hvv,
      fun c => ⟨hu c, hvv c⟩⟩
  choose! A B hA0 hAB hconj using hscal
  set Δ := simpleRoots Ψ with hΔdef
  let ν : Fin Δ.card → Fin τ.rank → ℤ := fun k =>
    S.rhoTwist v (Δ.equivFin.symm k : Fin τ.rank → ℤ)
  have hνinj : Function.Injective ν :=
    (injective_of_iform _ (S.iform_rhoTwist v)).comp
      (Subtype.val_injective.comp Δ.equivFin.symm.injective)
  have hνΔ : ∀ k, ν k ∈ simpleRoots (kernelRoots (rootCharHom a)) := by
    intro k
    have hβi : ν k ∈ Δ := hΔ _ (Δ.equivFin.symm k).2
    obtain ⟨hβk, hi⟩ := simpleRoots_subset hβi
    rw [mem_simpleRoots_kernelRoots_iff hβk, hi]
    exact hβi
  obtain ⟨cT, hcT⟩ := algebraically_closed_lattice_character_interpolation L τ.rank Δ.card ν
    (linearIndependent_simpleRoots_kernelRoots hνinj hνΔ)
    fun k => (Units.mk0 (A (Δ.equivFin.symm k)) (hA0 _ (Δ.equivFin.symm k).2))⁻¹
  have hχ : ∀ β ∈ Δ, (rootChar cT (S.rhoTwist v β) : L) = (A β)⁻¹ := by
    intro β hβ
    have hk := hcT (Δ.equivFin ⟨β, hβ⟩)
    have hν : ν (Δ.equivFin ⟨β, hβ⟩) = S.rhoTwist v β := by
      simp only [ν, Equiv.symm_apply_apply]
    have hk' : ((∏ j, cT j ^ ν (Δ.equivFin ⟨β, hβ⟩) j : Lˣ) : L) = (A β)⁻¹ := by
      rw [hk]
      simp
    rw [hν] at hk'
    exact hk'
  set y : ModGL τ L := rootDiagUnit τ cT * g with hy
  have hyφ : ∀ x : ModGL τ L, y * S.D.step x * y⁻¹ =
      rootDiagUnit τ cT * φ x * (rootDiagUnit τ cT)⁻¹ := by
    intro x
    rw [hφ, hy]
    group
  have hpin : ∀ β ∈ Δ, ∀ M : SL2 L, y * S.D.step (rootSL2 τ L β M) * y⁻¹ =
      rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map σ M) := by
    intro β hβ M
    have hδr : IsRoot τ (S.rhoTwist v β) := simpleRoots_isRoot (hΔ β hβ)
    have heq := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L))
      (f := ((MulAut.conj y).toMonoidHom.comp S.D.step).comp (rootSL2 τ L β))
      (g := (rootSL2 τ L (S.rhoTwist v β)).comp (Matrix.SpecialLinearGroup.map σ)) ?_
    · exact DFunLike.congr_fun heq M
    rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · change y * S.D.step (rootSL2 τ L β (uSL z)) * y⁻¹ =
        rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map σ (uSL z))
      rw [hyφ, (hconj β hβ z).1, (rootDiagUnit_conj_rootSL2 cT hδr _).1, map_uSL, hχ β hβ,
        ← mul_assoc, inv_mul_cancel₀ (hA0 β hβ), one_mul]
    · change y * S.D.step (rootSL2 τ L β (vSL z)) * y⁻¹ =
        rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map σ (vSL z))
      rw [hyφ, (hconj β hβ z).2, (rootDiagUnit_conj_rootSL2 cT hδr _).2, map_vSL]
      have hχ' : (((rootChar cT (S.rhoTwist v β))⁻¹ : Lˣ) : L) = A β := by
        rw [Units.val_inv_eq_inv_val, hχ β hβ, inv_inv]
      rw [hχ', ← mul_assoc, hAB β hβ, one_mul]
  have hT : rootDiagUnit τ cT ∈ torusGroup τ L := rootDiagUnit_mem_torusGroup cT
  refine ⟨y, mul_mem (Subgroup.mem_sup_left hT) (Subgroup.mem_sup_right hgS),
    mul_mem (torusGroup_le_monomialSubgroup hT) hgM, ?_, hpin⟩
  have h := (mapsRootLines_of_mem_torusGroup hT).mul hgv
  rwa [one_mul] at h

end Pin

end CFSG.HardMathSupport.Timmesfeld.LangTorus
