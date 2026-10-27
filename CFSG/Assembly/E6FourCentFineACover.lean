module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped MatrixGroups



private theorem frame_weyl_perm {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ, s = rootReflection γ}) :
    ∃ π' : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → w • σ a b = σ (π' a) (π' b) := by
  classical
  refine Subgroup.closure_induction
    (p := fun w _ => ∃ π' : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → w • σ a b = σ (π' a) (π' b))
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨γ, hγ, rfl⟩ := hx
    obtain ⟨x', y', hx'y', rfl⟩ := hγ
    exact ⟨Equiv.swap x' y', fun c d _ => hψ.rootReflection_smul hκ hnorm hx'y' c d⟩
  · exact ⟨1, fun a b _ => by simp⟩
  · intro x y hx hy hpx hpy
    obtain ⟨πx, hπx⟩ := hpx
    obtain ⟨πy, hπy⟩ := hpy
    refine ⟨πx * πy, fun a b hab => ?_⟩
    rw [mul_smul, hπy a b hab, hπx (πy a) (πy b) (πy.injective.ne hab)]
    simp only [Equiv.Perm.mul_apply]
  · intro x hx hpx
    obtain ⟨π, hπ⟩ := hpx
    refine ⟨π.symm, fun c d hcd => ?_⟩
    have h := hπ (π.symm c) (π.symm d) (π.symm.injective.ne hcd)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    have h3 := congrArg (fun z => x⁻¹ • z) h
    rw [inv_smul_smul] at h3
    exact h3.symm


theorem e6Four_A5_cover {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hq : S.D.q = 4) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 5 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hn : (componentRoots (rootCharHom a) i).ncard = 30)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (g : Matrix.SpecialLinearGroup (Fin 6) K →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      Nat.card K = 4 ∧ Function.Surjective g ∧
        g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) := by
  classical
  have hℓp : ringChar L ≠ 5 := ringChar_ne_of_pow_eq_one Nat.prime_five hap h1
  have hpL : ((5 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne Nat.prime_five hℓp
  have hTp : rootDiagUnit Tag.E6 a ^ 5 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by rw [hr]; norm_num
  have hn' : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) := by
    rw [hr, hn]
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_five hpL hTp i h2 hn'
  have hcard : (frameRoots σ).ncard = ν * (ν - 1) := by
    have hinj : Set.InjOn (fun p : Fin ν × Fin ν => σ p.1 p.2) {p | p.1 ≠ p.2} := by
      rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
      simp only [Set.mem_setOf_eq] at hab hcd
      obtain ⟨rfl, rfl⟩ := hψ.eq_of_eq hκ hnorm hab hcd h
      rfl
    have himg : frameRoots σ = (fun p : Fin ν × Fin ν => σ p.1 p.2) '' {p | p.1 ≠ p.2} := by
      ext r
      constructor
      · rintro ⟨a, b, hab, rfl⟩
        exact ⟨(a, b), hab, rfl⟩
      · rintro ⟨⟨a, b⟩, hab, rfl⟩
        exact ⟨a, b, hab, rfl⟩
    rw [himg, hinj.ncard_image]
    have hoff : ({p : Fin ν × Fin ν | p.1 ≠ p.2} : Set (Fin ν × Fin ν)) =
        ↑(Finset.univ.offDiag : Finset (Fin ν × Fin ν)) := by
      ext p
      simp [Finset.mem_offDiag]
    rw [hoff, Set.ncard_coe_finset, Finset.offDiag_card]
    rw [Finset.card_univ, Fintype.card_fin, Nat.mul_sub_left_distrib, mul_one]
  have h30 : ν * (ν - 1) = 30 := by
    rw [← hcard, ← hΨ]
    exact hn
  have hν6 : ν = 6 := by
    have hle : ν ≤ 6 := by
      have h1 : (ν : ℤ) * ((ν : ℤ) - 1) = 30 := by
        have hsub : ((ν - 1 : ℕ) : ℤ) = (ν : ℤ) - 1 := Int.ofNat_sub (show 1 ≤ ν by omega)
        rw [← hsub]
        exact_mod_cast h30
      have hsq : (0 : ℤ) ≤ ((ν : ℤ) - 6) ^ 2 := sq_nonneg _
      have : (ν : ℤ) ≤ 6 := by nlinarith
      omega
    interval_cases ν
    · norm_num at h30
    · norm_num at h30
    · norm_num at h30
    · rfl
  cases hν6
  obtain ⟨hs0, hsspec, _hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hsspec' : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    rw [hsdef]; exact hsspec
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have hmem : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]; exact ⟨x, y, hxy, rfl⟩
    have h2' : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
      ⟨_, hmem, rfl⟩
    rw [hsspec', hΨ] at h2'
    exact h2'
  have hneg : ∀ (n : ℕ) (γ : Fin Tag.E6.rank → ℤ),
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] (-γ) =
        -(S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    have hπc : ∀ x y, x ≠ y →
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y) := by
      intro x y hxy
      simpa only [hsdef] using hπ x y hxy
    obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
      split_exists_hom S hT i hν hψ hΨ π hπc hr hchar he hq'
    obtain ⟨hfinK, hcardK⟩ := finite_card_fixSubfield (L := L) (r := r)
      (n := e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (Nat.mul_pos he hs0) σQ hσc
    have hcol1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
      first | exact hs | (rw [← hsdef]; exact hs)
    have hcardK4 : Nat.card (fixSubfield σQ) = 4 := by
      rw [hcardK, hcol1, mul_one, ← hq', hq]
    have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 6) ↥(fixSubfield σQ)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ↥(fixSubfield σQ))
        (by norm_num)
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      le_antisymm (hf2 hperf) hf1
    let g : Matrix.SpecialLinearGroup (Fin 6) ↥(fixSubfield σQ) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      exact ⟨c, Subtype.ext hc⟩
    have hgker : g.ker ≤
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) ↥(fixSubfield σQ)) := by
      intro c hc
      apply hfker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    exact ⟨↥(fixSubfield σQ), inferInstance, hfinK, g, hcardK4, hgsurj, hgker⟩
  ·
    exfalso
    have hs1 : s = 1 := by
      first | exact hs | (rw [hsdef]; exact hs)
    have hπρ : ∀ x y, x ≠ y → S.ρ (σ x y) = σ (π y) (π x) := by
      intro x y hxy
      simpa [hs1, Function.iterate_one] using hπ x y hxy
    obtain ⟨w, hw, hwσ⟩ := hin
    rw [hΨ] at hw
    obtain ⟨π', hπ'⟩ := frame_weyl_perm hψ hκ hnorm hw
    have key : ∀ x y, x ≠ y → π y = π' x ∧ π x = π' y := by
      intro x y hxy
      have hmem : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]; exact ⟨x, y, hxy, rfl⟩
      have heq : σ (π y) (π x) = σ (π' x) (π' y) := by
        rw [← hπρ x y hxy, hwσ (σ x y) hmem, hπ' x y hxy]
      exact hψ.eq_of_eq hκ hnorm (Ne.symm (π.injective.ne hxy)) (π'.injective.ne hxy) heq
    have hab : (0 : Fin 6) ≠ 1 := by decide
    have hac : (0 : Fin 6) ≠ 2 := by decide
    have hbc : (1 : Fin 6) ≠ 2 := by decide
    obtain ⟨h01, -⟩ := key 0 1 hab
    obtain ⟨h02, -⟩ := key 0 2 hac
    exact hbc (π.injective (by rw [h01, h02]))

end CFSG.Assembly

end
