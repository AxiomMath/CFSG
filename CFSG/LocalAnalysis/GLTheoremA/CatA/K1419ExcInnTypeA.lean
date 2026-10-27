module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnArith
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped MatrixGroups

section Frames

theorem l3u3_inn_ncard_frameRoots_le {τ : Tag} {ν : ℕ} (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) :
    (frameRoots σ).ncard ≤ ν * ν - ν := by
  classical
  have h : frameRoots σ = ↑((Finset.univ : Finset (Fin ν)).offDiag.image fun p => σ p.1 p.2) := by
    ext x
    simp only [frameRoots, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_offDiag, Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨x1, x2, hne, rfl⟩
      exact ⟨x1, x2, hne, rfl⟩
    · rintro ⟨x1, x2, hne, rfl⟩
      exact ⟨x1, x2, hne, rfl⟩
  rw [h, Set.ncard_coe_finset]
  calc _ ≤ (Finset.univ : Finset (Fin ν)).offDiag.card := Finset.card_image_le
    _ = ν * ν - ν := by rw [Finset.offDiag_card]; simp

end Frames

section FrameShape


variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem l3u3_inn_weyl_perm {ρ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ, s = rootReflection γ}) :
    ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y → w • σ x y = σ (π x) (π y) := by
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, ⟨x, y', hxy, rfl⟩, rfl⟩ := hy
    exact ⟨Equiv.swap x y', fun c d _ => h.rootReflection_smul hκ hnorm hxy c d⟩
  | one => exact ⟨1, fun x y _ => by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨πu, hu⟩ := hu
    obtain ⟨πv, hv⟩ := hv
    refine ⟨πu * πv, fun x y hxy => ?_⟩
    rw [mul_smul, hv x y hxy, hu _ _ (πv.injective.ne hxy)]
    rfl
  | inv u _ hu =>
    obtain ⟨π, hπ⟩ := hu
    refine ⟨π⁻¹, fun x y hxy => ?_⟩
    rw [inv_smul_eq_iff, hπ _ _ (π⁻¹.injective.ne hxy)]
    simp

theorem l3u3_inn_false_of_unitary (hν : 3 ≤ ν) {ρ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (h : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (φ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → φ (σ a b) = σ (π b) (π a))
    (hin : ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ, s = rootReflection γ},
      ∀ γ ∈ frameRoots σ, φ γ = w • γ) : False := by
  obtain ⟨w, hw, hwφ⟩ := hin
  obtain ⟨π', hπ'⟩ := l3u3_inn_weyl_perm h hκ hnorm hw
  have key : ∀ x y : Fin ν, x ≠ y → π y = π' x := fun x y hxy => by
    have h1 := hwφ (σ x y) ⟨x, y, hxy, rfl⟩
    rw [hπ x y hxy, hπ' x y hxy] at h1
    exact (h.eq_of_eq hκ hnorm (π.injective.ne hxy.symm) (π'.injective.ne hxy) h1).1
  have h0 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  have h0' : (⟨0, by omega⟩ : Fin ν) ≠ ⟨2, by omega⟩ := by simp
  have h12 : π ⟨1, by omega⟩ = π ⟨2, by omega⟩ := (key _ _ h0).trans (key _ _ h0').symm
  have := π.injective h12
  simp at this

end FrameShape

section TypeA


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
  {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}

theorem l3u3_inn_typeA_false (hF : L3U3Facts) (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (hk : twistKind S.ρ (rootCharHom a) i = .inner)
    (hbig : 14 ≤ (componentRoots (rootCharHom a) i).ncard)
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hL : L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  classical
  haveI := finite_rationalComponent S a i
  have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by
    by_contra h
    have h1 : compRank (componentRoots (rootCharHom a) i) ≤ 1 := by omega
    have : compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) ≤ 1 * 2 :=
      Nat.mul_le_mul h1 (by omega)
    omega
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    norm_num
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
    g2LongA2Frame_proved S Nat.prime_three h3L hTp i h2 hA.2
  have hν5 : 5 ≤ ν := by
    by_contra hlt
    have hle := l3u3_inn_ncard_frameRoots_le σ
    rw [← hΨ] at hle
    have : ν * ν - ν ≤ 12 := by
      have : ν ≤ 4 := by omega
      interval_cases ν <;> simp
    omega
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hk
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    have hr2 : r = 2 := CharP.eq L hchar ‹CharP L 2›
    subst hr2
    haveI : Fact (Nat.Prime 2) := ⟨hr⟩
    obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := split_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
    obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := 2) (n := e * s)
      (Nat.mul_pos he hs0) σQ hσc
    have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      le_antisymm (hf2 hperf) hf1
    let g : SL(ν, ↥(fixSubfield σQ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      exact ⟨c, Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) := by
      intro c hc
      apply hfker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    have hcard := l3u3_inn_card_centerQuotient_mul hperf g hgsurj hgker
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center _ ν (by omega),
      CFSG.OrderReductions.LinearOrders.card_specialLinear _ ν (by omega), hKcard] at hcard
    exact l3u3_inn_not_order_of_card_sl hν5 (Nat.mul_pos he hs0) (hF.order _ hL) hcard
  · exact l3u3_inn_false_of_unitary hν hψ hκ hnorm _ π hπ (by rw [← hΨ]; exact hinner)

end TypeA

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
