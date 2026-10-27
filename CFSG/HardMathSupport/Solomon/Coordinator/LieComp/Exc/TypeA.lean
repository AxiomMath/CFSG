module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem ringChar_ne_three_of_pow_three {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) : ringChar L ≠ 3 := by
  intro h3
  haveI : CharP L 3 := ringChar.of_eq h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply h1
  have ha : a = 1 := by
    funext j
    have h : ((a j : L) - 1) ^ 3 = 0 := by
      rw [sub_pow_char, one_pow, sub_eq_zero]
      simpa using congrArg (fun u : Lˣ => (u : L)) (hap j)
    have h' : (a j : L) - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h
    exact Units.ext (sub_eq_zero.1 h')
  rw [ha]
  exact rootDiagUnit_one

@[reducible] private noncomputable def suFix {L : Type} [Field L] {ν : ℕ} (σ : L ≃+* L) : Subgroup SL(ν, L) :=
  CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σ)

section TypeA


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem rationalLieType_of_split_frame (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b))
    (hℓ3 : ringChar L ≠ 3) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := split_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfinK, -⟩ := finite_card_fixSubfield (L := L) (r := r)
    (n := e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
    (Nat.mul_pos he hs0) σQ hσc
  have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hperf) hf1
  let g : SL(ν, ↥(fixSubfield σQ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
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
  have hring : ringChar (fixSubfield σQ) = ringChar L := ringChar_subfield' _
  have hres := rationalLieType_of_slCover (K := ↥(fixSubfield σQ)) (ν := ν) (by omega)
    (fun h => by omega) (by rw [hring]; exact hℓ3)
    (rationalComponent S.ρ S.Γ (rootCharHom ta) i) g hgsurj hgker
  rwa [hring] at hres

theorem rationalLieType_of_unitary_frame (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfin, hqsC, hc216⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  by_cases h32 : (ν, r ^ (e * s)) = (3, 2)
  ·
    exfalso
    have hcard := hc216 h32
    haveI := hfin
    haveI := Fintype.ofFinite ↥(suFix (ν := ν) σQ)
    haveI : Group.IsSolvable ↥(suFix (ν := ν) σQ) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    haveI : Group.IsSolvable ↥f.range :=
      Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    haveI : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
    exact not_isSolvable_of_isQuasisimple hQS inferInstance
  · have hCperf : Group.IsPerfect ↥(suFix (ν := ν) σQ) := (hqsC h32).1
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
      le_antisymm (hf2 hCperf) hf1
    let g : ↥(suFix (ν := ν) σQ) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
      f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
    obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
    haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
      rw [hFcard]
      exact (pow_pos (pow_pos hr.pos _) 2).ne')
    haveI : Fintype ↥F := Fintype.ofFinite ↥F
    have hFcard' : Fintype.card ↥F = (r ^ (e * s)) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFcard
    let g' : ↥(StatedSU ν (r ^ (e * s)) F) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := g.comp eC.toMonoidHom
    have hg'surj : Function.Surjective g' := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      obtain ⟨c', rfl⟩ := eC.surjective c
      exact ⟨c', Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center ↥(suFix (ν := ν) σQ) := by
      intro c hc
      apply hfker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    have hg'ker : g'.ker ≤ Subgroup.center ↥(StatedSU ν (r ^ (e * s)) F) :=
      ker_comp_mulEquiv_le_center eC g hgker
    have hring : ringChar ↥F = ringChar L := ringChar_subfield' _
    have hres := rationalLieType_of_suCover hFcard' hν h32 (rationalComponent S.ρ S.Γ
      (rootCharHom ta) i) g' hg'surj hg'ker
    rwa [hring] at hres

variable {a : Fin τ.rank → Lˣ}

theorem rationalLieType_of_typeA (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓ3 : ringChar L ≠ 3 := ringChar_ne_three_of_pow_three hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · exact rationalLieType_of_rankOne S hT i hr1 (by rw [hA.2, hr1]) hℓ3 hQS
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have h3L : ((3 : ℕ) : L) ≠ 0 := by
      intro h
      have hd : ringChar L ∣ 3 := (ringChar.spec L 3).1 (by exact_mod_cast h)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h' | h'
      · exact CharP.ringChar_ne_one h'
      · exact hℓ3 h'
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S Nat.prime_three h3L hTp i h2 hA.2
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
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact rationalLieType_of_split_frame S hT i hν hψ hΨ π hπ hℓ3
    · exact rationalLieType_of_unitary_frame S hT i hν hψ hΨ π hπ hQS

end TypeA

section NonA


@[expose] def ExcRationalLieTypesNonA : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excRationalLieTypes_of_nonA (h : ExcRationalLieTypesNonA) : ExcRationalLieTypes := by
  intro τ L _ _ p₀ S a hT hap h1 i hq
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact rationalLieType_of_typeA S hT hap h1 i hA hq
  · exact h τ L p₀ S a hT hap h1 i hA hq

end NonA

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
