module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups commutatorElement

private lemma ncard_frameRoots_le_six
    {τ : Tag} (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ) :
    (frameRoots σ).ncard ≤ 6 := by
  classical
  let g : Fin 6 → Fin τ.rank → ℤ :=
    ![σ 0 1, σ 0 2, σ 1 0, σ 1 2, σ 2 0, σ 2 1]
  have hsub : frameRoots σ ⊆ (Finset.univ.image g : Finset (Fin τ.rank → ℤ)) := by
    rintro r ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have h1 : (frameRoots σ).ncard ≤ (Finset.univ.image g).card := by
    rw [← Set.ncard_coe_finset (Finset.univ.image g)]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have h2 : (Finset.univ.image g).card ≤ 6 := by
    calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin 6)).card :=
          Finset.card_image_le
      _ = 6 := by simp
  omega

private theorem rationalComponent_suN_quasisimple_of_not_small
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hkind : twistKind S.ρ (rootCharHom ta) i = .suN)
    (hnot : ¬ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 2 ∧
      (componentRoots (rootCharHom ta) i).ncard = 6))
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hkind
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hkind
    exact absurd hkind (by decide)
  have hmaps : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈ frameRoots σ := by
    intro a b hab
    have h1 : σ a b ∈ componentRoots (rootCharHom ta) i := by
      rw [hΨ]
      exact ⟨a, b, hab, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i := ⟨_, h1, rfl⟩
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
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨a, b, hab, rfl⟩ := hγ
      rw [hπ a b hab, hwσ]
  · obtain ⟨h1, -⟩ := rationalComponent_of_unitary_frame_T S hT i hν hψ hΨ π hπ
    refine h1 ?_
    intro h32
    have hQ2 : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 2 :=
      congrArg Prod.snd h32
    have hν3 : ν = 3 := congrArg Prod.fst h32
    apply hnot
    refine ⟨hQ2, ?_⟩
    have h2 : 2 ≤ compRank (componentRoots (rootCharHom ta) i) := (suN_rank_ncard hkind).1
    have hn : (componentRoots (rootCharHom ta) i).ncard =
        compRank (componentRoots (rootCharHom ta) i) *
          (compRank (componentRoots (rootCharHom ta) i) + 1) := (suN_rank_ncard hkind).2
    have hle : (componentRoots (rootCharHom ta) i).ncard ≤ 6 := by
      rw [hΨ]
      subst hν3
      exact ncard_frameRoots_le_six σ
    have hge : 6 ≤ (componentRoots (rootCharHom ta) i).ncard := by
      rw [hn]
      have h3 : 3 ≤ compRank (componentRoots (rootCharHom ta) i) + 1 := Nat.succ_le_succ h2
      calc 6 = 2 * 3 := by norm_num
        _ ≤ compRank (componentRoots (rootCharHom ta) i) *
              (compRank (componentRoots (rootCharHom ta) i) + 1) := Nat.mul_le_mul h2 h3
    omega

private theorem rationalComponent_inner_small_quasisimple_of_not_rankOne
    {τ : Tag} {L : Type} [Field L]
    [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hp : p.Prime) (hp5 : τ = .G2 → 5 ≤ p)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4)
    (hnrank : ¬ ∀ α ∈ componentRoots (rootCharHom a) i,
      ∀ δ ∈ componentRoots (rootCharHom a) i, δ = α ∨ δ = -α) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : r ^ (e * s) < 4 := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  set C := componentRootSpan (fixSubfield σ) (rootCharHom a) i with hCdef
  obtain ⟨f₁, hf₁1, -, -⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  obtain ⟨hDQ, hD⟩ := smallFieldInner_quasisimple_of_not_rankOne (rootCharHom a) i hp hp5
      (fun γ hγ => rootChar_pow_eq_one_of_pow hTp hγ)
      (by obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one ha1; exact ⟨γ, hγ, hne⟩) hKle hnrank
  have hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ (⁅C, C⁆).map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    rcases hD with hD2 | hDC
    · have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
        intro d hd hd0
        let : Fintype (fixSubfield σ) := Fintype.ofFinite _
        have hcard : Fintype.card (fixSubfield σ) = 2 := by
          rw [← Nat.card_eq_fintype_card]; exact hD2
        have hdK : d ∈ fixSubfield σ := hd
        have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : fixSubfield σ)
          (fun h => hd0 (congrArg Subtype.val h))
        rw [hcard] at h1
        simpa using congrArg Subtype.val h1
      have := orbit_commutator_mem_commutator_CQT S hT i hs hmin σ hsL hF hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
    · have := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← hDC] at this
  obtain ⟨f, hf1, hker, hf2⟩ := rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
    ⁅C, C⁆ (Subgroup.commutator_le_self _ |>.trans le_rfl) hY
  have hperfD : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := Subgroup.isPerfect_iff.1 hDQ.1
  rw [le_antisymm hf1 (hf2 hperfD)]
  exact isQuasisimple_range_of_ker_le_center hDQ f hker

theorem langQuasisimpleOfNotSmallSolv :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ p : ℕ) (S : LangSetup τ L p₀),
      τ ≠ .G2 → p.Prime → (p : L) ≠ 0 → ∀ a : Fin τ.rank → Lˣ,
        rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 →
        ∀ i : KernelComponent (rootCharHom a),
          ¬ ((S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 3 ∧
                (componentRoots (rootCharHom a) i).ncard = 2) ∨
             (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
                twistKind S.ρ (rootCharHom a) i = .suN ∧
                (componentRoots (rootCharHom a) i).ncard = 6)) →
          CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  intro τ L _ _ p₀ p S hne hp hpL a hT hap h1 i hnot
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | exc => exact langSetup_tame_exc_of_prime S hp hpL hT hTp h1 i hk
  | twoD => exact langSetup_tame_twoD_of_prime S hp hpL hT hTp h1 i hk
  | suN =>
    obtain ⟨h2, hn⟩ := suN_rank_ncard hk
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
    have hnotsuN : ¬ (S.D.q ^
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
        (componentRoots (rootCharHom a) i).ncard = 6) := by
      rintro ⟨hQ2, hn6⟩
      exact hnot (Or.inr ⟨hQ2, hk, hn6⟩)
    exact rationalComponent_suN_quasisimple_of_not_small S hT i hk hnotsuN hν hψ hκ hnorm hΨ
  | inner =>
    by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · exact rationalComponent_quasisimple_inner_of_four_leT S rootAutIsWeyl_holds hT i hk hQ
    · have hQlt : S.D.q ^
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4 := not_le.1 hQ
      have hQ3 : S.D.q ^
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 3 := by omega
      have hnrank : ¬ ∀ α ∈ componentRoots (rootCharHom a) i,
          ∀ δ ∈ componentRoots (rootCharHom a) i, δ = α ∨ δ = -α := by
        intro hrank
        have hncard2 := ncard_componentRoots_eq_two_of_rank_one (rootCharHom a) i hrank
        exact hnot (Or.inl ⟨hQ3, hncard2⟩)
      exact rationalComponent_inner_small_quasisimple_of_not_rankOne S hp
        (fun hτ => absurd hτ hne) hT hTp h1 i hk hQlt hnrank

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
