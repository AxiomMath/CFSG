module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodA2Char
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OrderSevenPair
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialSet

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement Matrix

set_option linter.unusedSectionVars false


section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem rootSpan_mono_aux {A B : Set (Fin τ.rank → ℤ)} (h : A ⊆ B) :
    rootSpan τ L A ≤ rootSpan τ L B :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le γ (h hγ) le_rfl

theorem rootSpan_le_adjointGroup_aux (T : Set (Fin τ.rank → ℤ)) :
    rootSpan τ L T ≤ adjointGroup τ L := by
  refine iSup₂_le fun γ _ => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  exact pinnedX_mem_adjointGroup _ _

theorem two_lt_ncard_A2roots (hsl : ∀ i, τ.symmetrizer i i = 1) {β β' : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβ' : IsRoot τ β') (hab : iform β β' = -1) :
    2 < (A2roots β β').ncard := by
  have h11 := SimplyLacedCover.iform_self_eq_two hsl hβ
  have h22 := SimplyLacedCover.iform_self_eq_two hsl hβ'
  have hne1 : β ≠ -β := fun h => by
    have := congrArg (iform β) h
    rw [SimplyLacedCover.iform_neg_right, h11] at this
    omega
  have hne2 : β ≠ β' := fun h => by
    rw [← h, h11] at hab
    omega
  have hne3 : -β ≠ β' := fun h => by
    have := congrArg (iform β) h
    rw [SimplyLacedCover.iform_neg_right, h11, hab] at this
    omega
  have hsub : ({β, -β, β'} : Set (Fin τ.rank → ℤ)) ⊆ A2roots β β' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [A2roots]
  have hfin : (A2roots β β').Finite := by
    have : A2roots β β' = ({β, -β, β', -β', β + β', -(β + β')} : Finset _) := by
      ext x; simp [A2roots]
    rw [this]; exact Finset.finite_toSet _
  have h3 : ({β, -β, β'} : Set (Fin τ.rank → ℤ)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨β, -β, β', hne1, hne2, hne3, rfl⟩
  have := Set.ncard_le_ncard hsub hfin
  omega

theorem isGoodRoot_of_A2orbit_two (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hp : p = 7) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ (S.ρ β))
    (hab : iform β (S.ρ β) = -1) (h2 : S.ρ (S.ρ β) = -(β + S.ρ β))
    (h3 : S.ρ (-(β + S.ρ β)) = β) : IsGoodRoot S β := by
  classical
  obtain ⟨β', hβ'def⟩ : ∃ β', β' = S.ρ β := ⟨_, rfl⟩
  rw [← hβ'def] at hβ' hab h2 h3
  have hsl := symmetrizer_diag_one hτ
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have hCharL : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2L)
  set χ := quotChar (A2lattice β β') with hχ
  have hker := kernelRoots_quotChar_A2 hsl hβ hβ' hab
  have hβk : β ∈ kernelRoots χ := by rw [hker]; simp [A2roots]
  set i : KernelComponent χ := ⟦⟨β, hβk⟩⟧ with hi
  have hcomp : componentRoots χ i = A2roots β β' := componentRoots_quotChar_A2 hsl hβ hβ' hab hβk
  have hρβ : S.ρ β = β' := hβ'def.symm
  have hρneg : ∀ x, S.ρ (-x) = -S.ρ x := fun x => S.frob.neg_eq x
  have hρ6 : S.ρ β = β' ∧ S.ρ β' = -(β + β') ∧ S.ρ (-(β + β')) = β ∧ S.ρ (-β) = -β' ∧
      S.ρ (-β') = β + β' ∧ S.ρ (β + β') = -β := by
    refine ⟨hρβ, h2.trans rfl, h3, ?_, ?_, ?_⟩
    · rw [hρneg, hρβ]
    · rw [hρneg, h2, neg_neg]
    · have := hρneg (-(β + β'))
      rw [neg_neg, h3] at this
      exact this
  obtain ⟨hρ1, hρ2, hρ3, hρ4, hρ5, hρ6'⟩ := hρ6
  have hρΨ : ∀ γ ∈ A2roots β β', S.ρ γ ∈ A2roots β β' := by
    intro γ hγ
    simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hρ1]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [hρ4]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [hρ2]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · rw [hρ5]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rw [hρ6']; exact Or.inr (Or.inl rfl)
    · rw [hρ3]; exact Or.inl rfl
  have hkerρ : ∀ (n : ℕ) {γ : Fin τ.rank → ℤ}, γ ∈ kernelRoots χ →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ kernelRoots χ := by
    intro n
    induction n with
    | zero => intro γ hγ; exact hγ
    | succ n ih =>
      intro γ hγ
      rw [Function.iterate_succ_apply']
      have h := ih hγ
      rw [hker] at h ⊢
      exact hρΨ _ h
  obtain ⟨w, hwmem, hw1, hw2, hw3, hw4, hw5, hw6⟩ := A2_rotation hsl hβ hβ' hab
  have hout : ∃ w ∈ Subgroup.closure
        {t : WeylGroup τ | ∃ γ ∈ componentRoots χ i, t = rootReflection γ},
      ∀ γ ∈ componentRoots χ i, (S.ρ : (Fin τ.rank → ℤ) → _)^[1] γ = w • ((1 : WeylGroup τ) • γ) := by
    refine ⟨w, by rw [hcomp]; exact hwmem, fun γ hγ => ?_⟩
    rw [hcomp] at hγ
    simp only [Function.iterate_one, one_smul]
    simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hρ1, hw1]
    · rw [hρ4, hw4]
    · rw [hρ2, hw2]
    · rw [hρ5, hw5]
    · rw [hρ6', hw6]
    · rw [hρ3, hw3]
  obtain ⟨σ, zu, hσ, hnorm, hz⟩ := exists_untwist_outer_chi S hkerρ i (s := 1) one_pos
    (1 : ModGL τ L) (one_mem _) 1 (by
      have : weylQuotientHom τ L ⟨(1 : ModGL τ L), one_mem _⟩ = 1 := map_one _
      exact this)
    (fun γ hγ => by simpa using And.intro hγ hγ) hout
  have hnormΨ : ∀ g : ModGL τ L, g ∈ rootSpan τ L (A2roots β β') ↔
      zu * g * zu⁻¹ ∈ rootSpan τ L (A2roots β β') := fun g => by
    rw [← hcomp]; exact hnorm i g
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, hq, pow_one]
  have h2K : (2 : fixSubfield σ) = 0 := by
    have e : ((2 : fixSubfield σ) : L) = 2 := map_ofNat (fixSubfield σ).subtype 2
    exact Subtype.ext (by rw [e, h2L]; rfl)
  have hCharK : CharP (fixSubfield σ) 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2K)
  have hK : ∀ c : fixSubfield σ, c = 0 ∨ c = 1 := by
    intro c
    have h1 : σ (c : L) = c := c.2
    rw [hσ2] at h1
    have h3 : (c : L) * ((c : L) - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (sub_eq_zero.1 h))
  have hrk : 2 < (componentRoots χ i).ncard := by
    rw [hcomp]; exact two_lt_ncard_A2roots hsl hβ hβ' hab
  have hperf := isPerfect_componentRootSpan_two (K := fixSubfield σ) hτ hK i hrk
  set Cg := componentRootSpan (fixSubfield σ) χ i with hCg
  have hCgspan : Cg = rootSpan τ (fixSubfield σ) (A2roots β β') := by rw [← hcomp]; rfl
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  have hιS : ∀ x ∈ Cg, ι x ∈ rootSpan τ L (A2roots β β') := fun x hx =>
    map_baseChangeGL_rootSpan_le (fixSubfield σ).subtype (A2roots β β')
      ⟨x, by rwa [hCgspan] at hx, rfl⟩
  have hιC : ∀ x ∈ Cg, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hx, rfl⟩
  let f : Cg →* ModGL τ L := (MulAut.conj zu).toMonoidHom.comp (ι.comp Cg.subtype)
  have hf : ∀ x : Cg, f x = zu * ι x.1 * zu⁻¹ := fun x => rfl
  have hfS : ∀ x : Cg, f x ∈ rootSpan τ L (A2roots β β') := fun x => by
    rw [hf]; exact (hnormΨ _).1 (hιS x.1 x.2)
  have hfix : ∀ x : Cg, iterHom S.D.step 1 (f x) = f x := by
    intro x
    rw [hf]
    have hxC : ι x.1 ∈ rootSpan τ L (componentRoots χ i) := by rw [hcomp]; exact hιS x.1 x.2
    rw [hz _ hxC, frobGL_eq_self_of_mem_CQ' σ i (hιC x.1 x.2)]
    simp
  have hM : ∀ x : Cg, f x ∈ S.D.model := fun x =>
    ⟨rootSpan_le_adjointGroup_aux _ (hfS x), hfix x⟩
  have hΓ : ∀ x : Cg, f x ∈ S.Γ := map_mem_commutator_of_perfect hperf f _ hM
  have hΨroot : ∀ γ ∈ A2roots β β', IsRoot τ γ := fun γ hγ => isRoot_A2roots hsl hβ hβ' hab hγ
  have hmemK : ∀ γ ∈ A2roots β β', pinnedX τ (fixSubfield σ) γ 1 ∈ Cg := fun γ hγ => by
    rw [hCgspan]; exact pinnedX_mem_rootSpan hγ 1
  have hfroot : ∀ γ (hγ : γ ∈ A2roots β β'), f ⟨_, hmemK γ hγ⟩ = zu * pinnedX τ L γ 1 * zu⁻¹ := by
    intro γ hγ
    rw [hf]
    show zu * baseChangeGL (fixSubfield σ).subtype (pinnedX τ (fixSubfield σ) γ 1) * zu⁻¹ = _
    rw [baseChangeGL_pinnedX, map_one]
  have hmem4 : pinnedX τ (fixSubfield σ) β' 1 * pinnedX τ (fixSubfield σ) (-β') 1 *
      pinnedX τ (fixSubfield σ) (-β) 1 * pinnedX τ (fixSubfield σ) β 1 ∈ Cg := by
    have a1 : β ∈ A2roots β β' := by simp [A2roots]
    have a2 : -β ∈ A2roots β β' := by simp [A2roots]
    have a3 : β' ∈ A2roots β β' := by simp [A2roots]
    have a4 : -β' ∈ A2roots β β' := by simp [A2roots]
    exact mul_mem (mul_mem (mul_mem (hmemK _ a3) (hmemK _ a4)) (hmemK _ a2)) (hmemK _ a1)
  have hord : orderOf (f ⟨_, hmem4⟩) = p := by
    have hf4 : f ⟨_, hmem4⟩ = zu * (pinnedX τ L β' 1 * pinnedX τ L (-β') 1 * pinnedX τ L (-β) 1 *
        pinnedX τ L β 1) * zu⁻¹ := by
      rw [hf]
      show zu * baseChangeGL (fixSubfield σ).subtype _ * zu⁻¹ = _
      simp only [map_mul, baseChangeGL_pinnedX, map_one]
    rw [hf4, hp]
    have := orderOf_pairWord_two (L := L) hτ hβ hβ' hab
    rw [← this]
    exact (MulAut.conj zu).orderOf_eq _
  have hcomm : ∀ z' : ModGL τ L, (∀ y ∈ f.range, Commute z' y) →
      ∀ x ∈ rootRankOneGroup τ L β, Commute z' x := by
    intro z' hc x hx
    have hneg : ∀ γ ∈ A2roots β β', -γ ∈ A2roots β β' := by
      intro γ hγ
      simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
      rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (neg_neg _)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl (neg_neg _)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (neg_neg _)))))
    have hadj : ∀ α ∈ A2roots β β', ∃ δ ∈ A2roots β β', iform α δ = 1 := by
      intro α hα
      rw [← hcomp] at hα
      obtain ⟨δ, hδ, h⟩ := exists_adjacent_root hτ i hrk hα
      exact ⟨δ, by rwa [hcomp] at hδ, h⟩
    have hzg : ∀ γ ∈ A2roots β β',
        z' * (zu * pinnedX τ L γ 1 * zu⁻¹) = (zu * pinnedX τ L γ 1 * zu⁻¹) * z' := fun γ hγ => by
      have := (hc (f ⟨_, hmemK γ hγ⟩) ⟨_, rfl⟩).eq
      rwa [hfroot γ hγ] at this
    have hall := commute_rootSpan_of_conj_gens_two hτ hΨroot hneg hadj hnormΨ hzg
    refine hall x ?_
    rw [rootRankOneGroup_eq_rootSpan_pair hβ] at hx
    refine rootSpan_mono_aux ?_ hx
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl <;> simp [A2roots]
  have hfield : ∀ (r f' j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f' → 0 < j → j < f' →
      ∀ z' : ModGL τ L, ¬ ∀ y ∈ f.range,
        z' * Units.map (entrywiseHom (iterateFrobenius L r j)) y * z'⁻¹ = y := by
    intro r f' j _ hr hq' hj0 hjf
    exfalso
    have hr2 := hr.two_le
    have hf2 : f' < 2 := by
      by_contra hcon
      have h1 : r ^ 2 ≤ r ^ f' := Nat.pow_le_pow_right hr.pos (not_lt.1 hcon)
      nlinarith
    omega
  have hrho : A2roots β β' ⊆ rhoOrbitPM S.ρ β := by
    intro γ hγ
    simp only [A2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨1, Or.inl hρβ.symm⟩
    · exact ⟨1, Or.inr (by
        change -β' = S.ρ (-β)
        rw [hρ4])⟩
    · exact ⟨2, Or.inr (by
        show β + β' = S.ρ (S.ρ (-β))
        rw [hρ4, hρneg, hρ2, neg_neg])⟩
    · exact ⟨2, Or.inl (by
        show -(β + β') = S.ρ (S.ρ β)
        rw [hρ1, hρ2])⟩
  refine ⟨hβ, f.range, ?_, commutator_range_eq_of_perfect hperf f, ?_, ⟨_, ⟨_, rfl⟩, hord⟩,
    hcomm, hfield⟩
  · rintro _ ⟨x, rfl⟩
    exact hΓ x
  · rintro _ ⟨x, rfl⟩
    exact rootSpan_mono_aux hrho (hfS x)

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus
