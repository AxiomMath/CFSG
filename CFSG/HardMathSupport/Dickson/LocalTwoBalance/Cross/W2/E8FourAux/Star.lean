module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.StarRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyQuad
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.AnyKindThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAnyKind
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Big

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
  (hτ : SimplyLacedTag τ) (hw4 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → w • w • δ = -δ)

include hFr hΦ hn hτ hw4

theorem bigComponent_of_star (hp2 : p ≠ 2) (hMΓ : S.D.model ≤ S.Γ) {a a' : Fin τ.rank → Lˣ}
    (ha'E : rootDiagUnit τ a' ∈ S.E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hχa : rootChar a γ = 1) (hχa' : rootChar a' γ ≠ 1) (i : KernelComponent (rootCharHom a))
    (hγi : γ ∈ componentRoots (rootCharHom a) i) :
    ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  have hp := S.hp
  have hE' : rootDiagUnit τ a' ∈ S.E := ha'E
  have htor : rootDiagUnit τ a' ∈ S.D.torus := (Subgroup.mem_inf.1 (S.E_le hE')).1
  have hpow : (rootDiagUnit τ a') ^ p = 1 := S.E_exp _ hE'
  have hpow' : a' ^ p = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ) (K := L)
    rw [← rootDiagUnit_pow, hpow, rootDiagUnit_one]
  set q := S.D.q with hq
  set ω : Lˣ := rootChar a' γ with hω
  have hωp : ω ^ p = 1 := by
    rw [hω, ← rootChar_pow, hpow', rootChar_one']
  have hχ : ∀ δ, IsRoot τ δ → rootChar a' (w • δ) = rootChar a' δ ^ q := fun δ hδ => by
    rw [← S.rho_eq_smul_of_frob hFr hΦ hn hδ]
    exact S.frob.rootChar_eq a' htor δ hδ
  have hr1 : IsRoot τ (w • γ) := (isRoot_smul_iff w).2 hγ
  have h1 : rootChar a' (w • γ) = ω ^ q := hχ γ hγ
  have h2 : rootChar a' (w • w • γ) = ω ^ q ^ 2 := by
    rw [hχ _ hr1, h1, ← pow_mul, sq]
  have h2' : rootChar a' (w • w • γ) = ω⁻¹ := by
    rw [hw4 γ hγ, rootChar_neg_tri]
  have hω1 : ω ≠ 1 := hχa'
  have hωq : ω ^ (q ^ 2 + 1) = 1 := by
    rw [pow_succ, ← h2, h2', inv_mul_cancel]
  have hk : ¬ (p : ℤ) ∣ ((p - 1 : ℕ) : ℤ) - 1 := by
    intro h
    have e1 : ((p - 1 : ℕ) : ℤ) - 1 = p - 2 := by
      push_cast [Nat.cast_sub hp.one_lt.le]
      ring
    rw [e1] at h
    have h2 : (p : ℤ) ∣ 2 := by
      have := dvd_sub (dvd_refl (p : ℤ)) h
      simpa using this
    have : p ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  obtain ⟨ν, hνm, hνF, hνc⟩ := S.quad_nu hFr hΦ hn hτ hw4 hγ
  have hΘ := quadOrbit_subset_rationalRoots S hFr hΦ hn i hγi hγ
  have hy : rootDiagUnit τ (quadY w q γ ω) ∈ rootSpan τ L (quadOrbit w γ) := by
    unfold quadY
    rw [rootDiagUnit_mul]
    refine mul_mem ?_ ?_
    · have h := Hel_mem_rootSpan_quadOrbit (L := L) hτ hw4 hγ 0 ω
      rw [pow_zero, one_smul] at h
      exact h
    · have h := Hel_mem_rootSpan_quadOrbit (L := L) hτ hw4 hγ 1 (ω ^ q)
      rw [pow_one] at h
      exact h
  exact not_coprime_of_commutator_pair S hMΓ i hΘ hy (S.step_quadY hFr hΦ hn hw4 hγ ω hωq)
    (quadY_pow q p γ ω hωp) (quadY_ne_one hτ hw4 q p hp hp2 hγ ω hωp hω1) hνm hνF
    (quadY_conj hτ hw4 q p hp.one_lt.le hγ ω hωp hνc) hk

end Big

section Main

variable {L : Type} [Field L] [IsAlgClosed L]

open CFSG.RankThree.Lattice in
theorem finite_setOf_isRoot (τ : Tag) : {γ : Fin τ.rank → ℤ | IsRoot τ γ}.Finite := by
  refine ((τ.artifactRoots.map (toVec τ.rank)).finite_toSet).subset fun γ hγ => ?_
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hγ
  exact List.mem_map.2 ⟨l, hl, rfl⟩

theorem two_lt_ncard_componentRoots {τ : Tag} {a : Fin τ.rank → Lˣ}
    (hadj : ∀ γ, IsRoot τ γ → rootChar a γ = 1 → ∃ γ', IsRoot τ γ' ∧ rootChar a γ' = 1 ∧
      γ' ≠ γ ∧ γ' ≠ -γ ∧ CFSG.LieType.Steinberg.Adjoint.iform γ γ' ≠ 0)
    (i : KernelComponent (rootCharHom a)) : 2 < (componentRoots (rootCharHom a) i).ncard := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  have hx := x.2
  obtain ⟨γ', hγ'r, hγ'χ, hne1, hne2, hform⟩ := hadj x.1 hx.1 hx.2
  have hmem' : γ' ∈ kernelRoots (rootCharHom a) := ⟨hγ'r, hγ'χ⟩
  have hnegmem : -x.1 ∈ kernelRoots (rootCharHom a) :=
    ⟨IsRoot.neg hx.1, chi_neg hx.2⟩
  have hfin : (componentRoots (rootCharHom a) (⟦x⟧ : KernelComponent (rootCharHom a))).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [Set.two_lt_ncard_iff hfin]
  have hpos := iform_self_pos_of_isRoot hx.1
  have hform1 : CFSG.LieType.Steinberg.Adjoint.iform (-x.1) x.1 ≠ 0 := by
    rw [← neg_one_smul ℤ x.1, CFSG.LieType.Steinberg.Adjoint.iform_smul_left]
    omega
  refine ⟨x.1, -x.1, γ', ⟨x.2, rfl⟩, ⟨hnegmem, ?_⟩, ⟨hmem', ?_⟩, ?_, hne1.symm, ?_⟩
  · exact mk_eq_of_iform_ne_zero (α := ⟨-x.1, hnegmem⟩) (β := x) hform1
  · refine mk_eq_of_iform_ne_zero (α := ⟨γ', hmem'⟩) (β := x) ?_
    rw [CFSG.LieType.Steinberg.Adjoint.iform_comm]
    exact hform
  · intro h
    have h3 : CFSG.LieType.Steinberg.Adjoint.iform x.1 x.1 =
        CFSG.LieType.Steinberg.Adjoint.iform (-x.1) x.1 := by rw [← h]
    rw [← neg_one_smul ℤ x.1, CFSG.LieType.Steinberg.Adjoint.iform_smul_left] at h3
    omega
  · exact fun h => hne2 h.symm

@[expose] def CommuteAt {τ : Tag} {p : ℕ} (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ) : Prop :=
  ∀ i : KernelComponent (rootCharHom a), ∀ z : ModGL τ L,
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g

theorem commuteAt_of_four_le {τ : Tag} {p : ℕ} (S : LangSetup τ L p) (hAK : AnyKindCommute)
    (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E) :
    CommuteAt S a := by
  intro i z hz
  have hpos := (componentOrbitLength_spec S hE i).1
  exact hAK τ L p S hτ a hE i (by omega)
    (hq4.trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hpos) _)) z hz

theorem commuteAt_three {τ : Tag} {p : ℕ} (S : LangSetup τ L p) (hAK3 : AnyKindCommuteThreeFull)
    (hτ : SimplyLacedTag τ) (hq : S.D.q = 3) {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E)
    (hbig3 : ∀ i : KernelComponent (rootCharHom a), 2 < (componentRoots (rootCharHom a) i).ncard) :
    CommuteAt S a :=
  fun i z hz => hAK3 τ L p S hτ hq a (Subgroup.mem_inf.1 (S.E_le hE)).1 i (fun _ => hbig3 i) z hz

theorem noFrobeniusInnerOn_star {τ : Tag} {p : ℕ} (S : LangSetup τ L p) (hτ : τ ≠ .G2)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ) {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E)
    (i : KernelComponent (rootCharHom a))
    (hbig : ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    NoFrobeniusInnerOn S (starSet S a) := by
  intro r f j _ hr hqf hj0 hjf z hz
  exact outer_false_of_component_fixed_by_twist_of_E S hτ hE i hr hqf hq4 hj0 hjf z
    (fun x hx => hz x ⟨i, hbig, hx⟩)

theorem commute_kernel_of_commute_starSet {τ : Tag} {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hCom : CommuteAt S a)
    (hbig : ∀ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)))
    {z : ModGL τ L} (hz : ∀ x ∈ starSet S a, Commute z x) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hχ : rootChar a γ = 1) (c : L) :
    z * pinnedX τ L γ c = pinnedX τ L γ c * z := by
  have hmem : γ ∈ kernelRoots (rootCharHom a) := ⟨hγ, hχ⟩
  have hγi : γ ∈ componentRoots (rootCharHom a) (⟦⟨γ, hmem⟩⟧ : KernelComponent (rootCharHom a)) :=
    ⟨hmem, rfl⟩
  have := hCom (⟦⟨γ, hmem⟩⟧ : KernelComponent (rootCharHom a)) z
    (fun x hx => hz x ⟨_, hbig _, hx⟩) (pinnedX τ L γ c) (pinnedX_mem_rootSpan hγi c)
  exact this.eq

theorem localDeltaIn_zpowers_eq_bot_of_star
    (S : LangSetup .E8 L 5)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem .E8) L e8PhiFourWeyl)
    (hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot .E8 δ → e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ)
    (hMΓ : S.D.model ≤ S.Γ) (hAlg : S.IsAlgebraic) (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ))
    {a a' : Fin Tag.E8.rank → Lˣ} (huE : rootDiagUnit .E8 a ∈ S.E)
    (hu1 : rootDiagUnit .E8 a ≠ 1) (ha'E : rootDiagUnit .E8 a' ∈ S.E)
    (hreg : ∀ γ, IsRoot .E8 γ → rootChar a γ = 1 → rootChar a' γ ≠ 1)
    (hne : ∃ γ, IsRoot .E8 γ ∧ rootChar a γ = 1) (hCom : CommuteAt S a)
    (hLL : ∀ z ∈ adjointGroup .E8 L, (∀ γ, IsRoot .E8 γ → rootChar a γ = 1 → ∀ c : L,
      z * pinnedX .E8 L γ c = pinnedX .E8 L γ c * z) → z ^ 5 = 1)
    {H : Subgroup (MulAut ↥S.Γ)} (hH : innerAut ↥S.Γ ≤ H) :
    localDeltaIn 5 H ((Subgroup.zpowers (⟨rootDiagUnit .E8 a, (S.E_le huE).2⟩ : ↥S.Γ)).map
      (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) = ⊥ := by
  classical
  have hp := S.hp
  have := S.finite_Γ
  have hbig : ∀ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime 5 (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    intro i
    obtain ⟨x, rfl⟩ := Quotient.exists_rep i
    have hx := x.2
    exact bigComponent_of_star S hFr hΦ hn (Or.inr (Or.inr (Or.inr rfl)))
      hw4 (by norm_num) hMΓ ha'E hx.1 hx.2
      (hreg _ hx.1 hx.2) _ ⟨hx, rfl⟩
  obtain ⟨γ0, hγ0, hχ0⟩ := hne
  have hmem0 : γ0 ∈ kernelRoots (rootCharHom a) := ⟨hγ0, hχ0⟩
  have hF : NoFrobeniusInnerOn S (starSet S a) :=
    noFrobeniusInnerOn_star S (by decide) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) huE
      (⟦⟨γ0, hmem0⟩⟧ : KernelComponent (rootCharHom a)) (hbig _)
  have hI : ∀ z ∈ adjointGroup .E8 L, (∀ x ∈ starSet S a, Commute z x) → z ^ 5 = 1 :=
    fun z hz hx => hLL z hz fun γ hγ hχ c => commute_kernel_of_commute_starSet S hCom hbig hx hγ hχ c
  set u : ↥S.Γ := ⟨rootDiagUnit .E8 a, (S.E_le huE).2⟩ with hu
  have hD₀ : Subgroup.zpowers u ≠ ⊥ := by
    intro h
    apply hu1
    have h1 : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rw [h, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  refine localDeltaIn_eq_bot_of_inner_components_rigid_ambient (A := S.Γ) (S := starSet S a)
    hp hinj hH hD₀ ?_ ?_
  · intro δ _ hδ _ hfixX
    exact rigidOn_E8 S (by norm_num) hAlg (starSet S a) (starSet_subset_Γ S a) hF hI δ hδ hfixX
  · intro x hx
    obtain ⟨i, hbigi, hxi⟩ := hx
    obtain ⟨hLC, hLsn⟩ := hsub .E8 L 5 S a huE hu1 i
    refine ⟨u, Subgroup.mem_zpowers u, fun h1 => hu1 (congrArg Subtype.val h1),
      rationalComponent S.ρ S.Γ (rootCharHom a) i, hxi, hLC, ?_, hLsn, hbigi⟩
    cases hkind : twistKind S.ρ (rootCharHom a) i
    · exact hin .E8 L 5 S a huE hu1 i hkind hbigi
    · exact hsu .E8 L 5 S a huE hu1 i hkind hbigi
    · exact htw .E8 L 5 S a huE hu1 i hkind hbigi
    · exact hex .E8 L 5 S a huE hu1 i hkind hbigi

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
