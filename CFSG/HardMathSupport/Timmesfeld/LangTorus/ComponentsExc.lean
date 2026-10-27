module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (D4TrialityLayer d4Nodes)
open scoped Matrix

section Setup

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p : ℕ}

omit [IsAlgClosed L] in
theorem pow_eq_one_of_rootDiagUnit_pow {a : Fin τ.rank → Lˣ}
    (hTp : rootDiagUnit τ a ^ p = 1) : ∀ i, a i ^ p = 1 := by
  have h1 : rootDiagUnit τ (a ^ p) = 1 := by
    have e : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
      map_pow (rootDiagUnitHom τ L) a p
    rw [e]
    exact hTp
  have h2 : a ^ p = 1 :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  exact fun i => congrFun h2 i

theorem LangSetup.natCast_ne_zero (S : LangSetup τ L p) : (p : L) ≠ 0 := by
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  intro h
  have hℓp : ℓ ∣ p := (CharP.cast_eq_zero_iff L ℓ p).1 h
  have hℓp' : ℓ = p := ((Nat.prime_dvd_prime_iff_eq hℓ S.hp).1 hℓp)
  apply S.hpq
  rw [hq, ← hℓp']
  exact dvd_pow_self ℓ (by omega)

theorem exists_kacT_of_pos {N : ℕ} (hN : 0 < N) (hNL : (N : L) ≠ 0) {K : KacData τ}
    (hK : K.Facts) {a : Fin τ.rank → Lˣ} (hTN : rootDiagUnit τ a ^ N = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ), K.IsNormal N μ ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ x, K.IsZ N μ x ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (K.comp N μ x) := by
  have : NeZero (N : L) := ⟨hNL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  have hu : IsUnit ζ := hζ.isUnit hN.ne'
  exact K.exists_smul_rootsOf hK hN (ζ := hu.unit) (by simpa using hζ) a
    (pow_eq_one_of_rootDiagUnit_pow hTN)

theorem LangSetup.exists_kacT_of_prime {p₀ : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ), K.IsNormal p μ ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ x, K.IsZ p μ x ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (K.comp p μ x) :=
  exists_kacT_of_pos hp.pos hpL hK hTp

omit [IsAlgClosed L] in
theorem exists_not_mem_comp (K : KacData τ) {N : ℕ} (hN : 0 < N) (μ : Fin τ.rank → ℤ)
    (x : Option (Fin τ.rank)) : ∃ y, y ∉ K.comp N μ x := by
  by_contra h
  push Not at h
  have hz : ∀ y, K.IsZ N μ y := fun y => (h y).1
  have hμ : μ = 0 := funext fun j => hz (some j)
  have h0 : K.θ ⬝ᵥ μ = N := hz none
  rw [hμ, dotProduct_zero] at h0
  omega

end Setup

section Pinned

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p : ℕ}

theorem exists_pinnedT_of_pos {N : ℕ} (hN : 0 < N) (hNL : (N : L) ≠ 0) {K : KacData τ}
    (hK : K.Facts) {a : Fin τ.rank → Lˣ} (hTN : rootDiagUnit τ a ^ N = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ),
      (∀ j : KernelComponent (rootCharHom a), ∃ y, K.IsZ N μ y ∧
        componentRoots (rootCharHom a) j = (fun α => v • α) '' K.rootsOf (K.comp N μ y)) ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ (x : Option (Fin τ.rank))
        (C : Finset (Option (Fin τ.rank))), K.comp N μ x = C ∧ (∃ y, y ∉ C) ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf C ∧
        compRank (componentRoots (rootCharHom a) i) = C.card ∧
        (componentRoots (rootCharHom a) i).ncard = kacCount τ K.θ C := by
  obtain ⟨v, μ, -, hall⟩ := exists_kacT_of_pos hN hNL hK hTN
  refine ⟨v, μ, hall, fun i => ?_⟩
  obtain ⟨x, -, hi⟩ := hall i
  set hfin := Set.toFinite (K.comp N μ x)
  have hC : K.comp N μ x = (hfin.toFinset : Set (Option (Fin τ.rank))) :=
    hfin.coe_toFinset.symm
  have hCp : ∃ y, y ∉ hfin.toFinset := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp K hN μ x
    exact ⟨y, fun h => hy (hfin.mem_toFinset.1 h)⟩
  rw [hC] at hi
  refine ⟨x, hfin.toFinset, hC, hCp, hi, ?_, ?_⟩
  · rw [hi, compRank_image, compRank_rootsOf K hK hCp]
  · rw [hi, ncard_image_smul, ncard_rootsOf K hK hCp]

theorem LangSetup.exists_pinnedT_of_prime {p₀ : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ),
      (∀ j : KernelComponent (rootCharHom a), ∃ y, K.IsZ p μ y ∧
        componentRoots (rootCharHom a) j = (fun α => v • α) '' K.rootsOf (K.comp p μ y)) ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ (x : Option (Fin τ.rank))
        (C : Finset (Option (Fin τ.rank))), K.comp p μ x = C ∧ (∃ y, y ∉ C) ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf C ∧
        compRank (componentRoots (rootCharHom a) i) = C.card ∧
        (componentRoots (rootCharHom a) i).ncard = kacCount τ K.θ C :=
  exists_pinnedT_of_pos hp.pos hpL hK hTp

theorem ncard_setOf_isRoot (τ : Tag) : {v : Fin τ.rank → ℤ | IsRoot τ v}.ncard = τ.rootCount := by
  have h := ncard_isRoot_and (τ := τ) (fun _ => True)
  simp only [and_true, decide_true, List.filter_true] at h
  rw [h, τ.length_artifactRoots]

omit [IsAlgClosed L] in
theorem rootDiagUnit_eq_one_of_ncard {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (h : τ.rootCount ≤ (componentRoots (rootCharHom a) i).ncard) : rootDiagUnit τ a = 1 := by
  have hsub : componentRoots (rootCharHom a) i ⊆ {v | IsRoot τ v} := fun γ hγ => hγ.1.1
  have heq : componentRoots (rootCharHom a) i = {v | IsRoot τ v} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_setOf_isRoot]; exact h)
      (finite_setOf_isRoot τ)
  have ha : a = 1 := by
    funext j
    have hj : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      rw [heq]
      exact isRoot_single τ j
    have h1 : rootChar a (Pi.single j 1) = 1 := hj.1.2
    have h2 := rootChar_nsmul_single a j 1
    rw [one_smul, pow_one] at h2
    rw [h2] at h1
    exact h1
  rw [ha]
  exact rootDiagUnit_one

theorem LangSetup.exists_image_subsetT (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    ∃ j : KernelComponent (rootCharHom a), ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) j := by
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) := by
    rintro γ ⟨hγ, hγ1⟩
    refine ⟨(S.frob.isRoot_iff γ).2 hγ, ?_⟩
    change rootChar a (S.ρ γ) = 1
    change rootChar a γ = 1 at hγ1
    rw [S.frob.rootChar_eq a haT γ hγ, hγ1, one_pow]
  let σ : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a) :=
    fun x => ⟨S.ρ x, hker x x.2⟩
  have hrel : ∀ x y : kernelRoots (rootCharHom a),
      (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 →
        (σ x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (σ y : Fin τ.rank → ℤ)) ≠ 0 := by
    intro x y h
    change S.ρ x ⬝ᵥ (τ.symmetrizedCartan *ᵥ S.ρ y) ≠ 0
    rwa [dotProduct_mulVec_eq_iform, S.frob.iform_eq, ← dotProduct_mulVec_eq_iform]
  have key : ∀ {x y : kernelRoots (rootCharHom a)}, Relation.EqvGen (fun α β :
      kernelRoots (rootCharHom a) =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
      Relation.EqvGen (fun α β : kernelRoots (rootCharHom a) =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) (σ x) (σ y) := by
    intro x y h
    induction h with
    | rel x y h => exact Relation.EqvGen.rel _ _ (hrel x y h)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  obtain ⟨γ₀, rfl⟩ := Quotient.exists_rep i
  refine ⟨⟦σ γ₀⟧, fun γ ⟨hγ, hγi⟩ => ⟨hker γ hγ, ?_⟩⟩
  exact Quotient.sound (key (Quotient.exact hγi))

theorem LangSetup.rho_mem_of_farT_of_prime {p₀ : ℕ} (S : LangSetup τ L p₀) {K : KacData τ}
    (hK : K.Facts)
    {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus) {v : WeylGroup τ}
    {μ : Fin τ.rank → ℤ}
    (hall : ∀ j : KernelComponent (rootCharHom a), ∃ y, K.IsZ p μ y ∧
      componentRoots (rootCharHom a) j = (fun α => v • α) '' K.rootsOf (K.comp p μ y))
    (i : KernelComponent (rootCharHom a)) {x : Option (Fin τ.rank)}
    {C : Finset (Option (Fin τ.rank))} (hC : K.comp p μ x = C)
    (hi : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf C)
    {F : Finset (Option (Fin τ.rank))} (hF : ∀ y, (∀ z ∈ C, y ≠ z ∧ ¬ K.Adj y z) → y ∈ F)
    (hFp : ∃ y, y ∉ F) (hlt : kacCount τ K.θ F < (componentRoots (rootCharHom a) i).ncard) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨j, hj⟩ := S.exists_image_subsetT haT i
  obtain ⟨y, hy, hjy⟩ := hall j
  by_cases hyx : y ∈ K.comp p μ x
  · have hcomp : K.comp p μ y = K.comp p μ x := K.comp_eq_of_mem hyx
    intro γ hγ
    have h1 := hj γ hγ
    rwa [hjy, hcomp, hC, ← hi] at h1
  · exfalso
    have hsep := K.comp_separated hy hyx
    have hsub : K.comp p μ y ⊆ (F : Set (Option (Fin τ.rank))) := by
      intro b hb
      refine hF b fun z hz => ?_
      have hz' : z ∈ K.comp p μ x := by
        rw [hC]
        exact hz
      obtain ⟨h1, h2⟩ := hsep z hz' b hb
      refine ⟨fun e => h1 e.symm, fun hadj => h2 ⟨h1, ?_⟩⟩
      rw [iform_comm]
      exact hadj.2
    have hfinF : (K.rootsOf (F : Set (Option (Fin τ.rank)))).Finite :=
      (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1
    have hfinj : (componentRoots (rootCharHom a) j).Finite :=
      (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
    have h1 : (componentRoots (rootCharHom a) j).ncard ≤ kacCount τ K.θ F := by
      rw [hjy, ncard_image_smul, ← ncard_rootsOf K hK hFp]
      exact Set.ncard_le_ncard (rootsOf_mono K hsub) hfinF
    have h2 : (componentRoots (rootCharHom a) i).ncard ≤
        (componentRoots (rootCharHom a) j).ncard := by
      rw [← Set.ncard_image_of_injective _ S.ρ.injective]
      exact Set.ncard_le_ncard (fun _ ⟨γ, hγ, e⟩ => e ▸ hj γ hγ) hfinj
    omega

end Pinned

section Far

@[expose] def extRootOf {r : ℕ} (θ : Fin r → ℤ) : Option (Fin r) → Fin r → ℤ
  | none => -θ
  | some j => Pi.single j 1

theorem extRoot_eq_extRootOf {τ : Tag} (K : KacData τ) :
    K.extRoot = extRootOf K.θ := by
  funext x
  cases x <;> rfl

theorem far_d4_E8 : ∀ y : Option (Fin Tag.E8.rank),
    (∀ z ∈ ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E8.rank))),
      y ≠ z ∧ ¬ (y ≠ z ∧ iform (τ := .E8) (extRootOf ![2, 3, 4, 6, 5, 4, 3, 2] y)
        (extRootOf ![2, 3, 4, 6, 5, 4, 3, 2] z) ≠ 0)) →
      y ∈ ({none, some 6, some 7} : Finset (Option (Fin Tag.E8.rank))) := by
  decide +kernel

theorem far_d4_E7 : ∀ y : Option (Fin Tag.E7.rank),
    (∀ z ∈ ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E7.rank))),
      y ≠ z ∧ ¬ (y ≠ z ∧ iform (τ := .E7) (extRootOf ![2, 2, 3, 4, 3, 2, 1] y)
        (extRootOf ![2, 2, 3, 4, 3, 2, 1] z) ≠ 0)) →
      y ∈ ({none, some 6} : Finset (Option (Fin Tag.E7.rank))) := by
  decide +kernel

theorem far_d4_E6 : ∀ y : Option (Fin Tag.E6.rank),
    (∀ z ∈ ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E6.rank))),
      y ≠ z ∧ ¬ (y ≠ z ∧ iform (τ := .E6) (extRootOf ![1, 2, 2, 3, 2, 1] y)
        (extRootOf ![1, 2, 2, 3, 2, 1] z) ≠ 0)) →
      y ∈ (∅ : Finset (Option (Fin Tag.E6.rank))) := by
  decide +kernel

theorem kacCount_far_E8 : kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] {none, some 6, some 7} = 12 := by
  decide +kernel

theorem kacCount_far_E7 : kacCount .E7 ![2, 2, 3, 4, 3, 2, 1] {none, some 6} = 4 := by
  decide +kernel

theorem kacCount_far_E6 : kacCount .E6 ![1, 2, 2, 3, 2, 1] ∅ = 0 := by
  decide +kernel

end Far

section Kind

variable {τ : Tag} {L : Type}
  [Field L]

theorem exc_kind {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    {i : KernelComponent χ} (hk : twistKind ρ χ i = .exc) :
    ¬ twistInner (componentRoots χ i)
        ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) ∧
      ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
        (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
          ¬ twistInner (componentRoots χ i)
            ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]))) := by
  unfold twistKind at hk
  split_ifs at hk with h1 h2
  exact ⟨h1, h2⟩

theorem compRank_le_rank (Ψ : Set (Fin τ.rank → ℤ)) : compRank Ψ ≤ τ.rank := by
  unfold compRank
  calc _ ≤ Module.finrank ℚ (Fin τ.rank → ℚ) := Submodule.finrank_le _
    _ = τ.rank := Module.finrank_fin_fun ℚ

end Kind

section Standard

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p : ℕ}

theorem LangSetup.e6_pinnedT_of_pos {p₀ N : ℕ} (S : LangSetup τ L p₀) (hN : 0 < N)
    (hNL : (N : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {E6C : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 6 → kacCount τ K.θ C = 72 → C = E6C)
    (hJ : ∀ j : Fin τ.rank, some j ∈ E6C ↔ j.val ≤ 5) (hnone : none ∉ E6C)
    {a : Fin τ.rank → Lˣ} (hTN : rootDiagUnit τ a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 6)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
  obtain ⟨v, μ, -, hpinned⟩ := exists_pinnedT_of_pos hN hNL hK hTN
  obtain ⟨x, C, -, -, hi, hr, hc⟩ := hpinned i
  have hC : C = E6C := hpin C (hr ▸ hrank) (hc ▸ hcard)
  subst hC
  refine ⟨v, ?_⟩
  rw [hi, K.rootsOf_eq_parabolicRoots (by exact_mod_cast hnone)]
  congr 2
  exact Set.ext fun j => hJ j

theorem LangSetup.e6_pinnedT_of_prime {p₀ : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {E6C : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 6 → kacCount τ K.θ C = 72 → C = E6C)
    (hJ : ∀ j : Fin τ.rank, some j ∈ E6C ↔ j.val ≤ 5) (hnone : none ∉ E6C)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 6)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) :=
  S.e6_pinnedT_of_pos hp.pos hpL hK hpin hJ hnone hTp i hrank hcard

theorem LangSetup.d4_pinnedT_of_pos {p₀ N : ℕ} (S : LangSetup τ L p₀) (hN : 0 < N)
    (hNL : (N : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {D4C F : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 4 → kacCount τ K.θ C = 24 → C = D4C)
    (hJ : ∀ j : Fin τ.rank, some j ∈ D4C ↔ 1 ≤ j.val ∧ j.val ≤ 4) (hnone : none ∉ D4C)
    (hF : ∀ y, (∀ z ∈ D4C, y ≠ z ∧ ¬ K.Adj y z) → y ∈ F) (hFp : ∃ y, y ∉ F)
    (hFc : kacCount τ K.θ F < 24)
    {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus) (hTN : rootDiagUnit τ a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨v, μ, hall, hpinned⟩ := exists_pinnedT_of_pos hN hNL hK hTN
  obtain ⟨x, C, hxC, -, hi, hr, hc⟩ := hpinned i
  have hC : C = D4C := hpin C (hr ▸ hrank) (hc ▸ hcard)
  subst hC
  refine ⟨v, ?_, S.rho_mem_of_farT_of_prime hK haT hall i hxC hi hF hFp (by omega)⟩
  rw [hi, K.rootsOf_eq_parabolicRoots (by exact_mod_cast hnone)]
  congr 2
  exact Set.ext fun j => hJ j

theorem LangSetup.d4_pinnedT_of_prime {p₀ : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {D4C F : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 4 → kacCount τ K.θ C = 24 → C = D4C)
    (hJ : ∀ j : Fin τ.rank, some j ∈ D4C ↔ 1 ≤ j.val ∧ j.val ≤ 4) (hnone : none ∉ D4C)
    (hF : ∀ y, (∀ z ∈ D4C, y ≠ z ∧ ¬ K.Adj y z) → y ∈ F) (hFp : ∃ y, y ∉ F)
    (hFc : kacCount τ K.θ F < 24)
    {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
  S.d4_pinnedT_of_pos hp.pos hpL hK hpin hJ hnone hF hFp hFc haT hTp i hrank hcard

end Standard

section Statements

@[expose] def ExcQuasisimpleAt (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.E → rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .exc →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def TwistedE6TrialityComponents : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup .E6 L p),
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a ∈ S.E → rootDiagUnit .E6 a ≠ 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
      ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcQuasisimpleAtT (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ p = 1 →
    rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .exc →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def TwistedE6TrialityComponentsT : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup .E6 L p),
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a ∈ S.D.torus → rootDiagUnit .E6 a ^ p = 1 →
    rootDiagUnit .E6 a ≠ 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
      ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem twistedE6TrialityComponents_of_T (h : TwistedE6TrialityComponentsT) :
    TwistedE6TrialityComponents :=
  fun L _ _ p S hS a ha ha1 i v hΨ hρ h1 h2 =>
    h L p S hS a (S.E_le ha).1 (S.E_exp _ ha) ha1 i v hΨ hρ h1 h2

@[expose] def ExcQuasisimpleAtT_ofPrime (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ p : ℕ) (S : LangSetup τ L p₀), p.Prime →
    (p : L) ≠ 0 → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
    rootDiagUnit τ a ^ p = 1 → rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .exc →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem ExcQuasisimpleAtT_ofPrime.toT {τ : Tag} (h : ExcQuasisimpleAtT_ofPrime τ) :
    ExcQuasisimpleAtT τ :=
  fun L _ _ p S a haT hTp ha1 i hk => h L p p S S.hp S.natCast_ne_zero a haT hTp ha1 i hk

@[expose] def TwistedE6TrialityComponentsT_ofPrime : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ p : ℕ) (S : LangSetup .E6 L p₀), p.Prime →
    (p : L) ≠ 0 →
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a ∈ S.D.torus → rootDiagUnit .E6 a ^ p = 1 →
    rootDiagUnit .E6 a ≠ 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem TwistedE6TrialityComponentsT_ofPrime.toT (h : TwistedE6TrialityComponentsT_ofPrime) :
    TwistedE6TrialityComponentsT :=
  fun L _ _ p S hS a haT hTp ha1 i v hΨ hρ h1 h2 =>
    h L p p S S.hp S.natCast_ne_zero hS a haT hTp ha1 i v hΨ hρ h1 h2

end Statements

section Small

theorem excQuasisimpleAt_G2T_of_prime : ExcQuasisimpleAtT_ofPrime .G2 := by
  intro L _ _ p₀ p S hp hpL a haT hTp ha1 i hk
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  obtain ⟨-, hA | ⟨hr, -, -⟩⟩ := exc_kind hk
  · rw [hA.1] at hle
    exact absurd hle (by decide)
  · rw [hr] at hle
    exact absurd hle (by decide)

theorem excQuasisimpleAt_F4T_of_prime : ExcQuasisimpleAtT_ofPrime .F4 := by
  intro L _ _ p₀ p S hp hpL a haT hTp ha1 i hk
  obtain ⟨-, hA | ⟨hr, hc, -⟩⟩ := exc_kind hk
  · have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hA.1] at hle
    exact absurd hle (by decide)
  · obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))

theorem excQuasisimpleAt_D4T_of_prime : ExcQuasisimpleAtT_ofPrime .D4 := by
  intro L _ _ p₀ p S hp hpL a haT hTp ha1 i hk
  obtain ⟨-, hA | ⟨-, hc, -⟩⟩ := exc_kind hk
  · have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hA.1] at hle
    exact absurd hle (by decide)
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1

theorem excQuasisimpleAt_G2T : ExcQuasisimpleAtT .G2 :=
  excQuasisimpleAt_G2T_of_prime.toT

theorem excQuasisimpleAt_F4T : ExcQuasisimpleAtT .F4 :=
  excQuasisimpleAt_F4T_of_prime.toT

theorem excQuasisimpleAt_D4T : ExcQuasisimpleAtT .D4 :=
  excQuasisimpleAt_D4T_of_prime.toT

theorem excQuasisimpleAt_G2 : ExcQuasisimpleAt .G2 := fun L _ _ p S a ha ha1 i hk =>
  excQuasisimpleAt_G2T L p S a (S.E_le ha).1 (S.E_exp _ ha) ha1 i hk

theorem excQuasisimpleAt_F4 : ExcQuasisimpleAt .F4 := fun L _ _ p S a ha ha1 i hk =>
  excQuasisimpleAt_F4T L p S a (S.E_le ha).1 (S.E_exp _ ha) ha1 i hk

theorem excQuasisimpleAt_D4 : ExcQuasisimpleAt .D4 := fun L _ _ p S a ha ha1 i hk =>
  excQuasisimpleAt_D4T L p S a (S.E_le ha).1 (S.E_exp _ ha) ha1 i hk

end Small

section Assembly

theorem excQuasisimpleAt_E8T_of_prime : ExcQuasisimpleAtT_ofPrime .E8 := by
  intro L _ _ p₀ p S hp hpL a haT hTp ha1 i hk
  obtain ⟨hnin, hA | ⟨hr, hc, hnin2⟩⟩ := exc_kind hk
  · obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i hA.1 hA.2
    exact isQuasisimple_rationalComponent_e6T S haT i v hv
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) haT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact isQuasisimple_rationalComponent_of_d4 d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hnin2

theorem excQuasisimpleAt_E8T : ExcQuasisimpleAtT .E8 :=
  excQuasisimpleAt_E8T_of_prime.toT

theorem excQuasisimpleAt_E8 : ExcQuasisimpleAt .E8 := fun L _ _ p S a ha ha1 i hk =>
  excQuasisimpleAt_E8T L p S a (S.E_le ha).1 (S.E_exp _ ha) ha1 i hk

theorem excQuasisimpleAt_E7T_of_prime : ExcQuasisimpleAtT_ofPrime .E7 := by
  intro L _ _ p₀ p S hp hpL a haT hTp ha1 i hk
  obtain ⟨hnin, hA | ⟨hr, hc, hnin2⟩⟩ := exc_kind hk
  · obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i hA.1 hA.2
    exact isQuasisimple_rationalComponent_e6T S haT i v hv
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) haT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact isQuasisimple_rationalComponent_of_d4 d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hnin2

theorem excQuasisimpleAt_E7T : ExcQuasisimpleAtT .E7 :=
  excQuasisimpleAt_E7T_of_prime.toT

theorem excQuasisimpleAt_E7 : ExcQuasisimpleAt .E7 := fun L _ _ p S a ha ha1 i hk =>
  excQuasisimpleAt_E7T L p S a (S.E_le ha).1 (S.E_exp _ ha) ha1 i hk

theorem excQuasisimpleAt_E6_of_of_prime {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup .E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) (a : Fin Tag.E6.rank → Lˣ)
    (haT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit .E6 a ^ p = 1) (ha1 : rootDiagUnit .E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (htw : (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹) →
      ∀ v : WeylGroup .E6,
        componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
        (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
        ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
        ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨hnin, hA | ⟨hr, hc, hnin2⟩⟩ := exc_kind hk
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hA.2]; rfl)) ha1
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) haT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact isQuasisimple_rationalComponent_of_d4 d4Base_E6 d4TrialityLayer_E6 S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hnin2
    · rw [hs, Function.iterate_one] at hnin
      rw [hs, mul_one] at hnin2
      exact htw ⟨t, ht, Fr, hFr, hΦ⟩ v hv hρ hnin hnin2

theorem excQuasisimpleAt_E6_of {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (a : Fin Tag.E6.rank → Lˣ) (haT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit .E6 a ^ p = 1) (ha1 : rootDiagUnit .E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (htw : (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹) →
      ∀ v : WeylGroup .E6,
        componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
        (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
        ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
        ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  excQuasisimpleAt_E6_of_of_prime S S.hp S.natCast_ne_zero a haT hTp ha1 i hk htw

theorem excQuasisimpleAt_E6T_of_prime (hTw : TwistedE6TrialityComponentsT_ofPrime) :
    ExcQuasisimpleAtT_ofPrime .E6 :=
  fun L _ _ p₀ p S hp hpL a haT hTp ha1 i hk =>
    excQuasisimpleAt_E6_of_of_prime S hp hpL a haT hTp ha1 i hk
      fun hS v hΨ hρ h1 h2 => hTw L p₀ p S hp hpL hS a haT hTp ha1 i v hΨ hρ h1 h2

theorem excQuasisimpleAt_E6T (hTw : TwistedE6TrialityComponentsT) : ExcQuasisimpleAtT .E6 :=
  fun L _ _ p S a haT hTp ha1 i hk => excQuasisimpleAt_E6_of S a haT hTp ha1 i hk
    fun hS v hΨ hρ h1 h2 => hTw L p S hS a haT hTp ha1 i v hΨ hρ h1 h2

theorem excQuasisimpleAt_E6 (hTw : TwistedE6TrialityComponents) : ExcQuasisimpleAt .E6 :=
  fun L _ _ p S a ha ha1 i hk =>
    excQuasisimpleAt_E6_of S a (S.E_le ha).1 (S.E_exp _ ha) ha1 i hk
      fun hS v hΨ hρ h1 h2 => hTw L p S hS a ha ha1 i v hΨ hρ h1 h2

theorem langComponentsQuasisimple_exc (hTw : TwistedE6TrialityComponents) :
    LangComponentsQuasisimple .exc := by
  intro τ
  cases τ with
  | G2 => exact fun L _ _ p S a ha ha1 i hk _ => excQuasisimpleAt_G2 L p S a ha ha1 i hk
  | F4 => exact fun L _ _ p S a ha ha1 i hk _ => excQuasisimpleAt_F4 L p S a ha ha1 i hk
  | D4 => exact fun L _ _ p S a ha ha1 i hk _ => excQuasisimpleAt_D4 L p S a ha ha1 i hk
  | E6 => exact fun L _ _ p S a ha ha1 i hk _ => excQuasisimpleAt_E6 hTw L p S a ha ha1 i hk
  | E7 => exact fun L _ _ p S a ha ha1 i hk _ => excQuasisimpleAt_E7 L p S a ha ha1 i hk
  | E8 => exact fun L _ _ p S a ha ha1 i hk _ => excQuasisimpleAt_E8 L p S a ha ha1 i hk

theorem excQuasisimpleAtT_of_prime (hTw : TwistedE6TrialityComponentsT_ofPrime) (τ : Tag) :
    ExcQuasisimpleAtT_ofPrime τ := by
  cases τ with
  | G2 => exact excQuasisimpleAt_G2T_of_prime
  | F4 => exact excQuasisimpleAt_F4T_of_prime
  | D4 => exact excQuasisimpleAt_D4T_of_prime
  | E6 => exact excQuasisimpleAt_E6T_of_prime hTw
  | E7 => exact excQuasisimpleAt_E7T_of_prime
  | E8 => exact excQuasisimpleAt_E8T_of_prime

theorem excQuasisimpleAtT_of (hTw : TwistedE6TrialityComponentsT) (τ : Tag) :
    ExcQuasisimpleAtT τ := by
  cases τ with
  | G2 => exact excQuasisimpleAt_G2T
  | F4 => exact excQuasisimpleAt_F4T
  | D4 => exact excQuasisimpleAt_D4T
  | E6 => exact excQuasisimpleAt_E6T hTw
  | E7 => exact excQuasisimpleAt_E7T
  | E8 => exact excQuasisimpleAt_E8T

end Assembly

end CFSG.HardMathSupport.Timmesfeld.LangTorus
