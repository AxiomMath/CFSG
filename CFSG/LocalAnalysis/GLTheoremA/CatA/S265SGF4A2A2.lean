module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4Kit
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433 (KernelA2A2)

section Helpers

private lemma rootDiagUnit_ne_one_of_exists_ne_zero
    {L : Type} [Field L] {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ}
    {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3)
    (hk0 : ∃ i, k i ≠ 0) (hak : ∀ i, a i = ω ^ k i) :
    rootDiagUnit Tag.F4 a ≠ 1 := by
  intro h
  obtain ⟨i, hi⟩ := hk0
  have ha : a = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
    (h.trans rootDiagUnit_one.symm)
  have hai : ω ^ k i = 1 := by rw [← hak i, ha, Pi.one_apply]
  rcases (by have := hk3 i; omega : k i = 1 ∨ k i = 2) with h' | h'
  · rw [h', pow_one] at hai
    exact hω1 hai
  · rw [h'] at hai
    have h3 : ω ^ 3 = ω ^ 2 * ω := pow_succ ω 2
    rw [hai, one_mul, hω3] at h3
    exact hω1 h3.symm

variable {L : Type} [Field L]
  [IsAlgClosed L] {p₀ : ℕ}

private lemma frameRoots_iterate_mem {τ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (S : LangSetup Tag.F4 L p₀)
    (hρτ : (S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' frameRoots τ =
      frameRoots τ) :
    ∀ n : ℕ, ∀ γ ∈ frameRoots τ, (⇑S.ρ)^[n] γ ∈ frameRoots τ := by
  intro n
  induction n with
  | zero => exact fun γ hγ => hγ
  | succ n ih =>
    intro γ hγ
    rw [Function.iterate_succ_apply', ← hρτ]
    exact Set.mem_image_of_mem _ (ih γ hγ)

private lemma rationalComponent_le_rootSpan (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.F4 L (rationalRoots S.ρ (rootCharHom a) i) :=
  (Subgroup.commutator_le_self _).trans inf_le_left

private lemma quasisimple_not_abelian (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hi : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        ∀ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute x y) := by
  intro hc
  have := hi.2.toNontrivial
  obtain ⟨z, hz⟩ := exists_ne
    (1 : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective z
  exact hz ((QuotientGroup.eq_one_iff u).2 (Subgroup.mem_center_iff.2 fun w =>
    Subtype.ext (hc w w.2 u u.2).eq))

end Helpers


section A2A2

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

omit
  [CharP L 2] in
private lemma rationalRoots_ne_of_kernelA2A2 (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} {σ τ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} {κ κ' : ℤ}
    {iΛ iΘ : KernelComponent (rootCharHom a)}
    (hP : Lemma27Ns.I1433.A2Pair σ τ κ κ')
    (hΛ : componentRoots (rootCharHom a) iΛ = frameRoots σ)
    (hΘ : componentRoots (rootCharHom a) iΘ = frameRoots τ)
    (hit : ∀ n : ℕ, ∀ γ ∈ frameRoots τ, (⇑S.ρ)^[n] γ ∈ frameRoots τ) :
    rationalRoots S.ρ (rootCharHom a) iΛ ≠ rationalRoots S.ρ (rootCharHom a) iΘ := by
  intro h
  have hmem : σ 0 1 ∈ rationalRoots S.ρ (rootCharHom a) iΘ := by
    rw [← h]
    exact ⟨0, σ 0 1, by rw [hΛ]; exact ⟨0, 1, by decide, rfl⟩, rfl⟩
  obtain ⟨n, δ, hδ, hδe⟩ := hmem
  rw [hΘ] at hδ
  obtain ⟨x', y', hxy', hτ⟩ := hit n δ hδ
  have h0 := hP.orth 0 1 x' y' (by decide) hxy'
  rw [← hτ, ← hδe, hP.σ_norm 0 1 (by decide)] at h0
  exact hP.κ_ne_zero (by omega)

omit
  [CharP L 2] in
private lemma components_and_hRle (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {C : Type} [Group C] [Finite C] (ι : C →* ModGL Tag.F4 L) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit Tag.F4 a * ι c * (rootDiagUnit Tag.F4 a)⁻¹)
    {J : Subgroup C} (hJ : IsComponentOf J (fixSubgroup β))
    (hle : ∀ J' : Subgroup C, IsComponentOf J' (fixSubgroup β) → J' ≤ J) :
    ∃ j : KernelComponent (rootCharHom a),
      ∀ i, CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
          rationalComponent S.ρ S.Γ (rootCharHom a) j := by
  classical
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hcomapfix :
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hcompR : ∀ i, CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a}) := fun i hi => by
    obtain ⟨hle', hsub⟩ := langSubnormal_of_mem_torus S hT i
    exact ⟨hle', (CFSG.Open.IsSubnormal.iff_subgroupOf hle').2 hsub, hi⟩
  obtain ⟨j, -, hj⟩ :=
    components_of_langSetup S Nat.prime_three ι hι hrange β hβ hT hap h1 hTame hJ
  refine ⟨j, fun i hi => ?_⟩
  have hF := isComponentOf_comap_of_injective ι hι ((hcompR i hi).1.trans hCdrange) hCdrange
    (hcompR i hi)
  rw [hcomapfix] at hF
  have h := Subgroup.map_mono (f := ι) (hle _ hF)
  rwa [Subgroup.map_comap_eq_self ((hcompR i hi).1.trans hCdrange), hj] at h

theorem SG.false_of_kernelA2A2_of_le_of_quasisimple (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hqs : ∀ i : KernelComponent (rootCharHom a),
      CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3)
    (hk0 : ∃ i, k i ≠ 0) (hak : ∀ i, a i = ω ^ k i) (hk : KernelA2A2 k)
    {C : Type} [Group C] [Finite C] (ι : C →* ModGL Tag.F4 L) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit Tag.F4 a * ι c * (rootDiagUnit Tag.F4 a)⁻¹)
    {J : Subgroup C} (hJ : IsComponentOf J (fixSubgroup β))
    (hle : ∀ J' : Subgroup C, IsComponentOf J' (fixSubgroup β) → J' ≤ J) : False := by
  classical
  have h1 := rootDiagUnit_ne_one_of_exists_ne_zero hω3 hω1 hk3 hk0 hak
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρσ, hρτ⟩ :=
    Lemma27Ns.I1433.exists_pair_frames S hT hap hω3 hω1 hak hk
  have hit := frameRoots_iterate_mem S hρτ
  have hne := rationalRoots_ne_of_kernelA2A2 S hP hΛ hΘ hit
  have hcomm :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rho_mem_kernelRoots_of_mem_torus S hT)
    S.frob.iform_eq hne
  have hR : ∀ i, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.F4 L (rationalRoots S.ρ (rootCharHom a) i) := fun i =>
    rationalComponent_le_rootSpan S i
  obtain ⟨j, hRle⟩ := components_and_hRle S hT hap h1 hTame ι hι hrange β hβ hJ hle
  rcases hall j with hjΛ | hjΘ
  · have h := hRle iΘ (hqs iΘ)
    rw [hjΛ] at h
    exact (quasisimple_not_abelian S iΘ (hqs iΘ)) fun x hx y hy =>
      (hcomm y (hR iΛ (h hy)) x (hR iΘ hx)).symm
  · have h := hRle iΛ (hqs iΛ)
    rw [hjΘ] at h
    exact (quasisimple_not_abelian S iΛ (hqs iΛ)) fun x hx y hy =>
      hcomm x (hR iΛ hx) y (hR iΘ (h hy))

end A2A2

end CFSG.LocalAnalysis.GLTheoremA.S265

end
