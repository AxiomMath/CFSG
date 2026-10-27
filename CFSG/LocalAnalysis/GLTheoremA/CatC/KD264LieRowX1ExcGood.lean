module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T
open scoped Matrix MatrixGroups

section Card

variable {τ : Tag} {L : Type} [Field L]
  {ν : ℕ} {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem ncard_le_of_class (X : Finset (Fin ν)) {C : Set (Fin τ.rank → ℤ)}
    (hC : ∀ γ ∈ C, ∃ i j, i ∈ X ∧ j ∈ X ∧ i ≠ j ∧ γ = σ i j) :
    C.ncard ≤ X.card * (X.card - 1) := by
  classical
  have hsub : C ⊆ (fun p : Fin ν × Fin ν => σ p.1 p.2) '' (X.offDiag : Set (Fin ν × Fin ν)) := by
    intro γ hγ
    obtain ⟨i, j, hi, hj, hij, rfl⟩ := hC γ hγ
    exact ⟨(i, j), by simp [hi, hj, hij], rfl⟩
  calc C.ncard ≤ ((fun p : Fin ν × Fin ν => σ p.1 p.2) ''
        (X.offDiag : Set (Fin ν × Fin ν))).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ (X.offDiag : Set (Fin ν × Fin ν)).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = X.card * (X.card - 1) := by
        rw [Set.ncard_coe_finset, Finset.offDiag_card, Nat.mul_sub, mul_one]

end Card

section Main


theorem exc_component_of_data {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup τ L 5)
    (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (hTor : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ∈ S.D.torus)
    (u v : Fin τ.rank → ZMod 3) (ord ordC : List (Fin τ.rank → ℤ)) (k c : ℕ)
    (hord : ∀ γ, (IsRoot τ γ ∧ dotT u γ = 0) ↔ γ ∈ ord)
    (hordconn : ∀ j : ℕ, j < ord.length → 0 < j →
      ∃ i : ℕ, i < j ∧ iform (ord.getD i default) (ord.getD j default) ≠ 0)
    (hnodup : ord.Nodup) (hcardk : ord.length = k * (k + 1)) (hk2 : 2 ≤ k)
    (hrank : compRank {γ | γ ∈ ord} = k)
    (hCne : ordC ≠ []) (hCsub : ∀ γ ∈ ordC, γ ∈ ord ∧ dotT v γ = 0)
    (hCconn : ∀ j : ℕ, j < ordC.length → 0 < j →
      ∃ i : ℕ, i < j ∧ iform (ordC.getD i default) (ordC.getD j default) ≠ 0)
    (hCnodup : ordC.Nodup) (hCcard : ordC.length = c)
    (hnum : ∀ m : ℕ, c ≤ m * (m - 1) → 4 ≤ m ∧ k + 1 < 2 * m) :
    ∃ J : Subgroup (ModGL τ L),
      CFSG.Open.IsSubnormal J (S.Γ ⊓
        Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ u)} : Set (ModGL τ L)) ⊓
        Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ v)} : Set (ModGL τ L))) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  classical
  set a : Fin τ.rank → Lˣ := thetaTupleG τ ζ u with ha
  set b : Fin τ.rank → Lˣ := thetaTupleG τ ζ v with hb
  have haT : rootDiagUnit τ a ∈ S.D.torus := hTor a (thetaTupleG_pow_three hζ u)
  have hker : ∀ γ, γ ∈ kernelRoots (rootCharHom a) ↔ γ ∈ ord := fun γ =>
    (mem_kernelRoots_thetaTupleG_iff hζ hζ' u γ).trans (hord γ)
  obtain ⟨α₀, hα₀⟩ := List.exists_mem_of_ne_nil _ hCne
  have hα₀ord : α₀ ∈ ord := (hCsub α₀ hα₀).1
  have hα₀ker : α₀ ∈ kernelRoots (rootCharHom a) := (hker α₀).2 hα₀ord
  set i : KernelComponent (rootCharHom a) := (⟦⟨α₀, hα₀ker⟩⟧ : KernelComponent (rootCharHom a)) with hi
  set Ψ : Set (Fin τ.rank → ℤ) := {γ | γ ∈ ord} with hΨ
  have hΨker : Ψ ⊆ kernelRoots (rootCharHom a) := fun γ hγ => (hker γ).2 hγ
  have hΨconn : ∀ x ∈ Ψ, ∀ y ∈ Ψ, Relation.ReflTransGen (KerAdj (rootCharHom a)) x y := by
    refine reflTransGen_of_ordering (KerAdj (rootCharHom a)) ord ?_
    intro j hj0 hjlt
    obtain ⟨i', hij, hadj⟩ := hordconn j hjlt hj0
    refine ⟨i', hij, ?_, ?_, hadj⟩
    · rw [List.getD_eq_getElem _ _ (by omega)]
      exact (hker _).2 (List.getElem_mem _)
    · rw [List.getD_eq_getElem _ _ hjlt]
      exact (hker _).2 (List.getElem_mem _)
  have hcomp : componentRoots (rootCharHom a) i = Ψ :=
    componentRoots_eq_of_closed (rootCharHom a) Ψ hΨker hΨconn (fun x _ y hy _ => (hker y).1 hy) hα₀ord
  have hncard : Ψ.ncard = k * (k + 1) := by
    have : Ψ = ↑ord.toFinset := by ext γ; simp [hΨ]
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hcardk]
  have hrk : compRank (componentRoots (rootCharHom a) i) = k := by rw [hcomp]; exact hrank
  have hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) * (compRank (componentRoots (rootCharHom a) i) + 1) := by
    rw [hcomp]; rw [show compRank Ψ = k from hrank]; exact hncard
  have hp3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := by
      have := S.hqpow.2
      rwa [hq2] at this
    have h3 : ((3 : ℕ) : L) = 1 := by
      push_cast at h2 ⊢
      linear_combination h2
    rw [h3]
    exact one_ne_zero
  have hTp : rootDiagUnit τ a ^ 3 = 1 := by
    have h1 : a ^ 3 = 1 := funext fun j => by
      rw [Pi.pow_apply, Pi.one_apply]; exact thetaTupleG_pow_three hζ u j
    have := map_pow (rootDiagUnitHom τ L) a 3
    rw [h1, map_one] at this
    exact this.symm
  obtain ⟨ν, ψ, σf, hν3, hψ, hnorm, hΨf⟩ : ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L)
      (σf : Fin ν → Fin ν → Fin τ.rank → ℤ), 3 ≤ ν ∧ IsSLFrame ψ σf ∧
      (∀ a b, a ≠ b → iform (σf a b) (σf a b) = 2 * 1) ∧
      componentRoots (rootCharHom a) i = frameRoots σf := by
    rcases hτ with rfl | rfl
    · exact exists_frame_of_typeA_E7_T_of_prime S Nat.prime_three hp3L hTp i (by omega) hn
    · exact exists_frame_of_typeA_E8_T_of_prime S Nat.prime_three hp3L hTp i (by omega) hn
  have hΨ' : Ψ = frameRoots σf := hcomp.symm.trans hΨf
  have hcard0 := ncard_frameRoots hψ (κ := 1) one_ne_zero hnorm
  have hcardν : k * (k + 1) = ν * (ν - 1) := by
    rw [← hncard, hΨ']
    exact hcard0
  have hν : ν = k + 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hcardν
    rcases lt_trichotomy m k with h | h | h
    · exfalso; nlinarith
    · omega
    · exfalso; nlinarith
  set C : Set (Fin τ.rank → ℤ) := {γ | γ ∈ ordC} with hCdef
  have hCΨ : C ⊆ Ψ := fun γ hγ => (hCsub γ hγ).1
  have hCσ : ∀ γ ∈ C, ∃ i j, i ≠ j ∧ γ = σf i j := fun γ hγ => by
    have : γ ∈ frameRoots σf := hΨ' ▸ hCΨ hγ
    exact this
  have hCb : ∀ γ ∈ C, rootChar b γ = 1 := fun γ hγ =>
    (rootChar_thetaTupleG_eq_one_iff hζ hζ' v γ).2 (hCsub γ hγ).2
  have hCconn' : ∀ x ∈ C, ∀ y ∈ C,
      Relation.ReflTransGen (fun p q => p ∈ C ∧ q ∈ C ∧ iform p q ≠ 0) x y := by
    haveI : Std.Symm (fun p q : Fin τ.rank → ℤ => p ∈ C ∧ q ∈ C ∧ iform p q ≠ 0) :=
      ⟨fun p q ⟨hp, hq, h⟩ => ⟨hq, hp, by rwa [iform_comm]⟩⟩
    refine reflTransGen_of_ordering _ ordC ?_
    intro j hj0 hjlt
    obtain ⟨i', hij, hadj⟩ := hCconn j hjlt hj0
    refine ⟨i', hij, ?_, ?_, hadj⟩
    · rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    · rw [List.getD_eq_getElem _ _ hjlt]
      exact List.getElem_mem _
  have hα₀C : α₀ ∈ C := hα₀
  obtain ⟨k₀, hk₀⟩ := exists_class_of_connected hψ hnorm b hCσ hCb hCconn' hα₀C
  set X : Finset (Fin ν) := Finset.univ.filter (fun l => rootChar b (σf l k₀) = 1) with hXdef
  have hX : ∀ l, l ∈ X ↔ rootChar b (σf l k₀) = 1 := fun l => by simp [hXdef]
  have hCX : ∀ γ ∈ C, ∃ i j, i ∈ X ∧ j ∈ X ∧ i ≠ j ∧ γ = σf i j := by
    intro γ hγ
    obtain ⟨i', j', hij', hγij, hi', hj'⟩ := hk₀ γ hγ
    exact ⟨i', j', (hX i').2 hi', (hX j').2 hj', hij', hγij⟩
  have hCncard : C.ncard = c := by
    have : C = ↑ordC.toFinset := by ext γ; simp [hCdef]
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hCnodup, hCcard]
  have hle := ncard_le_of_class X hCX
  obtain ⟨h4, h2'⟩ := hnum X.card (by rw [← hCncard]; exact hle)
  have h2X : ν < 2 * X.card := by omega
  have hω3 : ((ζ : Lˣ) : L) ^ 3 = 1 := by
    have := congrArg Units.val hζ
    simpa using this
  have hω1 : ((ζ : Lˣ) : L) ≠ 1 := by
    intro h
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ'
    omega
  exact block_component S hq2 hAlg hρ haT i hν3 hψ hΨf hω3 hω1 k₀ X hX h4 h2X

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
