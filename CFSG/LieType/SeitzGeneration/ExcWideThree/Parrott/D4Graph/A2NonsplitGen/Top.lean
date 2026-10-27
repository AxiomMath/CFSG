module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Lift
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Roots

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

@[expose] def rootsU2 : List (Fin Tag.D4.rank → ℤ) := [rootB1, rootB2, rootB3, rootH1, rootH2]

@[expose] def rootsH1 : List (Fin Tag.D4.rank → ℤ) :=
  [Pi.single ⟨1, by decide⟩ 1, rootF1, rootB1, rootB2, rootB3, rootH1, rootH2]

@[expose] def rootsH3 : List (Fin Tag.D4.rank → ℤ) :=
  [Pi.single ⟨3, by decide⟩ 1, rootF3, rootB1, rootB2, rootB3, rootH1, rootH2]

@[expose] def rootsN0 : List (Fin Tag.D4.rank → ℤ) :=
  [Pi.single ⟨1, by decide⟩ 1, rootF1, Pi.single ⟨3, by decide⟩ 1, rootF3, rootB1, rootB2, rootB3,
    rootH1, rootH2]

section Facts


theorem rootLists_sl2 : ∀ L ∈ [rootsU2, rootsH1, rootsH3],
    ∀ r ∈ [(Pi.single ⟨2, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), -Pi.single ⟨2, by decide⟩ 1],
      ∀ s ∈ L, IsRoot Tag.D4 s ∧ r ≠ -s ∧ (IsRoot Tag.D4 (r + s) → r + s ∈ L) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem rootLists_rho : (∀ s ∈ rootsU2, IsRoot Tag.D4 s ∧ rhoL s ∈ rootsU2) ∧
    (∀ s ∈ rootsH1, IsRoot Tag.D4 s ∧ rhoL s ∈ rootsH3) ∧
    (∀ s ∈ [(Pi.single ⟨0, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), rootF0],
      IsRoot Tag.D4 s ∧ rhoL s ∈ rootsH1) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem rootLists_normU2 : ∀ r ∈ rootsH1 ++ rootsH3, IsRoot Tag.D4 r ∧
    ∀ s ∈ rootsU2, IsRoot Tag.D4 s ∧ r ≠ -s ∧ (IsRoot Tag.D4 (r + s) → r + s ∈ rootsU2) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem rootLists_commU2 :
    ∀ r ∈ [(Pi.single ⟨0, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), rootF0], IsRoot Tag.D4 r ∧
      ∀ s ∈ rootsH1 ++ rootsH3, IsRoot Tag.D4 s ∧ r ≠ -s ∧
        (IsRoot Tag.D4 (r + s) → r + s ∈ rootsU2) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem rootLists_comm : IsRoot Tag.D4 rootB3 ∧
    (∀ s ∈ rootsN0, IsRoot Tag.D4 s ∧ rootB3 ≠ -s ∧ ¬IsRoot Tag.D4 (rootB3 + s)) ∧
    ∀ s ∈ rootsU2, ∀ s' ∈ rootsU2, IsRoot Tag.D4 s ∧ IsRoot Tag.D4 s' ∧ s ≠ -s' ∧
      ¬IsRoot Tag.D4 (s + s') := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem rootLists_incl : (∀ s ∈ rootsU2, s ∈ rootsN0) ∧ (∀ s ∈ rootsH1, s ∈ rootsN0) ∧
    ∀ s ∈ rootsH3, s ∈ rootsN0 := by
  decide

end Facts

section U2


variable {K : Type} [Field K]

theorem pow_ringChar_eq_one_of_mem_U2 {g : ↥(adjointGroup Tag.D4 K)}
    (hg : g ∈ spanRoots K rootsU2) : g ^ ringChar K = 1 := by
  obtain ⟨-, -, hab⟩ := rootLists_comm
  refine pow_eq_one_of_mem_closure ?_ ?_ hg
  · rintro _ ⟨s, hs, c, rfl⟩ _ ⟨s', hs', c', rfl⟩ -
    obtain ⟨hsr, hsr', hne, hsum⟩ := hab s hs s' hs'
    exact commute_xPar_of_not_isRoot hsr hsr' hne hsum c c'
  · rintro _ ⟨s, -, c, rfl⟩
    rw [xPar_pow, ringChar.Nat.cast_ringChar, zero_mul, xPar_zero]

theorem not_three_dvd_card_U2 [Finite K] (hK3 : ringChar K ≠ 3) [Finite ↥(spanRoots K rootsU2)] :
    ¬3 ∣ Nat.card ↥(spanRoots K rootsU2) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  have h3p : ¬3 ∣ ringChar K := fun h =>
    hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h).symm
  exact not_dvd_card_of_pow_eq_one Nat.prime_three h3p _ fun g hg =>
    pow_ringChar_eq_one_of_mem_U2 hg

theorem commute_xPar_rootB3_of_mem_N0 {n : ↥(adjointGroup Tag.D4 K)}
    (hn : n ∈ spanRoots K rootsN0) (c : K) : Commute (𝕩 rootB3 c) n := by
  obtain ⟨hb3, hN0, -⟩ := rootLists_comm
  have hle : spanRoots K rootsN0 ≤ Subgroup.centralizer {𝕩 rootB3 c} := by
    refine spanRoots_le fun s hs d => ?_
    obtain ⟨hsr, hne, hsum⟩ := hN0 s hs
    exact Subgroup.mem_centralizer_singleton_iff.2
      (commute_xPar_of_not_isRoot hb3 hsr hne hsum c d).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hn)).symm

theorem le_commModSubgroup {r : Fin Tag.D4.rank → ℤ}
    (hr : r ∈ [(Pi.single ⟨0, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), rootF0]) (t : K)
    {L : List (Fin Tag.D4.rank → ℤ)} (hL : ∀ s ∈ L, s ∈ rootsH1 ++ rootsH3) :
    spanRoots K L ≤ commModSubgroup (spanRoots K rootsU2) (𝕩 r t)⁻¹ := by
  obtain ⟨hrr, hrs⟩ := rootLists_commU2 r hr
  refine spanRoots_le fun s hs d => ⟨?_, ?_⟩
  · obtain ⟨hsr, hsU⟩ := rootLists_normU2 s (hL s hs)
    exact xPar_mem_normalizer_spanRoots hsr hsU d
  · obtain ⟨hsr, hne, hsum⟩ := hrs s (hL s hs)
    have h := commutator_xPar_mem_spanRoots (K := K) hrr hsr hne hsum (-t) d
    rw [commutatorElement_def] at h
    rwa [xPar_neg]

end U2

section Top


variable {K : Type} [Field K]

theorem sl2At_two_mem_normalizer_rootLists {L : List (Fin Tag.D4.rank → ℤ)}
    (hL : L ∈ [rootsU2, rootsH1, rootsH3]) (A : SL2 K) :
    sl2At K ⟨2, by decide⟩ A ∈
      Subgroup.normalizer (spanRoots K L : Set ↥(adjointGroup Tag.D4 K)) := by
  have h := rootLists_sl2 L hL
  refine sl2At_two_mem_normalizer (fun t => ?_) (fun t => ?_) A
  · exact xPar_mem_normalizer_spanRoots (isRoot_single Tag.D4 _) (h _ (by simp)) t
  · exact xPar_mem_normalizer_spanRoots (isRoot_neg_single Tag.D4 _) (h _ (by simp)) t

theorem gammaP_xPar_mem (B : SL2 K) {r : Fin Tag.D4.rank → ℤ}
    (hr : r ∈ [(Pi.single ⟨0, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), rootF0]) (t : K) :
    gammaP K B (𝕩 r t) ∈ spanRoots K rootsH1 ∧
      gammaP K B (gammaP K B (𝕩 r t)) ∈ spanRoots K rootsH3 := by
  obtain ⟨-, hρH, hρr⟩ := rootLists_rho
  have ha : gammaP K B (𝕩 r t) ∈ spanRoots K rootsH1 :=
    gammaP_mem_spanRoots (S := [r]) (fun s hs => by
      rw [List.mem_singleton] at hs
      subst hs
      exact hρr _ hr) (sl2At_two_mem_normalizer_rootLists (by simp) B)
      (xPar_mem_spanRoots (List.mem_singleton_self r) t)
  exact ⟨ha, gammaP_mem_spanRoots hρH (sl2At_two_mem_normalizer_rootLists (by simp) B) ha⟩

theorem exists_fixed_mul [Finite K] (hK3 : ringChar K ≠ 3) {B : SL2 K} (hB3 : B ^ 3 = 1)
    {r : Fin Tag.D4.rank → ℤ}
    (hr : r ∈ [(Pi.single ⟨0, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), rootF0]) (t : K) :
    ∃ m ∈ spanRoots K rootsU2, gammaP K B (𝕩 r t * gammaP K B (𝕩 r t) *
        gammaP K B (gammaP K B (𝕩 r t)) * m) =
      𝕩 r t * gammaP K B (𝕩 r t) * gammaP K B (gammaP K B (𝕩 r t)) * m := by
  obtain ⟨ha, hb⟩ := gammaP_xPar_mem B hr t
  set α := gammaP K B
  set v := 𝕩 r t
  have hα3 : ∀ g, α (α (α g)) = g := by
    intro g
    have h := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ g) (gammaP_pow_three hB3)
    simpa [pow_succ, MulAut.mul_apply] using h
  have hU : ∀ m ∈ spanRoots K rootsU2, α m ∈ spanRoots K rootsU2 := fun m hm =>
    gammaP_mem_spanRoots rootLists_rho.1 (sl2At_two_mem_normalizer_rootLists (by simp) B) hm
  have hy : α v * α (α v) ∈ commModSubgroup (spanRoots K rootsU2) v⁻¹ :=
    Subgroup.mul_mem _
      (le_commModSubgroup hr t (fun s hs => List.mem_append_left _ hs) ha)
      (le_commModSubgroup hr t (fun s hs => List.mem_append_right _ hs) hb)
  have hw : (v * α v * α (α v))⁻¹ * α (v * α v * α (α v)) ∈ spanRoots K rootsU2 := by
    obtain ⟨hyN, hyc⟩ := hy
    have e : (v * α v * α (α v))⁻¹ * α (v * α v * α (α v)) =
        (α v * α (α v))⁻¹ * (v⁻¹ * (α v * α (α v)) * v⁻¹⁻¹ * (α v * α (α v))⁻¹) *
          (α v * α (α v)) := by
      rw [map_mul, map_mul, hα3]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff''.1 hyN _).1 hyc
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have : Finite ↥(spanRoots K rootsU2) := Subtype.finite
  exact exists_fixed_mul_of_not_dvd α hα3 _ (not_three_dvd_card_U2 hK3) hU hw

theorem xPar_mem_closure_of_commutator [Finite K] (hK3 : ringChar K ≠ 3) {B : SL2 K}
    (hB3 : B ^ 3 = 1) {r r' : Fin Tag.D4.rank → ℤ}
    (hr : r ∈ [(Pi.single ⟨0, by decide⟩ 1 : Fin Tag.D4.rank → ℤ), rootF0])
    (hcomm : ∀ t : K, ⁅𝕩 rootB3 (1 : K), 𝕩 r t⁆ = 𝕩 r' (-t)) (t : K) :
    𝕩 r' (-t) ∈ Subgroup.closure
      ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪ frameSet K) := by
  set M := Subgroup.closure
    ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪ frameSet K)
  obtain ⟨m, hm, hfix⟩ := exists_fixed_mul hK3 hB3 hr t
  obtain ⟨ha, hb⟩ := gammaP_xPar_mem B hr t
  set a := gammaP K B (𝕩 r t)
  set b := gammaP K B a
  have hu : 𝕩 r t * a * b * m ∈ M := Subgroup.subset_closure (Or.inl (mem_fixedSubgroup.2 hfix))
  have hx : 𝕩 rootB3 (1 : K) ∈ M :=
    Subgroup.subset_closure (Or.inr ⟨rootB3, by decide, 1, Or.inl rfl⟩)
  obtain ⟨iU, iH1, iH3⟩ := rootLists_incl
  have hn : a * b * m ∈ spanRoots K rootsN0 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (spanRoots_mono iH1 ha) (spanRoots_mono iH3 hb))
      (spanRoots_mono iU hm)
  have key : ⁅𝕩 rootB3 (1 : K), 𝕩 r t * a * b * m⁆ = 𝕩 r' (-t) := by
    rw [show 𝕩 r t * a * b * m = 𝕩 r t * (a * b * m) by group,
      commutatorElement_mul_of_commute (commute_xPar_rootB3_of_mem_N0 hn 1), hcomm]
  rw [← key, commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hx hu) (M.inv_mem hx)) (M.inv_mem hu)

theorem frameTopRootsMem_holds : FrameTopRootsMem := by
  intro K _ _ hK3 B hB3 c
  have h1 : ∀ t : K, ⁅𝕩 rootB3 (1 : K), 𝕩 (Pi.single ⟨0, by decide⟩ 1) t⁆ = 𝕩 rootH1 (-t) := by
    intro t
    rw [commutator_eq_of_repCheck (a := 15) (b := 0) (g := 19) (C := -1) (ε := rootH1) (by decide)
      (by decide) (by decide) (by decide +kernel)]
    congr 1
    push_cast
    ring
  have h2 : ∀ t : K, ⁅𝕩 rootB3 (1 : K), 𝕩 rootF0 t⁆ = 𝕩 rootH2 (-t) := by
    intro t
    rw [commutator_eq_of_repCheck (a := 15) (b := 5) (g := 22) (C := -1) (ε := rootH2) (by decide)
      (by decide) (by decide) (by decide +kernel)]
    congr 1
    push_cast
    ring
  have m1 := xPar_mem_closure_of_commutator hK3 hB3 (by simp) h1 (-c)
  have m2 := xPar_mem_closure_of_commutator hK3 hB3 (by simp) h2 (-c)
  rw [neg_neg] at m1 m2
  exact ⟨m1, m2⟩

end Top

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen
