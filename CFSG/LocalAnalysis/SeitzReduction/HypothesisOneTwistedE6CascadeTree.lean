module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeWords
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeLevel

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

theorem twistedE6_isRoot_of_mem_posRoots
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ twistedE6PosRoots) :
    IsRoot TwistTag.E6.tag δ ∧ 0 < height δ := by
  have h : ∀ δ ∈ twistedE6PosRoots, twistedE6TwoRootB δ = true ∧ 0 < height δ := by
    decide +kernel
  exact ⟨isRoot_iff_twistedE6TwoRootB.2 (h δ hδ).1, (h δ hδ).2⟩

theorem twistedE6_mem_parabolic_of_mem
    {J : List (Fin TwistTag.E6.tag.rank)} {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : δ ∈ twistedE6PosRoots)
    (hs : ∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ J → δ l = 0) :
    δ ∈ parabolicPosRoots TwistTag.E6.tag {j | j ∈ J} :=
  ⟨⟨(twistedE6_isRoot_of_mem_posRoots hδ).1, fun l hl => hs l (List.mem_finRange l) hl⟩,
    twistedE6_isRoot_of_mem_posRoots hδ⟩

theorem twistedE6_parabolic_mono {J J' : Set (Fin TwistTag.E6.tag.rank)} (h : J ⊆ J') :
    parabolicPosRoots TwistTag.E6.tag J ⊆ parabolicPosRoots TwistTag.E6.tag J' :=
  fun _ hδ => ⟨⟨hδ.1.1, fun l hl => hδ.1.2 l fun h' => hl (h h')⟩, hδ.2⟩

set_option synthInstance.maxSize 2048 in
theorem twistedE6CascadeTree_roots :
    (e6CascC ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → e6CascC l = 0) ∧
      permLattice TwistTag.E6.perm e6CascC = e6CascC ∧ e6CascC ≠ e6RootA4 ∧
      iform e6CascC e6RootA4 = 0) ∧
    (e6RootA4 ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → e6RootA4 l = 0) ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → e6RootA4 l = 0) ∧
      permLattice TwistTag.E6.perm e6RootA4 = e6RootA4) ∧
    (e6RootA34 ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → e6RootA34 l = 0) ∧
      permLattice TwistTag.E6.perm e6RootA34 ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 →
        permLattice TwistTag.E6.perm e6RootA34 l = 0) ∧
      permLattice TwistTag.E6.perm e6RootA34 ≠ e6RootA34 ∧
      iform e6RootA34 (permLattice TwistTag.E6.perm e6RootA34) = 0) ∧
    (e6CascR17 ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → e6CascR17 l = 0) ∧
      permLattice TwistTag.E6.perm e6CascR17 = e6CascR17 ∧
      ¬ (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → e6CascR17 l = 0) ∧
      (∀ j ∈ twistedE6CascJA3, classKillPair j e6CascR17 = 0)) ∧
    (twistedE6CascPairA5 ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → twistedE6CascPairA5 l = 0) ∧
      permLattice TwistTag.E6.perm twistedE6CascPairA5 ∈ twistedE6PosRoots ∧
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 →
        permLattice TwistTag.E6.perm twistedE6CascPairA5 l = 0) ∧
      permLattice TwistTag.E6.perm twistedE6CascPairA5 ≠ twistedE6CascPairA5 ∧
      iform twistedE6CascPairA5 (permLattice TwistTag.E6.perm twistedE6CascPairA5) = 0 ∧
      twistedE6CascPairA5 ≠ e6RootA4 ∧ permLattice TwistTag.E6.perm twistedE6CascPairA5 ≠ e6RootA4 ∧
      iform twistedE6CascPairA5 e6RootA4 = 0 ∧
      iform (permLattice TwistTag.E6.perm twistedE6CascPairA5) e6RootA4 = 0) ∧
    (∀ δ ∈ twistedE6CascPosA3, δ ∈ twistedE6PosRoots ∧
      ∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → δ l = 0) ∧
    (∀ j ∈ twistedE6CascJA3, j ∈ twistedE6CascJA5) ∧
    (e6HighestRoot ∈ twistedE6PosRoots ∧
      permLattice TwistTag.E6.perm e6HighestRoot = e6HighestRoot ∧
      ¬ (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → e6HighestRoot l = 0) ∧
      (∀ j ∈ twistedE6CascJA5, classKillPair j e6HighestRoot = 0)) ∧
    (twistedE6CascPairE6 ∈ twistedE6PosRoots ∧
      permLattice TwistTag.E6.perm twistedE6CascPairE6 ∈ twistedE6PosRoots ∧
      permLattice TwistTag.E6.perm twistedE6CascPairE6 ≠ twistedE6CascPairE6 ∧
      iform twistedE6CascPairE6 (permLattice TwistTag.E6.perm twistedE6CascPairE6) = 0 ∧
      twistedE6CascPairE6 ∉ twistedE6CascPosA3' ∧
      permLattice TwistTag.E6.perm twistedE6CascPairE6 ∉ twistedE6CascPosA3' ∧
      ∀ δ ∈ twistedE6CascPosA3', iform twistedE6CascPairE6 δ = 0 ∧
        iform (permLattice TwistTag.E6.perm twistedE6CascPairE6) δ = 0) ∧
    (∀ δ ∈ twistedE6CascPosA5, δ ∈ twistedE6PosRoots ∧
      ∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → δ l = 0) ∧
    (∀ δ ∈ twistedE6CascPosA3', δ ∈ twistedE6PosRoots) ∧
    (∀ l : Fin TwistTag.E6.tag.rank, l ∈ twistedE6CascJE6) := by
  decide +kernel

theorem twistedE6Unit_of_fixed {θ : Fin TwistTag.E6.tag.rank → ℤ}
    (hθ : permLattice TwistTag.E6.perm θ = θ) : twistedE6Unit θ = [θ] := by
  simp [twistedE6Unit, hθ]

theorem twistedE6Unit_of_not_fixed {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : permLattice TwistTag.E6.perm γ ≠ γ) :
    twistedE6Unit γ = [γ, permLattice TwistTag.E6.perm γ] := by
  simp [twistedE6Unit, hγ]


theorem twistedE6RelX_of_fixed (σ : K →+* K) {θ : Fin TwistTag.E6.tag.rank → ℤ}
    (hθ : permLattice TwistTag.E6.perm θ = θ) (c : K) :
    twistedE6RelX K σ θ c = pinnedX TwistTag.E6.tag K θ c := by
  simp [twistedE6RelX, hθ]

theorem twistedE6RelX_of_not_fixed (σ : K →+* K) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : permLattice TwistTag.E6.perm γ ≠ γ) (c : K) :
    twistedE6RelX K σ γ c = twistedE6PairX σ γ c := by
  simp [twistedE6RelX, hγ]

@[expose] noncomputable def twistedE6PairCentralizer (K : Type) [Field K]
    (γ : Fin TwistTag.E6.tag.rank → ℤ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  ⨅ e : K, (Subgroup.centralizer {pinnedX TwistTag.E6.tag K γ e} ⊓
    Subgroup.centralizer {pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) e})

theorem twistedE6PairCentralizer_comm (σ : K →+* K) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ twistedE6PairCentralizer K γ) (c : K) :
    g * twistedE6PairX σ γ c = twistedE6PairX σ γ c * g := by
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_iInf.1 hg c).1
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_iInf.1 hg (σ c)).2
  rw [twistedE6PairX, ← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

theorem twistedE6LevelRes_cons_fixed {σ : K →+* K} {G G' : Subgroup (ModGL TwistTag.E6.tag K)}
    {P P' : Set (Fin TwistTag.E6.tag.rank → ℤ)} {θ : Fin TwistTag.E6.tag.rank → ℤ} {c₀ : K}
    (hc₀ : c₀ ≠ 0) (hc₀σ : σ c₀ = c₀) (hθρ : permLattice TwistTag.E6.perm θ = θ)
    (hθ : IsRoot TwistTag.E6.tag θ ∧ 0 < height θ) (hθP : θ ∈ P) (hθP'n : θ ∉ P')
    (hθP' : ∀ δ ∈ P', iform θ δ = 0) (hP' : P' ⊆ P) (hG' : G' ≤ G)
    (hcen : ∀ g ∈ G', g * pinnedX TwistTag.E6.tag K θ c₀ = pinnedX TwistTag.E6.tag K θ c₀ * g)
    {ℓ z g₀ : ModGL TwistTag.E6.tag K} (hg₀ : g₀ ∈ G)
    (hg₀C : g₀ ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (he : g₀ * ℓ * g₀⁻¹ = pinnedX TwistTag.E6.tag K θ c₀ * z) (hz : TwistedE6LevelRes K σ G' P' z) :
    TwistedE6LevelRes K σ G P ℓ := by
  have hu := twistedE6Unit_of_fixed hθρ
  refine twistedE6LevelRes_cons hc₀ (fun _ => hc₀σ) (by rw [hu]; exact List.nodup_singleton _)
    (fun β hβ => ?_) (by rw [hu]; exact List.pairwise_singleton _ _) (fun β hβ => ?_) hP' hG'
    (fun g hg => by rw [twistedE6RelX_of_fixed σ hθρ]; exact hcen g hg) hg₀ hg₀C
    (by rw [twistedE6RelX_of_fixed σ hθρ]; exact he) hz
  · rw [hu, List.mem_singleton] at hβ
    subst hβ
    exact ⟨hθ.1, hθ.2, hθP, hθP'n⟩
  · rw [hu, List.mem_singleton] at hβ
    subst hβ
    exact hθP'

theorem twistedE6LevelRes_cons_pair {σ : K →+* K} {G G' : Subgroup (ModGL TwistTag.E6.tag K)}
    {P P' : Set (Fin TwistTag.E6.tag.rank → ℤ)} {γ : Fin TwistTag.E6.tag.rank → ℤ} {c₀ : K}
    (hc₀ : c₀ ≠ 0) (hγρ : permLattice TwistTag.E6.perm γ ≠ γ)
    (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ)
    (hγ' : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm γ) ∧
      0 < height (permLattice TwistTag.E6.perm γ))
    (hγγ : iform γ (permLattice TwistTag.E6.perm γ) = 0)
    (hγP : γ ∈ P ∧ permLattice TwistTag.E6.perm γ ∈ P)
    (hγP'n : γ ∉ P' ∧ permLattice TwistTag.E6.perm γ ∉ P')
    (hγP' : ∀ δ ∈ P', iform γ δ = 0 ∧ iform (permLattice TwistTag.E6.perm γ) δ = 0)
    (hP' : P' ⊆ P) (hG' : G' ≤ G)
    (hcen : ∀ g ∈ G', g * twistedE6PairX σ γ c₀ = twistedE6PairX σ γ c₀ * g)
    {ℓ z g₀ : ModGL TwistTag.E6.tag K} (hg₀ : g₀ ∈ G)
    (hg₀C : g₀ ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (he : g₀ * ℓ * g₀⁻¹ = twistedE6PairX σ γ c₀ * z) (hz : TwistedE6LevelRes K σ G' P' z) :
    TwistedE6LevelRes K σ G P ℓ := by
  have hu := twistedE6Unit_of_not_fixed hγρ
  refine twistedE6LevelRes_cons hc₀ (fun h => absurd h hγρ)
    (by rw [hu]; exact List.nodup_cons.2 ⟨by simpa using Ne.symm hγρ, List.nodup_singleton _⟩)
    (fun β hβ => ?_) (by rw [hu]; exact List.pairwise_pair.2 hγγ) (fun β hβ => ?_) hP' hG'
    (fun g hg => by rw [twistedE6RelX_of_not_fixed σ hγρ]; exact hcen g hg) hg₀ hg₀C
    (by rw [twistedE6RelX_of_not_fixed σ hγρ]; exact he) hz
  · rw [hu] at hβ
    rcases List.mem_pair.1 hβ with rfl | rfl
    · exact ⟨hγ.1, hγ.2, hγP.1, hγP'n.1⟩
    · exact ⟨hγ'.1, hγ'.2, hγP.2, hγP'n.2⟩
  · rw [hu] at hβ
    rcases List.mem_pair.1 hβ with rfl | rfl
    · exact fun δ hδ => (hγP' δ hδ).1
    · exact fun δ hδ => (hγP' δ hδ).2

theorem twistedE6_pinnedX_param_injective {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α ∧ 0 < height α) {a b : K}
    (h : pinnedX TwistTag.E6.tag K α a = pinnedX TwistTag.E6.tag K α b) : a = b :=
  pinnedX_list_prod_injective [α] (List.nodup_singleton α)
    (fun β hβ => by rw [List.mem_singleton.1 hβ]; exact hα) (fun _ => a) (fun _ => b)
    (by simpa using h) α List.mem_cons_self

theorem twistedE6_pinnedX_commute_rootSpan {θ : Fin TwistTag.E6.tag.rank → ℤ}
    (hθ : IsRoot TwistTag.E6.tag θ) {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot TwistTag.E6.tag δ ∧ iform θ δ = 0) (c : K)
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K S) :
    pinnedX TwistTag.E6.tag K θ c * z = z * pinnedX TwistTag.E6.tag K θ c := by
  have hle : rootSpan TwistTag.E6.tag K S ≤
      Subgroup.centralizer {pinnedX TwistTag.E6.tag K θ c} := by
    refine iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (twistedE6_commute_of_iform_eq_zero hθ (hS δ hδ).1 (hS δ hδ).2 c d).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem twistedE6_sq_eq_one_of_conj {G : Type*} [Group G] {A z g ℓ : G} (hA : A * A = 1)
    (hAz : A * z = z * A) (hℓ : ℓ ^ 2 = 1) (he : g * ℓ * g⁻¹ = A * z) : z ^ 2 = 1 := by
  have h1 : (A * z) ^ 2 = 1 := by rw [← he, conj_pow, hℓ, mul_one, mul_inv_cancel]
  calc z ^ 2 = A * A * (z * z) := by rw [hA, one_mul, sq]
    _ = A * (A * z) * z := by group
    _ = A * (z * A) * z := by rw [hAz]
    _ = (A * z) ^ 2 := by rw [sq]; group
    _ = 1 := h1

theorem twistedE6PairX_mul_self [CharP K 2] (σ : K →+* K) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (c : K) :
    twistedE6PairX σ γ c * twistedE6PairX σ γ c = 1 := by
  have hcomm := (commute_pinnedX_permLattice_twistedE6 (K := K) hγ c (σ c)).eq
  rw [twistedE6PairX, show pinnedX TwistTag.E6.tag K γ c *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c) *
      (pinnedX TwistTag.E6.tag K γ c *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c)) =
      pinnedX TwistTag.E6.tag K γ c *
        (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c) *
          pinnedX TwistTag.E6.tag K γ c) *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c) by group, ← hcomm,
    show pinnedX TwistTag.E6.tag K γ c * (pinnedX TwistTag.E6.tag K γ c *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c)) *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c) =
      (pinnedX TwistTag.E6.tag K γ c * pinnedX TwistTag.E6.tag K γ c) *
        (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c)) by group,
    classKill_pinnedX_mul_self, classKill_pinnedX_mul_self, one_mul]

theorem twistedE6PairX_commute_rootSpan (σ : K →+* K) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot TwistTag.E6.tag δ ∧ iform γ δ = 0 ∧
      iform (permLattice TwistTag.E6.perm γ) δ = 0) (c : K)
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K S) :
    twistedE6PairX σ γ c * z = z * twistedE6PairX σ γ c := by
  have h1 := twistedE6_pinnedX_commute_rootSpan hγ (fun δ hδ => ⟨(hS δ hδ).1, (hS δ hδ).2.1⟩)
    c hz
  have h2 := twistedE6_pinnedX_commute_rootSpan (hγ.permLattice TwistTag.E6.cartan_perm)
    (fun δ hδ => ⟨(hS δ hδ).1, (hS δ hδ).2.2⟩) (σ c) hz
  rw [twistedE6PairX, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem twistedE6LevelRes_A4 [CharP K 2] (σ : K →+* K) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ [e6RootA4]})
    (hzΓ : z ∈ twistedFixedGroup TwistTag.E6 K σ) :
    TwistedE6LevelRes K σ ⊥ {δ | δ ∈ [e6RootA4]} z := by
  have hle : rootSpan TwistTag.E6.tag K {δ | δ ∈ [e6RootA4]} ≤
      rootSubgroup TwistTag.E6.tag K e6RootA4 :=
    iSup₂_le fun α hα => by
      rw [Set.mem_ofPred_eq, List.mem_singleton] at hα
      rw [hα]
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 (hle hz)
  have hr := twistedE6CascadeTree_roots
  have hA4 := twistedE6_isRoot_of_mem_posRoots hr.2.1.1
  have hA4ρ : permLattice TwistTag.E6.perm e6RootA4 = e6RootA4 := hr.2.1.2.2.2
  by_cases hd : d = 0
  · rw [hd, pinnedX_zero]
    exact twistedE6LevelRes_one σ ⊥ _
  have hσd : σ d = d := by
    have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hzΓ).2
    rw [twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ hA4.1, hA4ρ] at hF
    exact twistedE6_pinnedX_param_injective hA4 hF
  have hu := twistedE6Unit_of_fixed hA4ρ
  refine ⟨1, one_mem _, one_mem _, [e6RootA4], ⟨?_, ?_, ?_⟩, fun _ => d, ?_, ?_⟩
  · rw [List.flatMap_singleton, hu]
    exact List.nodup_singleton _
  · intro β hβ
    rw [List.flatMap_singleton, hu, List.mem_singleton] at hβ
    subst hβ
    exact ⟨hA4.1, hA4.2, List.mem_singleton_self _⟩
  · rw [List.flatMap_singleton, hu]
    exact List.pairwise_singleton _ _
  · intro γ _
    exact ⟨hd, fun _ => hσd⟩
  · rw [List.map_singleton, List.prod_singleton, twistedE6RelX_of_fixed σ hA4ρ]
    group

theorem twistedE6LevelRes_nil (σ : K →+* K) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ ([] : List (Fin TwistTag.E6.tag.rank → ℤ))}) :
    TwistedE6LevelRes K σ ⊥ {δ | δ ∈ ([] : List (Fin TwistTag.E6.tag.rank → ℤ))} z := by
  have hle : rootSpan TwistTag.E6.tag K
      {δ | δ ∈ ([] : List (Fin TwistTag.E6.tag.rank → ℤ))} ≤ ⊥ :=
    iSup₂_le fun α hα => absurd hα List.not_mem_nil
  rw [Subgroup.mem_bot.1 (hle hz)]
  exact twistedE6LevelRes_one σ ⊥ _

theorem twistedE6LevelRes_A3 [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (hkill : TwistedE6Kill K σ) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSpan TwistTag.E6.tag K
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA3}))
    (hzΓ : z ∈ twistedFixedGroup TwistTag.E6 K σ) (hz2 : z ^ 2 = 1) :
    TwistedE6LevelRes K σ (cascadeConjGroup TwistTag.E6.tag K {j | j ∈ twistedE6CascJA3})
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA3}) z := by
  by_cases h1 : z = 1
  · rw [h1]
    exact twistedE6LevelRes_one σ _ _
  have hr := twistedE6CascadeTree_roots
  obtain ⟨hC1, hC2, hC3, hC4, hC5⟩ := hr.1
  obtain ⟨hA1, hA2, -, -⟩ := hr.2.1
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6⟩ := hr.2.2.1
  obtain ⟨g, hg, hgC, hcase⟩ := twistedE6_level_step hσσ hkill twistedE6CascJA3
    twistedE6CascA3_rho twistedE6CascWordA3 e6CascC e6RootA34 [e6RootA4] [] twistedE6CascA3_word
    twistedE6CascA3_long twistedE6CascA3_short hz hzΓ hz2 h1
  rcases hcase with ⟨c, hc, hσc, z', hz', hz'Γ, he⟩ | ⟨c, hc, z', hz', -, he⟩
  · refine twistedE6LevelRes_cons_fixed (G' := ⊥) (P' := {δ | δ ∈ [e6RootA4]}) hc hσc hC3
      (twistedE6_isRoot_of_mem_posRoots hC1) (twistedE6_mem_parabolic_of_mem hC1 hC2)
      (by simpa using hC4) (fun δ hδ => ?_) (fun δ hδ => ?_) bot_le
      (fun g hg => by rw [Subgroup.mem_bot.1 hg]; group) hg hgC he
      (twistedE6LevelRes_A4 σ hz' hz'Γ)
    · rw [Set.mem_ofPred_eq, List.mem_singleton] at hδ
      rw [hδ]
      exact hC5
    · rw [Set.mem_ofPred_eq, List.mem_singleton] at hδ
      rw [hδ]
      exact twistedE6_mem_parabolic_of_mem hA1 hA2
  · exact twistedE6LevelRes_cons_pair (G' := ⊥)
      (P' := {δ | δ ∈ ([] : List (Fin TwistTag.E6.tag.rank → ℤ))}) hc hP5
      (twistedE6_isRoot_of_mem_posRoots hP1) (twistedE6_isRoot_of_mem_posRoots hP3) hP6
      ⟨twistedE6_mem_parabolic_of_mem hP1 hP2, twistedE6_mem_parabolic_of_mem hP3 hP4⟩
      ⟨List.not_mem_nil, List.not_mem_nil⟩ (fun δ hδ => absurd hδ List.not_mem_nil)
      (fun δ hδ => absurd hδ List.not_mem_nil) bot_le
      (fun g hg => by rw [Subgroup.mem_bot.1 hg]; group) hg hgC he (twistedE6LevelRes_nil σ hz')

theorem twistedE6LevelRes_A5 [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (hkill : TwistedE6Kill K σ) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSpan TwistTag.E6.tag K
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA5}))
    (hzΓ : z ∈ twistedFixedGroup TwistTag.E6 K σ) (hz2 : z ^ 2 = 1) :
    TwistedE6LevelRes K σ (cascadeConjGroup TwistTag.E6.tag K {j | j ∈ twistedE6CascJA5})
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA5}) z := by
  by_cases h1 : z = 1
  · rw [h1]
    exact twistedE6LevelRes_one σ _ _
  have hr := twistedE6CascadeTree_roots
  obtain ⟨hA1, -, hA5s, -⟩ := hr.2.1
  obtain ⟨hR1, hR2, hR3, hR4, hR5⟩ := hr.2.2.2.1
  obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hQ8, hQ9, hQ10⟩ := hr.2.2.2.2.1
  have hPosA3 := hr.2.2.2.2.2.1
  have hJ35 := hr.2.2.2.2.2.2.1
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨g, hg, hgC, hcase⟩ := twistedE6_level_step hσσ hkill twistedE6CascJA5
    twistedE6CascA5_rho twistedE6CascWordA5 e6CascR17 twistedE6CascPairA5 twistedE6CascPosA3
    [e6RootA4] twistedE6CascA5_word twistedE6CascA5_long twistedE6CascA5_short hz hzΓ hz2 h1
  have hJsub : {j | j ∈ twistedE6CascJA3} ⊆ {j | j ∈ twistedE6CascJA5} := fun j hj => hJ35 j hj
  have hR := twistedE6_isRoot_of_mem_posRoots hR1
  have hRperp : ∀ δ ∈ parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA3},
      iform e6CascR17 δ = 0 := fun δ hδ => cascade_iform_eq_zero_of_mem (fun j hj => hR5 j hj) hδ
  rcases hcase with ⟨c, hc, hσc, z', hz', hz'Γ, he⟩ | ⟨c, hc, z', hz', hz'Γ, he⟩
  · have hz'' : z' ∈ rootSpan TwistTag.E6.tag K
        (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA3}) :=
      classDescent_rootSpan_mono (fun δ hδ => twistedE6_mem_parabolic_of_mem (hPosA3 δ hδ).1
        (hPosA3 δ hδ).2) hz'
    have hz'2 : z' ^ 2 = 1 := twistedE6_sq_eq_one_of_conj (classKill_pinnedX_mul_self _ c)
      (twistedE6_pinnedX_commute_rootSpan hR.1 (fun δ hδ => ⟨hδ.1.1, hRperp δ hδ⟩) c hz'') hz2 he
    exact twistedE6LevelRes_cons_fixed
      (G' := cascadeConjGroup TwistTag.E6.tag K {j | j ∈ twistedE6CascJA3})
      (P' := parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA3}) hc hσc hR3 hR
      (twistedE6_mem_parabolic_of_mem hR1 hR2) (fun h => hR4 fun l _ hl => h.1.2 l hl) hRperp
      (twistedE6_parabolic_mono hJsub) (cascadeConjGroup_mono hJsub)
      (fun g hg => Subgroup.mem_centralizer_singleton_iff.1
        (cascadeConjGroup_le_centralizer hτ hR.1 hR.2 (fun j hj => hR5 j hj) c hg))
      hg hgC he (twistedE6LevelRes_A3 hσσ hkill hz'' hz'Γ hz'2)
  · refine twistedE6LevelRes_cons_pair (G' := ⊥) (P' := {δ | δ ∈ [e6RootA4]}) hc hQ5
      (twistedE6_isRoot_of_mem_posRoots hQ1) (twistedE6_isRoot_of_mem_posRoots hQ3) hQ6
      ⟨twistedE6_mem_parabolic_of_mem hQ1 hQ2, twistedE6_mem_parabolic_of_mem hQ3 hQ4⟩
      ⟨by simpa using hQ7, by simpa using hQ8⟩ (fun δ hδ => ?_) (fun δ hδ => ?_) bot_le
      (fun g hg => by rw [Subgroup.mem_bot.1 hg]; group) hg hgC he
      (twistedE6LevelRes_A4 σ hz' hz'Γ)
    · rw [Set.mem_ofPred_eq, List.mem_singleton] at hδ
      rw [hδ]
      exact ⟨hQ9, hQ10⟩
    · rw [Set.mem_ofPred_eq, List.mem_singleton] at hδ
      rw [hδ]
      exact twistedE6_mem_parabolic_of_mem hA1 hA5s

variable (K) in
@[expose] def TwistedE6LevelA3' (σ : K →+* K) : Prop :=
  ∀ z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ twistedE6CascPosA3'},
    z ∈ twistedFixedGroup TwistTag.E6 K σ → z ^ 2 = 1 →
      TwistedE6LevelRes K σ (twistedE6PairCentralizer K twistedE6CascPairE6)
        {δ | δ ∈ twistedE6CascPosA3'} z

theorem twistedE6LevelRes_E6 [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (hkill : TwistedE6Kill K σ) (hA3 : TwistedE6LevelA3' K σ) {ℓ : ModGL TwistTag.E6.tag K}
    (hℓ : ℓ ∈ rootSpan TwistTag.E6.tag K
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJE6}))
    (hℓΓ : ℓ ∈ twistedFixedGroup TwistTag.E6 K σ) (h2 : ℓ ^ 2 = 1) :
    TwistedE6LevelRes K σ ⊤ (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJE6}) ℓ := by
  by_cases h1 : ℓ = 1
  · rw [h1]
    exact twistedE6LevelRes_one σ _ _
  have hr := twistedE6CascadeTree_roots
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hr.2.2.2.2.2.2.2.1
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6, hG7⟩ := hr.2.2.2.2.2.2.2.2.1
  have hPosA5 := hr.2.2.2.2.2.2.2.2.2.1
  have hPosA3' := hr.2.2.2.2.2.2.2.2.2.2.1
  have hall := hr.2.2.2.2.2.2.2.2.2.2.2
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  have hsupp : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ,
      ∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJE6 → δ l = 0 :=
    fun δ l _ hl => absurd (hall l) hl
  obtain ⟨g, -, hgC, hcase⟩ := twistedE6_level_step hσσ hkill twistedE6CascJE6
    twistedE6CascE6_rho twistedE6CascWordE6 e6HighestRoot twistedE6CascPairE6 twistedE6CascPosA5
    twistedE6CascPosA3' twistedE6CascE6_word twistedE6CascE6_long twistedE6CascE6_short hℓ hℓΓ h2 h1
  have hJsub : {j | j ∈ twistedE6CascJA5} ⊆ {j | j ∈ twistedE6CascJE6} := fun j _ => hall j
  have hH := twistedE6_isRoot_of_mem_posRoots hH1
  have hHperp : ∀ δ ∈ parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA5},
      iform e6HighestRoot δ = 0 :=
    fun δ hδ => cascade_iform_eq_zero_of_mem (fun j hj => hH4 j hj) hδ
  rcases hcase with ⟨c, hc, hσc, z', hz', hz'Γ, he⟩ | ⟨c, hc, z', hz', hz'Γ, he⟩
  · have hz'' : z' ∈ rootSpan TwistTag.E6.tag K
        (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA5}) :=
      classDescent_rootSpan_mono (fun δ hδ => twistedE6_mem_parabolic_of_mem (hPosA5 δ hδ).1
        (hPosA5 δ hδ).2) hz'
    have hz'2 : z' ^ 2 = 1 := twistedE6_sq_eq_one_of_conj (classKill_pinnedX_mul_self _ c)
      (twistedE6_pinnedX_commute_rootSpan hH.1 (fun δ hδ => ⟨hδ.1.1, hHperp δ hδ⟩) c hz'') h2 he
    exact twistedE6LevelRes_cons_fixed
      (G' := cascadeConjGroup TwistTag.E6.tag K {j | j ∈ twistedE6CascJA5})
      (P' := parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA5}) hc hσc hH2 hH
      (twistedE6_mem_parabolic_of_mem hH1 (hsupp _)) (fun h => hH3 fun l _ hl => h.1.2 l hl) hHperp
      (twistedE6_parabolic_mono hJsub) le_top
      (fun g hg => Subgroup.mem_centralizer_singleton_iff.1
        (cascadeConjGroup_le_centralizer hτ hH.1 hH.2 (fun j hj => hH4 j hj) c hg))
      (Subgroup.mem_top g) hgC he (twistedE6LevelRes_A5 hσσ hkill hz'' hz'Γ hz'2)
  · have hG := twistedE6_isRoot_of_mem_posRoots hG1
    have hz'2 : z' ^ 2 = 1 := twistedE6_sq_eq_one_of_conj (twistedE6PairX_mul_self σ hG.1 c)
      (twistedE6PairX_commute_rootSpan σ hG.1 (fun δ hδ => ⟨(twistedE6_isRoot_of_mem_posRoots
        (hPosA3' δ hδ)).1, (hG7 δ hδ).1, (hG7 δ hδ).2⟩) c hz') h2 he
    exact twistedE6LevelRes_cons_pair (G' := twistedE6PairCentralizer K twistedE6CascPairE6)
      (P' := {δ | δ ∈ twistedE6CascPosA3'}) hc hG3 hG (twistedE6_isRoot_of_mem_posRoots hG2) hG4
      ⟨twistedE6_mem_parabolic_of_mem hG1 (hsupp _), twistedE6_mem_parabolic_of_mem hG2 (hsupp _)⟩
      ⟨hG5, hG6⟩ hG7 (fun δ hδ => twistedE6_mem_parabolic_of_mem (hPosA3' δ hδ) (hsupp _)) le_top
      (fun g hg => twistedE6PairCentralizer_comm σ hg c) (Subgroup.mem_top g) hgC he
      (hA3 z' hz' hz'Γ hz'2)

end CFSG.SeitzReduction
