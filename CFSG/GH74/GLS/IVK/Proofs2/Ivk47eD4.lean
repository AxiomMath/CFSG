module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exp_rootSpan_orbit {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α) :
    ∀ x ∈ rootSpan TwistTag.D4.tag K
      (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)), x ^ p = 1 := by
  set O : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
    (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) with hO
  have hrootsO : ∀ β ∈ O, IsRoot TwistTag.D4.tag β := fun β hβ =>
    TwistTag.D4.isRoot_of_mem_diagramOrbit hα hβ
  have hcomm : ∀ β ∈ O, ∀ γ ∈ O, ∀ x ∈ rootSubgroup TwistTag.D4.tag K β,
      ∀ y ∈ rootSubgroup TwistTag.D4.tag K γ, x * y = y * x := by
    intro β hβ γ hγ x hx y hy
    by_cases hβγ : β = γ
    · subst hβγ
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · exact (simply_laced_orthogonal_root_commutation TwistTag.D4.tag (Or.inl rfl)).2 K β γ
        (hrootsO β hβ) (hrootsO γ hγ)
        ((diagram_root_orbit_reduction TwistTag.D4).2.2.1 α hα β hβ γ hγ hβγ) x hx y hy
  have hexp : ∀ β ∈ O, ∀ y ∈ rootSubgroup TwistTag.D4.tag K β, y ^ p = 1 := by
    intro β _ y hy
    by_cases h1 : y = 1
    · rw [h1, one_pow]
    · rw [← orderOf_eq_of_mem_rootSubgroup hy h1]
      exact pow_orderOf_eq_one _
  have hcent : ∀ x : ModGL TwistTag.D4.tag K,
      (∀ β ∈ O, ∀ y ∈ rootSubgroup TwistTag.D4.tag K β, x * y = y * x) →
        ∀ y ∈ rootSpan TwistTag.D4.tag K O, x * y = y * x := by
    intro x hx y hy
    have hle : rootSpan TwistTag.D4.tag K O ≤ Subgroup.centralizer {x} :=
      iSup₂_le fun β hβ y hy => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hx β hβ y hy).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  intro x hx
  have key : x ^ p = 1 ∧ ∀ β ∈ O, ∀ z ∈ rootSubgroup TwistTag.D4.tag K β, x * z = z * x := by
    refine Subgroup.iSup_induction' (C := fun x _ => x ^ p = 1 ∧
      ∀ β ∈ O, ∀ z ∈ rootSubgroup TwistTag.D4.tag K β, x * z = z * x)
      (fun α' => ⨆ (_ : α' ∈ O), rootSubgroup TwistTag.D4.tag K α') ?_ ?_ ?_ hx
    · intro α' x hx
      by_cases h : α' ∈ O
      · rw [iSup_pos h] at hx
        exact ⟨hexp α' h x hx, fun β hβ y hy => hcomm α' h β hβ x hx y hy⟩
      · rw [iSup_neg h, Subgroup.mem_bot] at hx
        subst hx
        exact ⟨one_pow p, fun β _ y _ => by rw [one_mul, mul_one]⟩
    · exact ⟨one_pow p, fun β _ y _ => by rw [one_mul, mul_one]⟩
    · intro x y hx hy ihx ihy
      have hxy : x * y = y * x := hcent x ihx.2 y hy
      refine ⟨?_, fun β hβ z hz => ?_⟩
      · rw [(show Commute x y from hxy).mul_pow, ihx.1, ihy.1, one_mul]
      · rw [mul_assoc, ihy.2 β hβ z hz, ← mul_assoc, ihx.2 β hβ z hz, mul_assoc]
  exact key.1

theorem omegaGen_graphFixedPosUnipotent {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (σ : K ≃+* K) : OmegaGen p (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
  unfold OmegaGen
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_posOrbits TwistTag.D4
  have hSρ : ∀ α ∈ {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α},
      permLattice TwistTag.D4.perm α ∈
        {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α} :=
    fun α hα => ⟨hα.1.permLattice TwistTag.D4.cartan_perm, by
      rw [height_permLattice]
      exact hα.2⟩
  have hclosed : ∀ α ∈ {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α},
      ∀ β ∈ {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α},
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.D4.tag (a • α + b • β) →
        a • α + b • β ∈
          {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α} :=
    fun α hα β hβ a b ha hb hr => ⟨hr, by
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      rw [height_nsmul_add_nsmul]
      nlinarith [hα.2, hβ.2]⟩
  have hbij := bijOn_prod_graphFixed (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) σ.surjective
    (S := {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α})
    (fun α hα => hα) hSρ hclosed O hO hrange
  intro g hg
  obtain ⟨u, -, rfl⟩ := hbij.surjOn hg
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ Set.range O := Set.mem_range_self j
  rw [hrange] at hOj
  obtain ⟨⟨α, hα, hαO⟩, hsub⟩ := hOj
  have hu := (u j).2
  refine Subgroup.subset_closure ⟨⟨?_, hu.2⟩, ?_⟩
  · exact rootSpan_mono hsub hu.1
  · have h1 := exp_rootSpan_orbit (K := K) (p := p) hα (u j : ModGL TwistTag.D4.tag K)
      (by rw [hαO]; exact hu.1)
    exact h1

theorem sylow_D4 {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hmodel : TwistedChevalleyModel K .D4 (p ^ n)) (P : Sylow p K) : OmegaGen p (P : Subgroup K) := by
  obtain ⟨F, hFfield, hFfin, hFcard, σ, hσ, ⟨e⟩⟩ := hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h1 : Nat.card F = 1 := by simpa [TwistTag.order] using hFcard
    have := Finite.one_lt_card (α := F)
    omega
  have hFcard' : Nat.card F = p ^ (n * 3) := by
    rw [hFcard, ← pow_mul]
    rfl
  have hcharF : CharP F p := charP_of_natCard_eq_pow hp hFcard'
  have hσinj : Function.Injective σ := σ.injective
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective hσinj
  let σ' : F ≃+* F := RingEquiv.ofBijective σ ⟨hσinj, hσsurj⟩
  have hσ'rh : σ'.toRingHom = σ := rfl
  obtain ⟨-, -, hperf, -, -⟩ :=
    finite_fixed_root_group_perfect (p := p) (f := n) TwistTag.D4 hp hn F hFcard σ hσ
  let C₀ := graphFixedRootGroup TwistTag.D4 F σ
  let π : ↥C₀ →* K :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.D4 F σ, twistedFixedGroup TwistTag.D4 F σ⁆)).comp
      (MulEquiv.subgroupCongr hperf.symm).toMonoidHom)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (MulEquiv.subgroupCongr hperf.symm).surjective)
  have hUC : graphFixedPosUnipotent TwistTag.D4 F σ ≤ C₀ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 F σ
  have : Finite ↥C₀ := by
    have := finite_modGL (τ := TwistTag.D4.tag) (K := F)
    exact Finite.of_injective (Subgroup.subtype C₀) (Subgroup.subtype_injective C₀)
  have hUp := isPGroup_graphFixedPosUnipotent_subgroupOf (K := F) (σ := σ) (t := TwistTag.D4) p
  have hUi := not_dvd_index_graphFixedPosUnipotent (K := F) (σ := σ) (t := TwistTag.D4) p hσsurj
  let PU : Sylow p ↥C₀ := hUp.toSylow hUi
  have hPU : (PU : Subgroup ↥C₀) = (graphFixedPosUnipotent TwistTag.D4 F σ).subgroupOf C₀ :=
    IsPGroup.toSylow_coe hUp hUi
  let Q : Sylow p K := Sylow.mapSurjective (f := π) hπ PU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  have hP : (P : Subgroup K) =
      (((graphFixedPosUnipotent TwistTag.D4 F σ).subgroupOf C₀).map π).map
        (MulAut.conj g).toMonoidHom := by
    have h1 : (P : Subgroup K) = ((PU : Subgroup ↥C₀).map π).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rfl
    rw [h1, hPU]
  rw [hP, omegaGen_map_iff _ (MulAut.conj g).injective]
  refine omegaGen_map π ?_
  rw [← omegaGen_map_iff C₀.subtype C₀.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hUC]
  exact omegaGen_graphFixedPosUnipotent σ'

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47
