module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Perf
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinBase
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinCoords
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinExport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open scoped Pointwise

set_option linter.unusedSectionVars false


section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]

theorem d5_fixedTorus_le_orbitGroupC (D : GenFixedRootDatum Tag.E6 p₀ k M)
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (w : WeylGroup Tag.E6) (Jf : Finset (Fin Tag.E6.rank))
    (hΨ : Ψ = (fun α => w • α) '' parabolicRoots Tag.E6 (↑Jf : Set (Fin Tag.E6.rank)))
    (hΔ : simpleRoots Ψ = Jf.image fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
    (hν : ∀ j₀ ∈ Jf, ∃ ν : Fin Tag.E6.rank → ℤ, ∀ j ∈ Jf,
      ∑ l, Tag.E6.cartan j l * ν l = if j = j₀ then 1 else 0)
    (hDs : D.simpleRootsJ = ((simpleRoots Ψ : Finset (Fin Tag.E6.rank → ℤ)) :
      Set (Fin Tag.E6.rank → ℤ)))
    (hDt : D.torusJ = rootSpan Tag.E6 k Ψ ⊓ torusGroup Tag.E6 k) :
    D.fixedTorus ≤ D.orbitGroupC := by
  refine fixedTorus_le_orbitGroupC_of_coords D
    (Jf.image fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ?_ ?_ ?_
  · rw [hDs, hΔ]
  · intro t ht
    rw [hDt, inf_comm, hΨ] at ht
    exact torus_coords_of_conj w Jf ht
  · intro c c' h β hβ
    exact coords_unique_of_conj w Jf hν h hβ

theorem fixedGroup_eq_orbitGroupC_of_fixedTorus (D : GenFixedRootDatum τ p₀ k M)
    (h : D.fixedTorus ≤ D.orbitGroupC) : D.fixedGroup = D.orbitGroupC := by
  refine le_antisymm (fun g hg => ?_) D.orbitGroupC_le_fixedGroup
  have hg' : g ∈ (D.fixedGroup : Set (adjointGroup τ k)) := hg
  rw [D.coe_fixedGroup_eq_mul, Set.mem_mul] at hg'
  obtain ⟨t, ht, c, hc, rfl⟩ := hg'
  exact mul_mem (h ht) hc

theorem commutator_eq_self_of_map {G : Type*} [Group G] (P Q : Subgroup G) (φ : G →* G)
    (hφ : Function.Injective φ) (hmap : P.map φ = Q) (hQ : ⁅Q, Q⁆ = Q) : ⁅P, P⁆ = P := by
  apply Subgroup.map_injective hφ
  rw [Subgroup.map_commutator, hmap, hQ]

end Datum

section Main

theorem d5_fixedSpinPerfect : D5FixedSpinPerfect := by
  intro L _ _ p₀ S Fr hFr hΦ h3 h3q _hq2 a hT hap hk
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  obtain ⟨α, hα⟩ : (kernelRoots (rootCharHom a)).Nonempty := by
    rw [← Set.ncard_pos hfin, hk]
    norm_num
  let i : KernelComponent (rootCharHom a) := ⟦⟨α, hα⟩⟧
  obtain ⟨u, hu, hρ⟩ := exists_rho_neg_weyl_of_conn S hFr hΦ hT hap h3q (by rw [hk]; simp)
  obtain ⟨v₀, C, hC, hΨ₀, hn, hrk⟩ := d5_class_data h3 hap hk i
  have hΨk : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    Set.eq_of_subset_of_ncard_le (fun γ hγ => hγ.1) (by rw [hk, hn]) hfin
  have hu' : u ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
      ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ} :=
    kernelReflectionGroup_le_closure (by rw [hΨk]) hu
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hΨk] at hγ ⊢
    obtain ⟨hγr, hγ1⟩ := hγ
    refine ⟨(S.frob.isRoot_iff γ).2 hγr, ?_⟩
    have h1 : rootChar a γ = 1 := hγ1
    have h2 := S.frob.rootChar_eq a hT γ hγr
    change rootChar a (S.ρ γ) = 1
    rw [h2, h1, one_pow]
  have hlen : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one (hΨk ▸ hfin) hstab
  have hno := not_exists_neg_D5 hC v₀
  rw [← hΨ₀] at hno
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD := by
    classical
    unfold twistKind
    rw [hlen]
    have hni : ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : _ → _)^[1]) := by
      rw [Function.iterate_one]
      exact not_twistInner_of_neg hu' (fun γ hγ => hρ γ (hΨk ▸ hγ).1) hno
    rw [if_neg hni, if_neg (by rw [hrk, hn]; omega),
      if_pos ⟨by rw [hrk]; omega, by rw [hrk, hn]⟩]
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hperf, hDs, hDt, hε, hmap⟩ :=
    exists_twoD_export_fixed S (Or.inr (Or.inl rfl)) hT i hkind hrk.symm.le
  haveI := hr
  haveI := hchar
  have hmcard : m = 5 := by
    have h1 : Fintype.card (simpleRoots (componentRoots (rootCharHom a) i)) = m := by
      rw [Fintype.card_congr ε, Fintype.card_fin]
    rw [Fintype.card_coe, ← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card
      (isRootComponent_componentRoots i), hrk] at h1
    exact h1.symm
  subst hmcard
  obtain ⟨v, J, hJ, hΨv⟩ := d5_position h3 hap hk
  have hΨv' : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.E6 J := by
    rw [hΨk]
    exact hΨv
  obtain ⟨w, Jf, hw1, hw2, hν⟩ := d5_base_form (isRootComponent_componentRoots i) hJ hΨv' ε hε
  have hFT : D.fixedTorus ≤ D.orbitGroupC := d5_fixedTorus_le_orbitGroupC D w Jf hw1 hw2 hν hDs hDt
  have hfix : D.fixedGroup = D.orbitGroupC := fixedGroup_eq_orbitGroupC_of_fixedTorus D hFT
  have hfg : D.fixedGroup.map (adjointGroup Tag.E6 L).subtype = D.orbitGroup := by
    rw [hfix]
    change (D.orbitGroup.subgroupOf (adjointGroup Tag.E6 L)).map
      (adjointGroup Tag.E6 L).subtype = _
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 D.orbitGroup_le_adjointGroup
  rw [← hΨk]
  exact commutator_eq_self_of_map _ D.orbitGroup (MulAut.conj z⁻¹).toMonoidHom
    (MulAut.conj z⁻¹).injective (hmap.trans hfg) (Subgroup.isPerfect_iff.mp hperf)

end Main

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
