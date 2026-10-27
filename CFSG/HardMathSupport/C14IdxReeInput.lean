module

public import CFSG.HardMathSupport.C14IdxReeRetwist
public import CFSG.HardMathSupport.C14IdxReeTorusDecomp
public import CFSG.HardMathSupport.C14IdxReeTorusFixed
public import CFSG.HardMathSupport.C14IdxReeTorusOrbits
public import CFSG.HardMathSupport.C14IdxFrobInput

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


theorem idxConclusion_of_reePinned
    {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} {p : ℕ} {a : ι → Fin ReeTag.F4.tag.rank → Lˣ}
    {a₀ : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (familyKernel a) (familyKernel a))
    (hΨp : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (posRoots (familyKernel a))
      (posRoots (familyKernel a)))
    {σ : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hσ : ∀ g, σ g = nrep ReeTag.F4.tag L w * F g * (nrep ReeTag.F4.tag L w)⁻¹)
    (hfin : Finite ↥(σ.eqLocus (MonoidHom.id _))) (hp : p.Prime)
    (hsat : CorootPSaturated p (familyKernel a)) : IdxConclusion p a σ := by
  classical
  have hK : kernelRoots (familyChar a) = familyKernel a := kernelRoots_familyChar a
  have hU : unionRoots (familyChar a) Set.univ = familyKernel a :=
    (unionRoots_univ_eq_kernelRoots _).trans hK
  have hΨ' : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (kernelRoots (familyChar a)) (kernelRoots (familyChar a)) := hK.symm ▸ hΨ
  have hΨp' : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (posRoots (kernelRoots (familyChar a))) (posRoots (kernelRoots (familyChar a))) :=
    hK.symm ▸ hΨp
  have hΔ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (simpleRoots (kernelRoots (familyChar a)) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots (familyChar a)) : Set (Fin ReeTag.F4.tag.rank → ℤ)) :=
    bijOn_simpleRoots_of_reeTwist (χ := familyChar a) hΨ' hΨp'
  have hTp : ∀ t ∈ unionTorus L (familyChar a) Set.univ,
      t ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) →
      ∀ n : ℕ, t ^ p ^ n = 1 →
      t ∈ Subgroup.closure {x : ModGL ReeTag.F4.tag L |
        x ∈ unionRootSpan L (familyChar a) Set.univ ∧
          x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
            ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    intro t ht hσt n hn
    obtain ⟨c, rfl, hc⟩ := exists_coordTuple_of_reeTwist_fixed (χ := familyChar a) hF hΔ hp
      (hK.symm ▸ hsat) ht hσt hn
    exact rootDiagUnit_coordTuple_mem_closure_of_reeSimpleRoots (χ := familyChar a) hF
      hΨ' hΔ c hc
  have hI5 : ∀ s ∈ unionRootSpan L (familyChar a) Set.univ,
      s ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) →
      ∃ t ∈ unionTorus L (familyChar a) Set.univ,
        t ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
        t⁻¹ * s ∈ Subgroup.closure {x : ModGL ReeTag.F4.tag L |
          x ∈ unionRootSpan L (familyChar a) Set.univ ∧
            x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
              ∃ k : ℕ, x ^ 2 ^ k = 1} := fun s hs hσs =>
    exists_reeTwistFixed_torus_mul_mem_closure (χ := familyChar a) hF
      (hK.symm ▸ hΨ) (hK.symm ▸ hΨp) hs hσs
  have hS : (famS a).map (adjointGroup ReeTag.F4.tag L).subtype =
      unionRootSpan L (familyChar a) Set.univ := by
    rw [map_famS_subtype_eq_rootSpan, unionRootSpan, hU]
  let S' : Subgroup (ModGL ReeTag.F4.tag L) := unionRootSpan L (familyChar a) Set.univ
  have hS' : S' = (famS a).map (adjointGroup ReeTag.F4.tag L).subtype := hS.symm
  let nw : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L w
  let H : Subgroup (adjointGroup ReeTag.F4.tag L) := famS a ⊓ σ.eqLocus (MonoidHom.id _)
  let E : Set (adjointGroup ReeTag.F4.tag L) := {x | x ∈ H ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  let D : Subgroup (adjointGroup ReeTag.F4.tag L) := Subgroup.closure E
  let D' : Subgroup (ModGL ReeTag.F4.tag L) :=
    Subgroup.closure {x : ModGL ReeTag.F4.tag L | x ∈ S' ∧
      x ∈ twistedFixed F nw ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  let T : Subgroup (adjointGroup ReeTag.F4.tag L) :=
    (unionTorus L (familyChar a) Set.univ ⊓ twistedFixed F nw).comap
      (adjointGroup ReeTag.F4.tag L).subtype
  have hι : Function.Injective (adjointGroup ReeTag.F4.tag L).subtype :=
    Subgroup.subtype_injective _
  have hσ' : ∀ y : adjointGroup ReeTag.F4.tag L,
      (σ y : ModGL ReeTag.F4.tag L) = nw * Fext F (y : ModGL ReeTag.F4.tag L) * nw⁻¹ := by
    intro y
    rw [Fext_of_mem F y.2, hσ y]
    rfl
  have hEimage : (adjointGroup ReeTag.F4.tag L).subtype '' E =
      {x : ModGL ReeTag.F4.tag L | x ∈ S' ∧ x ∈ twistedFixed F nw ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hS']
        exact Subgroup.mem_map_of_mem _ hy.1.1
      · rw [mem_twistedFixed]
        refine ⟨(y : adjointGroup ReeTag.F4.tag L).2, ?_⟩
        have hy' : σ y = y := by simpa using hy.1.2
        calc nw * Fext F (y : ModGL ReeTag.F4.tag L) * nw⁻¹ =
              (σ y : ModGL ReeTag.F4.tag L) := (hσ' y).symm
          _ = (y : ModGL ReeTag.F4.tag L) := by rw [hy']
      · obtain ⟨k, hk⟩ := hy.2
        exact ⟨k, by simpa using congrArg (adjointGroup ReeTag.F4.tag L).subtype hk⟩
    · rintro ⟨hxS, hxT, hxk⟩
      rw [hS'] at hxS
      rcases Subgroup.mem_map.mp hxS with ⟨y, hyS, hyx⟩
      have hyx' : ((y : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) = x := hyx
      refine ⟨y, ?_, hyx⟩
      refine ⟨Subgroup.mem_inf.mpr ⟨hyS, ?_⟩, ?_⟩
      · apply (adjointGroup ReeTag.F4.tag L).subtype_injective
        calc (σ y : ModGL ReeTag.F4.tag L) =
              nw * Fext F (y : ModGL ReeTag.F4.tag L) * nw⁻¹ := hσ' y
          _ = x := by rw [hyx']; exact hxT.2
          _ = (y : ModGL ReeTag.F4.tag L) := hyx'.symm
      · obtain ⟨k, hk⟩ := hxk
        refine ⟨k, ?_⟩
        apply (adjointGroup ReeTag.F4.tag L).subtype_injective
        rw [map_pow, hyx, hk]
        simp
  have hDmap : D.map (adjointGroup ReeTag.F4.tag L).subtype = D' := by
    change (Subgroup.closure E).map (adjointGroup ReeTag.F4.tag L).subtype =
      Subgroup.closure {x : ModGL ReeTag.F4.tag L | x ∈ S' ∧ x ∈ twistedFixed F nw ∧
        ∃ k : ℕ, x ^ 2 ^ k = 1}
    rw [MonoidHom.map_closure, hEimage]
  have hHfin : Finite H := by
    have : Finite ↥(σ.eqLocus (MonoidHom.id _)) := hfin
    have hEq : (σ.eqLocus (MonoidHom.id _) : Set (adjointGroup ReeTag.F4.tag L)).Finite :=
      Set.toFinite _
    exact (hEq.subset (fun x hx => hx.2)).to_subtype
  have : Finite H := hHfin
  have hDH : D ≤ H := by
    change Subgroup.closure E ≤ H
    exact (Subgroup.closure_le H).2 (fun x hx => hx.1)
  have hnorm : (D.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDH]
    change H ≤ Subgroup.normalizer (Subgroup.closure E)
    rw [Subgroup.le_normalizer_closure_iff]
    intro h hh x hx
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (famS a).mul_mem ((famS a).mul_mem hh.1 hx.1.1) ((famS a).inv_mem hh.1)
      · show σ (h * x * h⁻¹) = h * x * h⁻¹
        have hh' : σ h = h := by simpa using hh.2
        have hx' : σ x = x := by simpa using hx.1.2
        rw [map_mul, map_mul, map_inv, hh', hx']
    · obtain ⟨k, hk⟩ := hx.2
      exact ⟨k, by rw [conj_pow, hk]; simp⟩
  have : (D.subgroupOf H).Normal := hnorm
  have hHT : ∀ h ∈ H, ∃ t ∈ T, t⁻¹ * h ∈ D := by
    intro h hh
    have hhS : ((h : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈ S' := by
      rw [hS']
      exact Subgroup.mem_map_of_mem _ hh.1
    have hhσ : ((h : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
        twistedFixed F nw := by
      rw [mem_twistedFixed]
      refine ⟨(h : adjointGroup ReeTag.F4.tag L).2, ?_⟩
      have hh' : σ h = h := by simpa using hh.2
      calc nw * Fext F (h : ModGL ReeTag.F4.tag L) * nw⁻¹ =
            (σ h : ModGL ReeTag.F4.tag L) := (hσ' h).symm
        _ = (h : ModGL ReeTag.F4.tag L) := by rw [hh']
    obtain ⟨t, htT, htfix, htd⟩ := exists_reeTwistFixed_torus_mul_mem_closure
      (χ := familyChar a) hF (hK.symm ▸ hΨ) (hK.symm ▸ hΨp) hhS hhσ
    have htS : t ∈ S' := unionTorus_le_unionRootSpan htT
    rw [hS'] at htS
    rcases Subgroup.mem_map.mp htS with ⟨tA, htAfamS, htAeq⟩
    refine ⟨tA, ?_, ?_⟩
    · rw [Subgroup.mem_comap]
      rw [htAeq]
      exact Subgroup.mem_inf.mpr ⟨htT, htfix⟩
    · have hmemD' : (adjointGroup ReeTag.F4.tag L).subtype (tA⁻¹ * h) ∈ D' := by
        rw [map_mul, map_inv, htAeq]
        exact htd
      rw [← hDmap] at hmemD'
      exact (Subgroup.mem_map_iff_mem hι).mp hmemD'
  have hT : ∀ t ∈ T, ∀ n : ℕ, t ^ p ^ n = 1 → t ∈ D := by
    intro t ht n hn
    rw [Subgroup.mem_comap] at ht
    obtain ⟨htTorus, htfix⟩ := Subgroup.mem_inf.mp ht
    have hn' : ((adjointGroup ReeTag.F4.tag L).subtype t) ^ p ^ n = 1 := by
      rw [← map_pow, hn, map_one]
    have hmemD' : (adjointGroup ReeTag.F4.tag L).subtype t ∈ D' :=
      hTp _ htTorus htfix n hn'
    rw [← hDmap] at hmemD'
    exact (Subgroup.mem_map_iff_mem hι).mp hmemD'
  have hnotdvd : ¬ p ∣ (D.subgroupOf H).index :=
    not_dvd_index_of_pow_eq_one_mem hp hDH hHT hT
  simpa [IdxConclusion, H, D, E] using hnotdvd

theorem excIdxReeInput_holds :
    ExcIdxReeInput := by
  intro L _ _ _ ι p hp hp2 a hf a₀ h F' hF' hM hfin hsat
  obtain ⟨C, hC⟩ := exists_reeClosure_reeEndo (L := L) hf a₀
  let F : MulAut (adjointGroup ReeTag.F4.tag L) := C.Φ * C.Fr ^ a₀
  have hF : IsReeFrob a₀ F := isReeFrob_of_reeEndo (F := F) hC
  obtain ⟨m, hm, w, hpin, hΨ, hΨp⟩ := exists_pinned_reeRetwist (hf := hf) hF' hM
  let σ : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L :=
    (MulAut.conj m⁻¹).toMonoidHom.comp (F'.comp (MulAut.conj m).toMonoidHom)
  have hσg : ∀ g, σ g = m⁻¹ * F' (m * g * m⁻¹) * m := fun g => by
    simp [σ, MulAut.conj_apply]
  refine idxConclusion_of_conj hm hσg ?_
  have hfin' : Finite ↥(σ.eqLocus (MonoidHom.id _)) := by
    have hmem : ∀ x : σ.eqLocus (MonoidHom.id _),
        F' (m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹) =
          m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹ := by
      intro x
      have hx : σ (x : adjointGroup ReeTag.F4.tag L) =
          (x : adjointGroup ReeTag.F4.tag L) := x.2
      rw [hσg] at hx
      calc F' (m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹)
          = m * (m⁻¹ * F' (m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹) * m) * m⁻¹ := by
            group
        _ = m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹ := by rw [hx]
    let f : σ.eqLocus (MonoidHom.id _) → F'.eqLocus (MonoidHom.id _) :=
      fun x => ⟨m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹, hmem x⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      calc (x : adjointGroup ReeTag.F4.tag L)
          = m⁻¹ * (m * (x : adjointGroup ReeTag.F4.tag L) * m⁻¹) * m := by group
        _ = m⁻¹ * (m * (y : adjointGroup ReeTag.F4.tag L) * m⁻¹) * m := by
              simpa [f] using congrArg (fun z : F'.eqLocus (MonoidHom.id _) =>
                m⁻¹ * (z : adjointGroup ReeTag.F4.tag L) * m) hxy
        _ = (y : adjointGroup ReeTag.F4.tag L) := by group
    exact Finite.of_injective f hf
  have hσ : ∀ g, σ g = nrep ReeTag.F4.tag L w * F g * (nrep ReeTag.F4.tag L w)⁻¹ := by
    intro g
    rw [hσg, hpin g, hC g]
  exact idxConclusion_of_reePinned (σ := σ) hF hΨ hΨp hσ hfin' hp hsat

end CFSG.HardMathSupport.C14Idx
