module

public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSExact

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
  CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped MatrixGroups


theorem exists_twistedA_of_statedClassicalModel_PSU {G : Type} [Group G] {m p f : ℕ}
    (h : StatedClassicalModel G .PSU (m + 1) p f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA m q).Valid), q.p = p ∧ q.exponent = f ∧
      Nonempty (G ≃* (CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hv := CFSG.ClassicalModels.unitaryCatalog_index_valid (m + 1) p f hadm
  let _ : Fact p.Prime := ⟨hp⟩
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin (m + 1)) φ) (glCongr_statedSU φ (m + 1) (p ^ f))
    (glCongr_statedScalars φ)
  have hv' : (LieTypeIndex.twistedA m q).Valid := by simpa using hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv'
  exact ⟨q, hv', rfl, rfl, ⟨(e.trans e1).trans eT.symm⟩⟩


theorem isLieQuot_of_twistedA_model {G : Type} [Group G] {m p f : ℕ}
    (h : StatedClassicalModel (G ⧸ Subgroup.center G) .PSU (m + 1) p f)
    (P : LieTypeIndex → Prop) (hP : ∀ q : PrimePower, q.p = p → q.exponent = f →
      P (.twistedA m q)) : IsLieQuot G P := by
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ := exists_twistedA_of_statedClassicalModel_PSU h
  exact ⟨⟨.twistedA m q, hv⟩, hP q hqp hqf, ⟨e⟩⟩

section Model


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem rationalComponent_suN_model (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hνQ : (ν, r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))) ≠ (3, 2)) :
    StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i))
      .PSU ν r (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfin, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have hCperf : Group.IsPerfect
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC hνQ).1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hr.pos _) 2).ne')
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := ↥F) (p := r) (f := e * s) hFcard hν hνQ
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hCperf.commutator_eq_top g hgsurj hgker
  let e2 := QuotientGroup.congr (Subgroup.center (StatedSU ν (r ^ (e * s)) ↥F))
    (Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)))
    eC (Subgroup.map_center_eq eC)
  let e3 := QuotientGroup.quotientMulEquivOfEq hZ
  exact ⟨⟨hr, hes, hν, hνQ⟩, ↥F, inferInstance, inferInstance, hFcard,
    ⟨(e1.symm.trans e2.symm).trans e3⟩⟩

end Model

end KSExact

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
