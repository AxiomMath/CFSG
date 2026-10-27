module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Sign

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Character

variable {K : Type} [Field K]

theorem twistedE6_rootChar_nsmul {τ : Tag} (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) (c : ℕ) :
    rootChar a (c • v) = rootChar a v ^ c := by
  induction c with
  | zero => simp [rootChar_zero]
  | succ c ih => rw [succ_nsmul, rootChar_add, ih, pow_succ]

theorem twistedE6_rootChar_neg {τ : Tag} (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]

end Character

section Phi

variable (p e : ℕ) [Fact p.Prime]

theorem twistedE6Phi_commute_of_rootChar
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    {β : Fin (Tag.rank .F4) → ℤ} (hb : rootChar b β = 1) {g : twistedE6Group p e}
    (hg : g ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) β) :
    twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g *
        rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
        twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g := by
  have hgen : ∀ α : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 α →
      (∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum orbitMap α = c • β) →
      e6Data_valid.rootGroup (GaloisField p (2 * e)) α ≤ (Subgroup.centralizer
        {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
          (twistedE6PhiAmbient p e) := by
    intro α hα hc g' hg'
    obtain ⟨c, -, hαc⟩ := hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    refine twistedE6PhiAmbient_rootGroup_commute p e hα ?_ hg'
    have h := rootChar_orbitMap (k := AlgebraicClosure (GaloisField p (2 * e))) b α
    have h2 : rootChar b (CFSG.LieType.Steinberg.orbitSum orbitMap α) =
        ∏ m, b m ^ CFSG.LieType.Steinberg.orbitSum orbitMap α m := rfl
    rw [h, ← h2, hαc, twistedE6_rootChar_nsmul, hb, one_pow]
  have hg' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
  have hle : (⨆ α ∈ {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum orbitMap α = c • β),
        e6Data_valid.rootGroup (GaloisField p (2 * e)) α) ≤ (Subgroup.centralizer
          {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
            (twistedE6PhiAmbient p e) :=
    iSup₂_le fun α hα => iSup_le fun hc => hgen α hα hc
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg')

end Phi

section Perfect

variable {p e : ℕ} [Fact p.Prime]

theorem twistedE6_exists_rankOne_eq_map_conj {K : Type*} [Group K]
    {D : CFSG.LieType.Universal.UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅) {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) :
    ∃ (g : K) (i : Fin D.rank), D.rootGroup δ ⊔ D.rootGroup (-δ) =
      (rankOne D.rootGroup i).map (MulAut.conj g).toMonoidHom := by
  rcases hδ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · obtain ⟨g', hg'⟩ := exists_map_conj_rankOne hct w
    exact ⟨g', i, (hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)).symm⟩
  · rw [hdiv] at hi
    exact absurd hi (Set.notMem_empty i)

theorem twistedE6_rootPair_perfect (he : 1 ≤ e) (h4 : 4 ≤ p ^ e) {δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) :
    twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ) ≤
      ⁅twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
          twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ),
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
          twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ)⁆ := by
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨Fact.out, he, rfl⟩
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .twistedE6 0 p e Fact.out trivial hadm
  have hδ' : δ ∈ (modelUniv .twistedE6 0 p e Fact.out).D.roots := by
    show δ ∈ (twistedE6Datum p e).roots
    rw [twistedDatum_roots]
    exact hδ
  obtain ⟨g, i, h⟩ := twistedE6_exists_rankOne_eq_map_conj hct rfl hδ'
  have h' : twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
      twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ) =
      (e6RankOne p e i).map (MulAut.conj g).toMonoidHom := h
  rw [h']
  exact fundPerfect_map_conj_le_commutator (twistedE6_rankOne_perfect p e he h4 i) g

theorem twistedE6_commute_of_phi_sign (he : 1 ≤ e) (h4 : 4 ≤ p ^ e)
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    {u : twistedE6Group p e}
    (hu : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) u =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ) (hb : rootChar b δ = 1) :
    ∀ r ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ), u * r = r * u := by
  have hperf := twistedE6_rootPair_perfect he h4 hδ
  have hb' : rootChar b (-δ) = 1 := by rw [twistedE6_rootChar_neg, hb, inv_one]
  have hle : twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
      twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ) ≤ (Subgroup.centralizer
        {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
          (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e)))) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact twistedE6Phi_commute_of_rootChar p e hb hg
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact twistedE6Phi_commute_of_rootChar p e hb' hg
  have hc : ∀ r ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
      twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ), ⁅u, r⁆ ∈ Subgroup.center _ := by
    intro r hr
    refine ker_twistedE6Phi_le_center p e (AlgebraicClosure (GaloisField p (2 * e))) ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hu]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (hle hr))
    calc rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
          twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r *
          (rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))⁻¹ *
          (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r)⁻¹
        = (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r *
          rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))) *
          (rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))⁻¹ *
          (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r)⁻¹ := by rw [h]
      _ = 1 := by group
  exact CFSG.ClassicalInvolution.RouteD.Exotic.commutes_of_commutator_mem_center hperf hc

end Perfect

end CFSG.ClassicalInvolution.ModelFacts
