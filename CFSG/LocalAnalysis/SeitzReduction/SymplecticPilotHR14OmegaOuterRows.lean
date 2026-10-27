module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

section SPL

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_injective_of_perfect_le_fixedSubgroup_conj (hset : SeitzSetting G L) {n : ℕ}
    (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (M : Set G)) (P : Subgroup M)
    (hPc : commutator P = ⊤)
    (hPF : P ≤ fixedSubgroup (M.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) :
    ∃ φ : P →* StatedSp n K, Function.Injective φ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  set ψ : M →* G := (MulAut.conj g).toMonoidHom.comp M.subtype with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj g).injective.comp M.subtype_injective
  have hPP : Group.IsPerfect P := Group.isPerfect_def.2 hPc
  have hPmP : Group.IsPerfect (P.map ψ) :=
    Group.IsPerfect.ofSurjective (f := ψ.subgroupMap P) (ψ.subgroupMap_surjective P)
  have hPt : P.map ψ ≤ centralizer ({t} : Set G) :=
    (Subgroup.map_mono hPF).trans (map_fixedSubgroup_conj_le_centralizer hg)
  have hPL : P.map ψ ≤ L :=
    std_perfect_le hset.standardSetting hOut htC ht (Subgroup.isPerfect_iff.mp hPmP) hPt
  refine ⟨
    { toFun := fun x => e ⟨ψ (x : M), hPL ⟨x, x.2, rfl⟩⟩
      map_one' := by
        rw [← map_one e]
        congr 1
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        rw [← map_mul e]
        congr 1
        apply Subtype.ext
        simp }, ?_⟩
  intro x y hxy
  have h1 := congrArg Subtype.val (e.injective hxy)
  exact Subtype.ext (hψinj h1)

end SPL

section Transport

variable {X P : Type*} [Group X] [Group P]

theorem mem_fixedSubgroup_congr_iff (ε : X ≃* P) (θ : MulAut X) (y : P) :
    y ∈ fixedSubgroup (MulAut.congr ε θ) ↔ ε.symm y ∈ fixedSubgroup θ := by
  change MulAut.congr ε θ y = y ↔ θ (ε.symm y) = ε.symm y
  have hc : MulAut.congr ε θ y = ε (θ (ε.symm y)) := rfl
  rw [hc]
  constructor
  · intro h
    have := congrArg ε.symm h
    simpa only [MulEquiv.symm_apply_apply] using this
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem exists_injective_of_congr {H : Type*} [Group H] (ε : X ≃* P) (θ : MulAut X)
    (h : ∀ P' : Subgroup X, commutator P' = ⊤ → P' ≤ fixedSubgroup θ →
      ∃ φ : P' →* H, Function.Injective φ)
    (P'' : Subgroup P) (hPc : commutator P'' = ⊤) (hPF : P'' ≤ fixedSubgroup (MulAut.congr ε θ)) :
    ∃ φ : P'' →* H, Function.Injective φ := by
  set e' : P'' ≃* P''.map ε.symm.toMonoidHom :=
    P''.equivMapOfInjective ε.symm.toMonoidHom ε.symm.injective with he'
  have hc : commutator (P''.map ε.symm.toMonoidHom) = ⊤ := commutator_top_transfer e' hPc
  have hle : P''.map ε.symm.toMonoidHom ≤ fixedSubgroup θ := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_fixedSubgroup_congr_iff ε θ y).1 (hPF hy)
  obtain ⟨φ, hφ⟩ := h _ hc hle
  exact ⟨φ.comp e'.toMonoidHom, hφ.comp e'.injective⟩

end Transport

section Rows

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_linear_of_conj (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ f)
    {Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    (∃ (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q), s * s = 1 ∧
      β⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) ∨
    (Even f ∧ Even (n + 1) ∧ ∃ P : Subgroup (matrixProjectiveDerived Q),
      P ≤ fixedSubgroup (MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) ∧
      commutator P = ⊤ ∧ LieModel P .POmegaMinus (n + 1) 2 (f / 2)) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  set θ := (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθ
  have hθθ : θ * θ = 1 := normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hemb : ∀ P : Subgroup (matrixProjectiveDerived Q), P ≤ fixedSubgroup (MulAut.congr ε θ) →
      commutator P = ⊤ → ∃ φ : P →* StatedSp (n + 1 - 1) K, Function.Injective φ := by
    intro P hPF hPc
    exact exists_injective_of_congr ε θ
      (fun P' hP'c hP'F => exists_injective_of_perfect_le_fixedSubgroup_conj hset (by omega) e ht
        hKt hg P' hP'c hP'F) P hPc hPF
  exact exists_conj_linear_of_embedding hf hK' (by omega) hQ hT hE hconj hKc hαα hemb

theorem exists_conj_linear_of_conj_of_input (hU18 : OmegaMinusSpNonembeddingInput)
    (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ f)
    {Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ∃ (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q), s * s = 1 ∧
      β⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
  rcases exists_conj_linear_of_conj hset hn hKc hf e ht hKt hK' hQ hT hE hconj ε hg with h | h
  · exact h
  · exfalso
    obtain ⟨⟨m, hm⟩, hNe, P, hPF, hPc, hPlie⟩ := h
    have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
    obtain ⟨φ, hφ⟩ := exists_injective_of_congr ε _
      (fun P' hP'c hP'F => exists_injective_of_perfect_le_fixedSubgroup_conj hset (by omega) e ht
        hKt hg P' hP'c hP'F) P hPc hPF
    have hN6 : 6 ≤ n + 1 := by obtain ⟨k, hk⟩ := hNe; omega
    exact hU18 P (n + 1) (f / 2) hN6 hNe (by omega) hPlie K (by rw [hKc]; congr 1; omega) φ hφ

end Rows

end CFSG.SeitzReduction.SymplecticPilot
