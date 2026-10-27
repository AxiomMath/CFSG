module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthType
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.StandardType (GGLabelRigidInput)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem i167COrth_fixed_special (hD : COrthLabelDict) (hRig : GGLabelRigidInput)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {g : ↥(orthDerived Q)} (hg : orderOf g = p) {h : F[X]}
    (hh : h ∈ primaryFactors (g : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (g : V ≃ₗ[F] V) h)) {J : Subgroup ↥(orthDerived Q)}
    (hJs : J = (specialBlock Q (g : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J))
    (hJt : Type167J p J) : False := by
  obtain ⟨f, hf, hcard⟩ := exists_natCard_eq_two_pow F
  have hm4 := i167COrth_hm4 hp hp2 hpq hQ hg hh hne hq
  have hU : catalogIs (PSimple p J) (isUnA (primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h)
      (Nat.card F)) := by
    rw [hJs]
    exact catalogIs_pSimple_specialBlock hp hp2 hpq hQ hg hh hne rfl hm4
  rw [hcard] at hU
  exact i167COrth_type_no_unitary hD hRig hJq hJp hJt (by omega) hf hU

theorem i167COrth_fixed_space (hD : COrthLabelDict) (hRig : GGLabelRigidInput)
    (hb : CatDistinct.OrderBridge) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {m : ℕ} (hm : 3 ≤ m)
    (hdim : Module.finrank F V = 2 * (m + 1)) {g : ↥(orthDerived Q)} (hg : orderOf g = p)
    (hdimW : Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) = 2 * m)
    (hiff : IsPlusType Q ↔ ¬ IsPlusType (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype))
    {J : Subgroup ↥(orthDerived Q)}
    (hJe : J = (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J))
    (hJt : Type167J p J) :
    (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
        catalogIs ↥(orthDerived Q) (isOmPA (n + 1) 2)) ∨
      ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
        catalogIs ↥(orthDerived Q) (isOmMA (n + 1) (2 ^ k)) := by
  classical
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hx : OddOrderIsometry Q p (g : V ≃ₗ[F] V) := oddOrderIsometry_of_orthDerived hp hpl hQ g hg
  have hR := hx.polarBilin_fixed_nondegenerate
  obtain ⟨f, hf, hcard⟩ := exists_natCard_eq_two_pow F
  subst hJe
  by_cases hplus : IsPlusType (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype)
  · have h2 := catalogIs_pSimple_supportedFixedDerived hx
      (catalogIs_pSimple_top_orthDerived_plus hR hm hdimW hplus hp hp2 hpq)
    rw [hcard] at h2
    obtain ⟨n, k, hn, hk, hpk, hc, hnm, hka⟩ := i167COrth_type_plus hD hRig hJq hJp hJt hb hm hf h2
    have h3 := catalogIs_orthDerived_minus hQ (by omega : 4 ≤ m + 1) hdim fun hV => hiff.1 hV hplus
    rw [hcard] at h3
    refine Or.inr ⟨n, k, hn, hk, hpk, hc, ?_⟩
    rw [hnm, hka]
    exact h3
  · have hV : IsPlusType Q := hiff.2 hplus
    by_cases hm4 : 4 ≤ m
    · have h2 := catalogIs_pSimple_supportedFixedDerived hx
        (catalogIs_pSimple_top_orthDerived_minus hR hm4 hdimW hplus hp hp2 hpq)
      rw [hcard] at h2
      obtain ⟨hp3, n, hn, hc, hnm, hf1⟩ := i167COrth_type_minus hD hRig hJq hJp hJt hm4 hf h2
      have h3 := catalogIs_orthDerived_plus hQ (by omega : 3 ≤ m + 1) hdim hV
      rw [hcard, hf1, pow_one] at h3
      exact Or.inl ⟨hp3, n, hn, hc, by rw [hnm]; exact h3⟩
    · have hm3 : m = 3 := by omega
      subst hm3
      have h2 := catalogIs_pSimple_supportedFixedDerived hx
        (i167COrth_catalogIs_minus_six hR (by omega) hplus hp hp2 hpq)
      rw [hcard] at h2
      exact (i167COrth_type_no_unitary hD hRig hJq hJp hJt (by norm_num) hf h2).elim

theorem i167COrth_fixed (hD : COrthLabelDict) (hRig : GGLabelRigidInput) (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {N : ℕ} (hdim : Module.finrank F V = 2 * N) (hN : 4 ≤ N)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A)
    (hmax : ∀ E : Subgroup ↥(orthDerived Q), IsElemAbelian p E → A ≤ E → E = A)
    {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p) {J : Subgroup ↥(orthDerived Q)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({g} : Set ↥(orthDerived Q))))
    (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J))
    (hCJ : ∀ a ∈ A, (∀ j ∈ J, a * j = j * a) → a ∈ Subgroup.zpowers g) (hJt : Type167J p J) :
    (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
        catalogIs ↥(orthDerived Q) (isOmPA (n + 1) 2)) ∨
      ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
        catalogIs ↥(orthDerived Q) (isOmMA (n + 1) (2 ^ k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases comp_cases_orthDerived_gen hQ hp hp2 hpq hg hJ with
    ⟨h, hh, hne, hq, hJs⟩ | ⟨G, -, hGle, -, hGdim, hJG⟩
  · exact (i167COrth_fixed_special hD hRig hQ hp hp2 hpq hg hh hne hq hJs hJ.2.2 hJp hJt).elim
  · have hCA : ∀ a ∈ A, (∀ j ∈ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q),
        a * j = j * a) → a ∈ Subgroup.zpowers g := by
      intro a ha hc
      apply hCJ a ha
      intro j hj
      apply hc j
      rw [hJG] at hj
      exact Subgroup.mem_subgroupOf.2 (hGle (Subgroup.mem_subgroupOf.1 hj))
    obtain ⟨hdimW, hiff⟩ := i167COrth_witt hQ hp hp2 hpq hdim hN hA hmax hgA hg hCA
    have hGeq : G = supportedFixedDerived Q (g : V ≃ₗ[F] V) := hGdim.resolve_left (by omega)
    exact i167COrth_fixed_space hD hRig hb hQ hp hp2 hpq (by omega) hdim hg (by omega) hiff
      (by rw [hJG, hGeq]) hJ.2.2 hJp hJt

end CFSG.LocalAnalysis.GLTheoremA.I167

end
