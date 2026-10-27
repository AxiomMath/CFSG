module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxBridge
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxBridge2
public import CFSG.RankThree.PartOne.KE6.Phi6A2A2
public import CFSG.RankThree.Classical.SteinbergBYExchangedSL3
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxSL3Fix
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE (wordProd_smul_eq_wordMat_mulVec)
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chain13 chain56 support13 support56 supportA2A2 e6Index chainRoot)
open CFSG.RankThree.Classical2 (isRoot_chainRoot56 chainRoot13_mem_parabolicRoots fixSubgroup
  twoA2MulSup twoA2MulSup_surjective twoA2MulSup_eq_one_iff rootSpan_supportA2A2)
open Matrix
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


namespace QuasiE6X2

abbrev Q12 (L : Type) [Field L] : Subgroup (ModGL TwClass.e6Six.tag L) :=
  subsystemGroup Tag.E6 L support13 ⊔ subsystemGroup Tag.E6 L support56

@[expose] def muGL (L : Type) [Field L] : SL(3, L) × SL(3, L) →* ModGL TwClass.e6Six.tag L :=
  (Q12 L).subtype.comp (twoA2MulSup (Ω := L))

theorem w_13 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain13 i j = chainRoot chain56 i j := by
  decide +kernel

theorem w_56 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain56 i j = chainRoot chain13 i j := by
  decide +kernel

theorem w_smul_13 (i j : Fin 3) (hij : i ≠ j) :
    TwClass.w TwClass.e6Six • (chainRoot chain13 i j : Fin TwClass.e6Six.tag.rank → ℤ) =
      chainRoot chain56 i j := by
  show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • chainRoot chain13 i j = chainRoot chain56 i j
  rw [wordProd_smul_eq_wordMat_mulVec]
  exact w_13 i j hij

theorem w_smul_56 (i j : Fin 3) (hij : i ≠ j) :
    TwClass.w TwClass.e6Six • (chainRoot chain56 i j : Fin TwClass.e6Six.tag.rank → ℤ) =
      chainRoot chain13 i j := by
  show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • chainRoot chain56 i j = chainRoot chain13 i j
  rw [wordProd_smul_eq_wordMat_mulVec]
  exact w_56 i j hij

variable {K : Type} [Field K] [Finite K]

theorem twist_13 (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : D.L, e * e = 1 ∧ ∀ c : D.L,
      ((MulAut.conj D.nW).toMonoidHom.comp D.frobGL)
          (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 D.L (chainRoot chain56 i j) (e * D.Fr c) := by
  have hroot : IsRoot TwClass.e6Six.tag (chainRoot chain13 i j) :=
    (chainRoot13_mem_parabolicRoots hij).1
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L TwClass.e6Six.w hroot
  refine ⟨ε, hε, fun c => ?_⟩
  have h' := h (D.Fr c)
  rw [w_smul_13 i j hij] at h'
  have e1 : D.frobGL (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) =
      pinnedX Tag.E6 D.L (chainRoot chain13 i j) (D.Fr c) :=
    CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX D.Fr _ c
  show D.nW * D.frobGL (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) * D.nW⁻¹ = _
  rw [e1]
  exact h'

theorem twist_56 (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : D.L, e * e = 1 ∧ ∀ c : D.L,
      ((MulAut.conj D.nW).toMonoidHom.comp D.frobGL)
          (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 D.L (chainRoot chain13 i j) (e * D.Fr c) := by
  have hroot : IsRoot TwClass.e6Six.tag (chainRoot chain56 i j) := isRoot_chainRoot56 hij
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L TwClass.e6Six.w hroot
  refine ⟨ε, hε, fun c => ?_⟩
  have h' := h (D.Fr c)
  rw [w_smul_56 i j hij] at h'
  have e1 : D.frobGL (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) =
      pinnedX Tag.E6 D.L (chainRoot chain56 i j) (D.Fr c) :=
    CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX D.Fr _ c
  show D.nW * D.frobGL (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) * D.nW⁻¹ = _
  rw [e1]
  exact h'

theorem twist_injective (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    Function.Injective ((MulAut.conj D.nW).toMonoidHom.comp D.frobGL) :=
  (MulAut.conj D.nW).injective.comp
    (Units.map_injective (f := entrywiseHom D.Fr) (entrywise_injective D.Fr))

theorem exchange (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    ∃ θ : ↥(Q12 D.L) ≃* ↥(Q12 D.L),
      (∀ g, (θ g : ModGL TwClass.e6Six.tag D.L) =
        ((MulAut.conj D.nW).toMonoidHom.comp D.frobGL) (g : ModGL TwClass.e6Six.tag D.L)) ∧
      ∃ a b : SL(3, D.L), ∀ A B : SL(3, D.L), θ (twoA2MulSup (A, B)) =
        twoA2MulSup (a * Matrix.SpecialLinearGroup.map D.Fr B * a⁻¹,
          b * Matrix.SpecialLinearGroup.map D.Fr A * b⁻¹) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  exact CFSG.RankThree.PartOne.KE6.exists_exchanged_layer_pos (Fr := D.Fr)
    D.Fr_bijective.2 ((MulAut.conj D.nW).toMonoidHom.comp D.frobGL) (twist_injective D) 1 1
    (twist_13 D) (twist_56 D)

theorem S₂_eq_parabolic : TwClass.S₂ TwClass.e6Six = parabolicRoots Tag.E6 supportA2A2 := by
  have hiff : ∀ i : Fin Tag.E6.rank,
      i ∈ CFSG.RankThree.E6.supportA2A2 ↔ i.val ∈ TwClass.J₂ TwClass.e6Six := by
    intro i
    rw [CFSG.RankThree.E6.mem_supportA2A2]
    have key : ∀ k : Fin 6, i = e6Index k ↔ i.val = k.val := fun k => Fin.ext_iff
    rw [key 0, key 2, key 4, key 5]
    simp only [TwClass.J₂, Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i fun h => hi ((hiff i).2 h)⟩
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i fun h => hi ((hiff i).1 h)⟩

theorem rootSpan_S₂ (L : Type) [Field L] :
    rootSpan TwClass.e6Six.tag L (TwClass.S₂ TwClass.e6Six) = Q12 L := by
  rw [S₂_eq_parabolic]
  exact rootSpan_supportA2A2 (Ω := L)

theorem exch_data (hK : 3 ≤ Nat.card K) (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    ∃ (a b : SL(3, D.L)) (P : Subgroup (ModGL TwClass.e6Six.tag D.L)),
      (∀ A B : SL(3, D.L),
        muGL D.L (a * Matrix.SpecialLinearGroup.map D.Fr B * a⁻¹,
            b * Matrix.SpecialLinearGroup.map D.Fr A * b⁻¹) =
          D.nW * D.frobGL (muGL D.L (A, B)) * D.nW⁻¹) ∧
      P ≤ D.fixedRoot (TwClass.S₂ TwClass.e6Six) ∧ CFSG.IsQuasisimple ↥P ∧
      ⁅D.fixedRoot (TwClass.S₂ TwClass.e6Six), D.fixedRoot (TwClass.S₂ TwClass.e6Six)⁆ = P ∧
      (¬ 3 ∣ Nat.card K - 1 → P = D.fixedRoot (TwClass.S₂ TwClass.e6Six)) ∧
      (∀ s : SL(3, D.L) × SL(3, D.L),
        (a * Matrix.SpecialLinearGroup.map D.Fr s.2 * a⁻¹,
          b * Matrix.SpecialLinearGroup.map D.Fr s.1 * b⁻¹) = s → muGL D.L s ∈ P) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : ∀ c, D.Fr c = c ^ (p ^ (m : ℕ)) := fun c => by rw [D.hFr, hcard']
  haveI : CharP D.L p := charP_of_injective_algebraMap (algebraMap K D.L).injective p
  obtain ⟨θ, hθΨ, a, b, hθ⟩ := exchange D
  obtain ⟨k₂, hk₂, h₁, h₂, ρ, hρ, hρfix, hρnorm, hρqs, hρker, hρkerc, hρiso, hρcen, hfin, hind,
    hder⟩ := CFSG.RankThree.Classical.SteinbergBY.exchanged_sl3_central_product_frobenius_full_fixed_layer
      (k := K) (Ω := D.L) (Q := ↥(Q12 D.L)) hpp m.pos hcard' D.Fr hFr twoA2MulSup
      twoA2MulSup_surjective
      (fun x => twoA2MulSup_eq_one_iff x.1 x.2) θ a b hθ
  set S₂ := TwClass.S₂ TwClass.e6Six with hS₂
  have hspan : rootSpan TwClass.e6Six.tag D.L S₂ = Q12 D.L := rootSpan_S₂ D.L
  have hΦ : D.fixedRoot S₂ = (fixSubgroup θ).map (Q12 D.L).subtype := by
    ext y
    constructor
    · intro hy
      obtain ⟨hy1, hy2⟩ := (D.mem_fixedRoot).1 hy
      have hyQ : y ∈ Q12 D.L := by rw [← hspan]; exact hy1
      refine ⟨⟨y, hyQ⟩, ?_, rfl⟩
      show θ ⟨y, hyQ⟩ = ⟨y, hyQ⟩
      apply Subtype.ext
      rw [hθΨ]
      exact hy2
    · rintro ⟨x, hx, rfl⟩
      have hx' : θ x = x := hx
      have hx2 := congrArg Subtype.val hx'
      rw [hθΨ] at hx2
      exact (D.mem_fixedRoot).2 ⟨by rw [hspan]; exact x.2, hx2⟩
  set P : Subgroup (ModGL TwClass.e6Six.tag D.L) := ρ.range.map (Q12 D.L).subtype with hP
  have hPle : P ≤ D.fixedRoot S₂ := by
    rw [hΦ]
    exact Subgroup.map_mono hρfix
  have h1 : ⁅fixSubgroup θ, fixSubgroup θ⁆ = ρ.range := by
    have e := congrArg (Subgroup.map (fixSubgroup θ).subtype) hder
    rw [Subgroup.map_subgroupOf_eq_of_le hρfix] at e
    rw [← e, commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm : ⁅D.fixedRoot S₂, D.fixedRoot S₂⁆ = P := by
    rw [hΦ, ← Subgroup.map_commutator, h1]
  have hPqs : CFSG.IsQuasisimple ↥P :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective ρ.range (Q12 D.L).subtype (Q12 D.L).subtype_injective).symm hρqs
  have hPeq : ¬ 3 ∣ Nat.card K - 1 → P = D.fixedRoot S₂ := by
    intro h3
    have hgcd : Nat.gcd 3 (Nat.card K - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [← hcard', hgcd] at hind
    have hidx : (ρ.range.subgroupOf (fixSubgroup θ)).index = 1 := Nat.dvd_one.1 hind
    have htop : ρ.range.subgroupOf (fixSubgroup θ) = ⊤ := Subgroup.index_eq_one.1 hidx
    have hfix : fixSubgroup θ = ρ.range := by
      refine le_antisymm (fun x hx => ?_) hρfix
      have hx' : (⟨x, hx⟩ : fixSubgroup θ) ∈ ρ.range.subgroupOf (fixSubgroup θ) := by
        rw [htop]; exact Subgroup.mem_top _
      exact hx'
    rw [hΦ, hfix]
  have hexact : ∀ s : SL(3, D.L) × SL(3, D.L),
      (a * Matrix.SpecialLinearGroup.map D.Fr s.2 * a⁻¹,
        b * Matrix.SpecialLinearGroup.map D.Fr s.1 * b⁻¹) = s → muGL D.L s ∈ P := by
    obtain ⟨F, hF, hFcard, ρ', hρ'⟩ := QuasiSL3.exchange_fixed_iff_range (Ω := D.L) (k := K)
      hpp m.pos hcard' D.Fr hFr a b
    intro s hs
    obtain ⟨A', rfl⟩ := (hρ' s).1 hs
    let φ : SL(3, ↥F) →* ↥(Q12 D.L) := (twoA2MulSup (Ω := D.L)).comp ρ'
    have hφfix : φ.range ≤ fixSubgroup θ := by
      rintro _ ⟨A, rfl⟩
      show θ (twoA2MulSup (ρ' A)) = twoA2MulSup (ρ' A)
      have := (hρ' (ρ' A)).2 ⟨A, rfl⟩
      rw [show ρ' A = ((ρ' A).1, (ρ' A).2) from rfl, hθ]
      exact congrArg twoA2MulSup this
    have hperfF : Group.IsPerfect SL(3, ↥F) :=
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := ↥F) (n := 3)
        le_rfl).1
    have hφperf : ⁅φ.range, φ.range⁆ = φ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        hperfF.commutator_eq_top]
    have hle : φ.range ≤ ρ.range :=
      calc φ.range = ⁅φ.range, φ.range⁆ := hφperf.symm
        _ ≤ ⁅fixSubgroup θ, fixSubgroup θ⁆ := Subgroup.commutator_mono hφfix hφfix
        _ = ρ.range := h1
    exact ⟨_, hle ⟨A', rfl⟩, rfl⟩
  refine ⟨a, b, P, fun A B => ?_, hPle, hPqs, hcomm, hPeq, hexact⟩
  show ((twoA2MulSup (a * Matrix.SpecialLinearGroup.map D.Fr B * a⁻¹,
      b * Matrix.SpecialLinearGroup.map D.Fr A * b⁻¹) : ↥(Q12 D.L)) : ModGL Tag.E6 D.L) = _
  rw [← hθ A B]
  exact hθΨ _

end QuasiE6X2

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
