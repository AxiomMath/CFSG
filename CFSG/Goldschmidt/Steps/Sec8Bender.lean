module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.Walter.Bender1970.S3.FStar
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem iSup_qCoreOf_le_centralizer (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    (⨆ (q : ℕ) (_ : q.Prime) (_ : q ≠ p), qCoreOf H q) ≤
      Subgroup.centralizer (qCoreOf H p : Set G) :=
  iSup_le fun _ => iSup_le fun hq => iSup_le fun hqp =>
    qCoreOf_centralizer_of_ne H hp hq (Ne.symm hqp)

theorem fittingSubgroupOf_eq_sup (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    CFSG.fittingSubgroupOf H =
      qCoreOf H p ⊔ ⨆ (q : ℕ) (_ : q.Prime) (_ : q ≠ p), qCoreOf H q := by
  refine le_antisymm ?_ (sup_le (qCoreOf_le_fittingSubgroupOf H p hp)
    (iSup_le fun q => iSup_le fun hq => iSup_le fun _ => qCoreOf_le_fittingSubgroupOf H q hq))
  rw [show CFSG.fittingSubgroupOf H = CFSG.GorensteinWalter.fittingSubgroupOf H from rfl,
    fittingSubgroupOf_eq_iSup_qCoreOf]
  refine iSup_le fun q => ?_
  by_cases hqp : q.1.1 = p
  · rw [hqp]
    exact le_sup_left
  · exact le_sup_of_le_right
      (le_iSup_of_le q.1.1 (le_iSup_of_le (Nat.prime_of_mem_primeFactors q.1.2)
        (le_iSup_of_le hqp le_rfl)))

theorem benderX (H : Subgroup G) {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : P ≤ qCoreOf H p) :
    let X := (qCoreOf H p ⊓ Subgroup.normalizer (P : Set G)) ⊔
      ((⨆ (q : ℕ) (_ : q.Prime) (_ : q ≠ p), qCoreOf H q) ⊔ componentLayerOf H)
    X ≤ generalizedFittingSubgroupOf H ∧
      (X.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal ∧
      generalizedFittingSubgroupOf H ⊓ Subgroup.centralizer (X : Set G) ≤ X ∧
      X ≤ Subgroup.normalizer (P : Set G) := by
  intro X
  set K := ⨆ (q : ℕ) (_ : q.Prime) (_ : q ≠ p), qCoreOf H q with hK
  have hKF : K ≤ CFSG.fittingSubgroupOf H := by
    rw [fittingSubgroupOf_eq_sup H hp]
    exact le_sup_right
  have hOF : qCoreOf H p ≤ CFSG.fittingSubgroupOf H := qCoreOf_le_fittingSubgroupOf H p hp
  have hFF : CFSG.fittingSubgroupOf H ≤ generalizedFittingSubgroupOf H := le_sup_left
  have hEF : componentLayerOf H ≤ generalizedFittingSubgroupOf H := le_sup_right
  have hXF : X ≤ generalizedFittingSubgroupOf H :=
    sup_le (inf_le_left.trans (hOF.trans hFF)) (sup_le (hKF.trans hFF) hEF)
  have hKC : K ≤ Subgroup.centralizer (P : Set G) :=
    (iSup_qCoreOf_le_centralizer H hp).trans (Subgroup.centralizer_le hP)
  have hEC : componentLayerOf H ≤ Subgroup.centralizer (P : Set G) :=
    (Walter.componentLayerOf_le_centralizer_fitting H).trans
      (Subgroup.centralizer_le (hP.trans hOF))
  refine ⟨hXF, Walter.isSubnormal_of_componentLayerOf_le (le_sup_right.trans le_sup_right) hXF,
    ?_, sup_le inf_le_right (sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _))
      (hEC.trans (Subgroup.centralizer_le_normalizer _)))⟩
  rintro y ⟨hyF, hyC⟩
  have hyE : y ∈ Subgroup.centralizer (componentLayerOf H : Set G) :=
    Subgroup.centralizer_le (le_sup_right.trans le_sup_right : componentLayerOf H ≤ X) hyC
  have hyFit : y ∈ CFSG.fittingSubgroupOf H :=
    Walter.generalizedFittingSubgroupOf_inf_centralizer_le H ⟨hyF, hyE⟩
  rw [fittingSubgroupOf_eq_sup H hp] at hyFit
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup_decompose_of_centralizes hyFit
    (iSup_qCoreOf_le_centralizer H hp)
  have hPX : P ≤ X := le_sup_left.trans' (le_inf hP Subgroup.le_normalizer)
  have hwP : w ∈ Subgroup.centralizer (P : Set G) := hKC hw
  have hyP : u * w ∈ Subgroup.centralizer (P : Set G) := Subgroup.centralizer_le hPX hyC
  have huP : u ∈ Subgroup.centralizer (P : Set G) := by
    simpa using Subgroup.mul_mem _ hyP (Subgroup.inv_mem _ hwP)
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hu, Subgroup.centralizer_le_normalizer _ huP⟩)
    (Subgroup.mem_sup_right (Subgroup.mem_sup_left hw))

theorem qCoreOf_inf_eq_bot (hsimple : IsSimpleGroup G) {H M : Subgroup G} (hH : IsCoatom H)
    {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : P ≤ qCoreOf H p)
    (hPM : Subgroup.normalizer (P : Set G) ≤ M) {q : ℕ} (hq : q.Prime)
    (hqF : q ∉ primesOfOrder (CFSG.fittingSubgroupOf H)) : qCoreOf M q ⊓ H = ⊥ := by
  obtain ⟨hXF, hXsub, hXC, hXN⟩ := benderX H hp hP
  exact bender1970_1_7_i_oddCoreDisjoint hsimple H hH _ hXF hXsub hXC (hXN.trans hPM) q hq hqF

theorem qCoreOf_le_of_mem (hsimple : IsSimpleGroup G) {H M : Subgroup G} (hH : IsCoatom H)
    {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : P ≤ qCoreOf H p)
    (hPM : Subgroup.normalizer (P : Set G) ≤ M) {q : ℕ} (hq : q.Prime)
    (hqF : q ∈ primesOfOrder (CFSG.fittingSubgroupOf H))
    (hres : pResidualOf (generalizedFittingSubgroupOf H) q ≠ ⊥) : qCoreOf M q ≤ H := by
  obtain ⟨hXF, hXsub, hXC, hXN⟩ := benderX H hp hP
  have hRA := pResidualOf_generalizedFitting_isNormalIn H q
  have hN := normalizer_eq_of_nontrivial_normal_in_coatom hsimple hH hRA.1 hres
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hRA.1).mpr (le_normalizer_of_isNormalIn hRA))
  calc qCoreOf M q
      ≤ Subgroup.centralizer (pResidualOf (generalizedFittingSubgroupOf H) q : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (bender1970_1_7_ii_commutator_pResidual hsimple H hH _ hXF hXsub hXC (hXN.trans hPM)
            q hq hqF)
    _ ≤ Subgroup.normalizer (pResidualOf (generalizedFittingSubgroupOf H) q : Set G) :=
        Subgroup.centralizer_le_normalizer _
    _ = H := hN

end CFSG.Goldschmidt.Sec8
