module

public import Mathlib
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
public import CFSG.GH74.KGroups.TwoM12CheckInputs
public meta import CFSG.GH74.KGroups.TwoM12CheckInputs
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2200
public import Certificates.Certificate3086
public import Certificates.Certificate5131
public import Certificates.Certificate10024
public import Certificates.Certificate11003
public import Certificates.Certificate11004

public section

namespace CFSG.GH74.KGroups.TwoM12

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.M12Cover CFSG.Blueprint Subgroup
open scoped commutatorElement

set_option compiler.extract_closed false

theorem card_centralizer_conj_eq {G : Type*} [Group G] (c t : G) :
    Nat.card (centralizer ({c * t * c⁻¹} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
  have h := centralizerEquiv (MulAut.conj c) t
  rw [MulAut.conj_apply] at h
  exact (Nat.card_congr h.toEquiv).symm

theorem fixedCount_elemA0 :
    fixedCount elemA0 = 4 := by
  show (Finset.univ.filter fun i : Fin 12 => permA0 i = i).card = 4
  decide +kernel

theorem card_centralizer_elemR :
    Nat.card (centralizer ({elemR} : Set NativeSporadic.M12)) = 192 := by
  obtain ⟨g, hg⟩ := conj_elemR_of_fixedCount_four elemA0 orderOf_elemA0 fixedCount_elemA0
  rw [← card_centralizer_elemA0, ← hg]
  exact (card_centralizer_conj_eq g elemR).symm

theorem solvable_centralizer_elemR :
    Group.IsSolvable ↥(centralizer ({elemR} : Set NativeSporadic.M12)) := by
  have := Fintype.ofFinite ↥(centralizer ({elemR} : Set NativeSporadic.M12))
  have h192 : Fintype.card ↥(centralizer ({elemR} : Set NativeSporadic.M12)) = 192 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_centralizer_elemR
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 6) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
    (h192.trans (by norm_num))

theorem gzPerm_mem : gzPerm ∈ NativeSporadic.M12 := evalCodes_mem _ m12_gens_mem' gzWord

theorem permZ_eq : permZ = gzPerm * m12Rep2 * gzPerm⁻¹ := gz_conj

theorem commCheck_eq :
    commCheckOn fixedDQ.orbitTables (elemsT m12CentQ2) = true :=
  Certificates.certificate5131

theorem exists_conj_mem_elemsT
    (x : NativeSporadic.M12)
    (hx : x ∈ centralizer ({elemZ} : Set NativeSporadic.M12)) :
    ∃ y ∈ elemsT m12CentQ2, gzPerm * y * gzPerm⁻¹ = (x : Equiv.Perm (Fin 12)) := by
  have hQ2 : ValidSchreier m12CentQ2 := m12_oddcore_cent2.1
  have hxz : (x : Equiv.Perm (Fin 12)) ∈ centralizerIn NativeSporadic.M12 permZ := by
    rw [mem_centralizerIn]
    exact ⟨x.2, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx)⟩
  rw [permZ_eq, centralizerIn_conj NativeSporadic.M12 gzPerm_mem, centralizerIn_m12Rep2] at hxz
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxz
  refine ⟨y, (mem_elemsT m12CentQ2 hQ2 y).2 hy, ?_⟩
  exact hyx

theorem commutator_centralizer_elemZ_le :
    ⁅centralizer ({elemZ} : Set NativeSporadic.M12), centralizer ({elemZ} : Set NativeSporadic.M12)⁆ ≤
      fixedD := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨y, hy, hya⟩ := exists_conj_mem_elemsT a ha
  obtain ⟨y', hy', hyb⟩ := exists_conj_mem_elemsT b hb
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 commCheck_eq y hy) y' hy'
  have h2 : ((⁅a, b⁆ : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ fixedDQ.originalSubgroup := by
    rw [mem_iff_sift fixedDQ fixedDQ_valid]
    have h3 : ((⁅a, b⁆ : NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
        gzPerm * (y * y' * y⁻¹ * y'⁻¹) * gzPerm⁻¹ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hya, ← hyb]
      group
    rw [h3]
    exact h1
  exact mem_fixedD.2 h2

end CFSG.GH74.KGroups.TwoM12
