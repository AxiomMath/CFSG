module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDichSolv
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDichP2
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Comp

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem isQuasisimple_cfsg_of_alt {Q : Type*} [Group Q] (hm : 5 ≤ m)
    (e : Q ≃* alternatingGroup (Fin m)) : CFSG.IsQuasisimple Q := by
  obtain ⟨hc, hs⟩ := isQuasisimple_of_alt hm e
  have hz := center_eq_bot_of_alt (by omega) e
  have hquot : (Q ⧸ center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  refine ⟨⟨hc⟩, hs, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_alt (by omega) e
  refine ⟨hquot.symm a, hquot.symm b, fun h => hab ?_⟩
  have := congrArg hquot h
  simpa using this

omit [Finite X] in
theorem isComponent_subgroupOf_centralizer (h : ExactShape t A m) (hm : 5 ≤ m) :
    CFSG.IsComponent (A.subgroupOf (centralizer ({t} : Set X))) := by
  obtain ⟨e⟩ := h.iso
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe h.le_cent).symm (isQuasisimple_cfsg_of_alt hm e)
  · have hnorm : (A.subgroupOf (centralizer ({t} : Set X))).Normal :=
      (normal_subgroupOf_iff_le_normalizer h.le_cent).2 h.cent_le_norm
    exact hnorm.isSubnormal

end Comp

section Main

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

omit [Finite X] in
theorem center_layer_le_fitting :
    (center (CFSG.layer X)).map (CFSG.layer X).subtype ≤ CFSG.fittingSubgroup X :=
  CFSG.WholeGroup.center_layer_le_fittingSubgroup

theorem section_dichotomy (hO : CFSG.oddCore X = ⊥) (h : ExactShape t A m) (hm : 5 ≤ m) :
    t ∈ center X ∨
    (∃ K : Subgroup X, CFSG.IsComponent K ∧ K.map (MulAut.conj t).toMonoidHom ≠ K ∧
        CFSG.layer X = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
        Nonempty (K ≃* alternatingGroup (Fin m)) ∧
        (A : Set X) = {g | ∃ k ∈ K, g = k * (t * k * t⁻¹)}) ∨
    AlmostSimple X := by
  classical
  by_cases hP : CFSG.pCore 2 X = ⊥
  swap
  · exact Or.inl (mem_center_of_pCore_ne_bot h hm hP)
  right
  obtain ⟨e⟩ := h.iso
  have hpp : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup X = ⊥ := (CFSG.Fitting_eq_pcore X 2 hpp).trans hP
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order] at this
  obtain ⟨-, K, hKc, -, -, -, hiff, -, hKt'⟩ :=
    SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer hpp ht2 h.le_cent
      (isComponent_subgroupOf_centralizer h hm)
  set Kt : Subgroup X := K.map (MulAut.conj t).toMonoidHom with hKtdef
  have hKtc : CFSG.IsComponent Kt := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hKc
  have hall : ∀ L : Subgroup X, CFSG.IsComponent L → L = K ∨ L = Kt := by
    intro L hL
    by_contra hne
    push Not at hne
    have hAL : ⁅A, L⁆ = ⊥ := by
      by_contra hAL
      rcases (hiff L hL).1 hAL with h1 | h1
      · exact hne.1 h1
      · exact hne.2 h1
    have hLC : L ≤ centralizer (A : Set X) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hAL
    have hsolv := solvable_centralizer_of_exactShape h
    have hLs : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLC)
        (Subgroup.inclusion_injective hLC)
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect L := hL.1.1
    exact Group.IsPerfect.not_isSolvable L hLs
  have hlayer : CFSG.layer X = K ⊔ Kt := by
    apply le_antisymm
    · refine sSup_le (fun L hL => ?_)
      rcases hall L hL with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_sSup hKc) (le_sSup hKtc)
  have hZK : center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzK : (z : X) ∈ K := z.2
    have hzc : ∀ l ∈ K, l * (z : X) = (z : X) * l := fun l hl => by
      have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hztc : ∀ l ∈ Kt, l * (z : X) = (z : X) * l := by
      intro l hl
      by_cases hKK : Kt = K
      · exact hzc l (hKK ▸ hl)
      · have hle : K ≤ centralizer (Kt : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hKt' hKK).1
        exact mem_centralizer_iff.1 (hle hzK) l hl
    have hzL : (z : X) ∈ CFSG.layer X := by
      rw [hlayer]; exact mem_sup_left hzK
    have hzLc : ∀ l ∈ CFSG.layer X, l * (z : X) = (z : X) * l := by
      intro l hl
      rw [hlayer] at hl
      have : K ⊔ Kt ≤ centralizer ({(z : X)} : Set X) :=
        sup_le (fun k hk => mem_centralizer_singleton_iff.2 (hzc k hk))
          (fun l hl => mem_centralizer_singleton_iff.2 (hztc l hl))
      exact mem_centralizer_singleton_iff.1 (this hl)
    have hmem : (z : X) ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype :=
      ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hzLc g g.2)), rfl⟩
    have hZlF := center_layer_le_fitting (X := X)
    rw [hF] at hZlF
    have h1 : (z : X) = 1 := Subgroup.mem_bot.1 (hZlF hmem)
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hquotK : (↥K ⧸ center K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  by_cases hKK : Kt = K
  ·
    right
    have hlay : CFSG.layer X = K := by rw [hlayer, hKK, sup_idem]
    have hFK : CFSG.generalizedFitting X = K := by
      simp only [CFSG.generalizedFitting.eq_sup]
      rw [hF, hlay, bot_sup_eq]
    have hsK : IsSimpleGroup (↥K ⧸ center K) := hKc.1.2.1
    have hsimpleK : IsSimpleGroup ↥K := hquotK.symm.isSimpleGroup
    refine ⟨CFSG.generalizedFitting X, rfl, (MulEquiv.subgroupCongr hFK).isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hKc.1.2.2
    let ε : (↥K ⧸ center K) ≃* ↥(CFSG.generalizedFitting X) :=
      hquotK.trans (MulEquiv.subgroupCongr hFK).symm
    exact ⟨ε a, ε b, fun hc => hab (ε.injective (by rw [map_mul, map_mul, hc]))⟩
  ·
    left
    refine ⟨K, hKc, hKK, hlayer, ?_, ?_⟩
    · obtain ⟨φ⟩ := (hKt' hKK).2.2.2
      have hzA := center_eq_bot_of_alt (by omega) e
      let hquotA : (↥A ⧸ center A) ≃* ↥A :=
        (QuotientGroup.quotientMulEquivOfEq hzA).trans QuotientGroup.quotientBot
      exact ⟨hquotK.symm.trans (φ.symm.trans (hquotA.trans e))⟩
    · rw [(hKt' hKK).2.2.1]
      ext g
      simp [eq_comm]

end Main

end CFSG.OddStandard.AltStdSec
