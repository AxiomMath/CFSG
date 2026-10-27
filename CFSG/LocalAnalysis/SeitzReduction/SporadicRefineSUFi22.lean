module

public import CFSG.Sporadic.FischerOddCore.Fi22LocalComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.UnitaryPilot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.LocalCores CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer
open CFSG.LocalAnalysis.ComponentInitial CFSG.Sporadic.FischerOddCore
open scoped commutatorElement

theorem component_card_center_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {B : Subgroup G} (hB : IsComponent B) :
    IsComponent (B.map e.toMonoidHom) ∧
      Nat.card (center B) = Nat.card (center (B.map e.toMonoidHom)) :=
  ⟨LocalCores.isComponent_map_mulEquiv e hB, Nat.card_congr
    (Subgroup.centerCongr (B.equivMapOfInjective e.toMonoidHom e.injective)).toEquiv⟩

theorem eq_top_of_sup_center_of_commutator_eq_top {E : Type*} [Group E] (hE : commutator E = ⊤)
    {M : Subgroup E} (hM : M ⊔ center E = ⊤) : M = ⊤ := by
  have hcl : ∀ x y z : E, z ∈ center E → ⁅x * z, y⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [commutatorElement_def, commutatorElement_def, mul_assoc x z y,
      ← Subgroup.mem_center_iff.mp hz y, ← mul_assoc]
    group
  have hcr : ∀ x y z : E, z ∈ center E → ⁅x, y * z⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [← commutatorElement_inv, hcl _ _ _ hz, commutatorElement_inv]
  rw [eq_top_iff, ← hE, _root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hM ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hM ▸ Subgroup.mem_top y)
  rw [hcl _ _ _ hz, hcr _ _ _ hz', commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem component_eq_top_of_central_kernel {E K : Type*} [Group E] [Group K]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E)
    (hKs : IsSimpleGroup K) (hE : commutator E = ⊤) {B : Subgroup E} (hB : IsComponent B) :
    B = ⊤ := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hnt : Nontrivial B := isQuasisimple_nontrivial hq
  have hmap : B.map ρ = ⊤ := by
    rcases (hsub.map hρ).eq_bot_or_top_of_isSimpleGroup hKs with h | h
    · exfalso
      have hBZ : B ≤ center E := fun b hb => hker (by
        rw [MonoidHom.mem_ker]
        have : ρ b ∈ B.map ρ := ⟨b, hb, rfl⟩
        rwa [h, Subgroup.mem_bot] at this)
      have : Group.IsSolvable B :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBZ)
      exact Group.IsPerfect.not_isSolvable B this
    · exact h
  refine eq_top_of_sup_center_of_commutator_eq_top hE (eq_top_iff.mpr fun g _ => ?_)
  obtain ⟨b, hb, hbg⟩ : ρ g ∈ B.map ρ := hmap ▸ Subgroup.mem_top _
  have hz : b⁻¹ * g ∈ center E :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hbg, inv_mul_cancel])
  have hg : g = b * (b⁻¹ * g) := by group
  rw [hg]
  exact Subgroup.mul_mem_sup hb hz

section Fi22


theorem fi22_Ca_component_eq_top {B : Subgroup Sporadic.Fi22.Ca} (hB : IsComponent B) :
    B = ⊤ :=
  component_eq_top_of_central_kernel fi22Kappa fi22Kappa_surjective ker_fi22Kappa.le
    CFSG.Fischer.isSimpleGroup_T46 Sporadic.Fi22.commutator_Ca hB

theorem fi22_Ca_component_card_center {B : Subgroup Sporadic.Fi22.Ca} (hB : IsComponent B) :
    Nat.card (center B) = 2 := by
  have h := fi22_Ca_component_eq_top hB
  subst h
  rw [Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv]
  exact Sporadic.Fi22.card_center_Ca

theorem fi22_CPz_component_card_center
    {B : Subgroup ↥(fi22P ⊓ Subgroup.centralizer {fi22OuterZ})} (hB : IsComponent B) :
    Nat.card (center B) = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_fi22OuterZP_fi22Ya
  have e1 := fi22CPzEquiv
  have e2 := Sporadic.FischerOddCore.centralizerMulEquiv (MulAut.conj c) fi22OuterZP
  have e3 : ↥(Subgroup.centralizer ({MulAut.conj c fi22OuterZP} : Set fi22P)) ≃*
      ↥(Subgroup.centralizer ({fi22Ya} : Set fi22P)) :=
    MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc])
  have e4 := @Sporadic.FischerOddCore.centralizerMulEquiv fi22P CFSG.Sporadic.Fi22.J
    inferInstance inferInstance fi22PJ fi22Ya
  have e5 : ↥(Subgroup.centralizer ({fi22PJ fi22Ya} : Set CFSG.Sporadic.Fi22.J)) ≃*
      Sporadic.Fi22.Ca :=
    MulEquiv.subgroupCongr (by rw [fi22Ya, MulEquiv.apply_symm_apply])
  obtain ⟨hB', hcard⟩ := @component_card_center_of_mulEquiv
    ↥(fi22P ⊓ Subgroup.centralizer {fi22OuterZ}) Sporadic.Fi22.Ca inferInstance inferInstance
    ((((e1.trans e2).trans e3).trans e4).trans e5) B hB
  rw [hcard]
  exact fi22_Ca_component_card_center hB'

theorem fi22_rep_component_card_center {k : ℕ} (hk : k < 3)
    {B : Subgroup ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k})} (hB : IsComponent B) :
    Nat.card (center B) = 2 := by
  obtain ⟨h0, h1, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · exfalso
    have e := MulEquiv.subgroupCongr h0
    have hs : Group.IsSolvable (fi22H 0) :=
      isSolvable_of_card_primeFactors_le_two (by rw [card_fi22H_zero]; exact
        primeFactors_card_fi22H_zero)
    exact not_isComponent_of_isSolvable hs (component_quotient_mulEquiv e hB).1
  · exfalso
    have e := MulEquiv.subgroupCongr h1
    exact CTI_Fi22_second_involution_centralizer_normal_two_subgroup.2.1 _
      (component_quotient_mulEquiv e hB).1
  · have e := MulEquiv.subgroupCongr (show fi22P ⊓ Subgroup.centralizer {fi22ExtRep 2} =
        fi22P ⊓ Subgroup.centralizer {fi22OuterZ} by rw [fi22ExtRep_two])
    obtain ⟨hB', hcard⟩ := component_card_center_of_mulEquiv e hB
    rw [hcard]
    exact fi22_CPz_component_card_center hB'

theorem fi22_involution_component_card_center {T : Type*} [Group T]
    (e : T ≃* Blueprint.NativeSporadic.Fi22) (t : T) (ht : orderOf t = 2)
    (B : Subgroup (Subgroup.centralizer ({t} : Set T))) (hB : IsComponent B) :
    Nat.card (center B) = 2 := by
  set f : T ≃* fi22P := e.trans fi22PermEquiv
  have hτP : ((f t : fi22P) : Equiv.Perm (Fin 3510)) ∈ fi22P := (f t).2
  have hτ : orderOf ((f t : fi22P) : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have g1 : ↥(Subgroup.centralizer ({t} : Set T)) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {((f t : fi22P) : Equiv.Perm (Fin 3510))}) :=
    (Sporadic.FischerOddCore.centralizerMulEquiv f t).trans
      (Sporadic.FischerOddCore.infCentralizerEquiv fi22P hτP).symm
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj (fi22P_le_R hτP) hτ
  have hrn := fi22R_le_normalizer hr
  have hkP : fi22ExtRep k ∈ fi22P := by
    rw [← hrτ]
    exact (Subgroup.mem_normalizer_iff.1 hrn _).1 hτP
  have hk3 : k < 3 := by
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    exact (CTUC_Fi22_all_extension_involutions_covered.2.1 j (by omega)).2 hkP
  have g2 : ↥(fi22P ⊓ Subgroup.centralizer {((f t : fi22P) : Equiv.Perm (Fin 3510))}) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k}) :=
    (fi22CP_conj_equiv hrn _).trans (MulEquiv.subgroupCongr (by rw [hrτ]))
  obtain ⟨hB', hcard⟩ := component_card_center_of_mulEquiv (g1.trans g2) hB
  rw [hcard]
  exact fi22_rep_component_card_center hk3 hB'

end Fi22

end CFSG.SeitzReduction.UnitaryPilot
