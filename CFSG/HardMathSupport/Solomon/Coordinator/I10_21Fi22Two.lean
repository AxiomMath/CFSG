module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4
public import Certificates.Certificate13501

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ
open CFSG.Sporadic.Fi22 (gA gB J fi22EquivJ matrixFacts)
open CFSG.Open (IsElemAbelian)
open scoped Matrix

theorem i1021_transport_elemAbelian {G F : Type*} [Group G] [Group F] {p : ℕ} {E J : Subgroup G}
    (hEJ : E ≤ J) (hE : IsElemAbelian p E) (f : F ≃* J) :
    ∃ V : Subgroup F, IsElemAbelian p V ∧ Nat.card V = Nat.card E := by
  refine ⟨(E.subgroupOf J).map f.symm.toMonoidHom, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map (i1021_isElemAbelian_subgroupOf hE J) _
  · rw [Subgroup.card_map_of_injective f.symm.injective,
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv)]

section Facts


abbrev i1021Φ : GL (Fin 77) (ZMod 3) →* Matrix (Fin 77) (Fin 77) (ZMod 3) := Units.coeHom _

theorem i1021Φ_injective : Function.Injective i1021Φ := Units.val_injective

theorem i1021_coe_inv_pow {M : Type*} [Monoid M] (u : Mˣ) {n : ℕ} (h : (u : M) ^ (n + 1) = 1) :
    ((u⁻¹ : Mˣ) : M) = (u : M) ^ n :=
  Units.inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact h)

theorem i1021Φ_gA : i1021Φ gA = CFSG.Sporadic.Fi22.mA := rfl

theorem i1021Φ_gB : i1021Φ gB = CFSG.Sporadic.Fi22.mB := rfl

theorem i1021Φ_gA_inv : i1021Φ gA⁻¹ = CFSG.Sporadic.Fi22.mA := by
  have h : (gA : Matrix (Fin 77) (Fin 77) (ZMod 3)) ^ (1 + 1) = 1 := by
    rw [pow_two]
    exact matrixFacts.A_sq
  have := i1021_coe_inv_pow gA h
  rw [pow_one] at this
  exact this

theorem i1021Φ_gB_inv : i1021Φ gB⁻¹ = CFSG.Sporadic.Fi22.mB ^ 12 :=
  i1021_coe_inv_pow gB (n := 12) matrixFacts.B_pow

theorem i1021_rep_gA : Rep (spec3 77) i1021Φ gA i1021Fi22RegA := by
  have hw := (spec3 77).decode_wf NativeSporadic.Fi22Seed1
  refine rep_of hw hw ?_ ?_
  · rw [(spec3 77).toMat_decode, i1021Φ_gA]
  · rw [(spec3 77).toMat_decode, i1021Φ_gA_inv]

theorem i1021_rep_gB : Rep (spec3 77) i1021Φ gB i1021Fi22RegB := by
  have hw := (spec3 77).decode_wf NativeSporadic.Fi22Seed2
  refine rep_of hw ((spec3 77).pow_spec hw 12).1 ?_ ?_
  · rw [(spec3 77).toMat_decode, i1021Φ_gB]
  · rw [((spec3 77).pow_spec hw 12).2, (spec3 77).toMat_decode, i1021Φ_gB_inv]

@[expose] noncomputable def i1021Fi22U (j : Fin 5) : GL (Fin 77) (ZMod 3) :=
  signedWord gA gB (i1021Fi22Word j)

theorem i1021_fi22_u_facts :
    (∀ j, i1021Fi22U j ^ 2 = 1) ∧ (∀ i j, Commute (i1021Fi22U i) (i1021Fi22U j)) ∧
      ∀ a : Fin 5 → Fin 2, a ≠ 0 →
        (List.ofFn fun i => i1021Fi22U i ^ (a i : ℕ)).prod ≠ 1 := by
  have hX : ∀ j, (spec3 77).WF (i1021Fi22X j) ∧
      (spec3 77).toMat (i1021Fi22X j) = i1021Φ (i1021Fi22U j) := fun j =>
    rep_signedWord i1021_rep_gA i1021_rep_gB (i1021Fi22Word j)
  exact OpsSpecFacts.elem2_of_ok (spec3 77) i1021Φ i1021Φ_injective i1021Fi22U i1021Fi22X hX
    Certificates.certificate13501

theorem i1021_fi22_u_mem (j : Fin 5) : i1021Fi22U j ∈ J :=
  signedWord_mem J (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) _

theorem i1021_J_two_rank_five :
    ∃ E : Subgroup (GL (Fin 77) (ZMod 3)), E ≤ J ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 5 := by
  obtain ⟨hsq, hcomm, hker⟩ := i1021_fi22_u_facts
  obtain ⟨η, -, -, -, -, hcard⟩ := exists_elemAbelian_two i1021Fi22U hsq hcomm hker
  refine ⟨Subgroup.closure (Set.range i1021Fi22U), ?_, ?_, hcard⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact i1021_fi22_u_mem i
  · refine i1020_isElemAbelian_closure ?_ ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hcomm i j
    · rintro _ ⟨i, rfl⟩
      exact hsq i

end Facts

theorem i1021_fi22_two_rank_five
    {F : Type} [Group F]
    (e : F ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) :
    ∃ V : Subgroup F, IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 5 := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b0
  let f : F ≃* J := (e.trans b.symm).trans fi22EquivJ
  obtain ⟨E, hEJ, hE, hEc⟩ := i1021_J_two_rank_five
  obtain ⟨V, hV, hVc⟩ := i1021_transport_elemAbelian hEJ hE f
  exact ⟨V, hV, hVc.trans hEc⟩

end CFSG.HardMathSupport.Solomon.Coordinator
