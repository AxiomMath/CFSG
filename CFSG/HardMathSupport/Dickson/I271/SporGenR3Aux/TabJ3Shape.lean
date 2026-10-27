module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzC
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerA6
public import Certificates.Certificate12622
public import Certificates.Certificate12624

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.CosetTable
  CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo CFSG.AGLEmbeddingD2.Wilson
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open scoped commutatorElement

section Main


set_option linter.unusedSectionVars false

theorem tabJ3_D_le : closure (Set.range j3tD) ≤ j3P := by
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  exact j3tD_mem i

theorem tabJ3_g_conj : j3tGPerm * j3tXA * j3tGPerm⁻¹ = j3tXA ^ 2 := by
  have hG : validA 6156 j3tG = true := by
    have h := j3t_derived_check.2.2.2.2
    simp only [detOK, Bool.and_eq_true] at h
    exact h.1.1.1
  have hRG : Rep 6156 j3tG j3tGPerm := rep_of_validA hG
  have hRX : Rep 6156 j3tReps[0]! j3tXA := rep_of_validA (j3tReps_spec (c := 0) (by norm_num)).1
  have hc := Certificates.certificate12622
  have e1 : j3tGPerm * j3tXA = (j3tXA * j3tXA) * j3tGPerm :=
    (eqA_iff (rep_compA hRG hRX) (rep_compA (rep_compA hRX hRX) hRG)).1 hc.1
  calc j3tGPerm * j3tXA * j3tGPerm⁻¹ = (j3tXA * j3tXA) * j3tGPerm * j3tGPerm⁻¹ := by rw [e1]
    _ = j3tXA ^ 2 := by rw [pow_two]; group

theorem tabJ3_g_normalizes (x : Equiv.Perm (Fin 6156)) :
    x ∈ closure (Set.range j3tD) ↔ j3tGPerm * x * j3tGPerm⁻¹ ∈ closure (Set.range j3tD) := by
  obtain ⟨eD⟩ := Census228Spor.nonempty_mulEquiv_D_alt6
  have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
  have hDC : closure (Set.range j3tD) ≤
      centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :=
    le_inf Census228Spor.closure_j3tD_le_centralizer tabJ3_D_le
  have hDeq : ⁅centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P,
      centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P⁆ = closure (Set.range j3tD) := by
    refine le_antisymm j3t_derived.1 ?_
    calc closure (Set.range j3tD) = ⁅closure (Set.range j3tD), closure (Set.range j3tD)⁆ :=
          (perfect_of_equiv_alt6 _ eD).symm
      _ ≤ _ := Subgroup.commutator_mono hDC hDC
  have hinj : Function.Injective (MulAut.conj j3tGPerm).toMonoidHom :=
    (MulAut.conj j3tGPerm).injective
  have hCσ : (centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P).map
      (MulAut.conj j3tGPerm).toMonoidHom =
        centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, map_conj_eq_of_mem j3tGPerm_mem, ← centralizer_conj_map',
      tabJ3_g_conj, CFSG.Quasithin.Kleidman.centralizer_pow_eq hA3 (Or.inr rfl)]
  have hDσ : (closure (Set.range j3tD)).map (MulAut.conj j3tGPerm).toMonoidHom =
      closure (Set.range j3tD) := by
    calc (closure (Set.range j3tD)).map (MulAut.conj j3tGPerm).toMonoidHom
        = (⁅centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P,
            centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P⁆).map
              (MulAut.conj j3tGPerm).toMonoidHom := by rw [hDeq]
      _ = ⁅(centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P).map
              (MulAut.conj j3tGPerm).toMonoidHom,
            (centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P).map
              (MulAut.conj j3tGPerm).toMonoidHom⁆ := Subgroup.map_commutator _ _ _
      _ = closure (Set.range j3tD) := by rw [hCσ, hDeq]
  have key := fun y => (Subgroup.mem_map_iff_mem (f := (MulAut.conj j3tGPerm).toMonoidHom)
    (K := closure (Set.range j3tD)) hinj (x := y)).symm
  rw [hDσ] at key
  exact key x

noncomputable abbrev tabJ3U : Equiv.Perm (Fin 6156) := evalW j3tD j3tWu

noncomputable abbrev tabJ3V : Equiv.Perm (Fin 6156) := evalW j3tD j3tWv

theorem tabJ3_evalW_mem {m : ℕ} {G : Type*} [Group G] (g : Fin m → G)
    (w : List (Fin m × Bool)) : evalW g w ∈ closure (Set.range g) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons x w ih =>
    have : evalW g (x :: w) = (cond x.2 (g x.1) (g x.1)⁻¹) * evalW g w := by
      simp [CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW]
    rw [this]
    refine Subgroup.mul_mem _ ?_ ih
    cases x.2
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨x.1, rfl⟩)
    · exact Subgroup.subset_closure ⟨x.1, rfl⟩

theorem tabJ3U_mem : tabJ3U ∈ closure (Set.range j3tD) := tabJ3_evalW_mem _ _

theorem tabJ3V_mem : tabJ3V ∈ closure (Set.range j3tD) := tabJ3_evalW_mem _ _

theorem tabJ3U_pow : tabJ3U ^ 3 = 1 :=
  (eqA_iff (rep_powArr (rep_evalWA_j3tD j3tWu) 3) rep_idA).1
    Certificates.certificate12624.1

theorem tabJ3V_pow : tabJ3V ^ 3 = 1 :=
  (eqA_iff (rep_powArr (rep_evalWA_j3tD j3tWv) 3) rep_idA).1
    Certificates.certificate12624.2.1

theorem tabJ3_uv_comm : Commute tabJ3U tabJ3V := j3t_det.2.2

@[expose] noncomputable def tabJ3Xs : Fin 2 → Equiv.Perm (Fin 6156) := fun i =>
  if i = 0 then tabJ3U else tabJ3V

@[expose] noncomputable def tabJ3UV (m : ℕ) : Equiv.Perm (Fin 6156) :=
  tabJ3U ^ (m / 3) * tabJ3V ^ (m % 3)

theorem rep_tabJ3UV (m : ℕ) : Rep 6156 (Certificates.j3uvElt m) (tabJ3UV m) :=
  rep_compA (rep_powArr (rep_evalWA_j3tD j3tWu) _) (rep_powArr (rep_evalWA_j3tD j3tWv) _)

theorem tabJ3UV_ne {m m' : ℕ} (hm : m < 9) (hm' : m' < m) : tabJ3UV m ≠ tabJ3UV m' := by
  have h := Certificates.certificate12624.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  have h1 := h m hm m' hm'
  intro heq
  have := (eqA_iff (rep_tabJ3UV m) (rep_tabJ3UV m')).2 heq
  rw [this] at h1
  exact absurd h1 (by decide)

theorem tabJ3UV_inj {m m' : ℕ} (hm : m < 9) (hm' : m' < 9) (h : tabJ3UV m = tabJ3UV m') :
    m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h.symm (tabJ3UV_ne hm' hlt)
  · exact heq
  · exact absurd h (tabJ3UV_ne hm hgt)

theorem tabJ3Xs_pow (i : Fin 2) : tabJ3Xs i ^ 3 = 1 := by
  unfold tabJ3Xs
  split_ifs
  · exact tabJ3U_pow
  · exact tabJ3V_pow

theorem tabJ3Xs_comm (i j : Fin 2) : Commute (tabJ3Xs i) (tabJ3Xs j) := by
  unfold tabJ3Xs
  split_ifs
  · exact Commute.refl _
  · exact tabJ3_uv_comm
  · exact tabJ3_uv_comm.symm
  · exact Commute.refl _

theorem basisProd_tabJ3Xs (a : Fin 2 → ZMod 3) :
    basisProd tabJ3Xs a = tabJ3UV (3 * (a 0).val + (a 1).val) := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have e1 : (3 * (a 0).val + (a 1).val) / 3 = (a 0).val := by omega
  have e2 : (3 * (a 0).val + (a 1).val) % 3 = (a 1).val := by omega
  rw [tabJ3UV, e1, e2]
  simp [basisProd, List.ofFn_succ, tabJ3Xs]

theorem tabJ3Xs_inj : Function.Injective (basisProd tabJ3Xs) := by
  intro a b h
  rw [basisProd_tabJ3Xs, basisProd_tabJ3Xs] at h
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have g0 := ZMod.val_lt (b 0)
  have g1 := ZMod.val_lt (b 1)
  have := tabJ3UV_inj (by omega) (by omega) h
  funext i
  fin_cases i
  · exact ZMod.val_injective 3 (by simp only [Fin.zero_eta]; omega)
  · exact ZMod.val_injective 3 (by simp only [Fin.mk_one]; omega)

theorem tabJ3_u_mem : tabJ3U ∈ closure (Set.range tabJ3Xs) :=
  Subgroup.subset_closure ⟨0, by simp [tabJ3Xs]⟩

theorem tabJ3_v_mem : tabJ3V ∈ closure (Set.range tabJ3Xs) :=
  Subgroup.subset_closure ⟨1, by simp [tabJ3Xs]⟩

theorem tabJ3_E3_le : closure (Set.range tabJ3Xs) ≤ closure (Set.range j3tD) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  unfold tabJ3Xs
  split_ifs
  · exact tabJ3U_mem
  · exact tabJ3V_mem

theorem tabJ3_E3_card : Nat.card (closure (Set.range tabJ3Xs)) = 9 := by
  rw [card_closure_basis tabJ3Xs_pow tabJ3Xs_comm tabJ3Xs_inj]
  norm_num

theorem tabJ3_E3_gen :
    ∀ g ∈ closure (Set.range tabJ3Xs), ∃ i j : ℕ, g = tabJ3U ^ i * tabJ3V ^ j := by
  intro g hg
  obtain ⟨a, ha⟩ := basisHom_surjective tabJ3Xs_pow tabJ3Xs_comm ⟨g, hg⟩
  have hga : g = basisProd tabJ3Xs (Multiplicative.toAdd a) := by
    rw [← coe_basisHom tabJ3Xs_pow tabJ3Xs_comm, ha]
  rw [hga, basisProd_tabJ3Xs]
  exact ⟨_, _, rfl⟩

theorem tabJ3_a6Split3 : A6Split3 ((closure (Set.range j3tD)).comap j3P.subtype) := by
  obtain ⟨eD⟩ := Census228Spor.nonempty_mulEquiv_D_alt6
  have h1 : j3tGPerm * tabJ3U * j3tGPerm⁻¹ = tabJ3U ^ 0 * tabJ3V ^ 1 := by
    simpa using j3t_det.1
  have h2 : j3tGPerm * tabJ3V * j3tGPerm⁻¹ = tabJ3U ^ 1 * tabJ3V ^ 1 := by
    simpa using j3t_det.2.1
  exact a6Split3_comap_subtype j3P (closure (Set.range j3tD)) tabJ3_D_le eD j3tGPerm_mem
    (tabJ3_D_le tabJ3U_mem) (tabJ3_D_le tabJ3V_mem) (closure (Set.range tabJ3Xs))
    tabJ3_g_normalizes tabJ3_E3_le tabJ3_E3_card tabJ3_u_mem tabJ3_v_mem tabJ3_uv_comm.eq
    tabJ3_E3_gen h1 h2 (by decide)

theorem splitShapeAt_j3A (y : ↥j3P)
    (hy : Subgroup.centralizer ({(y : Equiv.Perm (Fin 6156))} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156)))) : SplitShapeAt 3 y := by
  obtain ⟨eD⟩ := Census228Spor.nonempty_mulEquiv_D_alt6
  have hDC : closure (Set.range j3tD) ≤
      centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :=
    le_inf Census228Spor.closure_j3tD_le_centralizer tabJ3_D_le
  refine splitShapeAt_of_subgroup_data j3P y (closure (Set.range j3tD)) (by rw [hy]; exact hDC)
    ?_ eD (k := 1) ?_ tabJ3_a6Split3
  · intro g hg l hl
    rw [hy] at hg
    have h1 : ⁅g, l⁆ ∈ ⁅centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P,
        centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P⁆ :=
      Subgroup.commutator_mem_commutator hg (hDC hl)
    have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (closure (Set.range j3tD)).mul_mem (j3t_derived.1 h1) hl
  · rw [hy, Census228Spor.card_centralizer_XA, j3t_derived.2]
    norm_num

theorem splitShapeAt_j3B (y : ↥j3P)
    (hy : Subgroup.centralizer ({(y : Equiv.Perm (Fin 6156))} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer ({j3tXB} : Set (Equiv.Perm (Fin 6156)))) : SplitShapeAt 3 y := by
  refine Or.inl (pConstrainedShape_of_map_injective j3P.subtype j3P.subtype_injective ?_)
  rw [map_centralizer_subtype', hy]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥(centralizer ({j3tXB} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P) :=
    IsPGroup.of_card (n := 5) (by rw [Census228Spor.card_centralizer_XB]; norm_num)
  exact ⟨_, le_rfl, fun g hg q hq => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hq)
    (Subgroup.inv_mem _ hg), hp, inf_le_left⟩


theorem centShapeSplit_j3P : CentShapeSplit 3 ↥j3P := by
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 6156)) = 3 := by
    have h1 : (k : Equiv.Perm (Fin 6156)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 6156)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨k₀, hk₀, c, hc, e, he, hkeq⟩ := j3t_fusion k.2 hs3
  let K₀ : ↥j3P := ⟨k₀, hk₀⟩
  let y : ↥j3P := K₀⁻¹ * k * K₀
  have hy : (y : Equiv.Perm (Fin 6156)) = c ^ e := by
    show k₀⁻¹ * (k : Equiv.Perm (Fin 6156)) * k₀ = c ^ e
    rw [hkeq]
    group
  have hshape : SplitShapeAt 3 y := by
    rcases hc with rfl | rfl
    · refine splitShapeAt_j3A y ?_
      rw [hy]
      exact CFSG.Quasithin.Kleidman.centralizer_pow_eq (j3tReps_spec (c := 0) (by norm_num)).2 he
    · refine splitShapeAt_j3B y ?_
      rw [hy]
      exact CFSG.Quasithin.Kleidman.centralizer_pow_eq (j3tReps_spec (c := 1) (by norm_num)).2 he
  have hconj := SplitShapeAt.conj Nat.prime_three K₀ hshape
  have hk : K₀ * y * K₀⁻¹ = k := by
    simp only [y]
    group
  rw [hk] at hconj
  exact hconj

theorem centShapeSplit_J3 : CentShapeSplit 3 (NativeSporadic.Carrier .J3) := by
  have e : NativeSporadic.Carrier .J3 ≃* ↥j3P := Sec21.Item228CensusProof.j3CarrierEquiv
  haveI : Finite (NativeSporadic.Carrier .J3) := Finite.of_equiv ↥j3P e.symm.toEquiv
  exact CentShapeSplit.of_equiv Nat.prime_three e.symm centShapeSplit_j3P

end Main

end CFSG.HardMathSupport.Dickson.I271
