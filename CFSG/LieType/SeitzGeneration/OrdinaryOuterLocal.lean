module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcOpp
public import CFSG.LieType.SeitzGeneration.Coprime
public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.GGOppRadExc CFSG.GH74.GLS.Stage2.OddAut


theorem exists_normalized_generating_rSubgroups_adjointGroup
    {τ : CFSG.Blueprint.Chevalley.Tag} {k : Type} [Field k] [Finite k]
    {r : ℕ} [Fact r.Prime] [CharP k r] (hr2 : r ≠ 2)
    [IsSimpleGroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k)]
    (E : Subgroup (MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k)))
    (hE : IsPGroup 2 E)
    (R : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k))
    (hR : R ≠ ⊥) (hRr : IsPGroup r R)
    (hER : ∀ e ∈ E, R.map e.toMonoidHom = R) :
    ∃ U V : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k),
      R ≤ U ∧ IsPGroup r U ∧ IsPGroup r V ∧
      (∀ e ∈ E, U.map e.toMonoidHom = U) ∧
      (∀ e ∈ E, V.map e.toMonoidHom = V) ∧ U ⊔ V = ⊤ := by
  classical
  have hfinGL : Finite (ModGL τ k) := finite_modGL (τ := τ) (K := k)
  have hfinC : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k) := inferInstance
  let U : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k) := radInf r R
  have hRU : R ≤ U := le_radInf R
  have hUstab := exists_radSeq_stable (p := r) hRr
  have hU_p : IsPGroup r U := by
    obtain ⟨n, hRn, -⟩ := hUstab
    rw [show U = radInf r R from rfl, hRn]
    exact radSeq_isPGroup (p := r) hRr n
  have hU_rad : CFSG.Open.pCoreOf r
      (Subgroup.normalizer (U : Set ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k))) = U := by
    obtain ⟨n, hRn, hstab⟩ := hUstab
    rw [show U = radInf r R from rfl, hRn]
    exact hstab
  have hU_ne : U ≠ ⊥ := fun hbot =>
    hR (le_bot_iff.mp (hRU.trans hbot.le))
  have hU_E : ∀ e ∈ E, U.map e.toMonoidHom = U := fun e he => radInf_map_eq e (hER e he)
  have hU_rad' : CFSG.GroupTheory.IsRadicalPGroup r
      (⊤ : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k)) U := by
    unfold CFSG.GroupTheory.IsRadicalPGroup
    simpa only [top_inf_eq] using hU_rad
  let U' : Subgroup (ModGL τ k) :=
    U.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype
  have hU'_rad : CFSG.GroupTheory.IsRadicalPGroup r
      (CFSG.Blueprint.Chevalley.adjointGroup τ k) U' :=
    (CFSG.GroupTheory.isRadicalPGroup_top_map_subtype_iff
      (C := CFSG.Blueprint.Chevalley.adjointGroup τ k) r U).mp hU_rad'
  have hU'_ne : U' ≠ ⊥ := by
    intro hbot
    apply hU_ne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := U)
      (f := (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype)
      (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype_injective).mp hbot
  have hGood' : CFSG.GroupTheory.HasGoodOppositePRadicals r
      (CFSG.Blueprint.Chevalley.adjointGroup τ k) U' :=
    hasGoodOppositePRadicals_adjointGroup_prime r hU'_ne hU'_rad
  have hGood : CFSG.GroupTheory.HasGoodOppositePRadicals r
      (⊤ : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k)) U :=
    CFSG.GroupTheory.hasGoodOppositePRadicals_top_of_map_subtype
      (C := CFSG.Blueprint.Chevalley.adjointGroup τ k) hGood'
  obtain ⟨V, hV, hV_E⟩ := hGood.exists_fixed_of_twoGroup hr2 E hE
    (fun e _ => by simp) hU_E
  refine ⟨U, V, hRU, hU_p, hV.1.isPGroup, hU_E, hV_E, ?_⟩
  obtain ⟨V₀, -, hgen, hconj⟩ := hGood
  obtain ⟨u, hu, huV⟩ := hconj V hV
  have hgen' : U.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype ⊔
      V₀.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype =
        CFSG.Blueprint.Chevalley.adjointGroup τ k := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, Subgroup.range_subtype]
  have hU'conj : (U.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype).map
      (MulAut.conj ((CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype u)).toMonoidHom =
        U.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype := by
    have huU : U.map (MulAut.conj u).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
    rw [← CFSG.GroupTheory.map_subtype_map_conj
      (C := CFSG.Blueprint.Chevalley.adjointGroup τ k) U u, huU]
  have hV'map : V.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype =
      (V₀.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype).map
        (MulAut.conj ((CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype u)).toMonoidHom := by
    rw [huV, CFSG.GroupTheory.map_subtype_map_conj]
  have hAconj : (CFSG.Blueprint.Chevalley.adjointGroup τ k).map
      (MulAut.conj ((CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype u)).toMonoidHom =
        CFSG.Blueprint.Chevalley.adjointGroup τ k :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer u.2)
  have hsum' : U.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype ⊔
      V.map (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype =
        CFSG.Blueprint.Chevalley.adjointGroup τ k := by
    rw [hV'map, ← hU'conj, ← Subgroup.map_sup, hgen', hAconj]
  apply Subgroup.map_injective
    (f := (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype)
    (CFSG.Blueprint.Chevalley.adjointGroup τ k).subtype_injective
  rw [Subgroup.map_sup, hsum', Subgroup.map_top, Subgroup.range_subtype]

theorem planeGen_of_normalized_rSubgroup_adjointGroup
    {τ : CFSG.Blueprint.Chevalley.Tag} {k : Type} [Field k] [Finite k]
    {r : ℕ} [Fact r.Prime] [CharP k r] (hr2 : r ≠ 2)
    [IsSimpleGroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k)]
    (E : Subgroup (MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (R : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k))
    (hR : R ≠ ⊥) (hRr : IsPGroup r R)
    (hER : ∀ e ∈ E, R.map e.toMonoidHom = R) : PlaneGen E := by
  classical
  have hfinGL : Finite (ModGL τ k) := finite_modGL (τ := τ) (K := k)
  have hfinC : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup τ k) := inferInstance
  obtain ⟨U, V, hRU, hU_p, hV_p, hU_E, hV_E, htop⟩ :=
    exists_normalized_generating_rSubgroups_adjointGroup hr2 E hE.isPGroup R hR hRr hER
  have hA : 2 ^ 2 ≤ Nat.card E := by rw [h4]; norm_num
  have hU_odd : ¬ 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hU_p.exists_card_eq
    rw [hn]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr2).pow.not_two_dvd_nat
  have hV_odd : ¬ 2 ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := hV_p.exists_card_eq
    rw [hn]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr2).pow.not_two_dvd_nat
  have hUle : U ≤ planeClosure E :=
    le_planeClosure_of_invariant_coprime hE hA hU_E hU_odd
  have hVle : V ≤ planeClosure E :=
    le_planeClosure_of_invariant_coprime hE hA hV_E hV_odd
  unfold PlaneGen
  rw [eq_top_iff, ← htop]
  exact sup_le hUle hVle

end CFSG.LieType.SeitzGeneration
