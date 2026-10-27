module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpPoint
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.CycFour

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer borelCuts)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual

variable {r : ℕ} {K : Type} [Field K]

theorem exists_flag_blockBar [Finite K] [CharP K 2] {J : Subgroup (StatedSp r K)}
    {v : StatedSp r K} (h : BlockBarData J v) :
    ∃ (g : StatedSp r K) (I : Set ℕ) (v' : StatedSp r K), (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧
      I.Nonempty ∧ BlockBarData (flagStabilizer r K I) v' ∧
      ∀ x, x ∈ J ↔ g * x * g⁻¹ ∈ flagStabilizer r K I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ⟩ := h.parab
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  let T' : Sylow 2 (StatedSp r K) := hT.2.1.toSylow hidx
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp r K) U T'
  have hTx : T = (SymplecticFlag.unipotent r K).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • U : Sylow 2 (StatedSp r K)) : Subgroup (StatedSp r K)) = T := by
      rw [hx]; rfl
    rw [← h1, Sylow.coe_subgroup_smul, hU]
    rfl
  let e : StatedSp r K ≃* StatedSp r K := MulAut.conj x⁻¹
  have heT : T.map e.toMonoidHom = SymplecticFlag.unipotent r K := by
    rw [hTx, Subgroup.map_map]
    have : e.toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [this, Subgroup.map_id]
  have hbij : Function.Bijective e.toMonoidHom := e.bijective
  have hNmap : (Subgroup.normalizer (T : Set (StatedSp r K))).map e.toMonoidHom =
      SymplecticFlag.borelSubgroup r K := by
    rw [Subgroup.map_normalizer_eq_of_bijective T hbij, heT]
    exact SymplecticHigher.normalizer_unipotent
  have hh := h.map_mulEquiv e
  have hB : SymplecticFlag.borelSubgroup r K ≤ J.map e.toMonoidHom := by
    rw [← hNmap]
    exact Subgroup.map_mono hNJ
  obtain ⟨I, hI, hJ'⟩ : ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧
      J.map e.toMonoidHom = flagStabilizer r K I :=
    ⟨borelCuts K (J.map e.toMonoidHom), SymplecticHigher.borelCuts_le _,
      (SymplecticHigher.borel_overgroups _ hB).1⟩
  rw [hJ'] at hh
  refine ⟨x⁻¹, I, e v, hI, ?_, hh, fun y => ?_⟩
  · by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hh.ne_top
    rw [hne, SymplecticHigher.flagStabilizer_empty]
  · rw [← hJ']
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := e.injective hzy
      rw [← this]; exact hz

theorem eq_singleton_of_forall {I : Set ℕ} (hne : I.Nonempty) {k : ℕ} (h : ∀ j ∈ I, j = k) :
    I = {k} := by
  ext j
  simp only [Set.mem_singleton_iff]
  refine ⟨h j, fun hj => ?_⟩
  obtain ⟨i, hi⟩ := hne
  rw [hj, ← h i hi]; exact hi

theorem blockBar_sp_cases {r : ℕ} (hr : r = 3 ∨ r = 4) {J : Subgroup (StatedSp r (ZMod 2))}
    {v : StatedSp r (ZMod 2)} (h : BlockBarData J v) :
    r = 3 ∧ ∃ g : StatedSp r (ZMod 2),
      ∀ x, x ∈ J ↔ g * x * g⁻¹ ∈ flagStabilizer r (ZMod 2) {3} := by
  obtain ⟨g, I, v', hI, hne, hh, hJ⟩ := exists_flag_blockBar h
  have hK : KillData r I v' := ⟨hI, hh.join, hh.pow, hh.ne_one, hh.free⟩
  have h2 : 2 ∉ I := fun h2 => hK.false_of_two_mem h2
  rcases hr with rfl | rfl
  · by_cases h3 : 3 ∈ I
    · by_cases h1 : 1 ∈ I
      · exact (hK.false_of_one_three_mem h1 h3).elim
      · have hI3 : I = {3} := eq_singleton_of_forall hne fun j hj => by
          have := hI j hj
          have : j ≠ 2 := fun h => h2 (h ▸ hj)
          have : j ≠ 1 := fun h => h1 (h ▸ hj)
          omega
        subst hI3
        exact ⟨rfl, g, hJ⟩
    · have hI1 : I = {1} := eq_singleton_of_forall hne fun j hj => by
        have := hI j hj
        have : j ≠ 2 := fun h => h2 (h ▸ hj)
        have : j ≠ 3 := fun h => h3 (h ▸ hj)
        omega
      subst hI1
      exact (false_of_cyc_point (by norm_num) hh.cyc).elim
  · have h3 : 3 ∉ I := fun h3 => hK.false_of_pred_mem h3 (by decide) rfl
    by_cases h4 : 4 ∈ I
    · by_cases h1 : 1 ∈ I
      · exact (hK.false_of_even_odd h4 (by decide) h1 (by decide) (by norm_num)).elim
      · have hI4 : I = {4} := eq_singleton_of_forall hne fun j hj => by
          have := hI j hj
          have : j ≠ 2 := fun h => h2 (h ▸ hj)
          have : j ≠ 3 := fun h => h3 (h ▸ hj)
          have : j ≠ 1 := fun h => h1 (h ▸ hj)
          omega
        subst hI4
        exact (CycFour.false_of_cyc_lagrangian_four hh.cyc).elim
    · have hI1 : I = {1} := eq_singleton_of_forall hne fun j hj => by
        have := hI j hj
        have : j ≠ 2 := fun h => h2 (h ▸ hj)
        have : j ≠ 3 := fun h => h3 (h ▸ hj)
        have : j ≠ 4 := fun h => h4 (h ▸ hj)
        omega
      subst hI1
      exact (false_of_cyc_point (by norm_num) hh.cyc).elim

end CFSG.HardMathSupport.Curtis.UnitaryLevi
