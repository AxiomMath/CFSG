module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413Frame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L413Conj

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG.LieType.Universal.Spin Subgroup
open scoped MatrixGroups

namespace L413

variable {K : Type} [Field K]

@[expose] def Clauses (x : spinGroup (quadPlus 4 K))
    (J : ↥(center (spinGroup (quadPlus 4 K))) → Subgroup (spinGroup (quadPlus 4 K))) : Prop :=
  (∀ c, J c ≤ centralizer {x}) ∧ (∀ c, Nonempty (↥(J c) ≃* SL(2, K))) ∧
    (∀ c, x * (c : spinGroup (quadPlus 4 K)) ∈ J c) ∧
    (∀ c d, c ≠ d → ∀ a ∈ J c, ∀ b ∈ J d, a * b = b * a) ∧
    (∀ c, centralizer {x} ≤ normalizer (J c : Set (spinGroup (quadPlus 4 K)))) ∧
    ∀ (β : MulAut (spinGroup (quadPlus 4 K))) (c d : ↥(center (spinGroup (quadPlus 4 K)))),
      β (x * (c : spinGroup (quadPlus 4 K))) = x * (d : spinGroup (quadPlus 4 K)) →
        (J c).map β.toMonoidHom = J d

theorem Clauses.conj {y : spinGroup (quadPlus 4 K)}
    {J : ↥(center (spinGroup (quadPlus 4 K))) → Subgroup (spinGroup (quadPlus 4 K))}
    (h : Clauses y J) (g : spinGroup (quadPlus 4 K)) :
    Clauses (g * y * g⁻¹) fun c => (J c).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ := h
  have hcen : ∀ c : ↥(center (spinGroup (quadPlus 4 K))),
      g * y * g⁻¹ * (c : spinGroup (quadPlus 4 K)) = g * (y * c) * g⁻¹ := fun c => by
    rw [mul_assoc (g * y), mem_center_iff.mp c.2 g⁻¹]
    simp only [mul_assoc]
  have hcent : centralizer ({g * y * g⁻¹} : Set (spinGroup (quadPlus 4 K))) ≤
      (centralizer {y}).map (MulAut.conj g).toMonoidHom := by
    intro h hh
    refine ⟨g⁻¹ * h * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [mem_centralizer_singleton_iff] at hh
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    calc g⁻¹ * h * g * y = g⁻¹ * (h * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * h) * g := by rw [hh]
      _ = y * (g⁻¹ * h * g) := by group
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun c d hcd => ?_, fun c => ?_,
    fun β c d hβ => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have ha' := mem_centralizer_singleton_iff.mp (hA c ha)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * y * g⁻¹) = g * (a * y) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by rw [ha']
      _ = g * y * g⁻¹ * (g * a * g⁻¹) := by group
  · obtain ⟨e⟩ := hB c
    exact ⟨((J c).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e⟩
  · rw [hcen]
    exact ⟨_, hC c, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hD c d hcd a ha b hb]
  · exact hcent.trans ((map_mono (hE c)).trans (le_normalizer_map _))
  · set γ : MulAut (spinGroup (quadPlus 4 K)) := (MulAut.conj g)⁻¹ * β * MulAut.conj g
      with hγ
    have hγc : γ (y * c) = y * d := by
      rw [hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, ← hcen, hβ,
        MulAut.inv_apply]
      rw [show (MulAut.conj g).symm (g * y * g⁻¹ * (d : spinGroup (quadPlus 4 K))) =
          g⁻¹ * (g * y * g⁻¹ * d) * g from rfl]
      have hd := (mem_center_iff.mp d.2 g).symm
      calc g⁻¹ * (g * y * g⁻¹ * d) * g = y * g⁻¹ * (d * g) := by group
        _ = y * g⁻¹ * (g * d) := by rw [hd]
        _ = y * d := by group
    have hmap := hF γ c d hγc
    show ((J c).map (MulAut.conj g).toMonoidHom).map β.toMonoidHom =
      (J d).map (MulAut.conj g).toMonoidHom
    rw [← hmap, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun a => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hγ, MulAut.mul_apply,
      MulAut.conj_apply, MulAut.inv_apply]
    rw [show (MulAut.conj g).symm (β (g * a * g⁻¹)) = g⁻¹ * β (g * a * g⁻¹) * g from rfl]
    group

variable (K) in
@[expose] noncomputable def idx (c : ↥(center (spinGroup (quadPlus 4 K)))) : Fin 4 :=
  (exists_inv4_eq c.2).choose

theorem inv4_mul_eq_idx (c : ↥(center (spinGroup (quadPlus 4 K)))) :
    inv4 K 1 * c = inv4 K (idx K c) :=
  (exists_inv4_eq c.2).choose_spec

theorem clauses_inv4_mul [Finite K] (hodd : Odd (Nat.card K)) (h3K : 3 ≤ Nat.card K)
    (h3 : (3 : K) = 0) (c₀ : ↥(center (spinGroup (quadPlus 4 K)))) :
    Clauses (inv4 K 1 * (c₀ : spinGroup (quadPlus 4 K))) fun c =>
      (rt K (idx K (c₀ * c))).range := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hC : centralizer ({inv4 K 1 * (c₀ : spinGroup (quadPlus 4 K))} : Set _) =
      centralizer {inv4 K 1} := centralizer_mul_central _ c₀.2
  have hx : ∀ c : ↥(center (spinGroup (quadPlus 4 K))),
      inv4 K 1 * c₀ * (c : spinGroup (quadPlus 4 K)) = inv4 K (idx K (c₀ * c)) := fun c => by
    rw [← inv4_mul_eq_idx, mul_assoc]
    rfl
  refine ⟨fun c => ?_, fun c => ⟨(MonoidHom.ofInjective (rt_injective _)).symm⟩,
    fun c => ?_, fun c d hcd => ?_, fun c => ?_, fun β c d hβ => ?_⟩
  · rw [hC]
    exact rt_le_centralizer _
  · rw [hx]
    exact inv4_mem _
  · have hne : idx K (c₀ * c) ≠ idx K (c₀ * d) := by
      intro h
      apply hcd
      have h' : inv4 K 1 * c₀ * (c : spinGroup (quadPlus 4 K)) =
          inv4 K 1 * c₀ * (d : spinGroup (quadPlus 4 K)) := by rw [hx, hx, h]
      exact Subtype.ext (mul_left_cancel h')
    exact fun a ha b hb => commute_rt hne ha hb
  · rw [hC]
    exact centralizer_le_normalizer_rt h2 _
  · rw [hx, hx] at hβ
    exact map_rt_range hodd h3K h3 β hβ

theorem three_eq_zero_of_card [Finite K] {f : ℕ} (hK : Nat.card K = 3 ^ f) (hf : f ≠ 0) :
    (3 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK, Nat.cast_pow, Nat.cast_ofNat] at h
  exact (pow_eq_zero_iff hf).mp h

end L413

open L413 in
theorem harris82Lemma413Three_holds : Harris82Lemma413Three := by
  intro K _ _ f hK x hx hxZ
  have hodd : Odd (Nat.card K) := hK ▸ Odd.pow (by decide)
  have hf : f ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    exact lt_irrefl _ this
  have h3K : 3 ≤ Nat.card K := hK ▸ Nat.le_self_pow hf 3
  obtain ⟨g, c₀, hc₀, rfl⟩ := exists_conj_inv4_mul hodd hx hxZ
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ :=
    (clauses_inv4_mul hodd h3K (three_eq_zero_of_card hK hf) ⟨c₀, hc₀⟩).conj g
  refine ⟨_, hA, hB, hC, hD, fun c => ?_, hF⟩
  exact (normal_subgroupOf_of_le_normalizer (hE c)).isSubnormal

end CFSG.ComponentClassification.HarrisLit.T1
