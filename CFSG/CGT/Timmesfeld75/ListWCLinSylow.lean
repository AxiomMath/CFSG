module

public import CFSG.CGT.Timmesfeld75.ListWCLinBasic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem eq_one_add_single_of_commute_unitri (hm : 3 ≤ m) {u : SL(m, K)}
    (hu : u ∈ unitriangular m K) (hc : ∀ v ∈ unitriangular m K, u * v = v * u) :
    ∃ b : K, (u : Matrix (Fin m) (Fin m) K) =
      1 + single (⟨0, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) b := by
  obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.K1.eq_smul_one_add_single_of_commute (n := m)
    (by omega) (u : Matrix (Fin m) (Fin m) K) (by
      intro i j hij
      have hlt : i < j := by
        rw [Fin.lt_def]
        omega
      have h := congrArg (fun g : SpecialLinearGroup (Fin m) K => (g : Matrix (Fin m) (Fin m) K))
        (hc _ (CFSG.QuasithinUnique.K1.transvection_mem_unitriangular hlt (1 : K)))
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
        mul_add, add_mul, mul_one, one_mul] at h
      exact add_left_cancel h)
  have h00 : a = 1 := by
    have h := hu.2 ⟨0, by omega⟩
    have h' := congrFun₂ hab ⟨0, by omega⟩ ⟨0, by omega⟩
    have e : single (⟨0, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) (1 : K)
        ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 :=
      single_apply_of_ne _ _ _ _ _
        (fun h => CFSG.QuasithinUnique.K1.fin_mk_ne _ _ (by omega) h.2)
    rw [h, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply_eq, e] at h'
    simpa using h'.symm
  refine ⟨b, ?_⟩
  rw [hab, h00, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem single_eq_vecMulVec (i j : Fin m) (b : K) :
    single i j b = vecMulVec (Pi.single i b) (Pi.single j 1) := by
  ext a c
  rw [single_apply, vecMulVec_apply, Pi.single_apply, Pi.single_apply]
  by_cases ha : a = i
  · subst ha
    by_cases hc : c = j
    · subst hc
      simp
    · simp [hc, Ne.symm hc]
  · by_cases hc : c = j
    · subst hc
      simp [ha, Ne.symm ha]
    · simp [ha, hc, Ne.symm ha, Ne.symm hc]

variable [Finite K] [CharP K 2]

theorem exists_tv_mem_of_isWC (hm : 3 ≤ m) {T : Subgroup SL(m, K)} (hT : IsWC T)
    (hT1 : T ≠ ⊥) :
    ∃ t ∈ T, ∃ c φ : Fin m → K, c ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ c = 0 ∧
      (t : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c φ := by
  obtain ⟨P, hTP⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  have hPN : (P : Subgroup SL(m, K)) ≤ Subgroup.normalizer (T : Set SL(m, K)) :=
    hT.le_normalizer_of_le_pGroup P.isPGroup' hTP
  have hnorm : (T.subgroupOf (P : Subgroup SL(m, K))).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1 (hPN g.2) x).1 hx⟩
  have hne : T.subgroupOf (P : Subgroup SL(m, K)) ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hTP hx⟩ : (P : Subgroup SL(m, K))) ∈ T.subgroupOf (P : Subgroup SL(m, K)) := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  have : Group.IsNilpotent (P : Subgroup SL(m, K)) := P.isPGroup'.isNilpotent
  obtain ⟨⟨u, huT, huZ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hu1' : (u : SL(m, K)) ≠ 1 := fun h => hu1 (Subtype.ext (Subtype.ext h))
  have hucomm : ∀ y ∈ (P : Subgroup SL(m, K)), (u : SL(m, K)) * y = y * u := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 huZ ⟨y, hy⟩).symm)
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := m) (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(m, K) P₀ P
  have hmemP : ∀ x, x ∈ (P : Subgroup SL(m, K)) ↔ g⁻¹ * x * g ∈ unitriangular m K := by
    intro x
    rw [← hP₀, ← hg]
    exact mem_smul_sylow_iff_inv_mul_mul_mem
  set t' := g⁻¹ * (u : SL(m, K)) * g with ht'
  have ht'U : t' ∈ unitriangular m K := (hmemP _).1 u.2
  have ht'c : ∀ v ∈ unitriangular m K, t' * v = v * t' := by
    intro v hv
    have hgv : g * v * g⁻¹ ∈ (P : Subgroup SL(m, K)) := by
      rw [hmemP]
      simpa [mul_assoc] using hv
    have h := hucomm _ hgv
    calc t' * v = g⁻¹ * ((u : SL(m, K)) * (g * v * g⁻¹)) * g := by rw [ht']; group
      _ = g⁻¹ * ((g * v * g⁻¹) * u) * g := by rw [h]
      _ = v * t' := by rw [ht']; group
  obtain ⟨b, hb⟩ := eq_one_add_single_of_commute_unitri hm ht'U ht'c
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hu1'
    have h1 : t' = 1 := Subtype.ext (by simpa using hb)
    rw [ht'] at h1
    calc (u : SL(m, K)) = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hm0 : (⟨m - 1, by omega⟩ : Fin m) ≠ ⟨0, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hut : (u : SL(m, K)) = g * t' * g⁻¹ := by rw [ht']; group
  refine ⟨u, huT, (g : Matrix (Fin m) (Fin m) K) *ᵥ Pi.single ⟨0, by omega⟩ b,
    Pi.single ⟨m - 1, by omega⟩ 1 ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K),
    mulVec_ne_zero' g (by simpa using hb0), vecMul_ne_zero' _ (by simp), ?_, ?_⟩
  · rw [← dotProduct_mulVec, inv_mulVec_mulVec', dotProduct_single,
      Pi.single_eq_of_ne hm0.symm, zero_mul]
  · rw [hut, coe_conj_of_coe g (by rw [hb, single_eq_vecMulVec])]

end CFSG.CGT.Timmesfeld75
