module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMon

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Equiv Subgroup
open scoped commutatorElement

abbrev C5 : Type := Multiplicative (ZMod 5)

abbrev M5 : Type := Mon C5 5

theorem c5_pow_five (c : C5) : c ^ 5 = 1 := by
  revert c
  decide

theorem card_C5 : Nat.card C5 = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def sig5 : Perm (Fin 5) := finRotate 5

theorem sig5_pow_five : sig5 ^ 5 = 1 := by decide

theorem sig5_ne_one : sig5 ≠ 1 := by decide

theorem orderOf_sig5 : orderOf sig5 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime sig5_pow_five sig5_ne_one

theorem sig5_apply (i : Fin 5) : sig5 i = i + 1 := finRotate_succ_apply i

@[expose] def Pm : Subgroup M5 := (zpowers sig5).comap monPerm

@[expose] def T5 : Subgroup M5 := (SemidirectProduct.inl : (Fin 5 → C5) →* M5).range

@[expose] def Sc : Subgroup M5 := (monScalar C5 5).range

@[expose] def T0 : Subgroup M5 := T5 ⊓ (monDet : M5 →* C5).ker

theorem mem_Pm {x : M5} : x ∈ Pm ↔ x.right ∈ zpowers sig5 := Iff.rfl

theorem T5_eq_ker : T5 = (monPerm : M5 →* Perm (Fin 5)).ker := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact monPerm_monT t
  · intro hx
    exact ⟨x.left, (eq_monT_of_right_eq_one (MonoidHom.mem_ker.mp hx)).symm⟩

theorem mem_T5 {x : M5} : x ∈ T5 ↔ x = monT x.left := by
  rw [T5_eq_ker, MonoidHom.mem_ker]
  exact ⟨fun h => eq_monT_of_right_eq_one h, fun h => by rw [h, monPerm_monT]⟩

instance : T5.Normal := by
  rw [T5_eq_ker]
  infer_instance

theorem monT_mem_T5 (t : Fin 5 → C5) : monT t ∈ T5 := ⟨t, rfl⟩

theorem T5_le_Pm : T5 ≤ Pm := by
  intro x hx
  rw [T5_eq_ker, MonoidHom.mem_ker] at hx
  rw [mem_Pm]
  have : x.right = 1 := hx
  rw [this]
  exact one_mem _

theorem Sc_le_T5 : Sc ≤ T5 := by
  rintro _ ⟨c, rfl⟩
  exact monT_mem_T5 _

theorem monS_zpow_mem_Pm (k : ℤ) : monS (C := C5) (sig5 ^ k) ∈ Pm := by
  rw [mem_Pm]
  have : (monS (C := C5) (sig5 ^ k)).right = sig5 ^ k := rfl
  rw [this]
  exact zpow_mem (mem_zpowers sig5) k

theorem monDet_monScalar (c : C5) : monDet (monScalar C5 5 c) = 1 := by
  rw [monScalar_apply, monDet_monT]
  simp [c5_pow_five]

theorem Sc_le_T0 : Sc ≤ T0 := by
  rintro _ ⟨c, rfl⟩
  exact ⟨monT_mem_T5 _, monDet_monScalar c⟩

theorem card_T5 : Nat.card T5 = 5 ^ 5 := by
  unfold T5
  rw [← Nat.card_congr (MonoidHom.ofInjective (SemidirectProduct.inl_injective
    (φ := permAct C5 5) (G := Perm (Fin 5)))).toEquiv, Nat.card_fun, Nat.card_fin, card_C5]

theorem card_Sc : Nat.card Sc = 5 := by
  have hinj : Function.Injective (monScalar C5 5) := by
    intro a b h
    have := SemidirectProduct.inl_injective (φ := permAct C5 5) (G := Perm (Fin 5)) h
    exact congrFun this 0
  unfold Sc
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_C5]

theorem sig5_symm_apply (i : Fin 5) : sig5.symm i = i - 1 := by
  rw [Equiv.symm_apply_eq, sig5_apply, sub_add_cancel]

theorem T0_eq_map : T0 = ((entryProd C5 5).ker).map
    (SemidirectProduct.inl : (Fin 5 → C5) →* M5) := by
  ext x
  constructor
  · rintro ⟨hx5, hx⟩
    refine ⟨x.left, ?_, (mem_T5.mp hx5).symm⟩
    have h1 := MonoidHom.mem_ker.mp hx
    rw [mem_T5.mp hx5, monDet_monT] at h1
    exact h1
  · rintro ⟨t, ht, rfl⟩
    refine ⟨monT_mem_T5 t, ?_⟩
    have h1 : (entryProd C5 5) t = 1 := ht
    change monDet (monT t) = 1
    rw [monDet_monT]
    exact h1

theorem card_T0 : Nat.card T0 = 5 ^ 4 := by
  rw [T0_eq_map, Subgroup.card_map_of_injective (SemidirectProduct.inl_injective
    (φ := permAct C5 5) (G := Perm (Fin 5))),
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU.card_entryProd_ker (by norm_num : 1 ≤ 5),
    card_C5]

theorem comm_monT_left (s : Fin 5 → C5) (x : M5) :
    ⁅monT s, x⁆ = monT ((s ∘ x.right.symm)⁻¹ * s) := by
  rw [← commutatorElement_inv, mon_comm_monT, ← monT_inv, mul_inv_rev, inv_inv, mul_comm]

theorem commutator_T5_Pm : ⁅T5, Pm⁆ = T0 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro t ht x hx
    obtain ⟨s, rfl⟩ := ht
    refine ⟨?_, ?_⟩
    · have : ⁅(SemidirectProduct.inl s : M5), x⁆ = (SemidirectProduct.inl s) *
          (x * (SemidirectProduct.inl s)⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact T5.mul_mem ⟨s, rfl⟩ (Subgroup.Normal.conj_mem inferInstance _ (T5.inv_mem ⟨s, rfl⟩) x)
    · have h1 : (monDet : M5 →* C5) ⁅(SemidirectProduct.inl s : M5), x⁆ = 1 := by
        rw [map_commutatorElement]
        simp [commutatorElement_def, mul_comm]
      exact h1
  · rintro x ⟨hx5, hx⟩
    have hxe := mem_T5.mp hx5
    have h1 := MonoidHom.mem_ker.mp hx
    rw [hxe, monDet_monT] at h1
    set s : Fin 5 → C5 := x.left with hs
    have hprod : s 0 * s 1 * s 2 * s 3 * s 4 = 1 := by
      simpa [Fin.prod_univ_five] using h1
    let t : Fin 5 → C5 := ![1, s 1, s 1 * s 2, s 1 * s 2 * s 3, s 1 * s 2 * s 3 * s 4]
    have hσ : monS (C := C5) sig5 ∈ Pm := by
      have := monS_zpow_mem_Pm 1
      rwa [zpow_one] at this
    have hcomm := Subgroup.commutator_mem_commutator (monT_mem_T5 t) hσ
    have hxt : x = ⁅monT t, monS (C := C5) sig5⁆ := by
      rw [comm_monT_left, hxe]
      congr 1
      funext i
      have hmon : (monS (C := C5) sig5).right = sig5 := rfl
      simp only [hmon, Function.comp_apply, Pi.mul_apply, Pi.inv_apply, sig5_symm_apply]
      fin_cases i
      · simp [t]
        have h : s 0 = (s 1 * s 2 * s 3 * s 4)⁻¹ :=
          eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using hprod)
        rw [h]
        group
      · simp [t]
      · simp [t]
      · simp [t]
        group
      · simp [t]
        group
    rw [hxt]
    exact hcomm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
