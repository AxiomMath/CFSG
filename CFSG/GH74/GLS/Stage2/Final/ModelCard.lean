module

public import CFSG.GH74.GLS.Stage2.Final.ModelComps

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def negNeg (M : ModelData F) : ↥M.H2 × ↥M.H2 :=
  (⟨-1, M.neg_one_mem_H2⟩, ⟨-1, M.neg_one_mem_H2⟩)

theorem negNeg_sq (M : ModelData F) : negNeg M * negNeg M = 1 := by
  ext <;> simp [negNeg]

theorem negNeg_ne_one {M : ModelData F} (h2 : (2 : F) ≠ 0) : negNeg M ≠ 1 := by
  intro h
  have := congrArg (fun p : ↥M.H2 × ↥M.H2 => ((p.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [negNeg] at this
  apply h2
  linear_combination -this

theorem orderOf_negNeg {M : ModelData F} (h2 : (2 : F) ≠ 0) : orderOf (negNeg M) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact negNeg_sq M) (negNeg_ne_one h2)

theorem ker_iotaE [Finite F] {M : ModelData F} (hG : GoodModel M) :
    (iotaE M).ker = Subgroup.zpowers (negNeg M) := by
  have h2 := hG.two_ne_zero
  ext ⟨a, b⟩
  constructor
  · intro h
    rw [MonoidHom.mem_ker, iotaE_apply] at h
    have h1 : iota1 M a = iota2 M b⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left h
    obtain ⟨l, hl⟩ := iota1_eq_iota2_scalar a b⁻¹ h1
    have hdet := ((M.mem_H2 _).1 a.2).2
    rw [hl, det_sc2] at hdet
    have hll : l * l = 1 := Units.ext (by simpa [sq] using hdet)
    rcases units_sq_eq_one hll with rfl | rfl
    ·
      have ha : a = 1 := Subtype.ext (by rw [hl, sc2_one]; rfl)
      rw [ha, map_one] at h1
      have hb : b⁻¹ = 1 := iota2_injective M (by rw [map_one]; exact h1.symm)
      have hb' : b = 1 := inv_eq_one.1 hb
      rw [ha, hb']
      exact Subgroup.one_mem _
    · have ha : a = ⟨-1, M.neg_one_mem_H2⟩ := Subtype.ext (by
        rw [hl]; exact CFSG.GH74.L5U5.scalar_neg_one_eq (F := F) 2)
      rw [ha, iota1_negOne, ← iota2_negOne M] at h1
      have hb : b⁻¹ = ⟨-1, M.neg_one_mem_H2⟩ := iota2_injective M h1.symm
      have hb' : b = ⟨-1, M.neg_one_mem_H2⟩ := by
        have : b = (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2)⁻¹ := inv_eq_iff_eq_inv.1 hb
        rw [this]
        apply Subtype.ext
        show ((-1 : GL (Fin 2) F))⁻¹ = -1
        simp
      rw [ha, hb']
      exact ⟨1, by simp [negNeg]⟩
  · intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [MonoidHom.mem_ker, ← hn, map_zpow]
    have : iotaE M (negNeg M) = 1 := by
      rw [negNeg, iotaE_apply, iota1_negOne, iota2_negOne, yP_sq]
    rw [this, _root_.one_zpow]

theorem two_mul_card_Ebar [Finite F] {M : ModelData F} (hG : GoodModel M) :
    2 * Nat.card ↥(K1 M ⊔ K2 M) = Nat.card ↥M.H2 ^ 2 := by
  have h := Subgroup.card_ker_mul_card_range (iotaE M)
  rw [ker_iotaE hG, Nat.card_zpowers, orderOf_negNeg hG.two_ne_zero, range_iotaE, Nat.card_prod] at h
  rw [sq]
  exact h


theorem card_Zs_two {M : ModelData F} (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) : Nat.card ↥(Zs M) = 2 := by
  have : Zs M = Subgroup.zpowers M.xK := by
    apply le_antisymm
    · intro s hs
      rcases hZ s hs with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact xK_mem_Zs M
  rw [this, Nat.card_zpowers, M.orderOf_xK h2]

theorem card_Cg_mul_Zs [Finite F] (M : ModelData F) :
    Nat.card ↥(Cg M) * Nat.card ↥(Zs M) = Nat.card ↥(Nsub M) := by
  have h := Subgroup.card_ker_mul_card_range ((mkP M).comp (Nsub M).subtype)
  have hr : ((mkP M).comp (Nsub M).subtype).range = Cg M := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact (centralizer_yP M).symm
  have hker : (mkP M).ker ≤ Nsub M := (ker_mkP_le_D M).trans (Dsub_le_Nsub M)
  have hk : Nat.card ((mkP M).comp (Nsub M).subtype).ker = Nat.card ↥(Zs M) := by
    rw [← MonoidHom.comap_ker]
    show Nat.card ↥((mkP M).ker.subgroupOf (Nsub M)) = _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv, QuotientGroup.ker_mk']
  rw [hk, hr] at h
  rw [mul_comm]
  exact h

theorem card_Cg_eq_UH [Finite F] {M : ModelData F} (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) :
    Nat.card ↥(Cg M) = Nat.card ↥M.U2 * Nat.card ↥M.H2 := by
  have h1 := card_Cg_mul_Zs M
  rw [card_Zs_two h2 hZ, card_Nsub M h2, ModelOrd.card_centralizer_yK M h2] at h1
  omega

theorem card_Cg_eq [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M) {m : ℕ}
    (hm : Nat.card ↥M.U2 = Nat.card ↥M.H2 * m) :
    Nat.card ↥(Cg M) = 2 * m * Nat.card ↥(K1 M ⊔ K2 M) := by
  have h1 := card_Cg_eq_UH hG.two_ne_zero hZ
  have h2 := two_mul_card_Ebar hG
  rw [hm] at h1
  have : Nat.card ↥(Cg M) = m * Nat.card ↥M.H2 ^ 2 := by rw [h1]; ring
  rw [this, ← h2]
  ring

theorem card_U2_lin [Finite F] :
    Nat.card ↥(ModelData.lin F).U2 = Nat.card ↥(ModelData.lin F).H2 * (Nat.card F - 1) := by
  have h1 : Nat.card ↥(ModelData.lin F).U2 = Nat.card (GL (Fin 2) F) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [h1, ModelOrd.card_gl_two]
  show _ = Nat.card ↥(StatedSL 2 F) * _
  rw [ModelOrd.card_statedSL_two]
  ring

theorem card_U2_sp [Finite F] :
    Nat.card ↥(ModelData.sp F).U2 = Nat.card ↥(ModelData.sp F).H2 * 1 := by
  rw [mul_one, ModelSp.H2_sp_eq_U2]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem card_U2_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Nat.card ↥(ModelData.uni hF).U2 = Nat.card ↥(ModelData.uni hF).H2 * (p ^ f + 1) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact hf
  have h : UnitaryFieldData p f F := ⟨Fact.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hH : (Nat.card ↥(ModelData.uni hF).H2 : ℤ) =
      ((p ^ f : ℕ) : ℤ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
    have := ModelOrd.card_statedSU_int h (n := 2) (by norm_num)
    rw [ModelOrd.prod_Icc_two_two, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
    exact this
  have hU : (Nat.card ↥(ModelData.uni hF).U2 : ℤ) =
      ((p ^ f : ℕ) : ℤ) * ((((p ^ f : ℕ) : ℤ) + 1) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1)) := by
    have := ModelOrd.card_uniGL_int h (n := 2) (by norm_num)
    rw [ModelOrd.prod_Icc_one_two, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
    exact this
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hU, hH]
  ring

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

