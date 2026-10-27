module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.L34E9
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.Sporadic.ONOddCore.OuterQuot
public import CFSG.RankThree.Native.ONThreeFusion
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.RankThree.Native
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.PSL3Four
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem tSL_pow_three : tSL ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change tMat ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem pSL_pow_three : pSL ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change pMat ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem proj_tSL_ne_one : proj 3 F4 tSL ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  change tMat 0 0 = _ at h00
  change tMat 1 1 = _ at h11
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00 h11
  exact absurd (h00.trans h11.symm) (by decide)

theorem tSL_mul_pSL :
    tSL * pSL = scalarElement (Units.mk0 F4.ω (by decide)) (by ext; decide) * (pSL * tSL) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  change tMat * pMat = Matrix.scalar (Fin 3) F4.ω * (pMat * tMat)
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem proj_tSL_comm : proj 3 F4 tSL * proj 3 F4 pSL = proj 3 F4 pSL * proj 3 F4 tSL := by
  rw [← map_mul, ← map_mul, tSL_mul_pSL, map_mul,
    proj_eq_one_iff.mpr (scalarElement_mem_scalars _ _), one_mul]

section Lift


theorem exists_lift : ∃ s e : onL, lToS s = proj 3 F4 tSL ∧ lToS e = proj 3 F4 pSL ∧
    s ^ 3 = 1 ∧ e ^ 3 = 1 ∧ s * e = e * s := by
  have hQ4 : ∀ x ∈ lToS.ker, x ^ 4 = 1 := by
    intro x hx
    rw [ker_lToS] at hx
    have hc : Nat.card (onQ.subgroupOf onL) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv, card_onQ]
    have h4 := pow_card_eq_one' (G := ↥(onQ.subgroupOf onL)) (x := ⟨x, hx⟩)
    rw [hc] at h4
    exact congrArg Subtype.val h4
  have hlift : ∀ y : projectiveSL 3 F4, y ^ 3 = 1 → ∃ l : onL, lToS l = y ∧ l ^ 3 = 1 := by
    intro y hy
    obtain ⟨l, hl⟩ := lToS_surjective y
    refine ⟨l ^ 4, by rw [map_pow, hl, pow_succ, hy, one_mul], ?_⟩
    have hk : l ^ 3 ∈ lToS.ker := by rw [MonoidHom.mem_ker, map_pow, hl, hy]
    calc (l ^ 4) ^ 3 = (l ^ 3) ^ 4 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := hQ4 _ hk
  obtain ⟨s, hs, hs3⟩ := hlift (proj 3 F4 tSL) (by rw [← map_pow, tSL_pow_three, map_one])
  obtain ⟨e, he, he3⟩ := hlift (proj 3 F4 pSL) (by rw [← map_pow, pSL_pow_three, map_one])
  refine ⟨s, e, hs, he, hs3, he3, ?_⟩
  set c := s * e * s⁻¹ * e⁻¹ with hc
  have hck : c ∈ lToS.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hs, he,
      proj_tSL_comm]
    group
  have hcQ : (c : Equiv.Perm (Fin N)) ∈ onQ := by
    have := hck
    rw [ker_lToS] at this
    exact this
  have hcent : ∀ l : onL, c * l = l * c := by
    intro l
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (onQ_le_centralizer_L hcQ) l l.2).symm
  have h1 : s * e * s⁻¹ = c * e := by rw [hc]; group
  have hk : ∀ k : ℕ, s ^ k * e * (s ^ k)⁻¹ = c ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcs : c ^ k * s = s * c ^ k :=
        ((Commute.pow_left (show Commute c s from hcent s) k)).eq
      calc s ^ (k + 1) * e * (s ^ (k + 1))⁻¹ = s * (s ^ k * e * (s ^ k)⁻¹) * s⁻¹ := by group
        _ = s * (c ^ k * e) * s⁻¹ := by rw [ih]
        _ = c ^ k * (s * e * s⁻¹) := by
          rw [← mul_assoc, ← hcs]
          group
        _ = c ^ (k + 1) * e := by rw [h1]; group
  have hc3 : c ^ 3 = 1 := by
    have h3 := hk 3
    rw [hs3, one_mul, inv_one, mul_one] at h3
    have h4 : c ^ 3 * e * e⁻¹ = e * e⁻¹ := by rw [← h3]
    simpa using h4
  have hc4 : c ^ 4 = 1 := hQ4 c hck
  have hc1 : c = 1 := by
    calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc3, hc4]; group
  calc s * e = (s * e * s⁻¹ * e⁻¹) * e * s := by group
    _ = e * s := by rw [← hc, hc1, one_mul]

end Lift

theorem noOuterFixesCentralizer_Pv :
    NoOuterFixesCentralizer 3 Pv := by
  intro σ hσ2 hσ s hs
  by_contra hno
  push Not at hno
  obtain ⟨s0, e0, hs0, he0, hs03, he03, hse⟩ := exists_lift
  set s0P : Pv := ⟨s0, onM_le (onL_le_M s0.2)⟩ with hs0P
  set e0P : Pv := ⟨e0, onM_le (onL_le_M e0.2)⟩ with he0P
  have hs0P3 : orderOf s0P = 3 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => proj_tSL_ne_one ?_
    · simpa using congrArg Subtype.val hs03
    · have h0 : (s0 : Equiv.Perm (Fin N)) = 1 := congrArg Subtype.val h
      have h1 : s0 = 1 := Subtype.ext h0
      rw [← hs0, h1, map_one]
  have hy' : orderOf (onEquivPv.symm s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  have ht' : orderOf (onEquivPv.symm s0P) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs0P3
  obtain ⟨k0, hk0⟩ := onThree_fusion ht' hy'
  set k := onEquivPv k0 with hkdef
  have hk : k * s0P * k⁻¹ = s := by
    have h := congrArg onEquivPv hk0
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
  set σ' : MulAut Pv := MulAut.conj k⁻¹ * σ * MulAut.conj k with hσ'
  have hfix : ∀ t : Pv, s0P * t = t * s0P → σ' t = t := by
    intro t ht
    have hct : s * (k * t * k⁻¹) = (k * t * k⁻¹) * s := by
      rw [← hk]
      calc k * s0P * k⁻¹ * (k * t * k⁻¹) = k * (s0P * t) * k⁻¹ := by group
        _ = k * (t * s0P) * k⁻¹ := by rw [ht]
        _ = k * t * k⁻¹ * (k * s0P * k⁻¹) := by group
    have h1 := hno _ hct
    rw [hσ', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, h1]
    group
  have hσ'out : σ' ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
    rintro ⟨g, hg⟩
    apply hσ
    refine ⟨k * g * k⁻¹, ?_⟩
    rw [map_mul, map_mul, hg, hσ', map_inv]
    group
  have hz : σ' zP = zP := by
    refine hfix zP (Subtype.ext ?_)
    exact Subgroup.mem_centralizer_singleton_iff.1 (onM_le_centralizer_z (onL_le_M s0.2))
  obtain ⟨-, -, hrest⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨-, -, -, A, hA⟩ := hrest σ' hσ'out hz
  have hse' : (s0 : Equiv.Perm (Fin N)) * e0 = e0 * s0 := congrArg Subtype.val hse
  have hfs : ((σ' ⟨s0, onM_le (onL_le_M s0.2)⟩ : Pv) : Equiv.Perm (Fin N)) = s0 :=
    congrArg Subtype.val (hfix s0P rfl)
  have hfe : ((σ' ⟨e0, onM_le (onL_le_M e0.2)⟩ : Pv) : Equiv.Perm (Fin N)) = e0 :=
    congrArg Subtype.val (hfix e0P (Subtype.ext hse'))
  rcases hA with hA | hA
  · have h1 := hA s0 s0 hfs.symm
    have h2 := hA e0 e0 hfe.symm
    rw [hs0] at h1
    rw [he0] at h2
    exact not_fix_dual A h1.symm h2.symm
  · have h1 := hA s0 s0 hfs.symm
    have h2 := hA e0 e0 hfe.symm
    rw [hs0] at h1
    rw [he0] at h2
    exact not_fix_field A h1.symm h2.symm

theorem sporadicOuterHolds_ONan_three :
    SporadicOuterHolds .ONan 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.ON := e
  exact NoOuterFixesCentralizer.of_mulEquiv (e0.trans onEquivPv) noOuterFixesCentralizer_Pv

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
