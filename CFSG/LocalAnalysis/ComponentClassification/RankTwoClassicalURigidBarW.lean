module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinBarW

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ}

theorem pow_eq_one_of_commute_uBarW_uBarL (h : UnitaryFieldData 2 f K) (hk : 2 ≤ k) {ζ : K}
    (hζ : ζ ^ 2 ^ f * ζ = 1) (hζ1 : ζ ≠ 1) {x : StatedProj (StatedSU (2 + k) (2 ^ f) K)}
    (hW : ∀ w ∈ uBarW K k f, x * w = w * x) (hL : ∀ l ∈ uBarL K k f, x * l = l * x) :
    x ^ (2 ^ f + 1) = 1 := by
  obtain ⟨g, rfl, a, D, hg⟩ := exists_blk_of_commute_uBarW (by omega) hζ hζ1 hW
  obtain ⟨-, ha, hD⟩ := blk_unitary_of_mem h hg g.2
  have ha1 : a ^ 2 ^ f * a = 1 := by
    have := congrFun (congrFun ha 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h.bar_apply] using this
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha1
    exact zero_ne_one ha1
  have hcomm : ∀ S : StatedSU k (2 ^ f) K,
      D * (S : GL (Fin k) K).val = (S : GL (Fin k) K).val * D := by
    intro S
    have h1 := hL _ ⟨S, rfl⟩
    simp only [MonoidHom.comp_apply] at h1
    rw [← map_mul, ← map_mul, uProj_eq_uProj_iff] at h1
    obtain ⟨c, hc⟩ := h1
    have hm := congrArg Units.val hc
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Subgroup.coe_mul,
      Units.val_mul, Units.val_mul, hg, coe_uL, blk_mul, blk_mul, scalar_eq_blk, blk_mul] at hm
    obtain ⟨h1, h2⟩ := blk_injective hm
    have hc1 : (c : K) = 1 := by
      have h3 := congrFun (congrFun h1 0) 0
      simp only [Matrix.one_mul, smul_mul_smul, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
        mul_one] at h3
      have h4 : ((c : K) - 1) * a = 0 := by rw [sub_mul, ← h3, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right ha0)
    rw [hc1, one_smul, Matrix.one_mul] at h2
    exact h2.symm
  have hDs := eq_smul_one_of_commute_statedSU hk hζ hζ1 hcomm
  set d := D ⟨0, by omega⟩ ⟨0, by omega⟩
  have hd1 : d ^ 2 ^ f * d = 1 := by
    have := congrFun (congrFun hD ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [hDs] at this
    simpa [Matrix.mul_apply, h.bar_apply, Finset.sum_ite_eq', one_apply] using this
  have hg1 : g ^ (2 ^ f + 1) = 1 := by
    refine Subtype.ext (Units.ext ?_)
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hg, blk_pow, hDs, smul_pow, smul_pow,
      one_pow, one_pow, pow_succ, ha1, pow_succ, hd1, one_smul, one_smul, blk_one]
    rfl
  rw [← map_pow, hg1, map_one]

theorem noNormalTwo_centralizer_uBarW (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) (hk : 2 ≤ k) :
    NoNormalTwo (centralizer (uBarW K k f : Set (StatedProj (StatedSU (2 + k) (2 ^ f) K)))) := by
  have := h.finite
  have hK := h.card_eq_sq
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  intro Q hQ hQ2 hN
  have hLC : uBarL K k f ≤
      centralizer (uBarW K k f : Set (StatedProj (StatedSU (2 + k) (2 ^ f) K))) :=
    fun l hl => mem_centralizer_iff.mpr fun w hw => uBarW_commute_uBarL hw hl
  set M : Subgroup ↥(uBarL K k f) := Q.subgroupOf (uBarL K k f)
  have hMn : M.Normal :=
    ⟨fun n hn l => (mem_normalizer_iff.mp (hN (hLC l.2)) n.1).mp hn⟩
  have hM2 : IsPGroup 2 ↥M := fun g => by
    obtain ⟨n, hn⟩ := hQ2 ⟨g.1.1, g.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h' := congrArg (Subtype.val : ↥Q → StatedProj (StatedSU (2 + k) (2 ^ f) K)) hn
    simpa using h'
  have hMbot := eq_bot_of_normal_isPGroup_two_of_quasisimple (isQuasisimple_uBarL hK hf hk)
    (odd_card_center_uBarL hK hf hk) M hM2
  have hQW : ∀ x ∈ Q, ∀ w ∈ uBarW K k f, x * w = w * x := fun x hx w hw =>
    (mem_centralizer_iff.mp (hQ hx) w hw).symm
  have hQL : ∀ x ∈ Q, ∀ l ∈ uBarL K k f, x * l = l * x := by
    intro x hx l hl
    have h1 : ⁅x, l⁆ ∈ Q := by
      have hl' : l * x⁻¹ * l⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp (hN (hLC hl)) x⁻¹).mp (inv_mem hx)
      rw [commutatorElement_def, mul_assoc x, mul_assoc x]
      exact mul_mem hx hl'
    have h2 : ⁅x, l⁆ ∈ uBarL K k f := by
      obtain ⟨g, rfl, a, D, hg⟩ := exists_blk_of_commute_uBarW (by omega) hζ hζ1 (hQW x hx)
      obtain ⟨S, rfl⟩ := hl
      obtain ⟨S', hS'⟩ := commutatorElement_mem_range_uL h hg (coe_uL S)
        (show a • (1 : Matrix (Fin 2) (Fin 2) K) * 1 = 1 * a • 1 by
          rw [Matrix.mul_one, Matrix.one_mul])
      exact ⟨S', by simp only [MonoidHom.comp_apply]; rw [hS', map_commutatorElement]⟩
    have h3 : (⟨⁅x, l⁆, h2⟩ : ↥(uBarL K k f)) ∈ M := h1
    rw [hMbot, mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h3)
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have hpow := pow_eq_one_of_commute_uBarW_uBarL h hk hζ hζ1 (hQW x hx) (hQL x hx)
  obtain ⟨n, hn⟩ := hQ2 ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have h2 : orderOf x ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one hpow
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop : Nat.Coprime (2 ^ n) (2 ^ f + 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

end CFSG.ComponentClassification.RankTwoClassical.URigid
