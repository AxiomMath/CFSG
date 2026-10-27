module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQResidueLeaves
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.L28Local CFSG.Quasithin.F6.L28Res

namespace InnerQ.FieldInvertThree

private def twist (g : G8) (i : Bool) (x : G8) : G8 :=
  if i then frobF (g * x * g⁻¹) else frobF (frobF (g * x * g⁻¹))

set_option synthInstance.maxSize 1024 in
private theorem twist_check : ∀ g : G8, ∀ i : Bool,
    twist g i (twist g i (twist g i ga)) = ga → twist g i (twist g i (twist g i gb)) = gb →
    ∀ t : G8, t ≠ 1 → t * t * t = 1 → twist g i t = t →
      ∃ s : G8, s * s = 1 ∧ twist g i s = s ∧ s * t * s⁻¹ = t⁻¹ := by
  decide +kernel

private theorem frob_pow_three : frob ^ 3 = 1 := by
  refine MulEquiv.ext fun x => ?_
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
  exact frobF_frobF_frobF x

private theorem exists_twist (φ : MulAut G8) (hφ : ¬ ∃ y : G8, φ = MulAut.conj y) :
    ∃ g : G8, ∃ i : Bool, ∀ x, φ x = twist g i x := by
  have : Finite (MulAut G8) := finite_mulAut
  set N := (MulAut.conj : G8 →* MulAut G8).range
  have hN : N.Normal := ⟨by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, MulEquiv.ext fun x => ?_⟩
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]⟩
  have hinj : Function.Injective (MulAut.conj : G8 →* MulAut G8) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hc : ∀ h : G8, g * h = h * g := fun h => by
      have := congrArg (fun α : MulAut G8 => α h) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * h = g * h * g⁻¹ * g := by group
        _ = h * g := by rw [this]
    exact Subgroup.mem_bot.mpr (eq_one_of_commute g (hc ga) (hc gb))
  have hNcard : Nat.card N = 504 := by
    show Nat.card (MulAut.conj : G8 →* MulAut G8).range = 504
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, card_G8]
  have hidx : N.index = 3 := by
    have := N.card_mul_index
    rw [hNcard, card_mulAut] at this
    omega
  have hQ : Nat.card (MulAut G8 ⧸ N) = 3 := by rw [← Subgroup.index, hidx]
  have hfrob : (QuotientGroup.mk frob : MulAut G8 ⧸ N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    rintro ⟨g, hg⟩
    exact (frob_not_inner g).1 ⟨by rw [← MulAut.conj_apply, hg]; rfl,
      by rw [← MulAut.conj_apply, hg]; rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop := zpowers_eq_top_of_prime_card hQ hfrob
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top (QuotientGroup.mk φ))
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  obtain ⟨g, hg⟩ := hk
  have hφeq : φ = frob ^ k * MulAut.conj g := by rw [hg, mul_inv_cancel_left]
  have hk3 : frob ^ k = frob ^ (k % 3) := by
    have hk' : k = 3 * (k / 3) + k % 3 := by omega
    conv_lhs => rw [hk', zpow_add, zpow_mul]
    rw [show frob ^ (3 : ℤ) = 1 from by exact_mod_cast frob_pow_three, one_zpow, one_mul]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h
  · exact absurd ⟨g, by rw [hφeq, hk3, h, zpow_zero, one_mul]⟩ hφ
  · refine ⟨g, true, fun x => ?_⟩
    rw [hφeq, hk3, h]
    rfl
  · refine ⟨g, false, fun x => ?_⟩
    rw [hφeq, hk3, h]
    rfl

end InnerQ.FieldInvertThree

open InnerQ.FieldInvertThree in
theorem kFactCaseTwoFieldInvertThree : KFactCaseTwoFieldInvertThree := by
  intro K _ _ hK φ hφ3 hout t ht hφt
  obtain ⟨ε⟩ := nonempty_equiv_G8 hK
  set ψ : MulAut G8 := MulAut.congr ε φ
  have hψ : ∀ x, ψ x = ε (φ (ε.symm x)) := fun x => rfl
  have hψout : ¬ ∃ y : G8, ψ = MulAut.conj y := by
    rintro ⟨y, hy⟩
    refine hout ⟨ε.symm y, ?_⟩
    ext k
    have h := congrArg (fun α : MulAut G8 => ε.symm (α (ε k))) hy
    simp only [hψ, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
    rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  obtain ⟨g, i, hgi⟩ := exists_twist ψ hψout
  have hψ3 : ∀ x, twist g i (twist g i (twist g i x)) = x := by
    intro x
    have h : ψ ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
    have := congrArg (fun α : MulAut G8 => α x) h
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hgi] using this
  have ht3 : t * t * t = 1 := by
    rw [show t * t * t = t ^ 3 by rw [pow_three, mul_assoc], ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  obtain ⟨s, hs2, hsψ, hst⟩ := twist_check g i (hψ3 ga) (hψ3 gb) (ε t)
    (fun h => ht1 (ε.injective (h.trans (map_one ε).symm)))
    (by rw [← map_mul, ← map_mul, ht3, map_one])
    (by rw [← hgi, hψ, MulEquiv.symm_apply_apply, hφt])
  refine ⟨ε.symm s, ?_, ?_, ?_⟩
  · rw [pow_two, ← map_mul, hs2, map_one]
  · apply ε.injective
    rw [← MulEquiv.symm_apply_apply ε (φ (ε.symm s)), ← hψ, hgi, hsψ, MulEquiv.apply_symm_apply]
  · apply ε.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hst

end CFSG.LocalAnalysis.RankThreeTheoremC
