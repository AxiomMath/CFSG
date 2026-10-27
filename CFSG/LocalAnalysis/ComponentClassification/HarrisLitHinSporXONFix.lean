module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXONMat
public import CFSG.Sporadic.ONOddCore.OuterLocal

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin.SporX

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.PSL3Four

theorem pow_four_eq_one_of_mem_Q
    {y : onL}
    (hy : y ∈ onQ.subgroupOf onL) : y ^ 4 = 1 := by
  have h : (⟨(y : Equiv.Perm (Fin N)), hy⟩ : onQ) ^ Nat.card onQ = 1 := pow_card_eq_one'
  rw [card_onQ] at h
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

theorem exists_fixed_lift
    {γ : MulAut Pv}
    (hLm : ∀ x : Pv, ((γ x : Pv) : Equiv.Perm (Fin N)) ∈ onL ↔ (x : Equiv.Perm (Fin N)) ∈ onL)
    {γbar : MulAut S3}
    (hc : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((γ ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) → lToS a' = γbar (lToS a))
    {s : S3} (hs : γbar s = s) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hsr : orderOf s = r) :
    ∃ x : Pv, γ x = x ∧ (x : Equiv.Perm (Fin N)) ∈ onL ∧ orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  let ι : onL →* Pv := Subgroup.inclusion (onL_le_M.trans onM_le)
  have hι : Function.Injective ι := Subgroup.inclusion_injective _
  obtain ⟨l, hl⟩ := lToS_surjective s
  set l' : onL := ⟨γ (ι l), (hLm (ι l)).2 l.2⟩ with hl'
  have h1 : lToS l' = s := by rw [hc l l' rfl, hl, hs]
  have hγl : γ (ι l) = ι l' := Subtype.ext rfl
  have hq : l⁻¹ * l' ∈ onQ.subgroupOf onL := by
    rw [← ker_lToS, MonoidHom.mem_ker, map_mul, map_inv, hl, h1, inv_mul_cancel]
  have hcomm : Commute l (l⁻¹ * l') := by
    have h := Subgroup.mem_centralizer_iff.1 (onQ_le_centralizer_L hq) _ l.2
    refine Subtype.ext ?_
    show (l : Equiv.Perm (Fin N)) * ((l⁻¹ * l' : onL) : Equiv.Perm (Fin N)) =
      ((l⁻¹ * l' : onL) : Equiv.Perm (Fin N)) * l
    exact h
  have hl'4 : l' ^ 4 = l ^ 4 := by
    rw [show l' = l * (l⁻¹ * l') by group, hcomm.mul_pow, pow_four_eq_one_of_mem_Q hq, mul_one]
  have hx1 : l ^ 4 ≠ 1 := by
    intro h
    have h4 : s ^ 4 = 1 := by rw [← hl, ← map_pow, h, map_one]
    have hdvd : r ∣ 2 ^ 2 := hsr ▸ orderOf_dvd_of_pow_eq_one h4
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
  have hxr : (l ^ 4) ^ r = 1 := by
    have hQ : l ^ r ∈ onQ.subgroupOf onL := by
      rw [← ker_lToS, MonoidHom.mem_ker, map_pow, hl, ← hsr, pow_orderOf_eq_one]
    rw [← pow_mul, mul_comm, pow_mul, pow_four_eq_one_of_mem_Q hQ]
  refine ⟨ι (l ^ 4), ?_, (l ^ 4).2, ?_⟩
  · calc γ (ι (l ^ 4)) = (γ (ι l)) ^ 4 := by rw [map_pow, map_pow]
      _ = ι (l' ^ 4) := by rw [hγl, map_pow]
      _ = ι (l ^ 4) := by rw [hl'4]
  · rw [orderOf_injective ι hι]
    exact orderOf_eq_prime hxr hx1

theorem exists_fixed_odd_of_fix_z
    {γ : MulAut Pv}
    (hout : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hγ2 : γ * γ = 1) (hz : γ zP = zP) :
    ∃ x : Pv, γ x = x ∧ x * zP = zP * x ∧ (orderOf x = 5 ∨ orderOf x = 7) := by
  obtain ⟨-, hLm, -, A, hA⟩ := ctuc_on_outer_local_quotient_is_graph_or_field.2.2 γ hout hz
  rcases hA with hA | hA
  · obtain ⟨s, hs, hso⟩ := exists_fixed_five_of_graph A (induced_sq hγ2 hLm hA)
    obtain ⟨x, hx, hxL, hxo⟩ := exists_fixed_lift hLm hA hs (by norm_num) (by norm_num) hso
    exact ⟨x, hx, mem_M_iff_P.1 (onL_le_M hxL), Or.inl hxo⟩
  · obtain ⟨s, hs, hso⟩ := exists_fixed_seven_of_field A (induced_sq hγ2 hLm hA)
    obtain ⟨x, hx, hxL, hxo⟩ := exists_fixed_lift hLm hA hs (by norm_num) (by norm_num) hso
    exact ⟨x, hx, mem_M_iff_P.1 (onL_le_M hxL), Or.inr hxo⟩

theorem exists_fixed_odd_of_fix
    {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) {a : Pv}
    (ha : orderOf a = 2) (hαa : α a = a) :
    ∃ x : Pv, α x = x ∧ x * a = a * x ∧ (orderOf x = 5 ∨ orderOf x = 7) := by
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2
    (by rw [Subgroup.orderOf_coe]; exact ha)
  set gP : Pv := ⟨g, hg⟩
  set φ : Pv ≃* Pv := MulAut.conj gP⁻¹
  have hφa : φ a = zP := by
    apply Subtype.ext
    show (g⁻¹ * (a : Equiv.Perm (Fin N)) * g⁻¹⁻¹) = onz
    rw [hga]
    group
  set γ := MulAut.congr φ α with hγ
  have hz : γ zP = zP := by
    rw [← hφa, hγ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hαa]
  have hγ2 : γ * γ = 1 := by
    rw [hγ, ← map_mul, hα2, map_one]
  obtain ⟨x, hx, hxz, hxo⟩ := exists_fixed_odd_of_fix_z (not_inner_congr hout φ) hγ2 hz
  refine ⟨φ.symm x, ?_, ?_, ?_⟩
  · apply φ.injective
    rw [MulEquiv.apply_symm_apply]
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at hx
    exact hx
  · apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hφa]
    exact hxz
  · rw [MulEquiv.orderOf_eq]
    exact hxo

end CFSG.ComponentClassification.HarrisLit.Hin.SporX
