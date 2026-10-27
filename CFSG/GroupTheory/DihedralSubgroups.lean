module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public noncomputable section

namespace CFSG.GorensteinWalter

open scoped Classical

theorem noncyclic_subgroup_dihedral_two_pow {n : ℕ}
    (H : Subgroup (DihedralGroup (2 ^ n))) (hH : ¬ IsCyclic H) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num : 2 ≠ 0)⟩
  have hnot : ¬ H ≤ Subgroup.zpowers (DihedralGroup.r 1) := by
    intro hle
    exact hH (Subgroup.isCyclic_of_le hle)
  have hex : ∃ x : DihedralGroup (2 ^ n),
      x ∈ H ∧ x ∉ Subgroup.zpowers (DihedralGroup.r 1) := by
    by_contra hnone
    apply hnot
    intro x hx
    by_contra hxR
    exact hnone ⟨x, hx, hxR⟩
  obtain ⟨x, hx, hxR⟩ := hex
  obtain ⟨i, hi⟩ : ∃ i : ZMod (2 ^ n), DihedralGroup.sr i ∈ H := by
    rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact False.elim (hxR (r_mem_zpowers_r_one i))
    · exact ⟨i, hx⟩
  obtain ⟨a, ha, hagen⟩ := generator_of_inf H
  let ρ : H := ⟨a, ha⟩
  let σ : H := ⟨DihedralGroup.sr i, hi⟩
  have hrotation : a ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
    have ha' : a ∈ H ⊓ Subgroup.zpowers (DihedralGroup.r 1) := by
      rw [← hagen]
      exact Subgroup.mem_zpowers a
    exact ha'.2
  have hgen : (⊤ : Subgroup H) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply le_antisymm
    · intro y _
      rcases (mem_decomp H i hi y.val).mp y.property with hy | ⟨z, hz, hyz⟩
      · have hypow : y.val ∈ Subgroup.zpowers a := hagen ▸ hy
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hypow
        apply (le_sup_left : Subgroup.zpowers ρ ≤ Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ)
        refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
        exact Subtype.ext (by simpa [ρ] using hj)
      · let zH : H := ⟨z, hz.1⟩
        have hzpow : zH ∈ Subgroup.zpowers ρ := by
          have hz' : z ∈ Subgroup.zpowers a := hagen ▸ hz
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz'
          refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
          exact Subtype.ext (by simpa [ρ, zH] using hj)
        have hyzH : y = σ * zH := Subtype.ext hyz
        rw [hyzH]
        exact Subgroup.mul_mem _
          ((le_sup_right : Subgroup.zpowers σ ≤
            Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) (Subgroup.mem_zpowers σ))
          ((le_sup_left : Subgroup.zpowers ρ ≤
            Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) hzpow)
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    change (DihedralGroup.sr i) ^ 2 = (1 : DihedralGroup (2 ^ n))
    rw [pow_two, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    change DihedralGroup.sr i * a * (DihedralGroup.sr i)⁻¹ = a⁻¹
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hrotation
    rw [← hj, DihedralGroup.r_one_zpow, DihedralGroup.inv_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
    congr 1
    simp [sub_eq_add_neg, add_comm]
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hj' := congrArg Subtype.val hj
    have hsr : DihedralGroup.sr i ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
      change a ^ j = DihedralGroup.sr i at hj'
      rw [← hj']
      exact Subgroup.zpow_mem _ hrotation j
    exact sr_not_mem_zpowers_r_one i hsr
  obtain ⟨e⟩ := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have horder : orderOf ρ ∣ 2 ^ n := by
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers (DihedralGroup.r 1) :=
      Subgroup.zpowers_le.mpr hrotation
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, Nat.card_zpowers, DihedralGroup.orderOf_r_one] at hdvd
    have heq : orderOf a = orderOf ρ :=
      orderOf_injective H.subtype Subtype.val_injective ρ
    rwa [heq] at hdvd
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp horder
  have he : Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
    rw [← hk]
    exact ⟨e⟩
  have hkpos : 1 ≤ k := by
    by_contra h
    have hkzero : k = 0 := by omega
    have hcyc : IsCyclic (DihedralGroup (orderOf ρ)) :=
      DihedralGroup.isCyclic_iff.mpr (by simp [hk, hkzero])
    exact hH (e.isCyclic.mpr hcyc)
  exact ⟨k, hkpos, hkn, he⟩

end CFSG.GorensteinWalter
