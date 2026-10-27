module

public import CFSG.GH74.GLS.C3.Layer1.P34RealTr
public import CFSG.GH74.GLS.C3.Layer1.P34RealL2D

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1 Equiv

section Perm7

theorem perm7_shear {T : Sylow 2 (Perm (Fin 7))} {f₀ : Perm (Fin 7)} (hS : IsA7SylowSplit T f₀)
    {z : Perm (Fin 7)} (hzT : z ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))
    (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), x * z = z * x) :
    (∃ p ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), orderOf p = 2 ∧
      ∃ g ∈ alternatingGroup (Fin 7), g * f₀ * g⁻¹ = f₀ * p) ∧
    (∃ p ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), orderOf p = 2 ∧
      ∃ g ∈ alternatingGroup (Fin 7), g * (f₀ * z) * g⁻¹ = (f₀ * z) * p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hf₀2, hf₀ct, hf₀T, hinter, hcentral, hsplit⟩ := hS
  obtain ⟨g, hg⟩ := A7.exists_conj_T0 T
  have hf : f₀ = g * A7.f0 * g⁻¹ := A7.split_unique hg hf₀T hf₀ct hcentral
  have hz : z = g * A7.r ^ 2 * g⁻¹ := A7.central_involution_eq hg hzT hz2 hzc
  have hf₀odd : f₀ ∉ alternatingGroup (Fin 7) := by
    intro h
    have : f₀ ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊓ zpowers f₀ :=
      ⟨⟨hf₀T, h⟩, mem_zpowers f₀⟩
    rw [hinter, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hf₀2
    omega
  have hf₀sq : f₀ * f₀ = 1 := by
    have := pow_orderOf_eq_one f₀
    rwa [hf₀2, sq] at this
  have key : ∀ p₀ ∈ A7.P0list, p₀ * p₀ = 1 → p₀ ≠ 1 →
      g * p₀ * g⁻¹ ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ∧
        orderOf (g * p₀ * g⁻¹) = 2 := by
    intro p₀ hp₀ hp₀sq hp₀1
    refine ⟨?_, ?_⟩
    · rw [A7.mem_T_inf_A7 hg]
      have : g⁻¹ * (g * p₀ * g⁻¹) * g = p₀ := by group
      rw [this]
      exact hp₀
    · refine orderOf_eq_prime ?_ ?_
      · calc (g * p₀ * g⁻¹) ^ 2 = g * (p₀ * p₀) * g⁻¹ := by rw [sq]; group
          _ = 1 := by rw [hp₀sq]; group
      · intro h
        apply hp₀1
        calc p₀ = g⁻¹ * (g * p₀ * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
  constructor
  ·
    obtain ⟨hpT, hpo⟩ := key (A7.s * A7.f0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    refine ⟨_, hpT, hpo, ?_⟩
    have hv : f₀ * (g * (A7.s * A7.f0) * g⁻¹) = g * A7.s * g⁻¹ := by
      rw [hf]
      calc g * A7.f0 * g⁻¹ * (g * (A7.s * A7.f0) * g⁻¹) = g * (A7.f0 * (A7.s * A7.f0)) * g⁻¹ := by
            group
        _ = g * A7.s * g⁻¹ := by
          have : A7.f0 * (A7.s * A7.f0) = A7.s := by decide +kernel
          rw [this]
    rw [hv]
    refine Thm1.exists_alt_conj_of_odd hf₀odd hf₀sq (Equiv.Perm.isConj_iff_cycleType_eq.2 ?_)
    rw [hf₀ct, show g * A7.s * g⁻¹ = (g⁻¹)⁻¹ * A7.s * g⁻¹ by simp, A7.cycleType_conj_inv]
    exact (Equiv.Perm.isSwap_iff_cycleType.mp ⟨0, 2, by decide, rfl⟩).symm
  ·
    obtain ⟨hpT, hpo⟩ := key (A7.s * A7.r) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    refine ⟨_, hpT, hpo, ?_⟩
    have hfz : f₀ * z = g * (A7.f0 * A7.r ^ 2) * g⁻¹ := by
      rw [hf, hz]
      group
    have hfzodd : f₀ * z ∉ alternatingGroup (Fin 7) := by
      intro h
      apply hf₀odd
      have hzA : z ∈ alternatingGroup (Fin 7) := hzT.2
      have h2 := (alternatingGroup (Fin 7)).mul_mem h ((alternatingGroup (Fin 7)).inv_mem hzA)
      rwa [mul_inv_cancel_right] at h2
    have huu : (f₀ * z) * (f₀ * z) = 1 := by
      rw [hfz]
      obtain ⟨X, hX⟩ : ∃ X : Perm (Fin 7), X = A7.f0 * A7.r ^ 2 := ⟨_, rfl⟩
      have hXX : X * X = 1 := by rw [hX, ← sq]; exact A7.f0_mul_r_sq_sq
      rw [← hX]
      calc g * X * g⁻¹ * (g * X * g⁻¹) = g * (X * X) * g⁻¹ := by group
        _ = 1 := by rw [hXX]; group
    have hw2 : (A7.f0 * A7.r ^ 2 * (A7.s * A7.r)) ^ 2 = 1 := by decide +kernel
    have hwc : (A7.f0 * A7.r ^ 2 * (A7.s * A7.r)).support.card = 6 := by decide +kernel
    have hwct : (A7.f0 * A7.r ^ 2 * (A7.s * A7.r)).cycleType = {2, 2, 2} := by
      rw [A7.cycleType_replicate_two _ hw2, hwc]
      rfl
    have hv : (f₀ * z) * (g * (A7.s * A7.r) * g⁻¹) =
        g * (A7.f0 * A7.r ^ 2 * (A7.s * A7.r)) * g⁻¹ := by
      rw [hfz]
      group
    rw [hv]
    refine Thm1.exists_alt_conj_of_odd hfzodd huu (Equiv.Perm.isConj_iff_cycleType_eq.2 ?_)
    have h1 : (f₀ * z).cycleType = {2, 2, 2} := by
      rw [hf, hz]
      exact A7.cycleType_fz g
    rw [h1, show g * (A7.f0 * A7.r ^ 2 * (A7.s * A7.r)) * g⁻¹ =
      (g⁻¹)⁻¹ * (A7.f0 * A7.r ^ 2 * (A7.s * A7.r)) * g⁻¹ by simp, A7.cycleType_conj_inv, hwct]

theorem perm7_classify {T' : Sylow 2 (Perm (Fin 7))} {f₀ : Perm (Fin 7)}
    (hS : IsA7SylowSplit T' f₀) {B : Subgroup (Perm (Fin 7))}
    (hBT' : B ≤ (T' : Subgroup (Perm (Fin 7))))
    (hPeq : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) =
      B ⊓ alternatingGroup (Fin 7))
    {z : Perm (Fin 7)}
    (hzu : ∀ w ∈ B ⊓ alternatingGroup (Fin 7),
      (∀ q ∈ B ⊓ alternatingGroup (Fin 7), w * q = q * w) → w = 1 ∨ w = z)
    (hf₀zc : f₀ * z = z * f₀) {σ' : Perm (Fin 7)} (hσ'B : σ' ∈ B)
    (hσ'odd : σ' ∉ alternatingGroup (Fin 7))
    (hσ'c : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), σ' * q = q * σ') :
    σ' = f₀ ∨ σ' = f₀ * z := by
  obtain ⟨hf₀2, hf₀ct, hf₀T, hinter, hcentral, hsplit⟩ := hS
  have hf₀sq : f₀ * f₀ = 1 := by
    have := pow_orderOf_eq_one f₀
    rwa [hf₀2, sq] at this
  have hσ'T : σ' ∈ (T' : Subgroup (Perm (Fin 7))) := hBT' hσ'B
  have hcomm : ∀ p ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7),
      ∀ q ∈ zpowers f₀, p * q = q * p := by
    intro p hp q hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact (Commute.zpow_right (show Commute p f₀ from hcentral p hp) j).eq
  obtain ⟨p, hpP, w, hw, hσ'eq⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm (hsplit ▸ hσ'T)
  rcases mem_zpowers_of_mul_self hf₀sq hw with hw1 | hwf
  · exfalso
    apply hσ'odd
    rw [hσ'eq, hw1, mul_one]
    exact hpP.2
  · have hpP' : p ∈ B ⊓ alternatingGroup (Fin 7) := hPeq ▸ hpP
    have hpc : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), p * q = q * p := by
      intro q hq
      have hqT : q ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := hPeq ▸ hq
      have h1 := hσ'c q hq
      rw [hσ'eq, hwf] at h1
      have h2 : p * q * f₀ = q * p * f₀ := by
        calc p * q * f₀ = p * (q * f₀) := by group
          _ = p * (f₀ * q) := by rw [hcentral q hqT]
          _ = p * f₀ * q := by group
          _ = q * (p * f₀) := h1
          _ = q * p * f₀ := by group
      exact mul_right_cancel h2
    rcases hzu p hpP' hpc with hp1 | hpz
    · left
      rw [hσ'eq, hwf, hp1, one_mul]
    · right
      rw [hσ'eq, hwf, hpz, hf₀zc]

theorem autP34G_perm7 (B : Subgroup (Perm (Fin 7))) (hB : IsPGroup 2 ↥B)
    (hSyl : IsSylowOf 2 (B ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)))
    {α : Perm (Fin 7)} (hαB : α ∈ B) (hα2 : orderOf α = 2) (hαodd : α ∉ alternatingGroup (Fin 7))
    (hαc : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), α * q = q * α) :
    ∃ z : Perm (Fin 7), AutP34G (alternatingGroup (Fin 7)) B α z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hBT'⟩ := hB.exists_le_sylow
  obtain ⟨f₀, hS⟩ := ivk_1_1T T'
  have hS' := hS
  obtain ⟨hf₀2, hf₀ct, hf₀T, hinter, hcentral, hsplit⟩ := hS
  have hPeq : (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) =
      B ⊓ alternatingGroup (Fin 7) :=
    hSyl.eq_of_le (inf_le_inf_right _ hBT') inf_le_right T'.isPGroup'.to_inf_left
  have hdih : IsDihedralOrder ↥(B ⊓ alternatingGroup (Fin 7)) 8 := by
    rw [← hPeq]
    exact ivk_1_1a T'
  obtain ⟨z, hzH, hz2, hzc, hzu⟩ := exists_dihedral_center
    (H := B ⊓ alternatingGroup (Fin 7)) (n := 3) le_rfl
    ⟨by norm_num, by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hdih⟩
  have hzT : z ∈ (T' : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    rw [hPeq]
    exact hzH
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hαα : α * α = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα2, sq] at this
  have hsignodd : ∀ u : Perm (Fin 7), u ∉ alternatingGroup (Fin 7) → Equiv.Perm.sign u = -1 := by
    intro u hu
    rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hu
    · exact h
  have hαs := hsignodd α hαodd
  have hallin : ∀ u ∈ B, u ∈ (B ⊓ alternatingGroup (Fin 7)) ⊔ zpowers α := by
    intro u huB
    by_cases hu : u ∈ alternatingGroup (Fin 7)
    · exact Subgroup.mem_sup_left ⟨huB, hu⟩
    · have hus := hsignodd u hu
      have h1 : u * α⁻¹ ∈ B ⊓ alternatingGroup (Fin 7) :=
        ⟨B.mul_mem huB (B.inv_mem hαB), Equiv.Perm.mem_alternatingGroup.2 (by
          rw [map_mul, map_inv, hus, hαs]
          decide)⟩
      have := Subgroup.mul_mem_sup h1 (Subgroup.mem_zpowers α)
      simpa using this
  have hcomm : ∀ p ∈ B ⊓ alternatingGroup (Fin 7), ∀ a ∈ zpowers α, p * a = a * p := by
    intro p hp a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_right (show Commute p α from (hαc p hp).symm) j).eq
  refine ⟨z, ?_⟩
  refine
    { dihedral := ⟨3, le_rfl, by norm_num, by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hdih⟩
      z_mem := hzH
      z_order := hz2
      z_cent := hzc
      z_unique := hzu
      abelian := fun a ha b hb => ⟨B.mul_mem (B.mul_mem (B.mul_mem ha hb) (B.inv_mem ha))
        (B.inv_mem hb), Equiv.Perm.mem_alternatingGroup.2 (by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          simp [mul_comm, mul_left_comm, Int.units_mul_self])⟩
      invol_coset := fun u huB _ hunot => absurd (hallin u huB) hunot
      invol_dih := fun u huB _ hunot => absurd (hallin u huB) hunot
      cent_B := ?_
      conj_z := ?_
      fus_alpha := ?_
      shear := ?_ }
  ·
    intro w hwB hwc
    obtain ⟨p, hp, a, ha, hpa⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm (hallin w hwB)
    rcases mem_zpowers_of_mul_self hαα ha with h1 | h1
    · rw [h1, mul_one] at hpa
      rw [hpa]
      rcases hzu p hp (fun q hq => by rw [← hpa]; exact hwc q hq) with h2 | h2
      · rw [h2]
        exact Subgroup.one_mem _
      · rw [h2]
        exact Subgroup.mem_sup_right (mem_zpowers z)
    · rw [h1] at hpa
      have hpc : ∀ q ∈ B ⊓ alternatingGroup (Fin 7), p * q = q * p := by
        intro q hq
        have h2 := hwc q hq
        have h3 := hαc q hq
        rw [hpa] at h2
        have : p * α * q = q * (p * α) := h2
        calc p * q = p * α * q * α⁻¹ := by
              rw [mul_assoc p α q, h3]; group
          _ = q * (p * α) * α⁻¹ := by rw [this]
          _ = q * p := by group
      rw [hpa]
      refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_left (mem_zpowers α))
      rcases hzu p hp hpc with h2 | h2
      · rw [h2]
        exact Subgroup.one_mem _
      · rw [h2]
        exact Subgroup.mem_sup_right (mem_zpowers z)
  ·
    intro p hp hp2
    obtain ⟨g, hg, hgz⟩ := (ivk_1_1d).1 z p hzH.2 hp.2 hz2 hp2
    exact ⟨g, hg, hgz⟩
  ·
    intro v hv hv2
    have hvv : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [hv2, sq] at this
    have hαv : α * v = v * α := hαc v hv
    have huB : α * v ∈ B := B.mul_mem hαB hv.1
    have huu : (α * v) * (α * v) = 1 := by
      calc α * v * (α * v) = α * (v * α) * v := by group
        _ = α * (α * v) * v := by rw [← hαv]
        _ = (α * α) * (v * v) := by group
        _ = 1 := by rw [hαα, hvv, one_mul]
    have huodd : α * v ∉ alternatingGroup (Fin 7) := by
      intro h
      apply hαodd
      have h2 := (alternatingGroup (Fin 7)).mul_mem h ((alternatingGroup (Fin 7)).inv_mem hv.2)
      rwa [mul_inv_cancel_right] at h2
    have hu1 : α * v ≠ 1 := fun h => huodd (h ▸ Subgroup.one_mem _)
    have huo : orderOf (α * v) = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
    have hu_sup : α * v ∈ (B ⊓ alternatingGroup (Fin 7)) ⊔ zpowers α :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers α)) (Subgroup.mem_sup_left hv)
    obtain ⟨-, hfus⟩ := perm7_fus B hB hSyl hzH hz2 hzc α hαB hα2 hαodd hαc
    obtain ⟨g, hg, hgu⟩ := hfus (α * v) hu_sup huo
    rcases hgu with h | h | h
    · exfalso
      apply huodd
      have : α * v = g⁻¹ * z * g := by rw [← h]; group
      rw [this]
      exact (alternatingGroup (Fin 7)).mul_mem ((alternatingGroup (Fin 7)).mul_mem
        ((alternatingGroup (Fin 7)).inv_mem hg) hzH.2) hg
    · exact ⟨g, hg, Or.inl h⟩
    · exact ⟨g, hg, Or.inr h⟩
  ·
    intro σ' hσ'B _ hσ'odd hσ'c
    have hcls := perm7_classify hS' hBT' hPeq hzu (hcentral z hzT).symm hσ'B hσ'odd hσ'c
    obtain ⟨⟨p, hp, hp2, g, hg, hgp⟩, ⟨p', hp', hp'2, g', hg', hgp'⟩⟩ :=
      perm7_shear hS' hzT hz2 (fun x hx => (hzc x (by rw [← hPeq]; exact hx)).symm)
    rcases hcls with h | h
    · rw [h]
      exact ⟨p, by rw [← hPeq]; exact hp, hp2, g, hg, hgp⟩
    · rw [h]
      exact ⟨p', by rw [← hPeq]; exact hp', hp'2, g', hg', hgp'⟩

theorem factorization_two_eq {n m k : ℕ} (hn : n = 2 ^ k * m) (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    n.factorization 2 = k := by
  rw [hn, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem card_A7_factorization :
    (Nat.card ↥(alternatingGroup (Fin 7))).factorization 2 = 3 := by
  have h : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card]
    decide
  rw [h]
  exact factorization_two_eq (m := 315) (by norm_num) (by norm_num) (by norm_num)

theorem fix_two_part_perm7 {u : Perm (Fin 7)} (hu2 : orderOf u = 2)
    (huodd : u ∉ alternatingGroup (Fin 7)) :
    (Nat.card ↥(centralizer ({u} : Set (Perm (Fin 7))) ⊓
      alternatingGroup (Fin 7))).factorization 2 =
      (Nat.card ↥(alternatingGroup (Fin 7))).factorization 2 := by
  have hu1 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2] at this
  have hne : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  rw [card_A7_factorization]
  rcases odd_involution_cycleType hu2 huodd with hct | hct
  · rw [A7.card_centralizer_A7_two hct hu1 hne]
    exact factorization_two_eq (m := 15) (by norm_num) (by norm_num) (by norm_num)
  · rw [A7.card_centralizer_A7_two_two_two hct hu1 hne]
    exact factorization_two_eq (m := 3) (by norm_num) (by norm_num) (by norm_num)

end Perm7

theorem autLevelPA7_proved (Kb : Type) [Group Kb] [Finite Kb] : AutLevelPA7 Kb := by
  rintro ⟨e7⟩
  set ψ := psiEquiv e7 with hψ
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have hinn := psi_map_innAut e7
  have hBin : ∀ B : Subgroup (MulAut Kb), (B ⊓ innAut Kb).map ψ.toMonoidHom =
      B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7) := fun B => by
    rw [Subgroup.map_inf _ _ _ hinj, hinn]
  have hodd : ∀ α : MulAut Kb, α ∉ innAut Kb → ψ α ∉ alternatingGroup (Fin 7) := by
    intro α hα h
    apply hα
    rw [← hinn] at h
    simpa [hψ] using Subgroup.mem_map_equiv.1 h
  refine ⟨?_, ?_⟩
  · intro α hα2 hαinn
    obtain ⟨e1⟩ := fixedSubgroup_equiv_A7 e7 α
    rw [Nat.card_congr e1.toEquiv, Nat.card_congr e7.toEquiv]
    exact fix_two_part_perm7 (by rw [MulEquiv.orderOf_eq]; exact hα2) (hodd α hαinn)
  · intro B hB hSyl α hαB hα2 hαinn hαc
    have : Finite (MulAut Kb) := Finite.of_equiv _ ψ.symm.toEquiv
    have hB' : IsPGroup 2 ↥(B.map ψ.toMonoidHom) :=
      hB.of_equiv (Subgroup.equivMapOfInjective B ψ.toMonoidHom hinj)
    have hSyl' : IsSylowOf 2 (B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7))
        (alternatingGroup (Fin 7)) := by
      have := isSylowOf_map_equiv ψ hSyl
      rwa [hBin B, hinn] at this
    have hc : ∀ q ∈ B.map ψ.toMonoidHom ⊓ alternatingGroup (Fin 7), ψ α * q = q * ψ α := by
      intro q hq
      rw [← hBin B] at hq
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      show ψ α * ψ q₀ = ψ q₀ * ψ α
      rw [← map_mul, ← map_mul, hαc q₀ hq₀]
    have hαB' : ψ α ∈ B.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hαB
    have hα2' : orderOf (ψ α) = 2 := by rw [MulEquiv.orderOf_eq]; exact hα2
    obtain ⟨z', hz'⟩ := autP34G_perm7 (B.map ψ.toMonoidHom) hB' hSyl' hαB' hα2' (hodd α hαinn) hc
    refine ⟨ψ.symm z', AutP34G.of_equiv ψ ?_⟩
    rw [hinn, MulEquiv.apply_symm_apply]
    exact hz'

theorem b_prop34_autlevel_A7_proved : B_prop34_autlevel_A7 := fun Kb _ _ => autLevelPA7_proved Kb

end CFSG.GH74.GLS.C3.Layer1.P34Real
