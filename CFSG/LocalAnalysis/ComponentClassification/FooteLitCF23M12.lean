module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Tools
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Fus

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Blueprint Sporadic.Mathieu Sporadic.Schreier M12Cover

@[expose] def m12u : Equiv.Perm (Fin 12) :=
  evalCodes [m12gA, m12gB]
    [2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2]

@[expose] def m12v : Equiv.Perm (Fin 12) :=
  evalCodes [m12gA, m12gB]
    [-2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2]

@[expose] def m12c : Equiv.Perm (Fin 12) :=
  evalCodes [m12gA, m12gB] [-2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2]

theorem m12u_mem : m12u ∈ NativeSporadic.M12 := evalCodes_mem _ m12_gens_mem' _

theorem m12v_mem : m12v ∈ NativeSporadic.M12 := evalCodes_mem _ m12_gens_mem' _

theorem m12c_mem : m12c ∈ NativeSporadic.M12 := evalCodes_mem _ m12_gens_mem' _

theorem m12_witness_facts : m12u ^ 5 = 1 ∧ m12u ≠ 1 ∧ m12v ^ 5 = 1 ∧ m12v ≠ 1 ∧
    m12u * permA1 = permA1 * m12u ∧ m12v * permA1 = permA1 * m12v ∧
    (m12u * m12v) ^ 2 = 1 ∧ m12u * m12v ≠ 1 ∧
    m12c⁻¹ * permA1 * m12c = permA1 * (m12u * m12v) := by
  decide +kernel


theorem elemA1_coe : (elemA1 : Equiv.Perm (Fin 12)) = permA1 := by
  unfold elemA1
  rfl

theorem m12_inner {G : Type} [Group G] {N J : Subgroup G} (e : ↥N ≃* NativeSporadic.M12)
    {α : G} (hα : orderOf α = 2) (hαN : α ∈ N) (hJN : J ≤ N)
    (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hsmall : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)))
    (hZ : Odd (Nat.card (center ↥J))) :
    ∃ ζ₀ ∈ J, orderOf ζ₀ = 2 ∧ ∃ γ₀ ∈ N, γ₀⁻¹ * α * γ₀ = α * ζ₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := NativeSporadic.M12 with hMdef
  set f : ↥N →* Equiv.Perm (Fin 12) := M.subtype.comp e.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  set α' : ↥N := ⟨α, hαN⟩ with hα'
  have hB := isComponentOf_image hαN hJN hJα hJ e
  set B := (J.subgroupOf N).map f with hBdef
  have hα2 : orderOf (e α') = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hα]
  have hcardB : Nat.card B = Nat.card J :=
    (card_map_of_injective hf).trans (Nat.card_congr (subgroupOfEquivOfLe hJN).toEquiv)
  have hJZ : Nat.card (↥J ⧸ center ↥J) ∣ Nat.card J := by
    rw [← Subgroup.index_eq_card]
    exact (center ↥J).index_dvd_card
  obtain ⟨c, hc⟩ := m12_involution_conj_a0_a1 (e α') hα2
  obtain ⟨cc, hccM, rfl⟩ : ∃ cc : Equiv.Perm (Fin 12), ∃ h : cc ∈ M, c = ⟨cc, h⟩ :=
    ⟨c, c.2, rfl⟩
  have hcoe : ∀ {t : M}, e α' = ⟨cc, hccM⟩ * t * (⟨cc, hccM⟩ : M)⁻¹ →
      f α' = cc * (t : Equiv.Perm (Fin 12)) * cc⁻¹ := fun h => by
    show ((e α' : M) : Equiv.Perm (Fin 12)) = _
    rw [h]
    rfl
  set fc := (MulAut.conj cc⁻¹).toMonoidHom with hfcdef
  have hfcinj : Function.Injective fc := (MulAut.conj cc⁻¹).injective
  have hcardB' : Nat.card (B.map fc) = Nat.card J := (card_map_of_injective hfcinj).trans hcardB
  have hB0 : ∀ {t : M}, e α' = ⟨cc, hccM⟩ * t * (⟨cc, hccM⟩ : M)⁻¹ →
      Assembly.IsComponentOf (B.map fc) (M ⊓ centralizer ({(t : Equiv.Perm (Fin 12))} : Set _)) :=
    fun h => isComponentOf_conj hccM (by rw [← hcoe h]; exact hB)
  rcases hc with hc | hc
  ·
    exfalso
    have hB' := hB0 hc
    have hcard : Nat.card ↥(M ⊓
        centralizer ({(elemA0 : Equiv.Perm (Fin 12))} : Set (Equiv.Perm (Fin 12)))) = 192 := by
      rw [← card_inf_centralizer M elemA0]
      exact card_centralizer_elemA0
    have hdvd : Nat.card J ∣ 192 := by
      rw [← hcardB', ← hcard]
      exact Subgroup.card_dvd_of_le hB'.1
    exact false_of_small_dvd_192 hsmall (hJZ.trans hdvd)
  ·
    have hB' := hB0 hc
    have hcard : Nat.card ↥(M ⊓
        centralizer ({(elemA1 : Equiv.Perm (Fin 12))} : Set (Equiv.Perm (Fin 12)))) = 240 := by
      rw [← card_inf_centralizer M elemA1]
      exact card_centralizer_elemA1
    have hdvd : Nat.card J ∣ 240 := by
      rw [← hcardB', ← hcard]
      exact Subgroup.card_dvd_of_le hB'.1
    have h60 := card_eq_sixty_of_dvd hsmall (hJZ.trans hdvd)
    have hJ60 : Nat.card J = 60 := by
      have hm := Subgroup.card_mul_index (center ↥J)
      rw [Subgroup.index_eq_card, h60] at hm
      have hZ4 : Nat.card (center ↥J) ∣ 2 ^ 2 := by
        have : Nat.card (center ↥J) * 60 ∣ 4 * 60 := by rw [hm]; exact hdvd
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hZ4
      have hi0 : i = 0 := by
        rcases i with _ | i
        · rfl
        · rw [hi'] at hZ
          exact absurd (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero i)))
            (Nat.not_even_iff_odd.mpr hZ)
      rw [hi', hi0, pow_zero, one_mul] at hm
      exact hm.symm
    have hk : Nat.card ↥(M ⊓ centralizer ({(elemA1 : Equiv.Perm (Fin 12))} :
        Set (Equiv.Perm (Fin 12)))) = 2 ^ 2 * Nat.card (B.map fc) := by
      rw [hcard, hcardB', hJ60]
      norm_num
    obtain ⟨hu5, hu1, hv5, hv1, huc, hvc, huv2, huv1, hcw⟩ := m12_witness_facts
    rw [← elemA1_coe] at huc hvc hcw
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hodd5 : Odd 5 := by decide
    have huB : m12u ∈ B.map fc := mem_of_isSubnormal_of_odd hB'.2.1
      (by rw [orderOf_eq_prime hu5 hu1]; exact hodd5)
      (mem_inf.mpr ⟨m12u_mem, mem_centralizer_singleton_iff.mpr huc⟩) 2 hk
    have hvB : m12v ∈ B.map fc := mem_of_isSubnormal_of_odd hB'.2.1
      (by rw [orderOf_eq_prime hv5 hv1]; exact hodd5)
      (mem_inf.mpr ⟨m12v_mem, mem_centralizer_singleton_iff.mpr hvc⟩) 2 hk
    have hzB := (B.map fc).mul_mem huB hvB
    have hz2 : orderOf (m12u * m12v) = 2 := orderOf_eq_prime huv2 huv1
    generalize m12u * m12v = z at hzB hz2 hcw
    have hgz : cc * z * cc⁻¹ ∈ B := by
      obtain ⟨b, hb, hbz⟩ := mem_map.mp hzB
      have : b = cc * z * cc⁻¹ := by
        rw [← hbz]
        simp only [fc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [← this]
      exact hb
    obtain ⟨w, hw, hfw⟩ := mem_map.mp hgz
    have hcP : cc * m12c * cc⁻¹ ∈ M := M.mul_mem (M.mul_mem hccM m12c_mem) (M.inv_mem hccM)
    refine ⟨(w : G), mem_subgroupOf.mp hw, ?_, (e.symm ⟨cc * m12c * cc⁻¹, hcP⟩ : G),
      (e.symm ⟨cc * m12c * cc⁻¹, hcP⟩).2, ?_⟩
    · rw [Subgroup.orderOf_coe, ← orderOf_injective f hf, hfw, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq, hz2]
    · have hγ : f (e.symm ⟨cc * m12c * cc⁻¹, hcP⟩) = cc * m12c * cc⁻¹ := by
        show ((e (e.symm ⟨cc * m12c * cc⁻¹, hcP⟩) : M) : Equiv.Perm (Fin 12)) = _
        rw [MulEquiv.apply_symm_apply]
      have hτ := hcoe hc
      have hN' : (e.symm ⟨cc * m12c * cc⁻¹, hcP⟩)⁻¹ * α' * e.symm ⟨cc * m12c * cc⁻¹, hcP⟩ =
          α' * w := by
        apply hf
        rw [map_mul, map_mul, map_inv, hγ, map_mul, hfw, hτ]
        calc (cc * m12c * cc⁻¹)⁻¹ * (cc * (elemA1 : Equiv.Perm (Fin 12)) * cc⁻¹) *
              (cc * m12c * cc⁻¹) =
              cc * (m12c⁻¹ * (elemA1 : Equiv.Perm (Fin 12)) * m12c) * cc⁻¹ := by group
          _ = cc * ((elemA1 : Equiv.Perm (Fin 12)) * z) * cc⁻¹ := by rw [hcw]
          _ = cc * (elemA1 : Equiv.Perm (Fin 12)) * cc⁻¹ * (cc * z * cc⁻¹) := by group
      exact congrArg Subtype.val hN'

theorem m12 : CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M12 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  obtain ⟨e⟩ := hY
  have := hN
  have e' : ↥N ≃* NativeSporadic.M12 := e
  by_cases hαN : α ∈ N
  · obtain ⟨ζ₀, hζ₀, hζ₀2, γ₀, hγ₀, h⟩ := m12_inner e' hα hαN hJN hJα hJ hsmall hZ
    exact concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hζ₀ hζ₀2 hγ₀ h
  · exact concl_of_coset hα hJN hJα hZ (coset_of_mulAut_outer hC e' beta
      (fun φ h2 hφ => exists_conj_beta_of_outer h2 hφ) hα hαN)

end CFSG.ComponentClassification.GSThmB.CF23I
