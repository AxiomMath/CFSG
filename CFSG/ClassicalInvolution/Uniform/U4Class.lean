module

public import CFSG.ClassicalInvolution.Uniform.U4Quasi

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem exists_twin_product {K : Subgroup F} {z : F} (hK : Mem3 K z)
    {J : Subgroup F} {t : F} (hJ : Mem3 J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) :
    ∃ a ∈ K, ∃ b ∈ conjSub v⁻¹ K, a * a = z ∧ b * b = z ∧ a * b = b * a ∧ a * b = t := by
  classical
  have hKz : IsUniqueInvolution K z := hK.isUniqueInvolution
  have hJt : IsUniqueInvolution J t := hJ.isUniqueInvolution
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_four hv4
  have hvv : v * v = t := mul_self_eq_of_orderOf_four hJt hvJ hv4
  have htK : t ∈ Subgroup.normalizer (K : Set F) := hvv ▸ hvK
  have htz : t * z = z * t := by
    rw [← hvv]
    calc v * v * z = v * (v * z) := by group
      _ = v * (z * v) := by rw [hvz]
      _ = (v * z) * v := by group
      _ = (z * v) * v := by rw [hvz]
      _ = z * (v * v) := by group
  have hvK'' : conjSub v⁻¹ K ≠ K := conjSub_inv_ne hv
  obtain ⟨hK'mem, -, -, -⟩ := hK.twin_facts_conj (inv_comm_of_comm hvz) hvK''.symm
  set K' : Subgroup F := conjSub v⁻¹ K with hK'
  have hKK' : K ≠ K' := hvK''.symm
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ := exists_twin_sylow hK hv2 hvz hvK'' hvK
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  have hnt : ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
    have := nontrivAction hK hJ hne hvJ hv4 hvz hvK hv
    rwa [hvv] at this
  obtain ⟨k, hkK, -, hkact⟩ := typeI hK hJ hne hvJ hv4 hvz hvK hv
  have hnc : ¬ ∀ y ∈ K, ⁅k, y⁆ ∈ oddCoreOf K := by
    intro hc
    apply hnt
    intro y hy
    have e1 : ⁅t, y⁆ = (t * y * t⁻¹ * (k * y * k⁻¹)⁻¹) * ⁅k, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact (oddCoreOf K).mul_mem (hkact y hy) (hc y hy)
  obtain ⟨a₀, ⟨ha₀R, ha₀K⟩, ha₀2, hta₀⟩ :=
    exists_fixed_of_inner hK hR2 hRK htR ht2 htK hkK hkact hnc
  have ha₀pg : IsPGroup 2 (Subgroup.zpowers a₀) := AscFusion.isPGroup_zpowers_of_sq_eq hz2 ha₀2
  have ha₀ord : orderOf a₀ = 4 := AscFusion.orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha₀2
  have hzv : v⁻¹ * z * v = z := conj_eq_of_comm hvz
  set a₀' : F := v⁻¹ * a₀ * v with ha₀'
  obtain ⟨ha₀'R, ha₀'K'⟩ := hRinv a₀ ⟨ha₀R, ha₀K⟩
  have ha₀cm : a₀ * a₀' = a₀' * a₀ := hRcomm a₀ ⟨ha₀R, ha₀K⟩ a₀' ⟨ha₀'R, ha₀'K'⟩
  have ha₀'2 : a₀' * a₀' = z := by
    calc a₀' * a₀' = v⁻¹ * (a₀ * a₀) * v := by rw [ha₀']; group
      _ = z := by rw [ha₀2, hzv]
  have hta₀i : t * a₀⁻¹ = a₀⁻¹ * t := by
    calc t * a₀⁻¹ = a₀⁻¹ * (a₀ * t) * a₀⁻¹ := by group
      _ = a₀⁻¹ * (t * a₀) * a₀⁻¹ := by rw [hta₀]
      _ = a₀⁻¹ * t := by group
  by_cases hJa : a₀ ∈ Subgroup.normalizer (J : Set F)
  ·
    have hc : a₀ * a₀'⁻¹ = a₀'⁻¹ * a₀ := (Commute.inv_right (show Commute a₀ a₀' from ha₀cm)).eq
    have hσJ : a₀'⁻¹ * a₀ ∈ J := by
      have h1 : a₀⁻¹ * v * a₀ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (J : Set F)).inv_mem hJa) v).mp hvJ
        simpa using this
      have : a₀'⁻¹ * a₀ = v⁻¹ * (a₀⁻¹ * v * a₀) := by rw [ha₀']; group
      rw [this]
      exact J.mul_mem (J.inv_mem hvJ) h1
    have hσ2 : (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = 1 := by
      calc (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = a₀'⁻¹ * (a₀ * a₀'⁻¹) * a₀ := by group
        _ = a₀'⁻¹ * (a₀'⁻¹ * a₀) * a₀ := by rw [hc]
        _ = (a₀' * a₀')⁻¹ * (a₀ * a₀) := by group
        _ = 1 := by rw [ha₀'2, ha₀2]; exact inv_mul_cancel z
    have hσt : a₀'⁻¹ * a₀ = t := by
      rcases hJt.unique _ hσJ hσ2 with h | h
      · exfalso
        have hee : a₀' = a₀ := inv_mul_eq_one.mp h
        exact hKK' (hK.eq_of_mem_of_mem_same hK'mem ha₀K (hee ▸ ha₀'K') ha₀pg (by omega))
      · exact h
    refine ⟨a₀, ha₀K, a₀'⁻¹, K'.inv_mem ha₀'K', ha₀2, ?_, hc, ?_⟩
    · calc a₀'⁻¹ * a₀'⁻¹ = (a₀' * a₀')⁻¹ := by group
        _ = z := by rw [ha₀'2, hzi]
    · rw [hc]
      exact hσt
  ·
    have hv3 : 3 ≤ Nat.card (Subgroup.zpowers v) := by rw [Nat.card_zpowers, hv4]; omega
    have hzJ : z ∈ Subgroup.normalizer (J : Set F) :=
      hJ.mem_normalizer_of_commute_of_mem_noncentral hvJ hv2 hv3 hvz.symm
    have hnt_d := nontrivAction hJ hK hne.symm ha₀K ha₀ord hta₀.symm
      (by rw [ha₀2]; exact hzJ) hJa
    obtain ⟨κ, hκJ, hκ2, hκn, hκc⟩ :=
      exists_kappa hJ ha₀ord hta₀.symm hJa (by rw [ha₀2]; exact hzJ) hnt_d
    obtain ⟨δ, hδ2, hzδ, hδa⟩ := AscFusion.dual_delta_facts hz2 ht2 ha₀2 hta₀ hκ2 hκn hκc
    have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
    have hzδ' : δ⁻¹ * z = z * δ⁻¹ := by rw [hδi]; exact hzδ.symm
    set K₃ : Subgroup F := conjSub δ⁻¹ K with hK₃
    have hK₃z : Mem3 K₃ z := hK.conj_of_commute hzδ'
    have hb₃ : a₀ * t ∈ K₃ := by
      have := conj_mem_conjSub (n := δ⁻¹) ha₀K
      rw [inv_inv] at this
      rwa [hδa] at this
    have hK₃K : K₃ ≠ K := by
      intro h
      have htK' : t ∈ K := by
        have h1 : a₀ * t ∈ K := h ▸ hb₃
        have := K.mul_mem (K.inv_mem ha₀K) h1
        simpa using this
      rcases hKz.unique t htK' ht2 with h1 | h1
      · exact hJt.ne_one h1
      · exact hne h1
    have hK₃K' : K₃ = K' := by
      by_contra hK₃K'
      have htK'N : t ∈ Subgroup.normalizer (K' : Set F) := by
        have hvt : v * t = t * v := by rw [← hvv]; group
        have hconj : conjSub t K' = K' := by
          rw [hK', ← conjSub_mul, show t * v⁻¹ = v⁻¹ * t from (inv_comm_of_comm hvt).symm,
            conjSub_mul, conjSub_eq_of_mem_normalizer htK]
        exact AscHypOmega.mem_normalizer_of_conjSub_eq hconj
      have hvK'₂ : v ∉ Subgroup.normalizer (K' : Set F) := by
        intro h
        have h1 : conjSub v K' = K' := conjSub_eq_of_mem_normalizer h
        have h2 : conjSub v K' = K := by
          rw [hK', ← conjSub_mul, mul_inv_cancel, conjSub_one]
        exact hKK' (h2.symm.trans h1)
      apply nontrivAction hK'mem hJ hne hvJ hv4 hvz (hvv ▸ htK'N) hvK'₂
      intro k' hk'
      rw [hvv]
      have e : a₀⁻¹ * (a₀ * t) = t := by group
      have := commutator_mem_of_product hK hK₃z hK'mem hKK' hK₃K' (K.inv_mem ha₀K) hb₃ k' hk'
      rwa [e] at this
    have hb₃' : a₀ * t ∈ K' := hK₃K' ▸ hb₃
    refine ⟨a₀⁻¹, K.inv_mem ha₀K, a₀ * t, hb₃', ?_, ?_, ?_, ?_⟩
    · calc a₀⁻¹ * a₀⁻¹ = (a₀ * a₀)⁻¹ := by group
        _ = z := by rw [ha₀2, hzi]
    · calc a₀ * t * (a₀ * t) = a₀ * (t * a₀) * t := by group
        _ = a₀ * (a₀ * t) * t := by rw [hta₀]
        _ = (a₀ * a₀) * (t * t) := by group
        _ = z := by rw [ha₀2, ht2, mul_one]
    · calc a₀⁻¹ * (a₀ * t) = t := by group
        _ = a₀ * (a₀⁻¹ * t) := by group
        _ = a₀ * (t * a₀⁻¹) := by rw [hta₀i]
        _ = a₀ * t * a₀⁻¹ := by group
    · group

end CFSG.ClassicalInvolution.Uniform.U4
