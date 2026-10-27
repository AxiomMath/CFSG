module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePAlt

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem exists_conj_eq_of_inv_mul_mem_odd {X : Type*} [Group X] [Finite X] {O : Subgroup X}
    (hO : Odd (Nat.card O)) {t t' : X} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hn : t⁻¹ * t' ∈ O) : ∃ o ∈ O, o * t * o⁻¹ = t' := by
  set n := t⁻¹ * t' with hndef
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have ht'n : t' = t * n := by rw [hndef]; group
  have htn : t * n * t⁻¹ = n⁻¹ := by
    have h1 : t * n * (t * n) = 1 := by rw [← ht'n, ht']
    rw [hti]
    calc t * n * t = (t * n * (t * n)) * n⁻¹ := by group
      _ = n⁻¹ := by rw [h1, one_mul]
  have hodd : Odd (orderOf n) := by
    have h := orderOf_dvd_natCard (⟨n, hn⟩ : O)
    rw [Subgroup.orderOf_mk] at h
    exact hO.of_dvd_nat h
  obtain ⟨r, hr⟩ := hodd
  set k := r + 1 with hk
  set m := n ^ k with hm
  have hmm : m * m = n := by
    rw [hm, ← pow_add, show k + k = orderOf n + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have htm : t * m * t⁻¹ = m⁻¹ := by
    have := map_pow (MulAut.conj t) n k
    simp only [MulAut.conj_apply] at this
    rw [hm, this, htn, inv_pow]
  refine ⟨m⁻¹, O.inv_mem (O.pow_mem hn k), ?_⟩
  have htm' : t * m = m⁻¹ * t := by
    calc t * m = t * m * t⁻¹ * t := by group
      _ = m⁻¹ * t := by rw [htm]
  calc m⁻¹ * t * m⁻¹⁻¹ = m⁻¹ * (t * m) := by group
    _ = m⁻¹ * m⁻¹ * t := by rw [htm']; group
    _ = (m * m)⁻¹ * t := by group
    _ = n⁻¹ * t := by rw [hmm]
    _ = t * n * t⁻¹ * t := by rw [htn]
    _ = t' := by rw [ht'n]; group

theorem exists_conj_mul_eq_of_alternating {K : Type} [Group K] {L : Subgroup K}
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) {l₁ l₂ : L}
    (h1 : ((l₁ : L) : L ⧸ Subgroup.center L) * ((l₁ : L) : L ⧸ Subgroup.center L) = 1)
    (h1' : ((l₁ : L) : L ⧸ Subgroup.center L) ≠ 1)
    (h2 : ((l₂ : L) : L ⧸ Subgroup.center L) * ((l₂ : L) : L ⧸ Subgroup.center L) = 1)
    (h2' : ((l₂ : L) : L ⧸ Subgroup.center L) ≠ 1) {k : K}
    (hk : k ∈ Subgroup.centralizer (L : Set K)) :
    ∃ ω ∈ L, ∃ c ∈ Subgroup.center L, ω * (k * (l₁ : K)) * ω⁻¹ = k * (l₂ : K) * (c : K) := by
  obtain ⟨g, hg⟩ := exists_conj_of_involution_of_alternating eA h1 h1' h2 h2'
  obtain ⟨ω, rfl⟩ := QuotientGroup.mk_surjective g
  have hc : (ω⁻¹ * l₂ * ω)⁻¹ * l₁ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hg.symm
  set c := (ω⁻¹ * l₂ * ω)⁻¹ * l₁ with hcdef
  have hl₁ : l₁ = ω⁻¹ * l₂ * ω * c := by rw [hcdef]; group
  have hcω : ω * c = c * ω := Subgroup.mem_center_iff.mp hc ω
  refine ⟨ω, ω.2, c, hc, ?_⟩
  have hkω : (ω : K) * k = k * ω := Subgroup.mem_centralizer_iff.mp hk ω ω.2
  have hkey : (ω : K) * (l₁ : K) * (ω : K)⁻¹ = (l₂ : K) * (c : K) := by
    rw [hl₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (ω : K) * ((ω : K)⁻¹ * l₂ * ω * c) * (ω : K)⁻¹ = l₂ * ((ω : K) * c * (ω : K)⁻¹) by
      group, show (ω : K) * (c : K) = (c : K) * ω from congrArg Subtype.val hcω]
    group
  calc (ω : K) * (k * (l₁ : K)) * (ω : K)⁻¹ = (ω * k) * (l₁ : K) * (ω : K)⁻¹ := by group
    _ = k * ((ω : K) * (l₁ : K) * (ω : K)⁻¹) := by rw [hkω]; group
    _ = k * (l₂ : K) * (c : K) := by rw [hkey]; group

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
