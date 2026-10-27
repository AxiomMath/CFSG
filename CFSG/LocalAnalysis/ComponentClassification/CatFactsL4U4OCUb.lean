module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCLb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OCU

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut UnitaryConj HBlocks StabU DiagU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB CSU

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {p f : ℕ} {α : G}
  {J : Subgroup G}

theorem outer_diag_U4 (hcfg : OutInv.OuterL2Config G N p f α J) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (eU : ↥N ≃* StatedProj (StatedSU 4 (p ^ f) K)) {A : GL (Fin 4) K}
    (hαA : IsCU h A (AZ.actE eU α)) {τ : G} (hτα : τ * α = α * τ)
    (hτJ : ∀ x ∈ J, τ * x = x * τ) (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) : τ ∈ zpowers α := by
  classical
  obtain ⟨-, hC, -, hα2, hαN, hJα, -, hJ, hstd⟩ := hcfg
  obtain ⟨k, hk⟩ := hτ2
  have : Finite K := h.finite
  set Φ := AZ.actE eU with hΦ
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv eU (fun J hJ => DiagU.le_range_conj_of_perfect_U h hp2 hJ)) hJp
  have hJtype : IsSec8JType (↥J ⧸ center ↥J) p f := Or.inl hJ
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have := Fact.mk hs
  obtain ⟨⟨y, hyJ⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) s
    (hsJ.trans (Subgroup.card_quotient_dvd_card _))
  rw [Subgroup.orderOf_mk] at hys
  have hyN := hJN hyJ
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα2
    norm_num at hα2
  have hα1' : Φ α ≠ 1 := fun h1 => hα1 (AZ.eq_one_of_actE_eq_one hC eU h1)
  have hα2' : Φ α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  obtain ⟨hperf, hcJ, hfix⟩ := AZ.image_facts eU hJN
  set J' := (J.subgroupOf N).map eU.toMonoidHom with hJ'
  have hαfix : ∀ j ∈ J, α * j * α⁻¹ = j := by
    intro j hj
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hy' : eU ⟨y, hyN⟩ ∈ J' := ⟨⟨y, hyN⟩, mem_subgroupOf.2 hyJ, rfl⟩
  have hys' : orderOf (eU ⟨y, hyN⟩) = s := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, P, hbl, hP, hAP⟩ := exists_hyp_of_diag h hp2 hαA hα1' hα2' hs hs2 hsq hys'
    (hfix α hαfix _ hy')
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbl
    exact zero_ne_one (neg_eq_zero.1 hbl.symm).symm
  have hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J' := by
    have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥J))
    rw [hcJ, ← h1]
    omega
  obtain ⟨hJU, hJL, -⟩ := eq_of_perfect_diag h hp2 P hP hl0 hαA hAP (hfix α hαfix) (hperf hJp)
    hcard
  have hq3 : p ^ f % 4 = 3 := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h13 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    rcases h13 with h1 | h3
    · exfalso
      obtain ⟨Y, hY⟩ := exists_conj_of_mod_four h hp2 h1 P hbl hαA hAP
      apply hαN
      set x : G := (eU.symm (thU p f K Y) : G) with hx
      have hxN : x ∈ N := (eU.symm _).2
      have hex : eU ⟨x, hxN⟩ = thU p f K Y := by simp [hx]
      have h2 : Φ (α * x⁻¹) = 1 := by
        rw [map_mul, map_inv, hΦ, actE_eq_conj eU hxN, hex, ← hΦ, hY, mul_inv_cancel]
      rw [mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eU h2)]
      exact hxN
    · exact h3
  have hτ' : Φ τ ∈ CAU J' := fun x hx => hfix τ (fun j hj => by
    rw [hτJ j hj, mul_inv_cancel_right]) x hx
  by_cases hr : Φ τ ∈ InnU p f K h
  · have hτA : Φ τ ∈ CAU J' ⊓ InnU p f K h := Subgroup.mem_inf.2 ⟨hτ', hr⟩
    have hk' : Φ τ ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have hsq2 := DiagL.sq_eq_one_of_pow_two_pow
      (fun b hb hb4 => sq_eq_one_of_pow_four_AU h hp2 hq3 P hP hJU hJL hb hb4) k _ hτA hk'
    rcases eq_one_or_eq_of_sq_AU h hp2 P hP hl0 hαA hAP hJU hJL hτA hsq2 with h3 | h3
    · rw [AZ.eq_one_of_actE_eq_one hC eU h3]
      exact one_mem _
    · have : τ = α := by
        have h1 : Φ (τ * α⁻¹) = 1 := by rw [map_mul, map_inv, h3, mul_inv_cancel]
        exact mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eU h1)
      rw [this]
      exact mem_zpowers α
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  rcases innU_or_fixed h hp2 P hP hμ (Φ τ) (hτ' _ (hJU 1)) (hτ' _ (hJL 1)) (hτ' _ (hJU μ)) with
    h3 | ⟨g, hgfix, β, γ, hβ0, hgc⟩
  · exact absurd h3 hr
  have hgN := not_mem_normalizer_diag h hp2 P hP hl0 hαA hAP (bar_ne_of_generator h hμ)
    (hfix α hαfix) hJU hJL hβ0 hgc
  set w : G := (eU.symm (thU p f K g) : G) with hw
  have hwN : w ∈ N := (eU.symm _).2
  have hew : eU ⟨w, hwN⟩ = thU p f K g := by simp [hw]
  have hτw : w * τ = τ * w := by
    have h1 := AZ.actE_apply eU τ ⟨w, hwN⟩
    rw [← hΦ, hew, hgfix, ← hew] at h1
    have h3 : w = τ * w * τ⁻¹ := by
      have := congrArg Subtype.val (eU.injective h1)
      rw [MulAut.conjNormal_apply] at this
      exact this
    calc w * τ = τ * w * τ⁻¹ * τ := by rw [← h3]
      _ = τ * w := by group
  have hwJ : w ∉ normalizer (J : Set G) := by
    intro hwJ
    apply hgN
    rw [mem_normalizer_iff]
    intro x
    have := normalizes_of_mem_normalizer' eU hwN hwJ x
    rw [hew] at this
    exact this
  rw [OCL.eq_one_of_standard hstd hwJ hτJ hτw hk]
  exact one_mem _

end OCU

end CFSG.ComponentClassification.CatFactsL4U4
