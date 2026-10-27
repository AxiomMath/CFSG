module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSU

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut UnitaryConj HBlocks StabU DiagU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

theorem centerSylow_U4 {G : Type} [Group G] [Finite G] {N : Subgroup G} {α : G}
    {J R : Subgroup G} {τ : G} (hcfg : OutInv.CenterSylowConfig G N α J R τ) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hαN : α ∈ N)
    (hU : Blueprint.LieModel ↥N .PSU 4 p f)
    (hJ : Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p (2 * f)) : τ ∈ zpowers α := by
  classical
  obtain ⟨hNn, hC, hα2, hJα, -, hstd, hRM, hRα, hRS, hτα, hτJ, hτR, -⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, K, _, _, hK, ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Finite K := h.finite
  set Φ := AZ.actE eU with hΦ
  set θ := thU p f K with hθ
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
  obtain ⟨Yα, hYα⟩ := thU_surjective (eU ⟨α, hαN⟩)
  have hz : IsCU h (Yα : GL (Fin 4) K) (Φ α) := by
    rw [hΦ, actE_eq_conj eU hαN, ← hYα]
    exact isCU_conj h Yα
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
  have hys' : orderOf (eU ⟨y, hyN⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, P, hbl, hP, hAP⟩ := exists_hyp_of_diag h hp2 hz hα1' hα2' hs hs2 hsq hys'
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
  obtain ⟨hJU, hJL, -⟩ := eq_of_perfect_diag h hp2 P hP hl0 hz hAP (hfix α hαfix) (hperf hJp)
    hcard
  have hJeq := eq_map_commutator h hp2 P hP hl0 hz hAP (hfix α hαfix) (hperf hJp) hcard _ rfl
  have hl4 : l ^ 4 = 1 := by
    have hdet : ((Yα : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 :=
      ((mem_unitarySU_iff h).1 Yα.2).1
    have h1 := congrArg Matrix.det hAP
    rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, det_X1] at h1
    have hP0 : (P : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
    exact (mul_right_eq_self₀.mp h1.symm).resolve_right hP0
  have hq4 := card_mod_four_of_inner h hp2 hl4 hbl
  obtain ⟨ζ, hζ8, hζ4⟩ := exists_order_eight h hp2
  set T := tU h hq4 P hP hζ8 hζ4 with hT
  have hTcP : cP P T = blk ζ 0 0 (h.bar ζ)⁻¹ := cP_tU h hq4 P hP hζ8 hζ4
  have hT2 := thU_tU_sq_ne_one h hp2 hq4 P hP hζ8 hζ4
  set S := sU h P hP with hS
  have hScP : cP P S = blk 0 1 1 0 := cP_hypSU h P hP _ _ _
  have hYcP : cP P Yα = blk l 0 0 (-l) := by rw [cP_eq_of_mul P hAP, X1_eq_blk]
  have hTY : θ T * θ Yα = θ Yα * θ T := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply eq_of_cP_eq P
    rw [cP_mul, cP_mul, hTcP, hYcP, blk_mul_blk, blk_mul_blk, mul_comm ζ l,
      mul_comm (h.bar ζ)⁻¹ (-l)]
  have hSY : θ S * θ Yα = θ Yα * θ S := by
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul]
    apply thU_eq_one_of_val (c := -1)
    have h1 : cP P (S * Yα * (Yα * S)⁻¹) = -1 := by
      rw [_root_.mul_inv_rev, cP_mul, cP_mul, cP_mul, cP_inv_of P (M := blk 0 (-1) (-1) 0) (by
          rw [hScP]; ext i j; fin_cases i <;> fin_cases j <;>
            simp [blk, Matrix.mul_apply, Fin.sum_univ_four]),
        cP_inv_of P (M := blk l⁻¹ 0 0 (-l)⁻¹) (by
          rw [hYcP, blk_mul_blk, inv_mul_cancel₀ hl0, inv_mul_cancel₀ (neg_ne_zero.2 hl0),
            blk_one]),
        hScP, hYcP]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [blk, Matrix.mul_apply, Fin.sum_univ_four, hl0]
    rw [val_eq_cP P, h1, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, neg_smul, one_smul]
  have hzconj : Φ α = MulAut.conj (θ Yα) := by
    rw [hΦ, actE_eq_conj eU hαN, ← hYα]
  have hcommz : ∀ {x : StatedProj (StatedSU 4 (p ^ f) K)}, x * θ Yα = θ Yα * x →
      MulAut.conj x * Φ α = Φ α * MulAut.conj x := by
    intro x hx
    rw [hzconj, ← map_mul, ← map_mul, hx]
  set u : G := (eU.symm (θ T) : G) with hu
  set w : G := (eU.symm (θ S) : G) with hw
  have huN : u ∈ N := (eU.symm (θ T)).2
  have hwN : w ∈ N := (eU.symm (θ S)).2
  have heu : eU ⟨u, huN⟩ = θ T := by simp [hu]
  have hew : eU ⟨w, hwN⟩ = θ S := by simp [hw]
  have hαY : eU ⟨α, hαN⟩ = θ Yα := hYα.symm
  have hM : ∀ {g : G} (hgN : g ∈ N), (∀ x, x ∈ J' ↔ eU ⟨g, hgN⟩ * x * (eU ⟨g, hgN⟩)⁻¹ ∈ J') →
      eU ⟨g, hgN⟩ * θ Yα = θ Yα * eU ⟨g, hgN⟩ →
      g ∈ (N ⊓ normalizer (J : Set G)) ⊓ centralizer ({α} : Set G) := by
    intro g hgN hgJ hgk
    refine mem_inf.2 ⟨mem_inf.2 ⟨hgN, mem_normalizer_of_normalizes' eU hJN hgN hgJ⟩, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : eU (⟨g, hgN⟩ * ⟨α, hαN⟩) = eU (⟨α, hαN⟩ * ⟨g, hgN⟩) := by
      rw [map_mul, map_mul, hαY, hgk]
    exact congrArg Subtype.val (eU.injective h1)
  have hTnorm : ∀ x, x ∈ J' ↔ θ T * x * (θ T)⁻¹ ∈ J' :=
    normalizes_of_mem_CAU (conj_mem_CAU_of_blk h hp2 P hl0 hAP hJeq hTcP)
  have hSnorm : ∀ x, x ∈ J' ↔ θ S * x * (θ S)⁻¹ ∈ J' :=
    normalizes_of_comm h hp2 hz hJeq (hcommz hSY)
  have huM := hM huN (by rw [heu]; exact hTnorm) (by rw [heu]; exact hTY)
  have hwM := hM hwN (by rw [hew]; exact hSnorm) (by rw [hew]; exact hSY)
  have hu8 : u ^ 2 ^ 3 = 1 := by
    have hT8 : T ^ 8 = 1 := by
      apply eq_of_cP_eq P
      have e8 : ∀ n : ℕ, cP P (T ^ n) = blk (ζ ^ n) 0 0 ((h.bar ζ)⁻¹ ^ n) := by
        intro n
        induction n with
        | zero => rw [pow_zero, cP_one, pow_zero, pow_zero, blk_one]
        | succ n ih => rw [pow_succ, cP_mul, ih, hTcP, blk_mul_blk, pow_succ, pow_succ]
      rw [e8, cP_one, hζ8, inv_pow, ← map_pow, hζ8, map_one, inv_one, blk_one]
    have h2 : (⟨u, huN⟩ : ↥N) ^ 8 = 1 := by
      apply eU.injective
      rw [map_pow, heu, ← map_pow, hT8, map_one, map_one]
    have := congrArg Subtype.val h2
    simpa using this
  have hw2 : w ^ 2 ^ 1 = 1 := by
    have hS2 : θ S ^ 2 = 1 := by
      rw [← map_pow]
      apply thU_eq_one_of_val (c := -1)
      rw [val_eq_cP P, sq, cP_mul, hScP, swap_mul_swap, Matrix.mul_neg, Matrix.mul_one,
        Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, neg_smul, one_smul]
    have h2 : (⟨w, hwN⟩ : ↥N) ^ 2 = 1 := by
      apply eU.injective
      rw [map_pow, hew, hS2, map_one]
    have := congrArg Subtype.val h2
    simpa using this
  obtain ⟨c₁, hc₁, hc₁R⟩ := AltCent.exists_conj_le hRM hRα hRS (zpowers_le.mpr huM)
    (CSL.isPGroup_zpowers hu8)
  obtain ⟨c₂, hc₂, hc₂R⟩ := AltCent.exists_conj_le hRM hRα hRS (zpowers_le.mpr hwM)
    (CSL.isPGroup_zpowers hw2)
  have hc₁N : c₁ ∈ N := (mem_inf.1 (mem_inf.1 hc₁).1).1
  have hc₂N : c₂ ∈ N := (mem_inf.1 (mem_inf.1 hc₂).1).1
  have hc₁α : c₁ * α = α * c₁ := mem_centralizer_singleton_iff.mp (mem_inf.1 hc₁).2
  have hc₂α : c₂ * α = α * c₂ := mem_centralizer_singleton_iff.mp (mem_inf.1 hc₂).2
  have hcomm : ∀ {g : G} (hgN : g ∈ N), g * α = α * g →
      eU ⟨g, hgN⟩ * θ Yα = θ Yα * eU ⟨g, hgN⟩ := by
    intro g hgN hgα
    rw [← hαY, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgα
  have hτcomm : ∀ {g x : G} (hgN : g ∈ N) (hxN : x ∈ N), g * x * g⁻¹ ∈ R →
      Φ τ * MulAut.conj (eU ⟨g, hgN⟩ * eU ⟨x, hxN⟩ * (eU ⟨g, hgN⟩)⁻¹) =
        MulAut.conj (eU ⟨g, hgN⟩ * eU ⟨x, hxN⟩ * (eU ⟨g, hgN⟩)⁻¹) * Φ τ := by
    intro g x hgN hxN hR
    have hm : g * x * g⁻¹ ∈ N := mul_mem (mul_mem hgN hxN) (inv_mem hgN)
    have h1 := actE_comm_conj eU hm (hτR _ hR)
    have e1 : eU ⟨g * x * g⁻¹, hm⟩ = eU ⟨g, hgN⟩ * eU ⟨x, hxN⟩ * (eU ⟨g, hgN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rwa [e1] at h1
  have h₁ := hτcomm hc₁N huN (hc₁R u (mem_zpowers u))
  have h₂ := hτcomm hc₂N hwN (hc₂R w (mem_zpowers w))
  rw [heu] at h₁
  rw [hew] at h₂
  have hτ' : Φ τ ∈ CAU J' := fun x hx => hfix τ (fun j hj => by
    rw [hτJ j hj, mul_inv_cancel_right]) x hx
  rcases eq_one_or_eq_z h hp2 P hP hl0 hz hAP hJeq hJU hJL hτ' (x₁ := eU ⟨c₁, hc₁N⟩)
      (x₂ := eU ⟨c₂, hc₂N⟩) (hcommz (hcomm hc₁N hc₁α)) (hcommz (hcomm hc₂N hc₂α)) hTcP hT2
      h₁ h₂ with h3 | h3
  · have : τ = 1 := AZ.eq_one_of_actE_eq_one hC eU h3
    rw [this]
    exact one_mem _
  · have : τ = α := by
      have h1 : Φ (τ * α⁻¹) = 1 := by rw [map_mul, map_inv, h3, mul_inv_cancel]
      exact mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eU h1)
    rw [this]
    exact mem_zpowers α

end CSU

end CFSG.ComponentClassification.CatFactsL4U4
