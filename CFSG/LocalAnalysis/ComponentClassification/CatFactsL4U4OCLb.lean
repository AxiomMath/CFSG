module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZ
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OCL

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL CSL
  CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

theorem eq_one_of_two_pow_of_odd {X : Type*} [Group X] [Finite X] {H : Subgroup X} {x : X}
    (hx : x ∈ H) (hH : Odd (Nat.card H)) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hd1 : orderOf x ∣ Nat.card H := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card H) :=
    Nat.Coprime.pow_left k ((Nat.prime_two.coprime_iff_not_dvd).2 (by
      rw [Nat.two_dvd_ne_zero]
      exact Nat.odd_iff.mp hH))
  exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left hd2).eq_one_of_dvd hd1)

theorem eq_one_of_standard {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hstd : IsStandardSubgroup J) {g τ : G} (hg : g ∉ normalizer (J : Set G))
    (hτJ : ∀ x ∈ J, τ * x = x * τ) (hτg : g * τ = τ * g) {k : ℕ} (hk : τ ^ 2 ^ k = 1) :
    τ = 1 := by
  obtain ⟨-, -, hodd, hnorm, -⟩ := hstd
  have hgC : g ∉ normalizer (centralizer (J : Set G) : Set G) := by rw [hnorm]; exact hg
  have hτC : τ ∈ centralizer (J : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact (hτJ x hx).symm
  have hτCg : τ ∈ conjugate (centralizer (J : Set G)) g := by
    refine ⟨τ, hτC, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hτg, inv_mul_cancel_left]
  exact eq_one_of_two_pow_of_odd (mem_inf.2 ⟨hτC, hτCg⟩) (hodd g hgC) hk

theorem conjAut_mem_range_conj {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hneg : ¬ IsSquare (-1 : F)) {l : Fˣ} (hns : ¬ IsSquare (l : F)) {A P : GL (Fin 4) F}
    (hP : P⁻¹ * A * P = kG (Units.ne_zero l)) :
    ∃ Y : SpecialLinearGroup (Fin 4) F, conjAut 4 F A = MulAut.conj (proj 4 F Y) := by
  have hl0 : (l : F) ≠ 0 := Units.ne_zero l
  have h3 : quadraticChar F (-(l : F)) = 1 := by
    rw [show (-(l : F)) = -1 * l by ring, map_mul, quadraticChar_neg_one_iff_not_isSquare.2 hneg,
      quadraticChar_neg_one_iff_not_isSquare.2 hns]
    norm_num
  obtain ⟨m, hm⟩ := (quadraticChar_one_iff_isSquare (neg_ne_zero.2 hl0)).1 h3
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero, neg_eq_zero] at hm
    exact hl0 hm
  have hdetA : (A : Matrix (Fin 4) (Fin 4) F).det = (l : F) ^ 2 := by
    have h1 := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F).det) hP
    simp only [Units.val_mul, Matrix.det_mul, coe_kG, det_kZero] at h1
    have h3' : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det *
        (P : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [← h1]
    linear_combination (A : Matrix (Fin 4) (Fin 4) F).det * h3'.symm
  set u : Fˣ := Units.mk0 m hm0 with hu
  set A' : GL (Fin 4) F := GeneralLinearGroup.scalar (Fin 4) u⁻¹ * A with hA'
  have hdet' : (A' : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hA', Units.val_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdetA,
      Units.val_inv_eq_inv_val, hu, Units.val_mk0]
    have hl2 : (l : F) ^ 2 = m ^ 4 := by
      rw [show (l : F) = -(m * m) by rw [← hm, neg_neg]]
      ring
    rw [hl2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 4 hm0)]
  refine ⟨⟨A', hdet'⟩, ?_⟩
  have hY : SpecialLinearGroup.toGL (⟨A', hdet'⟩ : SpecialLinearGroup (Fin 4) F) = A' :=
    Units.ext rfl
  calc conjAut 4 F A = conjAut 4 F A' := by
        rw [hA', map_mul,
          (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2 ⟨u⁻¹, rfl⟩,
          one_mul]
    _ = conjAut 4 F (SpecialLinearGroup.toGL ⟨A', hdet'⟩) := by rw [hY]
    _ = MulAut.conj (proj 4 F ⟨A', hdet'⟩) := conjAut_toGL _

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {p f : ℕ} {α : G}
  {J : Subgroup G}

theorem outer_diag_L4 (hcfg : OutInv.OuterL2Config G N p f α J) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {F : Type} [Field F] [Fintype F] (hFq : Fintype.card F = p ^ f)
    (e : ↥N ≃* projectiveSL 4 F) {A : GL (Fin 4) F} (hαA : actP e α = conjAut 4 F A) {τ : G}
    (hτα : τ * α = α * τ) (hτJ : ∀ x ∈ J, τ * x = x * τ) (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) :
    τ ∈ zpowers α := by
  classical
  obtain ⟨-, hC, -, hα2, hαN, hJα, -, hJ, hstd⟩ := hcfg
  obtain ⟨k, hk⟩ := hτ2
  have hq : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_odd hq
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv e (fun J hJ => DiagL.le_range_conj_of_perfect hJ)) hJp
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
  have hA1 : conjAut 4 F A ≠ 1 := fun h => hα1 (eq_one_of_actP_eq_one hC e (hαA ▸ h))
  have hA2 : conjAut 4 F A ^ 2 = 1 := by rw [← hαA, ← map_pow, sq, hαα, map_one]
  have hyα : y * α = α * y := mem_centralizer_singleton_iff.mp (hJα hyJ)
  have hAy : conjAut 4 F A (e ⟨y, hyN⟩) = e ⟨y, hyN⟩ := by
    rw [← hαA]
    have := actP_comm_conj e hyN hyα.symm
    rw [← mul_inv_eq_iff_eq_mul, mul_conj_mul_inv] at this
    exact conj_injective this
  have hys' : orderOf (e ⟨y, hyN⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, hl2, hns⟩ := exists_nonsquare_of_conjAut hq hs hs2 (by rw [hFq]; exact hsq) A hA1
    hA2 hys' hAy
  obtain ⟨P, hP⟩ := exists_conj_eq_kG hns hl2
  have hl : (l : F) ≠ 0 := Units.ne_zero l
  have hl1 : (l : F) ≠ 1 := ne_one_of_not_isSquare hns
  have hneg : IsSquare (-1 : F) := by
    by_contra hneg
    obtain ⟨Y, hY⟩ := conjAut_mem_range_conj hneg hns hP
    apply hαN
    set x : G := (e.symm (proj 4 F Y) : G) with hx
    have hxN : x ∈ N := (e.symm _).2
    have hex : e ⟨x, hxN⟩ = proj 4 F Y := by simp [hx]
    have h1 : actP e (α * x⁻¹) = 1 := by
      rw [map_mul, map_inv, actP_eq_conj e hxN, hex, hαA, hY, mul_inv_cancel]
    rw [mul_inv_eq_one.mp (eq_one_of_actP_eq_one hC e h1)]
    exact hxN
  set e' : ↥N ≃* projectiveSL 4 F := e.trans (conjAut 4 F P⁻¹) with he'
  have hα' : actP e' α = conjAut 4 F (kG hl) := by
    rw [he', actP_trans, hαA, ← map_inv, ← map_mul, ← map_mul, inv_inv, hP]
  set J' : Subgroup (projectiveSL 4 F) := (J.subgroupOf N).map e'.toMonoidHom with hJ'
  have hJ'p : ⁅J', J'⁆ = J' := by
    rw [hJ', ← Subgroup.map_commutator, AZ.subgroupOf_perfect hJN hJp]
  have hfix : ∀ g : G, (∀ j ∈ J, g * j * g⁻¹ = j) → ∀ x ∈ J', actP e' g x = x := by
    rintro g hg _ ⟨z, hz, rfl⟩
    change actP e' g (e' z) = e' z
    rw [actP_apply]
    congr 1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hg _ (mem_subgroupOf.1 hz))
  have hJ'k : ∀ x ∈ J', conjAut 4 F (kG hl) x = x := by
    rw [← hα']
    refine hfix α fun j hj => ?_
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hcJ : Nat.card J' = Nat.card J := by
    rw [hJ', Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
  have hF : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hFq]
  have hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J' := by
    have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥J))
    rw [hcJ, hF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring, ← h1]
    omega
  have hJK : J' = JK F hl := eq_JK h2 hl hns hJ'k hJ'p hcard
  have hτ' : actP e' τ ∈ CA F hl := by
    intro x hx
    rw [← hJK] at hx
    refine hfix τ (fun j hj => ?_) x hx
    rw [hτJ j hj, mul_inv_cancel_right]
  by_cases hr : actP e' τ ∈ (conjAut 4 F).range
  ·
    have hτA : actP e' τ ∈ AK F hl := Subgroup.mem_inf.2 ⟨hτ', hr⟩
    have hk' : actP e' τ ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have hsq2 := sq_eq_one_of_pow_two_pow
      (fun b hb hb4 => sq_eq_one_of_pow_four h4 hneg hl hns hb hb4) k _ hτA hk'
    rcases eq_one_or_eq_of_sq h4 hl hl1 hτA hsq2 with h | h
    · rw [eq_one_of_actP_eq_one hC e' h]
      exact one_mem _
    · have : τ = α := by
        have h1 : actP e' (τ * α⁻¹) = 1 := by rw [map_mul, map_inv, h, hα', mul_inv_cancel]
        exact mul_inv_eq_one.mp (eq_one_of_actP_eq_one hC e' h1)
      rw [this]
      exact mem_zpowers α
  rcases mem_or_exists_mul_dualAut (actP e' τ) with hE | ⟨e₀, he₀, hτe⟩
  · exact absurd (mem_range_of_mem_CA h4 hl hl1 hτ' hE) hr
  obtain ⟨B, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 he₀
  obtain ⟨hσ, a, b, hB⟩ := eq_of_mem_CA_dual_gen h4 hl hl1 B σ (hτe ▸ hτ')
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  rw [hσ1, map_one, mul_one] at hτe
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hab
    rw [not_or, not_not, not_not] at hab
    obtain ⟨rfl, rfl⟩ := hab
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
    rw [hB, eK_zero_zero, Matrix.zero_mul, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet
  set hTs : SpecialLinearGroup (Fin 4) F := ⟨hT (l : F) a b, det_hT _ a b⟩ with hhTs
  have hfixT : actP e' τ (proj 4 F hTs) = proj 4 F hTs := by
    rw [hτe, MulAut.mul_apply, dualAut_proj, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
    set Hm := (hTs : Matrix (Fin 4) (Fin 4) F) with hHm
    set Hi := ((hTs⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHi
    have hHH' : Hi * Hm = 1 := by
      rw [hHm, hHi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hTT : Hmᵀ * Hiᵀ = 1 := by rw [← Matrix.transpose_mul, hHH', Matrix.transpose_one]
    have hform : Hm * (B : Matrix (Fin 4) (Fin 4) F) * Hmᵀ = B := by
      rw [hB]
      exact hT_form _ a b
    have key : (B : Matrix (Fin 4) (Fin 4) F) * Hiᵀ = Hm * B := by
      calc (B : Matrix (Fin 4) (Fin 4) F) * Hiᵀ = Hm * B * Hmᵀ * Hiᵀ := by rw [hform]
        _ = Hm * B * (Hmᵀ * Hiᵀ) := Matrix.mul_assoc _ _ _
        _ = Hm * B := by rw [hTT, Matrix.mul_one]
    rw [key, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  set g : G := (e'.symm (proj 4 F hTs) : G) with hg
  have hgN : g ∈ N := (e'.symm _).2
  have heg : e' ⟨g, hgN⟩ = proj 4 F hTs := by simp [hg]
  have hτg : g * τ = τ * g := by
    have h1 := actP_apply' e' τ hgN
    rw [heg, hfixT, ← heg] at h1
    have h3 : g = τ * g * τ⁻¹ := congrArg Subtype.val (e'.injective h1)
    calc g * τ = τ * g * τ⁻¹ * τ := by rw [← h3]
      _ = τ * g := by group
  have hgJ : g ∉ normalizer (J : Set G) := by
    intro hgJ
    have hn := normalizes_of_mem_normalizer e' hgN hgJ
    rw [heg] at hn
    have hn' : ∀ y, y ∈ JK F hl ↔ proj 4 F hTs * y * (proj 4 F hTs)⁻¹ ∈ JK F hl := by
      intro y
      rw [← hJK]
      exact hn y
    rcases conj_kZero_of_normalizes h2 hl hl1 hns hn' with h | h
    · exact (hT_kZero_ne h2 hab hl).1 h
    · exact (hT_kZero_ne h2 hab hl).2 h
  rw [eq_one_of_standard hstd hgJ hτJ hτg hk]
  exact one_mem _

end OCL

end CFSG.ComponentClassification.CatFactsL4U4
