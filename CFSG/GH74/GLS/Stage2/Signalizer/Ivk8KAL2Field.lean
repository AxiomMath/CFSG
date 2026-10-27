module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Cov
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2DihCls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Rigid

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem kaL2_eq_one_of_fixed (σ τ : F ≃+* F) (hσ : orderOf σ = 2) (hτ : Odd (orderOf τ))
    (hfix : ∀ t ∈ fixedField σ, τ t = t) : τ = 1 := by
  have hs : Nat.card (fixedField σ) ^ 2 = Nat.card F := by
    have := fixedField_card_pow σ
    rwa [hσ] at this
  have ht := fixedField_card_pow τ
  have hle : Nat.card (fixedField σ) ≤ Nat.card (fixedField τ) := by
    refine Nat.card_le_card_of_injective
      (fun x : fixedField σ => (⟨x.1, (mem_fixedField_iff τ _).mpr (hfix x.1 x.2)⟩ : fixedField τ))
      ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have h1 : Nat.card (fixedField σ) ^ orderOf τ ≤ Nat.card (fixedField σ) ^ 2 := by
    calc Nat.card (fixedField σ) ^ orderOf τ
        ≤ Nat.card (fixedField τ) ^ orderOf τ := Nat.pow_le_pow_left hle _
      _ = Nat.card F := ht
      _ = Nat.card (fixedField σ) ^ 2 := hs.symm
  have hq : 1 < Nat.card (fixedField σ) := one_lt_card_fixedField σ
  have h2 : orderOf τ ≤ 2 := (Nat.pow_le_pow_iff_right hq).mp h1
  have h3 := Nat.odd_iff.mp hτ
  have h4 := orderOf_pos τ
  exact orderOf_eq_one_iff.mp (by omega)

theorem kaL2_field_rigid (e : K ≃* L2 F) (σ₀ : F ≃+* F) (hσ₀ : orderOf σ₀ = 2)
    (hchar : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e'' : MulAut K)
    (hord : IsPGroup p ↥(Subgroup.zpowers e''))
    (hfix : ∀ r ∈ (kaFix (kaSlMap σ₀)).map (kaL2Cover e), e'' r = r) : e'' = 1 := by
  have hodd : Odd (orderOf e'') := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hord) ⟨e'', Subgroup.mem_zpowers e''⟩
    rw [Subgroup.orderOf_mk] at hm
    rw [hm]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨g, τ, hdec, hτord⟩ := kaL2_aut_decomp e e''
  obtain ⟨G, hGg⟩ := QuotientGroup.mk_surjective g
  have hmk : Matrix.ProjGenLinGroup.mk G = g := hGg
  have hτodd : Odd (orderOf τ) := Odd.of_dvd_nat hodd hτord
  have key : ∀ M ∈ kaFix (kaSlMap σ₀),
      g * pgl2FieldAut F τ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk M : PSL2 F)) * g⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk M : PSL2 F) := by
    intro M hM
    have h1 := hfix (kaL2Cover e M) ⟨M, hM, rfl⟩
    have h2 := kaL2_toPGL_apply e g τ (kaL2Cover e M)
    rw [← hdec, h1, toPSL_kaL2Cover] at h2
    exact h2.symm
  have hτF : ∀ t ∈ fixedField σ₀, τ t = t := by
    intro t ht
    obtain ⟨c, hrel⟩ := kaL2_matrix_rel τ G (kaSlTr t) (hmk ▸ key _ (kaSlTr_mem ht))
    have hG := kaL2_det_ne_zero G
    have := kaL2_trace_fixed hchar τ hτodd _ _ (kaSlTr t).2 hG c hrel
    simpa [kaSlTr, Matrix.trace_fin_two] using this
  have hτ1 : τ = 1 := kaL2_eq_one_of_fixed σ₀ τ hσ₀ hτodd hτF
  subst hτ1
  have hg1 : Matrix.ProjGenLinGroup.mk G = (1 : PGL2 F) := by
    obtain ⟨c, hu⟩ := kaL2_matrix_rel 1 G kaSlU (hmk ▸ key _ (kaSlU_mem σ₀))
    obtain ⟨c', hl⟩ := kaL2_matrix_rel 1 G kaSlL (hmk ▸ key _ (kaSlL_mem σ₀))
    have hG := kaL2_det_ne_zero G
    have hmap : ∀ A : Matrix (Fin 2) (Fin 2) F, A.map (⇑(1 : F ≃+* F)) = A := fun A => by
      ext i j
      rfl
    rw [hmap] at hu hl
    obtain ⟨s, hs0, hGs⟩ := kaL2_scalar_of_rel G.val hG c c' hu hl
    apply (QuotientGroup.eq_one_iff G).mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 s hs0, ?_⟩
    apply Units.ext
    rw [hGs]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]
  have hg1' : g = 1 := by
    rw [← hmk]
    exact hg1
  rw [hdec, hg1', map_one, map_one, mul_one]

end Rigid

section FieldClass

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem kaL2_field_pure (e : K ≃* L2 F) (σ₀ : F ≃+* F) (hσ₀ : orderOf σ₀ = 2)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card (fixedField σ₀)) :
    KAAll (fieldAutHom e σ₀) := by
  have hLq := kaFix_slMap_quasisimple σ₀ (by omega)
  refine ka_all_of_cover (conj_injective_of_L2 e) (kaL2Cover e) (kaL2Cover_surjective e)
    (kaL2Cover_central e) (kaSlMap σ₀) (kaL2Cover_field e σ₀) (kaFix (kaSlMap σ₀)) le_rfl
    (Subgroup.isPerfect_iff.mp hLq.1) (fun g hg => hg) hLq ?_
  intro p hp hp2 e'' hord _ hfix
  exact kaL2_field_rigid e σ₀ hσ₀ (kaL2_two_ne_zero hodd) hp hp2 e'' hord hfix

omit [Finite K] in
theorem kaL2_aut_nine (h9 : Nat.card F = 9) (τ : F ≃+* F) (hτ : Odd (orderOf τ)) : τ = 1 := by
  have h1 := fixedField_card_pow τ
  have hodd : Odd (Nat.card F) := by rw [h9]; decide
  have hq : Odd (Nat.card (fixedField τ)) := odd_card_fixedField τ hodd
  have hq1 : 1 < Nat.card (fixedField τ) := one_lt_card_fixedField τ
  have hq3 : 3 ≤ Nat.card (fixedField τ) := by
    have := Nat.odd_iff.mp hq
    omega
  have h2 : 3 ^ orderOf τ ≤ 3 ^ 2 := by
    calc 3 ^ orderOf τ ≤ Nat.card (fixedField τ) ^ orderOf τ := Nat.pow_le_pow_left hq3 _
      _ = 3 ^ 2 := by rw [h1, h9]; norm_num
  have h3 : orderOf τ ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have h4 := Nat.odd_iff.mp hτ
  have h5 := orderOf_pos τ
  exact orderOf_eq_one_iff.mp (by omega)

theorem kaL2_field_nine (hF : L2Field F) (e : K ≃* L2 F) (σ₀ : F ≃+* F) (hσ₀ : orderOf σ₀ = 2)
    (h3 : Nat.card (fixedField σ₀) = 3) : KAAll (fieldAutHom e σ₀) := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  have h9 : Nat.card F = 9 := by
    have := fixedField_card_pow σ₀
    rw [hσ₀, h3] at this
    omega
  have hinn : ∀ e' ∈ P, e' ∈ innAut K := by
    intro e' he'
    obtain ⟨g, τ, hdec, hτord⟩ := kaL2_aut_decomp e e'
    have hodd' := ka_odd_of_mem_pGroup hp hp2 hPp he'
    have hτ1 : τ = 1 := kaL2_aut_nine h9 τ (Odd.of_dvd_nat hodd' hτord)
    have hmem : e' ∈ innDiagSub e := by
      rw [hdec, hτ1, map_one, mul_one]
      exact ⟨g, rfl⟩
    exact kaL2_odd_mem_innAut hF e hmem hodd'
  refine ⟨fun x => commutator_mem_innAut hF e x _, ?_⟩
  have hcard : Nat.card ↥(fixedSubgroup K (fieldAutHom e σ₀)) = 24 := by
    rw [card_fixedSubgroup_of_even e σ₀ (by rw [hσ₀]; exact even_two), h3]
    norm_num
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  have hX0p := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub (fieldAutHom e σ₀) := kaInner_le_fixSub hinj hcomm
  have hX0cyc : IsCyclic ↥(kaInner P) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hX0p)
    have hdvd : Nat.card ↥(kaInner P) ∣ 24 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hX0C
    rw [hm] at hdvd
    have hc8 : Nat.Coprime (p ^ m) (2 ^ 3) :=
      Nat.Coprime.pow m 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h3' : p ^ m ∣ 3 := hc8.dvd_of_dvd_mul_left (by simpa using hdvd)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h | h
    · have hc1 : Nat.card ↥(kaInner P) = 1 := by rw [hm, h]
      have hsub := (Nat.card_eq_one_iff_unique.mp hc1).1
      exact isCyclic_of_subsingleton
    · have hc3 : Nat.card ↥(kaInner P) = 3 := by rw [hm, h]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card (p := 3) hc3
  let ψ : ↥(kaInner P) →* ↥P :=
    ((MulAut.conj : K →* MulAut K).comp (kaInner P).subtype).codRestrict P (fun y => y.2)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨e', he'⟩
    obtain ⟨y, hy⟩ := hinn e' he'
    exact ⟨⟨y, by rw [mem_kaInner, hy]; exact he'⟩, Subtype.ext hy⟩
  exact isCyclic_of_surjective ψ hsurj

omit [Finite K] in
theorem kaL2_field_class (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1) (hα1 : α ≠ 1)
    (hαD : α ∉ innDiagSub e) :
    ∃ (σ₀ : F ≃+* F) (h : MulAut K), orderOf σ₀ = 2 ∧ α = h * fieldAutHom e σ₀ * h⁻¹ := by
  set x : PGammaL2 F := (pgammaAut e).symm α with hx
  have hΦx : pgammaAut e x = α := by simp [hx]
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) hα1
  have hord : orderOf x = 2 := by
    have h := MulEquiv.orderOf_eq (pgammaAut e) x
    rw [hΦx, hα2] at h
    exact h.symm
  have hσ : x.right ≠ 1 := by
    intro h1
    apply hαD
    obtain ⟨g, hg⟩ : ∃ g, x = SemidirectProduct.inl g :=
      ⟨x.left, SemidirectProduct.ext (by simp) (by simpa using h1)⟩
    rw [hg, pgammaAut_inl] at hΦx
    exact ⟨g, hΦx⟩
  have hσ2 : orderOf x.right = 2 := by
    have hdvd : orderOf x.right ∣ orderOf x := orderOf_map_dvd (SemidirectProduct.rightHom) x
    rw [hord] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ
    · exact h
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr x hord hσ
  refine ⟨x.right, innDiagHom e C, hσ2, ?_⟩
  have hx' : x = SemidirectProduct.inl C * SemidirectProduct.inr x.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have h2 : α = pgammaAut e (SemidirectProduct.inl C * SemidirectProduct.inr x.right *
      (SemidirectProduct.inl C)⁻¹) := by rw [← hx', hΦx]
  rw [h2, map_mul, map_mul, map_inv, pgammaAut_inl, pgammaAut_inr]

omit [Finite K] [Finite F] in
theorem kaL2_congr_eq_mul (h f : MulAut K) : MulAut.congr h f = h * f * h⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem kaAll_L2 (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  by_cases hαD : α ∈ innDiagSub e
  · exact kaL2_dihedral_thm hF e α hα hα1 hαD
  · obtain ⟨σ₀, h, hσ₀, hαeq⟩ := kaL2_field_class e α hα hα1 hαD
    have hq : Odd (Nat.card (fixedField σ₀)) := odd_card_fixedField σ₀ hF.1
    have hq1 : 1 < Nat.card (fixedField σ₀) := one_lt_card_fixedField σ₀
    have hK : KAAll (fieldAutHom e σ₀) := by
      by_cases h3 : Nat.card (fixedField σ₀) = 3
      · exact kaL2_field_nine hF e σ₀ hσ₀ h3
      · refine kaL2_field_pure e σ₀ hσ₀ hF.1 ?_
        have := Nat.odd_iff.mp hq
        omega
    have := KAAll.of_mulEquiv (h : K ≃* K) hK
    rw [kaL2_congr_eq_mul] at this
    rw [hαeq]
    exact this

end FieldClass

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
