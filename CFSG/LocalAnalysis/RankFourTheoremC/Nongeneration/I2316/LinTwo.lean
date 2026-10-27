module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.GroupLemmas
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.PSLTwo
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90

public section

open CFSG.GorensteinWalter

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

variable {F : Type} [Field F] [Finite F]

theorem psl2FieldAut_sUpper (σ : F ≃+* F) : psl2FieldAut F σ (sUpper F) = sUpper F := by
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (tUpper F)) = _
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom (tUpper F)) =
    QuotientGroup.mk (tUpper F)
  congr 1
  ext a b
  simp [tUpper, Matrix.SpecialLinearGroup.transvection_coe]

theorem psl2FieldAut_sLower (σ : F ≃+* F) : psl2FieldAut F σ (sLower F) = sLower F := by
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (tLower F)) = _
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom (tLower F)) =
    QuotientGroup.mk (tLower F)
  congr 1
  ext a b
  simp [tLower, Matrix.SpecialLinearGroup.transvection_coe]

theorem exists_toPGL_of_pow_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : IsOddPrimePower (Nat.card F)) {g : PGL2 F} (hg : g ^ p = 1) :
    ∃ y : PSL2 F, Matrix.ProjectiveSpecialLinearGroup.toPGL y = g := by
  set H := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hidx : H.index = 2 := pgl2_psl2Range_index_eq_two F hK
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (PGL2 F ⧸ H) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  have h2 : ∀ x : PGL2 F ⧸ H, x ^ 2 = 1 := fun x => by
    have := pow_card_eq_one' (G := PGL2 F ⧸ H) (x := x)
    rwa [hcard] at this
  have hp1 : (QuotientGroup.mk g : PGL2 F ⧸ H) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h1 : (QuotientGroup.mk g : PGL2 F ⧸ H) = 1 := by
    have e1 := hp1
    rw [hk, pow_succ, pow_mul, h2 _, one_pow, one_mul] at e1
    exact e1
  exact (QuotientGroup.eq_one_iff g).1 h1

theorem finite_pGammaL2 : Finite (PGammaL2 F) := by
  haveI : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem planesGenerate_psl2 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) : PlanesGenerate p (PSL2 F) := by
  intro E hE hEc hnot
  have hpp : p.Prime := Fact.out
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card F = p ^ f := by
    haveI := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F p
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  set Φ := pGammaL2ToMulAutPSL2 F hK hcard with hΦ
  have hinj : Function.Injective Φ := pGammaL2ToMulAutPSL2_injective F hK hcard
  have hsurj : Function.Surjective Φ := pGammaL2ToMulAutPSL2_surjective F hf hK hcard
  set Ê : Subgroup (PGammaL2 F) := E.comap Φ
  have hÊe : ∀ x ∈ Ê, x ^ p = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hx
  have hÊc : Nat.card Ê = p ^ 2 := by
    have h1 : Ê.map Φ = E := Subgroup.map_comap_eq_self_of_surjective hsurj E
    have h2 := Subgroup.card_map_of_injective (K := Ê) (f := Φ) hinj
    rw [h1] at h2
    rw [← h2, hEc]
  obtain ⟨x, hxÊ, hx1, hxN⟩ : ∃ x ∈ Ê, x ≠ 1 ∧
      x ∈ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    haveI : IsCyclic (PGammaL2 F ⧸ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range) :=
      pGammaL2_quotient_pgl_isCyclic F hK
    haveI : Finite (PGammaL2 F) := finite_pGammaL2
    haveI : Finite (PGammaL2 F ⧸ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range) :=
      inferInstance
    obtain ⟨x, hxÊ, hx1, hxk⟩ := exists_ne_one_mem_ker_of_cyclic
      (QuotientGroup.mk' (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range) hpp hÊe hÊc
    exact ⟨x, hxÊ, hx1, (QuotientGroup.eq_one_iff x).1 hxk⟩
  obtain ⟨b, hbÊ, hbN⟩ : ∃ b ∈ Ê, b ∉ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    by_contra hcon
    push Not at hcon
    apply hnot
    intro e' he'
    obtain ⟨e, rfl⟩ := hsurj e'
    obtain ⟨g, rfl⟩ := hcon e he'
    have hg : g ^ p = 1 := by
      have h1 : (SemidirectProduct.inl g : PGammaL2 F) ^ p = 1 := hÊe _ he'
      rw [← map_pow] at h1
      exact SemidirectProduct.inl_injective (h1.trans (map_one SemidirectProduct.inl).symm)
    obtain ⟨y, hy⟩ := exists_toPGL_of_pow_eq_one hp2 hK hg
    refine ⟨y, ?_⟩
    rw [hΦ, pGammaL2ToMulAutPSL2_inl, ← hy, pgl2InnerAutPSL2_toPGL]
  have hbp : b ^ p = 1 := hÊe b hbÊ
  have hσ1 : b.right ≠ 1 := by
    intro h
    apply hbN
    refine ⟨b.left, ?_⟩
    have := SemidirectProduct.inl_left_mul_inr_right b
    rwa [h, map_one, mul_one] at this
  have hσp : b.right ^ p = 1 := by
    have h := map_pow (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) b p
    rw [hbp, map_one] at h
    simpa [SemidirectProduct.rightHom_eq_right] using h.symm
  have hord : orderOf b.right = p := orderOf_eq_prime hσp hσ1
  obtain ⟨C, hC⟩ := pGammaL2_conj_inr_of_pow_eq_one b (by rw [hord]; exact hbp)
  have hbC : b = SemidirectProduct.inl C * SemidirectProduct.inr b.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  obtain ⟨g, rfl⟩ := hxN
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  have hgp : g ^ p = 1 := by
    have h1 : (SemidirectProduct.inl g : PGammaL2 F) ^ p = 1 := hÊe _ hxÊ
    rw [← map_pow] at h1
    exact SemidirectProduct.inl_injective (h1.trans (map_one SemidirectProduct.inl).symm)
  have hg''p : (C⁻¹ * g * C) ^ p = 1 := by
    have := conj_pow (a := C⁻¹) (b := g) (i := p)
    rw [inv_inv] at this
    rw [this, hgp]
    simp
  obtain ⟨u, hu⟩ := exists_toPGL_of_pow_eq_one hp2 hK hg''p
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one] at hu
    apply hg1
    have h3 : g = C * (C⁻¹ * g * C) * C⁻¹ := by group
    rw [← hu] at h3
    simpa using h3
  have hup : u ^ p = 1 := by
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_pow, hu, hg''p, map_one]
  set α : MulAut (PSL2 F) := Φ (SemidirectProduct.inl C)⁻¹ with hα
  have hαinv : α⁻¹ = Φ (SemidirectProduct.inl C) := by rw [hα, map_inv, inv_inv]
  have hbE : Φ b ∈ E := hbÊ
  have hxE : Φ (SemidirectProduct.inl g) ∈ E := hxÊ
  have hσmem : Φ (SemidirectProduct.inr b.right) ∈ conjPlane α E := by
    rw [mem_conjPlane, hαinv, hα]
    have : Φ (SemidirectProduct.inl C) * Φ (SemidirectProduct.inr b.right) *
        Φ (SemidirectProduct.inl C)⁻¹ = Φ b := by
      rw [← map_mul, ← map_mul, ← hbC]
    rw [this]
    exact hbE
  set g'' : PGL2 F := C⁻¹ * g * C with hg''
  have hxmem : Φ (SemidirectProduct.inl g'') ∈ conjPlane α E := by
    rw [mem_conjPlane, hαinv, hα]
    have : Φ (SemidirectProduct.inl C) * Φ (SemidirectProduct.inl g'') *
        Φ (SemidirectProduct.inl C)⁻¹ = Φ (SemidirectProduct.inl g) := by
      rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hg'']
      congr 2
      group
    rw [this]
    exact hxE
  have hΦx : Φ (SemidirectProduct.inl g'') = MulAut.conj u := by
    rw [hΦ, pGammaL2ToMulAutPSL2_inl, ← hu, pgl2InnerAutPSL2_toPGL]
  have hxne : Φ (SemidirectProduct.inl g'') ≠ 1 := by
    intro h
    apply hg1
    have h2 : (SemidirectProduct.inl g'' : PGammaL2 F) = 1 := hinj (h.trans (map_one Φ).symm)
    have h3 : g'' = 1 :=
      SemidirectProduct.inl_injective (h2.trans (map_one SemidirectProduct.inl).symm)
    have h4 : g = C * g'' * C⁻¹ := by rw [hg'']; group
    rw [h4, h3]
    simp
  have hσne : Φ (SemidirectProduct.inr b.right) ≠ 1 := by
    intro h
    apply hσ1
    have h2 := hinj (h.trans (map_one Φ).symm)
    exact SemidirectProduct.inr_injective (h2.trans (map_one SemidirectProduct.inr).symm)
  have hfix1 : Φ (SemidirectProduct.inr b.right) (sUpper F) = sUpper F := by
    rw [hΦ, pGammaL2ToMulAutPSL2_inr]
    exact psl2FieldAut_sUpper _
  have hfix2 : Φ (SemidirectProduct.inr b.right) (sLower F) = sLower F := by
    rw [hΦ, pGammaL2ToMulAutPSL2_inr]
    exact psl2FieldAut_sLower _
  have hgen : Subgroup.closure (fixedPts (conjPlane α E)) = ⊤ := by
    refine eq_top_of_centralizer_le (F := F) hp2 hu1 hup ?_
      (Subgroup.subset_closure ⟨_, hσmem, hσne, hfix1⟩)
      (Subgroup.subset_closure ⟨_, hσmem, hσne, hfix2⟩)
    intro k hk
    apply Subgroup.subset_closure
    refine ⟨Φ (SemidirectProduct.inl g''), hxmem, hxne, ?_⟩
    rw [hΦx]
    have hc := Subgroup.mem_centralizer_iff.1 hk u (Set.mem_singleton u)
    rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
  exact closure_fixedPts_eq_top_of_conj α hgen

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
