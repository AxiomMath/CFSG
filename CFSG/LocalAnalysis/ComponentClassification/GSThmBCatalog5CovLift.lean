module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Fus

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.GSThmB.Fus23

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

noncomputable abbrev alphaK : MulAut (OddBar h.K) := actW h hKa ⟨h.a, h.a_mem_normalizer⟩

include hKa in
theorem a_conj_mem_K (k : h.K) : h.a * (k : H) * h.a⁻¹ ∈ h.K :=
  (mem_normalizer_iff.mp (W_le_normalizer_K h hKa h.a_mem_normalizer) k).mp k.2

include hKa in
theorem alphaK_mk (k : h.K) :
    alphaK hKa (k : OddBar h.K) = ((⟨h.a * k * h.a⁻¹, a_conj_mem_K hKa k⟩ : h.K) : OddBar h.K) :=
  rfl

include hKa in
theorem concl_of_twist (hI : CF23InnerFusion) (hZJ : center (OddBar h.J) = ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hexc : ¬ CF23Exception ↥(NL hKa) (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)))
    (htw : ∀ c ∈ center (OddBar h.K), ∃ k : OddBar h.K, (alphaK hKa k)⁻¹ * k = c) :
    h.Fus23Concl := by
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  have hres : GSRestricted ↥(NL hKa) := by
    rcases h.type_K with hr | ⟨hne, -⟩
    · exact OddQuot.gsRestricted_of_mulEquiv (eZ.symm.trans eN.symm) hr
    · exact absurd hKa hne
  have hJt : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) .PSL 2 p f) ∨
      Nonempty (↥(Jhat hKa) ⧸ center ↥(Jhat hKa) ≃* alternatingGroup (Fin 7)) := by
    rcases hJ with hA | ⟨p, f, hp, hp2, hf, hq, hm⟩
    · obtain ⟨e7⟩ := hA
      exact Or.inr ⟨eJ.trans e7⟩
    · exact Or.inl ⟨p, f, hp, hp2, hf, hq, OddQuot.lieModel_of_equiv eJ.symm hm⟩
  obtain ⟨z, hzD, hzS, hz2, hzP⟩ := exists_z h hZJ
  refine ⟨z, hzD, hzS, hz2, hzP, ?_⟩
  have hzJB := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hzK : z ∈ h.K := fixedLayer_le_K h hKa hzJB
  have hza : z * h.a = h.a * z := h.comm_a (h.D_le_S hzD)
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  set ζ : ↥(GAut hKa) := phi hKa (wbarMk h.B ⟨z, K_le_W h hzK⟩) with hζ
  have hζJ : ζ ∈ Jhat hKa := ⟨wbarMk h.B ⟨z, K_le_W h hzK⟩, ⟨⟨z, K_le_W h hzK⟩, hzJB, rfl⟩, rfl⟩
  obtain ⟨γ, hγN, hγ⟩ : ∃ γ ∈ NL hKa, γ⁻¹ * phi hKa (abar h) * γ = phi hKa (abar h) * ζ := by
    by_cases hζ1 : ζ = 1
    · exact ⟨1, one_mem _, by rw [hζ1]; group⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hζ2 : ζ * ζ = 1 := by
        rw [hζ, ← map_mul, ← map_mul, ← map_one (phi hKa), ← map_one (wbarMk h.B)]
        congr 2
        exact Subtype.ext hz2'
      have hζo : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hζ2) hζ1
      exact hI _ (NL hKa) (NL_normal hKa) (centralizer_NL hKa) hres _ _ (orderOf_phi_abar' hKa)
        (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2 (Jhat_standard hKa) hJt
        (odd_card_center_Jhat hKa hZJ) hexc ζ hζJ hζo
  obtain ⟨g, hgK, y, hy, hg⟩ := exists_conj_of_inner hKa hzK hza hz2' hγN hγ
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hainv : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨-, hyZ⟩ := mem_inf.mp hy
  rw [map_fusionZStar_eq] at hyZ
  obtain ⟨hyK, hyC⟩ := mem_inf.mp hyZ
  set yK : h.K := ⟨y, hyK⟩ with hyKdef
  have hyc : (yK : OddBar h.K) ∈ center (OddBar h.K) := mem_center_of_mem_kernel hKa hyC
  obtain ⟨kb, hkb⟩ := htw _ (inv_mem hyc)
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
  set gK : h.K := ⟨g, hgK⟩ with hgKdef
  set zK : h.K := ⟨z, hzK⟩ with hzKdef
  set x : h.K := k₀ * gK with hxdef
  set ax : h.K := ⟨h.a * x * h.a⁻¹, a_conj_mem_K hKa x⟩ with haxdef
  set c : h.K := ax⁻¹ * x with hcdef
  have hag : (⟨h.a * gK * h.a⁻¹, a_conj_mem_K hKa gK⟩ : h.K)⁻¹ * gK = zK * yK := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgKdef, hzKdef, hyKdef]
    calc (h.a * g * h.a⁻¹)⁻¹ * g = h.a * g⁻¹ * h.a⁻¹ * g := by group
      _ = h.a⁻¹ * (g⁻¹ * h.a * g) := by rw [hainv]; group
      _ = z * y := by rw [hg]; group
  have hc : (c : OddBar h.K) = (zK : OddBar h.K) := by
    have h1 : (c : OddBar h.K) = (alphaK hKa (x : OddBar h.K))⁻¹ * (x : OddBar h.K) := by
      rw [alphaK_mk, hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h2 : (alphaK hKa (gK : OddBar h.K))⁻¹ * (gK : OddBar h.K) =
        (zK : OddBar h.K) * (yK : OddBar h.K) := by
      rw [alphaK_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hag,
        QuotientGroup.mk_mul]
    have hyc' := mem_center_iff.mp (inv_mem hyc)
    rw [h1, hxdef, QuotientGroup.mk_mul, map_mul, mul_inv_rev]
    calc (alphaK hKa (gK : OddBar h.K))⁻¹ * (alphaK hKa (k₀ : OddBar h.K))⁻¹ *
          ((k₀ : OddBar h.K) * (gK : OddBar h.K)) =
        (alphaK hKa (gK : OddBar h.K))⁻¹ *
          ((alphaK hKa (k₀ : OddBar h.K))⁻¹ * (k₀ : OddBar h.K)) * (gK : OddBar h.K) := by
          group
      _ = (alphaK hKa (gK : OddBar h.K))⁻¹ * (yK : OddBar h.K)⁻¹ * (gK : OddBar h.K) := by
          rw [hkb]
      _ = (yK : OddBar h.K)⁻¹ * ((alphaK hKa (gK : OddBar h.K))⁻¹ * (gK : OddBar h.K)) := by
          rw [hyc' (alphaK hKa (gK : OddBar h.K))⁻¹]
          group
      _ = (zK : OddBar h.K) := by
          rw [h2, ← mul_assoc, ← hyc' (zK : OddBar h.K), mul_assoc, inv_mul_cancel, mul_one]
  set o : h.K := zK⁻¹ * c with hodef
  have ho : o ∈ pPrimeCore 2 h.K := by
    rw [← QuotientGroup.eq_one_iff, hodef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc,
      inv_mul_cancel]
  have hoodd : Odd (orderOf (o : H)) := odd_orderOf_of_mem_oddCoreIn ⟨o, ho, rfl⟩
  have hxa : (x : H)⁻¹ * h.a * x = h.a * z * o := by
    have hco : (c : H) = z * o := by
      simp only [hodef, Subgroup.coe_mul, Subgroup.coe_inv, hzKdef]
      group
    have hcx : (c : H) = h.a * (x : H)⁻¹ * h.a⁻¹ * x := by
      rw [hcdef, Subgroup.coe_mul, Subgroup.coe_inv, haxdef]
      group
    calc (x : H)⁻¹ * h.a * x = (h.a * h.a) * (x : H)⁻¹ * h.a * x := by rw [ha2, one_mul]
      _ = h.a * (h.a * (x : H)⁻¹ * h.a⁻¹ * x) := by rw [hainv]; group
      _ = h.a * z * o := by rw [← hcx, hco, mul_assoc]
  have hu : (h.a * z) * (h.a * z) = 1 := by
    calc h.a * z * (h.a * z) = h.a * (z * h.a) * z := by group
      _ = h.a * (h.a * z) * z := by rw [hza]
      _ = (h.a * h.a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2', one_mul]
  have huo : ((h.a * z) * o) * ((h.a * z) * o) = 1 := by
    rw [← hxa]
    calc (x : H)⁻¹ * h.a * x * ((x : H)⁻¹ * h.a * x) = (x : H)⁻¹ * (h.a * h.a) * x := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨n, hn⟩ := exists_zpow_conj_eq_of_odd hu huo hoodd
  refine ⟨(x : H) * (o : H) ^ n, K_le_W h (mul_mem x.2 (zpow_mem o.2 n)), ?_⟩
  calc ((x : H) * (o : H) ^ n)⁻¹ * h.a * ((x : H) * (o : H) ^ n) =
      ((o : H) ^ n)⁻¹ * ((x : H)⁻¹ * h.a * x) * (o : H) ^ n := by group
    _ = ((o : H) ^ n)⁻¹ * (h.a * z * o) * (o : H) ^ n := by rw [hxa]
    _ = h.a * z := hn

end CFSG.ComponentClassification.GSThmB.Cov
