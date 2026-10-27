module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwGen
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRLev
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

private theorem exists_conj_le_map_of_sylow_trn {M Y : Type*} [Group M] [Finite M] [Group Y]
    (f : M →* Y) (P₀ : Sylow 2 M) {P : Subgroup Y} (hP : IsPGroup 2 P) (hPr : P ≤ f.range) :
    ∃ m : M, ∀ p ∈ P, (f m)⁻¹ * p * f m ∈ (P₀ : Subgroup M).map f := by
  have hf : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  haveI : Finite ↥f.range := Finite.of_surjective _ hf
  obtain ⟨Q₁, hQ₁⟩ := (hP.comap_subtype (K := f.range)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥f.range (P₀.mapSurjective hf) Q₁
  obtain ⟨m, rfl⟩ := hf g
  refine ⟨m, fun p hp => ?_⟩
  have h1 : (⟨p, hPr hp⟩ : ↥f.range) ∈ (Q₁ : Subgroup ↥f.range) := hQ₁ hp
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Sylow.coe_mapSurjective] at h1
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp h1
  refine Subgroup.mem_map.mpr ⟨q, hq, ?_⟩
  have := congrArg Subtype.val hqe
  simpa [MulAut.smul_def] using this

private theorem mem_ssS_trn {x : WrE} : x ∈ ssS ↔ x.e = false ∧ x.a ∈ S ∧ x.b ∈ S := Iff.rfl

private theorem conj_noswap_trn (c₁ c₂ p q : Equiv.Perm (Fin 42)) :
    (⟨c₁, c₂, false⟩ : WrE) * ⟨p, q, false⟩ * (⟨c₁, c₂, false⟩ : WrE)⁻¹ =
      ⟨c₁ * p * c₁⁻¹, c₂ * q * c₂⁻¹, false⟩ := by
  simp [WrE.mul_def, WrE.inv_def, mul_assoc]

private theorem conj_swap_b_trn (u v s : Equiv.Perm (Fin 42)) :
    (⟨u, v, true⟩ : WrE) * ⟨1, s, false⟩ * (⟨u, v, true⟩ : WrE)⁻¹ =
      ⟨v * s * v⁻¹, 1, false⟩ := by
  simp [WrE.mul_def, WrE.inv_def, mul_assoc]

private theorem sq_noswap_trn {p q : Equiv.Perm (Fin 42)} :
    (⟨p, q, false⟩ : WrE) * ⟨p, q, false⟩ = 1 ↔ p * p = 1 ∧ q * q = 1 := by
  simp [WrE.mul_def, WrE.one_def]

private def CJtrn (B : Subgroup WrE) (x y : WrE) : Prop := ∃ c ∈ B, c * x * c⁻¹ = y

private theorem CJtrn.refl_trn (B : Subgroup WrE) (x : WrE) : CJtrn B x x :=
  ⟨1, B.one_mem, by simp⟩

private theorem CJtrn.symm_trn {B : Subgroup WrE} {x y : WrE} (h : CJtrn B x y) : CJtrn B y x := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c⁻¹, B.inv_mem hc, by group⟩

private theorem CJtrn.trans_trn {B : Subgroup WrE} {x y z : WrE} (h₁ : CJtrn B x y)
    (h₂ : CJtrn B y z) : CJtrn B x z := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨d, hd, rfl⟩ := h₂
  exact ⟨d * c, B.mul_mem hd hc, by group⟩

private theorem isD_decomp_trn {x : WrE} (hx : IsD x) :
    ∃ p q : Equiv.Perm (Fin 42), x = ⟨p, q, false⟩ ∧ p ∈ S ∧ q ∈ S ∧ p ≠ 1 ∧ q ≠ 1 ∧
      p * p = 1 ∧ q * q = 1 := by
  obtain ⟨xa, xb, xe⟩ := x
  obtain ⟨he, h2, h1a, h1b, hSa, hSb⟩ := hx
  change xe = false at he
  subst he
  obtain ⟨h2a, h2b⟩ := sq_noswap_trn.mp h2
  exact ⟨xa, xb, rfl, hSa, hSb, h1a, h1b, h2a, h2b⟩

private theorem isUU_decomp_trn {x : WrE} (hx : IsUU x) :
    ∃ p q : Equiv.Perm (Fin 42), x = ⟨p, q, false⟩ ∧ isUni p ∧ isUni q := by
  obtain ⟨xa, xb, xe⟩ := x
  obtain ⟨he, -, hpa, hpb⟩ := hx
  change xe = false at he
  subst he
  exact ⟨xa, xb, rfl, hpa, hpb⟩

private theorem exists_A_normal_trn {B : Subgroup WrE}
    (hB : B ≤ wrR) (hsw : ∃ c ∈ B, c.e = true) {x : WrE} (hx : IsA x) :
    ∃ s : Equiv.Perm (Fin 42), s ∈ S ∧ s ≠ 1 ∧ s * s = 1 ∧ CJtrn B x ⟨s, 1, false⟩ := by
  obtain ⟨⟨u, v, e⟩, hwB, hwe⟩ := hsw
  change e = true at hwe
  subst hwe
  obtain ⟨hu, hv⟩ : u ∈ R ∧ v ∈ R := hB hwB
  obtain ⟨xa, xb, xe⟩ := x
  obtain ⟨he, h2, hcase⟩ := hx
  change xe = false at he
  subst he
  obtain ⟨h2a, h2b⟩ := sq_noswap_trn.mp h2
  rcases hcase with ⟨ha1, hb1, hbS⟩ | ⟨hb1, ha1, haS⟩
  · change xa = 1 at ha1
    subst ha1
    change xb ≠ 1 at hb1
    change xb ∈ S at hbS
    refine ⟨v * xb * v⁻¹, conj_mem_S hv hbS, ?_, ?_,
      ⟨⟨u, v, true⟩, hwB, conj_swap_b_trn u v xb⟩⟩
    · intro h1
      exact hb1 (conj_eq_one_iff.mp h1)
    · calc v * xb * v⁻¹ * (v * xb * v⁻¹) = v * (xb * xb) * v⁻¹ := by group
        _ = 1 := by rw [h2b]; group
  · change xb = 1 at hb1
    subst hb1
    change xa ≠ 1 at ha1
    change xa ∈ S at haS
    exact ⟨xa, haS, ha1, h2a, CJtrn.refl_trn B _⟩

private theorem exists_conj_of_type_trn {B : Subgroup WrE}
    (hB : B ≤ wrR) (hss : ssS ≤ B) (hsw : ∃ c ∈ B, c.e = true) {x x' : WrE}
    (hty : (IsA x ∧ IsA x') ∨ (IsD x ∧ IsD x') ∨ (IsUU x ∧ IsUU x')) :
    ∃ c ∈ B, c * x * c⁻¹ = x' := by
  rcases hty with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ | ⟨hx, hx'⟩
  · obtain ⟨s, hsS, hs1, hs2, h1⟩ := exists_A_normal_trn hB hsw hx
    obtain ⟨s', hsS', hs1', hs2', h1'⟩ := exists_A_normal_trn hB hsw hx'
    obtain ⟨c, hcS, hc⟩ := inner_invol_conj hsS hsS' hs2 hs2' hs1 hs1'
    have h3 : CJtrn B ⟨s, 1, false⟩ ⟨s', 1, false⟩ :=
      ⟨⟨c, 1, false⟩, hss (mem_ssS_trn.mpr ⟨rfl, hcS, S.one_mem⟩), by
        rw [conj_noswap_trn, hc]; simp⟩
    exact CJtrn.trans_trn (CJtrn.trans_trn h1 h3) (CJtrn.symm_trn h1')
  · obtain ⟨p, q, rfl, hpS, hqS, hp1, hq1, hp2, hq2⟩ := isD_decomp_trn hx
    obtain ⟨p', q', rfl, hpS', hqS', hp1', hq1', hp2', hq2'⟩ := isD_decomp_trn hx'
    obtain ⟨c₁, hc₁S, hc₁⟩ := inner_invol_conj hpS hpS' hp2 hp2' hp1 hp1'
    obtain ⟨c₂, hc₂S, hc₂⟩ := inner_invol_conj hqS hqS' hq2 hq2' hq1 hq1'
    exact ⟨⟨c₁, c₂, false⟩, hss (mem_ssS_trn.mpr ⟨rfl, hc₁S, hc₂S⟩), by
      rw [conj_noswap_trn, hc₁, hc₂]⟩
  · obtain ⟨p, q, rfl, hp, hq⟩ := isUU_decomp_trn hx
    obtain ⟨p', q', rfl, hp', hq'⟩ := isUU_decomp_trn hx'
    obtain ⟨c₁, hc₁S, hc₁⟩ := uni_conj hp hp'
    obtain ⟨c₂, hc₂S, hc₂⟩ := uni_conj hq hq'
    exact ⟨⟨c₁, c₂, false⟩, hss (mem_ssS_trn.mpr ⟨rfl, hc₁S, hc₂S⟩), by
      rw [conj_noswap_trn, hc₁, hc₂]⟩

private theorem ssS_le_range_trn {G : Type} [Group G] {M K : Subgroup G} {t : G}
    {ρ : ↥M →* WrE} (hρ : TwModel M K t ρ) : ssS ≤ ρ.range := by
  rintro ⟨xa, xb, xe⟩ hx
  obtain ⟨he, haS, hbS⟩ := mem_ssS_trn.mp hx
  change xe = false at he
  subst he
  obtain ⟨m₁, -, hm₁⟩ := hρ.K_surj xa haS
  obtain ⟨m₂, -, hm₂⟩ := hρ.Kt_surj xb hbS
  refine ⟨m₁ * m₂, ?_⟩
  rw [map_mul, hm₁, hm₂]
  simp [WrE.mul_def]

private theorem odd_card_ker_trn {G : Type} [Group G] [Finite G] {M K : Subgroup G} {t : G}
    {ρ : ↥M →* WrE} (hρ : TwModel M K t ρ) : Odd (Nat.card ρ.ker) := by
  have hker : ρ.ker = pPrimeCore 2 ↥M := by
    ext m
    rw [MonoidHom.mem_ker, hρ.ker_iff, oddIn, Subgroup.mem_map]
    constructor
    · rintro ⟨o, ho, hoe⟩
      have : o = m := Subtype.ext hoe
      rwa [← this]
    · intro hm
      exact ⟨m, hm, rfl⟩
  rw [hker]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}

variable {ρ : ↥(normalizer (W : Set G)) →* WrE}

theorem invol_conj_of_type (h : TwHyp G a x J S' W K T t)
    (hρ : TwModel (normalizer (W : Set G)) K t ρ) {m₁ m₂ : ↥(normalizer (W : Set G))}
    (h₁ : m₁ * m₁ = 1) (h₂ : m₂ * m₂ = 1)
    (hty : (IsA (ρ m₁) ∧ IsA (ρ m₂)) ∨ (IsD (ρ m₁) ∧ IsD (ρ m₂)) ∨
      (IsUU (ρ m₁) ∧ IsUU (ρ m₂))) :
    ∃ g : ↥(normalizer (W : Set G)), g⁻¹ * m₁ * g = m₂ := by
  have hker := odd_card_ker_trn hρ
  have htM : t ∈ normalizer (W : Set G) := h.hTsyl.1 h.htT
  have hsw : ∃ c ∈ ρ.range, c.e = true :=
    ⟨ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩, (hρ.swap_iff ⟨t, htM⟩).mpr h.htK⟩
  have hB : ρ.range ≤ wrR := by
    rintro _ ⟨m, rfl⟩
    exact hρ.mem_wrR m
  obtain ⟨c, ⟨g, rfl⟩, hc⟩ := exists_conj_of_type_trn hB (ssS_le_range_trn hρ) hsw hty
  have h3 : ρ (g * m₁ * g⁻¹) = ρ m₂ := by
    rw [map_mul, map_mul, map_inv]
    exact hc
  have h4 : (g * m₁ * g⁻¹) * (g * m₁ * g⁻¹) = 1 := by
    calc (g * m₁ * g⁻¹) * (g * m₁ * g⁻¹) = g * (m₁ * m₁) * g⁻¹ := by group
      _ = 1 := by rw [h₁]; group
  obtain ⟨o, -, ho⟩ := exists_conj_of_ker ρ hker h4 h₂ h3
  refine ⟨g⁻¹ * o, ?_⟩
  rw [← ho]
  group

theorem exists_conj_le_imgT (h : TwHyp G a x J S' W K T t)
    (hρ : TwModel (normalizer (W : Set G)) K t ρ) {P : Subgroup WrE} (hP : IsPGroup 2 P)
    (hPr : P ≤ ρ.range) :
    ∃ m : ↥(normalizer (W : Set G)),
      ∀ p ∈ P, (ρ m)⁻¹ * p * ρ m ∈ imgT T (normalizer (W : Set G)) ρ := by
  obtain ⟨-, P₀, hP₀⟩ := h.hTsyl
  obtain ⟨m, hm⟩ := exists_conj_le_map_of_sylow_trn ρ P₀ hP hPr
  refine ⟨m, fun p hp => ?_⟩
  have := hm p hp
  rwa [hP₀] at this

end CFSG.ComponentClassification.GrSLit.L34Tw
