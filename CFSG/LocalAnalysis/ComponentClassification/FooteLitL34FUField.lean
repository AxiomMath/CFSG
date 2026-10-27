module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUCover
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUType
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUCount
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem zStarIn_map (φ : X ≃* X) (K : Subgroup X) :
    zStarIn (K.map φ.toMonoidHom) = (zStarIn K).map φ.toMonoidHom := by
  rw [zStarIn, zStarIn, GSThmB.map_fusionZStar_eq, GSThmB.map_fusionZStar_eq,
    Subgroup.map_inf _ _ _ φ.injective, map_coreActionKernel]

omit [Finite X] in
theorem commZStar_map (φ : X ≃* X) (K : Subgroup X) (v : X) :
    commZStar (K.map φ.toMonoidHom) (φ v) = (commZStar K v).map φ.toMonoidHom := by
  ext x
  rw [mem_map_equiv, mem_commZStar, mem_commZStar, mem_map_equiv, zStarIn_map, mem_map_equiv]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

omit [Finite X] in
theorem card_commZStar_conjugate (K : Subgroup X) (v g : X) :
    Nat.card (commZStar (conjugate K g) (g⁻¹ * v * g)) = Nat.card (commZStar K v) ∧
      Nat.card (zStarIn (conjugate K g)) = Nat.card (zStarIn K) := by
  have hv : (MulAut.conj g⁻¹) v = g⁻¹ * v * g := by simp
  constructor
  · rw [conjugate, ← hv, commZStar_map]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  · rw [conjugate, zStarIn_map]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective

theorem mem_coreActionKernel_of_pow_eight
    {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hL34 : IsL34Type (K ⧸ Open.fusionZStar K)) {b r g : X} (hb2 : b * b = 1) (hr8 : r ^ 8 = b)
    (hrN : g⁻¹ * r * g ∈ normalizer (K : Set X)) : g⁻¹ * b * g ∈ coreActionKernel K := by
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL34
  set r' := g⁻¹ * r * g with hr'
  have hHN : zpowers r' ≤ normalizer (K : Set X) := zpowers_le.mpr hrN
  obtain ⟨ψ, hψR, hψ⟩ := GrS4.exists_realization_hom hHN hqS hqsurj hqker
  set ρ := ψ ⟨r', mem_zpowers r'⟩ with hρ
  have hpow : ∀ n : ℕ, (g⁻¹ * r * g) ^ n = g⁻¹ * r ^ n * g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  have hr8' : r' ^ 8 = g⁻¹ * b * g := by rw [hr', hpow, hr8]
  have hmem : g⁻¹ * b * g ∈ zpowers r' := hr8' ▸ pow_mem (mem_zpowers r') 8
  have he8 : (⟨r', mem_zpowers r'⟩ : ↥(zpowers r')) ^ 8 = ⟨g⁻¹ * b * g, hmem⟩ :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hr8')
  have h16 : ρ ^ 16 = 1 := by
    have e1 : (⟨r', mem_zpowers r'⟩ : ↥(zpowers r')) ^ 16 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, show (16 : ℕ) = 8 + 8 from rfl, pow_add,
        hr8']
      calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
        _ = 1 := by rw [hb2]; group
    rw [hρ, ← map_pow, e1, map_one]
  have h8 : ρ ^ 8 = 1 := pow_eight_eq_one (hψR _) h16
  have hb0 : ψ ⟨g⁻¹ * b * g, hmem⟩ = 1 := by rw [← he8, map_pow, ← hρ, h8]
  refine GrS4.mem_coreActionKernel_of_realization_eq_one hK (hHN hmem) hqker fun e => ?_
  have := hψ ⟨g⁻¹ * b * g, hmem⟩ e
  rw [hb0, inv_one, one_mul, mul_one] at this
  exact this

theorem card_commZStar_conj (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {b : X}
    (hb : orderOf b = 2) {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({b} : Set X)))
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hbK : b ∈ K) {v : X} (hv : HarrisLit.EndB.IsL34Field K v) (hvb : v * b = b * v) {g : X}
    (hc : g⁻¹ * b * g ∈ coreActionKernel K) (hcb : g⁻¹ * b * g * b = b * (g⁻¹ * b * g))
    (hwK : g⁻¹ * v * g ∈ normalizer (K : Set X)) :
    Nat.card (commZStar K (g⁻¹ * v * g)) = 168 * Nat.card (zStarIn K) := by
  set c := g⁻¹ * b * g with hcdef
  set w := g⁻¹ * v * g with hwdef
  have hc2 : orderOf c = 2 := by rw [hcdef, orderOf_conj, hb]
  have hcp : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  set K₀ := twoLayerIn (K ⊓ centralizer ({c} : Set X)) with hK₀
  obtain ⟨-, hsupK, -, -⟩ := cover_twoLayerIn hK hcp hc
  have hle0 : K₀ ≤ K := (map_subtype_le _).trans inf_le_left
  have hleKg : K₀ ≤ conjugate K g := twoLayerIn_le_conjugate h13 hnab hKP hb hK hKmax hKl g hc
  have hKg : IsTwoComponentIn (conjugate K g) (centralizer ({c} : Set X)) := by
    have := isTwoComponentIn_map (MulAut.conj g⁻¹) hK
    rwa [show (centralizer ({b} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      conjugate (centralizer ({b} : Set X)) g from rfl, conjugate_centralizer] at this
  have hbK₀ : b ∈ K₀ := mem_twoLayerIn_of_pow hK hcp hc hbK hcb.symm (k := 1) (by rw [hb, pow_one])
  obtain ⟨eKg⟩ := nonempty_quotient_fusionZStar_map (MulAut.conj g⁻¹) K
  have hsupKg : K₀ ⊔ oddCoreIn (conjugate K g) = conjugate K g :=
    sup_oddCoreIn_eq_of_le hK hcp hc hKg hleKg ⟨b, hbK₀, hb⟩ ⟨eKg.symm⟩
  have hwc : w * c = c * w := by
    calc w * c = g⁻¹ * (v * b) * g := by rw [hwdef, hcdef]; group
      _ = g⁻¹ * (b * v) * g := by rw [hvb]
      _ = c * w := by rw [hwdef, hcdef]; group
  have hwK₀ : w ∈ normalizer (K₀ : Set X) := mem_normalizer_twoLayerIn hwK hwc
  have hwKg : w ∈ normalizer (conjugate K g : Set X) := by
    have h := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hv.1
    rw [map_equiv_normalizer_eq] at h
    have e : (MulAut.conj g⁻¹).toMonoidHom v = w := by
      rw [hwdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [e] at h
    exact h
  obtain ⟨hcntg, hZg⟩ := card_commZStar_conjugate K v g
  have hcntv : Nat.card (commZStar K v) = 168 * Nat.card (zStarIn K) := by
    rw [← card_subtype_eq_card_commZStar]
    exact hv.2.2.2
  have h1 := card_commZStar_mul hleKg hsupKg hwKg hwK₀
  have h2 := card_commZStar_mul hle0 hsupK hwK hwK₀
  rw [hcntg, hZg, hcntv] at h1
  have hpos : 0 < Nat.card (zStarIn K₀) := Nat.card_pos
  have h3 : Nat.card (commZStar K w) * Nat.card (zStarIn K₀) =
      168 * Nat.card (zStarIn K) * Nat.card (zStarIn K₀) := by rw [h2, ← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos h3

end CFSG.ComponentClassification.TBLit.L34FU
