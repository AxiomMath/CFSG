module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwGen
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRLev
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwSmall
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTrans


public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

private theorem inf_oddIn_eq_bot_uu {M T : Subgroup G} (hT : IsSylowTwoIn T M) :
    T ⊓ oddIn M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_of_le_two_group_of_le_odd (P := T) (O := oddIn M)
    (GrS4.isPGroup_of_isSylowTwoIn hT) ?_ inf_le_left inf_le_right
  rw [oddIn, card_map_of_injective (subtype_injective _)]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem odd_card_ker_uu {M : Subgroup G} {ρ : ↥M →* WrE}
    (hker : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ oddIn M) : Odd (Nat.card ρ.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ρ.ker = pPrimeCore 2 ↥M := by
    ext m
    rw [MonoidHom.mem_ker, hker m, oddIn]
    exact Subgroup.mem_map_iff_mem M.subtype_injective
  rw [hk]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem mem_imgT_iff_uu {M T : Subgroup G} {ρ : ↥M →* WrE} {z : WrE} :
    z ∈ imgT T M ρ ↔ ∃ m : ↥M, (m : G) ∈ T ∧ ρ m = z := by
  unfold imgT
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨m, hm, e⟩ => ⟨m, mem_subgroupOf.mp hm, e⟩,
    fun ⟨m, hm, e⟩ => ⟨m, mem_subgroupOf.mpr hm, e⟩⟩

private theorem pow_eq_one_of_rho_uu {M T : Subgroup G} (hT : IsSylowTwoIn T M) {ρ : ↥M →* WrE}
    (hker : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ oddIn M) {m : ↥M} (hm : (m : G) ∈ T) {n : ℕ}
    (hn : ρ m ^ n = 1) : m ^ n = 1 := by
  have h1 : ρ (m ^ n) = 1 := by rw [map_pow, hn]
  have h2 : ((m ^ n : ↥M) : G) ∈ oddIn M := (hker _).mp h1
  have h3 : ((m ^ n : ↥M) : G) ∈ T := by
    rw [Subgroup.coe_pow]
    exact pow_mem hm n
  have h4 : ((m ^ n : ↥M) : G) ∈ T ⊓ oddIn M := mem_inf.mpr ⟨h3, h2⟩
  rw [inf_oddIn_eq_bot_uu hT, mem_bot] at h4
  exact Subtype.ext h4

private theorem orderOf_rho_uu {M T : Subgroup G} (hT : IsSylowTwoIn T M) {ρ : ↥M →* WrE}
    (hker : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ oddIn M) {m : ↥M} (hm : (m : G) ∈ T) :
    orderOf (ρ m) = orderOf (m : G) := by
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_orderOf_iff.mpr fun n =>
    ⟨fun hn => pow_eq_one_of_rho_uu hT hker hm hn, fun hn => by rw [← map_pow, hn, map_one]⟩

private theorem conjugate_le_uu {M K : Subgroup G} {t : G} (hK : K ≤ M) (ht : t ∈ M) :
    conjugate K t ≤ M := by
  rintro _ ⟨k, hk, rfl⟩
  have h1 : t⁻¹ * k * t ∈ M := M.mul_mem (M.mul_mem (M.inv_mem ht) (hK hk)) ht
  simpa using h1

private theorem mem_ssS_uu {x : WrE} : x ∈ ssS ↔ x.e = false ∧ x.a ∈ S ∧ x.b ∈ S := Iff.rfl

private theorem conj_noswap_uu (c₁ c₂ p q : Equiv.Perm (Fin 42)) :
    (⟨c₁, c₂, false⟩ : WrE) * ⟨p, q, false⟩ * (⟨c₁, c₂, false⟩ : WrE)⁻¹ =
      ⟨c₁ * p * c₁⁻¹, c₂ * q * c₂⁻¹, false⟩ := by
  simp [WrE.mul_def, WrE.inv_def, mul_assoc]

private theorem sq_noswap_uu {x : WrE} (he : x.e = false) (h : x * x = 1) :
    x.a * x.a = 1 ∧ x.b * x.b = 1 := by
  rcases x with ⟨xa, xb, xe⟩
  cases he
  simpa [WrE.mul_def, WrE.one_def] using h

private theorem isA_cases_uu {x : WrE} (hx : IsA x) :
    (∃ s : Equiv.Perm (Fin 42), x = ⟨1, s, false⟩ ∧ s ∈ S ∧ s ≠ 1 ∧ s * s = 1) ∨
    (∃ s : Equiv.Perm (Fin 42), x = ⟨s, 1, false⟩ ∧ s ∈ S ∧ s ≠ 1 ∧ s * s = 1) := by
  obtain ⟨he, hsq, hcase⟩ := hx
  have h2 := sq_noswap_uu he hsq
  rcases hcase with ⟨ha1, hb1, hbS⟩ | ⟨hb1, ha1, haS⟩
  · exact Or.inl ⟨x.b, WrE.ext ha1 rfl he, hbS, hb1, h2.2⟩
  · exact Or.inr ⟨x.a, WrE.ext rfl hb1 he, haS, ha1, h2.1⟩

private theorem r₄_ne_one_uu : r₄ ≠ 1 := by
  intro h
  have h0 := congrArg (fun p : Equiv.Perm (Fin 42) => (p 0).val) h
  have h1 : (r₄ 0).val = (g5Fun (g6Fun 0)).val := rfl
  have h2 : g6Fun 0 = ⟨21, by omega⟩ := by simp [g6Fun]
  have h3 : (g5Fun ⟨21, by omega⟩).val =
      21 * (21 / 21) + vIdx (fun k => vecOf (⟨21, by omega⟩ : Fin 42) k ^ 2) := rfl
  simp only [Equiv.Perm.coe_one, id_eq] at h0
  rw [h1, h2, h3] at h0
  omega

private theorem isUni_ne_one_uu {r : Equiv.Perm (Fin 42)} (h : isUni r) : r ≠ 1 := by
  obtain ⟨c, -, rfl⟩ := h
  intro h1
  apply r₄_ne_one_uu
  have := congrArg (fun p => c⁻¹ * p * c) h1
  simpa [mul_assoc] using this

private theorem exists_uu_lift_uu {M : Type} [Group M] [Finite M] (ρ : M →* WrE)
    (hker : Odd (Nat.card ρ.ker)) {aM u : M} (haa : aM * aM = 1) (hU : IsUU (ρ u))
    (hc : ρ u * ρ aM = ρ aM * ρ u) :
    ∃ y : M, y * y = 1 ∧ IsUU (ρ y) ∧ y * aM = aM * y := by
  have hne : ρ u ≠ 1 := fun h1 => isUni_ne_one_uu hU.2.2.1 (congrArg WrE.a h1)
  obtain ⟨y, hy2, hρy, hyc⟩ := exists_invol_lift_commuting ρ hker haa hU.2.1 hc hne
  exact ⟨y, hy2, by rw [hρy]; exact hU, hyc⟩

variable {a x : G} {J S' W K T : Subgroup G} {t : G}
  {ρ : ↥(normalizer (W : Set G)) →* WrE}

private theorem exists_swapper_data_uu (h : TwHyp G a x J S' W K T t)
    (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) :
    ∃ v : ↥(normalizer (W : Set G)), (v : G) ∈ T ∧ (v : G) ∉ normalizer (K : Set G) ∧
      (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf (v : G) ≤ orderOf y) ∧
      v * v * (v * v) = 1 ∧ IsUU (ρ (v * v)) := by
  classical
  obtain ⟨u, huT, huN, -⟩ := h.hu
  have hex : ∃ n, ∃ v ∈ T, v ∉ normalizer (K : Set G) ∧ orderOf v = n :=
    ⟨_, u, huT, huN, rfl⟩
  obtain ⟨v, hvT, hvN, hv⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y := by
    intro y hyT hyN
    rw [hv]
    exact Nat.find_min' hex ⟨y, hyT, hyN, rfl⟩
  have hTsyl := h.hTsyl
  have hker := hρ.ker_iff
  obtain ⟨v', rfl⟩ : ∃ v' : ↥(normalizer (W : Set G)), (v' : G) = v := ⟨⟨v, hTsyl.1 hvT⟩, rfl⟩
  have hvX : ρ v' ∈ imgT T (normalizer (W : Set G)) ρ := mem_imgT_iff_uu.mpr ⟨v', hvT, rfl⟩
  have hve : (ρ v').e = true := (hρ.swap_iff v').mpr hvN
  have hminX : ∀ z ∈ imgT T (normalizer (W : Set G)) ρ, z.e = true →
      orderOf (ρ v') ≤ orderOf z := by
    intro z hz hze
    obtain ⟨m, hmT, rfl⟩ := mem_imgT_iff_uu.mp hz
    rw [orderOf_rho_uu hTsyl hker hvT, orderOf_rho_uu hTsyl hker hmT]
    exact hmin _ hmT ((hρ.swap_iff m).mp hze)
  obtain ⟨h4, hUU⟩ := hC.swap_min _ hvX hve hminX
  have h4' : v' ^ 4 = 1 := pow_eq_one_of_rho_uu hTsyl hker hvT h4
  refine ⟨v', hvT, hvN, hmin, ?_, ?_⟩
  · calc v' * v' * (v' * v') = v' ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4'
  · rw [map_mul]
    exact hUU

theorem exists_uu_commuting (h : TwHyp G a x J S' W K T t)
    (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) :
    ∃ y : ↥(normalizer (W : Set G)), y * y = 1 ∧ IsUU (ρ y) ∧ (y : G) * a = a * (y : G) := by
  obtain ⟨haM, hA⟩ := isA_a h hρ
  obtain ⟨v, -, -, -, hv4, hvU⟩ := exists_swapper_data_uu h hρ hC
  have haord : orderOf a = 2 := h.hset.2.1.1
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
    rwa [pow_two] at h2
  have haa : (⟨a, haM⟩ : ↥(normalizer (W : Set G))) * ⟨a, haM⟩ = 1 := Subtype.ext ha2
  have hker := odd_card_ker_uu hρ.ker_iff
  obtain ⟨σ₁, σ₂, hρy₀⟩ : ∃ σ₁ σ₂ : Equiv.Perm (Fin 42), ρ (v * v) = ⟨σ₁, σ₂, false⟩ :=
    ⟨_, _, WrE.ext rfl rfl hvU.1⟩
  have hσ₁ : isUni σ₁ := by
    have := hvU.2.2.1
    rwa [hρy₀] at this
  have hσ₂ : isUni σ₂ := by
    have := hvU.2.2.2
    rwa [hρy₀] at this
  suffices H : ∃ y : ↥(normalizer (W : Set G)), y * y = 1 ∧ IsUU (ρ y) ∧
      y * ⟨a, haM⟩ = ⟨a, haM⟩ * y by
    obtain ⟨y, hy2, hyU, hyc⟩ := H
    exact ⟨y, hy2, hyU, congrArg Subtype.val hyc⟩
  have hsq : ∀ m : ↥(normalizer (W : Set G)),
      m * (v * v) * m⁻¹ * (m * (v * v) * m⁻¹) = 1 := fun m => by
    calc m * (v * v) * m⁻¹ * (m * (v * v) * m⁻¹) = m * (v * v * (v * v)) * m⁻¹ := by group
      _ = 1 := by rw [hv4]; group
  rcases isA_cases_uu hA with ⟨s, hρa, hsS, hs1, hss⟩ | ⟨s, hρa, hsS, hs1, hss⟩
  ·
    obtain ⟨σ, hσ, hσs⟩ := exists_uni_commuting_inner hsS hss hs1
    obtain ⟨c, hcS, hcσ⟩ := uni_conj hσ₂ hσ
    obtain ⟨m, -, hm⟩ := hρ.Kt_surj c hcS
    have hρu : ρ (m * (v * v) * m⁻¹) = ⟨σ₁, σ, false⟩ := by
      rw [map_mul, map_mul, map_inv, hm, hρy₀, conj_noswap_uu]
      simp [hcσ]
    refine exists_uu_lift_uu ρ hker haa (u := m * (v * v) * m⁻¹) ?_ ?_
    · refine ⟨by rw [hρu], ?_, by rw [hρu]; exact hσ₁, by rw [hρu]; exact hσ⟩
      rw [← map_mul, hsq m, map_one]
    · rw [hρu, hρa]
      simp [WrE.mul_def, hσs]
  ·
    obtain ⟨σ, hσ, hσs⟩ := exists_uni_commuting_inner hsS hss hs1
    obtain ⟨c, hcS, hcσ⟩ := uni_conj hσ₁ hσ
    obtain ⟨m, -, hm⟩ := hρ.K_surj c hcS
    have hρu : ρ (m * (v * v) * m⁻¹) = ⟨σ, σ₂, false⟩ := by
      rw [map_mul, map_mul, map_inv, hm, hρy₀, conj_noswap_uu]
      simp [hcσ]
    refine exists_uu_lift_uu ρ hker haa (u := m * (v * v) * m⁻¹) ?_ ?_
    · refine ⟨by rw [hρu], ?_, by rw [hρu]; exact hσ, by rw [hρu]; exact hσ₂⟩
      rw [← map_mul, hsq m, map_one]
    · rw [hρu, hρa]
      simp [WrE.mul_def, hσs]

theorem uu_fusion (h : TwHyp G a x J S' W K T t)
    (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) {y : ↥(normalizer (W : Set G))}
    (hy2 : y * y = 1) (hyU : IsUU (ρ y)) :
    ∃ (g : G) (m : ↥(normalizer (W : Set G))), m * m = 1 ∧ (IsA (ρ m) ∨ IsD (ρ m)) ∧
      g⁻¹ * (y : G) * g = (m : G) := by
  obtain ⟨v, hvT, hvN, hmin, hv4, hvU⟩ := exists_swapper_data_uu h hρ hC
  have hTsyl := h.hTsyl
  have hTM : T ≤ normalizer (W : Set G) := hTsyl.1
  obtain ⟨k, hk⟩ := invol_conj_of_type h hρ hy2 hv4 (Or.inr (Or.inr ⟨hyU, hvU⟩))
  have hk' : (k : G)⁻¹ * (y : G) * k = (v : G) * (v : G) := congrArg Subtype.val hk
  obtain ⟨g, hg⟩ := h.hE6 (v : G) hvT hvN hmin
  have hww := h.hE4 _ hg
  have hwwT : (g⁻¹ * (v : G) * g) * (g⁻¹ * (v : G) * g) ∈ T :=
    T.mul_mem (mem_inf.mp hg).1 (mem_inf.mp hg).1
  have hQ : K ⊔ conjugate K t ≤ (ssS.comap ρ).map (normalizer (W : Set G)).subtype := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · have hzM : z ∈ normalizer (W : Set G) := h.hKM hz
      refine ⟨⟨z, hzM⟩, Subgroup.mem_comap.mpr (mem_ssS_uu.mpr ?_), rfl⟩
      obtain ⟨he, hb, ha⟩ := hρ.K_img ⟨z, hzM⟩ hz
      exact ⟨he, ha, by rw [hb]; exact S.one_mem⟩
    · have hzM : z ∈ normalizer (W : Set G) := conjugate_le_uu h.hKM (hTM h.htT) hz
      refine ⟨⟨z, hzM⟩, Subgroup.mem_comap.mpr (mem_ssS_uu.mpr ?_), rfl⟩
      obtain ⟨he, ha, hb⟩ := hρ.Kt_img ⟨z, hzM⟩ hz
      exact ⟨he, by rw [ha]; exact S.one_mem, hb⟩
  obtain ⟨m, hmss, hm⟩ := hQ hww
  have hm' : (m : G) = (g⁻¹ * (v : G) * g) * (g⁻¹ * (v : G) * g) := hm
  have hmeq : (m : G) = g⁻¹ * ((v : G) * (v : G)) * g := by rw [hm']; group
  have hmT : (m : G) ∈ T := by rw [hm']; exact hwwT
  have hm2 : m * m = 1 := by
    apply Subtype.ext
    show (m : G) * (m : G) = 1
    have h4 : (v : G) * v * ((v : G) * v) = 1 := congrArg Subtype.val hv4
    rw [hmeq]
    calc g⁻¹ * ((v : G) * (v : G)) * g * (g⁻¹ * ((v : G) * (v : G)) * g)
        = g⁻¹ * ((v : G) * v * ((v : G) * v)) * g := by group
      _ = 1 := by rw [h4]; group
  have hy₀1 : (v * v : ↥(normalizer (W : Set G))) ≠ 1 := by
    intro h1
    apply isUni_ne_one_uu hvU.2.2.1
    have : ρ (v * v) = 1 := by rw [h1, map_one]
    exact congrArg WrE.a this
  have hρm1 : ρ m ≠ 1 := by
    intro h1
    have h2 : (m : G) ∈ oddIn (normalizer (W : Set G)) := (hρ.ker_iff m).mp h1
    have h3 : (m : G) ∈ T ⊓ oddIn (normalizer (W : Set G)) := mem_inf.mpr ⟨hmT, h2⟩
    rw [inf_oddIn_eq_bot_uu hTsyl, mem_bot] at h3
    apply hy₀1
    have h4 : g⁻¹ * ((v : G) * (v : G)) * g = 1 := by rw [← hmeq]; exact h3
    apply Subtype.ext
    show (v : G) * (v : G) = 1
    have := congrArg (fun z => g * z * g⁻¹) h4
    simpa [mul_assoc] using this
  have hρm2 : ρ m * ρ m = 1 := by rw [← map_mul, hm2, map_one]
  obtain ⟨he, ha, hb⟩ := mem_ssS_uu.mp (Subgroup.mem_comap.mp hmss)
  refine ⟨(k : G) * g, m, hm2, ?_, ?_⟩
  · by_cases ha1 : (ρ m).a = 1
    · exact Or.inl ⟨he, hρm2, Or.inl ⟨ha1, fun hb1 => hρm1 (WrE.ext ha1 hb1 he), hb⟩⟩
    · by_cases hb1 : (ρ m).b = 1
      · exact Or.inl ⟨he, hρm2, Or.inr ⟨hb1, ha1, ha⟩⟩
      · exact Or.inr ⟨he, hρm2, ha1, hb1, ha, hb⟩
  · calc ((k : G) * g)⁻¹ * (y : G) * ((k : G) * g)
        = g⁻¹ * ((k : G)⁻¹ * (y : G) * k) * g := by group
      _ = g⁻¹ * ((v : G) * (v : G)) * g := by rw [hk']
      _ = (m : G) := hmeq.symm

end CFSG.ComponentClassification.GrSLit.L34Tw
