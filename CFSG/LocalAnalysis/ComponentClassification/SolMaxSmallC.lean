module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 7)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)}

theorem image_of_seven [Finite X] {T : Subgroup X}
    (hTN : T ≤ normalizer (M : Set X)) (hTperf : ⁅T, T⁆ = T)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤)
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 7))
    (hne : ∃ l : ↥T, ρ (inclusion hTN l) ≠ 1) :
    (∀ g ∈ alternatingGroup (Fin 7), ∃ l : ↥T, ρ (inclusion hTN l) = g) ∧
      (∀ l : ↥T, ρ (inclusion hTN l) ∈ alternatingGroup (Fin 7)) ∧
      ∀ l : ↥T, l ∈ pPrimeCore 2 ↥T → ρ (inclusion hTN l) = 1 := by
  classical
  have hA : ∀ l : ↥T, ρ (inclusion hTN l) ∈ alternatingGroup (Fin 7) := by
    intro l
    have hperf : Group.IsPerfect ↥T := (Subgroup.isPerfect_iff).mpr hTperf
    have h1 := Abelianization.commutator_subset_ker (Perm.sign.comp (ρ.comp (inclusion hTN)))
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (mem_top l)
  let φ : ↥T →* alternatingGroup (Fin 7) :=
    (ρ.comp (inclusion hTN)).codRestrict (alternatingGroup (Fin 7)) hA
  obtain ⟨l₀, hl₀⟩ := hne
  have hφ : φ l₀ ≠ 1 := fun h => hl₀ (congrArg Subtype.val h)
  have hQ : ∀ l, φ l ∈ fixAlt (1 : Perm (Fin 7)) := by
    intro l
    rw [mem_fixAlt]
    simp
  have hQc : Nat.card (fixAlt (1 : Perm (Fin 7))) ≤ Nat.factorial 7 / 2 := by
    rw [card_fixAlt (by simp)]
    simp
  obtain ⟨ψL, hψL⟩ := exists_coreQuot_equiv_of_hom hres (by norm_num) χ φ ⟨l₀, hφ⟩ hQ hQc
  refine ⟨fun g hg => ?_, hA, fun l hl => ?_⟩
  · have hgQ : (⟨g, hg⟩ : alternatingGroup (Fin 7)) ∈ fixAlt (1 : Perm (Fin 7)) := by
      rw [mem_fixAlt]
      simp
    obtain ⟨q, hq⟩ := ψL.surjective ⟨⟨g, hg⟩, hgQ⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨l, ?_⟩
    have h1 := hψL l
    rw [hq] at h1
    exact (congrArg Subtype.val h1).symm
  · have h1 := hψL l
    rw [(QuotientGroup.eq_one_iff l).mpr hl, map_one] at h1
    exact (congrArg Subtype.val h1).symm

theorem eq_one_of_mem_cak_of_image {T : Subgroup X}
    (hTN : T ≤ normalizer (M : Set X))
    (hsurj : ∀ g ∈ alternatingGroup (Fin 7), ∃ l : ↥T, ρ (inclusion hTN l) = g)
    (hO : ∀ l : ↥T, l ∈ pPrimeCore 2 ↥T → ρ (inclusion hTN l) = 1) {y : X}
    (hyN : y ∈ normalizer (M : Set X)) (hyT : y ∈ UnbalancedLayer.coreActionKernel T) :
    ρ ⟨y, hyN⟩ = 1 := by
  refine eq_one_of_commute_fixAlt (τ := 1) (fun x hx => by simp at hx) (by simp)
    fun b _ => ?_
  obtain ⟨l, hl⟩ := hsurj b b.2
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hyT)).2 l l.2
  rw [inv_inv] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have hyl : y * (l : X) * y⁻¹ = (l : X) * (o : X) := by
    change (o : X) = (l : X)⁻¹ * y * l * y⁻¹ at hoeq
    rw [hoeq]
    group
  have h2 : (⟨y, hyN⟩ : ↥(normalizer (M : Set X))) * inclusion hTN l * ⟨y, hyN⟩⁻¹ =
      inclusion hTN l * inclusion hTN o := Subtype.ext hyl
  have h3 : ρ (inclusion hTN o) = 1 := hO o ho
  calc ρ ⟨y, hyN⟩ * (b : Perm (Fin 7)) = ρ ⟨y, hyN⟩ * ρ (inclusion hTN l) := by rw [hl]
    _ = ρ (⟨y, hyN⟩ * inclusion hTN l * ⟨y, hyN⟩⁻¹) * ρ ⟨y, hyN⟩ := by
        rw [map_mul, map_mul, map_inv]
        group
    _ = ρ (inclusion hTN l) * ρ ⟨y, hyN⟩ := by rw [h2, map_mul, h3, mul_one]
    _ = (b : Perm (Fin 7)) * ρ ⟨y, hyN⟩ := by rw [hl]

theorem coreNOf_le_coreActionKernel [Finite X] (M : Subgroup X) :
    coreNOf M ≤ UnbalancedLayer.coreActionKernel M := by
  intro o ho
  have hoM : o ∈ M := map_subtype_le _ ho
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨le_normalizer hoM, fun j hj => ?_⟩
  have h1 : j⁻¹ * o⁻¹ * j ∈ coreNOf M := by
    have := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer (inv_mem hj)))
      o⁻¹).mp (inv_mem ho)
    simpa using this
  exact mul_mem h1 ho

theorem nontrivial_coreQuot_of_seven {T : Subgroup X}
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 7)) :
    Nontrivial (↥T ⧸ pPrimeCore 2 ↥T) := by
  have : Nontrivial (Fin 7) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
  have : Nontrivial (alternatingGroup (Fin 7)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
  exact χ.toEquiv.nontrivial

theorem mem_coreActionKernel_of_le_centralizer {T : Subgroup X} {t : X}
    (hTC : T ≤ centralizer ({t} : Set X)) : t ∈ UnbalancedLayer.coreActionKernel T := by
  have htC : t ∈ centralizer (T : Set X) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hTC hl)
  refine UnbalancedLayer.mem_coreActionKernel.mpr
    ⟨Subgroup.centralizer_le_normalizer _ htC, fun l hl => ?_⟩
  have hlt : l * t = t * l := mem_centralizer_singleton_iff.mp (hTC hl)
  have h1 : l⁻¹ * t⁻¹ * l * t = 1 := by
    calc l⁻¹ * t⁻¹ * l * t = l⁻¹ * (t⁻¹ * (l * t)) := by group
      _ = l⁻¹ * (t⁻¹ * (t * l)) := by rw [hlt]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

theorem le_coreActionKernel_of_trivial_pump [Finite X] {M T X₀ : Subgroup X} {t : X}
    (htt : t * t = 1) (htN : t ∈ normalizer (M : Set X)) (hTM : T ≤ M)
    (hTC : T ≤ centralizer ({t} : Set X)) (hTperf : ⁅T, T⁆ = T)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤)
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 7)) (hM : ⁅M, M⁆ = M)
    (ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 7)) (hodd : Odd (Nat.card X₀))
    (hX₀N : X₀ ≤ normalizer (M : Set X)) (htX : ∀ x ∈ X₀, t * x * t⁻¹ ∈ X₀)
    (hY : ∀ y ∈ X₀, t * y = y * t → y ∈ UnbalancedLayer.coreActionKernel T) :
    X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_isPermActionZ (N := M) (by norm_num) (by norm_num) ψ
  have hTN : T ≤ normalizer (M : Set X) := hTM.trans le_normalizer
  have hne : ∃ l : ↥T, ρ (inclusion hTN l) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_coreActionKernel_of_le hTM hTperf (nontrivial_coreQuot_of_seven χ)
    intro l hl
    exact hρ.mem_coreActionKernel hM (hTN hl) (hall ⟨l, hl⟩)
  obtain ⟨hsurj, -, hO⟩ := image_of_seven hTN hTperf hres χ hne
  have hρt : ρ ⟨t, htN⟩ = 1 :=
    eq_one_of_mem_cak_of_image hTN hsurj hO htN (mem_coreActionKernel_of_le_centralizer hTC)
  set K : Subgroup X := ρ.ker.map (normalizer (M : Set X)).subtype with hKdef
  have hmemK : ∀ (g : X) (hg : g ∈ normalizer (M : Set X)), ρ ⟨g, hg⟩ = 1 → g ∈ K :=
    fun g hg h => ⟨⟨g, hg⟩, h, rfl⟩
  have hKmem : ∀ g ∈ K, ∃ hg : g ∈ normalizer (M : Set X), ρ ⟨g, hg⟩ = 1 := by
    rintro _ ⟨⟨g, hg⟩, h, rfl⟩
    exact ⟨hg, h⟩
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro k hk
    obtain ⟨hkN, hk1⟩ := hKmem k hk
    have hc : t * k * t⁻¹ ∈ normalizer (M : Set X) := mul_mem (mul_mem htN hkN) (inv_mem htN)
    refine hmemK _ hc ?_
    have h1 : (⟨t * k * t⁻¹, hc⟩ : ↥(normalizer (M : Set X))) =
        ⟨t, htN⟩ * ⟨k, hkN⟩ * (⟨t, htN⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hρt, hk1]
    group
  intro x hx
  have hxK : x ∈ K := by
    refine mem_of_conj_mem hodd htt htX htK (fun y hy hyt => ?_) hx ?_
    · exact hmemK y (hX₀N hy)
        (eq_one_of_mem_cak_of_image hTN hsurj hO (hX₀N hy) (hY y hy hyt))
    · have hxN := hX₀N hx
      have hc : x⁻¹ * (t * x * t⁻¹) ∈ normalizer (M : Set X) :=
        mul_mem (inv_mem hxN) (mul_mem (mul_mem htN hxN) (inv_mem htN))
      refine hmemK _ hc ?_
      have h1 : (⟨x⁻¹ * (t * x * t⁻¹), hc⟩ : ↥(normalizer (M : Set X))) =
          (⟨x, hxN⟩ : ↥(normalizer (M : Set X)))⁻¹ *
            (⟨t, htN⟩ * ⟨x, hxN⟩ * (⟨t, htN⟩ : ↥(normalizer (M : Set X)))⁻¹) := rfl
      rw [h1, map_mul, map_inv, map_mul, map_mul, map_inv, hρt]
      group
  obtain ⟨hxN, hx1⟩ := hKmem x hxK
  exact hρ.mem_coreActionKernel hM hxN hx1

end CFSG.ComponentClassification.SolMax
