module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB2

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma43TwistedStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J = ⊥ →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        ¬ oddIn K ≤ J →
        ∀ T : Subgroup G, IsSylowTwoIn T (normalizer (W : Set G)) → S ≤ T →
          (∃ P : Sylow 2 G, (P : Subgroup G) = T) →
          ∀ t ∈ T, t ∉ normalizer (K : Set G) →
          (∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t) →
          (∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1) →
          (∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G)) →
          (∃ u ∈ T, u ∉ normalizer (K : Set G) ∧ u ^ 4 = 1) →
          (∀ u ∈ T, u ∉ normalizer (K : Set G) → u ^ 4 = 1 →
            ¬ ∃ F ≤ T ⊓ centralizer ({u} : Set G), IsEightGroup F ∧
              ∃ w ∈ T ⊓ centralizer ({u} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧
                w ∉ F) →
          False

end CFSG.ComponentClassification.GrSLit

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem false_of_witness_order_four [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {W K T : Subgroup G} (hTsyl : IsSylowTwoIn T (normalizer (W : Set G)))
    (hTG : ∃ P : Sylow 2 G, (P : Subgroup G) = T)
    (hWT : ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
      (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W)
    {t : G} (htT : t ∈ T) (htK : t ∉ normalizer (K : Set G))
    (httK : t * t ∈ normalizer (K : Set G))
    (hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t)
    (hinv : ∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G))
    {u : G} (huT : u ∈ T) (huK : u ∉ normalizer (K : Set G)) (hu4 : u ^ 4 = 1)
    {F : Subgroup G} (hFT : F ≤ T ⊓ centralizer ({u} : Set G)) (hF : IsEightGroup F) {w : G}
    (hwT : w ∈ T ⊓ centralizer ({u} : Set G)) (hww : w * w = 1)
    (hwF : ∀ e ∈ F, w * e = e * w) (hwn : w ∉ F) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hTG
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  have hidx := HeSN.relIndex_eq_two (hTM htT) htK httK hr2
  have hu4' : u * u * (u * u) = 1 := by
    have h1 := hu4
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at h1
    exact h1
  have hu2 : u * u ≠ 1 := fun h1 => huK (hinv u (hTM huT) (orderOf_eq_prime (by
    rw [pow_two]; exact h1) fun h2 => huK (h2 ▸ one_mem _)))
  have huu2 : orderOf (u * u) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu4') hu2
  have hidx' : ((normalizer (W : Set G) ⊓ normalizer (K : Set G)).subgroupOf
      (normalizer (W : Set G))).index = 2 := hidx
  have hiff : ∀ x ∈ normalizer (W : Set G), ∀ y ∈ normalizer (W : Set G),
      (x * y ∈ normalizer (K : Set G) ↔
        (x ∈ normalizer (K : Set G) ↔ y ∈ normalizer (K : Set G))) := by
    intro x hx y hy
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf] at h1
    simpa [hx, hy, mul_mem hx hy] using h1
  have hconj : ∀ m ∈ normalizer (W : Set G), ∀ x ∈ normalizer (W : Set G),
      x ∈ normalizer (K : Set G) → m * x * m⁻¹ ∈ normalizer (K : Set G) := by
    intro m hm x hxM hx
    rw [hiff _ (mul_mem hm hxM) _ (inv_mem hm), hiff _ hm _ hxM]
    have h1 := hiff m hm m⁻¹ (inv_mem hm)
    rw [mul_inv_cancel] at h1
    have h2 := h1.mp (one_mem _)
    exact ⟨fun h3 => h2.mp (h3.mpr hx), fun h3 => ⟨fun _ => hx, fun _ => h2.mpr h3⟩⟩
  have hout : ∀ g ∈ T, g ∉ normalizer (K : Set G) → u⁻¹ * g ∈ normalizer (K : Set G) :=
    fun g hg hgK => (hiff _ (inv_mem (hTM huT)) _ (hTM hg)).mpr
      ⟨fun h1 => absurd (by simpa using inv_mem h1) huK, fun h1 => absurd h1 hgK⟩
  have hTidx : ¬ 2 ∣ T.index := by
    rw [← hP₀]
    exact P₀.not_dvd_index
  have hQn : ∀ g ∈ T, ∀ q ∈ T ⊓ normalizer (K : Set G),
      g * q * g⁻¹ ∈ T ⊓ normalizer (K : Set G) := fun g hg q hq =>
    mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hq).1) (inv_mem hg),
      hconj g (hTM hg) q (hTM (mem_inf.mp hq).1) (mem_inf.mp hq).2⟩
  have hcyc : ∃ b ∈ T, ∀ g ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * g ∈ T ⊓ normalizer (K : Set G) := by
    refine ⟨u, huT, fun g hg => ?_⟩
    by_cases hgK : g ∈ normalizer (K : Set G)
    · exact ⟨0, by simpa using mem_inf.mpr ⟨hg, hgK⟩⟩
    · exact ⟨1, by simpa using mem_inf.mpr ⟨mul_mem (inv_mem huT) hg, hout g hg hgK⟩⟩
  have hb' : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T →
      g⁻¹ * u ^ (2 * k) * g ∈ T ⊓ normalizer (K : Set G) := by
    intro g k hg
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have h1 : u ^ (2 * (j + j)) = 1 := by
        rw [show 2 * (j + j) = 4 * j by ring, pow_mul, hu4, one_pow]
      rw [h1, mul_one, inv_mul_cancel]
      exact one_mem _
    · have h1 : u ^ (2 * (2 * j + 1)) = u * u := by
        rw [show 2 * (2 * j + 1) = 4 * j + 2 by ring, pow_add, pow_mul, hu4, one_pow, one_mul,
          pow_two]
      rw [h1] at hg ⊢
      refine mem_inf.mpr ⟨hg, hinv _ (hTM hg) ?_⟩
      rw [← huu2]
      exact SemiconjBy.orderOf_eq g (show g * (g⁻¹ * (u * u) * g) = u * u * g by group)
  have hc' : ∀ g : G, g⁻¹ * u * g ∈ T →
      GH74.GLS.Bg.Thompson.IsExtremalIn 2 T (g⁻¹ * u * g) →
        g⁻¹ * u * g ∈ T ⊓ normalizer (K : Set G) ∨
          u⁻¹ * (g⁻¹ * u * g) ∈ T ⊓ normalizer (K : Set G) := by
    intro g hg _
    by_cases h' : g⁻¹ * u * g ∈ normalizer (K : Set G)
    · exact Or.inl (mem_inf.mpr ⟨hg, h'⟩)
    · exact Or.inr (mem_inf.mpr ⟨mul_mem (inv_mem huT) hg, hout _ hg h'⟩)
  rcases GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hT2 hTidx hQn hcyc huT
      (fun h' => huK (mem_inf.mp h').2) hb' hc' with ⟨N, hNn, -, hNp, huN⟩ | ⟨g, hgQ, hgext, -⟩
  ·
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
    · subst hN
      have hG2 : IsPGroup 2 G := hNp.of_equiv QuotientGroup.quotientBot
      have : Group.IsNilpotent G := hG2.isNilpotent
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)
    · exact huN (hN ▸ mem_top u)
  ·
    have hext := isExtremalIn_of_thompson (mem_inf.mp hgQ).1 hgext
    obtain ⟨m, hmM, hm⟩ := exists_conj_of_witness hT2 hWT hext hFT hF hwT hww hwF hwn
    apply huK
    have h1 := hconj m (hmM) _ (hTM (mem_inf.mp hgQ).1) (mem_inf.mp hgQ).2
    rwa [hm, show m * (m⁻¹ * u * m) * m⁻¹ = u by group] at h1

end CFSG.ComponentClassification.GrSLit.KSw
