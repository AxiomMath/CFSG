module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenGL

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open

theorem normalizer_le_of_stronglyEmbedded {K : Type} [Group K] [Finite K] (Q : Sylow 2 K)
    (hQ : fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup K) : Set K)))
    {R : Subgroup K} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRQ : R ≤ Q) :
    Subgroup.normalizer (R : Set K) ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
  set B := Subgroup.normalizer ((Q : Subgroup K) : Set K) with hB
  have hQB : (Q : Subgroup K) ≤ B := Subgroup.le_normalizer
  intro g hg
  by_contra hgB
  have hgodd := hQ.2.2 g hgB
  have hUle : R ≤ B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro u hu
    refine ⟨hQB (hRQ hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, ?_, ?_⟩⟩
    · exact hQB (hRQ ((Subgroup.mem_normalizer_iff.mp hg u).mp hu))
    · simp [mul_assoc]
  have hne : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  obtain ⟨n, hn, hcard⟩ := hR2.nontrivial_iff_card.mp hne
  have hdvd : 2 ∣ Nat.card (B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup K) :=
    (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
  exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)

theorem le_sylow_of_isPGroup_normalizer {K : Type} [Group K] [Finite K] (Q : Sylow 2 K)
    {T : Subgroup K} (hT : T ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K))
    (hT2 : IsPGroup 2 T) : T ≤ Q := by
  have hsup : IsPGroup 2 (T ⊔ (Q : Subgroup K) : Subgroup K) :=
    hT2.to_sup_of_normal_right' Q.isPGroup' hT
  have := Q.is_maximal' hsup le_sup_right
  exact le_sup_left.trans this.le

theorem mem_sylow_of_pow_eq_one_normalizer {K : Type} [Group K] [Finite K] (Q : Sylow 2 K)
    {x : K} (hx : x ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K)) {n : ℕ}
    (hn : x ^ (2 ^ n) = 1) : x ∈ (Q : Subgroup K) := by
  have h2 : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  exact le_sylow_of_isPGroup_normalizer Q (Subgroup.zpowers_le.2 hx) h2
    (Subgroup.mem_zpowers x)

theorem not_isLThreeTwo_of_stronglyEmbedded {K : Type} [Group K] [Finite K]
    (hSE : ∀ Q : Sylow 2 K, fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup K) : Set K)))
    (Y : Subgroup K) : ¬ IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  intro hY
  obtain ⟨V, s, g, hV2, hV1, hs, hg, hg3, hg1, hsg, hs', hg', hs2⟩ := exists_s4_data hY
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hmk
  obtain ⟨s', hs'e⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) s
  obtain ⟨g', hg'e⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) g
  have hker : IsPGroup 2 mk.ker := by
    rw [hmk, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  set R : Subgroup K := (V.comap mk).map Y.subtype with hR
  have hR2 : IsPGroup 2 R := (IsPGroup.comap_of_ker_isPGroup hV2 mk hker).map _
  have hR1 : R ≠ ⊥ := by
    intro hbot
    obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV1
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) (v : ↥Y ⧸ CFSG.pCore 2 ↥Y)
    have hyV : y ∈ V.comap mk := by
      show mk y ∈ V
      have : mk y = v := hy
      rw [this]; exact v.2
    have hym : (y : K) ∈ R := ⟨y, hyV, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hym
    have hy1 : y = 1 := Subtype.ext hym
    apply hv1
    apply Subtype.ext
    have : mk y = v := hy
    rw [← this, hy1, map_one]
    rfl
  obtain ⟨Q, hRQ⟩ := hR2.exists_le_sylow
  have hNQ := normalizer_le_of_stronglyEmbedded Q (hSE Q) hR2 hR1 hRQ
  have hnorm : ∀ t : Y, (∀ v ∈ V, mk t * v * (mk t)⁻¹ ∈ V) → (∀ v ∈ V, (mk t)⁻¹ * v * mk t ∈ V) →
      (t : K) ∈ Subgroup.normalizer (R : Set K) := by
    intro t ht ht'
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨t * y * t⁻¹, ?_, by simp⟩
      show mk (t * y * t⁻¹) ∈ V
      rw [map_mul, map_mul, map_inv]
      exact ht _ hy
    · rintro ⟨y, hy, hyr⟩
      have hy' : (y : K) = (t : K) * r * (t : K)⁻¹ := hyr
      have hr : r = ((t⁻¹ * y * t : Y) : K) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hy']
        group
      rw [hr]
      refine ⟨t⁻¹ * y * t, ?_, rfl⟩
      show mk (t⁻¹ * y * t) ∈ V
      rw [map_mul, map_mul, map_inv]
      exact ht' _ hy
  have hcore : ∀ z : Y, z ∈ CFSG.pCore 2 ↥Y → ∃ n : ℕ, (z : K) ^ (2 ^ n) = 1 := by
    intro z hz
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨z, hz⟩
    refine ⟨n, ?_⟩
    have h1 : z ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    rw [← Subgroup.coe_pow, h1]; rfl
  have hmem1 : ∀ z : Y, mk z = 1 → z ∈ CFSG.pCore 2 ↥Y := fun z hz =>
    (QuotientGroup.eq_one_iff z).1 hz
  have hs'N : (s' : K) ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    refine hNQ (hnorm s' ?_ ?_)
    · rw [show mk s' = s from hs'e]; exact hs
    · rw [show mk s' = s from hs'e]; exact hs'
  have hg'N : (g' : K) ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    refine hNQ (hnorm g' ?_ ?_)
    · rw [show mk g' = g from hg'e]; exact hg
    · rw [show mk g' = g from hg'e]; exact hg'
  have hs'Q : (s' : K) ∈ (Q : Subgroup K) := by
    obtain ⟨n, hn⟩ := hcore (s' ^ 2) (hmem1 _ (by
      rw [map_pow, show mk s' = s from hs'e, hs2]))
    refine mem_sylow_of_pow_eq_one_normalizer Q hs'N (n := n + 1) ?_
    rw [pow_succ', pow_mul]
    simpa [Subgroup.coe_pow] using hn
  set o : Y := s' * g' * s'⁻¹ * g' with ho
  have ho1 : o ∈ CFSG.pCore 2 ↥Y := by
    apply hmem1
    rw [ho, map_mul, map_mul, map_mul, map_inv, show mk s' = s from hs'e,
      show mk g' = g from hg'e, hsg, inv_mul_cancel]
  have hoQ : (o : K) ∈ (Q : Subgroup K) := by
    obtain ⟨n, hn⟩ := hcore o ho1
    refine mem_sylow_of_pow_eq_one_normalizer Q ?_ hn
    rw [ho]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem (mul_mem hs'N hg'N) (inv_mem hs'N)) hg'N
  have hcQ : (s' : K) * ((g' : K) * (s' : K)⁻¹ * (g' : K)⁻¹) ∈ (Q : Subgroup K) := by
    refine mul_mem hs'Q ?_
    exact (Subgroup.mem_normalizer_iff.1 hg'N _).1 (inv_mem hs'Q)
  have hg2 : (g' : K) ^ 2 ∈ (Q : Subgroup K) := by
    have : (g' : K) ^ 2 =
        ((s' : K) * ((g' : K) * (s' : K)⁻¹ * (g' : K)⁻¹))⁻¹ * (o : K) := by
      rw [ho, pow_two]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]
    exact mul_mem (inv_mem hcQ) hoQ
  obtain ⟨m, hm⟩ := Q.isPGroup' ⟨(g' : K) ^ 2, hg2⟩
  have hm' : (g' : K) ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ', pow_mul]
    exact congrArg Subtype.val hm
  have hm'' : g' ^ (2 ^ (m + 1)) = 1 := Subtype.ext (by simpa [Subgroup.coe_pow] using hm')
  have hgm : g ^ (2 ^ (m + 1)) = 1 := by
    rw [← show mk g' = g from hg'e, ← map_pow, hm'', map_one]
  have h3 : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have h3d : 3 ∣ 2 ^ (m + 1) := h3 ▸ orderOf_dvd_of_pow_eq_one hgm
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
