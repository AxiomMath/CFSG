module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointPSL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.AGLEmbedding
open scoped MatrixGroups

theorem spw_normalizerPowers_of_transitive {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hpl : SylowIsPlane p K) (htr : NormalizerTransitive p K) : NormalizerPowers p K := by
  intro S t ht ht1 k hk
  have htp : t ^ p = 1 := (hpl S).1.2 t ht
  have hto : orderOf t = p := orderOf_eq_prime htp ht1
  have htk1 : t ^ k ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hto] at this
    exact hk this
  exact htr S t ht ht1 (t ^ k) ((S : Subgroup K).pow_mem ht k) htk1

theorem spw_normalizerPowers_of_equiv {p : ℕ} [Fact p.Prime] {Q K : Type} [Group Q] [Finite Q]
    [Group K] [Finite K] (e : Q ≃* K) (h : NormalizerPowers p K) : NormalizerPowers p Q := by
  intro S t ht ht1 k hk
  have hS := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  obtain ⟨n', hn', hnt⟩ := h (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S) (e t)
    (by rw [hS]; exact ⟨t, ht, rfl⟩) (by simpa using ht1) k hk
  refine ⟨e.symm n', ?_, ?_⟩
  · rw [← psl2_mem_normalizer_map e, MulEquiv.apply_symm_apply]
    rwa [hS] at hn'
  · apply e.injective
    simpa [map_pow] using hnt

theorem spw_normalizerPowers_five {K : Type} [Group K] [Finite K] (hpl : SylowIsPlane 5 K)
    (hsc : A10Scalars K) : NormalizerPowers 5 K := by
  intro S t ht ht1 k hk
  obtain ⟨n, hn, hns⟩ := hsc S
  have h5 : ∀ s ∈ (S : Subgroup K), s ^ 5 = 1 := (hpl S).1.2
  have hact : ∀ i : ℕ, ∀ s ∈ (S : Subgroup K), n ^ i * s * (n ^ i)⁻¹ = s ^ (2 ^ i) := by
    intro i
    induction i with
    | zero => intro s hs; simp
    | succ i ih =>
      intro s hs
      have e1 : n ^ (i + 1) * s * (n ^ (i + 1))⁻¹ = n * (n ^ i * s * (n ^ i)⁻¹) * n⁻¹ := by group
      rw [e1, ih s hs, ← conj_pow, hns s hs, ← pow_two, ← pow_mul, ← pow_succ']
  have hk5 : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  have key : ∃ i : ℕ, 2 ^ i % 5 = k % 5 := by
    rcases hk5 with h | h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨3, by norm_num [h]⟩
    · exact ⟨2, by norm_num [h]⟩
  obtain ⟨i, hi⟩ := key
  refine ⟨n ^ i, (normalizer ((S : Subgroup K) : Set K)).pow_mem hn i, ?_⟩
  rw [hact i t ht, pow_eq_pow_mod (2 ^ i) (h5 t ht), pow_eq_pow_mod k (h5 t ht), hi]

theorem spw_natCast_isSquare_gf {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ} (hk : ¬ p ∣ k) :
    IsSquare ((k : ℕ) : GaloisField p 2) := by
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hF2 : ringChar (GaloisField p 2) ≠ 2 := by
    rw [ringChar.eq (GaloisField p 2) p]
    exact hp2
  have hkF : ((k : ℕ) : GaloisField p 2) ≠ 0 := fun h => hk ((CharP.cast_eq_zero_iff (GaloisField p 2) p k).1 h)
  rw [FiniteField.isSquare_iff hF2 hkF]
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by norm_num)
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hk
  have hfermat : ((k : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hkz
  have hcast : ((k : ℕ) : GaloisField p 2) = algebraMap (ZMod p) (GaloisField p 2) ((k : ℕ) : ZMod p) :=
    (map_natCast (algebraMap (ZMod p) (GaloisField p 2)) k).symm
  have hodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  obtain ⟨m, hm⟩ := hodd
  have hsq : p ^ 2 = 2 * (2 * m * m + 2 * m) + 1 := by rw [hm]; ring
  have hexp : p ^ 2 / 2 = (p - 1) * ((p + 1) / 2) := by
    have h1 : p - 1 = 2 * m := by omega
    have h2 : (p + 1) / 2 = m + 1 := by omega
    have h3 : (p - 1) * ((p + 1) / 2) = 2 * m * m + 2 * m := by
      rw [h1, h2]
      ring
    rw [h3]
    omega
  rw [hcard, hexp, hcast, ← map_pow, pow_mul, hfermat, one_pow, map_one]

theorem spw_normalizerPowers_psl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    NormalizerPowers p (PSL(2, GaloisField p 2)) := by
  intro S t ht ht1 k hk
  obtain ⟨ψ, hψ, hψU, hψc⟩ := CFSG.AGLEmbedding.exists_torus_action hp2 (by norm_num : 1 ≤ 2) S
  have ht' : t ∈ ψ.range := by
    rw [hψU]
    exact ht
  obtain ⟨a, rfl⟩ := ht'
  obtain ⟨r, hr⟩ := spw_natCast_isSquare_gf hp2 hk
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hkF : ((k : ℕ) : GaloisField p 2) = 0 := by simpa using hr
    exact hk ((CharP.cast_eq_zero_iff (GaloisField p 2) p k).1 hkF)
  obtain ⟨c, hcN, hc⟩ := hψc (Units.mk0 r hr0)
  refine ⟨c, hcN, ?_⟩
  rw [hc a, ← map_pow]
  congr 1
  change _ = Multiplicative.ofAdd (k • Multiplicative.toAdd a)
  rw [nsmul_eq_mul, hr]
  simp [pow_two]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
