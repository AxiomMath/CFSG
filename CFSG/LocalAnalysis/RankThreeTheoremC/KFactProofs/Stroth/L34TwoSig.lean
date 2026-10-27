module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupCases
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Hom
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34TwoSigSpec
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer

open CFSG.ComponentClassification.PSL3Four CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34TwoSig

private theorem pow_256_eq_one {y : Equiv.Perm (Fin 42)}
    (hy : y ∈ R) {n : ℕ} (hn : y ^ 2 ^ n = 1) : y ^ 256 = 1 := by
  have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf y ∣ 241920 := by
    rw [← card_R]
    have := orderOf_dvd_natCard (⟨y, hy⟩ : R)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hm] at h2
  have hm8 : m ≤ 8 := by
    by_contra h
    have := (Nat.pow_dvd_pow 2 (by omega : 9 ≤ m)).trans h2
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hm]
  exact (Nat.pow_dvd_pow 2 hm8).trans (by norm_num)

theorem twoSignalizerL34 :
    TwoSignalizerL34 := by
  intro X _ _ K hKn _hs _hnab B _hB hBc _hBC hcase T hT hBT
  obtain ⟨hL, hBK⟩ := hcase
  haveI : K.Normal := hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ε, ψ, hker, hψR, hψK⟩ := L34Hom.exists_hom_R hL
  obtain ⟨B₀, hB₀S, hB₀c, hcheck⟩ := l34TwoSig_check
  have hψK' : ∀ k (hk : k ∈ K), ψ k = ((ε ⟨k, hk⟩ : ↥S) : Equiv.Perm (Fin 42)) :=
    fun k hk => hψK ⟨k, hk⟩
  have hinj : Set.InjOn ψ (B : Set X) := by
    intro a ha b hb hab
    have : ε ⟨a, hBK ha⟩ = ε ⟨b, hBK hb⟩ :=
      Subtype.ext (by rw [← hψK' a (hBK ha), ← hψK' b (hBK hb)]; exact hab)
    exact congrArg Subtype.val (ε.injective this)
  let B' : Subgroup (Equiv.Perm (Fin 42)) := B.map ψ
  have hB'S : B' ≤ S := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hψK' b (hBK hb)]
    exact (ε _).2
  have hB'c : Nat.card B' = 9 := by
    have h1 : Nat.card B' = Nat.card B := by
      show Nat.card ((B' : Set (Equiv.Perm (Fin 42)))) = Nat.card ((B : Set X))
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Subgroup.coe_map,
        hinj.ncard_image]
    rw [h1, hBc]
    norm_num
  have hfac : (Nat.card S).factorization 3 = 2 := by
    rw [card_S, Nat.factorization_def _ Nat.prime_three,
      show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hsyl₀ : IsSylowOf 3 B₀ S := isSylowOf_of_card hB₀S (by rw [hfac, hB₀c]; norm_num)
  have hsyl₁ : IsSylowOf 3 B' S := isSylowOf_of_card hB'S (by rw [hfac, hB'c]; norm_num)
  obtain ⟨s, hsS, hs⟩ := hsyl₀.exists_mem_conj hsyl₁
  have hsR : s ∈ R := S_le_R hsS
  have hconjR : ∀ t, s⁻¹ * ψ t * s ∈ R := fun t =>
    R.mul_mem (R.mul_mem (R.inv_mem hsR) (hψR t)) hsR
  have h256 : ∀ t ∈ T, (s⁻¹ * ψ t * s) ^ 256 = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    have htn : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
    refine pow_256_eq_one (hconjR t) (n := n) ?_
    have e : s⁻¹ * ψ t * s = (MulAut.conj s⁻¹) (ψ t) := by simp [MulAut.conj_apply]
    rw [e, ← map_pow, ← map_pow, htn, map_one, map_one]
  have hcomm : ∀ t ∈ T, ∀ c ∈ B₀, c * (s⁻¹ * ψ t * s) = s⁻¹ * ψ t * s * c := by
    intro t ht
    rcases hcheck _ (hconjR t) (h256 t ht) with h | ⟨w, hw, hw256⟩
    · exact h
    · exfalso
      let T' : Subgroup (Equiv.Perm (Fin 42)) := (T.map ψ).map (MulAut.conj s⁻¹).toMonoidHom
      have hcl : Subgroup.closure {x | ∃ c ∈ B₀, x = c * (s⁻¹ * ψ t * s) * c⁻¹} ≤ T' := by
        rw [Subgroup.closure_le]
        rintro _ ⟨c, hc, rfl⟩
        have hy : s * c * s⁻¹ ∈ B' :=
          (hs _).2 (by rw [show s⁻¹ * (s * c * s⁻¹) * s = c by group]; exact hc)
        obtain ⟨b, hb, hbe⟩ := hy
        refine ⟨ψ (b * t * b⁻¹), ⟨b * t * b⁻¹, ?_, rfl⟩, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
        · have e : c = s⁻¹ * ψ b * s := by rw [hbe]; group
          rw [e]
          change (MulAut.conj s⁻¹) (ψ (b * t * b⁻¹)) = _
          rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
          group
      obtain ⟨_, ⟨t', ht', rfl⟩, rfl⟩ := hcl hw
      apply hw256
      have := h256 t' ht'
      simpa [MulAut.conj_apply] using this
  rw [Subgroup.commutator_le]
  intro b hb t ht
  apply hker
  have hc := hcomm t ht _ ((hs _).1 (⟨b, hb, rfl⟩ : ψ b ∈ B'))
  have e : ψ b * ψ t = ψ t * ψ b := by
    have h1 : s⁻¹ * (ψ b * ψ t) * s = s⁻¹ * (ψ t * ψ b) * s := by
      calc s⁻¹ * (ψ b * ψ t) * s = s⁻¹ * ψ b * s * (s⁻¹ * ψ t * s) := by group
        _ = s⁻¹ * ψ t * s * (s⁻¹ * ψ b * s) := hc
        _ = s⁻¹ * (ψ t * ψ b) * s := by group
    exact mul_left_cancel (mul_right_cancel h1)
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, e]
  group

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer
