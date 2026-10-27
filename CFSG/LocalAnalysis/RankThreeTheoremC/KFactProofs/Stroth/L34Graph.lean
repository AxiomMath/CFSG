module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Embed
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34GraphSpec
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.PSL3Four

theorem kFactL34Graph :
    KFactL34Graph := by
  intro X _ _ K hKn hC hL P hPK hPsyl u huK hu3 huN W hW hWN hWC
  haveI := hKn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε, ψ, hψinj, hψR, hψK⟩ := KFactProofs.Stroth.L34Embed.exists_embedding_R hC hL
  have hKcard : Nat.card K = 20160 := by
    rw [Nat.card_congr ε.toEquiv]
    exact card_S
  have hPcard : Nat.card P = 64 := by
    rw [hPsyl.card_eq, hKcard, Nat.factorization_def _ Nat.prime_two,
      show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hψS : ∀ k ∈ K, ψ k ∈ S := fun k hk => by
    show ψ ((⟨k, hk⟩ : K) : X) ∈ S
    rw [hψK]
    exact (ε ⟨k, hk⟩).2
  let S₁ : Subgroup (Equiv.Perm (Fin 42)) := P.map ψ
  have hS₁S : S₁ ≤ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact hψS p (hPK hp)
  have hS₁c : Nat.card S₁ = 64 := by
    rw [Subgroup.card_map_of_injective hψinj]
    exact hPcard
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu3
    omega
  have hu3' : u ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu3] at this
  have hψN : ∀ g ∈ normalizer (P : Set X), ∀ t ∈ S₁, ψ g * t * (ψ g)⁻¹ ∈ S₁ := by
    rintro g hg _ ⟨p, hp, rfl⟩
    refine ⟨g * p * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg p).1 hp, ?_⟩
    rw [map_mul, map_mul, map_inv]
  obtain ⟨hA, hB, hC'⟩ := KFactProofs.Stroth.L34Graph.l34Graph_of_sylow hS₁S hS₁c (hψS u huK)
    (by rw [← map_pow, hu3', map_one]) (fun h => hu1 (hψinj (by rw [h, map_one])))
    (hψN u huN)
  have hWψ : ∀ w ∈ W, ψ w ∈ R ∧ (∀ t ∈ S₁, ψ w * t * (ψ w)⁻¹ ∈ S₁) ∧ ψ w * ψ u = ψ u * ψ w := by
    intro w hw
    refine ⟨hψR w, hψN w (hWN hw), ?_⟩
    have hwu : w * u = u * w := Subgroup.mem_centralizer_singleton_iff.1 (hWC hw)
    rw [← map_mul, ← map_mul, hwu]
  have step : ∀ k : ℕ, ∀ w ∈ W, w ^ (2 ^ (k + 2)) = 1 → w ^ (2 ^ (k + 1)) = 1 := by
    intro k w hw hwk
    have hv : w ^ (2 ^ k) ∈ W := W.pow_mem hw _
    obtain ⟨hvR, hvN, hvu⟩ := hWψ _ hv
    have hv4 : (w ^ (2 ^ k)) ^ 4 = 1 := by
      rw [← pow_mul, show 2 ^ k * 4 = 2 ^ (k + 2) by ring]
      exact hwk
    have h2 := hA (ψ (w ^ (2 ^ k))) hvR hvN hvu (by rw [← map_pow, hv4, map_one])
    have hv2 : (w ^ (2 ^ k)) ^ 2 = 1 := hψinj (by rw [map_pow, h2, map_one])
    rw [pow_succ, pow_mul]
    exact hv2
  have down : ∀ j : ℕ, ∀ w ∈ W, w ^ (2 ^ (j + 1)) = 1 → w ^ 2 = 1 := by
    intro j
    induction j with
    | zero =>
      intro w _ h
      simpa using h
    | succ j ih =>
      intro w hw h
      exact ih w hw (step j w hw h)
  have hsq : ∀ w ∈ W, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
    have hk' : w ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rcases k with _ | j
    · rw [pow_zero, pow_one] at hk'
      rw [hk']
      exact one_pow 2
    · exact down j w hw hk'
  have huniq : ∀ a ∈ W, ∀ b ∈ W, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    by_contra hne
    have hcomm : a * b = b * a := by
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq a ha)
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq b hb)
      have hab' : (a * b)⁻¹ = a * b :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq _ (W.mul_mem ha hb))
      calc a * b = (a * b)⁻¹ := hab'.symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [ha', hb']
    obtain ⟨haR, haN, hau⟩ := hWψ a ha
    obtain ⟨hbR, hbN, hbu⟩ := hWψ b hb
    exact hB (ψ a) haR haN hau (ψ b) hbR hbN hbu (by rw [← map_pow, hsq a ha, map_one])
      (by rw [← map_pow, hsq b hb, map_one]) (fun h => ha1 (hψinj (by rw [h, map_one])))
      (fun h => hb1 (hψinj (by rw [h, map_one]))) (fun h => hne (hψinj h))
      (by rw [← map_mul, ← map_mul, hcomm])
  have hWcard : Nat.card W ≤ 2 := by
    classical
    have hinj : Function.Injective (fun w : W => (decide ((w : X) = 1) : Bool)) := by
      intro a b hab
      simp only [decide_eq_decide] at hab
      by_cases ha : (a : X) = 1
      · exact Subtype.ext (ha.trans (hab.1 ha).symm)
      · exact Subtype.ext (huniq a a.2 b b.2 ha (fun hb => ha (hab.2 hb)))
    calc Nat.card W ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  refine ⟨hWcard, ?_⟩
  intro w hw hw1 t ht hwt
  obtain ⟨htC, htK⟩ := Subgroup.mem_inf.1 ht
  obtain ⟨hwR, hwN, hwu⟩ := hWψ w hw
  have htu : t * u = u * t := Subgroup.mem_centralizer_singleton_iff.1 htC
  have h3 := hC' (ψ w) hwR hwN hwu (by rw [← map_pow, hsq w hw, map_one])
    (fun h => hw1 (hψinj (by rw [h, map_one]))) (ψ t) (hψS t htK)
    (by rw [← map_mul, ← map_mul, htu]) (by rw [← map_mul, ← map_mul, hwt.symm])
  rcases h3 with h | h | h
  · have : t = 1 := hψinj (by rw [h, map_one])
    rw [this]
    exact one_mem _
  · have : t = u := hψinj h
    rw [this]
    exact mem_zpowers u
  · have : t = u * u := hψinj (by rw [h, map_mul])
    rw [this]
    exact Subgroup.mul_mem _ (mem_zpowers u) (mem_zpowers u)

end CFSG.LocalAnalysis.RankThreeTheoremC
