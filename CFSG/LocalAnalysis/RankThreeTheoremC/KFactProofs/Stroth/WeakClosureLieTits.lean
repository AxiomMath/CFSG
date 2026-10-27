module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Sporadic.Schreier.Tits (titsD card_titsD titsModelEquiv titsD_center)
open CFSG.SectionRank (exists_mulEquiv_titsGroup_of_model Tits_sylow3_cubic_witness)
open CFSG.AGLEmbeddingD2 (torusLocal_tits_sylow TorusLocal)

theorem normalizerMovesLines_of_torusLocal {p : ℕ} {X : Type} [Group X] {R : Subgroup X}
    (h : TorusLocal p R) : NormalizerMovesLines p R := by
  obtain ⟨-, -, -, -, t, ht, m, lam, e, hm, -, -, -, -, hlines⟩ := h
  intro A hAR hA
  refine ⟨t, ht, fun hmap => ?_⟩
  exact hlines 1 one_pos (by omega) A hAR hA
    (by rw [pow_one, Subgroup.mem_normalizer_iff_map_conj_eq]; exact hmap)

theorem factorization_titsOrder_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp5 : p ≠ 5) : (17971200 : ℕ).factorization p ≤ 1 := by
  by_contra hcon
  have hdvd : p ^ 2 ∣ 17971200 := (hp.pow_dvd_iff_le_factorization (by norm_num)).2 (by omega)
  have h17 : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [h17] at hdvd
  have key : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 13 := by
    have hpd : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := (dvd_pow_self p two_ne_zero).trans hdvd
    rcases hp.dvd_mul.1 hpd with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · rcases hp.dvd_mul.1 h with h | h
        · exact Or.inl (hp.dvd_of_dvd_pow h)
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inr (Or.inl (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases key with h | h | h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  · have h13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h13
    norm_num at hdvd

theorem crossReeTits_tits :
    CrossReeTits .Tits := by
  intro K _ _ ℓ f p _ hadm hp2 hpℓ hmodel
  obtain ⟨-, -, -, rfl, rfl⟩ := hadm
  obtain ⟨e⟩ := titsModelEquiv K 2 1 hmodel
  have hcard : Nat.card K = 17971200 := (Nat.card_congr e.toEquiv).trans card_titsD
  by_cases h3 : p = 3
  · subst h3
    obtain ⟨F, _, _, _, hF, ⟨e'⟩⟩ := exists_mulEquiv_titsGroup_of_model hmodel
    obtain ⟨x, y, h, -, -, hcomm, -, -, hcardQ, -, -, -⟩ := Tits_sylow3_cubic_witness hF
    refine WCOn.of_hom_noncomm (x := x) (y := y) e'.symm.toMonoidHom (IsPGroup.of_card hcardQ) ?_
      (Subgroup.subset_closure (Set.mem_insert x {y}))
      (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))) ?_
    · intro g _ hg
      exact e'.symm.injective (hg.trans (map_one e'.symm).symm)
    · intro hxy
      exact hcomm (commutatorElement_eq_one_iff_mul_comm.2 hxy)
  by_cases h5 : p = 5
  · subst h5
    have hctr : Subgroup.center K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : e x ∈ Subgroup.center titsD := by
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro y
        obtain ⟨y', rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, hx y']
      rw [titsD_center, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact e.injective (h1.trans e.map_one.symm)
    have hKc : Subgroup.centralizer ((⊤ : Subgroup K) : Set K) = ⊥ := by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, hctr]
    obtain ⟨P₀⟩ : Nonempty (Sylow 5 K) := inferInstance
    exact WCOn.of_normalizerMovesLines P₀ fun _ _ =>
      normalizerMovesLines_of_torusLocal (torusLocal_tits_sylow hKc (Subgroup.topEquiv.trans e) P₀)
  · apply WCOn.of_factorization_le_one
    rw [hcard]
    exact factorization_titsOrder_le_one Fact.out hp2 h3 h5

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
