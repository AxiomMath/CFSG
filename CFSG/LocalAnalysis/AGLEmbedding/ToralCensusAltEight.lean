module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeCore
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

theorem center_eq_bot_of_mulEquiv_alt_eight {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 8)) : Subgroup.center L = ⊥ := by
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier ⟨hq.1⟩
    (CFSG.GH74.Generic.centralQuotientMap e)
    (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
    CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup le_rfl] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem nonempty_alt_eight_mulEquiv_projectiveSL :
    Nonempty (alternatingGroup (Fin 8) ≃* projectiveSL 4 (GaloisField 2 1)) := by
  have hm : CFSG.Blueprint.LieModel (projectiveSL 4 (GaloisField 2 1)) .PSL 4 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_of_projectiveSL_evenChar le_rfl
      (GaloisField.card 2 1 one_ne_zero) (by norm_num) (by omega) (MulEquiv.refl _)⟩
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).1 hm
  exact ⟨e.symm⟩

theorem exists_naturalSetup_of_compat {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hCP : CompParab L J) {n f : ℕ} (hf : 1 ≤ f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f))
    {ρ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L}
    (hρ : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n (GaloisField 2 f) g) {p : ℕ}
    (hcyc : CycPerfect p J) {u : Y} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y))
    (hup : u ^ p = 1) (huC : u ∉ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ (σ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L)
      (e' : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f)) (I : Set ℕ)
      (t : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)),
      NaturalSetup L J p u n f σ e' I t ∧
        (u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y) →
          t ∈ perfectJoin (flagStabilizer n (GaloisField 2 f) I)) := by
  have hq := hCP.comp.2.2
  have hJL : J ≤ L := hCP.parab.1
  have hn : 1 ≤ n := by
    by_contra hn
    have := subsingleton_projectiveSL (n := n) (by omega) (GaloisField 2 f)
    have := hq.2.toNontrivial
    exact not_subsingleton _ e.toEquiv.subsingleton
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hne, hnb⟩ := exists_comap_eq_flagStabilizer hCP.odd hn e
    (surjective_and_ker_le_of_compat hq.1 e ρ hρ).1 hρ hCP.parab
  have hσk := (surjective_and_ker_le_of_compat hq.1 e' σ hσ).2
  obtain ⟨i, hiI⟩ := hne hCP.ne_top
  obtain ⟨i₀, hi₀, hi₀n, hi₀I⟩ := hnb hCP.ne_borel
  have hn3 : 3 ≤ n := by
    by_contra h
    have hi := hI i hiI
    exact hi₀I (show i₀ = i by omega ▸ hiI)
  obtain ⟨t, ht, c, hc, hut⟩ : ∃ t, (u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y) →
      t ∈ perfectJoin (flagStabilizer n (GaloisField 2 f) I)) ∧
      ∃ c ∈ Subgroup.centralizer (L : Set Y), u = (σ t : Y) * c := by
    by_cases hj : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)
    · obtain ⟨t, ht, hc⟩ := exists_eq_mul_of_mem_perfectJoin_sup hσs hσk hJL hj
      exact ⟨t, fun _ => hcomap ▸ ht, hc⟩
    · obtain ⟨t, hc⟩ := exists_eq_cover_mul_of_mem_sup hσs hu
      exact ⟨t, fun h => absurd h hj, hc⟩
  refine ⟨σ, e', I, t, ⟨hn3, hf, hσs, hσk, hσ, hI, ⟨i, hiI⟩, ⟨i₀, hi₀, hi₀n, hi₀I⟩, hcomap,
    ⟨c, hc, hut⟩, pow_mem_center_of_eq_mul hσ hc hut hup, not_mem_center_of_eq_mul hσs hc hut huC,
    hcomap ▸ centralizer_le_comap_of_eq_mul hc hut hfix, fun Q hQ hQp hQZ =>
      isCyclic_of_cycPerfect_comap hσs hσk hJL hcyc (hcomap ▸ hQ) hQp hQZ⟩, ht⟩

end ToralCensus

open ToralCensus in
theorem fixThreeVoid_alt_eight :
    FixThreeVoid (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 8))) := by
  intro Y _ _ L J u hd ⟨eA⟩
  have hZ := center_eq_bot_of_mulEquiv_alt_eight hd.parab.comp.2.2 hd.parab.odd eA
  obtain ⟨e8⟩ := nonempty_alt_eight_mulEquiv_projectiveSL
  obtain ⟨ρ, hρ⟩ := exists_compat_of_center_eq_bot hZ (eA.trans e8)
  obtain ⟨σ, e, I, t, hS, hjoin⟩ := exists_naturalSetup_of_compat hd.parab le_rfl _ hρ hd.cyc
    (Subgroup.mem_sup_left hd.mem) hd.pow hd.not_mem hd.fix
  have h3 := (eq_three_of_threeCensus hS.cuts hS.nonempty (hjoin hd.join) hS.pow_mem
    hS.centralizer_le hS.cyc).1
  omega

theorem FixThreeVoid.or {𝔉₁ 𝔉₂ : (X : Type) → [Group X] → Prop} (h₁ : FixThreeVoid 𝔉₁)
    (h₂ : FixThreeVoid 𝔉₂) : FixThreeVoid (fun X _ => 𝔉₁ X ∨ 𝔉₂ X) := by
  intro Y _ _ L J u hd h
  rcases h with h | h
  · exact h₁ Y L J u hd h
  · exact h₂ Y L J u hd h

theorem FixThreeVoid.mono {𝔉 𝔊 : (X : Type) → [Group X] → Prop} (h : FixThreeVoid 𝔊)
    (hle : ∀ (X : Type) [Group X], 𝔉 X → 𝔊 X) : FixThreeVoid 𝔉 :=
  fun Y _ _ L J u hd hF => h Y L J u hd (hle _ hF)

theorem fixThreeVoid_isSmallTwoOrG2_of {P4 : (X : Type) → [Group X] → Prop}
    (h4 : FixThreeVoid P4)
    (hP4 : ∀ (X : Type) [Group X], IsSmallTwoOrG2 X →
      P4 X ∨ Nonempty (X ≃* alternatingGroup (Fin 8))) :
    FixThreeVoid IsSmallTwoOrG2 :=
  (h4.or fixThreeVoid_alt_eight).mono hP4

end CFSG.AGLEmbedding
