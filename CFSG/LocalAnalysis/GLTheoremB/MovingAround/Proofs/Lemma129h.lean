module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129g

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129h

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129g
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

section Final

variable {G : Type} [Group G] [Finite G] {N K F A E : Subgroup G}

theorem isThreeCycle_of_mem_zpowers {α : Type*} [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hσ : σ.IsThreeCycle) {g : Equiv.Perm α} (hg : g ∈ Subgroup.zpowers σ) (hg1 : g ≠ 1) :
    g.IsThreeCycle := by
  obtain ⟨z, rfl⟩ := hg
  have hord := hσ.orderOf
  have h1 : σ ^ (z % ((orderOf σ : ℕ) : ℤ)) = σ ^ z := zpow_mod_orderOf σ z
  rw [hord] at h1
  have h2 : 0 ≤ z % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : z % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  change (σ ^ z) ≠ 1 at hg1
  change (σ ^ z).IsThreeCycle
  rw [← h1] at hg1 ⊢
  generalize z % ((3 : ℕ) : ℤ) = k at h2 h3 hg1 ⊢
  interval_cases k
  · exact absurd (by simp) hg1
  · simpa using hσ
  · have : σ ^ (2 : ℤ) = σ * σ := by rw [zpow_two]
    rw [this]
    exact hσ.isThreeCycle_sq

theorem alt_final_data {n : ℕ} (hn13 : n = 13) (ψ : ↥(barX 3 N K) ≃* alternatingGroup (Fin n))
    (Ω₀ : Set (Fin n)) (hΩ₀ : Ω₀.ncard = 4)
    (hFfix : ∀ g ∈ permImage ψ (barX 3 N F), ∀ j ∈ Ω₀, g j = j)
    (hFmoves : ∀ j, j ∉ Ω₀ → ∃ g ∈ permImage ψ (barX 3 N F), g j ≠ j)
    (htrans : ∀ j k : Fin n, j ∉ Ω₀ → k ∉ Ω₀ →
      ∃! g : Equiv.Perm (Fin n), g ∈ permImage ψ (barX 3 N F) ∧ g j = k)
    (hF : IsEkIn 3 2 A F) {a : G} (haA : a ∈ A) (hAeq : A = F ⊔ Subgroup.zpowers a)
    (hFa : F ⊓ Subgroup.zpowers a = ⊥) {σ : Equiv.Perm (Fin n)} (hσ3 : σ.IsThreeCycle)
    (hσsupp : ∀ j, j ∉ Ω₀ → σ j = j)
    (hperm : permImage ψ (barX 3 N (Subgroup.zpowers a)) = Subgroup.zpowers σ)
    (horb : ∃ i : Fin n, Set.ncard (MulAction.orbit ↥(permImage ψ (barX 3 N (E ⊓ A))) i) = 9) :
    Lemma129IvAData N K E A := by
  subst hn13
  refine ⟨ψ, horb, F, a, hF, ?_, ?_, haA, hAeq, hFa, ?_⟩
  · have : {j : Fin 13 | ∀ g ∈ permImage ψ (barX 3 N F), g j = j} = Ω₀ := by
      ext j
      constructor
      · intro hj
        by_contra hjΩ
        obtain ⟨g, hg, hgj⟩ := hFmoves j hjΩ
        exact hgj (hj g hg)
      · intro hj g hg
        exact hFfix g hg j hj
    show Set.ncard {j : Fin 13 | ∀ g ∈ permImage ψ (barX 3 N F), g j = j} = 4
    rw [this]
    exact hΩ₀
  · intro j k hj hk
    obtain ⟨g, hg, hgj⟩ := hj
    obtain ⟨g', hg', hgk⟩ := hk
    have hjΩ : j ∉ Ω₀ := fun hjΩ => hgj (hFfix g hg j hjΩ)
    have hkΩ : k ∉ Ω₀ := fun hkΩ => hgk (hFfix g' hg' k hkΩ)
    exact htrans j k hjΩ hkΩ
  · intro g hg hg1
    have hg' : g ∈ Subgroup.zpowers σ := by rw [← hperm]; exact hg
    refine ⟨isThreeCycle_of_mem_zpowers hσ3 hg' hg1, fun j hj => ?_⟩
    obtain ⟨h, hh, hhj⟩ := hj
    have hjΩ : j ∉ Ω₀ := fun hjΩ => hhj (hFfix h hh j hjΩ)
    obtain ⟨z, rfl⟩ := hg'
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hσsupp j hjΩ) z

end Final

section OrbitNine

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A N D S F K : Subgroup G}

theorem alt_orbit_nine (h23 : Input23_5) (h : Cex127 G m 3 B M E A N D) (hs : Setup2 M A N 3 S F K)
    (D' : AltData 3 N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A)
    (hδ4 : D'.δ = 4) (hr2 : CFSG.Open.pRank 3 F = 2) :
    ∃ i : Fin D'.n, Set.ncard (MulAction.orbit ↥(permImage D'.ψ (barX 3 N (E ⊓ A))) i) = 9 := by
  have hp := prime_of h
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 := ne_two_of h
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hA0N : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hle : barX 3 N A ≤ barX 3 N K := alt_le_K h hs D' hAK hFA rfl hδ4
  have hH : barX 3 N (E ⊓ A) ≤
      Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    barX_le_normalizer (inf_le_right.trans hAK)
  have hHp : IsPGroup 3 ↥(barX 3 N (E ⊓ A)) :=
    Lemma129.isPGroup_barX ((A_el h).mono inf_le_right).isPGroup hA0N
  obtain ⟨κ₀, hκ₀⟩ := exists_implementer (by omega) (by omega) D'.ψ hp hp2 hH hHp
  have hA0K : barX 3 N (E ⊓ A) ≤ barX 3 N K := (barX_mono129 inf_le_right).trans hle
  have hκself : ∀ a : ↥(barX 3 N (E ⊓ A)), κ₀ a = ⟨(a : ↥N ⧸ GLAPPrimeCore 3 ↥N), hA0K a.2⟩ := by
    intro a
    apply impl_unique (by omega) D'.ψ
    intro x
    rw [← hκ₀ a x]
  have hAcard : Nat.card A = 27 := by
    have := card_A_of_ne hp hs hFA
    rw [card_eq_pow_pRank hp ((A_el h).mono hFA'), hr2] at this
    simpa using this
  have hA0card : Nat.card (E ⊓ A : Subgroup G) ≤ 9 := by
    have hlt : Nat.card (E ⊓ A : Subgroup G) < Nat.card A := card_lt_of_lt' (A0_lt_A h)
    have hdvd : Nat.card (E ⊓ A : Subgroup G) ∣ 3 ^ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : E ⊓ A ≤ A)
      rw [hAcard] at this
      simpa using this
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [hjeq] at hlt ⊢
    rw [hAcard] at hlt
    have : j < 3 := by
      by_contra hj3
      have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  have hAr : CFSG.Open.pRank 3 A = CFSG.Open.pRank 3 F + 1 := by
    have h1 := card_A_of_ne hp hs hFA
    rw [card_eq_pow_pRank hp (A_el h), card_eq_pow_pRank hp ((A_el h).mono hFA'),
      ← pow_succ'] at h1
    exact (Nat.pow_right_injective hp.two_le) h1
  obtain ⟨i, hi⟩ := alt_orbit_big h23 h hs D' hAK (Or.inr ⟨rfl, hδ4, hAr⟩) κ₀ hκ₀
  refine ⟨i, ?_⟩
  have hset : {j : Fin D'.n | ∃ b ∈ κ₀.range,
      ((D'.ψ b : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) i = j} =
      MulAction.orbit ↥(permImage D'.ψ (barX 3 N (E ⊓ A))) i := by
    ext j
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
      refine ⟨⟨_, (mem_permImage D'.ψ).2 ⟨κ₀ a, ?_, rfl⟩⟩, rfl⟩
      rw [hκself a]
      exact a.2
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (mem_permImage D'.ψ).1 hg
      refine ⟨x, ⟨⟨x, hx⟩, ?_⟩, rfl⟩
      rw [hκself]
  have hlen : orbitLen D'.ψ κ₀.range i = Set.ncard (MulAction.orbit
      ↥(permImage D'.ψ (barX 3 N (E ⊓ A))) i) := by
    unfold orbitLen
    rw [hset]
  rw [← hlen]
  have h1 : orbitLen D'.ψ κ₀.range i ≤ Nat.card κ₀.range := orbitLen_le_card D'.ψ κ₀.range i
  have h2 : Nat.card κ₀.range ≤ Nat.card (barX 3 N (E ⊓ A)) :=
    Nat.card_le_card_of_surjective _ κ₀.rangeRestrict_surjective
  have h3 : Nat.card (barX 3 N (E ⊓ A)) = Nat.card (E ⊓ A : Subgroup G) :=
    card_barX_of_isPGroup hp hA0N ((A_el h).mono inf_le_right).isPGroup
  rw [hr2] at hi
  have : (3 : ℕ) ^ 2 = 9 := by norm_num
  omega

end OrbitNine

section CaseA

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem isAltType_of_n13 {n : ℕ} (hn13 : n = 13) (hp : p.Prime) (hK : GLAPComponent p N K)
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) : IsAltType 13 (barOf p K) := by
  subst hn13
  exact ⟨(quotEquivBarX hp hK.1 hK.2.1).trans ψ⟩

theorem alt_case_of_norm (h23 : Input23_5) (h121 : Prop121_corStatement)
    (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) (D' : AltData p N K F)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hr2 : CFSG.Open.pRank p F = 2) (hE5 : 5 ≤ CFSG.Open.pRank p E) :
    Lemma129Common p M E A N K ∧
      (p = 3 ∧ 5 ≤ CFSG.Open.pRank 3 E ∧ IsAltType 13 (barOf 3 K) ∧ barX 3 N A ≤ barX 3 N K ∧
        Lemma129IvAData N K E A) := by
  have hp := prime_of h
  have hFA := alt_F_ne_A h23 h hs D'
  obtain ⟨hp3, hδ4⟩ := alt_p_three_delta_four h121 h hs D' hAK hFA
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 := ne_two_of h
  obtain ⟨hcomp, hpcore, -⟩ := alt_Ystruct h hs D' hAK hFA rfl hδ4
  have hle := alt_le_K h hs D' hAK hFA rfl hδ4
  obtain ⟨hm1, htrans, a, haA, hAeq, hFa, σ, hσ3, hσsupp, hperm⟩ :=
    alt_structure h hs D' hAK hFA rfl hδ4
  have hn13 : D'.n = 13 := by
    have := D'.hn
    rw [hδ4, hm1, hr2] at this
    simpa using this
  have horb := alt_orbit_nine h23 h hs D' hAK hFA hδ4 hr2
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hFN : F ≤ N := hFA'.trans hAN
  have hFK : barX 3 N F ≤ barX 3 N K := (barX_mono129 hFA').trans hle
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hκself : ∀ f : ↥(barX 3 N F), D'.κ f = ⟨(f : ↥N ⧸ GLAPPrimeCore 3 ↥N), hFK f.2⟩ := by
    intro f
    apply impl_unique (by omega) D'.ψ
    intro x
    rw [← D'.hκ f x]
  have hFperm : ∀ g ∈ permImage D'.ψ (barX 3 N F), ∃ f : ↥(barX 3 N F),
      g = ((D'.ψ (D'.κ f) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := (mem_permImage D'.ψ).1 hg
    refine ⟨⟨(x : ↥N ⧸ GLAPPrimeCore 3 ↥N), hx⟩, ?_⟩
    rw [hκself]
  have hFfix : ∀ g ∈ permImage D'.ψ (barX 3 N F), ∀ j ∈ D'.Ω₀, g j = j := by
    intro g hg j hj
    obtain ⟨f, rfl⟩ := hFperm g hg
    exact D'.hfix f j hj
  have hFel : IsElemAbelian 3 F := (A_el h).mono hFA'
  have hFcard : Nat.card (barX 3 N F) = 3 ^ CFSG.Open.pRank 3 F := by
    rw [card_barX_of_isPGroup hp hFN hFel.isPGroup, card_eq_pow_pRank hp hFel]
  have hFmoves : ∀ j, j ∉ D'.Ω₀ → ∃ g ∈ permImage D'.ψ (barX 3 N F), g j ≠ j := by
    intro j hj
    have h9 : Nat.card (barX 3 N F) = 9 := by rw [hFcard, hr2]; norm_num
    have hnt : Nontrivial ↥(barX 3 N F) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨f, hf1⟩ := exists_ne (1 : ↥(barX 3 N F))
    refine ⟨((D'.ψ (D'.κ f) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)), ?_,
      D'.hsemi f hf1 j hj⟩
    refine (mem_permImage D'.ψ).2 ⟨D'.κ f, ?_, rfl⟩
    rw [hκself]
    exact f.2
  have hF : IsEkIn 3 2 A F := ⟨hFA', hFel, by rw [card_eq_pow_pRank hp hFel, hr2]⟩
  have hAr : CFSG.Open.pRank 3 A = 3 := by
    have h1 := card_A_of_ne hp hs hFA
    rw [card_eq_pow_pRank hp (A_el h), card_eq_pow_pRank hp hFel, hr2] at h1
    have h2 : (3 : ℕ) ^ CFSG.Open.pRank 3 A = 3 ^ 3 := by rw [h1]; norm_num
    exact (Nat.pow_right_injective hp.two_le) h2
  have hA0 : CFSG.Open.pRank 3 (E ⊓ A) = 2 :=
    le_antisymm (c104_rank_inf_le_two_of_DD hp h.pair (Or.inr hAr)) (two_le_rank_inf h)
  refine ⟨⟨hs.hK, ⟨hAr, hA0⟩, hs.hnc, ⟨layer_eq_of_comp h hs hcomp, hpcore⟩⟩, rfl, hE5,
    isAltType_of_n13 hn13 hp hs.hK D'.ψ, hle, ?_⟩
  exact alt_final_data hn13 D'.ψ D'.Ω₀ (by rw [D'.hΩ₀, hδ4]) hFfix hFmoves htrans hF haA hAeq hFa
    hσ3 hσsupp hperm horb

end CaseA



end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129h

end
