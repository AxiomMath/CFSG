module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129f

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129g

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

section Pipeline

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem inf_normalizer_eq_of_not_le (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hAK : ¬ A ≤ Subgroup.normalizer (K : Set G)) : A ⊓ Subgroup.normalizer (K : Set G) = F := by
  have hp := prime_of h
  have hFA := hs.F_le_A
  have hFne : F ≠ A := fun hFA' => hAK (hFA' ▸ hs.hFK)
  have hcard := card_A_of_ne hp hs hFne
  set C := A ⊓ Subgroup.normalizer (K : Set G) with hC
  have hFC : F ≤ C := le_inf hFA hs.hFK
  have hCA : C ≤ A := inf_le_left
  have h1 : Nat.card F ∣ Nat.card C := Subgroup.card_dvd_of_le hFC
  have h2 : Nat.card C ∣ p * Nat.card F := hcard ▸ Subgroup.card_dvd_of_le hCA
  obtain ⟨c, hc⟩ := h1
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have h3 : c ∣ p := by
    rw [hc] at h2
    have : Nat.card F * c ∣ Nat.card F * p := by rwa [mul_comm p] at h2
    exact (Nat.mul_dvd_mul_iff_left hFpos).1 this
  rcases (Nat.dvd_prime hp).1 h3 with h4 | h4
  · rw [h4, mul_one] at hc
    exact (Subgroup.eq_of_le_of_card_ge hFC (le_of_eq hc)).symm
  · exfalso
    apply hAK
    have : C = A := Subgroup.eq_of_le_of_card_ge hCA (by rw [hc, h4, hcard, mul_comm])
    rw [← this]
    exact inf_le_right

theorem AltData.hFinner (D' : AltData p N K F) :
    ∀ f ∈ barX p N F, ∃ k ∈ barX p N K, ∀ y ∈ barX p N K, f * y * f⁻¹ = k * y * k⁻¹ := by
  intro f hf
  refine ⟨(D'.κ ⟨f, hf⟩ : ↥(barX p N K)), (D'.κ ⟨f, hf⟩).2, fun y hy => ?_⟩
  exact D'.hκ ⟨f, hf⟩ ⟨y, hy⟩

theorem A0_lt_A (h : Cex127 G m p B M E A N D) : E ⊓ A < A :=
  lt_of_le_of_ne inf_le_right (c104_inf_ne h.pair.1.1 h.pair.1.2.1).2

theorem alt_F_ne_A (h23 : Input23_5) (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) : F ≠ A := by
  intro hFA'
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := ne_two_of h
  have hAN := A_le_N h
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hFA' ▸ hs.hFK
  have hA0N : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hn11 := D'.hn11 (by have := hp.two_le; omega) hs.hr
  have hH : barX p N (E ⊓ A) ≤
      Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    barX_le_normalizer (inf_le_right.trans hAK)
  have hHp : IsPGroup p ↥(barX p N (E ⊓ A)) :=
    Lemma129.isPGroup_barX ((A_el h).mono inf_le_right).isPGroup hA0N
  obtain ⟨κ₀, hκ₀⟩ := exists_implementer (by omega) (by omega) D'.ψ hp hp2 hH hHp
  obtain ⟨i, hi⟩ := alt_orbit_big h23 h hs D' hAK (Or.inl (by rw [hFA'])) κ₀ hκ₀
  have h1 : orbitLen D'.ψ κ₀.range i ≤ Nat.card κ₀.range := orbitLen_le_card D'.ψ κ₀.range i
  have h2 : Nat.card κ₀.range ≤ Nat.card (barX p N (E ⊓ A)) :=
    Nat.card_le_card_of_surjective _ κ₀.rangeRestrict_surjective
  have h3 : Nat.card (barX p N (E ⊓ A)) = Nat.card (E ⊓ A : Subgroup G) :=
    card_barX_of_isPGroup hp hA0N ((A_el h).mono inf_le_right).isPGroup
  have hlt : Nat.card (E ⊓ A : Subgroup G) < Nat.card A := card_lt_of_lt' (A0_lt_A h)
  have hAcard : Nat.card A = p ^ CFSG.Open.pRank p F := by
    rw [card_eq_pow_pRank hp (A_el h), hFA']
  omega

theorem alt_Ystruct (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A)
    (hp3 : p = 3) (hδ4 : D'.δ = 4) :
    (∀ K' : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N), IsComponentOf K' ⊤ →
        ∃ g ∈ barX p N A, K' = GLBConj g (barX p N K)) ∧
      CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N) = ⊥ ∧
      Subgroup.centralizer ((⨆ g ∈ barX p N A, GLBConj g (barX p N K) :
        Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) : Set (↥N ⧸ GLAPPrimeCore p ↥N)) = ⊥ := by
  have hcen := alt_centralizer_trivial h hs D' hAK hFA hp3 hδ4
  have hp := prime_of h
  refine Lemma129Y.scp_centralizer_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
    (Lemma129b.barX_A_isSCp h) hs.hK.2.2.1 ?_
  intro x hx hxc
  have hK₁le : barX p N K ≤ (⨆ g ∈ barX p N A, GLBConj g (barX p N K) :
      Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    refine le_iSup₂_of_le (1 : ↥N ⧸ GLAPPrimeCore p ↥N) (Subgroup.one_mem _) ?_
    rw [gLBConj_one]
  exact hcen x hx fun y hy => hxc y (hK₁le hy)

theorem layer_eq_of_comp (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hcomp : ∀ K' : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N), IsComponentOf K' ⊤ →
        ∃ g ∈ barX p N A, K' = GLBConj g (barX p N K)) :
    GLAPLayer p N = ⨆ g ∈ A, GLBConj g K := by
  have hAN := A_le_N h
  have hconjcomp : ∀ g ∈ A, GLAPComponent p N (GLBConj g K) := fun g hg => by
    have := glaPComponent_gLBConj hs.hK g
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hAN hg))] at this
  unfold GLAPLayer
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    have hL' : GLAPComponent p N L := hL
    have hLc : IsComponentOf (barX p N L) ⊤ := hL'.2.2.1
    obtain ⟨g', hg', hLg⟩ := hcomp (barX p N L) hLc
    obtain ⟨⟨g, hgN⟩, hgA, rfl⟩ := hg'
    have hgA' : g ∈ A := (Subgroup.mem_subgroupOf).1 hgA
    have hL'' : L = GLBConj g K := by
      refine glaPComponent_unique hL' (hconjcomp g hgA') ?_
      rw [barX_gLBConj_eq p hgN K]
      exact hLg
    rw [hL'']
    exact le_iSup₂_of_le g hgA' le_rfl
  · exact iSup₂_le fun g hg => le_sSup (hconjcomp g hg)

end Pipeline

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129g

end
