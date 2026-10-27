module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section

variable {G G' : Type*} [Group G] [Group G'] [Finite G]

theorem i116red_unique {p : ℕ} (hp : p.Prime) (ψ : G →* G')
    (hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup G) ⊓ ψ.ker))) {L L' : Subgroup G}
    (hL : GLAPComponent p ⊤ L) (hL' : GLAPComponent p ⊤ L') (h : L.map ψ = L'.map ψ) :
    L = L' := by
  have e1 := lcEquiv_barX hp ψ ⊤ hker (le_top : L ≤ ⊤)
  have e2 := lcEquiv_barX hp ψ ⊤ hker (le_top : L' ≤ ⊤)
  rw [h] at e1
  exact glaPComponent_unique hL hL'
    (Subgroup.map_injective (lcEquiv hp ψ ⊤ hker).injective (e1.trans e2.symm))

theorem i116red_map_component {p : ℕ} (hp : p.Prime) (ψ : G →* G')
    (hψ : Function.Surjective ψ) (hker : Nat.Coprime p (Nat.card ψ.ker)) {L : Subgroup G}
    (hL : GLAPComponent p ⊤ L) : GLAPComponent p ⊤ (L.map ψ) := by
  have hk : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup G) ⊓ ψ.ker)) := by
    rwa [top_inf_eq]
  have h1 := glaPComponent_map hp ψ hk hL
  rwa [Subgroup.map_top_of_surjective ψ hψ] at h1

omit [Finite G] in
theorem i116red_map_gLBConj (ψ : G →* G') (y : G) (L : Subgroup G) :
    (GLBConj y L).map ψ = GLBConj (ψ y) (L.map ψ) := by
  unfold GLBConj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

omit [Finite G] in
theorem i116red_gLBConj_top (y : G) : GLBConj y (⊤ : Subgroup G) = ⊤ := by
  unfold GLBConj
  exact Subgroup.map_top_of_surjective _ (MulAut.conj y⁻¹).surjective

end

theorem i116red_pRank_le {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) {B : Subgroup X} (hB : IsPGroup p B) :
    CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (B.map (QuotientGroup.mk' N)) := by
  have : Fact p.Prime := ⟨hp⟩
  set f : B →* X ⧸ N := (QuotientGroup.mk' N).comp B.subtype with hf
  have hfi : Function.Injective f := by
    obtain ⟨k, hk⟩ := hB.exists_card_eq
    have hcop : Nat.Coprime (Nat.card B) (Nat.card N) := by
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := B) (K := N) hcop
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have h1 : (s : X) ∈ B ⊓ N := ⟨s.2, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hrange : B.map (QuotientGroup.mk' N) = (⊤ : Subgroup B).map f := by
    rw [hf, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  rw [hrange, pRank_map_eq_of_injective hp.one_lt f hfi, ← pRank_eq_pRank_top_subtype hp.one_lt]

theorem input11_6_of_reduced : Input11_6Reduced → Input11_6 := by
  intro red X _ _ hK p hp hp2 B hB hrank Y hY hBY L hL
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup X := GLAPPrimeCore p X with hNdef
  set ψ : X →* X ⧸ N := QuotientGroup.mk' N with hψdef
  have hNc : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hN : ¬ p ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hp).1 hNc
  have hker : Nat.Coprime p (Nat.card ψ.ker) := by
    rwa [hψdef, QuotientGroup.ker_mk']
  have hcore : GLAPPrimeCore p (X ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hKQ : CFSG.Open.IsKGroup (X ⧸ N) := isKGroup_quotient' hK N
  have hBp : IsPGroup p B := by
    have := hB.2.1
    exact fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2.1.2 g.1 g.2)⟩
  have hSC : IsSCp (G := X ⧸ N) p ⊤ (B.map ψ) := isSCp_map_quotient N hN hB
  have hrankQ : GLATwoLocalRank p (X ⧸ N) ≤ CFSG.Open.pRank p (B.map ψ) :=
    ((glaTwoLocalRank_quotient_le hp hp2 N hN).trans hrank).trans
      (i116red_pRank_le hp N hN hBp)
  have hYcop : Nat.Coprime p (Nat.card (Y.map ψ)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ ψ) hY
  have hBYQ : B.map ψ ≤ Subgroup.normalizer ((Y.map ψ : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    (Subgroup.map_mono hBY).trans (Subgroup.le_normalizer_map ψ)
  have hLQ : GLAPComponent p (⊤ : Subgroup (X ⧸ N)) (L.map ψ) :=
    i116red_map_component hp ψ (QuotientGroup.mk'_surjective N) hker hL
  have hmain := red (X ⧸ N) hKQ p hp hp2 hcore (B.map ψ) hSC hrankQ (Y.map ψ) hYcop hBYQ
    (L.map ψ) hLQ
  intro y hy
  rw [mem_normalizer_iff_gLBConj_eq]
  have hker' : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup X) ⊓ ψ.ker)) := by
    rwa [top_inf_eq]
  have hcomp : GLAPComponent p ⊤ (GLBConj y L) := by
    have := glaPComponent_gLBConj hL y
    rwa [i116red_gLBConj_top] at this
  refine i116red_unique hp ψ hker' hcomp hL ?_
  rw [i116red_map_gLBConj]
  exact mem_normalizer_iff_gLBConj_eq.1 (hmain ⟨y, hy, rfl⟩)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
