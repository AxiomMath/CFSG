module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSDiagE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

structure SelComp (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B₀ T' : Subgroup Ω) (x : Ω)
    (J : Subgroup Ω) : Prop where
  comp : IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω))
  pdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)
  act : ⁅(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω), J⁆ ≠ ⊥
  inn : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
    J ⊔ (S ⊓ Subgroup.centralizer ({x} : Set Ω) ⊓ Subgroup.centralizer (J : Set Ω))
  chev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J)
  gf : p = 3 → ¬ GLAMarking (↥J) (fun lab _ _ _ _ _ => lab.n = 1)

@[expose] def T263SelW (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ → GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 →
    ∀ B₀ : Subgroup Ω, T263HasB0 p S B B₀ → T263Dich p S B →
    p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ →
    ∀ T' : Subgroup Ω, T' ≠ ⊥ → IsPGroup 2 T' → T' ≤ S → B ≤ Subgroup.normalizer (T' : Set Ω) →
    B ⊓ Subgroup.centralizer (T' : Set Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    ∀ x : Ω, x ∈ B₀ → x ∉ Subgroup.centralizer (S : Set Ω) →
    (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥ →
    T263GConcl p S B ∨ ∃ J : Subgroup Ω, SelComp p S B₀ T' x J

theorem t263DescSeed_of_selW {Q : TauCeti.CFSGIndex → Prop} (h : T263SelW Q) :
    T263DescSeed Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm
  rcases h p hp hp2 Ω hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm with hc | ⟨J, hJ⟩
  · exact Or.inl hc
  · right
    obtain ⟨hBel, -, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
        ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
    have hB₀B : B₀ ≤ B := hB₀.1
    have hJo : CFSG.Open.IsQuasisimple ↥J := hJ.comp.2.2
    have hJn : CFSG.IsQuasisimple ↥J := native_of_open_dx hJo
    have hJX : J ≤ S ⊓ Subgroup.centralizer ({x} : Set Ω) := hJ.comp.1
    obtain ⟨hBX, hBP, hPT'⟩ :=
      norm_data_dx hSn (fun a ha b hb => isElemAbelian_commute hBel ha hb) hB₀B hxB₀ hBT'
    have hPX : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
        S ⊓ Subgroup.centralizer ({x} : Set Ω) := hJ.inn.trans (sup_le hJX inf_le_left)
    obtain ⟨W, hWJ, hW2, hWB, hWC⟩ := exists_two_of_act_open hJX hJo (hT'2.to_le hPT') hPX
      hJ.inn hJ.act (inf_le_left.trans hBX) inf_le_right (inf_le_left.trans hBP)
    refine ⟨J, W, glaPComponent_of_isComponentOf_of_dvd hp hJ.comp hJ.pdvd,
      open_of_native_dx (isQuasisimple_pQuot_of_dvd hp hJn hJ.pdvd), ?_, ?_, hWJ, hW2, hWB,
      fun h => hWC ((h.trans (glaPPrimeCoreOf_le_centralizer_of_dvd hp hJn hJ.pdvd)).trans
        inf_le_right)⟩
    · obtain ⟨ε⟩ := nonempty_pSimple_equiv_of_dvd hp hJn hJ.pdvd
      exact isChevSimple_of_equiv ε.symm hJ.chev
    · intro h3 hm
      subst h3
      exact hJ.gf rfl (glaMarking_of_pQuot hp hJn hJ.pdvd (fun lab => lab.n = 1) hm)

theorem t263Desc_of_selW {Q : TauCeti.CFSGIndex → Prop} (h : T263SelW Q) : T263Desc Q :=
  t263Desc_of_seed_proved (t263DescSeed_of_selW h)

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
