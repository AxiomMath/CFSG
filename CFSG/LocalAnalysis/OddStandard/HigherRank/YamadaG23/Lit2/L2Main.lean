module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitHat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitCaseOut
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitCaseData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Filter
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Small
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Form
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Quot
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Pauli
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Cases
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Transport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three
open scoped commutatorElement

private lemma l2_dvd_360 {Q : Subgroup (Equiv.Perm (Fin 6))}
    (h : Q = alternatingGroup (Fin 6) ∨ Q = ⊤) : 360 ∣ Nat.card ↥Q := by
  rcases h with rfl | rfl
  · rw [lit_card_alt6]
  · rw [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem lit2_main {X : Type} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal] (h : LitCtx Z A)
    (hnab : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z)
    (hO : ∀ a ∈ A, ∀ x ∈ CFSG.oddCore X, x * a = a * x)
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x) (hτZ : ∀ x ∈ Z, τ x ∈ Z)
    (hTs : Group.IsSolvable ↥(litTSub τ Z)) (h72 : 72 ∣ (litP Z).relIndex (litTSub τ Z))
    (hz : ∃ z ∈ Z, τ z ≠ z) (h4 : ∃ z ∈ Z, orderOf z = 4)
    (hcat : ∀ H : Subgroup X, CFSG.IsQuasisimple ↥H →
      CFSG.Blueprint.Catalog (↥H ⧸ center ↥H))
    (hT : L2Tables) (hI : GomiOuterPSLU4 ∧ GomiOuterM22) (hLS : L2NoPauliPSL) (hUS : L2NoPauliPSU)
    (hOS : L2NoPauliPOmega) :
    ∃ H : Subgroup X, H.Characteristic ∧ CFSG.IsQuasisimple ↥H ∧ Z ≤ H ∧
      centralizer (H : Set X) = litP Z ∧ IsSU43 (↥H ⧸ CFSG.oddCore ↥H) := by
  classical
  haveI : (litP Z).Normal := Subgroup.sup_normal Z (CFSG.oddCore X)
  let π : X →* X ⧸ litP Z := QuotientGroup.mk' (litP Z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (litP Z)
  have hk : π.ker = litP Z := QuotientGroup.ker_mk' (litP Z)
  haveI : Finite (X ⧸ litP Z) := Finite.of_surjective π hπ
  have hZmap : Z.map (τ : X →* X) = Z := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      exact hτZ x hx
    · intro x hx
      exact ⟨τ x, hτZ x hx, hτ x⟩
  have hOmap : (CFSG.oddCore X).map (τ : X →* X) = CFSG.oddCore X :=
    (Subgroup.characteristic_iff_map_eq.mp (lit_oddCore_characteristic X)) τ
  have hPmap : (litP Z).map (τ : X →* X) = litP Z := by
    unfold litP
    rw [Subgroup.map_sup, hZmap, hOmap]
  let σ : X ⧸ litP Z ≃* X ⧸ litP Z := QuotientGroup.congr (litP Z) (litP Z) τ hPmap
  have hσ : ∀ x, σ (π x) = π (τ x) :=
    fun x => QuotientGroup.congr_mk' (litP Z) (litP Z) τ hPmap x
  let d : LitTData π Z τ σ :=
    { surj := hπ, ker := hk, invol := hτ, Z_inv := hτZ, comm := hσ }
  obtain ⟨φ', hbar, _hφ'⟩ := lit_bar h hπ hk φ hφs hφk
  obtain ⟨M, hmono, hA6⟩ := lit_monoData hbar
  obtain ⟨hHM, hcent, hZH⟩ := lit_hat h hnab φ hφs hφk hO hπ hk hmono
  have hperf : ⁅litPerf (M.comap π), litPerf (M.comap π)⁆ = litPerf (M.comap π) :=
    litPerf_perfect (M.comap π)
  have hsolv : Group.IsSolvable ↥π.ker := by
    rw [hk]
    exact lit_solvable_litP h.central
  haveI : M.Normal := hmono.normal
  have hchar : (litPerf (M.comap π)).Characteristic :=
    lit_perf_char hπ hsolv hmono.simple hmono.nonab hmono.min
  have hq : CFSG.IsQuasisimple ↥(litPerf (M.comap π)) :=
    lit_quasisimple hmono.simple hmono.nonab hperf hHM hcent
  have hC : centralizer (litPerf (M.comap π) : Set X) = litP Z :=
    (lit_centralizer_H hmono.cent hHM hcent).trans hk
  have hτH : ∀ x, x ∈ litPerf (M.comap π) ↔ τ x ∈ litPerf (M.comap π) := by
    intro x
    have hfix : (litPerf (M.comap π)).comap (τ : X →* X) = litPerf (M.comap π) :=
      hchar.fixed τ
    have h1 : x ∈ (litPerf (M.comap π)).comap (τ : X →* X) ↔
        x ∈ litPerf (M.comap π) := by
      rw [hfix]
    rw [Subgroup.mem_comap] at h1
    exact h1.symm
  refine ⟨litPerf (M.comap π), hchar, hq, hZH, hC, ?_⟩
  have hE := lit_isE_bar (B := A) (π := π) h hk
  have h72' : 72 ∣ Nat.card ↥((litTSub τ Z).map π) := by
    rw [← Subgroup.relIndex_ker π (K := litTSub τ Z), hk]
    exact h72
  obtain ⟨z, hzZ, hz_ne⟩ := hz
  have hzH : z ∈ litPerf (M.comap π) := hZH hzZ
  have hfour : ∀ w ∈ Z, w ^ 4 = 1 := by
    intro w hw
    simpa [h.card_Z] using
      congrArg (fun v : ↥Z => (v : X)) (pow_card_eq_one' (x := (⟨w, hw⟩ : ↥Z)))
  have hz2 : ∃ k : ℕ, z ^ 2 ^ k = 1 :=
    ⟨2, by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hfour z hzZ⟩
  have hσne : ∃ x, σ x ≠ x :=
    lit_sigma_nontriv d hperf (fun x hx => (hτH x).mp hx) hcent hzH hz_ne
  obtain ⟨ρ, hρs, _hρcoe, hρker⟩ := lit_H_hom hmono.simple hmono.nonab hHM hcent
  let e₁ : ↥(litPerf (M.comap π)) ⧸ ρ.ker ≃* ↥M := QuotientGroup.quotientKerEquivOfSurjective ρ hρs
  let e : ↥(litPerf (M.comap π)) ⧸ center ↥(litPerf (M.comap π)) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans e₁
  have hz4 : ∃ w ∈ center ↥(litPerf (M.comap π)), orderOf w = 4 := by
    obtain ⟨z4, hz4Z, hz4⟩ := h4
    refine ⟨⟨z4, hZH hz4Z⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (h.central z4 hz4Z (y : X)).symm
    · rw [Subgroup.orderOf_mk]
      exact hz4
  have hZM : L2Z4Type ↥M :=
    l2z4_of_mulEquiv e.symm (l2_filter hT hq (hcat _ hq) hz4)
  have hsetup : L2Setup Z A π M (litPerf (M.comap π)) :=
    { surj := hπ, ker := hk, central := h.central, four := hfour, Z_le_A := h.Z_le_A,
      Z_le_H := hZH, simple := hmono.simple, nonab := hmono.nonab, perf := hperf,
      map_H := hHM, cent := hcent, A_le := hmono.A_le }
  obtain ⟨ρ', hρ's, hq', hker', h2', hcomp⟩ := l2_quot hsetup
  have hpauli := l2_pauli hsetup (l2_form h hnab φ hφs hφk h4) hcomp
  have hsylM := lit_sylow_M hbar hmono.A_le
  rcases l2_cases hLS hUS hOS ρ' _ hρ's hq' hker' h2' (l2_E_sub hmono.A_le hE) hpauli
      (l2_sylow_top hmono.A_le hsylM) hZM with hM22 | hL34 | hPSLU
  · exact (lit_caseM22 hI.2 d hM22 hmono.cent h72' hσne).elim
  · refine (l2_not_L34 (lit_quotIso_M hbar M) hE hsylM.1
      (l2_dvd_360 (lit_image_cases hA6)) hL34).elim
  · exact lit_casePSLU hI.1 d h.central hTs hmono.simple hmono.nonab hPSLU hq hHM hcent hτH hzZ
      hzH hz2 hz_ne

end CFSG.OddStandard.HigherRank.YamadaG23
