module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalOddMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreHyp

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

namespace Sec5Ctx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {N A : Subgroup X} {M : AhatModel X n A}

theorem isDoubleCover_of_even (h : Sec5Ctx X n z N A M)
    (heven : ∀ (c : X) (hc : c ∈ N), sign (h.psi ⟨c, hc⟩) = 1)
    (hA : IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n) :
    IsDoubleCoverOfAlt (↥N ⧸ pPrimeCore 2 ↥N) n := by
  obtain ⟨e⟩ := quotOddCore_equiv h.hAN h.hNA (fun c hc => by
    obtain ⟨a, ha, o, ho, hc'⟩ := h.exists_decomp hc (heven c hc)
    exact ⟨a, ha, o, ho, hc'⟩)
  exact isDoubleCoverOfAlt_congr' e hA

end Sec5Ctx

theorem sec5_main (hF : Solomon75Frac53) {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
    (hAB : AlternatingBalanceData n)
    {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}
    (h : Sec5Data X n z (zpowers z) S) (h1 : Sec5One X n (zpowers z))
    (hQ : centralizer ({z} : Set X) ⊓ QOf (K0 X n (centralizer ({z} : Set X))) =
      oddCoreOf (centralizer ({z} : Set X)) ⊔ zpowers z)
    {s₁ x : X} (hs₁S : s₁ ∈ Sec5Syl S) (hxS : x ∈ Sec5Syl S) (hs₁2 : orderOf s₁ = 2)
    (hs₁Z : s₁ ∉ zpowers z) (hs₁c : ∃ g : X, g⁻¹ * z * g = s₁) (hxx : x * x = s₁) :
    IsDoubleCoverOfAlt (↥(centralizer ({z} : Set X)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set X)))
      n := by
  have hz := h.orderOf_z
  have hNC : normalizer ((zpowers z : Subgroup X) : Set X) = centralizer ({z} : Set X) :=
    normalizer_zpowers_eq_centralizer hz
  obtain ⟨A, hA, -⟩ := h.exists_comp
  have hKA : K0 X n (normalizer ((zpowers z : Subgroup X) : Set X)) = A :=
    K0_eq_of_sec5Comp_unique h1 hA
  have hAN : A ≤ normalizer ((zpowers z : Subgroup X) : Set X) := hKA ▸ K0_le n _
  have hNA : normalizer ((zpowers z : Subgroup X) : Set X) ≤ normalizer (A : Set X) :=
    hKA ▸ Sec5Data.le_normalizer_K0 X n _
  have hzA : z ∈ A := hKA ▸ h.z_mem_K0
  have hn : 8 ≤ n := h.maxdeg.1
  let M : AhatModel X n A := ⟨↥A ⧸ pPrimeCore 2 ↥A, MulEquiv.refl _,
    AhatData.CoverSetup.ofCover hA.2⟩
  have hNz : ∀ c ∈ normalizer ((zpowers z : Subgroup X) : Set X), z * c = c * z := fun c hc => by
    have : c ∈ centralizer ({z} : Set X) := by rw [← hNC]; exact hc
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hQ' : normalizer ((zpowers z : Subgroup X) : Set X) ⊓ QOf A =
      oddCoreOf (normalizer ((zpowers z : Subgroup X) : Set X)) ⊔ zpowers z := by
    rw [hNC, ← hKA, hNC]
    exact hQ
  have hctx : Sec5Ctx X n z (normalizer ((zpowers z : Subgroup X) : Set X)) A M :=
    ⟨hn, hz, hNz, hAN, hNA, hzA, fun c hc h1 => by
      have h2 : c ∈ QOf A := mem_QOf_iff.2 ⟨hNA hc, (M.perm_eq_one_iff hn _).1 h1⟩
      rw [← hQ']
      exact ⟨hc, h2⟩⟩
  rw [← hNC]
  by_cases heven : ∀ (c : X) (hc : c ∈ normalizer ((zpowers z : Subgroup X) : Set X)),
      sign (hctx.psi ⟨c, hc⟩) = 1
  · exact hctx.isDoubleCover_of_even heven hA.2
  · exfalso
    push Not at heven
    obtain ⟨t, htN, ht⟩ := heven
    have hodd : sign (hctx.psi ⟨t, htN⟩) = -1 := by
      rcases Int.units_eq_one_or (sign (hctx.psi ⟨t, htN⟩)) with h2 | h2
      · exact absurd h2 ht
      · exact h2
    have : Finite M.K := inferInstanceAs (Finite (↥A ⧸ pPrimeCore 2 ↥A))
    refine hctx.odd_false (fun u v hu hv hu' hv' => hAB.one_class M.K M.C.hX u v hu hv hu' hv')
      h.cex.simple h.cex.nonabelian S h.l52.d hs₁S hxS hs₁2
      (fun h2 => hs₁Z (h2 ▸ Subgroup.mem_zpowers z)) hs₁c hxx ?_ htN hodd
    intro t' ht'N ht'2 ht'1 ht'z hconj
    have hsec : IsSec5Inv X (zpowers z) t' :=
      ⟨ht'N, fun h2 => by
          rcases (mem_zpowers_iff_of_orderOf_two hz).1 h2 with h3 | h3
          · exact ht'1 h3
          · exact ht'z h3,
        ht'2, by
          obtain ⟨g, hg⟩ := hconj
          refine ⟨g⁻¹, ?_, ?_⟩
          · have : g⁻¹⁻¹ * t' * g⁻¹ = z := by rw [← hg]; group
            rw [this]; exact Subgroup.mem_zpowers z
          · have : g⁻¹⁻¹ * t' * g⁻¹ = z := by rw [← hg]; group
            rw [this]
            intro h3
            rw [h3, orderOf_one] at hz
            exact absurd hz (by norm_num)⟩
    exact ⟨(hF X n z (zpowers z) S h t' hsec).1 A hA (hNA ht'N) M |>.1,
      (hF X n z (zpowers z) S h t' hsec).1 A hA (hNA ht'N) M |>.2⟩

theorem thm310 (hF : Solomon75Frac53) (h55 : Solomon75Lemma55) (h56 : Solomon75Cor56)
    (h57 : Solomon75Lemma57) (h58 : Solomon75Lemma58)
    (hAB : ∀ m : ℕ, 8 ≤ m → m ≤ 11 → AlternatingBalanceData m)
    {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
    {S : Sylow 2 ↥(normalizer (Z : Set X))} (h : Sec5Data X n z Z S) :
    IsDoubleCoverOfAlt (↥(centralizer ({z} : Set X)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set X)))
      n ∧ 8 ≤ n ∧ n ≤ 11 := by
  have h1 : Sec5One X n Z := h55 X n z Z S h
  obtain ⟨hZ, s₁, x, hs₁S, hxS, hs₁2, hs₁Z, hs₁c, hxx⟩ := h56 X n z Z S h h1
  have hn11 : n ≤ 11 := h58 X n z Z S h h1 hZ
  obtain ⟨hQ, -⟩ := h57 X n z Z S h h1 hZ
  refine ⟨?_, h.maxdeg.1, hn11⟩
  subst hZ
  exact sec5_main hF (hAB n h.maxdeg.1 hn11) h h1 hQ hs₁S hxS hs₁2 hs₁Z hs₁c hxx

end CFSG.OddStandard.Solomon75
