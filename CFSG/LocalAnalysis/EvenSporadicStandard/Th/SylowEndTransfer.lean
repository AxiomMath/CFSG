module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.exists_conj_card_eq
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hSP : S ⊔ zpowers t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) :
    ∃ g : G, D ⊓ centralizer ({b} : Set G) ≤ centralizer ({g⁻¹ * t * g} : Set G) ∧
      g⁻¹ * t * g ∉ D ∧ Nat.card ↥(D ⊓ centralizer ({b} : Set G)) = 2 ^ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP' : S ≤ P := le_sup_left.trans hSP
  have htP : t ∈ P := hSP (mem_sup_right (mem_zpowers t))
  have hBpP : Bp A t ≤ P := H.Bp_le_of_le_normalizer W hP hPidx hPN
  have := H.simple
  have hG := not_exists_normal_index_two_of_nonabelian H.nonabelian
  obtain ⟨g, hgQ, hext, -⟩ := exists_extremal_conj_of_cyclic hG hP hPidx
    (fun p hp q hq => (mem_normalizer_iff.1
      (H.P_le_normalizer_sup W W2 hD hP hSP' hBpP hPN hp) q).1 hq)
    (H.exists_cyclic_sup W W2 hD hP hSP' hBpP hPN htP) htP (H.t_not_mem_sup W W2 hD) H.sq_t
  have huP : g⁻¹ * t * g ∈ P :=
    (sup_le ((H.D_le_Bp W W2 hD).trans hBpP) hSP' : D ⊔ S ≤ P) hgQ
  obtain ⟨hnD, hcard, -, -, d₁, hd₁, h | h | h⟩ :=
    H.ext_extremal W W2 hD hAb hZ hP hSP hBpP hPN hext huP
  · exfalso
    apply H.t_not_mem_sup W W2 hD
    have : t = d₁⁻¹ * (g⁻¹ * t * g) := by rw [h]; group
    rw [this]
    exact mul_mem (inv_mem (mem_sup_left hd₁)) hgQ
  · have hCeq := inf_centralizer_mul_eq hD.comm (v := b) hd₁
    refine ⟨g, ?_, hnD, ?_⟩
    · rw [h, ← hCeq]
      exact inf_le_right
    · rw [h, hCeq] at hcard
      exact hcard
  · exfalso
    apply H.t_not_mem_sup W W2 hD
    have hdb : d₁ * b ∈ D ⊔ S := mul_mem (mem_sup_left hd₁) (mem_sup_right (W.B_le_S W2.b_mem))
    have : t = (d₁ * b)⁻¹ * (g⁻¹ * t * g) := by rw [h]; group
    rw [this]
    exact mul_mem (inv_mem hdb) hgQ

end

end CFSG.EvenSporadicStandard.ThStd
