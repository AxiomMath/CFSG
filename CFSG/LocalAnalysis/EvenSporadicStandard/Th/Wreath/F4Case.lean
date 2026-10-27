module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SemilinearConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.EndOnA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.F4Exclusion

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private theorem conj_conj_eq_of_isRep_one_add_single {c : G → (Fin 4 → ZMod 2)}
    (hc : IsCoord A c) {s : G} (hs : ∀ a ∈ A, s * a * s⁻¹ ∈ A)
    (hM : IsRep A c s (1 + Matrix.single 0 3 1)) (a : G) (ha : a ∈ A) :
    s * (s * a * s⁻¹) * s⁻¹ = a := by
  have hMM : ((1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single 0 3 1) *
      (1 + Matrix.single 0 3 1) = 1 := by decide
  have h2 := hM.mul hM hs
  rw [hMM] at h2
  have e : s * (s * a * s⁻¹) * s⁻¹ = s * s * a * (s * s)⁻¹ := by group
  rw [e]
  refine hc.inj _ ?_ _ ha (by rw [h2 a ha, Matrix.one_mulVec])
  rw [← e]
  exact hs _ (hs a ha)

theorem ThCyc.false_of_F4_case (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (F : SylowFacts L S B Aa) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {Q T : Subgroup G}
    (hQ : QHyp L A D t Q) (hT : THyp S D Q t T) (hq4 : ∀ q ∈ Q, q ^ 4 = 1)
    (hsq : ∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) {g : G}
    (hgT : g ∈ normalizer (T : Set G)) (hgQ : g ∈ normalizer (Q : Set G))
    (hgM : g ∉ normalizer (D : Set G)) {w : AddMonoid.End (VSub hD)} (hgw : g ∈ wComm hD w)
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hτw : vConj hD t * w * vConj hD t = w + 1) (hβ : phiQ hD Q b = 1)
    (hΦ : ∀ c ∈ normalizer (Q : Set G) ⊓ centralizer (omega1 D hD.comm : Set G),
      phiQ hD Q c = 0 ∨ phiQ hD Q c = 1 ∨ phiQ hD Q c = w ∨ phiQ hD Q c = w + 1)
    (hw2 : w * w = w + 1) : False := by
  obtain ⟨c, hc, hS, hsurj⟩ := W.exists_coord_unitriangular
  obtain ⟨s₀, hs₀S, hu, hcomm, hne⟩ :=
    H.exists_conj_t_eq_t_mul W W2 hD h4 hb hc hsurj hQ hT hgT hgQ hgM hwH hτw hgw.2
  have hM : IsRep A c s₀ (1 + Matrix.single 0 3 1) :=
    W.isRep_of_central hc hS hsurj hs₀S
      (fun s hs a ha => hcomm s hs a (H.A_le_omega1 W W2 hD ha)) hne
  have hs₀A : ∀ a ∈ A, s₀ * a * s₀⁻¹ ∈ A := fun a ha => W.conj_mem_A_of_mem_S hs₀S ha
  have hs₀H : s₀ ∈ L ⊓ normalizer (A : Set G) :=
    ⟨W.S_le hs₀S, le_normalizer_of_conj_mem (N := S) (D := A)
      (fun s hs a ha => W.conj_mem_A_of_mem_S hs ha) hs₀S⟩
  have hx := H.exists_mem_vConj_eq_one_add_w W W2 hD hwH hτw hQ hgQ hgw.2 hs₀H
    (conj_conj_eq_of_isRep_one_add_single hc hs₀A hM) hu
  exact H.false_of_F4 W W2 F hD hb hQ hq4 hsq hwH hw2 hΦ hβ hc hS hsurj
    (fun f f' hf hf' h => H.end_eq_of_commute_of_eq_on_A W W2 hD hτw hf hf' h) hs₀S hM hx

end CFSG.EvenSporadicStandard.ThStd
