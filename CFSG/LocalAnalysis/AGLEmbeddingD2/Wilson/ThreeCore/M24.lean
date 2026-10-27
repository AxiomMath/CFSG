
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Base

public import Certificates.Certificate12613

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.RankThree.LocalRank CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem m24ThreeSpec :
    closure (tp 24 '' {x | x ∈ ([wT s1W, wT s2W] : List Table).toArray}) ≤ NativeSporadic.M24 ∧
      Nat.card ↥(closure (tp 24 '' {x | x ∈ ([wT s1W, wT s2W] : List Table).toArray})) = 27 ∧
      (∀ r ∈ [m24Row3A, m24Row3B], tp 24 r.rep ∈ NativeSporadic.M24 ∧
        orderOf (tp 24 r.rep) = 3 ∧
        Nat.card ↥(NativeSporadic.M24 ⊓
          centralizer ({tp 24 r.rep} : Set (Equiv.Perm (Fin 24)))) = r.centOrder ∧
        aschbacherSolvableCore 3
          ↥(NativeSporadic.M24 ⊓ centralizer ({tp 24 r.rep} : Set (Equiv.Perm (Fin 24)))) = ⊥) ∧
      (∀ t ∈ NativeSporadic.M24, orderOf t = 3 →
        ∃ r ∈ [m24Row3A, m24Row3B], ∃ g ∈ NativeSporadic.M24, t = g * tp 24 r.rep * g⁻¹) ∧
      (∀ t ∈ NativeSporadic.M24, orderOf t = 3 →
        aschbacherSolvableCore 3
          ↥(NativeSporadic.M24 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 24)))) = ⊥) ∧
      closure (tp 24 '' {x | x ∈ m24Row3A.centGens.toArray}) =
        NativeSporadic.M24 ⊓ centralizer ({tp 24 m24Row3A.rep} : Set (Equiv.Perm (Fin 24))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hconj, ⟨hSP, hScard⟩, ⟨hgA, hA⟩, hB⟩ := Certificates.certificate12613
  have eA : tp 24 m24Row3A.rep = wordG letG xW := tp_wT xW
  have eB : tp 24 m24Row3B.rep = wordG letG x2W := tp_wT x2W
  have gA : tp 24 '' {x | x ∈ m24Row3A.centGens.toArray} = {wordG letG ca1W, wordG letG ca2W} :=
    tp_image_pair ca1W ca2W
  have hrows : ∀ r ∈ [m24Row3A, m24Row3B], tp 24 r.rep ∈ NativeSporadic.M24 ∧
      orderOf (tp 24 r.rep) = 3 ∧
      Nat.card ↥(NativeSporadic.M24 ⊓
        centralizer ({tp 24 r.rep} : Set (Equiv.Perm (Fin 24)))) = r.centOrder ∧
      aschbacherSolvableCore 3
        ↥(NativeSporadic.M24 ⊓ centralizer ({tp 24 r.rep} : Set (Equiv.Perm (Fin 24)))) = ⊥ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [eA]
      exact ⟨wordG_mem _, orderOf_eq_prime xW_pow xW_ne, hA.1,
        theta_of_words _ [(ra0W, ha0W), (ra1W, ha1W), (ra2W, ha2W)] hA.2.1 hA.2.2⟩
    · rw [eB]
      exact ⟨wordG_mem _, orderOf_eq_prime x2W_pow x2W_ne, hB.1,
        theta_of_words _ [(rb0W, hb0W), (rb1W, hb1W), (rb2W, hb2W)] hB.2.1 hB.2.2⟩
  have hcover : ∀ t ∈ NativeSporadic.M24, orderOf t = 3 →
      ∃ r ∈ [m24Row3A, m24Row3B], ∃ g ∈ NativeSporadic.M24, t = g * tp 24 r.rep * g⁻¹ := by
    intro t ht ht3
    obtain ⟨g, hg, h | h⟩ := hconj t ht ht3
    · refine ⟨m24Row3A, by simp, g, hg, ?_⟩
      rw [eA]
      exact h
    · refine ⟨m24Row3B, by simp, g, hg, ?_⟩
      rw [eB]
      exact h
  rw [tp_image_pair s1W s2W, gA, eA]
  refine ⟨hSP, hScard, hrows, hcover, ?_, hgA⟩
  intro t ht ht3
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht3
  exact aschbacherSolvableCore_inf_centralizer_conj NativeSporadic.M24 hg (hrows r hr).2.2.2

theorem theta_m24_perm
    (t : Equiv.Perm (Fin 24)) (ht : t ∈ NativeSporadic.M24) (ht3 : orderOf t = 3) :
    aschbacherSolvableCore 3
      ↥(NativeSporadic.M24 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 24)))) = ⊥ :=
  m24ThreeSpec.2.2.2.2.1 t ht ht3

theorem thetaCent_m24
    (b : NativeSporadic.M24) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set NativeSporadic.M24)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (b : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hb3 hb1
  exact aschbacherSolvableCore_centralizer_subtype b (theta_m24_perm b b.2 hord)

theorem thetaCent_of_m24
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .M24) (b : X)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set X)) = ⊥ := by
  let e' : X ≃* NativeSporadic.M24 := e
  rw [aschbacherSolvableCore_three_centralizer_eq_bot_iff e' b]
  refine thetaCent_m24 (e' b) (by rw [← map_pow, hb3, map_one]) fun h => hb1 ?_
  exact e'.injective (by rw [h, map_one])

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24
