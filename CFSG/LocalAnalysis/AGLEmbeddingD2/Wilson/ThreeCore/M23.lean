
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23Base

public import Certificates.Certificate12641

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.RankThree.LocalRank CFSG.Blueprint

theorem m23_cover (t : Equiv.Perm (Fin 23))
    (ht : t ∈ NativeSporadic.M23) (ht3 : orderOf t = 3) :
    ∃ g ∈ NativeSporadic.M23, t = g * wordG letG xW * g⁻¹ :=
  Certificates.certificate12641.1 t ht ht3

theorem theta_m23_rep :
    aschbacherSolvableCore 3
      ↥(NativeSporadic.M23 ⊓ centralizer ({wordG letG xW} : Set (Equiv.Perm (Fin 23)))) = ⊥ := by
  obtain ⟨-, -, -, hcov, hwit⟩ := Certificates.certificate12641
  exact theta_of_words_m23 _ [(r0W, h0W), (r1W, h1W), (r2W, h2W)] hcov hwit

theorem theta_m23_perm
    (t : Equiv.Perm (Fin 23)) (ht : t ∈ NativeSporadic.M23) (ht3 : orderOf t = 3) :
    aschbacherSolvableCore 3
      ↥(NativeSporadic.M23 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 23)))) = ⊥ := by
  obtain ⟨g, hg, rfl⟩ := m23_cover t ht ht3
  exact aschbacherSolvableCore_inf_centralizer_conj NativeSporadic.M23 hg theta_m23_rep

theorem thetaCent_m23
    (b : NativeSporadic.M23) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set NativeSporadic.M23)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (b : Equiv.Perm (Fin 23)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hb3 hb1
  exact aschbacherSolvableCore_centralizer_subtype b (theta_m23_perm b b.2 hord)

theorem thetaCent_of_m23
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .M23) (b : X)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set X)) = ⊥ := by
  let e' : X ≃* NativeSporadic.M23 := e
  rw [aschbacherSolvableCore_three_centralizer_eq_bot_iff e' b]
  refine thetaCent_m23 (e' b) (by rw [← map_pow, hb3, map_one]) fun h => hb1 ?_
  exact e'.injective (by rw [h, map_one])

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23
