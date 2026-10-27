module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HI3C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HP2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_i3_proved : Asc82Sec8I3 := by
  intro G _ _ L S hL hS ⟨y, α, hy⟩
  have key : ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (_ : FiniteDimensional (ZMod 3) V) (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x₀ : ProjSim Q),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧
        InducesViaP L (Subgroup.center ↥L) hQ e y x₀ ∧
        ∃ α₀ : ℤˣ, SimHasType x₀ 1 α₀ ∨ SimHasType x₀ 3 α₀ := by
    rcases hy with ⟨V, i1, i2, i3, Q, hQ, e, x₀, hdim, hsgn, hind, hsim⟩ |
      ⟨V, i1, i2, i3, Q, hQ, e, x₀, hdim, hsgn, hind, hsim⟩
    · exact ⟨V, i1, i2, i3, Q, hQ, e, x₀, hdim, hsgn, hind, α, Or.inl hsim⟩
    · exact ⟨V, i1, i2, i3, Q, hQ, e, x₀, hdim, hsgn, hind, α, Or.inr hsim⟩
  obtain ⟨V, i1, i2, i3, Q, hQ, e, x₀, hdim, hsgn, hind, α₀, hsim⟩ := key
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6m_odd_center hL
  let θ := ffTheta6M hQ hdim hsgn e
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hind.1
  have hθy : θ ⟨y, hyN⟩ = x₀ :=
    (ffTheta_eq_iff hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨y, hyN⟩ x₀).mpr hind
  have hsq : x₀ * x₀ = 1 := by
    rcases hsim with h | h
    · exact simHasType_sq h
    · exact simHasType_sq h
  obtain ⟨m', ⟨a, hm'a⟩, hθm'⟩ :=
    sec8t84h_exists_two_part θ ⟨y, hyN⟩ (by rw [hθy]; exact hsq)
  have hm'G : (m' : G) ^ 2 ^ a = 1 := by
    have h := congrArg (fun z : ↥(Subgroup.normalizer (L : Set G)) => (z : G)) hm'a
    simpa using h
  have hK2 : IsPGroup 2 (Subgroup.zpowers (m' : G)) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := a) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hm'G)
  have hKN : Subgroup.zpowers (m' : G) ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr m'.2
  obtain ⟨g, hgN, hg⟩ := sec8t84h_exists_conj_into_sylow2 hS hKN hK2
  let y' : G := g * (m' : G) * g⁻¹
  have hy'S : y' ∈ S := hg (m' : G) (Subgroup.mem_zpowers (m' : G))
  have hsub : (⟨y', hS.1 hy'S⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨g, hgN⟩ * m' * ⟨g, hgN⟩⁻¹ := by
    apply Subtype.ext
    rfl
  have hθy' : θ ⟨y', hS.1 hy'S⟩ = θ ⟨g, hgN⟩ * x₀ * (θ ⟨g, hgN⟩)⁻¹ := by
    rw [hsub, map_mul, map_mul, map_inv, hθm', hθy]
  have hty : ∃ α' : ℤˣ, SimHasType (θ ⟨y', hS.1 hy'S⟩) 1 α' ∨
      SimHasType (θ ⟨y', hS.1 hy'S⟩) 3 α' := by
    rcases hsim with h | h
    · obtain ⟨α', hα'⟩ := sec8t84h_simHasType_conj hQ h (θ ⟨g, hgN⟩)
      exact ⟨α', Or.inl (by rw [hθy']; exact hα')⟩
    · obtain ⟨α', hα'⟩ := sec8t84h_simHasType_conj hQ h (θ ⟨g, hgN⟩)
      exact ⟨α', Or.inr (by rw [hθy']; exact hα')⟩
  exact sec8t84h_i3_core hQ hdim hsgn e hodd hS hy'S rfl hty

end CFSG.OddStandard.SmallF3.Omega
