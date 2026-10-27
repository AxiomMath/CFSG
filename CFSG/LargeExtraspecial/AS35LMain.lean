module

public import CFSG.LargeExtraspecial.AS35LBridge
public import CFSG.LargeExtraspecial.AS35JFiveNineTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem eq_bot_of_normalized_L {N : Subgroup S.O} (hNM : N ≤ S.Mbar)
    (hN : S.Mbar ≤ normalizer (N : Set S.O)) (h2 : IsPGroup 2 N) : N = ⊥ := by
  set N' : Subgroup S.M := N.comap S.ρ with hN'
  have hnorm : N'.Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [hN', mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hN ⟨g, rfl⟩) (S.ρ y)).1 hy
  have hp : IsPGroup 2 N' := by
    intro y
    obtain ⟨a, ha⟩ := h2 ⟨S.ρ y, y.2⟩
    have h1 : S.ρ ((y : S.M) ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have hQ : (y : S.M) ^ 2 ^ a ∈ S.Q := S.mem_Q_of_ρ_eq_one h1
    obtain ⟨b, hb⟩ := S.extraspecial.1 ⟨_, hQ⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((y : S.M) ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    rw [Subgroup.coe_pow, pow_add, pow_mul, hb', Subgroup.coe_one]
  have hle := S.le_of_normal N' hnorm hp
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨g, rfl⟩ := hNM hn
  rw [mem_bot]
  exact S.ρ_eq_one_of_mem_Q (hle (show g ∈ N' from hn))

theorem conj_mem_DbarAsc_L {m : S.O} (hm : m ∈ S.Mbar) {d : S.O} (hd : d ∈ S.DbarAsc) :
    m * d * m⁻¹ ∈ S.DbarAsc := by
  obtain ⟨⟨m₀, hm₀⟩, rfl⟩ := hm
  obtain ⟨s, hs, hsM, rfl⟩ := hd
  refine ⟨m₀ * s * m₀⁻¹, S.conj_mem_DSet hm₀ hs,
    S.M.mul_mem (S.M.mul_mem hm₀ hsM) (S.M.inv_mem hm₀), ?_⟩
  have e : (⟨m₀ * s * m₀⁻¹, S.M.mul_mem (S.M.mul_mem hm₀ hsM) (S.M.inv_mem hm₀)⟩ : S.M) =
      ⟨m₀, hm₀⟩ * ⟨s, hsM⟩ * ⟨m₀, hm₀⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

theorem hyp_L (h65 : S.SixFiveConcl) {k : ℕ} (hk : S.width = k + 2) :
    AS35L.Hyp S.Mbar S.DbarAsc k where
  finite := inferInstance
  two_le := by have := h65.four_le_width; omega
  sub := by
    rintro _ ⟨t, -, htM, rfl⟩
    exact ⟨⟨t, htM⟩, rfl⟩
  conj m hm d hd := S.conj_mem_DbarAsc_L hm hd
  cls := h65.conj
  inv d hd := by
    obtain ⟨t, ht, htM, rfl⟩ := hd
    exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))
  three := h65.three
  psu := by
    obtain ⟨e⟩ := h65.psu
    rw [hk] at e
    exact ⟨e.trans (AS35U.pgEquiv (by have := h65.four_le_width; omega)).symm⟩
  core N hNM hN h2 := S.eq_bot_of_normalized_L hNM hN h2

theorem fiveNineHyp_L (h65 : S.SixFiveConcl) {t : G} (ht : t ∈ S.DSet)
    (htM : t ∈ S.M) {U : Subgroup S.O} (hUM : U ≤ S.Mbar) (hU2 : ∀ u ∈ U, u * u = 1)
    (htU : S.ρ ⟨t, htM⟩ ∈ U)
    (hUn : ∀ c ∈ S.Mbar, c * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) :
    U ≤ zpowers (S.ρ ⟨t, htM⟩) := by
  obtain ⟨k, hk⟩ : ∃ k, S.width = k + 2 := ⟨S.width - 2, by have := h65.four_le_width; omega⟩
  exact (S.hyp_L h65 hk).le_zpowers (S.ρ_mem_DbarAsc ht htM) hUM hU2 htU hUn

end Setting

namespace S14

theorem aschbacherFiveNineHypStmt : AschbacherFiveNineHypStmt :=
  fun _ _ _ S _ h65 _ ht htM _ hUM hU2 htU hUn => S.fiveNineHyp_L h65 ht htM hUM hU2 htU hUn

theorem aschbacherFiveNineTwoStmt : AschbacherFiveNineTwoStmt :=
  aschbacherFiveNineTwoStmt_of aschbacherFiveNineHypStmt

end S14

end CFSG.LargeExtraspecial
