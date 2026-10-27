module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EA173
public import CFSG.ClassicalInvolution.Asc77.AscE186Thm2A

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E.Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.AscE186 (perfect_centralizes_of_centralizes_cent)
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_centralizer_of_normal_two (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {N : Subgroup G} [N.Normal] (hN2 : IsPGroup 2 ↥N)
    (hzN : z ∈ N) : K ≤ Subgroup.centralizer (N : Set G) := by
  have hzc : ∀ k ∈ K, k * z = z * k := fun k hk => (hz.commute_of_mem hk).symm
  have hperf : Group.IsPerfect ↥K := by
    obtain ⟨z', hz'⟩ := hΩ.classical K hK
    exact hz'.perfect Uniform.MemberType.not_isSolvableType_twoA7
  rcases AscThmA.le_or_commutator_le_oddCoreOf hΩ hK hz N with hKN | hcomm
  ·
    exfalso
    have hK2 : IsPGroup 2 ↥K := hN2.to_le hKN
    have : Nontrivial ↥K := ⟨⟨⟨z, hz.mem⟩, 1, fun h => hz.ne_one (congrArg Subtype.val h)⟩⟩
    have : Group.IsNilpotent ↥K := hK2.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  have hcent : ∀ k ∈ K, ∀ x ∈ N, x * z = z * x → k * x = x * k := by
    intro k hk x hxN hxz
    have h1 : ⁅k, x⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
      hcomm (Subgroup.commutator_mem_commutator hk
        ⟨hxN, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩)
    have h2 : ⁅k, x⁆ ∈ N := by
      have e : ⁅k, x⁆ = (k * x * k⁻¹) * x⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact N.mul_mem (‹N.Normal›.conj_mem x hxN k) (N.inv_mem hxN)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅k, x⁆) := hN2.to_le (Subgroup.zpowers_le.mpr h2)
    have h4 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1 h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h4
  have hKN : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N := fun k _ x hx => ‹N.Normal›.conj_mem x hx k
  have := perfect_centralizes_of_centralizes_cent hperf hz.mem hzc (Nat.card N) N rfl hN2 hzN hKN
    hcent
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (this k hk x hx).symm

theorem thm2 : Thm2 := by
  intro G _ _ Ω hΩ _ hgen K hK htrans z hz hN
  obtain ⟨N, hNn, hN2, hzN⟩ := hN
  have hnorm : ∀ J ∈ Ω, J ≤ Subgroup.normalizer (K : Set G) := by
    intro J hJ
    by_cases hJK : J = K
    · rw [hJK]
      exact Subgroup.le_normalizer
    obtain ⟨g, rfl⟩ := htrans J hJ
    have hzJ : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
    have hzJN : g * z * g⁻¹ ∈ N := hNn.conj_mem z hzN g
    have hcentN := le_centralizer_of_normal_two hΩ hJ hzJ hN2 hzJN
    have hJc : conjSub g K ≤ Subgroup.centralizer ({z} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hcentN hj) z hzN).symm
    refine hΩ.le_of_forall_isSylow2In hJ (M := Subgroup.normalizer (K : Set G)) fun V hV => ?_
    have h8 := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJ hV)
    exact hΩ.le_normalizer_of_le_centralizer hK hJ (fun h => hJK h.symm) hz hV.1 hV.2.1
      (by omega) (hV.1.trans hJc)
  have : Subgroup.normalizer (K : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le hnorm
  exact Subgroup.normalizer_eq_top_iff.mp this

end CFSG.ClassicalInvolution.Hat2A7E.Asc77.AscE186
