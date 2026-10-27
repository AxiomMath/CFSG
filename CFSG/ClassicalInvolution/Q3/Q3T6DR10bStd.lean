module

public import CFSG.ClassicalInvolution.Q3.Q3T6D9A
public import CFSG.ClassicalInvolution.Q3.Q3T6DSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open scoped commutatorElement Pointwise

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.r9_cStar_S (d : Std20Three K K' J S R R' W V z t) (c8 : Concl20_8 S K' R) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') {y : G} (hy : y ∈ (S : Subgroup G))
    (hyc : y ∈ cStar K) : y ∈ R' := by
  have c8' : centralizerModOdd (S : Subgroup G) K' = R := c8
  have h1 : y ∈ centralizerModOdd (S : Subgroup G) K := by
    obtain ⟨-, hN, hNO, hcomm⟩ := (mem_centralizerModOdd_top_iff (L := K)).mpr hyc
    exact ⟨hy, hN, hNO, hcomm⟩
  have h2 := late_cmo_conj_mem h1 u
  rw [conjSub_eq_self_of_mem hu, huK, c8'] at h2
  have h3 : u * y * u⁻¹ ∈ K := d.hR.1 h2
  have hK' : conjSub u K' = K := (d.late_swap_data hu huK).1
  have h4 : conjSub u⁻¹ K = K' := by rw [← hK', conjSub_inv_conjSub]
  have h5 : y ∈ K' := by
    rw [← h4, mem_conjSub_iff]
    simpa using h3
  rw [d.late_R'_eq]
  exact ⟨h5, hy⟩

theorem Std20Three.r9_vdata (d : Std20Three K K' J S R R' W V z t) :
    ∃ v : G, V = Subgroup.zpowers v ∧ 2 * orderOf v = Nat.card R ∧
      v ∈ Subgroup.normalizer (K : Set G) := by
  have hΩ := d.late_hΩ
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨-, -, -, -, -, -, hVcyc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ d.hV
  obtain ⟨g, hg⟩ := hVcyc.exists_generator
  have hVeq : V = Subgroup.zpowers (g : G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      exact (Subgroup.zpowers_le (H := V)).mpr g.2 hx
  have hord : orderOf (g : G) = Nat.card V := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hc := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet hΩ d.hV hKΩ d.hR
  refine ⟨(g : G), hVeq, by rw [hord, hc], ?_⟩
  exact d.late_W_le_N_K (d.hVW g.2)

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
