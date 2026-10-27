module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryMono
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni

open CFSG.Open Subgroup Matrix
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_unitary_of_inputs odUZ mem_odUZ
  od_unitary_nonpower l212in_suConj l212in_suConj_coe l212in_suPhi l212in_suPhi_mk
  l212in_scalar_comm exists_cover_unitary card_scalars_statedSU i294ODUnitaryTorus_holds
  i294ODUnitaryMonomial_holds)

section Unitary

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem unitary_case (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZp : IsPGroup 5 (center ↥L))
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup 5 (Y ⧸ N) → N = ⊤)
    {x : Y} (hx : orderOf x = 5) (hx2 : CFSG.Open.pRank 5 (centralizer ({x} : Set Y)) ≤ 2)
    (hpn : 5 ∣ n) (hK : Nat.card K = (r ^ f) ^ 2) (hpq : 5 ∣ r ^ f + 1)
    (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSU n (r ^ f) K)) : I291P65.Is29a ↥L := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : Nat.Prime 5 := by norm_num
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (StatedProj (StatedSU 0 (r ^ f) K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := Nat.le_of_dvd hn0 hpn
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_unitary hp le_rfl hGA hq hZp hn5 hK e
  have hF := odFamily_unitary_of_inputs i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds hp
    le_rfl hpn hn0 hK hpq
  have hperfSU : Group.IsPerfect (StatedSU n (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  have hnp : n = 5 := by
    refine n_eq_p_of_cover (p := 5) le_rfl hpn hn0 L hperf hx hx2 hperfSU
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)))
      (fun B => (l212in_suConj hK B).toMonoidHom) (l212in_suPhi hK) (odUZ K n r f) hF.central
      hF.comm_mem (fun B h => (hF.ker_eq B).1 h) e φ hφπ
      (fun B s => (l212in_suPhi_mk hK B s).symm) (fun w hw B => ?_) (fun B hB => ?_)
      (fun hn B hBZ hBnp => ?_)
    ·
      obtain ⟨u, hu⟩ := mem_odUZ.1 hw
      refine MonoidHom.ext fun g => Subtype.ext ?_
      show ((l212in_suConj hK (w * B) g : StatedSU n (r ^ f) K) : GL (Fin n) K) =
        ((l212in_suConj hK B g : StatedSU n (r ^ f) K) : GL (Fin n) K)
      rw [l212in_suConj_coe, l212in_suConj_coe, Subgroup.coe_mul, _root_.mul_inv_rev, ← hu]
      have hc := l212in_scalar_comm ((B : GL (Fin n) K) * (g : GL (Fin n) K) *
        (B : GL (Fin n) K)⁻¹) u
      calc GeneralLinearGroup.scalar (Fin n) u * (B : GL (Fin n) K) * (g : GL (Fin n) K) *
            ((B : GL (Fin n) K)⁻¹ * (GeneralLinearGroup.scalar (Fin n) u)⁻¹)
          = GeneralLinearGroup.scalar (Fin n) u * ((B : GL (Fin n) K) * (g : GL (Fin n) K) *
              (B : GL (Fin n) K)⁻¹) * (GeneralLinearGroup.scalar (Fin n) u)⁻¹ := by group
        _ = (B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ := by
          rw [← hc, _root_.mul_inv_cancel_right]
    ·
      have hBp : (B : GL (Fin n) K) ^ 5 = 1 := by
        have h1 := congrArg Subtype.val hB
        simpa using h1
      obtain ⟨F, hFi, hFc, hFs⟩ := i294ODUnitaryTorus_holds hp hn5 hK hpq (B : GL (Fin n) K) B.2
        hBp
      refine ⟨F, ?_, fun a => ?_⟩
      · rw [injective_iff_map_eq_one]
        intro y hy
        have h1 : F y ∈ (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
            (StatedSU n (r ^ f) K))).ker := hy
        rw [QuotientGroup.ker_mk'] at h1
        exact (injective_iff_map_eq_one F).1 hFi y (hFs y (Subgroup.mem_subgroupOf.1 h1))
      · apply Subtype.ext
        show ((l212in_suConj hK B (F a) : StatedSU n (r ^ f) K) : GL (Fin n) K) =
          (F a : GL (Fin n) K)
        rw [l212in_suConj_coe, hFc a, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
    ·
      obtain ⟨c, hBp, hnpow⟩ := od_unitary_nonpower hn0 hp hp2 hK hpq hBZ hBnp
      obtain ⟨T, hTe, hTcard, hTnorm⟩ := i294ODUnitaryMonomial_holds hp hp2 hK hpq hn
        (B : GL (Fin n) K) B.2 c hBp hnpow
      refine ⟨T, hTe, hTcard, fun g hg => ?_⟩
      obtain ⟨g', hg', hgg'⟩ := hTnorm g hg
      have h : l212in_suConj hK B g = g' := Subtype.ext (by rw [l212in_suConj_coe]; exact hgg')
      show l212in_suConj hK B g ∈ T
      rw [h]
      exact hg'
  subst hnp
  have hcard : Nat.card (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
      (StatedSU 5 (r ^ f) K))).ker = 5 := by
    rw [QuotientGroup.ker_mk', card_scalars_statedSU hK (by norm_num), Nat.gcd_eq_left hpq]
  rcases final_of_cover (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
      (StatedSU 5 (r ^ f) K))) e φ hφ hφπ hcard with ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩
  · exact Or.inr ⟨r ^ f, K, inferInstance, inferInstance, hK, hpq, Or.inl ⟨h.symm⟩⟩
  · exact Or.inr ⟨r ^ f, K, inferInstance, inferInstance, hK, hpq, Or.inr ⟨h⟩⟩

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni
