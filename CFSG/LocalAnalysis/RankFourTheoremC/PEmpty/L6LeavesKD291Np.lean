module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Mem
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryMono
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniFam
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_linear l212in_projectiveSLEquivStated
  exists_cover_linear l212in_descend odC odFamily_unitary_of_inputs odUZ mem_odUZ
  od_unitary_nonpower l212in_suConj l212in_suConj_coe l212in_suPhi l212in_suPhi_mk
  l212in_scalar_comm exists_cover_unitary i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds)

section Linear

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem linear_n_eq_p (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} [hpp : Fact p.Prime]
    (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZp : IsPGroup p (center ↥L))
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hpn : p ∣ n) (hpK : p ∣ Nat.card K - 1)
    (e : ↥L ⧸ center ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL n K))
    (hmem : ∃ B : GL (Fin n) K, conjAut n K B =
      l212in_descend (e.trans (l212in_projectiveSLEquivStated n K).symm) (odC L x)) :
    n = p := by
  have hp : p.Prime := hpp.out
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  let e' : ↥L ⧸ center ↥L ≃* projectiveSL n K :=
    e.trans (l212in_projectiveSLEquivStated n K).symm
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_linear hp hp5 hGA hq hZp (by omega) e'
  have hF := odFamily_linear hp hp5 hpn hn0 hpK
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hcZ : ∀ w ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range,
      ∀ B : GL (Fin n) K,
      (fun B => (slConjugation n K B).toMonoidHom) (w * B) =
        (fun B => (slConjugation n K B).toMonoidHom) B := by
    intro w hw B
    obtain ⟨u, rfl⟩ := hw
    refine MonoidHom.ext fun g => ?_
    show slConjugation n K (GeneralLinearGroup.scalar (Fin n) u * B) g = slConjugation n K B g
    rw [map_mul, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar,
      one_mul]
  have htorus : ∀ B : GL (Fin n) K, B ^ p = 1 →
      ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* SpecialLinearGroup (Fin n) K,
        Function.Injective ((proj n K).comp f) ∧ ∀ a, slConjugation n K B (f a) = f a :=
    fun B hB => I291LinUni.linear_torus hp hn5 hpK B hB
  exact n_eq_p_of_mem hp5 hpn hn0 L hx hx2 hperfSL (proj n K)
    (fun B => (slConjugation n K B).toMonoidHom) (conjAut n K)
    (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range hF.central
    (fun B h => (hF.ker_eq B).1 h) e' φ hφπ (fun B s => (conjAut_proj B s).symm) hcZ htorus
    (fun hn B hBZ hnp => I291LinUni.linear_mono hp hpK hn B hBZ hnp) hmem

end Linear

section Unitary

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem unitary_n_eq_p (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} [hpp : Fact p.Prime]
    (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZp : IsPGroup p (center ↥L))
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hpn : p ∣ n) (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1)
    (e : ↥L ⧸ center ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K))
    (hmem : ∃ B : Uid (unitaryInvolution K r f) n,
      l212in_suPhi hK B = l212in_descend e (odC L x)) : n = p := by
  have hp : p.Prime := hpp.out
  have hp2 : p ≠ 2 := by omega
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSU 0 (r ^ f) K)) :=
        inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_unitary hp hp5 hGA hq hZp hn5 hK e
  have hF := odFamily_unitary_of_inputs i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds hp
    hp5 hpn hn0 hK hpq
  have hperfSU : Group.IsPerfect (CFSG.Open.StatedSU n (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  have hcZ : ∀ w ∈ odUZ K n r f, ∀ B : Uid (unitaryInvolution K r f) n,
      (fun B : Uid (unitaryInvolution K r f) n => (l212in_suConj hK B).toMonoidHom) (w * B) =
        (fun B : Uid (unitaryInvolution K r f) n => (l212in_suConj hK B).toMonoidHom) B := by
    intro w hw B
    obtain ⟨u, hu⟩ := mem_odUZ.1 hw
    refine MonoidHom.ext fun g => Subtype.ext ?_
    show ((l212in_suConj hK (w * B) g : CFSG.Open.StatedSU n (r ^ f) K) : GL (Fin n) K) =
      ((l212in_suConj hK B g : CFSG.Open.StatedSU n (r ^ f) K) : GL (Fin n) K)
    rw [l212in_suConj_coe, l212in_suConj_coe, Subgroup.coe_mul, _root_.mul_inv_rev, ← hu]
    have hc := l212in_scalar_comm ((B : GL (Fin n) K) * (g : GL (Fin n) K) *
      (B : GL (Fin n) K)⁻¹) u
    calc GeneralLinearGroup.scalar (Fin n) u * (B : GL (Fin n) K) * (g : GL (Fin n) K) *
          ((B : GL (Fin n) K)⁻¹ * (GeneralLinearGroup.scalar (Fin n) u)⁻¹)
        = GeneralLinearGroup.scalar (Fin n) u * ((B : GL (Fin n) K) * (g : GL (Fin n) K) *
            (B : GL (Fin n) K)⁻¹) * (GeneralLinearGroup.scalar (Fin n) u)⁻¹ := by group
      _ = (B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ := by
        rw [← hc, _root_.mul_inv_cancel_right]
  have htorus : ∀ B : Uid (unitaryInvolution K r f) n, B ^ p = 1 →
      ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* CFSG.Open.StatedSU n (r ^ f) K,
        Function.Injective ((QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin n) K).subgroupOf
          (CFSG.Open.StatedSU n (r ^ f) K))).comp F) ∧
        ∀ a, (l212in_suConj hK B).toMonoidHom (F a) = F a := by
    intro B hB
    have hBp : (B : GL (Fin n) K) ^ p = 1 := by
      have h1 := congrArg Subtype.val hB
      simpa using h1
    obtain ⟨F, hFi, hFc, hFs⟩ := i294ODUnitaryTorus_holds hp hn5 hK hpq (B : GL (Fin n) K) B.2 hBp
    refine ⟨F, ?_, fun a => ?_⟩
    · rw [injective_iff_map_eq_one]
      intro y hy
      have h1 : F y ∈ (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin n) K).subgroupOf
          (CFSG.Open.StatedSU n (r ^ f) K))).ker := hy
      rw [QuotientGroup.ker_mk'] at h1
      exact (injective_iff_map_eq_one F).1 hFi y (hFs y (Subgroup.mem_subgroupOf.1 h1))
    · apply Subtype.ext
      show ((l212in_suConj hK B (F a) : CFSG.Open.StatedSU n (r ^ f) K) : GL (Fin n) K) =
        (F a : GL (Fin n) K)
      rw [l212in_suConj_coe, hFc a, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
  refine n_eq_p_of_mem hp5 hpn hn0 L hx hx2 hperfSU
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin n) K).subgroupOf
      (CFSG.Open.StatedSU n (r ^ f) K)))
    (fun B => (l212in_suConj hK B).toMonoidHom) (l212in_suPhi hK) (odUZ K n r f) hF.central
    (fun B h => (hF.ker_eq B).1 h) e φ hφπ
    (fun B s => (l212in_suPhi_mk hK B s).symm) hcZ htorus (fun hn B hBZ hBnp => ?_) hmem
  obtain ⟨c, hBp, hnpow⟩ := od_unitary_nonpower hn0 hp hp2 hK hpq hBZ hBnp
  obtain ⟨T, hTe, hTcard, hTnorm⟩ := i294ODUnitaryMonomial_holds hp hp2 hK hpq hn
    (B : GL (Fin n) K) B.2 c hBp hnpow
  refine ⟨T, hTe, hTcard, fun g hg => ?_⟩
  obtain ⟨g', hg', hgg'⟩ := hTnorm g hg
  have h : l212in_suConj hK B g = g' := Subtype.ext (by rw [l212in_suConj_coe]; exact hgg')
  show l212in_suConj hK B g ∈ T
  rw [h]
  exact hg'

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
