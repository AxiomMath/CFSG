module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Lin
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryMono

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open Subgroup Matrix
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_unitary_of_inputs odUZ mem_odUZ
  od_unitary_nonpower l212in_suConj l212in_suConj_coe l212in_suPhi l212in_suPhi_mk
  l212in_scalar_comm exists_cover_unitary card_scalars_statedSU i294ODUnitaryTorus_holds
  i294ODUnitaryMonomial_holds l212in_descend l212in_descend_apply odC l212in_scalar_unitary
  l212in_scalar_mem_Uid_iff)

section Unitary

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem unitary_compat (hK : Nat.card K = (r ^ f) ^ 2) {Y : Type} [Group Y] (L : Subgroup Y)
    [L.Normal] {x : Y} (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSU n (r ^ f) K))
    (B : Uid (unitaryInvolution K r f) n) (ŷ : GL (Fin n) K)
    (hŷ : ∀ M : GL (Fin n) K, ŷ * M * ŷ⁻¹ = (B : GL (Fin n) K) * M * (B : GL (Fin n) K)⁻¹)
    (hB : l212in_suPhi hK B = l212in_descend e (odC L x)) :
    ∀ (g h : ↥L) (A B₀ : ↥(StatedSU n (r ^ f) K)), x * (g : Y) * x⁻¹ = (h : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B₀ : GL (Fin n) K) = ŷ * (A : GL (Fin n) K) * ŷ⁻¹ →
      e (QuotientGroup.mk h) = QuotientGroup.mk B₀ := by
  intro g h A B₀ hxg heA hB₀
  have hh : odC L x g = h := Subtype.ext (by rw [odC, MulAut.conjNormal_apply]; exact hxg)
  have h1 : e (QuotientGroup.mk h) = l212in_suPhi hK B (e (QuotientGroup.mk g)) := by
    rw [hB, ← hh, l212in_descend_apply]
  rw [h1, heA, l212in_suPhi_mk]
  congr 1
  refine Subtype.ext ?_
  rw [hB₀, hŷ, l212in_suConj_coe]

theorem factorization_sq_sub_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) : (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
  have hq1 : ¬ p ∣ q - 1 := by
    intro h
    have h2 : p ∣ 2 := by
      have h3 : q + 1 = (q - 1) + 2 := by omega
      rw [h3] at hpq
      exact (Nat.dvd_add_right h).1 hpq
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hq0 : q - 1 ≠ 0 := by
    intro h0
    rw [h0] at hq1
    exact hq1 (dvd_zero p)
  have h2 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have h : (m + 1) ^ 2 = (m + 1 + 1) * (m + 1 - 1) + 1 := by
      rw [Nat.add_sub_cancel]
      ring
    omega
  rw [h2, Nat.factorization_mul (by omega) hq0]
  simp [Nat.factorization_eq_zero_of_not_dvd hq1]

theorem unitary_model (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} [hpp : Fact p.Prime]
    (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZp : IsPGroup p (center ↥L))
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hpn : p ∣ n) (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1)
    (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSU n (r ^ f) K)) :
    LinUniModelUni p x L := by
  have hp : p.Prime := hpp.out
  have hp2 : p ≠ 2 := by omega
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (StatedProj (StatedSU 0 (r ^ f) K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_unitary hp hp5 hGA hq hZp hn5 hK e
  have hF := odFamily_unitary_of_inputs i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds hp
    hp5 hpn hn0 hK hpq
  have hperfSU : Group.IsPerfect (StatedSU n (r ^ f) K) :=
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
  have htorus : ∀ B : Uid (unitaryInvolution K r f) n, B ^ p = 1 →
      ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* StatedSU n (r ^ f) K,
        Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).comp F) ∧
        ∀ a, (l212in_suConj hK B).toMonoidHom (F a) = F a := by
    intro B hB
    have hBp : (B : GL (Fin n) K) ^ p = 1 := by
      have h1 := congrArg Subtype.val hB
      simpa using h1
    obtain ⟨F, hFi, hFc, hFs⟩ := i294ODUnitaryTorus_holds hp hn5 hK hpq (B : GL (Fin n) K) B.2 hBp
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
  have hnp : n = p := by
    refine I291LinUni.n_eq_p_of_cover (p := p) hp5 hpn hn0 L hperf hx hx2 hperfSU
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)))
      (fun B => (l212in_suConj hK B).toMonoidHom) (l212in_suPhi hK) (odUZ K n r f) hF.central
      hF.comm_mem (fun B h => (hF.ker_eq B).1 h) e φ hφπ
      (fun B s => (l212in_suPhi_mk hK B s).symm) hcZ htorus (fun hn B hBZ hBnp => ?_)
    obtain ⟨c, hBp, hnpow⟩ := od_unitary_nonpower hn0 hp hp2 hK hpq hBZ hBnp
    obtain ⟨T, hTe, hTcard, hTnorm⟩ := i294ODUnitaryMonomial_holds hp hp2 hK hpq hn
      (B : GL (Fin n) K) B.2 c hBp hnpow
    refine ⟨T, hTe, hTcard, fun g hg => ?_⟩
    obtain ⟨g', hg', hgg'⟩ := hTnorm g hg
    have h : l212in_suConj hK B g = g' := Subtype.ext (by rw [l212in_suConj_coe]; exact hgg')
    show l212in_suConj hK B g ∈ T
    rw [h]
    exact hg'
  obtain ⟨B, hB, hBZ, hBnp⟩ := L6KD291.exists_B_of_cover hp5 L hperf hx hx2 hperfSU
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)))
    (fun B => (l212in_suConj hK B).toMonoidHom) (l212in_suPhi hK) (odUZ K n r f) hF.central
    hF.comm_mem (fun B h => (hF.ker_eq B).1 h) e φ hφπ
    (fun B s => (l212in_suPhi_mk hK B s).symm) hcZ htorus
  obtain ⟨c, hBp, hnpow⟩ := od_unitary_nonpower hn0 hp hp2 hK hpq hBZ hBnp
  have hcu : c ^ (r ^ f + 1) = 1 :=
    l212in_scalar_unitary hn0 (by rw [← hBp]; exact Subgroup.pow_mem _ B.2 p)
  have hcnp : ∀ b : Kˣ, b ^ p ≠ c := fun b hb =>
    hnpow (b : K) (by simpa using congrArg Units.val hb)
  have hfac : (orderOf c).factorization p = (r ^ f + 1).factorization p := by
    rw [factorization_orderOf_eq_of_not_pow hp hcnp, Nat.card_units, hK]
    exact factorization_sq_sub_one hp hp5 (Nat.one_le_pow _ _ (Fact.out : r.Prime).pos) hpq
  obtain ⟨d, hdmem, hd⟩ := exists_pow_mul_orderOf_eq hp c
  have hd1 : d ^ (r ^ f + 1) = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hdmem
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hcu,
      _root_.one_zpow]
  have hdU : GeneralLinearGroup.scalar (Fin n) d ∈ Uid (unitaryInvolution K r f) n :=
    (l212in_scalar_mem_Uid_iff hn0 d).2 hd1
  have hyU : GeneralLinearGroup.scalar (Fin n) d * (B : GL (Fin n) K) ∈
      Uid (unitaryInvolution K r f) n := mul_mem hdU B.2
  subst hnp
  refine ⟨r ^ f, K, inferInstance, inferInstance, e,
    GeneralLinearGroup.scalar (Fin n) d * (B : GL (Fin n) K), d ^ n * c, hK, hpq, ?_, ?_, ?_, ?_⟩
  · have h1 := (mem_Uid_iff _ _ _).1 hyU
    have hσ : (⇑(unitaryInvolution K r f) : K → K) = fun c => c ^ r ^ f :=
      funext (unitaryInvolution_apply K r f)
    simpa only [conjTr, hσ] using h1
  · rw [(Commute.symm (l212in_scalar_comm (B : GL (Fin n) K) d)).mul_pow, hBp, ← map_pow,
      ← map_mul]
  · rw [hd, hfac]
  · exact unitary_compat hK L e B _ (scalar_mul_conj d (B : GL (Fin n) K)) hB

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
