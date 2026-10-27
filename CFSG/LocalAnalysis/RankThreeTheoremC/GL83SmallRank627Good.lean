module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem exists_mem_normalizer_not_mem_of_lt_aux {H : Type} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {R Q : Subgroup H} (hR : IsPGroup p R) (hQR : Q < R) :
    ∃ r ∈ R, r ∈ normalizer (Q : Set H) ∧ r ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hQ : Q.subgroupOf R < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hQR.not_ge (subgroupOf_eq_top.mp h)
  obtain ⟨a, ha, haQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hQ)
  refine ⟨a, a.2, ?_, haQ⟩
  rw [← subgroupOf_normalizer_eq hQR.le] at ha
  exact ha

private theorem exists_mem_normalizer_isPGroup_sup_zpowers_aux {p : ℕ} [Fact p.Prime]
    {C Q : Subgroup G} (hQC : Q ≤ C) (hQ : IsPGroup p Q) (hdvd : p ∣ (Q.subgroupOf C).index) :
    ∃ r ∈ C, r ∈ normalizer (Q : Set G) ∧ r ∉ Q ∧ IsPGroup p (Q ⊔ zpowers r : Subgroup G) := by
  obtain ⟨R, hR⟩ := (hQ.comap_subtype (K := C)).exists_le_sylow
  have hlt : Q.subgroupOf C < R :=
    lt_of_le_of_ne hR fun h => R.not_dvd_index (h ▸ hdvd)
  obtain ⟨a, haR, hanorm, haQ⟩ := exists_mem_normalizer_not_mem_of_lt_aux R.isPGroup' hlt
  refine ⟨a, a.2, ?_, haQ, ?_⟩
  · rw [← subgroupOf_normalizer_eq hQC] at hanorm
    exact hanorm
  · refine ((R.isPGroup'.map C.subtype).to_le ?_)
    exact sup_le (fun q hq => ⟨⟨q, hQC hq⟩, hR hq, rfl⟩) (zpowers_le.mpr ⟨a, haR, rfl⟩)

theorem exists_smallRankPoint (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hΓ : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M)
    (hempty : ∀ y : G, ¬ IsLargeObstruction p M y) : ∃ x : G, SmallRankPoint P M x := by
  have _ := hempty
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  let 𝒳 : Set G :=
    {x | x ∈ (P : Subgroup G) ∧ x ≠ 1 ∧ x ^ p = 1 ∧ ¬ centralizer ({x} : Set G) ≤ M}
  obtain ⟨x₀, hx₀P, hx₀1, hx₀p, hx₀M⟩ :=
    exists_centralizer_not_le_of_not_gamma_one_le hS hU0 hp hM hΓ
  obtain ⟨x, ⟨hxP, hx1, hxp, hxM⟩, hmax⟩ := Set.exists_max_image 𝒳
    (fun x => Nat.card ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G))
    (Set.toFinite 𝒳) ⟨x₀, hx₀P, hx₀1, hx₀p, hx₀M⟩
  refine ⟨x, hxP, hx1, hxp, hxM, fun hdvd => ?_⟩
  set Q₀ : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hQ₀
  have hQ₀p : IsPGroup p Q₀ := P.isPGroup'.to_inf_left
  have hQ₀M : Q₀ ≤ M := inf_le_left.trans hPM
  have hN : normalizer (Q₀ : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hQ₀p hQ₀M
      (two_le_pRank_inf_centralizer P.isPGroup' (by omega) hxP hx1 hxp)
  obtain ⟨r, hrC, hrN, hrQ, hS₁p⟩ :=
    exists_mem_normalizer_isPGroup_sup_zpowers_aux
      (inf_le_right : Q₀ ≤ centralizer ({x} : Set G)) hQ₀p hdvd
  set S₁ : Subgroup G := Q₀ ⊔ zpowers r with hS₁
  have hS₁M : S₁ ≤ M := sup_le hQ₀M (zpowers_le.mpr (hN hrN))
  have hS₁C : S₁ ≤ centralizer ({x} : Set G) := sup_le inf_le_right (zpowers_le.mpr hrC)
  have hrS₁ : r ∈ S₁ := mem_sup_right (mem_zpowers r)
  have hQ₀S₁ : Q₀ ≤ S₁ := le_sup_left
  have hcard : Nat.card Q₀ < Nat.card S₁ :=
    card_lt_of_lt (lt_of_le_of_ne hQ₀S₁ fun h => (show r ∉ Q₀ from hrQ) (h ▸ hrS₁))
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM S₁ hS₁p hS₁M
  have hxQ₀ : x ∈ Q₀ := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hx'P : (m : G) * x * (m : G)⁻¹ ∈ (P : Subgroup G) := hm ⟨x, hQ₀S₁ hxQ₀, rfl⟩
  have hx'1 : (m : G) * x * (m : G)⁻¹ ≠ 1 := fun h => hx1 (by simpa using h)
  have hx'p : ((m : G) * x * (m : G)⁻¹) ^ p = 1 := by
    rw [conj_pow, hxp]
    simp
  have hx'M : ¬ centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) ≤ M := by
    intro h
    apply hxM
    intro y hy
    have hy' : y * x = x * y := mem_centralizer_singleton_iff.mp hy
    have hcomm : (m : G) * y * (m : G)⁻¹ ∈ centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) := by
      rw [mem_centralizer_singleton_iff, show (m : G) * y * (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) =
        (m : G) * (y * x) * (m : G)⁻¹ by group, hy']
      group
    have h2 := M.mul_mem (M.mul_mem (M.inv_mem m.2) (h hcomm)) m.2
    simpa [mul_assoc] using h2
  have hle : S₁.map (MulAut.conj (m : G)).toMonoidHom ≤
      (P : Subgroup G) ⊓ centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) := by
    refine le_inf hm ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s * x = x * s := mem_centralizer_singleton_iff.mp (hS₁C hs)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show (m : G) * s * (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) =
        (m : G) * (s * x) * (m : G)⁻¹ by group, hs']
    group
  have hmax' := hmax _ ⟨hx'P, hx'1, hx'p, hx'M⟩
  have hcard' := card_le_of_le hle
  rw [card_map_of_injective (MulAut.conj (m : G)).injective] at hcard'
  change Nat.card ((P : Subgroup G) ⊓ centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) :
    Subgroup G) ≤ Nat.card Q₀ at hmax'
  omega

theorem exists_smallRankSylowTwo (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    ∃ T : Subgroup G, SmallRankSylowTwo P M T := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨-, hMO, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  obtain ⟨S, hSn⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p 2
    hprime Nat.prime_two (P : Subgroup G) (rankThreePrimeCore p M) P.isPGroup' (hPM.trans hMO) hcop
  refine ⟨(S : Subgroup (rankThreePrimeCore p M)).map (rankThreePrimeCore p M).subtype,
    map_subtype_le _, S.isPGroup'.map _, ?_, hSn⟩
  rw [Subgroup.subgroupOf,
    comap_map_eq_self_of_injective (rankThreePrimeCore p M).subtype_injective]
  exact S.not_dvd_index

end CFSG.LocalAnalysis.RankThreeTheoremC
