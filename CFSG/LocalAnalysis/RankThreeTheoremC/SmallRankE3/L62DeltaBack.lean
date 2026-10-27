module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Delta
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Quotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (qs_injOn qs_ker qs_card_map)

variable {G : Type} [Group G] [Finite G]

section Delta3Core

variable {H : Type} [Group H] [Finite H]

theorem delta3_map_inf_comap {S : Subgroup H} {Q : Subgroup (Bar H)}
    (hQS : Q ≤ S.map (barMk H)) :
    (S ⊓ Q.comap (barMk H)).map (barMk H) = Q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hy).2
  · intro hx
    obtain ⟨y, hyS, hyx⟩ := Subgroup.mem_map.mp (hQS hx)
    refine ⟨y, Subgroup.mem_inf.mpr ⟨hyS, Subgroup.mem_comap.mpr ?_⟩, hyx⟩
    rw [hyx]
    exact hx

theorem delta3_sup_prime {S : Subgroup H} {Q : Subgroup (Bar H)}
    (hQS : Q ≤ S.map (barMk H)) :
    (S ⊓ Q.comap (barMk H)) ⊔ primeComplementCore (G := H) 3 = Q.comap (barMk H) := by
  apply le_antisymm
  · refine sup_le inf_le_right ?_
    intro x hx
    have hker : x ∈ (barMk H).ker := by
      rw [qs_ker]
      exact hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hker]
    exact Q.one_mem
  · intro r hr
    have hpr : barMk H r ∈ Q := Subgroup.mem_comap.mp hr
    obtain ⟨s, hsS, hsr⟩ := Subgroup.mem_map.mp (hQS hpr)
    have hs : s ∈ S ⊓ Q.comap (barMk H) :=
      Subgroup.mem_inf.mpr ⟨hsS, Subgroup.mem_comap.mpr (by rw [hsr]; exact hpr)⟩
    have hd : s⁻¹ * r ∈ primeComplementCore (G := H) 3 := by
      rw [← qs_ker, MonoidHom.mem_ker, map_mul, map_inv, hsr, inv_mul_cancel]
    have h := Subgroup.mul_mem_sup hs hd
    rwa [mul_inv_cancel_left] at h

theorem delta3_mulEquiv {S : Subgroup H} (hS : IsPGroup 3 S) {Q : Subgroup (Bar H)}
    (hQS : Q ≤ S.map (barMk H)) :
    Nonempty (↥(S ⊓ Q.comap (barMk H)) ≃* ↥Q) := by
  have hinj : Function.Injective ((barMk H).comp (S ⊓ Q.comap (barMk H)).subtype) := by
    intro a b hab
    exact Subtype.ext (qs_injOn (Q := S) hS (Subgroup.mem_inf.mp a.2).1
      (Subgroup.mem_inf.mp b.2).1 hab)
  have hrange : ((barMk H).comp (S ⊓ Q.comap (barMk H)).subtype).range = Q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, delta3_map_inf_comap hQS]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem delta3_card_eq {S : Subgroup H} (hS : IsPGroup 3 S) {Q : Subgroup (Bar H)}
    (hQS : Q ≤ S.map (barMk H)) :
    Nat.card ↥(S ⊓ Q.comap (barMk H)) = Nat.card ↥Q := by
  have h1 := qs_card_map hS (inf_le_left : S ⊓ Q.comap (barMk H) ≤ S)
  rw [delta3_map_inf_comap hQS] at h1
  exact h1.symm

theorem delta3_isCyclic {S : Subgroup H} (hS : IsPGroup 3 S) {Q : Subgroup (Bar H)}
    (hQS : Q ≤ S.map (barMk H)) (hcyc : IsCyclic ↥Q) :
    IsCyclic ↥(S ⊓ Q.comap (barMk H)) := by
  obtain ⟨e⟩ := delta3_mulEquiv hS hQS
  exact isCyclic_of_injective e.toMonoidHom e.injective

end Delta3Core

theorem smallRankCaseDelta3_of_sylow {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M : Subgroup G} (S : Sylow 3 ↥M)
    (hSP : ∀ s : ↥M, s ∈ (S : Subgroup ↥M) → (s : G) ∈ (P : Subgroup G))
    {Q : Subgroup (Bar ↥M)} (hQn : Q.Normal) (hcyc : IsCyclic ↥Q) (h9 : 9 ∣ Nat.card ↥Q)
    (hQS : Q ≤ (S : Subgroup ↥M).map (barMk ↥M)) :
    SmallRankCaseDelta3 P M := by
  have hS3 : IsPGroup 3 (S : Subgroup ↥M) := S.isPGroup'
  have hMinj : Function.Injective M.subtype := Subgroup.subtype_injective M
  have hN0 : IsCyclic ↥((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)) :=
    delta3_isCyclic hS3 hQS hcyc
  have hsup : ((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)).map M.subtype ⊔
      rankThreePrimeCore 3 M = (Q.comap (barMk ↥M)).map M.subtype := by
    rw [rankThreePrimeCore_eq_map_primeComplementCore 3 M, ← Subgroup.map_sup,
      delta3_sup_prime hQS]
  have hsub : ((Q.comap (barMk ↥M)).map M.subtype).subgroupOf M = Q.comap (barMk ↥M) := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective hMinj]
  have hRn : (Q.comap (barMk ↥M)).Normal := hQn.comap (barMk ↥M)
  have hcard : Nat.card ↥(((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)).map M.subtype) =
      Nat.card ↥Q := by
    rw [Subgroup.card_map_of_injective hMinj, delta3_card_eq hS3 hQS]
  have hcycN : IsCyclic ↥(((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)).map M.subtype) :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective ((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)) M.subtype hMinj)
      (Subgroup.equivMapOfInjective ((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)) M.subtype hMinj).surjective
  unfold SmallRankCaseDelta3
  refine ⟨((S : Subgroup ↥M) ⊓ Q.comap (barMk ↥M)).map M.subtype, ?_, hcycN, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
    exact hSP s (Subgroup.mem_inf.mp hs).1
  · rw [hcard]
    exact h9
  · rw [hsup]
    exact Subgroup.map_subtype_le _
  · rw [hsup, hsub]
    exact hRn

theorem smallRankCaseDelta3_of_pCore {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hcyc : IsCyclic ↥(CFSG.pCore 3 (Bar ↥M)))
    (h9 : 9 ≤ Nat.card ↥(CFSG.pCore 3 (Bar ↥M))) :
    SmallRankCaseDelta3 P M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective (barMk ↥M) :=
    QuotientGroup.mk'_surjective (primeComplementCore (G := ↥M) 3)
  have h9dvd : 9 ∣ Nat.card ↥(CFSG.pCore 3 (Bar ↥M)) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 3) (G := Bar ↥M)).exists_card_eq
    rw [hn] at h9 ⊢
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n <;> norm_num at h9
    · exact dvd_trans (by norm_num) (pow_dvd_pow 3 hge)
  have hSP : ∀ s : ↥M, s ∈ ((P.subtype hPM : Sylow 3 ↥M) : Subgroup ↥M) →
      (s : G) ∈ (P : Subgroup G) := by
    intro s hs
    have hs' : s ∈ (P : Subgroup G).subgroupOf M := hs
    exact Subgroup.mem_subgroupOf.mp hs'
  exact smallRankCaseDelta3_of_sylow (P.subtype hPM) hSP (Q := CFSG.pCore 3 (Bar ↥M))
    CFSG.pCore_normal hcyc h9dvd
    (CFSG.fitting_pCore_le_sylow ((P.subtype hPM).mapSurjective hsurj))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
