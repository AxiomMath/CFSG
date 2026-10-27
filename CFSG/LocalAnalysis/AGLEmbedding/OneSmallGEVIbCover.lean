module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_second_component (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    ∃ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ ∧
      L' ≤ d1X0 p M H ∧ ∀ hzH : z ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈ L' := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  unfold D1SmallIa at hnIa
  push Not at hnIa
  obtain ⟨L', hL', hne⟩ := hnIa
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hL'C : L' ≤ C := le_centralizer_of_component_ne hL' hd.comp hne
  obtain ⟨zs, hzsR, hzsK, hzsp, hzsc⟩ := hd.z
  have hCX : C ≤ d1X0 p M H :=
    hd.cfg.red.centralizer_le_of_rankOne hd.noncyclic hzsR hzsK hzsp hzsc
  refine ⟨L', hL', hL'C.trans hCX, fun hzH => ?_⟩
  obtain ⟨t, ⟨htR, htL⟩, htp, -⟩ := exists_mem_sylow_inf_component hp hp2
    hd.cfg.red.core_eq_bot Rbar hL'
  set zb := QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩
  have hzbR : zb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact ⟨⟨z, hzH⟩, hz.1, rfl⟩
  have hzbC : zb ∈ C := hz.2.2.2
  have hcard := D1OneSmallData.card_le_of_le_centralizer hd hR
    (inf_le_right : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ C ≤ C)
    (Rbar.isPGroup'.to_le inf_le_left)
  have hle : Subgroup.zpowers t ≤ (Rbar : Subgroup _) ⊓ C :=
    Subgroup.zpowers_le.mpr ⟨htR, hL'C htL⟩
  have heq : Subgroup.zpowers t = (Rbar : Subgroup _) ⊓ C :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, htp]; exact hcard)
  have hzbt : zb ∈ Subgroup.zpowers t := by rw [heq]; exact ⟨hzbR, hzbC⟩
  exact (Subgroup.zpowers_le.mpr htL) hzbt

omit [Finite G] in
theorem commutator_eq_self_of_component {X : Type*} [Group X] {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : ⁅L, L⁆ = L := by
  have h1 : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := hL.2.2.1
  calc ⁅L, L⁆ = ⁅(⊤ : Subgroup ↥L).map L.subtype, (⊤ : Subgroup ↥L).map L.subtype⁆ := by rw [h1]
    _ = Subgroup.map L.subtype ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ :=
      (Subgroup.map_commutator _ _ _).symm
    _ = L := by rw [h2, h1]

theorem D1OneSmallData.exists_perfect_cover (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hzM : z ∈ M) (hnIa : ¬ D1SmallIa p H K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    ∃ U : Subgroup G, U ≤ H ⊓ M ∧ ⁅U, U⁆ = U ∧ z ∈ U := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L', hL', hL'X, hzL'⟩ := D1OneSmallData.exists_second_component hd hz hnIa hR
  have hzH : z ∈ H := hz.2.2.1
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set Y : Subgroup G := (L'.comap π).map H.subtype ⊓ M
  have hYHM : Y ≤ H ⊓ M := le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) inf_le_right
  have hYH : Y ≤ H := hYHM.trans inf_le_left
  set U := perfectCore Y
  have hUY : U ≤ Y := perfectCore_le Y
  refine ⟨U, hUY.trans hYHM, perfectCore_perfect Y, ?_⟩
  set ψ := π.comp (Subgroup.inclusion hYH)
  have hzY : z ∈ Y := ⟨⟨⟨z, hzH⟩, hzL' hzH, rfl⟩, hzM⟩
  have hrange : ψ.range = L' := by
    refine le_antisymm ?_ fun l hl => ?_
    · rintro _ ⟨⟨y, ⟨h, hh, rfl⟩, -⟩, rfl⟩
      have : Subgroup.inclusion hYH ⟨(h : G), ⟨h, hh, rfl⟩, ‹_›⟩ = h := Subtype.ext rfl
      simpa [ψ, this] using hh
    · obtain ⟨h, hh, rfl⟩ := hL'X hl
      have hhM : (h : G) ∈ M := (Subgroup.mem_subgroupOf.mp hh).2
      refine ⟨⟨h, ⟨h, ?_, rfl⟩, hhM⟩, ?_⟩
      · exact hl
      · show π (Subgroup.inclusion hYH _) = π h
        congr 1
  have hW : (perfectCore (⊤ : Subgroup ↥Y)).map ψ = L' := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, hrange]
    exact perfectCore_eq_self_of_perfect (commutator_eq_self_of_component hL')
  have hWU : (perfectCore (⊤ : Subgroup ↥Y)).map Y.subtype = U := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hzW : π ⟨z, hzH⟩ ∈ (perfectCore (⊤ : Subgroup ↥Y)).map ψ := by
    rw [hW]
    exact hzL' hzH
  obtain ⟨w', hw'W, hw'z⟩ := hzW
  have hwU : (w' : G) ∈ U := hWU ▸ ⟨w', hw'W, rfl⟩
  set n : ↥Y := w'⁻¹ * ⟨z, hzY⟩
  have hn : p.Coprime (orderOf n) := by
    have h1 : ψ n = 1 := by
      rw [map_mul, map_inv, hw'z]
      exact inv_mul_cancel _
    have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 : orderOf (Subgroup.inclusion hYH n) ∣ Nat.card (GLBPrimeCore p H) := by
      have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H) (x := (Subgroup.inclusion hYH n : G))
        h2
      rwa [Subgroup.orderOf_coe] at this
    rw [orderOf_injective _ (Subgroup.inclusion_injective hYH)] at h3
    exact (glbPrimeCore_coprime p H).coprime_dvd_right h3
  have hUn : (U.subgroupOf Y).Normal := perfectCore_normal Y
  set q := QuotientGroup.mk' (U.subgroupOf Y)
  have hqw : q w' = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwU)
  have hqz : q ⟨z, hzY⟩ = q n := by
    rw [show n = w'⁻¹ * ⟨z, hzY⟩ from rfl, map_mul, map_inv, hqw, inv_one, one_mul]
  have hzp : orderOf (⟨z, hzY⟩ : ↥Y) = p := by rw [Subgroup.orderOf_mk]; exact hz.2.1
  have h1 : orderOf (q ⟨z, hzY⟩) ∣ p := hzp ▸ orderOf_map_dvd q _
  have h2 : orderOf (q ⟨z, hzY⟩) ∣ orderOf n := hqz ▸ orderOf_map_dvd q n
  have h3 : orderOf (q ⟨z, hzY⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hn) h2
  have h4 : ⟨z, hzY⟩ ∈ U.subgroupOf Y := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  exact Subgroup.mem_subgroupOf.mp h4

end CFSG.AGLEmbedding
