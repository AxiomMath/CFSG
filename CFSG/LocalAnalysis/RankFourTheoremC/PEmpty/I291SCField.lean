module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.Semidihedral.FocalTransfer
open scoped commutatorElement

theorem exists_index_prime_of_focal_ne {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact (Nat.Prime p)] (S : Sylow p G) (hF : (S : Subgroup G).focalSubgroup ≠ S) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = p := by
  have hproper : conjugatePairFocal (S : Subgroup G) ≠ ⊤ := by
    intro htop
    apply hF
    rw [← map_conjugatePairFocal (S : Subgroup G), htop, Subgroup.map_top,
      Subgroup.range_subtype]
  have : Nontrivial (S ⧸ conjugatePairFocal (S : Subgroup G)) :=
    QuotientGroup.nontrivial_iff.mpr hproper
  obtain ⟨M, hnormal, hindex⟩ := exists_index_prime_of_nontrivial_abelian_pgroup
    (S.isPGroup'.to_quotient (conjugatePairFocal (S : Subgroup G)))
  let : M.Normal := hnormal
  refine ⟨M.comap (focalTransfer (S : Subgroup G)), inferInstance, ?_⟩
  exact (M.index_comap_of_surjective (focalTransfer_surjective S)).trans hindex

theorem focalSubgroup_le_of_kdInndiag (hΔ : KDInndiagP5) {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (L : Subgroup Y) [L.Normal] (hs : IsSimpleGroup L)
    (hn : ∃ a b : L, a * b ≠ b * a) (hc : IsCatalogGroup L) (hlu : ¬ IsLinearOrUnitaryAt p L)
    (hC : centralizer (L : Set Y) = ⊥) (P : Sylow p Y) :
    (P : Subgroup Y).focalSubgroup ≤ L := by
  rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro g ⟨hgP, a, haP, u, rfl⟩
  let φ : Y →* MulAut L := MulAut.conjNormal
  have hpow : ∀ y ∈ (P : Subgroup Y), ∃ k : ℕ, (φ y) ^ p ^ k = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have hy1 : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow, hy1, map_one]
  have hw : u * a * u⁻¹ * a⁻¹ = ⁅a, u⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  have hcomm : φ u * φ a * (φ u)⁻¹ * (φ a)⁻¹ = φ (u * a * u⁻¹ * a⁻¹) := by
    simp only [map_mul, map_inv]
  have hwP : u * a * u⁻¹ * a⁻¹ ∈ (P : Subgroup Y) := hw ▸ inv_mem hgP
  obtain ⟨l, hl⟩ := hΔ p hp hp5 L hs hn hc hlu (φ u) (φ a) (hpow a haP)
    (hcomm ▸ hpow _ hwP)
  rw [hcomm] at hl
  have hcen : (l : Y)⁻¹ * (u * a * u⁻¹ * a⁻¹) ∈ centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun ψ : MulAut L => ((ψ ⟨h, hh⟩ : L) : Y)) hl
    simp only [φ, MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    have h2 : (u * a * u⁻¹ * a⁻¹) * h = (l : Y) * h * (l : Y)⁻¹ * (u * a * u⁻¹ * a⁻¹) := by
      rw [h1]
      group
    calc h * ((l : Y)⁻¹ * (u * a * u⁻¹ * a⁻¹))
        = (l : Y)⁻¹ * ((l : Y) * h * (l : Y)⁻¹ * (u * a * u⁻¹ * a⁻¹)) := by group
      _ = (l : Y)⁻¹ * ((u * a * u⁻¹ * a⁻¹) * h) := by rw [h2]
      _ = (l : Y)⁻¹ * (u * a * u⁻¹ * a⁻¹) * h := by group
  rw [hC, Subgroup.mem_bot] at hcen
  have hwL : u * a * u⁻¹ * a⁻¹ ∈ L := by
    have : u * a * u⁻¹ * a⁻¹ = (l : Y) := by
      calc u * a * u⁻¹ * a⁻¹ = (l : Y) * ((l : Y)⁻¹ * (u * a * u⁻¹ * a⁻¹)) := by group
        _ = (l : Y) := by rw [hcen, mul_one]
    rw [this]
    exact l.2
  have := inv_mem hwL
  rwa [hw, inv_inv] at this

section CertificateInstances


theorem kdFieldP5_holds : KDFieldP5 := by
  intro p hp hp5 Y _ _ hcat _ L hLn hs hn hlu hC _ x hxL hxo
  right
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI := hLn
  have hxp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  refine exists_index_prime_of_focal_ne P fun hF => hxL ?_
  have hle := focalSubgroup_le_of_kdInndiag kdInndiagP5_holds hp hp5 L hs hn
    (hcat.simple_subgroup L hs hn) hlu hC P
  rw [hF] at hle
  exact hle (hP (mem_zpowers x))

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
