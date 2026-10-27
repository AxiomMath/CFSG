module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiPx

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private lemma p622_relIndex_inf_map_conj {P C : Subgroup G} {g : G} (hg : g ∈ P) :
    (P ⊓ C.map (MulAut.conj g).toMonoidHom).relIndex (C.map (MulAut.conj g).toMonoidHom) =
      (P ⊓ C).relIndex C := by
  have hP : P.map (MulAut.conj g).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
  calc (P ⊓ C.map (MulAut.conj g).toMonoidHom).relIndex (C.map (MulAut.conj g).toMonoidHom)
      = (P.map (MulAut.conj g).toMonoidHom ⊓ C.map (MulAut.conj g).toMonoidHom).relIndex
          (C.map (MulAut.conj g).toMonoidHom) := by rw [hP]
    _ = ((P ⊓ C).map (MulAut.conj g).toMonoidHom).relIndex (C.map (MulAut.conj g).toMonoidHom) := by
        rw [map_inf_eq P C (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    _ = (P ⊓ C).relIndex C :=
        relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _
          (MulAut.conj g).injective

theorem p622_smallRankPoint_of_mem_plane (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {b : G} (hb : b ∈ zpowers x ⊔ zpowers z)
    (hbz : b ∉ zpowers z) : SmallRankPoint P M b := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  have hbP : b ∈ (P : Subgroup G) := hB.isIsolatedPlane.1 hb
  have hbp : b ^ p = 1 := hB.isElemAbelian.2 b hb
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
  obtain ⟨g, hg, hgx⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx hz hb hbz
  have hgP : g ∈ (P : Subgroup G) := hg.1
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({b} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom :=
    calc centralizer ({b} : Set G)
        = centralizer ((zpowers b : Subgroup G) : Set G) := hcz b
      _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [hgx]
      _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        (CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism _ _).symm
      _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]
  refine ⟨hbP, hb1, hbp, ?_, ?_⟩
  ·
    intro hle
    apply hx.not_centralizer_le
    intro c hc
    have hcM : g * c * g⁻¹ ∈ M := hle (by rw [hC]; exact ⟨c, hc, rfl⟩)
    have hgM : g ∈ M := hPM hgP
    have hc' := M.mul_mem (M.mul_mem (M.inv_mem hgM) hcM) hgM
    simpa [mul_assoc] using hc'
  ·
    have hrel := hx.sylow_centralizer
    rw [hC]
    show ¬ p ∣ ((P : Subgroup G) ⊓ (centralizer ({x} : Set G)).map
      (MulAut.conj g).toMonoidHom).relIndex ((centralizer ({x} : Set G)).map
        (MulAut.conj g).toMonoidHom)
    rw [p622_relIndex_inf_map_conj hgP]
    exact hrel

theorem p622_conj_mem_zpowers (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  by_contra hgz
  have h2 := pRank_centralizer_le_two3 hS hsit
    (p622_smallRankPoint_of_mem_plane hS hsit hx hz hg hgz)
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
  have hPz : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqz : q * z = z * q := mem_centralizer_iff.mp hz.centralizes q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  have h3 := pRank_mono p hprime.one_lt hPz
  rw [pRank_map_automorphism p hprime.one_lt, hP3] at h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
