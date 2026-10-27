module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Lattice
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

omit [Finite G] in
theorem commute_of_barM_commute {M R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 3 R) {a b : G}
    (ha : a ∈ R) (hb : b ∈ R)
    (hab : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, hRM ha⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hRM hb⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hRM hb⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, hRM ha⟩) : a * b = b * a := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (⟨a, hRM ha⟩ * ⟨b, hRM hb⟩ * (⟨b, hRM hb⟩ * ⟨a, hRM ha⟩)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hab, mul_inv_cancel]
  have h2 := eq_one_of_mem_pCoreOf_two Nat.prime_three (by norm_num) hR
    (R.mul_mem (R.mul_mem ha hb) (R.inv_mem (R.mul_mem hb ha)))
    (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  have := mul_inv_eq_one.mp h2
  simpa using this

theorem commute_of_inner_parts {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤) {x a b : X} (ha : a ∈ A) (hb : b ∈ B)
    (hac : a⁻¹ * x ∈ Subgroup.centralizer (A : Set X))
    (hbc : b⁻¹ * x ∈ Subgroup.centralizer (B : Set X)) : a * b = b * a := by
  by_cases hAB : A = B
  · subst hAB
    have hc : a⁻¹ * b ∈ Subgroup.centralizer (A : Set X) := by
      have := Subgroup.mul_mem _ hac (Subgroup.inv_mem _ hbc)
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc a ha
    have e : b = a * (a⁻¹ * b) := by group
    rw [e]
    calc a * (a * (a⁻¹ * b)) = a * ((a⁻¹ * b) * a) := by rw [h1]
      _ = a * (a⁻¹ * b) * a := by group
  · exact (Subgroup.mem_centralizer_iff.mp (le_centralizer_of_component_ne hB hA (Ne.symm hAB) hb)
      a ha)

theorem D1IbCubeThreeData.rep_mem_center (hc : D1IbCubeThreeData p P M H R Rbar K z)
    (hp3 : p = 3) (h3 : D1PhaseThree p P M H R) (hShape : KFactSmallSylowShape)
    (hOrb3 : KFactSmallOrbitsCube) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {r : G} (hrR : r ∈ R)
    (hrL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, h3.le_M hrR⟩ ∈ barM M L)
    (hrc : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, h3.le_M hrR⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, h3.le_M hc.elt.1⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ c ∈ centerOf (d1LiftX p H R K), ∃ i : ℕ, r = c * z ^ i := by
  subst hp3
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hRM : R ≤ M := h3.le_M
  have hRp : IsPGroup 3 R := h3.isPGroup
  have hzR : z ∈ R := hc.elt.1
  set zb := mk ⟨z, hRM hzR⟩ with hzb
  set X : Set G := {s | ∃ hsR : s ∈ R, ∃ L' : Subgroup G, IsWeakSBlock M S L' ∧
    mk ⟨s, hRM hsR⟩ ∈ barM M L' ∧
    (mk ⟨s, hRM hsR⟩)⁻¹ * zb ∈ Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M))}
    with hXdef
  have hXR : X ⊆ R := fun s hs => hs.1
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    rintro a ⟨haR, La, hLa, haL, hac⟩ b ⟨hbR, Lb, hLb, hbL, hbc⟩
    exact commute_of_barM_commute hRM hRp haR hbR
      (commute_of_inner_parts hLa.component hLb.component haL hbL hac hbc)
  set B := Subgroup.closure X with hB
  have hBR : B ≤ R := (Subgroup.closure_le R).mpr hXR
  have hXC : B ≤ Subgroup.centralizer X :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hcomm a ha b hb).symm
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    have hXB : X ⊆ Subgroup.centralizer (B : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp (hXC hb) x hx).symm
    have hBB : B ≤ Subgroup.centralizer (B : Set G) := (Subgroup.closure_le _).mpr hXB
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hBB hb) a ha)
  have hBinv : IsInvR 3 H R K z B := by
    intro n hn hnz _ b hb
    have hnM : n ∈ M := h3.toD1Escape.normalizer_le hn
    have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * z = n * z * n⁻¹ * n := by group
        _ = z * n := by rw [hnz]
    have hnS : n ∈ Subgroup.normalizer (S : Set G) :=
      localGroup_le_normalizer_pCoreOf 2 H (hCz hnC)
    have hXn : (MulAut.conj n).toMonoidHom '' X ⊆ X := by
      rintro _ ⟨s, ⟨hsR, L', hL', hsL, hsc⟩, rfl⟩
      show n * s * n⁻¹ ∈ X
      have hs'R : n * s * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn s).mp hsR
      have hnzb : mk ⟨n, hnM⟩ * zb * (mk ⟨n, hnM⟩)⁻¹ = zb := by
        rw [hzb, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hnz
      have he : mk ⟨n * s * n⁻¹, hRM hs'R⟩ = mk ⟨n, hnM⟩ * mk ⟨s, hRM hsR⟩ * (mk ⟨n, hnM⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      refine ⟨hs'R, L'.map (MulAut.conj n).toMonoidHom, hL'.map_conj hnM hnS, ?_, ?_⟩
      · rw [barM_map_conj hnM L', he]
        exact ⟨_, hsL, rfl⟩
      · rw [barM_map_conj hnM L', he]
        have := conj_mem_centralizer_map_of_mem (g := mk ⟨n, hnM⟩) hsc
        have e : mk ⟨n, hnM⟩ * ((mk ⟨s, hRM hsR⟩)⁻¹ * zb) * (mk ⟨n, hnM⟩)⁻¹ =
            (mk ⟨n, hnM⟩ * mk ⟨s, hRM hsR⟩ * (mk ⟨n, hnM⟩)⁻¹)⁻¹ * zb := by
          calc mk ⟨n, hnM⟩ * ((mk ⟨s, hRM hsR⟩)⁻¹ * zb) * (mk ⟨n, hnM⟩)⁻¹
              = (mk ⟨n, hnM⟩ * mk ⟨s, hRM hsR⟩ * (mk ⟨n, hnM⟩)⁻¹)⁻¹ *
                (mk ⟨n, hnM⟩ * zb * (mk ⟨n, hnM⟩)⁻¹) := by group
            _ = _ := by rw [hnzb]
        rwa [e] at this
    have hmap : B.map (MulAut.conj n).toMonoidHom ≤ B := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono hXn
    exact hmap ⟨b, hb, rfl⟩
  rcases hc.lattice hShape hOrb3 hBR hBinv with hT | ⟨hdec', -, -⟩
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hc.nonabelian hShape
    exact hab (hBcomm a (hT ha) b (hT hb))
  · exact hdec' r (Subgroup.subset_closure ⟨hrR, L, hL, hrL, hrc⟩)

omit [Finite G] in
theorem barM_commutator {M X : Subgroup G} (hXM : X ≤ M) :
    barM M ⁅X, X⁆ = ⁅barM M X, barM M X⁆ := by
  have hXX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.mpr fun a ha b hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have h1 : ⁅X.subgroupOf M, X.subgroupOf M⁆ = (⁅X, X⁆).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXM,
      Subgroup.map_subgroupOf_eq_of_le (hXX.trans hXM)]
  change ((⁅X, X⁆).subgroupOf M).map _ = ⁅(X.subgroupOf M).map _, (X.subgroupOf M).map _⁆
  rw [← Subgroup.map_commutator, h1]

end CFSG.AGLEmbedding
