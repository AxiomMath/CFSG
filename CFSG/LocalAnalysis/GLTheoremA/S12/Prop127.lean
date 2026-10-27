module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma124

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem comm_core_le {d : G} {M : Subgroup G} (hp : p.Prime)
    (hM : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) M) :
    (⁅M, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G) ≤ Xc p M := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set N := GLAPPrimeCoreOf p C with hN
  have hNM : N ≤ Subgroup.normalizer (M : Set G) := primeCore_le_normalizer hM
  have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
    hM.1.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p C))
  have hY : (⁅M, N⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p M := comm_le_primeCore hp hM
  have hMM : M ≤ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer
  have hNN : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  have hMY : M ≤ Subgroup.normalizer ((⁅M, N⁆ : Subgroup G) : Set G) := le_normalizer_commutator hMM hMN
  have hNY : N ≤ Subgroup.normalizer ((⁅M, N⁆ : Subgroup G) : Set G) := le_normalizer_commutator hNM hNN
  have hMW : M ≤ Subgroup.normalizer ((⁅(⁅M, N⁆ : Subgroup G), M⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hMY hMM
  have hNW : N ≤ Subgroup.normalizer ((⁅(⁅M, N⁆ : Subgroup G), M⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hNY hNM
  have h3 : (⁅(⁅M, M⁆ : Subgroup G), N⁆ : Subgroup G) ≤ ⁅(⁅M, N⁆ : Subgroup G), M⁆ := by
    refine three_subgroups_mod (X := M) (Y := N) (Z := M) hMW hNW hMW le_rfl ?_
    rw [Subgroup.commutator_comm N M]
  rw [glaPComponent_perfect hM] at h3
  refine h3.trans ?_
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mono le_rfl hY

theorem comm_primeCore_bot_of_qs {X M : Subgroup G} (hp : p.Prime) (hM : GLAPComponent p X M)
    (hq : CFSG.Open.IsQuasisimple ↥M) : Xc p M = ⊥ :=
  S9.commutator_eq_bot_of_isQuasisimple hp hM hq

theorem cx_eq_of_mem_zpowers (h : Cfg12 G m p B x L D K) {d : G} (hd : d ∈ Subgroup.zpowers x) (hd1 : d ≠ 1) :
    Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := h.elem.2 x h.xD
  have hord : orderOf x = p := orderOf_eq_prime hxp h.tri.ne_one
  have hdord : orderOf d = p := by
    have h1 : orderOf d ∣ p := hord ▸ orderOf_dvd_of_mem_zpowers hd
    rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hd1
    · exact h2
  have hxd : x ∈ Subgroup.zpowers d := by
    have hle : Subgroup.zpowers d ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hd
    have heq : Subgroup.zpowers d = Subgroup.zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hdord, hord]
    rw [heq]
    exact Subgroup.mem_zpowers x
  have key : ∀ {a b : G}, b ∈ Subgroup.zpowers a → ∀ g : G, g * a = a * g → g * b = b * g := by
    intro a b hb g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute g a from hg) k).eq
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun hg => key hxd g hg, fun hg => key hd g hg⟩

theorem closureIn_le_self {K L : Subgroup G} (hK : K ≤ L) : closureIn K L ≤ L := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  have h1 : GLBConj a K ≤ GLBConj a L := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono a hK
  rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer ha)] at h1

theorem prop127 (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Odd (Nat.card ↥(⁅Ky p K d, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G)) := by
  have hcom := hin.l122.l121.common
  by_cases hdx : d ∈ Subgroup.zpowers x
  ·
    have hcx := cx_eq_of_mem_zpowers h hdx hd1
    have hlay : GLAPLayer p (Subgroup.centralizer ({d} : Set G)) = L := by
      rw [hcx]
      exact h.tri.layer h.ctx
    have hKL : K ≤ L := h.K_le_L
    have hle : (⁅Ky p K d, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G) ≤
        ⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ := by
      refine Subgroup.commutator_mono ?_ le_rfl
      show closureIn K (GLAPLayer p (Subgroup.centralizer ({d} : Set G))) ≤ L
      rw [hlay]
      exact closureIn_le_self hKL
    have h415 := h.ctx.ctx.stage4.1 B x L h.tri.star.1.1
    rw [← hcx] at h415
    exact Odd.of_dvd_nat h415 (Subgroup.card_dvd_of_le hle)
  ·
    obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := ky_family h hcom hd hdx
    by_cases hex : ∃ M ∈ 𝒞, CentMod p M x
    · obtain ⟨M, hM𝒞, hc⟩ := hex
      have hMK : M ≤ Ky p K d := by
        rw [← hC2]
        exact le_biSup (fun M' => M') hM𝒞
      have hMeq := ky_single_of_centMod h hcom hd hdx (hC1 M hM𝒞) hMK hc.1
      have hcov := cover_of_centMod h hcom hd hdx (hC1 M hM𝒞) hMeq hc
      have hKM : K ≤ M := by
        rw [← hMeq]
        exact le_closureIn_self K _
      have hBM : B ≤ Subgroup.normalizer (M : Set G) := by
        rw [← hMeq]
        exact ky_norm h hd
      have hodd := oddCore_of_cover h hin.l122.l121 hin.i1810 hd hd1 (hC1 M hM𝒞) hKM hBM hcov
      rw [hMeq]
      exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le (comm_core_le h.prime (hC1 M hM𝒞)))
    ·
      push Not at hex
      have hbot : (⁅Ky p K d, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G) = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hC2]
        refine iSup₂_le fun M hM𝒞 => ?_
        have hMK : M ≤ Ky p K d := by
          rw [← hC2]
          exact le_biSup (fun M' => M') hM𝒞
        obtain ⟨hS, hN⟩ := nbr_of_not_centMod h hcom hd hdx (hC1 M hM𝒞) hMK (hex M hM𝒞)
        have hqs := (prop122 (⟨h, hS, hN⟩ : NbrCfg G m p B x L D K d M) hin.l122).qs
        have h1 := comm_core_le (d := d) h.prime (hC1 M hM𝒞)
        rw [comm_primeCore_bot_of_qs h.prime (hC1 M hM𝒞) hqs] at h1
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h1)
      rw [hbot, Subgroup.card_bot]
      exact odd_one

end S12

end CFSG.LocalAnalysis.GLTheoremA
