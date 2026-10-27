module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem SPLMSide.mem_pCore_of_comm_fitting_layer {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {t : Y} (hD : IsPGroup p (Subgroup.zpowers t))
    (hF : ∀ y ∈ fittingSubgroup Y, t * y = y * t)
    (hE : ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → ∀ a ∈ Λ, t * a = a * t) :
    t ∈ CFSG.pCore p Y := by
  have hFs : generalizedFitting Y ≤ Subgroup.centralizer ({t} : Set Y) := by
    refine sup_le (fun y hy => ?_) (sSup_le fun Λ hΛ y hy => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro h rfl
      exact hF y hy
    · rw [Subgroup.mem_centralizer_iff]
      rintro h rfl
      exact hE Λ hΛ y hy
  have htC : t ∈ Subgroup.centralizer (generalizedFitting Y : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (Subgroup.mem_centralizer_iff.mp (hFs hh) t rfl).symm
  have hCFs := CFSG.centralizer_generalizedFitting_le Y
  have hFsN : (generalizedFitting Y).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Y)
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  have hCcomm : ∀ a ∈ Subgroup.centralizer (generalizedFitting Y : Set Y),
      ∀ b ∈ Subgroup.centralizer (generalizedFitting Y : Set Y), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a (hCFs ha)
  have hCnil : Group.IsNilpotent (Subgroup.centralizer (generalizedFitting Y : Set Y)) := by
    have : IsMulCommutative (Subgroup.centralizer (generalizedFitting Y : Set Y)) :=
      ⟨⟨fun a b => Subtype.ext (hCcomm _ a.2 _ b.2)⟩⟩
    infer_instance
  have hCF : Subgroup.centralizer (generalizedFitting Y : Set Y) ≤ fittingSubgroup Y :=
    CFSG.LocalCores.fitting_characteristic.2.2 _ inferInstance hCnil
  exact CFSG.ABGLocalTools.le_pCore_of_isPGroup_of_le_fitting hD
    ((Subgroup.zpowers_le.mpr htC).trans hCF) (Subgroup.mem_zpowers t)

theorem d1SPLPieceLemmaT_holds : D1SPLPieceLemmaT := by
  intro G _ _ p P M H R Rbar K z D hzM hCz hBl hZK T₀ c₀ hc₀ r hTo t ht hE
  have hp : p.Prime := D.data.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Oz := GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) with hOz
  have hq : ∀ q : ℕ, q.Prime → ∀ y ∈ CFSG.pCore q (↥M ⧸ CFSG.pCore 2 ↥M), t * y = y * t := by
    intro q hqp y hy
    by_cases hq2 : q = 2
    · subst hq2
      rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hy
      rw [hy, one_mul, mul_one]
    by_cases hqp' : q = p
    · subst hqp'
      rw [hBl.pcore] at hy
      exact hTo.T_X t ht y hy
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨m, hmC, hmy⟩ := hCz.lift y (hZK q hqp hq2 hqp' hy)
    set N : Subgroup G := ((CFSG.pCore q (↥M ⧸ CFSG.pCore 2 ↥M)).comap mk).map M.subtype ⊓
      Subgroup.centralizer ({z} : Set G) with hN
    have hNle : N ≤ Subgroup.centralizer ({z} : Set G) ⊓ M := by
      rintro n ⟨⟨n', -, rfl⟩, hnC⟩
      exact ⟨hnC, n'.2⟩
    have hNnorm : ∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      rintro g ⟨hgC, hgM⟩ n ⟨⟨n', hn', rfl⟩, hnC⟩
      refine ⟨⟨⟨g, hgM⟩ * n' * (⟨g, hgM⟩ : M)⁻¹, ?_, rfl⟩,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC hnC) (Subgroup.inv_mem _ hgC)⟩
      have hnorm := (CFSG.pCore_normal (p := q) (G := ↥M ⧸ CFSG.pCore 2 ↥M)).conj_mem _ hn'
        (mk ⟨g, hgM⟩)
      simpa [Subgroup.mem_comap, map_mul, map_inv] using hnorm
    have hNq : IsPGroup q N := by
      rintro ⟨n, hn⟩
      obtain ⟨⟨n', hn', hnn'⟩, hnC⟩ := hn
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := q) (G := ↥M ⧸ CFSG.pCore 2 ↥M)) ⟨_, hn'⟩
      have ha' : mk (n' ^ q ^ a) = 1 := by
        have := congrArg Subtype.val ha
        simpa [map_pow] using this
      have hmem : n ^ q ^ a ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) := by
        refine ⟨⟨n' ^ q ^ a, ?_, by rw [← hnn']; simp⟩,
          Subgroup.pow_mem _ hnC _⟩
        rw [hmk, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at ha'
        rw [SetLike.mem_coe]
        exact ha'
      rw [hCz.twoCore_inf, Subgroup.mem_bot] at hmem
      exact ⟨a, Subtype.ext (by simpa using hmem)⟩
    have hNcop : p.Coprime (Nat.card N) := by
      obtain ⟨k, hk⟩ := hNq.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hqp).mpr (Ne.symm hqp'))
    have hmO : (m : G) ∈ Oz := hCz.normal_le N hNle hNnorm hNcop
      ⟨⟨m, by change mk m ∈ CFSG.pCore q _; rw [hmy]; exact hy, rfl⟩, hmC⟩
    have hyO : y ∈ barM M Oz := ⟨m, Subgroup.mem_subgroupOf.mpr hmO, hmy⟩
    exact hTo.T_O t ht y hyO
  have hF : ∀ y ∈ fittingSubgroup (↥M ⧸ CFSG.pCore 2 ↥M), t * y = y * t := by
    intro y hy
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hy
    have hle : (⨆ q : (Nat.card (↥M ⧸ CFSG.pCore 2 ↥M)).primeFactors,
        CFSG.pCore (q : ℕ) (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.centralizer ({t} : Set _) :=
      iSup_le fun q x hx => by
        rw [Subgroup.mem_centralizer_iff]
        rintro h rfl
        exact hq q (Nat.prime_of_mem_primeFactors q.2) x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hy) t rfl
  rw [← hBl.pcore]
  exact SPLMSide.mem_pCore_of_comm_fitting_layer (hTo.T_p.to_le (Subgroup.zpowers_le.mpr ht)) hF hE

end CFSG.AGLEmbedding
