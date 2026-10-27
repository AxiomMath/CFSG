module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.Blueprint

open CFSG.Open CFSG.SectionRank
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_injective scalar_eq_torusDiag
  torusDiag_mem_SL torusDiag_mem_SU)
open CFSG.RankThree.PartTwo.Census (torusEntries torusEntries_of_gt rootsOfUnity_pow_eq_one
  card_fun_rootsOfUnity card_rootsOfUnity_of_dvd prod_torusEntries torusEntries_injective)

theorem le_pRank_statedProj_of_torus {K : Type} [Field K] [Finite K] {n r m : ℕ}
    (hr : r.Prime) (hrK : r ∣ Nat.card Kˣ) (hmn : m < n)
    (hcen : m + 1 < n ∨ ¬ r ∣ n) {H : Subgroup (GL (Fin n) K)}
    (hH : ∀ d : Fin n → Kˣ, (∀ i, d i ^ r = 1) → ∏ i, d i = 1 →
      CFSG.SectionRank.ClassicalEven.torusDiag d ∈ H) :
    m ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj H)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hμ : Nat.card (rootsOfUnity r K) = r := card_rootsOfUnity_of_dvd hr hrK
  let μ := rootsOfUnity r K
  let incl : μ →* Kˣ := μ.subtype
  let d : (Fin m → μ) →* (Fin n → Kˣ) := (incl.compLeft (Fin n)).comp (torusEntries μ m n)
  let ψ : (Fin m → μ) →* GL (Fin n) K := (torusDiag (ι := Fin n)).comp d
  have hd : ∀ (s : Fin m → μ) (i : Fin n), d s i = incl (torusEntries μ m n s i) :=
    fun _ _ => rfl
  have hdr : ∀ (s : Fin m → μ) (i : Fin n), d s i ^ r = 1 := by
    intro s i
    rw [hd, ← map_pow, rootsOfUnity_pow_eq_one, map_one]
  have hprod : ∀ s : Fin m → μ, ∏ i, d s i = 1 := by
    intro s
    have h : ∏ i, d s i = incl (∏ i, torusEntries μ m n s i) := by
      rw [map_prod]
      rfl
    rw [h, prod_torusEntries hmn, map_one]
  have hψ : ∀ s : Fin m → μ, ψ s ∈ H := fun s => hH (d s) (hdr s) (hprod s)
  let N := (StatedScalars (Fin n) K).subgroupOf H
  let ψ' : (Fin m → μ) →* H := ψ.codRestrict H hψ
  let φ : (Fin m → μ) →* StatedProj H := (QuotientGroup.mk' N).comp ψ'
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have hsS : (ψ' s : GL (Fin n) K) ∈ StatedScalars (Fin n) K :=
      Subgroup.mem_subgroupOf.mp hs
    rw [StatedScalars] at hsS
    obtain ⟨c, hc⟩ := hsS
    have hc' : torusDiag (d s) = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
    have hconst : d s = fun _ : Fin n => c :=
      torusDiag_injective (hc'.trans (scalar_eq_torusDiag c))
    have hcr : c ^ r = 1 := by
      have h := hdr s ⟨m, hmn⟩
      rwa [show d s ⟨m, hmn⟩ = c from congrFun hconst _] at h
    have hcn : c ^ n = 1 := by
      have h := hprod s
      rw [hconst, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hc1 : c = 1 := by
      rcases hcen with hlt | hndvd
      · have h1 : d s ⟨m + 1, hlt⟩ = 1 := by
          rw [hd, torusEntries_of_gt s (i := ⟨m + 1, hlt⟩) (by simp), map_one]
        have h := congrFun hconst ⟨m + 1, hlt⟩
        rw [h1] at h
        exact h.symm
      · have hg : c ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr hndvd),
          pow_one] at hg
    have hd1 : d s = 1 := by
      rw [hconst]
      funext i
      exact hc1
    have hte : torusEntries μ m n s = 1 := by
      funext i
      have h2 : (torusEntries μ m n s i : Kˣ) = 1 := by
        have h := congrFun hd1 i
        rwa [hd] at h
      exact Subtype.ext h2
    exact torusEntries_injective hmn.le (hte.trans (map_one (torusEntries μ m n)).symm)
  refine CFSG.SectionRank.le_pRank_of_injective (G := StatedProj H) (A := Fin m → μ)
    hr.one_lt (fun a b => mul_comm' a b) (fun a => ?_) (card_fun_rootsOfUnity hμ) φ hφ le_top
  funext j
  simpa using rootsOfUnity_pow_eq_one (a j)

theorem LieModel.le_pRank_psl_of_dvd {X : Type} [Group X] [Finite X] {n p f r m : ℕ}
    (h : LieModel X .PSL n p f) (hr : r.Prime) (hrq : r ∣ p ^ f - 1) (hmn : m < n)
    (hcen : m + 1 < n ∨ ¬ r ∣ n) : m ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by omega)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrq
  rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact le_pRank_statedProj_of_torus hr hrK hmn hcen fun d _ hd => torusDiag_mem_SL hd

theorem LieModel.le_pRank_psu_of_dvd {X : Type} [Group X] [Finite X] {n p f r m : ℕ}
    (h : LieModel X .PSU n p f) (hr : r.Prime) (hrq : r ∣ p ^ f + 1) (hmn : m < n)
    (hcen : m + 1 < n ∨ ¬ r ∣ n) : m ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, -, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by omega)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hq : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
  have hcard : Nat.card Kˣ = (p ^ f + 1) * (p ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  have hrK : r ∣ Nat.card Kˣ := by
    rw [hcard]
    exact hrq.mul_right _
  rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
  refine le_pRank_statedProj_of_torus hr hrK hmn hcen fun d hdr hd => ?_
  refine torusDiag_mem_SU hq hd (funext fun i => ?_)
  simp only [Pi.pow_apply, Pi.one_apply]
  obtain ⟨k, hk⟩ := hrq
  rw [hk, pow_mul, hdr i, one_pow]

end CFSG.Blueprint
