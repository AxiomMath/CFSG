module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofLift
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverSU
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def L212TorusSL : Prop :=
  ∀ {p n : ℕ} {K : Type} [Field K] [Finite K], p.Prime → 5 ≤ n → p ∣ Nat.card K - 1 →
    ∀ s : Matrix.SpecialLinearGroup (Fin n) K, s ^ p = 1 →
      ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* Matrix.SpecialLinearGroup (Fin n) K,
        Function.Injective f ∧ (∀ x, Commute (f x) s) ∧
          ∀ x, f x ∈ LinearFlag.scalars n K → f x = 1

theorem rank_ge_three_of_cover {p : ℕ} (hp : p.Prime) {S L : Type} [Group S] [Group L] [Finite L]
    (φ : S →* L) (hφ : Function.Surjective φ) (Z : Subgroup S) [IsCyclic Z]
    (hZ : Z ≤ center S) (hker : φ.ker ≤ Z) (hcenter : center L ≤ Z.map φ)
    (hnt : center L ≠ ⊥) (hZp : IsPGroup p (center L))
    (htorus : ∀ s : S, s ^ p = 1 →
      ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* S, Function.Injective F ∧
        (∀ x, Commute (F x) s) ∧ ∀ x, F x ∈ Z → F x = 1)
    {d : L} (hd : d ^ p = 1) : 3 ≤ CFSG.Open.pRank p (centralizer ({d} : Set L)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, hsp, c, hc, hφs⟩ := exists_lift_pow_eq_one hp φ hφ Z hZ hker hcenter hnt hZp hd
  obtain ⟨F, hFi, hFc, hFZ⟩ := htorus s hsp
  have hinj : Function.Injective (φ.comp F) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : F x ∈ φ.ker := hx
    have h2 : F x = 1 := hFZ x (hker h1)
    exact hFi (by rw [h2, map_one])
  have hrange : (φ.comp F).range ≤ centralizer ({d} : Set L) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : φ (F x) * φ s = φ s * φ (F x) := by
      rw [← map_mul, ← map_mul, (hFc x).eq]
    have hcc : Commute c (φ (F x)) := ((mem_center_iff.1 hc) (φ (F x))).symm
    have h2 : d = φ s * c⁻¹ := by rw [hφs]; group
    show φ (F x) * d = d * φ (F x)
    rw [h2]
    calc φ (F x) * (φ s * c⁻¹) = (φ (F x) * φ s) * c⁻¹ := by group
      _ = (φ s * φ (F x)) * c⁻¹ := by rw [h1]
      _ = φ s * (φ (F x) * c⁻¹) := by group
      _ = φ s * (c⁻¹ * φ (F x)) := by rw [hcc.inv_left.eq]
      _ = (φ s * c⁻¹) * φ (F x) := by group
  have hcard : Nat.card (Fin 3 → Multiplicative (ZMod p)) = p ^ 3 := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b)
    (fun a => by
      funext i
      change (a i) ^ p = 1
      rw [← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        ofAdd_zero])
    hcard (φ.comp F) hinj hrange

theorem gl83PElementCentralizerRank_of_tori (hGA : CFSG.Open.GriessAllModelsStatement)
    (hTL : L212TorusSL) (hTU : ∀ {p n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP
        K r], p.Prime → 5 ≤ n → Nat.card K = (r ^ f) ^ 2 → p ∣ r ^ f + 1 → ∀ s : StatedSU n (r ^ f)
        K, s ^ p = 1 → ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* StatedSU n (r ^ f) K,
        Function.Injective F ∧ (∀ x, Commute (F x) s) ∧ ∀ x, ((F x : StatedSU n (r ^ f) K) : GL (Fin
        n) K) ∈ StatedScalars (Fin n) K → F x = 1) : GL83PElementCentralizerRank := by
  intro p hp hp5 L _ _ hL hlin hZne hZp d hdp hdz
  haveI := hL.2
  rcases hlin with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
  · have hn5 : 5 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
        exact absurd e.injective.subsingleton (not_subsingleton _)
      · exact hp5.trans (Nat.le_of_dvd hn0 hpn)
    let e' : L ⧸ center L ≃* LinearFlag.projectiveSL n K :=
      e.trans (l212in_projectiveSLEquivStated n K).symm
    obtain ⟨φ, hφ, hφπ⟩ := exists_cover_linear hp hp5 hGA hL hZp (by omega) e'
    obtain ⟨hker, hcenter⟩ := cover_ker_center φ hφ (LinearFlag.proj n K) e' hφπ
    rw [LinearFlag.ker_proj] at hker hcenter
    haveI : IsCyclic (LinearFlag.scalars n K) := by
      rw [LinearFlag.scalars_eq_center]
      exact CFSG.LieType.Steinberg.isCyclic_center_specialLinearGroup n K
    exact rank_ge_three_of_cover hp φ hφ (LinearFlag.scalars n K)
      (LinearFlag.scalars_le_center n K) hker hcenter hZne hZp
      (fun s hs => hTL hp hn5 hpK s hs) hdp
  · have hn5 : 5 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · haveI : Subsingleton (StatedProj (StatedSU 0 q K)) := inferInstance
        exact absurd e.injective.subsingleton (not_subsingleton _)
      · exact hp5.trans (Nat.le_of_dvd hn0 hpn)
    obtain ⟨r, m, hr, hchar, -, hKr⟩ := exists_char_pow_card K
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hKr, hKq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    obtain ⟨φ, hφ, hφπ⟩ := exists_cover_unitary hp hp5 hGA hL hZp hn5 hKq e
    obtain ⟨hker, hcenter⟩ := cover_ker_center φ hφ (QuotientGroup.mk' _) e hφπ
    rw [QuotientGroup.ker_mk'] at hker hcenter
    haveI := isCyclic_scalars_statedSU hKq (by omega : 1 ≤ n)
    exact rank_ge_three_of_cover hp φ hφ _
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) hker hcenter hZne hZp
      (fun s hs => hTU hp hn5 hKq hpq s hs) hdp

end CFSG.LocalAnalysis.RankFourTheoremC
