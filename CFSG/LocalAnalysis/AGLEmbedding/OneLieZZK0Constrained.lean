module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Sylow
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Facts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def StmtCoprimeAutRankTwo : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y N : Type) [Group Y] [Finite Y] [Group N] [Finite N],
    IsPGroup p (⊤ : Subgroup N) → Open.pRank p (⊤ : Subgroup N) ≤ 2 →
    ∀ ρ : Y →* MulAut N, Function.Injective ρ → ∀ m : ℕ, 2 ≤ m →
      p ^ m + 1 ∣ Nat.card Y → False

theorem ReducedNongeneration.pRank_le_two_of_normal {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    {Rb : Sylow p Y} {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {N : Subgroup Y}
    (hN : N.Normal) (hNp : IsPGroup p N) : Open.pRank p N ≤ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hNR : N ≤ (Rb : Subgroup Y) := hNp.le_sylow_of_normal Rb
  have hmem : Subgroup.normalizer (N : Set Y) ≤ GLBWeakCore p (Rb : Subgroup Y) :=
    le_sSup ⟨N, hNR, by omega, hlt.trans_le (pRank_mono p hp le_sup_left), rfl⟩
  apply h.ne_top
  rw [eq_top_iff]
  calc (⊤ : Subgroup Y) = Subgroup.normalizer (N : Set Y) :=
        (Subgroup.normalizer_eq_top_iff.mpr hN).symm
    _ ≤ GLBWeakCore p (Rb : Subgroup Y) := hmem
    _ ≤ Y₀ := h.weakCore_le

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem false_of_hasPrimeConstraint_of_coprimeAut
    (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) (hSC : KFactOneLieSylowCount)
    (hPR : StmtCoprimeAutRankTwo) (hcon : HasPrimeConstraint (G := H₁) p) : False := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  set Jt := ((nclIn H X).subgroupOf H₁).map π₁ with hJt
  obtain ⟨N, hNn, hNp, hCN⟩ := hcon
  have : N.Normal := hNn
  let ρ : Jt →* MulAut N := (MulAut.conjNormal (H := N)).comp Jt.subtype
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have hjC : (j : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
        Subgroup.centralizer (N : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) :
        H₁ ⧸ primeComplementCore (G := H₁) p)) hj
      simp only [ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply, MulAut.one_apply] at h1
      set y : H₁ ⧸ primeComplementCore (G := H₁) p := (j : H₁ ⧸ primeComplementCore (G := H₁) p)
      calc n * y = y * n * y⁻¹ * y := by rw [h1]
        _ = y * n := by group
    exact Subtype.ext (hc.eq_one_of_mem_of_normal hNn hNp (hCN hjC) j.2)
  obtain ⟨Rb₁, -, hred₁⟩ := hc.escape.reducedNongeneration
  have hN2 := hred₁.pRank_le_two_of_normal hNn hNp
  obtain ⟨φ, hφs, -, -⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  obtain ⟨T, -, hKcat, hTnc, hΓ, -⟩ := hd.exists_kFactHyps
  obtain ⟨m, hm⟩ := T.isPGroup'.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    apply hTnc
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rw [pow_zero] at hm
      have : Subsingleton (T : Subgroup K) := (Nat.card_eq_one_iff_unique.mp hm).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hm
      exact isCyclic_of_prime_card hm
  have hcount := hSC K hKs hKnab hKcat p hp hc.escape.ne_two T hTnc hΓ hd.big
  have hdvd : p ^ m + 1 ∣ Nat.card Jt := by
    rw [← hm, ← hcount, Sylow.card_eq_index_normalizer T]
    exact (Subgroup.index_dvd_card _).trans (Subgroup.card_dvd_of_surjective hφs)
  refine hPR p hp hc.escape.ne_two Jt N (hNp.to_subgroup ⊤) ?_ ρ hρ m hm2 hdvd
  rw [← pRank_map_of_injective p hp N.subtype N.subtype_injective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  exact hN2

end D1OneLieKZeroData

end CFSG.AGLEmbedding
