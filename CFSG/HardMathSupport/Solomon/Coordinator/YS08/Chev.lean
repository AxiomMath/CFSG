module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.AltDown
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

theorem sl3Eps_facts {p : ℕ} {X : Type} [Group X] [Finite X] (h : SL3EpsOfChar p X) :
    Nat.card (Subgroup.center X) = 3 ∧ 60480 ≤ Nat.card X := by
  rcases h with ⟨F, hF, hfin, -, hmod, ⟨e⟩⟩ | ⟨F, hF, hfin, q, -, hcard, hq3, hq2, ⟨e⟩⟩
  · have hnt : Nontrivial F := inferInstance
    have hq1 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.2 hnt
    have hq4 : 4 ≤ Nat.card F := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact CFSG.Open.StatedCenterThree.card_center_statedSL_three
        (Nat.dvd_of_mod_eq_zero (by omega))
    · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
      set r := Nat.card F with hr
      have h64 : 64 ≤ r ^ 3 := by
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ r ^ 3 := Nat.pow_le_pow_left hq4 3
      have h16 : 16 ≤ r ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ r ^ 2 := Nat.pow_le_pow_left hq4 2
      have h1 : 15 ≤ r ^ 2 - 1 := by omega
      have h2 : 63 ≤ r ^ 3 - 1 := by omega
      calc 60480 = 64 * 15 * 63 := by norm_num
        _ ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h64 h1) h2
  · have hq5 : 5 ≤ q := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hcard
        (Nat.dvd_of_mod_eq_zero (by omega))
    · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hcard]
      have h125 : 125 ≤ q ^ 3 := by
        calc 125 = 5 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
      have h25 : 25 ≤ q ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
      have h1 : 24 ≤ q ^ 2 - 1 := by omega
      have h2 : 126 ≤ q ^ 3 + 1 := by omega
      calc 60480 ≤ 125 * 24 * 126 := by norm_num
        _ ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h125 h1) h2

theorem l3EpsAlt_holds :
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      Lemma25Ns.IsAltType (Y ⧸ Subgroup.center Y) → ∀ α : MulAut Y, α ^ 3 = 1 →
      ∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J →
        ∀ p : ℕ, ¬ SL3EpsOfChar p (barOf 3 J) := by
  intro Y _ _ hY hAlt α hα J hJ p hSL
  have hKq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  obtain ⟨hZ3, hbig⟩ := sl3Eps_facts hSL
  have hLZ : Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) * 3 = Nat.card (barOf 3 J) := by
    have h := (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (barOf 3 J))).symm
    rwa [hZ3] at h
  rcases alt_down_core hY hAlt hα hJ with hle | ⟨β, _, _, h5, ⟨eA⟩⟩
  · omega
  · have hnt : Nontrivial β := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    have h2 := two_mul_nat_card_alternatingGroup (α := β)
    rw [Nat.card_perm, ← Nat.card_congr eA.toEquiv] at h2
    have hn8 : 8 ≤ Nat.card β := by
      by_contra hlt
      have h1 : (Nat.card β).factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
      have h7 : (7 : ℕ).factorial = 5040 := by decide
      omega
    obtain ⟨m, hm⟩ : ∃ m, Nat.card β = m + 2 := ⟨Nat.card β - 2, by omega⟩
    have hcardβ : Fintype.card β = m + 2 := by rw [← Nat.card_eq_fintype_card]; exact hm
    let η : barOf 3 J →* ↥(alternatingGroup (Fin (m + 2))) :=
      ((Equiv.altCongrHom (Fintype.equivFinOfCardEq hcardβ)).toMonoidHom.comp
        eA.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center (barOf 3 J)))
    have hη : Function.Surjective η :=
      ((Equiv.altCongrHom (Fintype.equivFinOfCardEq hcardβ)).surjective.comp
        eA.surjective).comp (QuotientGroup.mk'_surjective _)
    have hker : η.ker = Subgroup.center (barOf 3 J) := by
      ext x
      simp only [MonoidHom.mem_ker, η, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, map_eq_one_iff _ (MulEquiv.injective _)]
      exact QuotientGroup.eq_one_iff x
    haveI : Group.IsPerfect (barOf 3 J) := ⟨hKq.1⟩
    have hodd : Odd (Nat.card η.ker) := by rw [hker, hZ3]; decide
    have := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hη hker.le hodd
    rw [hker, hZ3] at this
    omega

@[expose] def L3EpsSporBranch (s : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ α : MulAut Y, α ^ 3 = 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (Lemma510Ns.fixSub α) J → ∀ p : ℕ, ¬ SL3EpsOfChar p (barOf 3 J)

@[expose] def L3EpsLieBranch : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    ∀ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ α : MulAut Y, α ^ 3 = 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (Lemma510Ns.fixSub α) J → ∀ p : ℕ, p.Prime →
        SL3EpsOfChar p (barOf 3 J) → IsChevIndexOfChar p idx.1

theorem chev_of_branches (hS : ∀ s, L3EpsSporBranch s) (hL : L3EpsLieBranch)
    (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKK : CFSG.Open.IsKGroup ↥K) (b : Y)
    (hb : b ∈ Subgroup.normalizer (K : Set Y)) (hb3 : b ^ 3 ∈ Subgroup.centralizer (K : Set Y))
    (J : Subgroup Y) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J)
    (p : ℕ) (hp : p.Prime) (hJL : SL3EpsOfChar p (↥J ⧸ GLAPPrimeCore 3 ↥J)) :
    IsChevOfChar p (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨α, J', hα, hJ', ⟨eJ⟩⟩ := component_to_aut K hb hb3 hJ
  have hJL' : SL3EpsOfChar p (barOf 3 J') := by
    rcases hJL with ⟨F, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨F, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨e⟩⟩
    · exact Or.inl ⟨F, hF, hfin, hchar, hmod, ⟨eJ.trans e⟩⟩
    · exact Or.inr ⟨F, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨eJ.trans e⟩⟩
  obtain ⟨hnab, i, ⟨e⟩⟩ := I1420.catalog_of_quasisimple hKq hKK
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, c, hac⟩ := hnab
    apply hac
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact absurd hJL' (l3EpsAlt_holds ↥K hKq ⟨n, ⟨e⟩⟩ α hα J' hJ' p)
  | lie idx => exact ⟨idx, hL ↥K hKq idx ⟨e⟩ α hα J' hJ' p hp hJL', ⟨e⟩⟩
  | sporadic s => exact absurd hJL' (hS s ↥K hKq ⟨e⟩ α hα J' hJ' p)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
