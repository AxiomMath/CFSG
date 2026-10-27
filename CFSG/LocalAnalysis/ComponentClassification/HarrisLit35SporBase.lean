module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Triv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporData
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Spor

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem exists_isComponent_congr' {Y : Type} [Group Y] {H H' : Subgroup Y} (hH : H = H')
    {Q : (X : Type) → [Group X] → Prop} {B : Subgroup ↥H} (hB : IsComponent B) (hQ : Q ↥B) :
    ∃ B' : Subgroup ↥H', IsComponent B' ∧ Q ↥B' := by
  subst hH
  exact ⟨B, hB, hQ⟩

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem false_of_center_eq_bot (h : Config G p w v L K)
    (hZ : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥) : False := by
  have h2 := h.even_card_center
  rw [hZ, card_bot] at h2
  exact absurd h2 (by decide)

theorem false_of_noTwoCover (h : Config G p w v L K)
    (hN : GH74.Generic.NoTwoCover (↥K ⧸ Open.fusionZStar ↥K)) : False := by
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  exact h.false_of_center_eq_bot (hN _ h.quasisimple_quot
    (N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2)) ⟨eZ.symm⟩)

theorem false_of_odd_hopfMultiplier (h : Config G p w v L K) {X : Type} [Group X]
    (e : ↥K ⧸ Open.fusionZStar ↥K ≃* X)
    (hX : Odd (Nat.card (RankThree.PerfectCover.hopfMultiplier X))) : False := by
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hd := GH74.Generic.card_center_dvd_hopfMultiplier h.quasisimple_quot (eZ.symm.trans e)
  exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hX hd)) h.even_card_center

theorem exists_comp (h : Config G p w v L K) {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s)
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* NativeSporadic.Carrier s) :
    (∃ t : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K), orderOf t = 2 ∧
      ∃ B : Subgroup ↥(centralizer ({t} : Set ((↥K ⧸ pPrimeCore 2 ↥K) ⧸
        center (↥K ⧸ pPrimeCore 2 ↥K)))), IsComponent B ∧
        ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧ LieModel (↥B ⧸ center ↥B) .PSL 2 p k) ∨
    (∃ α : MulAut ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)), α * α = 1 ∧
      α ∉ OuterAutomorphisms.inner ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      ∃ B : Subgroup ↥(Sporadic.Schreier.fixSub α), IsComponent B ∧
        ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧ LieModel (↥B ⧸ center ↥B) .PSL 2 p k) := by
  have hq := h.quasisimple_quot
  have hS : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hna := hq.2.2
  have hsq : quotAut h.tau * quotAut h.tau = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hσ2 : orderOf (quotAut h.tau) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq) h.quotAut_tau_ne_one
  have hO := N36.pPrimeCore_fixedPoints_eq_bot_of_mulAut hna
    (fun i hi => N36.mulAut_oddCore_eq_bot hodd hna e i hi) hσ2
  obtain ⟨hB, hL⟩ := h.isComponent_hat hO
  have hZ := CatLeaf.center_eq_bot_of_simple hna
  by_cases hinn : quotAut h.tau ∈ innAut ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
  · left
    obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (Hin.conj_injective_of_center hZ) t, ht]
      exact hσ2
    have heq : fixedPoints (quotAut h.tau) = centralizer ({t} : Set ((↥K ⧸ pPrimeCore 2 ↥K) ⧸
        center (↥K ⧸ pPrimeCore 2 ↥K))) := by
      rw [Hin.centralizer_eq_fixedPoints_conj, ht]
    exact ⟨t, ht2, exists_isComponent_congr' (Q := fun X _ => ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧
      LieModel (X ⧸ center X) .PSL 2 p k) heq hB hL⟩
  · right
    exact ⟨_, hsq, hinn, exists_isComponent_congr' (Q := fun X _ => ∃ k : ℕ, 1 ≤ k ∧
      5 ≤ p ^ k ∧ LieModel (X ⧸ center X) .PSL 2 p k) (Hin.fixSub_eq_fixedPoints _).symm hB hL⟩

end Config

theorem rowFor_spor_of_compData {s : TauCeti.SporadicName} (hd : SporCompData s) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y s := by
  intro G _ _ p w v L K h ⟨e⟩
  exfalso
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hq := h.quasisimple_quot
  have hsmall : ∀ (X : Type) [Group X], (∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧
      LieModel (X ⧸ center X) .PSL 2 p k) → SmallCentralQuotient X :=
    fun X _ ⟨k, hk, hs5, hm⟩ => Or.inl ⟨p, k, h.prime, h.ne_two, hk, hs5, hm⟩
  rcases h.exists_comp hd.oddCore (eZ.symm.trans e) with ⟨t, ht2, B, hB, hL⟩ |
    ⟨α, hsq, hinn, B, hB, hL⟩
  · exact hd.inner _ hq.2.1 hq.2.2 ⟨eZ.symm.trans e⟩ t ht2 B hB (hsmall _ hL)
  · exact hd.outer _ hq.2.1 hq.2.2 ⟨eZ.symm.trans e⟩ α hsq hinn B hB (hsmall _ hL)

theorem rowFor_spor_of_card {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s) (S : Set ℕ)
    (hS : ∀ q N : ℕ, N ∈ S → q * (q ^ 2 - 1) ≠ 2 * N)
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → ∀ B : Subgroup ↥(centralizer ({t} : Set G)), IsComponent B →
        Nat.card (↥B ⧸ center ↥B) ∈ S)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
        α ∉ OuterAutomorphisms.inner G → ∀ B : Subgroup ↥(Sporadic.Schreier.fixSub α),
          IsComponent B → Nat.card (↥B ⧸ center ↥B) ∈ S) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y s := by
  intro G _ _ p w v L K h ⟨e⟩
  exfalso
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hq := h.quasisimple_quot
  have hcard : ∀ (X : Type) [Group X], (∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧
      LieModel (X ⧸ center X) .PSL 2 p k) →
        ∃ q : ℕ, q * (q ^ 2 - 1) = 2 * Nat.card (X ⧸ center X) :=
    fun X _ ⟨k, _, _, hm⟩ => ⟨p ^ k, by
      rw [GSThmB.card_of_lieModel_psl_two h.ne_two hm]
      exact (two_mul_ordA_one (h.prime.eq_two_or_odd'.resolve_left h.ne_two).pow).symm⟩
  rcases h.exists_comp hodd (eZ.symm.trans e) with ⟨t, ht2, B, hB, hL⟩ |
    ⟨α, hsq, hinn, B, hB, hL⟩
  · obtain ⟨q, hq'⟩ := hcard _ hL
    exact hS q _ (hin _ ⟨eZ.symm.trans e⟩ t ht2 B hB) hq'
  · obtain ⟨q, hq'⟩ := hcard _ hL
    exact hS q _ (hout _ hq.2.1 hq.2.2 ⟨eZ.symm.trans e⟩ α hsq hinn B hB) hq'

end CFSG.ComponentClassification.HarrisLit.L35
