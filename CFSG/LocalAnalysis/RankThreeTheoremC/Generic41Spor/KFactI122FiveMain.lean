module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI122FiveDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI122FiveQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI122FiveOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.Open.MonsterY443Finiteness
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut pGoodOut_of_catalogGroup d4PGood)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd)

theorem exists_conj_mem_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p X) {S : Subgroup X} (hS : IsPGroup p S) :
    ∃ g : X, ∀ s ∈ S, g * s * g⁻¹ ∈ (Q : Subgroup X) := by
  obtain ⟨Q', hSQ'⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q' Q
  refine ⟨g, fun s hs => ?_⟩
  have hgQ : ((g • Q' : Sylow p X) : Subgroup X) =
      (Q' : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hg, hgQ]
  exact ⟨s, hSQ' hs, rfl⟩

theorem sporOrd_five_dvd (s : TauCeti.SporadicName) (h : 5 ^ 5 ∣ sporOrd s) :
    5 ^ 6 ∣ sporOrd s := by
  revert h
  cases s <;> decide

theorem five_pow_six_dvd_factorial (n : ℕ) (h : 5 ^ 5 ∣ n.factorial) : 5 ^ 6 ∣ n.factorial := by
  by_cases hn : n < 25
  · exfalso
    have h1 : n.factorial ∣ (24 : ℕ).factorial := Nat.factorial_dvd_factorial (by omega)
    have h2 : ¬ 5 ^ 5 ∣ (24 : ℕ).factorial := by decide
    exact h2 (h.trans h1)
  · have h1 : (25 : ℕ).factorial ∣ n.factorial := Nat.factorial_dvd_factorial (by omega)
    have h2 : 5 ^ 6 ∣ (25 : ℕ).factorial := by decide
    exact h2.trans h1

section Heavy

theorem pGoodOut_five_of_not_diag {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K) (hd : ¬ FiveDiagType K) :
    PGoodOut 5 K :=
  pGoodOut_of_catalogGroup hnab hcat Nat.prime_five le_rfl
    (fun {n ℓ f} hm hdvd => hd (Or.inl ⟨n, ℓ, f, hm, hdvd⟩))
    (fun {n ℓ f} hm hdvd => hd (Or.inr ⟨n, ℓ, f, hm, hdvd⟩)) d4PGood

theorem kFactI122Five_of_inputs (hR1 : Sylow5OmegaLie) (hR2 : FiveDiagSylow) :
    KFactI122Five := by
  intro X _ _ K hKn hs hnab hcat hKC Q A B y hQcard hAQ hBQ hAc hBc hAcard hBcard hAB hcomm hyQ
    hyord hyAB hgen hyA hyB hZ
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup K := hs
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, hEQ, hEcomm, hEcard, hEmem, hQnab⟩ :=
    fiveShape_exists_elem (Q : Subgroup X) A B y hAQ hBQ hAc hBc hAcard hBcard hAB hcomm hyQ hyord
      hyAB hgen hyA hyB hZ
  have hconj : ∀ S : Subgroup K, IsPGroup 5 S →
      ∃ g : X, ∀ s ∈ S, g * (s : X) * g⁻¹ ∈ (Q : Subgroup X) := by
    intro S hS
    obtain ⟨g, hg⟩ := exists_conj_mem_sylow Q (hS.map K.subtype)
    exact ⟨g, fun s hs => hg _ ⟨s, hs, rfl⟩⟩
  have hSle : ∀ S : Sylow 5 K, Nat.card (S : Subgroup K) ≤ 5 ^ 5 := by
    intro S
    obtain ⟨g, hg⟩ := hconj (S : Subgroup K) S.isPGroup'
    rw [← hQcard]
    refine Nat.card_le_card_of_injective
      (fun s : (S : Subgroup K) => (⟨g * ((s : K) : X) * g⁻¹, hg _ s.2⟩ : (Q : Subgroup X))) ?_
    intro s t hst
    have h1 := congrArg Subtype.val hst
    have h2 : ((s : K) : X) = ((t : K) : X) := by simpa using h1
    exact Subtype.ext (Subtype.ext h2)
  by_cases hdiag : FiveDiagType K
  · exfalso
    obtain ⟨S⟩ : Nonempty (Sylow 5 K) := inferInstance
    obtain ⟨g, hg⟩ := hconj (S : Subgroup K) S.isPGroup'
    rcases hR2 K hs hnab hcat hdiag S with h6 | ⟨h4, hexp⟩
    · have := hSle S
      have h56 : 5 ^ 5 < 5 ^ 6 := by norm_num
      omega
    · have hmem : ∀ s : (S : Subgroup K), g * ((s : K) : X) * g⁻¹ ∈ E := by
        intro s
        refine hEmem _ (hg _ s.2) ?_
        have h5 : ((s : K)) ^ 5 = 1 := hexp _ s.2
        have h5' : ((s : K) : X) ^ 5 = 1 := by
          have := congrArg (fun k : K => (k : X)) h5
          simpa using this
        rw [conj_pow]
        simp [h5']
      have hle : Nat.card (S : Subgroup K) ≤ Nat.card E := by
        refine Nat.card_le_card_of_injective
          (fun s : (S : Subgroup K) => (⟨g * ((s : K) : X) * g⁻¹, hmem s⟩ : E)) ?_
        intro s t hst
        have h1 := congrArg Subtype.val hst
        have h2 : ((s : K) : X) = ((t : K) : X) := by simpa using h1
        exact Subtype.ext (Subtype.ext h2)
      have h125 : Nat.card E ≤ 5 ^ 3 := hEcard
      have h54 : 5 ^ 3 < 5 ^ 4 := by norm_num
      omega
  · have hP : PGoodOut 5 K := pGoodOut_five_of_not_diag hnab hcat hdiag
    by_cases hQK : (Q : Subgroup X) ≤ K
    · exfalso
      let S₀ : Subgroup K := (Q : Subgroup X).subgroupOf K
      have hS₀card : Nat.card S₀ = 5 ^ 5 := by
        rw [← hQcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
      have hS₀p : IsPGroup 5 S₀ := IsPGroup.of_card (n := 5) hS₀card
      obtain ⟨S, hS₀S⟩ := hS₀p.exists_le_sylow
      have hSeq : (S : Subgroup K) = S₀ :=
        (Subgroup.eq_of_le_of_card_ge hS₀S (by rw [hS₀card]; exact hSle S)).symm
      have hSord : Nat.card (S : Subgroup K) = 5 ^ 5 := by rw [hSeq, hS₀card]
      have hfac : (Nat.card K).factorization 5 = 5 := by
        have h1 := Sylow.card_eq_multiplicity S
        rw [hSord] at h1
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1.symm
      have hd5 : 5 ^ 5 ∣ Nat.card K :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').2 hfac.ge
      have hnd6 : ¬ 5 ^ 6 ∣ Nat.card K := fun h => by
        have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 h
        omega
      rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge K hnab hcat) with
        ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
      · obtain ⟨a, b, hab⟩ := hnab
        exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
      · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
        have hcard : Nat.card K = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
        have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
          have h2' := two_mul_nat_card_alternatingGroup (α := Fin n)
          rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
            Fintype.card_fin] at h2'
          exact h2'
        have h3 : 5 ^ 5 ∣ n.factorial := by
          rw [← h2]
          exact hcard ▸ hd5 |>.mul_left 2
        have h4 := five_pow_six_dvd_factorial n h3
        rw [← h2] at h4
        exact hnd6 (hcard ▸ (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h4))
      · have hmemQ : ∀ k : K, k ∈ (S : Subgroup K) → (k : X) ∈ (Q : Subgroup X) := by
          intro k hk
          have : k ∈ S₀ := hSeq ▸ hk
          exact this
        have hclos : ∀ c ∈ Subgroup.closure {g : K | g ∈ (S : Subgroup K) ∧ g ^ 5 = 1},
            (c : X) ∈ E := by
          intro c hc
          induction hc using Subgroup.closure_induction with
          | mem g hg =>
            refine hEmem _ (hmemQ g hg.1) ?_
            have := congrArg (fun k : K => (k : X)) hg.2
            simpa using this
          | one => simpa using E.one_mem
          | mul a b _ _ ha hb => simpa using E.mul_mem ha hb
          | inv a _ ha => simpa using E.inv_mem ha
        have hcommC : IsMulCommutative
            (Subgroup.closure {g : K | g ∈ (S : Subgroup K) ∧ g ^ 5 = 1}) :=
          ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
            have := hEcomm _ (hclos a a.2) _ (hclos b b.2)
            simpa using this))⟩⟩
        have hcommS := hR1 K hs hnab hcat ⟨t, n, ℓ, f, hadm, hmodel⟩ S hSord hcommC
        apply hQnab
        intro a ha b hb
        have haK : a ∈ K := hQK ha
        have hbK : b ∈ K := hQK hb
        have haS : (⟨a, haK⟩ : K) ∈ (S : Subgroup K) := hSeq ▸ ha
        have hbS : (⟨b, hbK⟩ : K) ∈ (S : Subgroup K) := hSeq ▸ hb
        have := isMulCommutative_iff.mp hcommS ⟨⟨a, haK⟩, haS⟩ ⟨⟨b, hbK⟩, hbS⟩
        simpa using congrArg (fun k : (S : Subgroup K) => ((k : K) : X)) this
      · have hcard : Nat.card K = sporOrd s :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card s)
        exact hnd6 (hcard ▸ sporOrd_five_dvd s (hcard ▸ hd5))
    · obtain ⟨q, hqQ, hqK⟩ := SetLike.not_le_iff_exists.1 hQK
      have hq5 : ∃ k : ℕ, q ^ (5 ^ k) = 1 := by
        obtain ⟨k, hk⟩ := Q.isPGroup' ⟨q, hqQ⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      exact exists_normal_index_pow_of_pGoodOut Nat.prime_five K hKC hP hq5 hqK

end Heavy

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
