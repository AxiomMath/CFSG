module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12End175
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1a
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndModel

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.Endgame CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.AschbacherTheorem3 CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem sq_eq_one_of_isSylowOf_conj {R T : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRab : ∀ x ∈ R, x ^ 2 = 1) {g : G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    (∀ x ∈ T, x ^ 2 = 1) ∧ Nat.card T = Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRg := J2End.isSylowOf_conj hR g
  obtain ⟨c, -, hc⟩ := exists_rightConjugate_eq_of_isSylowOf hT hRg
  refine ⟨fun x hx => ?_, by rw [hT.card_eq, hR.card_eq, rightConjugate_card]⟩
  rw [← hc] at hx
  have h1 := (mem_rightConjugate_iff _ c x).mp hx
  have h2 := hRab _ ((mem_rightConjugate_iff _ g _).mp h1)
  have h4 : (g * (c * x * c⁻¹) * g⁻¹) ^ 2 = (g * c) * x ^ 2 * (g * c)⁻¹ := by
    rw [sq, sq]
    group
  rw [h4] at h2
  have := congrArg (fun z => (g * c)⁻¹ * z * (g * c)) h2
  simpa [mul_assoc] using this

theorem m12Commutator_mem (x y : ↥autModel) :
    ⁅x, y⁆ ∈ blockGroup.subgroupOf autModel := by
  have h2 := index_blockGroup
  rw [commutatorElement_def, mul_mem_iff_of_index_two h2, mul_mem_iff_of_index_two h2,
    mul_mem_iff_of_index_two h2, inv_mem_iff, inv_mem_iff]
  tauto

theorem false_of_config
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (hc : m12CheckW S Wd m12E0 sG roots nodes cS wcs excs = true)
    (hE : m12EndCheck S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true)
    (hA : standardComponentIsStandard A)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .M12) {g : G}
    (hg : g ∉ normalizer (A : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTN : T ≤ normalizer (A : Set G)) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRab : ∀ x ∈ R, x ^ 2 = 1)
    (hR4 : 4 ≤ Nat.card R) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  obtain ⟨ψ, hψ⟩ := exists_isActionHom m12AutModel hA.1.1 e
  have hcen := m12_yCensusExc hc
  have hc' := hc
  simp only [m12CheckW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨hk, hch⟩, -⟩, -⟩, -⟩ := hc'
  have hF := m12EndFacts_of_check hk hch hE
  obtain ⟨hTab, hTcard⟩ := sq_eq_one_of_isSylowOf_conj hR hRab hT
  have hT4 : 4 ≤ Nat.card T := hTcard ▸ hR4
  have hT1' : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (A : Set G)) :=
    hT.of_le (le_inf hT.le hTN) inf_le_left
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h] at hT4
    simp at hT4
  have hTKN : T ≤ normalizer (K : Set G) := by
    rw [AS76b.normalizer_centralizer_eq hA]
    exact hTN
  obtain ⟨S₀, hS₀, hTS₀⟩ := exists_isSylowOf_le hT.isPGroup (le_sup_right : T ≤ K ⊔ T)
  have hRK : IsSylowOf 2 (S₀ ⊓ K) K :=
    hS₀.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTKN)
  have hTRK : T ≤ normalizer ((S₀ ⊓ K : Subgroup G) : Set G) := fun t ht =>
    Asc76.Sec5.mem_normalizer_inf (le_normalizer (hTS₀ ht)) (hTKN ht)
  set RK := S₀ ⊓ K with hRKdef
  obtain ⟨hRKab, hRKcard⟩ := sq_eq_one_of_isSylowOf_conj (T := RK) (g := 1) hR hRab
    (by rw [rightConjugate_one]; exact hRK)
  have hRK4 : 4 ≤ Nat.card RK := hRKcard ▸ hR4
  have hov : Asc76.Sec5.Overlap A RK g T := ⟨hA, hg, hT1', hT1, hRK, hTRK⟩
  have hRKC : RK ≤ centralizer (T : Set G) := by
    have h1 := hov.card_inf_centralizer
    have h2 : Nat.card RK ≤ Nat.card (RK ⊓ centralizer (T : Set G) : Subgroup G) := by
      rw [h1, hTcard, ← hRKcard]
    exact inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left h2)
  obtain ⟨w, hwR, hw⟩ := exc_of_overlap hA hψ hcen hg hT1' hTab hT4
  obtain ⟨t, htT, htψ⟩ := exists_of_excClass hw hF.mem
  have ht2 : (t : G) ^ 2 = 1 := hTab _ htT
  have htK : (t : G) ∈ rightConjugate K g := hT.le htT
  have htD : ((ψ t : ↥autModel) : Equiv.Perm (Fin 24)) ∈ blockGroup := by
    rw [htψ]
    exact (mem_normalizer_iff.mp
      ((normal_subgroupOf_iff_le_normalizer blockGroup_le_autModel).1 m12_normal hwR) _).mp
      hF.mem_P
  have ht₀1 : permOfArr 24 (m12T0 m12E0) ≠ 1 := by
    intro h1
    obtain ⟨a₀, -, -, hnot₀, -⟩ := hF.exists_conj
    apply hnot₀
    rw [h1, mul_one, inv_mul_cancel]
    exact one_mem _
  have hfpf : ∀ p, ((ψ t : ↥autModel) : Equiv.Perm (Fin 24)) p ≠ p := by
    rw [htψ]
    exact hF.Q_conj w hwR _ (hF.Q_of_mem _ hF.mem ht₀1)
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    have h2 : t = 1 := Subtype.ext h1
    have := hfpf 0
    rw [h2, map_one] at this
    exact this rfl
  obtain ⟨a', ha', ha'e⟩ := hψ.exists_eq (ψ t) htD
  have htAK : (t : G) ∈ A ⊔ K := by
    have hk : a'⁻¹ * (t : G) ∈ K := by
      have h1 : ψ ((⟨a', le_normalizer ha'⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
        rw [map_mul, map_inv, ha'e, inv_mul_cancel]
      simpa using (hψ.eq_one_iff _).mp h1
    have e1 : (t : G) = a' * (a'⁻¹ * t) := by group
    rw [e1]
    exact mul_mem (mem_sup_left ha') (mem_sup_right hk)
  obtain ⟨a, ha, r, hr, htar⟩ := Asc76.Sec5.exists_mul_of_mem_sup_centralizer hRK htAK
    (hTRK htT) (m := 1) (by rw [pow_one]; exact ht2)
  have hrK : r ∈ K := hRK.le hr
  have hat : ψ ⟨a, le_normalizer ha⟩ = ψ t := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
      rw [hψ.eq_one_iff]
      change a⁻¹ * (t : G) ∈ K
      rw [htar, inv_mul_cancel_left]
      exact hrK
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hc2 : (a⁻¹ * t) ^ 2 = 1 := by
    rw [htar, inv_mul_cancel_left]
    exact hRKab r hr
  have hZ := m12_odd_card_center hA e hψ ht2 hfpf ha hat hc2
  have hRKN : RK ≤ normalizer (rightConjugate A g : Set G) := by
    intro x hx
    exact mem_normalizer_conj_of_commute' hA htK ht1 ht2
      (mem_centralizer_iff.mp (hRKC hx) t htT).symm
  exact false_of_endgame_out hA hZ blockGroup_le_autModel
    ((normal_subgroupOf_iff_le_normalizer blockGroup_le_autModel).1 m12_normal)
    m12Commutator_mem hF hψ hcen hg hRK hRKab hRK4 hT hTab hT4 hTN hRKN

end CFSG.ComponentClassification.RankTwoSporadic.M12
