module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilp
public import Certificates.Certificate2007
public import Certificates.Certificate2013
public import Certificates.Certificate2014

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

structure Q3ModelData (K₀ : Type) [Group K₀] (G : Type) [Group G] where
  M : AutModel K₀ G
  PA : M.P ≤ M.A
  cent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1
  card : Nat.card M.A = 2 * Nat.card M.P
  m : ℕ
  hm : Odd m
  hK : ∀ d : ℕ, d ∣ Nat.card K₀ → Odd d → d ∣ m
  noNilp : ∀ s ∈ M.A, s * s = 1 → ∃ x₁ ∈ M.P, ∃ x₂ ∈ M.P, x₁ * s = s * x₁ ∧
    x₂ * s = s * x₂ ∧ x₁ ^ m = 1 ∧ x₂ ^ m = 1 ∧ (x₁ * x₂) ^ m ≠ 1
  s₀ : G
  adm : ∀ s ∈ M.A, s * s = 1 → s ∉ M.P →
    5 ∣ Nat.card ↥(M.P ⊓ centralizer ({s} : Set G)) → ∃ k ∈ M.A, k * s₀ * k⁻¹ = s
  L : Subgroup G
  commL : ⁅M.P ⊓ centralizer ({s₀} : Set G), M.P ⊓ centralizer ({s₀} : Set G)⁆ = L
  cardL : Nat.card L = 360
  oddL : ∀ N : Subgroup G, N ≤ L → (∀ x ∈ L, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
    Odd (Nat.card N) → N = ⊥
  Q₀ : Subgroup G
  Q₀le : Q₀ ≤ M.A ⊓ centralizer ({s₀} : Set G)
  cardCA : Nat.card ↥(M.A ⊓ centralizer ({s₀} : Set G)) = 2 ^ 5 * 45
  cardQ₀ : Nat.card Q₀ = 2 ^ 5
  g₀ : G
  g₀P : g₀ ∈ M.P
  g₀N : ∀ q ∈ Q₀, g₀ * q * g₀⁻¹ ∈ Q₀
  g₀Q : g₀ ∉ Q₀
  g₀2 : g₀ * g₀ ∈ Q₀
  g₀σ : s₀ * (g₀⁻¹ * s₀ * g₀) ∈ M.P

theorem odd_dvd_of_dvd_mul {d m : ℕ} (hd : d ∣ 2 ^ 6 * m) (hdo : Odd d) : d ∣ m :=
  (Nat.Coprime.pow_right 6 (Odd.coprime_two_right hdo)).dvd_of_dvd_mul_left hd

namespace A8

noncomputable def q3Data {K₀ : Type} [Group K₀] (e : K₀ ≃* alternatingGroup (Fin 8)) :
    Q3ModelData K₀ (Equiv.Perm (Fin 8)) := by
  classical
  let M := (exists_model e).choose
  have hP : M.P = QA8.originalSubgroup := (exists_model e).choose_spec.1
  have hA : M.A = QS8.originalSubgroup := (exists_model e).choose_spec.2
  have hK : Nat.card K₀ = 2 ^ 6 * 315 := by
    rw [Nat.card_congr e.toEquiv, card_alt8]
    norm_num
  exact
    { M := M
      PA := by rw [hP, hA]; exact P_le_A
      cent := by rw [hP, hA]; exact cent_triv
      card := by rw [hP, hA]; exact card_A_eq
      m := 315
      hm := by decide
      hK := fun d hd hdo => odd_dvd_of_dvd_mul (hK ▸ hd) hdo
      noNilp := by rw [hP, hA]; exact fun s hs hs2 => noNilp_fact hs hs2
      s₀ := s8
      adm := by
        rw [hP, hA]
        intro s hs hs2 hsP h5
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 5 h5
        rw [Subgroup.orderOf_mk] at hxo
        have hx5 : x ∈ five8 := by
          rw [five8, List.mem_filter, mem_elemsT QA8 QA8_ok]
          refine ⟨hx.1, ?_⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
            decide_eq_false_iff_not]
          exact ⟨hxo ▸ pow_orderOf_eq_one x, fun h1 => by rw [h1, orderOf_one] at hxo; omega⟩
        obtain ⟨k, hk, hks⟩ := exists_conj_of_admCheck QA8_ok adm_ok
          ((mem_elemsT QS8 QS8_ok s).2 hs) hs2 hsP hx5 (mem_centralizer_singleton_iff.1 hx.2)
        exact ⟨k, admConj_mem k hk, hks⟩
      L := QL8.originalSubgroup
      commL := by rw [hP]; exact commutator_C0
      cardL := card_QL8
      oddL := L_oddNormal
      Q₀ := QQ8.originalSubgroup
      Q₀le := by rw [hA]; exact QQ8_le
      cardCA := by rw [hA]; exact card_CA0
      cardQ₀ := card_QQ8
      g₀ := g08
      g₀P := by rw [hP]; exact g08_mem
      g₀N := g08_norm
      g₀Q := g08_not_mem
      g₀2 := g08_sq
      g₀σ := by rw [hP]; exact g08_sigma }

end A8

section Generic

variable {K₀ : Type} [Group K₀] {G : Type} [Group G]

theorem q3Out_of_data [Finite K₀] (D : Q3ModelData K₀ G) (α : MulAut K₀)
    (hα : Cat8.IsAdm K₀ α) :
    Cat8.Inn K₀ ⊔ zpowers α = ⊤ :=
  sup_zpowers_eq_top_of_not_mem D.M D.PA D.cent D.card α hα.out

theorem q3NoNilp_of_data [Finite K₀] (D : Q3ModelData K₀ G) (α : MulAut K₀) (hα : α * α = 1) :
    ¬ ∃ N : Subgroup K₀, N ≤ Eight.fixSubgroup α ∧
      (N.subgroupOf (Eight.fixSubgroup α)).Normal ∧ Odd (Nat.card N) ∧
      ∀ y ∈ Eight.fixSubgroup α, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
  have hs2 : (D.M.Φ α : G) * (D.M.Φ α : G) = 1 := by
    rw [← D.M.Φ_mul, hα, D.M.Φ_one]
  obtain ⟨x₁, h₁, x₂, h₂, hc₁, hc₂, hx₁, hx₂, h12⟩ := D.noNilp _ (D.M.Φ α).2 hs2
  exact not_two_nilpotent_of_witness D.M D.hm D.hK α h₁ h₂ hc₁ hc₂ hx₁ hx₂ h12

theorem exists_model_s₀ (D : Q3ModelData K₀ G) (α : MulAut K₀) (hα : Cat8.IsAdm K₀ α) :
    ∃ M' : AutModel K₀ G, M'.P = D.M.P ∧ M'.A = D.M.A ∧ (M'.Φ α : G) = D.s₀ := by
  have hs2 : (D.M.Φ α : G) * (D.M.Φ α : G) = 1 := by
    rw [← D.M.Φ_mul, hα.sq, D.M.Φ_one]
  have hsP : (D.M.Φ α : G) ∉ D.M.P := by
    rw [← mem_range_conj_iff D.M D.PA D.cent]
    exact hα.out
  have h5 : 5 ∣ Nat.card ↥(D.M.P ⊓ centralizer ({(D.M.Φ α : G)} : Set G)) := by
    rw [← card_fixSubgroup D.M α]
    exact (show 5 ∣ 360 by norm_num).trans hα.dvd
  obtain ⟨k, hk, hks⟩ := D.adm _ (D.M.Φ α).2 hs2 hsP h5
  refine exists_model_eq D.M α hk ?_
  rw [← hks]
  group

theorem q3L0_of_data (D : Q3ModelData K₀ G) (α : MulAut K₀) (hα : Cat8.IsAdm K₀ α) :
    Nat.card (Cat8.L0 K₀ α) = 360 ∧
      ∀ N : Subgroup (MulAut K₀), N ≤ Cat8.L0 K₀ α → (N.subgroupOf (Cat8.L0 K₀ α)).Normal →
        Odd (Nat.card N) → N = ⊥ := by
  obtain ⟨M', hP, hA, hΦ⟩ := exists_model_s₀ D α hα
  have hPA : M'.P ≤ M'.A := by rw [hP, hA]; exact D.PA
  have hcent : ∀ g ∈ M'.A, (∀ x ∈ M'.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact D.cent
  refine l0_of_model M' hPA hcent α D.L ?_ D.cardL D.oddL
  rw [hP, hΦ]
  exact D.commL

theorem q3F2_of_data [Finite K₀] (D : Q3ModelData K₀ G) (α : MulAut K₀) (hα : Cat8.IsAdm K₀ α)
    (Q : Subgroup (MulAut K₀))
    (hQC : Q ≤ centralizer ({α} : Set (MulAut K₀)))
    (hQS : ∃ T : Sylow 2 ↥(centralizer ({α} : Set (MulAut K₀))),
      (T : Subgroup _) = Q.subgroupOf (centralizer ({α} : Set (MulAut K₀)))) :
    ∃ g : MulAut K₀, g ∈ Cat8.Inn K₀ ∧ g ∈ normalizer (Q : Set (MulAut K₀)) ∧ g ∉ Q ∧
      g * g ∈ Q ∧ α * (g⁻¹ * α * g) ∈ Cat8.Inn K₀ := by
  obtain ⟨M', hP, hA, hΦ⟩ := exists_model_s₀ D α hα
  have hPA : M'.P ≤ M'.A := by rw [hP, hA]; exact D.PA
  have hcent : ∀ g ∈ M'.A, (∀ x ∈ M'.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact D.cent
  refine f2_of_model M' hPA hcent α D.Q₀ ?_ ?_ D.cardQ₀ D.g₀ ?_ D.g₀N D.g₀Q D.g₀2 ?_ Q hQC hQS
  · rw [hΦ, hA]; exact D.Q₀le
  · rw [hΦ, hA]; exact D.cardCA
  · rw [hP]; exact D.g₀P
  · rw [hP, hΦ]; exact D.g₀σ

end Generic

end CFSG.ComponentClassification.CatFactsSmall
