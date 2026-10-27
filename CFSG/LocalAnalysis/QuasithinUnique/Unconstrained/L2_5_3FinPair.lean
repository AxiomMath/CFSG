module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinBasic

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open
open scoped Pointwise

section Pair

variable {G : Type} [Group G]

theorem isPGroup_of_forall_pow {X : Subgroup G} (h : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsPGroup 2 ↥X := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := h x hx
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem projection_two_element {K K' R : Subgroup G} (hc : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKK' : ∀ x, x ∈ K → x ∈ K' → x = 1)
    (hcK : ∀ A : Subgroup G, A ≤ K → IsPGroup 2 ↥A → A ≠ ⊥ →
      IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (A : Set G)))
    (hRD : R ≤ K ⊔ K') (hR2 : IsPGroup 2 ↥R) (hRK : ¬ R ≤ Subgroup.centralizer (K : Set G))
    {a : G} (ha : a ∈ K) {b : G} (hb : b ∈ K') (hx : ∀ r ∈ R, (a * b) * r = r * (a * b)) :
    ∃ k : ℕ, a ^ 2 ^ k = 1 := by
  have hKcent : K ≤ Subgroup.centralizer (K' : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm
  have hKN : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (hKcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hcoe : ((R ⊔ K' : Subgroup G) : Set G) = (R : Set G) * (K' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right R K' (hRD.trans hKN)
  obtain ⟨RK, hRK_def⟩ : ∃ X : Subgroup G, X = K ⊓ (R ⊔ K') := ⟨_, rfl⟩
  have hmem : ∀ a₀ : G, a₀ ∈ RK ↔ a₀ ∈ K ∧ ∃ b₀ ∈ K', a₀ * b₀ ∈ R := by
    intro a₀
    rw [hRK_def, Subgroup.mem_inf]
    constructor
    · rintro ⟨ha₀, ha₀'⟩
      have h1 : a₀ ∈ (R : Set G) * (K' : Set G) := by
        rw [← hcoe]
        exact ha₀'
      obtain ⟨r, hr, b₁, hb₁, hrb⟩ := Set.mem_mul.mp h1
      refine ⟨ha₀, b₁⁻¹, K'.inv_mem hb₁, ?_⟩
      have : a₀ * b₁⁻¹ = r := by rw [← hrb]; group
      rw [this]
      exact hr
    · rintro ⟨ha₀, b₀, hb₀, hab⟩
      refine ⟨ha₀, ?_⟩
      have : a₀ = (a₀ * b₀) * b₀⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hab) (Subgroup.mem_sup_right (K'.inv_mem hb₀))
  have hRKK : RK ≤ K := by rw [hRK_def]; exact inf_le_left
  have hRK2 : IsPGroup 2 ↥RK := by
    refine isPGroup_of_forall_pow fun a₀ ha₀ => ?_
    obtain ⟨ha₀K, b₀, hb₀, hab⟩ := (hmem a₀).mp ha₀
    obtain ⟨k, hk⟩ := hR2 ⟨a₀ * b₀, hab⟩
    have hk' : (a₀ * b₀) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : Commute a₀ b₀ := hc a₀ ha₀K b₀ hb₀
    rw [hcomm.mul_pow] at hk'
    refine ⟨k, hKK' _ (K.pow_mem ha₀K _) ?_⟩
    have h2 : a₀ ^ 2 ^ k = (b₀ ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk'
    rw [h2]
    exact K'.inv_mem (K'.pow_mem hb₀ _)
  have hRKne : RK ≠ ⊥ := by
    intro hbot
    apply hRK
    intro r hr
    obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp (hRD hr)
    have hab' : a₁ * b₁ ∈ R := by rw [hab]; exact hr
    have ha₁RK : a₁ ∈ RK := (hmem a₁).mpr ⟨ha₁, b₁, hb₁, hab'⟩
    rw [hbot, Subgroup.mem_bot] at ha₁RK
    rw [← hab, ha₁RK, one_mul]
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => hc k hk b₁ hb₁
  have hacent : a ∈ Subgroup.centralizer (RK : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a' ha'
    obtain ⟨ha'K, b', hb', hab'⟩ := (hmem a').mp ha'
    have hE := hx _ hab'
    have h1 : a * b * (a' * b') = (a * a') * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [← hc a' ha'K b hb]
        _ = (a * a') * (b * b') := by group
    have h2 : (a' * b') * (a * b) = (a' * a) * (b' * b) := by
      calc (a' * b') * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [← hc a ha b' hb']
        _ = (a' * a) * (b' * b) := by group
    rw [h1, h2] at hE
    have h3 : (a' * a)⁻¹ * (a * a') = (b' * b) * (b * b')⁻¹ := by
      have h4 : (a' * a)⁻¹ * (a * a') * (b * b') = b' * b := by
        calc (a' * a)⁻¹ * (a * a') * (b * b') = (a' * a)⁻¹ * ((a * a') * (b * b')) := by
              rw [mul_assoc]
          _ = (a' * a)⁻¹ * ((a' * a) * (b' * b)) := by rw [hE]
          _ = b' * b := by group
      exact eq_mul_inv_of_mul_eq h4
    have hK1 : (a' * a)⁻¹ * (a * a') ∈ K :=
      K.mul_mem (K.inv_mem (K.mul_mem ha'K ha)) (K.mul_mem ha ha'K)
    have hK2 : (a' * a)⁻¹ * (a * a') ∈ K' := by
      rw [h3]
      exact K'.mul_mem (K'.mul_mem hb' hb) (K'.inv_mem (K'.mul_mem hb hb'))
    exact inv_mul_eq_one.mp (hKK' _ hK1 hK2)
  obtain ⟨k, hk⟩ := hcK RK hRKK hRK2 hRKne ⟨a, ha, hacent⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem charTwo_of_isPGroup_inf_centralizer {N R : Subgroup G}
    (hNR : N ≤ Subgroup.normalizer (R : Set G)) (hrad : pCoreOf 2 N = R)
    (hC2 : IsPGroup 2 ↥(N ⊓ Subgroup.centralizer (R : Set G))) : CharTwo N := by
  have hNC : N ≤ Subgroup.normalizer ((N ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf N N _
      Subgroup.le_normalizer (hNR.trans (normalizer_le_normalizer_centralizer R))
  have hCR : N ⊓ Subgroup.centralizer (R : Set G) ≤ pCoreOf 2 N :=
    le_pCoreOf_of_normal_pGroup inf_le_left hNC hC2
  unfold CharTwo
  rw [hrad] at hCR ⊢
  exact hCR

theorem charTwo_inf_normalizer_of_pair {K K' R : Subgroup G}
    (hc : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hKK' : ∀ x, x ∈ K → x ∈ K' → x = 1)
    (hcK : ∀ A : Subgroup G, A ≤ K → IsPGroup 2 ↥A → A ≠ ⊥ →
      IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (A : Set G)))
    (hcK' : ∀ A : Subgroup G, A ≤ K' → IsPGroup 2 ↥A → A ≠ ⊥ →
      IsPGroup 2 ↥(K' ⊓ Subgroup.centralizer (A : Set G)))
    (hRD : R ≤ K ⊔ K') (hR2 : IsPGroup 2 ↥R) (hRK : ¬ R ≤ Subgroup.centralizer (K : Set G))
    (hRK' : ¬ R ≤ Subgroup.centralizer (K' : Set G))
    (hrad : pCoreOf 2 ((K ⊔ K') ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo ((K ⊔ K') ⊓ Subgroup.normalizer (R : Set G)) := by
  have hc' : ∀ b ∈ K', ∀ a ∈ K, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hKK'' : ∀ x, x ∈ K' → x ∈ K → x = 1 := fun x hx hx' => hKK' x hx' hx
  have hRD' : R ≤ K' ⊔ K := by rw [sup_comm]; exact hRD
  set N : Subgroup G := (K ⊔ K') ⊓ Subgroup.normalizer (R : Set G) with hN
  set C : Subgroup G := N ⊓ Subgroup.centralizer (R : Set G) with hC
  have hC2 : IsPGroup 2 ↥C := by
    refine isPGroup_of_forall_pow fun y hy => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hy.1.1
    have hyR : ∀ r ∈ R, (a * b) * r = r * (a * b) := by
      intro r hr
      rw [hab]
      exact (Subgroup.mem_centralizer_iff.mp hy.2 r hr).symm
    have hyR' : ∀ r ∈ R, (b * a) * r = r * (b * a) := by
      intro r hr
      rw [← hc a ha b hb]
      exact hyR r hr
    obtain ⟨i, hi⟩ := projection_two_element hc hKK' hcK hRD hR2 hRK ha hb hyR
    obtain ⟨j, hj⟩ := projection_two_element hc' hKK'' hcK' hRD' hR2 hRK' hb ha hyR'
    obtain ⟨k, hk⟩ := Unc25G2.exists_pow_two_pow_eq_one_mul (hc a ha b hb) hi hj
    exact ⟨k, by rw [← hab]; exact hk⟩
  exact charTwo_of_isPGroup_inf_centralizer inf_le_right hrad hC2

end Pair

end CFSG.QuasithinUnique.Fin253
