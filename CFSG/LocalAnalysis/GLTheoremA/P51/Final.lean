module

public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_isPGroup_of_glaPComponent {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {X K : Subgroup G} (hK : GLAPComponent p X K) : ¬ IsPGroup q K := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hKq
  obtain ⟨n, hn⟩ := hKq.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥K)) := by
    rw [Subgroup.card_top, hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
  have htop : GLAPPrimeCore p ↥K = ⊤ :=
    top_le_iff.1 (le_sSup ⟨inferInstance, hcop⟩)
  have hsub : Subsingleton (PQuot p K) := by
    show Subsingleton (↥K ⧸ GLAPPrimeCore p ↥K)
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_nontrivial_iff_subsingleton.2 hsub)
    (isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hK))

private theorem le_of_commutator_aux {K X : Subgroup G} (hK : IsSubnormal K X) :
    ∀ {A H : Subgroup G}, A ≤ X → H ≤ K → (⁅A, H⁆ : Subgroup G) = A → A ≤ K := by
  induction hK with
  | refl => intro A H hAX _ _; exact hAX
  | @step K₁ M X₁ hKM hn hM ih =>
    intro A H hAX hHK hA
    have hAM : A ≤ M := ih hAX (hHK.trans hKM) hA
    have hcomm : (⁅M, K₁⁆ : Subgroup G) ≤ K₁ := by
      refine Subgroup.commutator_le.2 ?_
      intro m hm k hk
      have hkM : (⟨k, hKM hk⟩ : ↥M) ∈ K₁.subgroupOf M := Subgroup.mem_subgroupOf.2 hk
      have hmk : (⟨m, hm⟩ : ↥M) * ⟨k, hKM hk⟩ * (⟨m, hm⟩ : ↥M)⁻¹ ∈ K₁.subgroupOf M :=
        hn.conj_mem _ hkM _
      have hmk' : m * k * m⁻¹ ∈ K₁ := Subgroup.mem_subgroupOf.1 hmk
      rw [commutatorElement_def]
      exact K₁.mul_mem hmk' (K₁.inv_mem hk)
    calc A = ⁅A, H⁆ := hA.symm
      _ ≤ ⁅M, K₁⁆ := Subgroup.commutator_mono hAM hHK
      _ ≤ K₁ := hcomm

theorem le_of_commutator_eq_of_isSubnormal {K X A H : Subgroup G} (hK : IsSubnormal K X)
    (hAX : A ≤ X) (hHK : H ≤ K) (hA : (⁅A, H⁆ : Subgroup G) = A) : A ≤ K :=
  le_of_commutator_aux hK hAX hHK hA

theorem eq_bot_of_le_sup_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X K H W : Subgroup G} (hK : GLAPComponent p X K) (hHK : H ≤ K)
    (hKH : K ≤ H ⊔ GLAPPrimeCoreOf p K) (hWK : W ≤ K) (hW2 : IsPGroup 2 W)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) (hW : (⁅W, H⁆ : Subgroup G) = W)
    (hodd : Odd (Nat.card (⁅K, GLAPPrimeCoreOf p X⁆ : Subgroup G))) : W = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : Nontrivial (PQuot p K) := isQuasisimple_nontrivial hQ
  have hOX : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1]
    exact inf_le_right
  have hHN : H ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    hHK.trans (le_normalizer_glaPPrimeCoreOf p K)
  obtain ⟨π, hπ⟩ : ∃ π : ↥K →* PQuot p K, π = QuotientGroup.mk' (GLAPPrimeCore p ↥K) :=
    ⟨_, rfl⟩
  have hπsurj : Function.Surjective π := by
    rw [hπ]
    exact QuotientGroup.mk'_surjective _
  have hπeq : ∀ x y : ↥K, π x = π y ↔ x⁻¹ * y ∈ GLAPPrimeCore p ↥K := by
    intro x y
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hπker : ∀ x : ↥K, π x = 1 ↔ x ∈ GLAPPrimeCore p ↥K := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hHsurj : ∀ q : PQuot p K, ∃ h : ↥K, (h : G) ∈ H ∧ π h = q := by
    intro q
    obtain ⟨x, rfl⟩ := hπsurj q
    have hx : (x : G) ∈ (H ⊔ GLAPPrimeCoreOf p K : Subgroup G) := hKH x.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H _ hHN] at hx
    obtain ⟨y, hy, o, ho, hyo⟩ := Set.mem_mul.mp hx
    obtain ⟨o', ho', ho'eq⟩ := ho
    have ho'val : (o' : G) = o := ho'eq
    have hinv : (⟨y, hHK hy⟩ : ↥K)⁻¹ * x = o' := by
      apply Subtype.ext
      show y⁻¹ * (x : G) = (o' : G)
      rw [ho'val, ← hyo]
      exact inv_mul_cancel_left y o
    exact ⟨⟨y, hHK hy⟩, hy, (hπeq _ _).2 (by rw [hinv]; exact ho')⟩
  have hW'norm : ((W.subgroupOf K).map π).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨h, hhH, rfl⟩ := hHsurj g
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
    have hmem : h * w * h⁻¹ ∈ W.subgroupOf K :=
      Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hHW hhH) (w : G)).1 hwW)
    exact Subgroup.mem_map.2 ⟨h * w * h⁻¹, hmem, by simp only [map_mul, map_inv]⟩
  have hW₀2 : IsPGroup 2 ↥(W.subgroupOf K) :=
    hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  have hW'top : (W.subgroupOf K).map π ≠ ⊤ := by
    intro htop
    have h2 : IsPGroup 2 ↥((W.subgroupOf K).map π) := hW₀2.map π
    rw [htop] at h2
    have h2Q : IsPGroup 2 (PQuot p K) := h2.of_equiv Subgroup.topEquiv
    haveI : Group.IsPerfect (PQuot p K) := ⟨hQ.1⟩
    exact Group.IsPerfect.not_isNilpotent (PQuot p K) h2Q.isNilpotent
  have hW'cent : (W.subgroupOf K).map π ≤ Subgroup.center (PQuot p K) :=
    le_center_of_normal_of_isQuasisimple hQ hW'norm hW'top
  have hWO : W ≤ GLAPPrimeCoreOf p K := by
    have hcomm : (⁅W, H⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p K := by
      refine Subgroup.commutator_le.2 ?_
      intro w hw h hh
      have hA : π ⟨w, hWK hw⟩ ∈ Subgroup.center (PQuot p K) :=
        hW'cent (Subgroup.mem_map.2 ⟨⟨w, hWK hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩)
      have hpi : π ⁅(⟨w, hWK hw⟩ : ↥K), (⟨h, hHK hh⟩ : ↥K)⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hA _).symm
      exact Subgroup.mem_map.2 ⟨_, (hπker _).1 hpi, rfl⟩
    exact hW.symm.trans_le hcomm
  have hWX : W ≤ GLAPPrimeCoreOf p X := hWO.trans hOX
  have hcomm2 : (⁅W, H⁆ : Subgroup G) ≤ ⁅K, GLAPPrimeCoreOf p X⁆ :=
    calc (⁅W, H⁆ : Subgroup G) ≤ ⁅GLAPPrimeCoreOf p X, K⁆ := Subgroup.commutator_mono hWX hHK
      _ = ⁅K, GLAPPrimeCoreOf p X⁆ := Subgroup.commutator_comm _ _
  have hWle : W ≤ ⁅K, GLAPPrimeCoreOf p X⁆ := hW.symm.trans_le hcomm2
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hdvd : Nat.card W ∣ Nat.card (⁅K, GLAPPrimeCoreOf p X⁆ : Subgroup G) :=
    Subgroup.card_dvd_of_le hWle
  rw [hn] at hdvd
  have hodd2 : Odd (2 ^ n) := Odd.of_dvd_nat hodd hdvd
  have hn0 : n = 0 := by
    by_contra hn0
    exact (Nat.not_even_iff_odd.2 hodd2) (Nat.even_pow.2 ⟨even_two, hn0⟩)
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.1 hn

end CFSG.LocalAnalysis.GLTheoremA.P51
