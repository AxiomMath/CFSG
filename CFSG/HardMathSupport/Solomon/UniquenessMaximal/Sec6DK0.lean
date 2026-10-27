module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DBar

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_comm_pow {E : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (he : ∀ x ∈ E, x ^ 3 = 1) : IsElemAbelian 3 E :=
  ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hc a a.2 b b.2), he⟩

theorem factorization_three_card_mul {a c : ℕ} (ha : a ≠ 0) (hc : c ≠ 0) (hcop : Nat.Coprime 3 c) :
    (a * c).factorization 3 = a.factorization 3 := by
  rw [Nat.factorization_mul ha hc, Finsupp.add_apply]
  have : ¬ 3 ∣ c := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  rw [Nat.factorization_eq_zero_of_not_dvd this, add_zero]

theorem factorization_barX {X K : Subgroup G} (hKX : K ≤ X) :
    (Nat.card ↥(barX 3 X K)).factorization 3 = (Nat.card ↥K).factorization 3 := by
  have h := card_barX_mul_card_inf hKX
  have hcop : Nat.Coprime 3 (Nat.card ↥(K ⊓ GLAPPrimeCoreOf 3 X)) := by
    refine (coprime_card_core 3 X).coprime_dvd_right ?_
    exact Subgroup.card_dvd_of_le inf_le_right
  rw [← h, factorization_three_card_mul Nat.card_pos.ne' Nat.card_pos.ne' hcop]

theorem k0_sylow_facts {X K K₀ R₁ S₀ : Subgroup G} (hK : GLAPComponent 3 X K)
    (hR₁ : IsThreeOnePlusTwo R₁) (hR₁K : R₁ ≤ K)
    (hR₁c : Nat.card R₁ = 3 ^ (Nat.card K).factorization 3)
    (hcenR : barCenterX 3 X R₁ = barCenterX 3 X K)
    (φ : (↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀) ≃* (↥(barX 3 X K) ⧸ Subgroup.center ↥(barX 3 X K)))
    (hS₀K : S₀ ≤ K₀) (hS₀p : IsPGroup 3 ↥S₀)
    (hS₀c : Nat.card S₀ = 3 ^ (Nat.card K₀).factorization 3) :
    Nat.card S₀ = 9 ∧ IsElemAbelian 3 S₀ := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKX : K ≤ X := hK.1
  have hR₁X : R₁ ≤ X := hR₁K.trans hKX
  have hR₁p : IsPGroup 3 ↥R₁ := by
    apply IsPGroup.of_card (n := 3)
    rw [hR₁.2.1]; norm_num
  have hv : (Nat.card K).factorization 3 = 3 := by
    have h27 : (3 : ℕ) ^ (Nat.card K).factorization 3 = 3 ^ 3 := by
      rw [← hR₁c, hR₁.2.1]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h27
  set Q := barX 3 X K with hQ
  have hQq : CFSG.Open.IsQuasisimple ↥Q := hK.2.2.1.2.2
  have hQv : (Nat.card Q).factorization 3 = 3 := by rw [hQ, factorization_barX hKX, hv]
  have hZ : Nat.card (Subgroup.center ↥Q) = 3 := by
    have h1 : Nat.card ↥(barCenterX 3 X K) = Nat.card (Subgroup.center ↥Q) := by
      unfold barCenterX
      exact Subgroup.card_map_of_injective Q.subtype_injective
    rw [← h1, ← hcenR]
    exact card_barCenterX_of_heis hR₁ hR₁X
  have hQZ : Nat.card (↥Q ⧸ Subgroup.center ↥Q) * 3 = Nat.card Q := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Q)
    rw [hZ] at hh
    exact hh.symm
  have hQZ0 : Nat.card (↥Q ⧸ Subgroup.center ↥Q) ≠ 0 := Nat.card_pos.ne'
  have hQZv : (Nat.card (↥Q ⧸ Subgroup.center ↥Q)).factorization 3 = 2 := by
    have := congrArg (fun n => n.factorization 3) hQZ
    rw [Nat.factorization_mul hQZ0 (by norm_num : (3 : ℕ) ≠ 0), Finsupp.add_apply, hQv,
      Nat.Prime.factorization_self Nat.prime_three] at this
    omega
  have hK₀card : Nat.card ↥K₀ = Nat.card (↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀) *
      Nat.card (GLAPPrimeCore 3 ↥K₀) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥K₀)
  have hK₀v : (Nat.card ↥K₀).factorization 3 = 2 := by
    rw [hK₀card, factorization_three_card_mul Nat.card_pos.ne' Nat.card_pos.ne'
      (coprime_card_gLAPPrimeCore_aux 3 ↥K₀), Nat.card_congr φ.toEquiv, hQZv]
  have hS9 : Nat.card S₀ = 9 := by rw [hS₀c, hK₀v]; norm_num
  refine ⟨hS9, ?_⟩
  refine isElemAbelian_of_comm_pow (fun a ha b hb => ?_) (fun s hs => ?_)
  · have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥S₀) (p := 3)
      (by rw [hS9]; norm_num)
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  ·
    obtain ⟨j, hj⟩ := hS₀p ⟨s, hs⟩
    have hsj : s ^ (3 ^ j) = 1 := congrArg Subtype.val hj
    set m : ↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀ := QuotientGroup.mk ⟨s, hS₀K hs⟩ with hm
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (φ m)
    have hmj : m ^ (3 ^ j) = 1 := by
      rw [hm, ← QuotientGroup.mk_pow]
      have : (⟨s, hS₀K hs⟩ : ↥K₀) ^ (3 ^ j) = 1 := Subtype.ext hsj
      rw [this]; rfl
    have hqj : q ^ (3 ^ j) ∈ Subgroup.center ↥Q := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← map_pow, hmj, map_one]
    have hZp : (q ^ (3 ^ j)) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center ↥Q)) (x := ⟨_, hqj⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have hq3 : q ^ 3 = 1 := by
      apply pow_three_eq_one_of_sylow (Q := ↥Q) ((barX 3 X R₁).subgroupOf Q) ?_ ?_ ⟨j + 1, ?_⟩
      · have hle : barX 3 X R₁ ≤ Q := by
          intro z hz
          obtain ⟨⟨r, hrX⟩, hrR, rfl⟩ := mem_barX_iff.1 hz
          exact mem_barX_iff.2 ⟨⟨r, hrX⟩, hR₁K hrR, rfl⟩
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
          card_barX_of_isPGroup Nat.prime_three hR₁X hR₁p, hR₁.2.1, hQv]
        norm_num
      · intro r hr
        obtain ⟨⟨z, hzX⟩, hzR, hz⟩ := mem_barX_iff.1 ((Subgroup.mem_subgroupOf).1 hr)
        have h3 : (r : ↥X ⧸ GLAPPrimeCore 3 ↥X) ^ 3 = 1 := by
          rw [← hz, ← map_pow]
          have : (⟨z, hzX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (hR₁.2.2 z hzR)
          rw [this, map_one]
        exact Subtype.ext h3
      · rw [pow_succ, pow_mul]
        exact hZp
    have hmc : m ^ 3 = 1 := by
      apply φ.injective
      rw [map_pow, ← hq, ← QuotientGroup.mk_pow, hq3, map_one]
      rfl
    have h5 : s ^ 3 ∈ GLAPPrimeCoreOf 3 K₀ := by
      have h6 : (⟨s, hS₀K hs⟩ : ↥K₀) ^ 3 ∈ GLAPPrimeCore 3 ↥K₀ := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hmc
      have := (mem_coreOf_iff (p := 3) (X := K₀) ((⟨s, hS₀K hs⟩ : ↥K₀) ^ 3)).2 h6
      simpa using this
    have h7 : s ^ 3 ∈ S₀ ⊓ GLAPPrimeCoreOf 3 K₀ := ⟨S₀.pow_mem hs 3, h5⟩
    rw [pgroup_inf_core_eq_bot K₀ hS₀p, Subgroup.mem_bot] at h7
    exact h7

theorem k0_centreless {X K K₀ : Subgroup G} (hK : GLAPComponent 3 X K)
    (φ : (↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀) ≃* (↥(barX 3 X K) ⧸ Subgroup.center ↥(barX 3 X K)))
    {g : G} (hg : g ∈ K₀) (hc : ∀ k ∈ K₀, k * g * k⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 K₀) :
    g ∈ GLAPPrimeCoreOf 3 K₀ := by
  have hQq : CFSG.Open.IsQuasisimple ↥(barX 3 X K) := hK.2.2.1.2.2
  have hbot := center_quot_center_eq_bot hQq
  set m : ↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀ := QuotientGroup.mk ⟨g, hg⟩ with hm
  have hcen : ∀ w : ↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀, w * m = m * w := by
    intro w
    induction w using QuotientGroup.induction_on with | H k => ?_
    have h1 := (mem_coreOf_iff (p := 3) (X := K₀) (k * ⟨g, hg⟩ * k⁻¹ * ⟨g, hg⟩⁻¹)).1
      (by simpa using hc k.1 k.2)
    have h2 : (QuotientGroup.mk (k * ⟨g, hg⟩ * k⁻¹ * ⟨g, hg⟩⁻¹) : ↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀) = 1 :=
      (QuotientGroup.eq_one_iff _).2 h1
    rw [hm]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    have h3 : (QuotientGroup.mk k : ↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀) * QuotientGroup.mk ⟨g, hg⟩ =
        QuotientGroup.mk ⟨g, hg⟩ * QuotientGroup.mk k := by
      have := commutatorElement_eq_one_iff_mul_comm.1 (show ⁅(QuotientGroup.mk k : ↥K₀ ⧸ GLAPPrimeCore 3 ↥K₀), QuotientGroup.mk ⟨g, hg⟩⁆ = 1 from h2)
      exact this
    exact h3
  have hφ : φ m ∈ Subgroup.center (↥(barX 3 X K) ⧸ Subgroup.center ↥(barX 3 X K)) := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨w, rfl⟩ := φ.surjective c
    rw [← map_mul, ← map_mul, hcen w]
  rw [hbot, Subgroup.mem_bot] at hφ
  have hm1 : m = 1 := φ.injective (by rw [hφ, map_one])
  have : (⟨g, hg⟩ : ↥K₀) ∈ GLAPPrimeCore 3 ↥K₀ := (QuotientGroup.eq_one_iff _).1 hm1
  exact (mem_coreOf_iff (p := 3) (X := K₀) ⟨g, hg⟩).2 this

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
