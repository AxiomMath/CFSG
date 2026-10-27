module

public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem eq_one_of_forall_smul_eq
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} (hg : ∀ x ∈ suzukiOmega a K, g • x = x) : g = 1 := by
  have hT := mem_suzukiT_of_smul_eq hK (hg _ (suzukiInfty_mem_suzukiOmega a K))
    (hg _ (suzukiLine_mem_suzukiOmega a K 0 0))
  obtain ⟨μ, rfl⟩ := mem_suzukiT_iff.1 hT
  have h := hg _ (suzukiLine_mem_suzukiOmega a K 1 0)
  rw [(suzuki_ovoid_torus_action a hK μ 1 0).2, suzukiLine_eq_iff, mul_one] at h
  have hμ : μ = 1 := Units.ext (inv_eq_one.1 h.1)
  rw [hμ, suzukiDElt_one]

theorem pow_smul_eq_self {G α : Type*} [Monoid G] [MulAction G α] {g : G} {x : α}
    (h : g • x = x) : ∀ m : ℕ, g ^ m • x = x
  | 0 => by rw [pow_zero, one_smul]
  | m + 1 => by rw [pow_succ, mul_smul, h, pow_smul_eq_self h m]

theorem smul_eq_self_of_pow_smul {G α : Type*} [Group G] [MulAction G α] {σ : G}
    (hσ : orderOf σ = 5) {y : α} {d : ℕ} (hd1 : 1 ≤ d) (hd5 : d < 5) (h : σ ^ d • y = y) :
    σ • y = y := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d * m % 5 = 1 := by
    interval_cases d
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩
  have h' := pow_smul_eq_self h m
  rwa [← pow_mul, ← pow_mod_orderOf, hσ, hm, pow_one] at h'

theorem suzuki_two_normal_five_complement_core_trivial
    {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    Nat.card (suzukiGroup 0 k) = 20 ∧
      ∃ P : Subgroup (suzukiGroup 0 k), P.Normal ∧ Nat.card P = 5 ∧
        Subgroup.centralizer (P : Set (suzukiGroup 0 k)) = P ∧
        ∀ R : Subgroup (suzukiGroup 0 k), R.Normal → Nat.Coprime (Nat.card R) 5 → R = ⊥ := by
  have hK : Nat.card k = 2 ^ (2 * 0 + 1) := by rw [hk]; norm_num
  have hH : Nat.card (suzukiGroup 0 k) = 20 := by rw [suzuki_order hK]; norm_num
  have := finite_suzukiGroup hK
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨hH, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 (suzukiGroup 0 k)) := inferInstance
  have hPcard : Nat.card (P : Subgroup (suzukiGroup 0 k)) = 5 := by
    rw [Sylow.card_eq_multiplicity, hH, show (20 : ℕ) = 5 * 4 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero, pow_one]
  have hindex : (P : Subgroup (suzukiGroup 0 k)).index = 4 := by
    have h := (P : Subgroup (suzukiGroup 0 k)).card_mul_index
    rw [hPcard, hH] at h
    omega
  have hcount : Nat.card (Sylow 5 (suzukiGroup 0 k)) = 1 := by
    have h1 := card_sylow_modEq_one (p := 5) (G := suzukiGroup 0 k)
    have h2 := Sylow.card_dvd_index P
    rw [hindex] at h2
    have h3 : Nat.card (Sylow 5 (suzukiGroup 0 k)) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have h4 : 0 < Nat.card (Sylow 5 (suzukiGroup 0 k)) := Nat.card_pos
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card (Sylow 5 (suzukiGroup 0 k)) <;> simp_all
  have : Subsingleton (Sylow 5 (suzukiGroup 0 k)) := (Nat.card_eq_one_iff_unique.1 hcount).1
  have hPnormal := Sylow.normal_of_subsingleton P
  have : IsCyclic (P : Subgroup (suzukiGroup 0 k)) := isCyclic_of_prime_card hPcard
  obtain ⟨σ', hσ'⟩ := IsCyclic.exists_generator (α := (P : Subgroup (suzukiGroup 0 k)))
  set σ : suzukiGroup 0 k := (σ' : suzukiGroup 0 k) with hσdef
  have hσP : σ ∈ (P : Subgroup (suzukiGroup 0 k)) := σ'.2
  have hσord : orderOf σ = 5 := by
    rw [hσdef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hσ', hPcard]
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσord
    norm_num at hσord
  obtain ⟨x0, hx0, hmove⟩ : ∃ x0 ∈ suzukiOmega 0 k, σ • x0 ≠ x0 := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (eq_one_of_forall_smul_eq hK hcon)
  set f : Fin 5 → ℙ k (Fin 4 → k) := fun j => σ ^ (j : ℕ) • x0 with hf
  have hlt : ∀ i j : ℕ, i < j → j < 5 → σ ^ i • x0 ≠ σ ^ j • x0 := by
    intro i j hij hj5 heq
    have h1 : σ ^ j • x0 = σ ^ (j - i) • (σ ^ i • x0) := by
      rw [← mul_smul, pow_sub_mul_pow σ hij.le]
    have h2 : σ • (σ ^ i • x0) = σ ^ i • x0 :=
      smul_eq_self_of_pow_smul hσord (by omega) (by omega) (h1 ▸ heq).symm
    apply hmove
    apply smul_left_cancel (σ ^ i)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, h2]
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
    · exact hlt i j h j.isLt hij
    · exact hlt j i h i.isLt hij.symm
  have hmemΩ : ∀ (g : suzukiGroup 0 k) (x : ℙ k (Fin 4 → k)), x ∈ suzukiOmega 0 k →
      g • x ∈ suzukiOmega 0 k := fun g x hx => suzuki_smul_mem_suzukiOmega hK g hx
  have hΩcard : (suzukiOmega 0 k).ncard = 5 := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2
  have hrange : Set.range f = suzukiOmega 0 k := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.finite_of_ncard_ne_zero (by omega))
    · rintro _ ⟨j, rfl⟩
      exact hmemΩ _ _ hx0
    · rw [hΩcard, Set.ncard_range_of_injective hfinj, Nat.card_fin]
  have horbit : ∀ x ∈ suzukiOmega 0 k, ∃ j : ℕ, σ ^ j • x0 = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨j, rfl⟩
  have hcent : Subgroup.centralizer (P : Set (suzukiGroup 0 k)) =
      (P : Subgroup (suzukiGroup 0 k)) := by
    apply le_antisymm
    · intro i hi
      have hcomm : ∀ p ∈ (P : Subgroup (suzukiGroup 0 k)), p * i = i * p :=
        Subgroup.mem_centralizer_iff.1 hi
      obtain ⟨j0, hj0⟩ := horbit _ (hmemΩ i x0 hx0)
      have hact : ∀ x ∈ suzukiOmega 0 k, ((σ ^ j0)⁻¹ * i) • x = x := by
        intro x hx
        obtain ⟨j, rfl⟩ := horbit x hx
        calc ((σ ^ j0)⁻¹ * i) • (σ ^ j • x0) = ((σ ^ j0)⁻¹ * (i * σ ^ j)) • x0 := by
              rw [mul_smul, mul_smul, mul_smul]
          _ = ((σ ^ j0)⁻¹ * (σ ^ j * i)) • x0 := by rw [← hcomm _ (pow_mem hσP j)]
          _ = ((σ ^ j0)⁻¹ * σ ^ j) • (i • x0) := by rw [← mul_assoc, mul_smul]
          _ = ((σ ^ j0)⁻¹ * σ ^ j) • (σ ^ j0 • x0) := by rw [hj0]
          _ = ((σ ^ j0)⁻¹ * σ ^ j * σ ^ j0) • x0 := by rw [← mul_smul]
          _ = σ ^ j • x0 := by
              rw [mul_assoc, (Commute.pow_pow_self σ j j0).eq, inv_mul_cancel_left]
      have h1 := eq_one_of_forall_smul_eq hK hact
      rw [inv_mul_eq_one] at h1
      rw [← h1]
      exact pow_mem hσP j0
    · intro p hp
      refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
      have := (inferInstance : IsCyclic (P : Subgroup (suzukiGroup 0 k)))
      have hc := IsCyclic.commGroup.mul_comm (⟨q, hq⟩ : (P : Subgroup (suzukiGroup 0 k)))
        ⟨p, hp⟩
      exact congrArg Subtype.val hc
  refine ⟨P, hPnormal, hPcard, hcent, fun R hR hcop => ?_⟩
  have hRP : R ⊓ (P : Subgroup (suzukiGroup 0 k)) = ⊥ := by
    have h1 : Nat.card (R ⊓ (P : Subgroup (suzukiGroup 0 k)) : Subgroup _) ∣ Nat.card R :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (R ⊓ (P : Subgroup (suzukiGroup 0 k)) : Subgroup _) ∣ 5 := by
      have h2' := Subgroup.card_dvd_of_le
        (inf_le_right : R ⊓ (P : Subgroup (suzukiGroup 0 k)) ≤ (P : Subgroup (suzukiGroup 0 k)))
      rwa [hPcard] at h2'
    have h3 : Nat.card (R ⊓ (P : Subgroup (suzukiGroup 0 k)) : Subgroup _) = 1 :=
      Nat.eq_one_of_dvd_one (by rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd h1 h2)
    exact Subgroup.eq_bot_of_card_eq _ h3
  refine (Subgroup.eq_bot_iff_forall R).2 fun r hr => ?_
  have hrc : r ∈ Subgroup.centralizer (P : Set (suzukiGroup 0 k)) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hmemR : r * x * r⁻¹ * x⁻¹ ∈ R := by
      have h := mul_mem hr (hR.conj_mem r⁻¹ (inv_mem hr) x)
      rwa [← mul_assoc, ← mul_assoc] at h
    have hmemP : r * x * r⁻¹ * x⁻¹ ∈ (P : Subgroup (suzukiGroup 0 k)) :=
      mul_mem (hPnormal.conj_mem x hx r) (inv_mem hx)
    have hmem : r * x * r⁻¹ * x⁻¹ ∈ R ⊓ (P : Subgroup (suzukiGroup 0 k)) := ⟨hmemR, hmemP⟩
    rw [hRP, Subgroup.mem_bot] at hmem
    have h2 : r * x * r⁻¹ = x := mul_inv_eq_one.1 hmem
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hcent] at hrc
  have : r ∈ R ⊓ (P : Subgroup (suzukiGroup 0 k)) := ⟨hr, hrc⟩
  rwa [hRP, Subgroup.mem_bot] at this

end CFSG.LieType.Ree
