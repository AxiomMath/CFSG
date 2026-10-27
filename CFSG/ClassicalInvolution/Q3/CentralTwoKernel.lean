module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.ClassicalInvolution.Q3.CentralKernel

open Subgroup
open scoped commutatorElement

theorem mem_commutator_of_central_kernel {E G : Type*} [Group E] [Finite E] [Group G]
    (π : E →* G) (hπ : Function.Surjective π) (hper : Group.IsPerfect E)
    (hcen : π.ker ≤ Subgroup.center E) {p : ℕ} [Fact p.Prime] (hker : IsPGroup p π.ker)
    (S : Subgroup G) (hS : ¬ p ∣ S.index) {z : E} (hz : z ∈ π.ker) :
    ∃ hzS : z ∈ S.comap π, (⟨z, hzS⟩ : ↥(S.comap π)) ∈ commutator ↥(S.comap π) := by
  set H : Subgroup E := S.comap π with hH
  have hzH : z ∈ H := by
    rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact S.one_mem
  refine ⟨hzH, ?_⟩
  let ϕ : ↥H →* Abelianization ↥H := Abelianization.of
  have hT : ∀ e : E, MonoidHom.transfer ϕ e = 1 := by
    intro e
    have : e ∈ commutator E := by rw [hper.commutator_eq_top]; trivial
    exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker _ this)
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : g₀ * z ^ k = z ^ k * g₀ :=
      Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ (hcen hz) k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hc]
      _ = z ^ k := by group
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  rw [hT z] at h1
  have h2 : (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1.symm
  have hidx : H.index = S.index := Subgroup.index_comap_of_surjective S hπ
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hker ⟨z, hz⟩
  have hord : Nat.Coprime H.index (orderOf z) := by
    rw [hidx, ← Subgroup.orderOf_mk z hz, hk]
    exact Nat.Coprime.pow_right k (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hS).symm)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hord
  have : (⟨z, hzH⟩ : ↥H) = (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : ↥H) ^ m :=
    Subtype.ext hm.symm
  rw [this]
  exact Subgroup.pow_mem _ h2 m

theorem inf_commutator_eq_bot_of_sd16 {P : Type*} [Group P] (Z : Subgroup P)
    (hZ : Z ≤ Subgroup.center P) (a b : P)
    (hgen : Subgroup.closure ({a, b} : Set P) ⊔ Z = ⊤) (h2 : b ^ 2 ∈ Z)
    (h3 : b * a * b⁻¹ * (a ^ 3)⁻¹ ∈ Z) (h4 : ∀ k : ℕ, a ^ k ∈ Z → 8 ∣ k) :
    Z ⊓ commutator P = ⊥ := by
  set d : P := b * a * b⁻¹ * (a ^ 3)⁻¹ with hd
  have hdc : ∀ g, g * d = d * g := fun g => Subgroup.mem_center_iff.mp (hZ h3) g
  have hb2c : ∀ g, g * (b * b) = (b * b) * g := fun g => by
    simpa [pow_two] using Subgroup.mem_center_iff.mp (hZ h2) g
  have hzc : ∀ z ∈ Z, ∀ g, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.mp (hZ hz) g
  have hbab : b * a * b⁻¹ = d * a ^ 3 := by rw [hd]; group
  have hcomm : Commute d (a ^ 3) := (hdc (a ^ 3)).symm
  have hdpow : ∀ k n : ℕ, a ^ k * d ^ n = d ^ n * a ^ k := fun k n =>
    (Commute.pow_pow (hdc a) k n).eq
  have hrel : a ^ 8 * d ^ 4 = 1 := by
    have e1 : b * (b * a * b⁻¹) * b⁻¹ = a := by
      calc b * (b * a * b⁻¹) * b⁻¹ = (b * b) * a * (b⁻¹ * b⁻¹) := by group
        _ = a * (b * b) * (b⁻¹ * b⁻¹) := by rw [hb2c a]
        _ = a := by group
    have e2 : b * (b * a * b⁻¹) * b⁻¹ = d ^ 4 * a ^ 9 := by
      rw [hbab]
      have : b * (d * a ^ 3) * b⁻¹ = (b * d * b⁻¹) * (b * a * b⁻¹) ^ 3 := by
        rw [conj_pow]; group
      have hbd : b * d * b⁻¹ = d := by rw [hdc b]; group
      rw [this, hbab, hbd, hcomm.mul_pow]
      group
    have e3 : d ^ 4 * a ^ 9 = a := e2.symm.trans e1
    have e5 : d ^ 4 * a ^ 8 * a = 1 * a := by
      calc d ^ 4 * a ^ 8 * a = d ^ 4 * a ^ 9 := by group
        _ = a := e3
        _ = 1 * a := by group
    rw [hdpow 8 4]
    exact mul_right_cancel e5
  set w : P := a ^ 2 * d with hw
  have hwc : Commute a w := by
    rw [hw]; exact ((Commute.refl a).pow_right 2).mul_right (hdc a)
  have hw4 : w ^ 4 = 1 := by
    rw [hw, (show Commute (a ^ 2) d from hdc (a ^ 2)).mul_pow, ← pow_mul]
    exact hrel
  have hbw : b * w * b⁻¹ = w⁻¹ := by
    have e : b * w * b⁻¹ = (d * a ^ 3) ^ 2 * d := by
      rw [hw]
      have hbd : b * d * b⁻¹ = d := by rw [hdc b]; group
      calc b * (a ^ 2 * d) * b⁻¹ = (b * a ^ 2 * b⁻¹) * (b * d * b⁻¹) := by group
        _ = (b * a * b⁻¹) ^ 2 * d := by rw [hbd, conj_pow]
        _ = (d * a ^ 3) ^ 2 * d := by rw [hbab]
    rw [e]
    apply eq_inv_of_mul_eq_one_left
    rw [hw, hcomm.mul_pow]
    calc d ^ 2 * (a ^ 3) ^ 2 * d * (a ^ 2 * d)
        = d ^ 2 * ((a ^ 3) ^ 2 * d) * (a ^ 2 * d) := by group
      _ = d ^ 2 * (d * (a ^ 3) ^ 2) * (a ^ 2 * d) := by rw [hdc ((a ^ 3) ^ 2)]
      _ = d ^ 3 * a ^ 8 * d := by group
      _ = d ^ 3 * (a ^ 8 * d) := by group
      _ = d ^ 3 * (d * a ^ 8) := by rw [hdc (a ^ 8)]
      _ = d ^ 4 * a ^ 8 := by group
      _ = 1 := by rw [← hdpow 8 4]; exact hrel
  set K : Subgroup P := Subgroup.zpowers w with hK
  have hwK : w ∈ K := Subgroup.mem_zpowers w
  have hKa : ∀ k ∈ K, a * k * a⁻¹ = k := by
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (hwc.zpow_right m).mul_inv_cancel
  have hKb : ∀ k ∈ K, b * k * b⁻¹ = k⁻¹ := by
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← conj_zpow, hbw, inv_zpow]
  have hKb' : ∀ k ∈ K, b⁻¹ * k * b = k⁻¹ := by
    intro k hk
    have hc : (b * b)⁻¹ * (b * k * b⁻¹) * (b * b) = b * k * b⁻¹ := by
      have := hb2c (b * k * b⁻¹)
      calc (b * b)⁻¹ * (b * k * b⁻¹) * (b * b) = (b * b)⁻¹ * ((b * k * b⁻¹) * (b * b)) := by group
        _ = (b * b)⁻¹ * ((b * b) * (b * k * b⁻¹)) := by rw [this]
        _ = b * k * b⁻¹ := by group
    calc b⁻¹ * k * b = (b * b)⁻¹ * (b * k * b⁻¹) * (b * b) := by group
      _ = b * k * b⁻¹ := hc
      _ = k⁻¹ := hKb k hk
  have hKnorm : K.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [eq_top_iff, ← hgen]
    refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
    · intro g hg
      rcases hg with hg | hg
      · rw [hg, SetLike.mem_coe, Subgroup.mem_normalizer_iff]
        intro h
        refine ⟨fun hh => by rw [hKa h hh]; exact hh, fun hh => ?_⟩
        have hh' : a * h * a⁻¹ = h := by
          have := hKa _ hh
          calc a * h * a⁻¹ = a⁻¹ * (a * (a * h * a⁻¹) * a⁻¹) * a := by group
            _ = a⁻¹ * (a * h * a⁻¹) * a := by rw [this]
            _ = h := by group
        rwa [hh'] at hh
      · rw [Set.mem_singleton_iff] at hg
        rw [hg, SetLike.mem_coe, Subgroup.mem_normalizer_iff]
        intro h
        refine ⟨fun hh => by rw [hKb h hh]; exact K.inv_mem hh, fun hh => ?_⟩
        have hh' : h = (b * h * b⁻¹)⁻¹ := by
          calc h = b⁻¹ * (b * h * b⁻¹) * b := by group
            _ = (b * h * b⁻¹)⁻¹ := hKb' _ hh
        have := K.inv_mem hh
        rwa [← hh'] at this
    · intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have : z * h * z⁻¹ = h := by
        have := hzc z hz h
        calc z * h * z⁻¹ = h * z * z⁻¹ := by rw [this]
          _ = h := by group
      rw [this]
  have hbaw : ⁅b, a⁆ = w := by
    rw [commutatorElement_def]
    calc b * a * b⁻¹ * a⁻¹ = (b * a * b⁻¹) * a⁻¹ := rfl
      _ = d * a ^ 3 * a⁻¹ := by rw [hbab]
      _ = d * a ^ 2 := by group
      _ = a ^ 2 * d := (hdc (a ^ 2)).symm
  have hcommP : ∀ g h : P, ⁅g, h⁆ ∈ K := by
    have := hKnorm
    set φ : P →* P ⧸ K := QuotientGroup.mk' K with hφ
    set X : Set P := ({a, b} : Set P) ∪ (Z : Set P) with hX
    have hXtop : Subgroup.closure X = ⊤ := by
      rw [hX, Subgroup.closure_union, Subgroup.closure_eq, hgen]
    have hYtop : Subgroup.closure (φ '' X) = ⊤ := by
      rw [← MonoidHom.map_closure, hXtop]
      exact Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective K)
    have hcomK : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ K := by
      intro x hx y hy
      have hz1 : ∀ z ∈ Z, ∀ g : P, ⁅z, g⁆ = 1 := fun z hz g =>
        commutatorElement_eq_one_iff_mul_comm.mpr (hzc z hz g).symm
      have hz2 : ∀ z ∈ Z, ∀ g : P, ⁅g, z⁆ = 1 := fun z hz g =>
        commutatorElement_eq_one_iff_mul_comm.mpr (hzc z hz g)
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · rcases hx with hx | hx <;> rcases hy with hy | hy
          · rw [hx, hy, commutatorElement_self]; exact K.one_mem
          · rw [Set.mem_singleton_iff] at hy
            rw [hx, hy, ← commutatorElement_inv b a, hbaw]; exact K.inv_mem hwK
          · rw [Set.mem_singleton_iff] at hx
            rw [hx, hy, hbaw]; exact hwK
          · rw [Set.mem_singleton_iff] at hx hy
            rw [hx, hy, commutatorElement_self]; exact K.one_mem
        · rw [hz2 y hy]; exact K.one_mem
      · rw [hz1 x hx]; exact K.one_mem
    have hpair : (φ '' X).Pairwise Commute := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
      have h1 : φ ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomK x hx y hy)
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_commute.mp h1
    have : IsMulCommutative ↥(Subgroup.closure (φ '' X)) :=
      Subgroup.isMulCommutative_closure hpair
    intro g h
    have hg : φ g ∈ Subgroup.closure (φ '' X) := by rw [hYtop]; trivial
    have hh : φ h ∈ Subgroup.closure (φ '' X) := by rw [hYtop]; trivial
    have h2 : φ g * φ h = φ h * φ g :=
      congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨φ g, hg⟩ : ↥(Subgroup.closure (φ '' X))) ⟨φ h, hh⟩)
    have h3 : φ ⁅g, h⁆ = 1 := by
      rw [map_commutatorElement]; exact commutatorElement_eq_one_iff_mul_comm.mpr h2
    exact (QuotientGroup.eq_one_iff _).mp h3
  have hcommle : commutator P ≤ K := Subgroup.commutator_le.mpr fun g _ h _ => hcommP g h
  have hZK : Z ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzZ, hzK⟩
    rw [Subgroup.mem_bot]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzK
    obtain ⟨r, hr4, hmr⟩ : ∃ r : ℕ, r < 4 ∧ w ^ m = w ^ r := by
      refine ⟨(m % 4).toNat, by omega, ?_⟩
      have h0 : (((m % 4).toNat : ℕ) : ℤ) = m % 4 :=
        Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
      rw [← zpow_natCast, h0]
      have h4' : w ^ (4 : ℤ) = 1 := by exact_mod_cast hw4
      conv_lhs => rw [← Int.emod_add_mul_ediv m 4, zpow_add, zpow_mul, h4', one_zpow, mul_one]
    rw [hmr] at hzZ ⊢
    by_cases hr0 : r = 0
    · subst hr0; simp only [pow_zero]
    · exfalso
      have e : w ^ r = a ^ (2 * r) * d ^ r := by
        rw [hw, (show Commute (a ^ 2) d from hdc (a ^ 2)).mul_pow, ← pow_mul]
      have h5 : a ^ (2 * r) ∈ Z := by
        have h6 : a ^ (2 * r) = w ^ r * (d ^ r)⁻¹ := by rw [e]; group
        rw [h6]
        exact Z.mul_mem hzZ (Z.inv_mem (Z.pow_mem h3 r))
      have h7 := h4 _ h5
      omega
  rw [eq_bot_iff, ← hZK]
  exact inf_le_inf_left Z hcommle

end CFSG.ClassicalInvolution.Q3.CentralKernel
