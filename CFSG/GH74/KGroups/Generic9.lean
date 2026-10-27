module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.Generic7

public section

namespace CFSG.GH74.KGroups

open scoped commutatorElement Pointwise

section Sylow

variable {K G : Type*} [Group K] [Group G]

theorem exists_conj_of_sylow [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G)
    (hSP : S ≤ P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m) (hm : Odd m)
    (T : Sylow 2 K) :
    ∃ g : K, ∀ k : K, k ∈ (T : Subgroup K) ↔ ((e (g⁻¹ * k * g) : P) : G) ∈ S := by
  classical
  set T0 : Subgroup K := (S.subgroupOf P).comap e.toMonoidHom with hT0
  have hT0mem : ∀ k : K, k ∈ T0 ↔ ((e k : P) : G) ∈ S := fun k => Iff.rfl
  have hcard : Nat.card T0 = 2 ^ v := by
    have h1 : Nat.card T0 = Nat.card (S.subgroupOf P) := by
      refine Nat.card_congr ?_
      exact (MulEquiv.subgroupMap e T0).toEquiv.trans
        (Equiv.subtypeEquivProp (by
          ext y
          simp only [hT0, Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx
          · intro hy
            exact ⟨e.symm y, by simpa using hy, by simp⟩))
    rw [h1, ← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
  have hp0 : IsPGroup 2 T0 := IsPGroup.of_card (n := v) hcard
  have hindex : T0.index = m := by
    have h1 := Subgroup.card_mul_index T0
    rw [hcard, hK] at h1
    have : 0 < 2 ^ v := by positivity
    exact Nat.eq_of_mul_eq_mul_left this h1
  have hnd : ¬ 2 ∣ T0.index := by
    rw [hindex]
    exact fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K (hp0.toSylow hnd) T
  refine ⟨g, fun k => ?_⟩
  have h1 : k ∈ (T : Subgroup K) ↔ g⁻¹ * k * g ∈ T0 := by
    have hT : (T : Subgroup K) = MulAut.conj g • (T0 : Subgroup K) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    rw [hT, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [h1, hT0mem]

end Sylow

section Twist

variable {K G : Type*} [Group K] [Group G]

@[expose] noncomputable def AutModel.twist (M : AutModel K G) (c : MulAut K) : AutModel K G where
  P := M.P
  A := M.A
  e := MulEquiv.trans c M.e
  Φ := (MulAut.conj c).trans M.Φ
  spec := by
    intro φ x
    have h := M.spec (c * φ * c⁻¹) (c x)
    have h1 : (c * φ * c⁻¹) (c x) = c (φ x) := by simp [MulAut.mul_apply]
    rw [h1] at h
    exact h

theorem AutModel.twist_e (M : AutModel K G) (c : MulAut K) (x : K) :
    (M.twist c).e x = M.e (c x) := rfl

end Twist

theorem eq_of_central_diff {C : Type*} [Group C] (hperf : commutator C = ⊤) (Z : Subgroup C)
    (hZ : ∀ z ∈ Z, ∀ g : C, g * z = z * g) (φ₁ φ₂ : C →* C)
    (h : ∀ x : C, φ₁ x * (φ₂ x)⁻¹ ∈ Z) : φ₁ = φ₂ := by
  have hle : commutator C ≤ MonoidHom.eqLocus φ₁ φ₂ := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    show φ₁ ⁅a, b⁆ = φ₂ ⁅a, b⁆
    obtain ⟨za, hza, hza'⟩ : ∃ z ∈ Z, φ₁ a = z * φ₂ a :=
      ⟨φ₁ a * (φ₂ a)⁻¹, h a, by group⟩
    obtain ⟨zb, hzb, hzb'⟩ : ∃ z ∈ Z, φ₁ b = z * φ₂ b :=
      ⟨φ₁ b * (φ₂ b)⁻¹, h b, by group⟩
    rw [map_commutatorElement, map_commutatorElement, hza', hzb']
    exact commutator_central_mul Z hZ za zb _ _ hza hzb
  rw [hperf] at hle
  ext x
  exact hle (Subgroup.mem_top x)

section Fix

variable {K G : Type*} [Group K] [Group G]

theorem AutModel.inner_of_fix_sylow [Finite K] (M : AutModel K G) (S : Subgroup G)
    (hSP : S ≤ M.P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m)
    (hm : Odd m) (hC : ∀ σ ∈ M.A, (∀ q ∈ S, σ * q = q * σ) → σ ∈ S) (T : Sylow 2 K)
    (φ : MulAut K) (hφ : ∀ t ∈ (T : Subgroup K), φ t = t) :
    ∃ k ∈ (T : Subgroup K), ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨g, hg⟩ := exists_conj_of_sylow M.P M.e S hSP hS hK hm T
  set M' : AutModel K G := M.twist (MulAut.conj g⁻¹) with hM'
  have hmem : ∀ k : K, k ∈ (T : Subgroup K) ↔ ((M'.e k : M'.P) : G) ∈ S := by
    intro k
    rw [hg k, hM', AutModel.twist_e, MulAut.conj_apply, inv_inv]
  set σ : G := (M'.Φ φ : G) with hσdef
  have hσA : σ ∈ M.A := (M'.Φ φ).2
  have hcomm : ∀ q ∈ S, σ * q = q * σ := by
    intro q hq
    obtain ⟨t, hq'⟩ := M'.e.surjective ⟨q, hSP hq⟩
    have hqt : ((M'.e t : M'.P) : G) = q := congrArg Subtype.val hq'
    have ht : t ∈ (T : Subgroup K) := (hmem t).2 (by rw [hqt]; exact hq)
    have h1 := M'.spec φ t
    rw [hφ t ht, hqt] at h1
    calc σ * q = (σ * q * σ⁻¹) * σ := by group
      _ = q * σ := by rw [← h1]
  have hσS : σ ∈ S := hC σ hσA hcomm
  have hσP : σ ∈ M'.P := hSP hσS
  refine ⟨M'.e.symm ⟨σ, hσP⟩, (hmem _).2 (by simpa using hσS), fun x => ?_⟩
  apply M'.e.injective
  apply Subtype.ext
  rw [M'.spec]
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

theorem aut_fix_sylow_trivial {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center K))
    (hZP : ∀ P : Sylow 2 K, Subgroup.center ↥(P : Subgroup K) =
      (Subgroup.center K).subgroupOf (P : Subgroup K))
    (M : AutModel (K ⧸ Subgroup.center K) G) (S : Subgroup G) (hSP : S ≤ M.P) {v m : ℕ}
    (hS : Nat.card S = 2 ^ v) (hK : Nat.card (K ⧸ Subgroup.center K) = 2 ^ v * m) (hm : Odd m)
    (hC : ∀ σ ∈ M.A, (∀ q ∈ S, σ * q = q * σ) → σ ∈ S) (P : Sylow 2 K) (φ : MulAut K)
    (hφ : ∀ g ∈ (P : Subgroup K), φ g = g) : φ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup K := Subgroup.center K with hZdef
  have hZP' : Z ≤ (P : Subgroup K) := hZ2.le_sylow_of_normal P
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hT2 : IsPGroup 2 ((P : Subgroup K).map π) := P.isPGroup'.map π
  have hTi : ¬ 2 ∣ ((P : Subgroup K).map π).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.index_map_dvd (P : Subgroup K) hπ))
  let T : Sylow 2 (K ⧸ Z) := hT2.toSylow hTi
  let φb : MulAut (K ⧸ Z) := QuotientGroup.congr Z Z φ (Subgroup.map_center_eq φ)
  have hφb : ∀ x : K, φb (π x) = π (φ x) := fun x => rfl
  have hφbT : ∀ t ∈ (T : Subgroup (K ⧸ Z)), φb t = t := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := (Subgroup.mem_map).1 ht
    rw [hφb, hφ p hp]
  obtain ⟨kb, hkbT, hkb⟩ := M.inner_of_fix_sylow S hSP hS hK hm hC T φb hφbT
  obtain ⟨k, rfl⟩ := hπ kb
  have hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.1 hz g
  have hconj : (φ : K →* K) = (MulAut.conj k : K →* K) := by
    apply eq_of_central_diff hperf Z hZc
    intro x
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    have h1 := hkb (π x)
    rw [hφb] at h1
    change π (φ x) * (π (k * x * k⁻¹))⁻¹ = 1
    rw [map_mul, map_mul, map_inv, ← h1]
    group
  have hkP : k ∈ (P : Subgroup K) := by
    obtain ⟨p, hp, hpk⟩ := (Subgroup.mem_map).1 hkbT
    have h1 : p⁻¹ * k ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, hpk, inv_mul_cancel]
    have h2 : k = p * (p⁻¹ * k) := by group
    rw [h2]
    exact (P : Subgroup K).mul_mem hp (hZP' h1)
  have hkc : ∀ y : (P : Subgroup K), y * (⟨k, hkP⟩ : (P : Subgroup K)) = ⟨k, hkP⟩ * y := by
    intro y
    apply Subtype.ext
    have h1 : φ y.1 = y.1 := hφ y.1 y.2
    have h2 : φ y.1 = k * y.1 * k⁻¹ := by
      have := congrArg (fun f : K →* K => f y.1) hconj
      simpa using this
    rw [h1] at h2
    simp only [Subgroup.coe_mul]
    calc y.1 * k = (k * y.1 * k⁻¹) * k := by rw [← h2]
      _ = k * y.1 := by group
  have hkZ : k ∈ Z := by
    have h1 : (⟨k, hkP⟩ : (P : Subgroup K)) ∈ Subgroup.center ↥(P : Subgroup K) :=
      Subgroup.mem_center_iff.2 hkc
    rw [hZP P] at h1
    exact h1
  ext x
  have := congrArg (fun f : K →* K => f x) hconj
  simp only [MulAut.one_apply]
  have h2 : φ x = k * x * k⁻¹ := by simpa using this
  rw [h2, ← hZc k hkZ x]
  group

end Fix

end CFSG.GH74.KGroups
