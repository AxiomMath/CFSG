module

public import CFSG.GH74.KGroups.Generic3
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.KGroups

theorem exists_subgroup_card_two_mul {K : Type*} [Group K] [Finite K] [Nontrivial K]
    (h2 : IsPGroup 2 K) : ∃ M : Subgroup K, Nat.card K = 2 * Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K = 1 := by simpa using hm
    exact (Finite.one_lt_card (α := K)).ne' h1
  obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := m - 1) Nat.prime_two
    h2 (by rw [hm]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m 1))
  refine ⟨M, ?_⟩
  rw [hm, hM, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]

theorem exists_double_cover {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (hJ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥) :
    ∃ (C : Type) (_ : Group C) (_ : Finite C) (φ : K →* C), Function.Surjective φ ∧
      IsPGroup 2 φ.ker ∧ commutator C = ⊤ ∧ Nat.card (Subgroup.center C) = 2 ∧
      Nonempty (C ⧸ Subgroup.center C ≃* K ⧸ Subgroup.center K) := by
  classical
  set Z : Subgroup K := Subgroup.center K with hZdef
  have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨M₀, hM₀⟩ := exists_subgroup_card_two_mul hZ2
  set M : Subgroup K := M₀.map Z.subtype with hMdef
  have hMZ : M ≤ Z := Subgroup.map_subtype_le M₀
  have hMcard : Nat.card Z = 2 * Nat.card M := by
    rw [hM₀, hMdef, Subgroup.card_map_of_injective Z.subtype_injective]
  have : M.Normal := Subgroup.normal_of_le_center hMZ
  let φ : K →* K ⧸ M := QuotientGroup.mk' M
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective M
  have hker : φ.ker = M := QuotientGroup.ker_mk' M
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  let ψ : K ⧸ M →* K ⧸ Z := QuotientGroup.lift M π (by rw [hπker]; exact hMZ)
  have hψφ : ∀ x : K, ψ (φ x) = π x := fun x => rfl
  have hψ : Function.Surjective ψ := by
    intro j
    obtain ⟨x, rfl⟩ := hπ j
    exact ⟨φ x, hψφ x⟩
  have hmemZ : ∀ x : K, x ∈ Z ↔ π x = 1 := fun x => by rw [← MonoidHom.mem_ker, hπker]
  have hψker : ψ.ker = Subgroup.center (K ⧸ M) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨x, rfl⟩ := hφ q
      have hx : x ∈ Z := (hmemZ x).2 (by rw [← hψφ]; exact hq)
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hφ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    · intro q hq
      have h1 : ψ q ∈ Subgroup.center (K ⧸ Z) := by
        rw [Subgroup.mem_center_iff]
        intro j
        obtain ⟨r, rfl⟩ := hψ j
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hq r]
      rw [hJ, Subgroup.mem_bot] at h1
      exact h1
  have hJpos : 0 < Nat.card (K ⧸ Z) := Nat.card_pos
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hπcard := Subgroup.card_ker_mul_card_of_surjective hπ
  have hQ := Subgroup.card_ker_mul_card_of_surjective hψ
  have hKM := Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hkerQcard : Nat.card ψ.ker = 2 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hJpos hMpos) ?_
    calc Nat.card ψ.ker * (Nat.card (K ⧸ Z) * Nat.card M)
        = (Nat.card ψ.ker * Nat.card (K ⧸ Z)) * Nat.card M := by ring
      _ = Nat.card K := by rw [hQ, ← hKM]
      _ = Nat.card π.ker * Nat.card (K ⧸ Z) := hπcard.symm
      _ = 2 * (Nat.card (K ⧸ Z) * Nat.card M) := by rw [hπker, hMcard]; ring
  have hperfK : Group.IsPerfect K := ⟨hperf⟩
  have hperfC : Group.IsPerfect (K ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := φ) hφ
  refine ⟨K ⧸ M, inferInstance, inferInstance, φ, hφ, ?_, hperfC.commutator_eq_top, ?_, ?_⟩
  · rw [hker]
    exact hZ2.to_le hMZ
  · rw [← hψker]; exact hkerQcard
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem sectional_le_of_surjective {K C : Type*} [Group K] [Finite K] [Group C] (φ : K →* C)
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) (r : ℕ)
    (h : ∀ P : Subgroup K, IsPGroup 2 P → ∃ s : Finset K, s.card ≤ r ∧
      Subgroup.closure (s : Set K) = P) :
    ∀ Q : Subgroup C, IsPGroup 2 Q → ∃ s : Finset C, s.card ≤ r ∧
      Subgroup.closure (s : Set C) = Q := by
  classical
  intro Q hQ
  have hP : IsPGroup 2 (Q.comap φ) := hQ.comap_of_ker_isPGroup φ hker
  obtain ⟨s, hs, hcl⟩ := h _ hP
  refine ⟨s.image φ, (Finset.card_image_le).trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hcl, Subgroup.map_comap_eq_self_of_surjective hφ]

theorem elementary_of_conj {K : Type*} [Group K] (A Z : Subgroup K)
    (hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hsq : ∀ a ∈ A, a ^ 2 ∈ Z)
    (hconj : ∀ x ∈ A, x ∉ Z → ∀ y ∈ A, y ∉ Z → ∃ g : K, ∃ z ∈ Z, g * x * g⁻¹ = y * z)
    (a b d : K) (ha : a ∈ A) (hb : b ∈ A) (hd : d ∈ A)
    (haZ : a ∉ Z) (hbZ : b ∉ Z) (hdZ : d ∉ Z) (habZ : a * b ∉ Z) (hadZ : a * d ∉ Z)
    (hbdZ : b * d ∉ Z) (habdZ : a * (b * d) ∉ Z) :
    ∀ x ∈ A, x ^ 2 = 1 ∧ ∀ y ∈ A, x * y = y * x := by
  have hsame : ∀ x ∈ A, x ∉ Z → ∀ y ∈ A, y ∉ Z → x ^ 2 = y ^ 2 := by
    intro x hx hxZ y hy hyZ
    obtain ⟨g, z, hz, hk⟩ := hconj x hx hxZ y hy hyZ
    have h1 : (g * x * g⁻¹) ^ 2 = x ^ 2 := by
      have hc := hZc (x ^ 2) (hsq x hx) g
      rw [conj_pow, hc]
      group
    have h2 : (y * z) ^ 2 = y ^ 2 := by
      have hzc : z * y = y * z := (hZc z hz y).symm
      have hz2 := hZ2 z hz
      calc (y * z) ^ 2 = y * (z * y) * z := by rw [pow_two]; group
        _ = y * y * (z * z) := by rw [hzc]; group
        _ = y ^ 2 := by rw [← pow_two z, hz2, mul_one, pow_two]
    rw [← h1, hk, h2]
  have hcZ : a ^ 2 ∈ Z := hsq a ha
  by_cases hc1 : a ^ 2 = 1
  · have hall : ∀ x ∈ A, x ^ 2 = 1 := by
      intro x hx
      by_cases hxZ : x ∈ Z
      · exact hZ2 x hxZ
      · rw [hsame x hx hxZ a ha haZ, hc1]
    refine fun x hx => ⟨hall x hx, fun y hy => ?_⟩
    have hinv : ∀ w ∈ A, w⁻¹ = w := fun w hw =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hall w hw)
    have h1 : (x * y)⁻¹ = x * y := hinv _ (A.mul_mem hx hy)
    rw [mul_inv_rev, hinv x hx, hinv y hy] at h1
    exact h1.symm
  · exfalso
    set c := a ^ 2 with hcdef
    have hcc : ∀ g : K, g * c = c * g := hZc c hcZ
    have hcsq : c ^ 2 = 1 := hZ2 c hcZ
    have hsqx : ∀ x ∈ A, x ∉ Z → x ^ 2 = c := fun x hx hxZ => hsame x hx hxZ a ha haZ
    have hcomm_eq : ∀ y ∈ A, y ∉ Z → a * y ∉ Z → a * y * a⁻¹ * y⁻¹ = c := by
      intro y hy hyZ hay
      have h := comm_eq_sq a y c (a * y * a⁻¹ * y⁻¹) rfl (hsqx y hy hyZ) hcc hcsq rfl
      rw [← h]
      exact hsqx _ (A.mul_mem ha hy) hay
    have e1 := hcomm_eq b hb hbZ habZ
    have e2 := hcomm_eq d hd hdZ hadZ
    have e3 := hcomm_eq (b * d) (A.mul_mem hb hd) hbdZ habdZ
    have hid : a * (b * d) * a⁻¹ * (b * d)⁻¹ =
        (a * b * a⁻¹ * b⁻¹) * (b * (a * d * a⁻¹ * d⁻¹) * b⁻¹) := by group
    rw [e1, e2, e3, hcc b] at hid
    rw [mul_inv_cancel_right] at hid
    exact hc1 (by simpa using hid)

end CFSG.GH74.KGroups
