module

public import CFSG.GF2Type.CenterFour.CaseBPsiHom
public import CFSG.GF2Type.CenterFour.CaseBCard

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem mul_self_eq_one_of_config (hC : Config z n) : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rwa [hC.orderOf_eq, sq] at h

omit [Finite G] in
private theorem conj_mul_self_eq_one {z : G} (hz : z * z = 1) (g : G) :
    (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
  rw [show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hz]
  group

omit [Finite G] in
private theorem psi_one' {z₁ : G} (hz₁ : z₁ * z₁ = 1) : psi z₁ 1 = 1 := by
  simp [psi, hz₁]

private theorem mul_z_mem_image (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {q : G} (hq : q ∈ coreAt z) :
    psi (g⁻¹ * z * g) q * z ∈ (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G) := by
  obtain ⟨k, hZk, hk4, hk2⟩ := hC.exists_generator
  have hkZ : k ∈ centerAt z := by
    rw [hZk]
    exact Subgroup.mem_zpowers k
  exact ⟨q * k, Subgroup.mul_mem _ hq (hC.center_le_core hkZ),
    CaseB.psi_mul_generator hC hH hK hZk hk4 hk2 hq⟩

private theorem mul_mem_image (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {q q' : G}
    (hq : q ∈ coreAt z) (hq' : q' ∈ coreAt z) :
    psi (g⁻¹ * z * g) q * psi (g⁻¹ * z * g) q' ∈
      (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G) := by
  have hz2 := mul_self_eq_one_of_config hC
  have hz₁ := conj_mul_self_eq_one hz2 g
  rcases CaseB.conj_psi hC hH hq hq' with h | h
  · have e : psi (g⁻¹ * z * g) (q * q') = psi (g⁻¹ * z * g) q * psi (g⁻¹ * z * g) q' := by
      rw [CaseB.psi_mul hz₁, h]
    exact ⟨q * q', Subgroup.mul_mem _ hq hq', e⟩
  · have e : psi (g⁻¹ * z * g) (q * q') = psi (g⁻¹ * z * g) q * psi (g⁻¹ * z * g) q' * z := by
      rw [CaseB.psi_mul hz₁, h]
      exact (mul_assoc _ _ _).symm
    have key : psi (g⁻¹ * z * g) q * psi (g⁻¹ * z * g) q' =
        psi (g⁻¹ * z * g) (q * q') * z := by
      rw [e, mul_assoc _ z z, hz2, mul_one]
    rw [key]
    exact mul_z_mem_image hC hH hK (Subgroup.mul_mem _ hq hq')

private theorem exists_eq_mul_of_sq_eq_z (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {q₀ q : G}
    (hq₀ : q₀ ∈ coreAt z) (hsq₀ : psi (g⁻¹ * z * g) q₀ ^ 2 = z)
    (hq : q ∈ coreAt z) (hsq : psi (g⁻¹ * z * g) q ^ 2 = z) :
    ∃ j, (j ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ∧
        j ∈ (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G)) ∧
      psi (g⁻¹ * z * g) q = psi (g⁻¹ * z * g) q₀ * j := by
  have hz2 := mul_self_eq_one_of_config hC
  have hz₁ := conj_mul_self_eq_one hz2 g
  have hsqinv : psi (g⁻¹ * z * g) q₀⁻¹ ^ 2 = z := by
    have h := CaseB.psi_sq_mul hC hH hK (inv_mem hq₀) hq₀
    rw [inv_mul_cancel q₀, psi_one' hz₁, one_pow, hsq₀] at h
    exact (eq_inv_of_mul_eq_one_left h.symm).trans (inv_eq_of_mul_eq_one_right hz2)
  have hr : q₀⁻¹ * q ∈ coreAt z := Subgroup.mul_mem _ (inv_mem hq₀) hq
  have hsr : psi (g⁻¹ * z * g) (q₀⁻¹ * q) ^ 2 = 1 := by
    rw [CaseB.psi_sq_mul hC hH hK (inv_mem hq₀) hq, hsqinv, hsq]
    exact hz2
  have hψr : psi (g⁻¹ * z * g) (q₀⁻¹ * q) ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) :=
    (psi_mem_iff_sq_eq_one hC hz₁ hH hr).mpr hsr
  have e : psi (g⁻¹ * z * g) q = psi (g⁻¹ * z * g) q₀ *
      (q₀ * psi (g⁻¹ * z * g) (q₀⁻¹ * q) * q₀⁻¹) := by
    have h := CaseB.psi_mul hz₁ q₀ (q₀⁻¹ * q)
    rw [mul_inv_cancel_left q₀ q] at h
    exact h
  rcases CaseB.conj_psi hC hH hq₀ hr with h | h
  · refine ⟨psi (g⁻¹ * z * g) (q₀⁻¹ * q), ⟨hψr, ⟨q₀⁻¹ * q, hr, rfl⟩⟩, ?_⟩
    rw [e, h]
  · refine ⟨psi (g⁻¹ * z * g) (q₀⁻¹ * q) * z,
      ⟨Subgroup.mul_mem _ hψr (CaseB.mem hC hH), mul_z_mem_image hC hH hK hr⟩, ?_⟩
    rw [e, h]

private theorem exists_subgroup_psi (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    ∃ J : Subgroup G, (J : Set G) = {x | x ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ∧
        x ∈ (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G)} := by
  have hz2 := mul_self_eq_one_of_config hC
  have hz₁ := conj_mul_self_eq_one hz2 g
  let S : Set G := {x | x ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ∧
    x ∈ (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G)}
  refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro a b ⟨ha1, q, hq, rfl⟩ ⟨hb1, q', hq', rfl⟩
    exact ⟨Subgroup.mul_mem _ ha1 hb1, mul_mem_image hC hH hK hq hq'⟩
  · exact ⟨one_mem _, 1, one_mem _, psi_one' hz₁⟩
  · rintro x ⟨hx1, q, hq, rfl⟩
    have hsq : psi (g⁻¹ * z * g) q ^ 2 = 1 := (psi_mem_iff_sq_eq_one hC hz₁ hH hq).mp hx1
    have hinv : (psi (g⁻¹ * z * g) q)⁻¹ = psi (g⁻¹ * z * g) q :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq)
    rw [hinv]
    exact ⟨hx1, q, hq, rfl⟩

theorem CaseB.dichotomy (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    (∀ q ∈ coreAt z, psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ∨
      ((∃ q ∈ coreAt z,
          psi (g⁻¹ * z * g) q ∉ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ∧
        ∃ J : Subgroup G, J ≤ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ∧
          Nat.card J = 2 ^ n ∧ ∀ j ∈ J, ∃ q ∈ coreAt z, psi (g⁻¹ * z * g) q = j) := by
  have hz2 := mul_self_eq_one_of_config hC
  have hz₁ := conj_mul_self_eq_one hz2 g
  by_cases hall : ∀ q ∈ coreAt z,
      psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨q₀, hq₀, hψ₀⟩ := hall
  have hsq₀ : psi (g⁻¹ * z * g) q₀ ^ 2 = z := by
    rcases hC.sq_eq _ (psi_mem_core hC hz₁ hH hq₀) with h | h
    · exact absurd ((psi_mem_iff_sq_eq_one hC hz₁ hH hq₀).mpr h) hψ₀
    · exact h
  refine ⟨⟨q₀, hq₀, hψ₀⟩, ?_⟩
  obtain ⟨J, hJ⟩ := exists_subgroup_psi hC hH hK
  have hmemJ : ∀ x, x ∈ J ↔ (x ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ∧
      x ∈ (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G)) := by
    intro x
    rw [← SetLike.mem_coe, hJ]
    rfl
  have hT : (fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G) =
      (J : Set G) ∪ (fun j => psi (g⁻¹ * z * g) q₀ * j) '' (J : Set G) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hC.sq_eq _ (psi_mem_core hC hz₁ hH hq) with h1 | h1
      · refine Set.mem_union_left _ ?_
        rw [SetLike.mem_coe, hmemJ]
        exact ⟨(psi_mem_iff_sq_eq_one hC hz₁ hH hq).mpr h1, q, hq, rfl⟩
      · obtain ⟨j, hj, hej⟩ := exists_eq_mul_of_sq_eq_z hC hH hK hq₀ hsq₀ hq h1
        exact Set.mem_union_right _ ⟨j, (hmemJ j).mpr hj, hej.symm⟩
    · rintro (hxJ | ⟨j, hjJ, rfl⟩)
      · exact ((hmemJ x).mp hxJ).2
      · obtain ⟨-, r, hr, hrj⟩ := (hmemJ j).mp hjJ
        rw [← hrj]
        exact mul_mem_image hC hH hK hq₀ hr
  have hrange : Set.ncard ((fun x => psi (g⁻¹ * z * g) x) '' (coreAt z : Set G)) =
      2 ^ (n + 1) := by
    have h := CaseB.ncard_range_psi hC (g⁻¹ * z * g)
    have h2 : (2 : ℕ) ^ (2 * n + 2) = 2 ^ (n + 1) * 2 ^ (n + 1) := by
      rw [← pow_add]
      ring_nf
    rw [CaseB.card hC hH hK, hC.card_core, h2] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) _) h
  have hdisj : Disjoint (J : Set G) ((fun j => psi (g⁻¹ * z * g) q₀ * j) '' (J : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hxJ ⟨j, hjJ, rfl⟩
    have hx1 := ((hmemJ _).mp hxJ).1
    have hj1 := ((hmemJ j).mp hjJ).1
    apply hψ₀
    have := Subgroup.mul_mem _ hx1 (inv_mem hj1)
    rwa [mul_inv_cancel_right] at this
  have hcardJ : Set.ncard (J : Set G) = 2 ^ n := by
    have h := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [← hT, hrange, Set.ncard_image_of_injective _ (mul_right_injective _)] at h
    rw [pow_succ] at h
    omega
  refine ⟨J, fun x hx => ((hmemJ x).mp hx).1, ?_, fun j hj => ?_⟩
  · rw [← hcardJ, ← Nat.card_coe_set_eq]
    rfl
  · obtain ⟨-, q, hq, hqj⟩ := (hmemJ j).mp hj
    exact ⟨q, hq, hqj⟩

end CFSG.GF2Type.CenterFour
