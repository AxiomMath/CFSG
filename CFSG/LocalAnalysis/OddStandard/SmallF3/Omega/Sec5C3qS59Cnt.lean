module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Step56

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5c3q_pair_card [Finite G] {C : Subgroup G} {τ : G} (hτ : τ ∈ C) {P : Set G}
    (hPC : P ⊆ (C : Set G)) (hP : ∀ x ∈ P, τ * x ∉ P) : 2 * P.ncard ≤ Nat.card C := by
  have hinj : Function.Injective (fun x : G => τ * x) := mul_right_injective τ
  have hQC : (fun x : G => τ * x) '' P ⊆ (C : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact C.mul_mem hτ (hPC hx)
  have hdisj : Disjoint P ((fun x : G => τ * x) '' P) := by
    rw [Set.disjoint_left]
    rintro y hyP ⟨x, hxP, rfl⟩
    exact hP x hxP hyP
  have hunion : (P ∪ (fun x : G => τ * x) '' P).ncard = 2 * P.ncard := by
    rw [Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ hinj]
    ring
  have hsub : P ∪ (fun x : G => τ * x) '' P ⊆ (C : Set G) := Set.union_subset hPC hQC
  calc 2 * P.ncard = (P ∪ (fun x : G => τ * x) '' P).ncard := hunion.symm
    _ ≤ (C : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card C := (Nat.card_coe_set_eq (C : Set G)).symm

theorem sec5c3q_card_le_two [Finite G] {L D : Subgroup G}
    (hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))))
    (hD : D ≤ centralizer (L : Set G)) (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hsq : ∀ x ∈ D, x * x = 1) : Nat.card D ≤ 2 := by
  by_cases h : ∃ y ∈ D, y ≠ 1
  · obtain ⟨y, hyD, hy1⟩ := h
    have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq y hyD) hy1
    have hsub : (D : Set G) ⊆ {1, y} := by
      intro x hx
      rcases sec4_eq_of_commute hcyc (hD hx) (hD hyD) (hsq x hx) hy2 (hcomm x hx y hyD) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    calc Nat.card D = (D : Set G).ncard := (Nat.card_coe_set_eq (D : Set G)).symm
      _ ≤ ({1, y} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le 1 {y}).trans ?_
        rw [Set.ncard_singleton]
  · push Not at h
    have hsub : (D : Set G) ⊆ {1} := fun x hx => Set.mem_singleton_iff.mpr (h x hx)
    calc Nat.card D = (D : Set G).ncard := (Nat.card_coe_set_eq (D : Set G)).symm
      _ ≤ ({1} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by rw [Set.ncard_singleton]; norm_num

theorem sec5c3q_card_eq_32 [Finite G] {A C : Subgroup G} (hCA : C ≤ A) (hA : Nat.card A = 64)
    (hne : C ≠ A) (h30 : 30 ≤ Nat.card C) : Nat.card C = 32 := by
  have hdvd : Nat.card C ∣ 2 ^ 6 := by
    have := Subgroup.card_dvd_of_le hCA
    rwa [hA] at this
  obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hlt : Nat.card C < 64 := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [← hA]
      exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hCA)
    · intro h64
      exact hne (Subgroup.eq_of_le_of_card_ge hCA (by rw [hA, h64]))
  rw [hCk] at h30 hlt ⊢
  interval_cases k <;> simp_all

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

theorem sec5c3q_s59_card_inter (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a) (hZ : Asc82ZExists)
    (n1 : Asc82E64Kind3) (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ)
    {g₀ : G} (hg₀ : g₀⁻¹ * t * g₀ = t * z) {a : G} (haA : a ∈ A)
    (haL : a ∉ CFSG.conjugate L g₀) : Nat.card ↥(A ⊓ CFSG.conjugate L g₀) = 32 := by
  have h := hR.toSec5Ctx
  have h' := sec5_step56_ctx hy.h52b hy.h53 hy.h37 hZ hy.tab h hg₀
  have hL1 : IsOm6Z2 (CFSG.conjugate L g₀) := h'.toSec5Setting.isOm6Z2
  have htzZ : t * z ∈ centerIn (CFSG.conjugate L g₀) :=
    sec5_t_mem_centerIn hy.h52b h'.toSec5Setting
  have htz2 : orderOf (t * z) = 2 := h'.involution
  have htzL1 : t * z ∈ CFSG.conjugate L g₀ := (sec5_mem_centerIn_iff.mp htzZ).1
  have htzA : t * z ∈ A := A.mul_mem hm.mem_A.1 hm.mem_A.2.2
  have hAN : A ≤ normalizer (CFSG.conjugate L g₀ : Set G) := fun x hx =>
    sec4_mem_normalizer hy.h36 h'.toSec3SettingLB x (h'.sylow.1 (hR.A_le hx))
  have hAC : Nat.card ↥(A ⊓ centralizer (CFSG.conjugate L g₀ : Set G)) ≤ 2 :=
    sec5c3q_card_le_two (h52a G (t * z) (CFSG.conjugate L g₀) h'.toSec5Setting) inf_le_right
      (fun x hx y hy => sec5c3q_A_comm hm (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hy).1)
      (fun x hx => sec5c3q_A_sq hm (Subgroup.mem_inf.mp hx).1)
  have hT3 := n1 G (CFSG.conjugate L g₀) hL1 A hAN (sec5c3q_A_isElemAb2 hm) hAC
  have hP2 : 2 * {x : G | x ∈ A ⊓ CFSG.conjugate L g₀ ∧ IsI4PlusIn (CFSG.conjugate L g₀) x}.ncard ≤
      Nat.card ↥(A ⊓ CFSG.conjugate L g₀) := by
    refine sec5c3q_pair_card (τ := t * z) (Subgroup.mem_inf.mpr ⟨htzA, htzL1⟩)
      (fun x hx => hx.1) ?_
    intro x hx hx'
    exact hy.tab.tz_not_pocket G _ hL1 (t * z) htzZ htz2 x hx.2 hx'.2
  have hzM : conjClassIn (normalizer (A : Set G)) z ⊆
      {x : G | x ∈ A ⊓ CFSG.conjugate L g₀ ∧ IsI4PlusIn (CFSG.conjugate L g₀) x} ∪
        {x : G | x ∈ A ∧ ∃ α : ℤˣ, InducesTypeSome (CFSG.conjugate L g₀) x 6 (-1) 3 α} := by
    rintro y ⟨m, hmM, rfl⟩
    have hyA : m * z * m⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hmM z).mp hm.mem_A.2.2
    have hyC : (m⁻¹)⁻¹ * z * m⁻¹ ∈ centralizer ({t * z} : Set G) := by
      rw [inv_inv, Subgroup.mem_centralizer_singleton_iff]
      exact sec5c3q_A_comm hm hyA htzA
    rcases hy.h54 G (t * z) (CFSG.conjugate L g₀) S z h' m⁻¹ hyC with hcl | ⟨α, hα⟩
    · rw [inv_inv] at hcl
      obtain ⟨c, hc, hcz⟩ := hcl
      left
      refine ⟨Subgroup.mem_inf.mpr ⟨hyA, ?_⟩, ?_⟩
      · rw [hcz]
        exact (CFSG.conjugate L g₀).mul_mem
          ((CFSG.conjugate L g₀).mul_mem hc h'.pocket.mem) ((CFSG.conjugate L g₀).inv_mem hc)
      · rw [hcz]
        exact IsI4PlusIn.conj_of_mem h'.pocket hc
    · rw [inv_inv] at hα
      exact Or.inr ⟨hyA, α, hα⟩
  have h35 := sec5b_zM_ncard hy hR hm
  have hle : 35 ≤
      {x : G | x ∈ A ⊓ CFSG.conjugate L g₀ ∧ IsI4PlusIn (CFSG.conjugate L g₀) x}.ncard +
        {x : G | x ∈ A ∧ ∃ α : ℤˣ,
          InducesTypeSome (CFSG.conjugate L g₀) x 6 (-1) 3 α}.ncard := by
    calc 35 = (conjClassIn (normalizer (A : Set G)) z).ncard := h35.symm
      _ ≤ _ := Set.ncard_le_ncard hzM (Set.toFinite _)
      _ ≤ _ := Set.ncard_union_le _ _
  have hne : A ⊓ CFSG.conjugate L g₀ ≠ A := by
    intro heq
    have haC : a ∈ A ⊓ CFSG.conjugate L g₀ := by
      rw [heq]
      exact haA
    exact haL (Subgroup.mem_inf.mp haC).2
  exact sec5c3q_card_eq_32 inf_le_left hm.perm.card_A hne (by omega)

end CFSG.OddStandard.SmallF3.Omega
