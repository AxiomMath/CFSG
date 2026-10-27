module

public import CFSG.ClassicalInvolution.Asc77.AscE187P1a

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_pair_in_E {B W₁ : Subgroup G} {b z₁ : G} (hBp : IsPGroup 2 B)
    (hBb : IsUniqueInvolution B b) (hB8 : 8 ≤ Nat.card B)
    (hW₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y = y * x) (hBW₁ : ∀ β ∈ B, conjSub β W₁ = W₁)
    (hz₁W : z₁ ∈ W₁) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1) (hbz : ¬ b * z₁ = z₁ * b) :
    ∃ E : Subgroup G, ∃ u v : G,
      E = Subgroup.closure (Set.range fun β : ↥B => (β : G) * z₁ * (β : G)⁻¹) ∧
      E ≤ W₁ ∧ (∀ w ∈ E, w * w = 1) ∧ u ∈ E ∧ v ∈ E ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      b * u = u * b ∧ b * v = v * b := by
  classical
  set X : Set G := Set.range fun β : ↥B => (β : G) * z₁ * (β : G)⁻¹ with hX
  have hXW : X ⊆ W₁ := by
    rintro _ ⟨β, rfl⟩
    have := conj_mem_conjSub (n := (β : G)) hz₁W
    rwa [hBW₁ β β.2] at this
  have hXsq : ∀ x ∈ X, x * x = 1 := by
    rintro _ ⟨β, rfl⟩
    calc (β : G) * z₁ * (β : G)⁻¹ * ((β : G) * z₁ * (β : G)⁻¹)
        = (β : G) * (z₁ * z₁) * (β : G)⁻¹ := by group
      _ = 1 := by rw [hz₁2]; group
  set E : Subgroup G := Subgroup.closure X with hE
  have hEW : E ≤ W₁ := (Subgroup.closure_le W₁).mpr hXW
  have hEsq : ∀ w ∈ E, w * w = 1 := fun w hw => sq_eq_one_of_mem_closure hW₁ hXW hXsq hw
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => hW₁ x (hEW hx) y (hEW hy)
  have hinj : Function.Injective fun β : ↥B => (β : G) * z₁ * (β : G)⁻¹ := by
    intro β β' hββ'
    have hγ : ((β' : G)⁻¹ * β) * z₁ * ((β' : G)⁻¹ * β)⁻¹ = z₁ := by
      have h1 : (β : G) * z₁ * (β : G)⁻¹ = (β' : G) * z₁ * (β' : G)⁻¹ := hββ'
      calc ((β' : G)⁻¹ * β) * z₁ * ((β' : G)⁻¹ * β)⁻¹
          = (β' : G)⁻¹ * ((β : G) * z₁ * (β : G)⁻¹) * (β' : G) := by group
        _ = (β' : G)⁻¹ * ((β' : G) * z₁ * (β' : G)⁻¹) * (β' : G) := by rw [h1]
        _ = z₁ := by group
    by_contra hne
    have hγ1 : (β' : G)⁻¹ * β ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      exact (inv_mul_eq_one.mp h1).symm
    have hγB : (β' : G)⁻¹ * β ∈ B := B.mul_mem (B.inv_mem β'.2) β.2
    have hb_mem : b ∈ Subgroup.zpowers ((β' : G)⁻¹ * β) :=
      mem_zpowers_of_isUniqueInvolution hBb hγB hγ1 (hBp.to_le (Subgroup.zpowers_le.mpr hγB))
    have hcomm : Commute ((β' : G)⁻¹ * β) z₁ := by
      have : ((β' : G)⁻¹ * β) * z₁ = z₁ * ((β' : G)⁻¹ * β) := by
        calc ((β' : G)⁻¹ * β) * z₁ = (((β' : G)⁻¹ * β) * z₁ * ((β' : G)⁻¹ * β)⁻¹) *
            ((β' : G)⁻¹ * β) := by group
          _ = z₁ * ((β' : G)⁻¹ * β) := by rw [hγ]
      exact this
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb_mem
    apply hbz
    have := (hcomm.zpow_left m).eq
    rw [← hm]
    exact this
  have hXcard : 8 ≤ X.ncard := by
    have h1 : Nat.card X = Nat.card ↥B := Nat.card_range_of_injective hinj
    have h2 : Nat.card X = X.ncard := Nat.card_coe_set_eq X
    omega
  have h1X : (1 : G) ∉ X := by
    rintro ⟨β, hβ⟩
    have : z₁ = 1 := by
      have h2 : (β : G) * z₁ * (β : G)⁻¹ = 1 := hβ
      calc z₁ = (β : G)⁻¹ * ((β : G) * z₁ * (β : G)⁻¹) * (β : G) := by group
        _ = 1 := by rw [h2]; group
    exact hz₁1 this
  have hEcard : 9 ≤ Nat.card E := by
    have hsub : X ⊂ (E : Set G) := by
      refine ⟨Subgroup.subset_closure, fun hle => h1X (hle E.one_mem)⟩
    have h1 : X.ncard < (E : Set G).ncard := Set.ncard_lt_ncard hsub (Set.toFinite _)
    have h2 : (E : Set G).ncard = Nat.card E := by
      rw [← Nat.card_coe_set_eq]
      rfl
    omega
  have hEp : IsPGroup 2 E := fun g => ⟨1, by
    apply Subtype.ext
    have := hEsq g g.2
    simpa [pow_two] using this⟩
  have hE16 : 16 ≤ Nat.card E := by
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    by_contra hlt
    push Not at hlt
    have hn4 : n < 4 := by
      by_contra h4
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> omega
  have hbE : conjSub b E = E := by
    have hmem : ∀ γ ∈ B, ∀ e ∈ E, γ * e * γ⁻¹ ∈ E := by
      intro γ hγ e he
      induction he using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨β, rfl⟩ := hx
        have : γ * ((β : G) * z₁ * (β : G)⁻¹) * γ⁻¹ =
            ((⟨γ, hγ⟩ * β : ↥B) : G) * z₁ * ((⟨γ, hγ⟩ * β : ↥B) : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
        rw [this]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      | one => simp
      | mul a a' _ _ ha ha' =>
        have : γ * (a * a') * γ⁻¹ = (γ * a * γ⁻¹) * (γ * a' * γ⁻¹) := by group
        rw [this]
        exact E.mul_mem ha ha'
      | inv a _ ha =>
        have : γ * a⁻¹ * γ⁻¹ = (γ * a * γ⁻¹)⁻¹ := by group
        rw [this]
        exact E.inv_mem ha
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have := hmem b hBb.mem _ hx
      have e : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rwa [e] at this
    · intro hx
      have := hmem b⁻¹ (B.inv_mem hBb.mem) x hx
      rwa [inv_inv] at this
  have hcard := natCard_le_sq_inf_centralizer hEcomm hEsq hBb.sq hbE
  have h4 : 4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({b} : Set G)) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(E ⊓ Subgroup.centralizer ({b} : Set G)) ^ 2 ≤ 9 := by
      have : Nat.card ↥(E ⊓ Subgroup.centralizer ({b} : Set G)) ≤ 3 := by omega
      calc Nat.card ↥(E ⊓ Subgroup.centralizer ({b} : Set G)) ^ 2 ≤ 3 ^ 2 :=
          Nat.pow_le_pow_left this 2
        _ = 9 := by norm_num
    omega
  obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := exists_two_ne_one_of_four_le h4
  refine ⟨E, u, v, rfl, hEW, hEsq, hu.1, hv.1, hu1, hv1, huv, ?_, ?_⟩
  · have := Subgroup.mem_centralizer_singleton_iff.mp hu.2
    exact this.symm
  · have := Subgroup.mem_centralizer_singleton_iff.mp hv.2
    exact this.symm

end CFSG.ClassicalInvolution.Asc77
