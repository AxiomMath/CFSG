module

public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.GH74.GLS.IVK.L2.Lemma12

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter
open scoped commutatorElement

section TStruct

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] {e : K ≃* L2 F}

omit [Finite K] in
theorem fieldAut_two_elt_mem_T (N : L2Notation e) {φ : MulAut K} (hφ : φ ∈ fieldAutSub e)
    (k : ℕ) (hk : orderOf φ = 2 ^ k) : φ ∈ (N.T : Subgroup (MulAut K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers φ) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hk]
  have hle : zpowers φ ≤ normalizer (N.T : Set (MulAut K)) :=
    (Subgroup.zpowers_le).2 (N.T_inv hφ)
  have h1 := hp.inf_normalizer_sylow N.T
  have h2 : zpowers φ ⊓ normalizer (N.T : Set (MulAut K)) = zpowers φ :=
    inf_eq_left.mpr hle
  rw [h2] at h1
  have : zpowers φ ≤ (N.T : Subgroup (MulAut K)) := h1.le.trans inf_le_right
  exact this (Subgroup.mem_zpowers φ)

theorem T_decomp (N : L2Notation e) (τ : MulAut K) (hτ : τ ∈ (N.T : Subgroup (MulAut K))) :
    ∃ d ∈ N.Pt, ∃ r ∈ N.R, τ = d * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hτg⟩ := fieldAutHom_fieldProj_mul e τ
  set σ : F ≃+* F := fieldProj e τ with hσ
  set φ : MulAut K := fieldAutHom e σ with hφ
  have hφF : φ ∈ fieldAutSub e := ⟨σ, rfl⟩
  obtain ⟨k, hk⟩ := N.T.isPGroup'.exists_card_eq
  have hτo : orderOf τ ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard _ hτ
  have hσo : orderOf σ ∣ orderOf τ := orderOf_map_dvd (fieldProj e) τ
  have hφo : orderOf φ = orderOf σ := orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hφo ▸ hσo.trans hτo)
  have hφT : φ ∈ (N.T : Subgroup (MulAut K)) := fieldAut_two_elt_mem_T N hφF j hj
  refine ⟨g, ⟨?_, hg⟩, φ, ⟨hφT, hφF⟩, hτg⟩
  have : g = τ * φ⁻¹ := by rw [hτg]; simp
  rw [this]
  exact (N.T : Subgroup (MulAut K)).mul_mem hτ ((N.T : Subgroup (MulAut K)).inv_mem hφT)

omit [Finite K] in
theorem R_isCyclic (N : L2Notation e) : IsCyclic ↥N.R := by
  have h1 : IsCyclic ↥(fieldAutSub e) := isCyclic_fieldAutSub e
  have h2 : IsCyclic ↥(N.R.subgroupOf (fieldAutSub e)) := Subgroup.isCyclic _
  exact (Subgroup.subgroupOfEquivOfLe (inf_le_right : N.R ≤ fieldAutSub e)).isCyclic.mp h2

omit [Finite K] in
theorem P_eq_Pt_inf_innAut (N : L2Notation e) : N.P = N.Pt ⊓ innAut K := by
  ext x
  simp only [L2Notation.P, L2Notation.Pt, Subgroup.mem_inf]
  constructor
  · rintro ⟨hT, hI⟩
    exact ⟨⟨hT, innAut_le_innDiagSub e hI⟩, hI⟩
  · rintro ⟨⟨hT, -⟩, hI⟩
    exact ⟨hT, hI⟩

omit [Finite K] in
theorem P_le_Pt (N : L2Notation e) : N.P ≤ N.Pt := by
  rw [P_eq_Pt_inf_innAut N]; exact inf_le_left

omit [Finite K] in
theorem Pt_le_innDiagSub (N : L2Notation e) : N.Pt ≤ innDiagSub e := inf_le_right

theorem P_index_two (h : L2Field F) (N : L2Notation e) : (N.P.subgroupOf N.Pt).index = 2 := by
  have hidx := innAut_relIndex_two e h
  unfold Subgroup.relIndex at hidx
  have hmem : ∀ x : N.Pt, (x : MulAut K) ∈ N.P ↔ (x : MulAut K) ∈ innAut K := by
    intro x
    rw [P_eq_Pt_inf_innAut N]
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨N.t, ⟨N.t_mem, N.t_mem_diag⟩⟩, fun b => ?_⟩
  have hb : (b : MulAut K) ∈ innDiagSub e := Pt_le_innDiagSub N b.2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨b, hb⟩ : ↥(innDiagSub e)))
    (b := ⟨N.t, N.t_mem_diag⟩)
  simp only [Subgroup.mem_subgroupOf] at key ⊢
  have h1 : ((b * ⟨N.t, ⟨N.t_mem, N.t_mem_diag⟩⟩ : N.Pt) : MulAut K) ∈ N.P ↔
      (b : MulAut K) * N.t ∈ innAut K := by
    rw [hmem]; rfl
  rw [h1, hmem]
  have h2 := key
  simp only [Subgroup.coe_mul] at h2
  by_cases hbI : (b : MulAut K) ∈ innAut K
  · have : (b : MulAut K) * N.t ∉ innAut K := by
      intro hh
      have := h2.mp hh
      exact N.t_not_mem_inn (this.mp hbI)
    exact Or.inr ⟨hbI, this⟩
  · have : (b : MulAut K) * N.t ∈ innAut K := h2.mpr (iff_of_false hbI N.t_not_mem_inn)
    exact Or.inl ⟨this, hbI⟩

theorem card_Pt_eq (h : L2Field F) (N : L2Notation e) : Nat.card N.Pt = 2 * Nat.card N.P := by
  have h1 := Subgroup.card_mul_index (N.P.subgroupOf N.Pt)
  rw [P_index_two h N, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P_le_Pt N)).toEquiv] at h1
  omega

theorem Pt_dihedral_model (h : L2Field F) (N : L2Notation e) (n : ℕ) (hn : Nat.card N.P = 2 ^ n) :
    Nonempty (↥N.Pt ≃* DihedralGroup (2 ^ n)) := by
  obtain ⟨m, hm, ⟨d⟩⟩ := dihedral_of_sylow_inf_innDiag e h N.T
  have hc := card_Pt_eq h N
  rw [hn] at hc
  have h2 : Nat.card N.Pt = 2 * 2 ^ m := by
    have h' := Nat.card_congr d.toEquiv
    rw [DihedralGroup.nat_card] at h'
    exact h'
  have h3 : 2 ^ m = 2 ^ n := by omega
  have h4 : m = n := Nat.pow_right_injective (le_refl 2) h3
  subst h4
  exact ⟨d⟩

theorem P_dihedral_model (h : L2Field F) (N : L2Notation e) (n : ℕ) (hn : Nat.card N.P = 2 ^ n) :
    ∃ k, 2 ^ n = 2 * k ∧ 2 ≤ k ∧ Nonempty (↥N.P ≃* DihedralGroup k) := by
  obtain ⟨n', hn'⟩ := ivk_1_2c F h K e N
  obtain ⟨-, k, hk, hk2, ⟨d⟩⟩ := hn'
  refine ⟨k, ?_, hk2, ⟨d⟩⟩
  have h1 : Nat.card N.P = 2 * k := by
    rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
  omega

end TStruct

end CFSG.GH74.GLS.IVK
