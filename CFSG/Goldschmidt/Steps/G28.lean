module

public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G28

variable {G : Type*} [Group G]

@[expose] def prodConj (N : Subgroup G) (a : G) : Set G :=
  {x | ∃ m ∈ N, ∃ n ∈ N, x = (m⁻¹ * a * m) * (n⁻¹ * a * n)}

theorem le_normalizer_closure (N : Subgroup G) (a : G) :
    N ≤ Subgroup.normalizer (Subgroup.closure (prodConj N a) : Set G) := by
  have key : ∀ n ∈ N, ∀ x ∈ Subgroup.closure (prodConj N a),
      n * x * n⁻¹ ∈ Subgroup.closure (prodConj N a) := by
    intro n hn x hx
    have hle : Subgroup.closure (prodConj N a) ≤
        (Subgroup.closure (prodConj N a)).comap (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨m, hm, m', hm', rfl⟩
      apply Subgroup.subset_closure
      refine ⟨m * n⁻¹, N.mul_mem hm (N.inv_mem hn), m' * n⁻¹, N.mul_mem hm' (N.inv_mem hn), ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    exact hle hx
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (N.inv_mem hn) _ hx
  simpa [mul_assoc] using this

end G28

theorem G28 : S_G28 := by
  intro G _ _ A N A₀ hA h4 hN hirr hA₀ hidx a ha ha1
  by_contra hcon
  push Not at hcon
  have hconjA : ∀ n ∈ N, n⁻¹ * a * n ∈ A := by
    intro n hn
    have := (Subgroup.mem_normalizer_iff.mp (hN (N.inv_mem hn)) a).mp ha
    simpa using this
  set B := Subgroup.closure (G28.prodConj N a) with hB
  have hBA₀ : B ≤ A₀ := by
    rw [hB, Subgroup.closure_le]
    rintro _ ⟨m, hm, m', hm', rfl⟩
    have h1 := hconjA m hm
    have h2 := hconjA m' hm'
    have key := (Subgroup.mul_mem_iff_of_index_two (H := A₀.subgroupOf A) hidx
      (a := ⟨m⁻¹ * a * m, h1⟩) (b := ⟨m'⁻¹ * a * m', h2⟩)).mpr (by
        simp only [Subgroup.mem_subgroupOf]
        exact iff_of_false (hcon m hm) (hcon m' hm'))
    simpa [Subgroup.mem_subgroupOf] using key
  rcases hirr B (hBA₀.trans hA₀) (G28.le_normalizer_closure N a) with hbot | htop
  ·
    have hfix : ∀ n ∈ N, n⁻¹ * a * n = a := by
      intro n hn
      have hmem : (n⁻¹ * a * n) * (1⁻¹ * a * 1) ∈ B :=
        Subgroup.subset_closure ⟨n, hn, 1, N.one_mem, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have ha2 : a * a = 1 := by rw [← pow_two]; exact hA.2 a ha
      have : n⁻¹ * a * n = a⁻¹ := by
        simpa using eq_inv_of_mul_eq_one_left hmem
      rw [this, inv_eq_of_mul_eq_one_left ha2]
    have hnormV : N ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      intro n hn
      have hcomm : ∀ k : ℤ, n * a ^ k * n⁻¹ = a ^ k := by
        intro k
        have h1 : n * a * n⁻¹ = a := by
          have := hfix n⁻¹ (N.inv_mem hn)
          simpa using this
        rw [← conj_zpow, h1]
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, (hcomm k).symm⟩
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hk' : x = n⁻¹ * a ^ k * n := by
          rw [show a ^ k = n * x * n⁻¹ from hk]
          group
        rw [hk']
        have := hcomm k
        calc a ^ k = n⁻¹ * (n * a ^ k * n⁻¹) * n := by group
          _ = n⁻¹ * a ^ k * n := by rw [this]
    have hVA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr ha
    rcases hirr _ hVA hnormV with hV | hV
    · exact ha1 (Subgroup.zpowers_eq_bot.mp hV)
    · have hcard : Nat.card A = orderOf a := by
        rw [← hV, Nat.card_zpowers]
      have hord : orderOf a ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (hA.2 a ha)
      omega
  ·
    have hle : A ≤ A₀ := htop ▸ hBA₀
    have h1 : A₀.subgroupOf A = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      exact hle hx
    rw [h1, Subgroup.index_top] at hidx
    omega

end CFSG.Goldschmidt
