module

public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GH74.Uniqueness.Bender.Sylow2Basic

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG.BenderSuzuki

section Psl2

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.sq_eq_one_of_two_pow_linear
    {J : Type*} [Group J] [Finite J] {n : ℕ}
    (hJ : BenderType J n 1 1) {x : J} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x * x = 1 := by
  obtain ⟨S, -⟩ : ∃ S : Sylow 2 J, True := ⟨default, trivial⟩
  obtain ⟨t, hc⟩ := hJ.exists_benderCore S
  have hSZ : rootCenter (S : Subgroup J) = (S : Subgroup J) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (le_of_eq (by rw [hc.card_center, hc.card_eq, pow_one]))
  exact sq_eq_one_of_two_pow_of_sylow S
    (fun x hx => hc.center_sq x (by rw [hSZ]; exact hx)) hx

theorem BenderType.exists_psl2_pair_of_mem
    {n e : ℕ} (h : BenderType K n 3 e) {J : Subgroup K}
    (φ : J ≃* PSL2Model n) {z : K} (hzJ : z ∈ J) (hz : z * z = 1) :
    ∃ (Q : Sylow 2 K) (t : K), z ∈ rootCenter (Q : Subgroup K) ∧ t * t = 1 ∧ t ∈ J ∧
      t ∉ borel (Q : Subgroup K) ∧ rootCenter (Q : Subgroup K) ≤ J ∧
      rootCenter (Q : Subgroup K) ⊔ zpowers t = J := by
  classical
  have hn2 : 2 ≤ n := h.two_le.2
  have hJ : BenderType J n 1 1 := BenderType.linear n hn2 φ
  have : IsSimpleGroup J := hJ.isSimple
  obtain ⟨S, hzS⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one (G := J) (z := ⟨z, hzJ⟩)
    (Subtype.ext hz)).exists_le_sylow
  obtain ⟨t₂, hc₂⟩ := hJ.exists_benderCore S
  have hSZ : rootCenter (S : Subgroup J) = (S : Subgroup J) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (le_of_eq (by rw [hc₂.card_center, hc₂.card_eq, pow_one]))
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup K, Z = (S : Subgroup J).map J.subtype := ⟨_, rfl⟩
  have hmemZ : ∀ x : J, (x : K) ∈ Z ↔ x ∈ (S : Subgroup J) := by
    intro x
    rw [hZdef]
    constructor
    · rintro ⟨s, hs, hsx⟩
      have : s = x := Subtype.ext hsx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hZsq : ∀ x ∈ Z, x * x = 1 := by
    intro x hx
    rw [hZdef] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have := hc₂.center_sq s (by rw [hSZ]; exact hs)
    exact congrArg Subtype.val this
  have hZcard : Nat.card Z = 2 ^ n := by
    rw [hZdef, Subgroup.card_map_of_injective J.subtype_injective, hc₂.card_eq, pow_one]
  obtain ⟨Q, hZQ⟩ := (isPGroup_two_of_mul_self_eq_one hZsq).exists_le_sylow
  obtain ⟨t₀, hc₀⟩ := h.exists_benderCore Q
  have hZle : Z ≤ rootCenter (Q : Subgroup K) := hc₀.elemAbelian_le_rootCenter hZQ hZsq
  have hZeq : Z = rootCenter (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hZcard, hc₀.card_center])
  have ht₂sq : (t₂ : K) * t₂ = 1 := congrArg Subtype.val hc₂.sq_eq_one
  have ht₂Q : (t₂ : K) ∉ borel (Q : Subgroup K) := by
    intro hmem
    apply hc₂.not_mem
    rw [mem_borel_iff]
    intro x
    have h1 := mem_rootCenter_conj_iff hmem (x : K)
    rw [← hZeq] at h1
    exact (hmemZ x).symm.trans (h1.trans (hmemZ (t₂ * x * t₂⁻¹)))
  have hsup := hc₂.sup_zpowers_eq_top hc₂.not_mem
  have hJeq : Z ⊔ zpowers (t₂ : K) = J := by
    have h1 := congrArg (Subgroup.map J.subtype) hsup
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      ← hZdef] at h1
    exact h1
  have hzZ : z ∈ rootCenter (Q : Subgroup K) :=
    hZeq ▸ (hmemZ ⟨z, hzJ⟩).mpr (hzS (Subgroup.mem_zpowers _))
  refine ⟨Q, t₂, hzZ, ht₂sq, t₂.2, ht₂Q, ?_, ?_⟩
  · rw [← hZeq, hZdef]
    exact Subgroup.map_subtype_le _
  · rw [← hZeq]
    exact hJeq

theorem BenderType.exists_psl2_pair
    {n e : ℕ} (h : BenderType K n 3 e) {J : Subgroup K}
    (φ : J ≃* PSL2Model n) :
    ∃ (Q : Sylow 2 K) (t : K), t * t = 1 ∧ t ∈ J ∧ t ∉ borel (Q : Subgroup K) ∧
      rootCenter (Q : Subgroup K) ≤ J ∧ rootCenter (Q : Subgroup K) ⊔ zpowers t = J := by
  obtain ⟨Q, t, -, h1, h2, h3, h4, h5⟩ := h.exists_psl2_pair_of_mem φ J.one_mem (mul_one 1)
  exact ⟨Q, t, h1, h2, h3, h4, h5⟩

theorem BenderType.psl2_subgroups_conjugate
    {n e : ℕ} (h : BenderType K n 3 e) {J₁ J₂ : Subgroup K}
    (φ₁ : J₁ ≃* PSL2Model n) (φ₂ : J₂ ≃* PSL2Model n) :
    ∃ g : K, J₂ = J₁.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Q₁, t₁, ht₁, -, ht₁Q, -, hJ₁⟩ := h.exists_psl2_pair φ₁
  obtain ⟨Q₂, t₂, ht₂, -, ht₂Q, -, hJ₂⟩ := h.exists_psl2_pair φ₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q₁ Q₂
  have hU : (Q₁ : Subgroup K).map (MulAut.conj g).toMonoidHom = (Q₂ : Subgroup K) := by
    rw [← hg]
    ext x
    rw [Subgroup.mem_map_equiv, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hZ : (rootCenter (Q₁ : Subgroup K)).map (MulAut.conj g).toMonoidHom =
      rootCenter (Q₂ : Subgroup K) := by
    rw [← hU, rootCenter_map]
  have ht'sq : (g * t₁ * g⁻¹) * (g * t₁ * g⁻¹) = 1 := by
    calc (g * t₁ * g⁻¹) * (g * t₁ * g⁻¹) = g * (t₁ * t₁) * g⁻¹ := by group
      _ = 1 := by rw [ht₁]; group
  have ht'Q : g * t₁ * g⁻¹ ∉ borel (Q₂ : Subgroup K) := by
    intro hmem
    apply ht₁Q
    rw [← hU, borel_map, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    have e1 : g⁻¹ * (g * t₁ * g⁻¹) * g = t₁ := by group
    rwa [e1] at hmem
  have hc : BenderCore (2 ^ n) 3 e (Q₂ : Subgroup K) t₂ := h.benderCore Q₂ ht₂ ht₂Q
  obtain ⟨m, hm, hmt⟩ := hc.exists_conj_eq ht'sq ht'Q
  have ht₂eq : m * (g * t₁ * g⁻¹) * m⁻¹ = t₂ := by
    rw [hmt]
    group
  have hZm : (rootCenter (Q₂ : Subgroup K)).map (MulAut.conj m).toMonoidHom =
      rootCenter (Q₂ : Subgroup K) := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h1 := (mem_rootCenter_conj_iff ((borel (Q₂ : Subgroup K)).inv_mem hm) x).symm
    rw [inv_inv] at h1
    exact h1
  have hcomp : (MulAut.conj (m * g)).toMonoidHom =
      (MulAut.conj m).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply]
    group
  refine ⟨m * g, ?_⟩
  rw [← hJ₂, ← hJ₁, hcomp, ← Subgroup.map_map, Subgroup.map_sup, Subgroup.map_sup, hZ, hZm,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht₂eq]

end Psl2

end CFSG.GH74.Uniqueness.Bender
