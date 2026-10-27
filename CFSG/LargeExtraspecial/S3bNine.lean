module

public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.LargeExtraspecial.S3Asch

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions

theorem conj_commutator_eq_of_conj {G : Type*} [Group G] {z c d k : G} (hzc : z * c = c * z)
    (hzd : z * d = d * z) (hc : k * c * k⁻¹ = c ∨ k * c * k⁻¹ = c * z)
    (hd : k * d * k⁻¹ = d ∨ k * d * k⁻¹ = d * z) :
    k * (c * d * c⁻¹ * d⁻¹) * k⁻¹ = c * d * c⁻¹ * d⁻¹ := by
  have hzc' : z * c⁻¹ = c⁻¹ * z := by
    calc z * c⁻¹ = c⁻¹ * (c * z) * c⁻¹ := by group
      _ = c⁻¹ * (z * c) * c⁻¹ := by rw [hzc]
      _ = c⁻¹ * z := by group
  have e : k * (c * d * c⁻¹ * d⁻¹) * k⁻¹ =
      (k * c * k⁻¹) * (k * d * k⁻¹) * (k * c * k⁻¹)⁻¹ * (k * d * k⁻¹)⁻¹ := by group
  rw [e]
  rcases hc with h1 | h1 <;> rcases hd with h2 | h2 <;> rw [h1, h2]
  · calc c * (d * z) * c⁻¹ * (d * z)⁻¹ = c * d * (z * c⁻¹) * z⁻¹ * d⁻¹ := by group
      _ = c * d * (c⁻¹ * z) * z⁻¹ * d⁻¹ := by rw [hzc']
      _ = c * d * c⁻¹ * d⁻¹ := by group
  · calc c * z * d * (c * z)⁻¹ * d⁻¹ = c * (z * d) * z⁻¹ * c⁻¹ * d⁻¹ := by group
      _ = c * (d * z) * z⁻¹ * c⁻¹ * d⁻¹ := by rw [hzd]
      _ = c * d * c⁻¹ * d⁻¹ := by group
  · calc c * z * (d * z) * (c * z)⁻¹ * (d * z)⁻¹ = c * (z * d) * c⁻¹ * z⁻¹ * d⁻¹ := by group
      _ = c * (d * z) * c⁻¹ * z⁻¹ * d⁻¹ := by rw [hzd]
      _ = c * d * (z * c⁻¹) * z⁻¹ * d⁻¹ := by group
      _ = c * d * (c⁻¹ * z) * z⁻¹ * d⁻¹ := by rw [hzc']
      _ = c * d * c⁻¹ * d⁻¹ := by group

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] [Finite G] {c w a : G}
    (hc2 : c ^ 2 = a) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) (hw : w ∈ zpowers c) (hw2 : w ^ 2 = 1) :
    w = 1 ∨ w = a := by
  classical
  have hc4 : c ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hc2, ha2]
  have hord : orderOf c = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow (n := 1) (p := 2) ?_ ?_
    · rw [pow_one, hc2]
      exact ha1
    · exact hc4
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hw
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  have hk4 : k < 4 := Finset.mem_range.mp hk
  interval_cases k
  · left
    exact pow_zero c
  · exfalso
    apply ha1
    rw [← hc2]
    simpa using hw2
  · right
    exact hc2
  · exfalso
    apply ha1
    rw [← hc2]
    have e : (c ^ 3) ^ 2 = c ^ 4 * c ^ 2 := by rw [← pow_mul, ← pow_add]
    rw [e, hc4, one_mul] at hw2
    exact hw2

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem conj_eq_or_of_conj_eq_or {x y : G} (hxM : x ∈ S.M) (hyM : y ∈ S.M)
    (h : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * S.z) : x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y * S.z := by
  rcases h with h | h
  · left
    have hyx : y * x = x * y := by
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [h]
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hyx]
      _ = y := by group
  · right
    have e1 : y * x * y⁻¹ * x⁻¹ = S.z := by
      rw [h, S.z_comm hxM, mul_inv_cancel_right]
    have e2 : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e1, S.z_inv] at e2
    calc x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by group
      _ = S.z * y := by rw [e2]
      _ = y * S.z := (S.z_comm hyM).symm

theorem exists_commutator_eq_conj_z (h2 : 2 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ y₁ ∈ S.L0 g, ∃ y₂ ∈ S.L0 g, y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = g * S.z * g⁻¹ := by
  obtain ⟨Q₀, hQ₀, -, -, -, hcard, hZ, -⟩ := S.exists_L0_eq haQ hne
  set T := S.conjBy g
  have ha2 : orderOf (g * S.z * g⁻¹) = 2 := T.orderOf_z
  obtain ⟨y₁, hy₁, hy₁a⟩ : ∃ y₁ ∈ Q₀, y₁ ∉ zpowers (g * S.z * g⁻¹) := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (H := Q₀) (K := zpowers (g * S.z * g⁻¹)) h
    rw [hcard, Nat.card_zpowers, ha2] at hle
    have : 2 ^ 3 ≤ 2 ^ (1 + 2 * (S.width - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hy₁c : y₁ ∉ centralizer (Q₀ : Set G) := fun h => hy₁a (hZ ▸ ⟨hy₁, h⟩)
  rw [mem_centralizer_iff] at hy₁c
  push Not at hy₁c
  obtain ⟨y₂, hy₂, hne₂⟩ := hy₁c
  refine ⟨y₁, hQ₀ hy₁, y₂, hQ₀ hy₂, ?_⟩
  rcases T.commutator_eq_one_or_z (hQ₀ hy₁).1 (hQ₀ hy₂).1 with h | h
  · exfalso
    apply hne₂
    calc y₂ * y₁ = (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)⁻¹ * y₁ * y₂ := by group
      _ = y₁ * y₂ := by rw [h]; group
  · exact h

theorem commute_conj_z_of_cl_mem_fixLbar (h2 : 2 ≤ S.width) {g x : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hx : x ∈ S.QG)
    (hfix : S.cl x ∈ S.fixLbar g) : x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hc⟩ := S.exists_commutator_eq_conj_z h2 haQ hne
  have hfix' := (S.cl_mem_fixLbar_iff hx).mp hfix
  have hconj : ∀ y ∈ S.L0 g, x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y * S.z := fun y hy =>
    S.conj_eq_or_of_conj_eq_or (S.QG_le_M hx) (S.L0_le_M g hy) (hfix' y hy)
  have h := conj_commutator_eq_of_conj (S.z_comm (S.L0_le_M g hy₁)).symm
    (S.z_comm (S.L0_le_M g hy₂)).symm (hconj y₁ hy₁) (hconj y₂ hy₂)
  rw [hc] at h
  calc x * (g * S.z * g⁻¹) = x * (g * S.z * g⁻¹) * x⁻¹ * x := by group
    _ = g * S.z * g⁻¹ * x := by rw [h]

theorem exists_typeA_of_involution {g x : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hxQ : x ∈ S.QG) (hx2 : x ^ 2 = 1)
    (hxa : x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x) (hxQa : x ∉ S.Qa g)
    (hfix : ∀ y ∈ S.L0 g, y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * S.z) :
    ∃ α : S.M, (α : G) ∈ S.L0 g ∧ (α : G) ∉ S.QG ∧ S.IsTypeAOn α 2 := by
  set T := S.conjBy g with hT
  have hTz : T.z = g * S.z * g⁻¹ := rfl
  have hxTM : x ∈ T.M := T.mem_M_iff.mpr (by rw [hTz]; exact hxa)
  have hL0 : (S.L0 g).relIndex T.QG = 2 := S.relIndex_L0 haQ hne
  by_cases hall : ∀ y ∈ S.L0 g, y * x * y⁻¹ = x
  · exfalso
    refine hxQa (T.mem_QG_of_sq_eq_one_of_commute (S.L0_le_Qa g) hL0 hx2 fun f hf => ?_)
    have h := hall f hf
    calc x * f = f * x * f⁻¹ * f := by rw [h]
      _ = f * x := by group
  push Not at hall
  obtain ⟨y₀, hy₀, hy₀x⟩ := hall
  have hy₀x' : y₀ * x * y₀⁻¹ = x * S.z := (hfix y₀ hy₀).resolve_left hy₀x
  set Y := S.L0 g ⊓ centralizer ({x} : Set G) with hY
  have hmemY : ∀ y ∈ S.L0 g, y ∈ Y ↔ y * x * y⁻¹ = x := fun y hy => by
    rw [hY, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [h]
      group
    · intro h
      refine ⟨hy, ?_⟩
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [h]
  have hYi : Y.relIndex (S.L0 g) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨y₀, hy₀, fun b hb => ?_⟩
    have hby : b * y₀ ∈ S.L0 g := mul_mem hb hy₀
    rw [hmemY _ hby, hmemY _ hb]
    have e : b * y₀ * x * (b * y₀)⁻¹ = b * (y₀ * x * y₀⁻¹) * b⁻¹ := by group
    rw [e, hy₀x']
    have hzb : b * (x * S.z) * b⁻¹ = b * x * b⁻¹ * S.z := by
      rw [show b * (x * S.z) * b⁻¹ = b * x * (S.z * b⁻¹) by group, ← S.z_comm (S.M.inv_mem
        (S.L0_le_M g hb))]
      group
    rw [hzb]
    have hxz : x * S.z ≠ x := fun h' => S.z_ne_one (by simpa using h')
    rcases hfix b hb with h | h
    · rw [h]
      exact Or.inr ⟨rfl, hxz⟩
    · rw [h, mul_assoc, S.z_mul_z, mul_one]
      exact Or.inl ⟨rfl, hxz⟩
  have hY4 : Y.relIndex T.QG ≤ 4 := by
    rw [← relIndex_mul_relIndex Y (S.L0 g) T.QG inf_le_left (S.L0_le_Qa g), hYi, hL0]
  have hYQ : Y ≤ T.QG := fun y hy => S.L0_le_Qa g hy.1
  have hxY : ∀ y ∈ Y, x * y = y * x := fun y hy => (mem_centralizer_singleton_iff.mp hy.2).symm
  rcases T.aschbacher_4_5 hxTM hx2 hxQa hYQ hY4 hxY with hA | hB
  · obtain ⟨u, -, huz, hua⟩ := S.exists_swap rfl haQ hne
    have hk : u * T.z * u⁻¹ = S.z := hua
    have hk' : u * S.z * u⁻¹ = T.z := huz
    have hA' := isTypeAOn_transport T S hk hA
    refine ⟨_, ⟨?_, ?_⟩, ?_, hA'⟩
    · exact conj_mem_QG_of_conj_eq S T hk' hxQ
    · exact conj_mem_M_of_conj_eq T S hk hxTM
    · intro hmem
      apply hxQa
      have := conj_mem_QG_of_conj_eq S T (inv_conj_eq_of_conj_eq T S hk) hmem
      exact (by simpa [mul_assoc] using this : x ∈ T.QG)
  · exfalso
    have hdim : finrank (ZMod 2) (T.commQt x) = 1 := by
      rw [T.commQt_of_mem hxTM]
      exact hB.2.2.1
    obtain ⟨-, c, -, hc2, heq⟩ := T.aschbacher_8_6 hxTM hdim
    have hz : x * y₀ * x⁻¹ * y₀⁻¹ = S.z := by
      have e1 : y₀ * x * y₀⁻¹ * x⁻¹ = S.z := by
        rw [hy₀x', S.z_comm (S.QG_le_M hxQ), mul_inv_cancel_right]
      have e2 : x * y₀ * x⁻¹ * y₀⁻¹ = (y₀ * x * y₀⁻¹ * x⁻¹)⁻¹ := by group
      rw [e2, e1, S.z_inv]
    have hmem : S.z ∈ zpowers c := by
      rw [← heq, ← hz]
      have := commutator_mem_commutator (mem_zpowers x) (S.L0_le_Qa g hy₀)
      rwa [commutatorElement_def] at this
    rcases eq_one_or_eq_of_mem_zpowers hc2 T.z_ne_one T.z_sq hmem S.z_sq with h | h
    · exact S.z_ne_one h
    · exact hne (hTz.symm.trans h.symm)

theorem lemma_3_9 (h2 : 2 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    (∀ v ∈ S.fixLbar g, S.q v = 0 → v = 0 ∨ v = S.cl (g * S.z * g⁻¹)) ∨ S.HasTypeAInL g := by
  by_cases h : ∀ v ∈ S.fixLbar g, S.q v = 0 → v = 0 ∨ v = S.cl (g * S.z * g⁻¹)
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨v, hv, hqv, hv0, hva⟩ := h
  obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
  have hx2 : x ^ 2 = 1 := (S.q_cl_eq_zero_iff hxQ).mp hqv
  have hxQa : x ∉ S.Qa g := by
    intro hxa
    have hfix : ∀ y ∈ S.L0 g, S.cl (y * x * y⁻¹) = S.cl x := fun y hy => by
      rcases (S.cl_mem_fixLbar_iff hxQ).mp hv y hy with h | h
      · rw [h]
      · rw [h, S.cl_mul_z hxQ]
    rcases S.mem_of_cl_fixed_by_L0 haQ hne ⟨hxQ, hxa⟩ hfix with h | h | h | h
    · exact hv0 (by rw [h, S.cl_one])
    · exact hva (by rw [h])
    · exact hv0 (by rw [h, S.cl_z])
    · exact hva (by rw [h, S.cl_mul S.z_mem_QG haQ, S.cl_z, zero_add])
  obtain ⟨α, hα, hαQ, hαA⟩ := S.exists_typeA_of_involution haQ hne hxQ hx2
    (S.commute_conj_z_of_cl_mem_fixLbar h2 haQ hne hxQ hv) hxQa
    ((S.cl_mem_fixLbar_iff hxQ).mp hv)
  exact S.hasTypeAInL_of_mem_L0 hα hαQ hαA

theorem fixes_of_mem_normalizer_Lbar (h2 : 2 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {s : S.O}
    (hs : s ∈ normalizer (S.Lbar g : Set S.O)) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have huniq := (S.lemma_3_9 h2 haQ hne).resolve_right hno
  have hmem : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ S.fixLbar g := by
    refine S.mem_fixLbar.mpr fun t ht => ?_
    have ht' : s⁻¹ * t * s ∈ S.Lbar g := by
      have := (mem_normalizer_iff.mp (inv_mem hs) t).mp ht
      simpa using this
    have h1 := S.mem_fixLbar.mp (S.cl_mem_fixLbar_self haQ) (s⁻¹ * t * s) ht'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply] at h1
    calc (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
        (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))))) :=
        (OrthoF2.apply_inv_apply _ _).symm
      _ = (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by rw [h1]
  have hq : S.q ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup s.2]
    exact S.q_cl_conj_z haQ
  rcases huniq _ hmem hq with h | h
  · exact absurd ((LinearEquiv.map_eq_zero_iff _).mp h) (S.cl_conj_z_ne_zero haQ hne)
  · exact h

end Setting

end CFSG.LargeExtraspecial
