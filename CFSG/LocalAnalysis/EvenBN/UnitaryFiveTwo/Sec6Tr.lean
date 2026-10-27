module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44Three

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open scoped MatrixGroups

theorem conj_mem_YK {p y : SL(4, F4)} (hp : p ∈ PK) (hy : y ∈ YK) : p * y * p⁻¹ ∈ YK := by
  have hE : (YK.map (MulAut.conj p).toMonoidHom) ≤ PK := by
    rintro _ ⟨z, hz, rfl⟩
    exact PK.mul_mem (PK.mul_mem hp (YK_le_PK hz)) (PK.inv_mem hp)
  have hc : ∀ x ∈ YK.map (MulAut.conj p).toMonoidHom, ∀ y ∈ YK.map (MulAut.conj p).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show p * a * p⁻¹ * (p * b * p⁻¹) = p * (a * b) * p⁻¹ by group,
      show p * b * p⁻¹ * (p * a * p⁻¹) = p * (b * a) * p⁻¹ by group, elemAb_YK.1 a ha b hb]
  have hs : ∀ x ∈ YK.map (MulAut.conj p).toMonoidHom, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show p * a * p⁻¹ * (p * a * p⁻¹) = p * (a * a) * p⁻¹ by group, elemAb_YK.2 a ha]
    group
  have h8 : 2 ^ 8 ≤ Nat.card (YK.map (MulAut.conj p).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj p).injective, card_YK]
  have := eq_YK_of_elemAb hE hc hs h8
  rw [← this]
  exact ⟨y, hy, rfl⟩

section Transport

variable {G : Type} [Group G]

theorem exists_chi_of_pGroup [Finite G] {K : Subgroup G} (φ : SL(4, F4) ≃* K) {A : Subgroup G}
    (hA : IsPGroup 2 A) (hAK : A ≤ K) :
    ∃ χ : SL(4, F4) →* G, Function.Injective χ ∧ (∀ g ∈ K, ∃ x, χ x = g) ∧ (∀ x, χ x ∈ K) ∧
      A ≤ PK.map χ := by
  set ψ : SL(4, F4) →* G := K.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := K.subtype_injective.comp φ.injective
  have hA₀ : IsPGroup 2 (A.comap ψ) := hA.comap_of_injective ψ hψinj
  obtain ⟨Q, hQ⟩ := hA₀.exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := exists_sylow_PK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(4, F4) Q S₀
  have hmem : ∀ x, x ∈ (Q : Subgroup SL(4, F4)) ↔ g * x * g⁻¹ ∈ PK := by
    intro x
    rw [← hS₀, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    constructor
    · intro hx
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      have h2 : g * y * g⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hyx
      have h3 : y = x := mul_left_cancel (mul_right_cancel h2)
      rwa [h3] at hy
  have hχ : ∀ y, (ψ.comp (MulAut.conj g⁻¹).toMonoidHom) (g * y * g⁻¹) = ψ y := fun y => by
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    show ψ ((MulAut.conj g⁻¹) (g * y * g⁻¹)) = ψ y
    rw [MulAut.conj_apply, e]
  refine ⟨ψ.comp (MulAut.conj g⁻¹).toMonoidHom, hψinj.comp (MulAut.conj g⁻¹).injective, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨g * φ.symm ⟨k, hk⟩ * g⁻¹, ?_⟩
    rw [hχ]
    simp [ψ]
  · intro x
    exact (φ ((MulAut.conj g⁻¹) x)).2
  · intro a ha
    have haK := hAK ha
    set y := φ.symm ⟨a, haK⟩ with hy
    have hya : ψ y = a := by simp [ψ, hy]
    have hyQ : y ∈ (Q : Subgroup SL(4, F4)) := hQ (by
      show ψ y ∈ A
      rw [hya]; exact ha)
    refine ⟨g * y * g⁻¹, (hmem y).1 hyQ, ?_⟩
    rw [hχ, hya]

theorem eq_map_YK {χ : SL(4, F4) →* G} (hχ : Function.Injective χ) {E : Subgroup G}
    (hE : E ≤ PK.map χ) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 2 ^ 8) : E = YK.map χ := by
  set E' : Subgroup SL(4, F4) := E.comap χ ⊓ PK with hE'
  have hmap : E'.map χ = E := by
    ext e
    constructor
    · rintro ⟨x, ⟨hxE, -⟩, rfl⟩
      exact hxE
    · intro he
      obtain ⟨p, hp, rfl⟩ := hE he
      exact ⟨p, ⟨he, hp⟩, rfl⟩
  have hcard' : Nat.card E' = 2 ^ 8 := by
    rw [← hcard, ← hmap, Subgroup.card_map_of_injective hχ]
  have hc' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy => hχ (by
    rw [map_mul, map_mul]; exact hc _ hx.1 _ hy.1)
  have hs' : ∀ x ∈ E', x * x = 1 := fun x hx => hχ (by
    rw [map_mul, map_one]; exact hs _ hx.1)
  have := eq_YK_of_elemAb inf_le_right hc' hs' (le_of_eq hcard'.symm)
  rw [← hmap]
  exact congrArg (Subgroup.map χ) this

theorem map_YK_conj {χ : SL(4, F4) →* G} {q y : G} (hq : q ∈ PK.map χ) (hy : y ∈ YK.map χ) :
    q * y * q⁻¹ ∈ YK.map χ := by
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨p * y' * p⁻¹, conj_mem_YK hp hy', by simp⟩

theorem map_ZK_comm {χ : SL(4, F4) →* G} {q z : G} (hq : q ∈ PK.map χ) (hz : z ∈ ZK.map χ) :
    q * z = z * q := by
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨z', hz', rfl⟩ := hz
  rw [← map_mul, ← map_mul, comm_of_mem_ZK hz' hp]

theorem map_Z₂K_comm {χ : SL(4, F4) →* G} {q z : G} (hq : q ∈ PK.map χ) (hz : z ∈ Z₂K.map χ) :
    q * z * q⁻¹ * z⁻¹ ∈ ZK.map χ := by
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨z', hz', rfl⟩ := hz
  refine ⟨p * z' * p⁻¹ * z'⁻¹, ?_, by simp⟩
  have h1 := (mem_Z₂K_iff.1 hz').2 p hp
  have h2 : p * z' * p⁻¹ * z'⁻¹ = (z' * p * z'⁻¹ * p⁻¹)⁻¹ := by group
  rw [h2]
  exact ZK.inv_mem h1

theorem isSylowOf_map_PK [Finite G] {K : Subgroup G} {χ : SL(4, F4) →* G}
    (hinj : Function.Injective χ) (hsurj : ∀ g ∈ K, ∃ x, χ x = g) (hKm : ∀ x, χ x ∈ K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (PK.map χ) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hKm x
  · exact (IsPGroup.of_card (n := 12) card_PK).map χ
  · have hK : K = (⊤ : Subgroup SL(4, F4)).map χ := by
      ext g
      constructor
      · intro hg
        obtain ⟨x, hx⟩ := hsurj g hg
        exact ⟨x, trivial, hx⟩
      · rintro ⟨x, -, rfl⟩
        exact hKm x
    rw [hK, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]
    obtain ⟨S₀, hS₀⟩ := exists_sylow_PK
    rw [← hS₀]
    exact S₀.not_dvd_index

end Transport

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
