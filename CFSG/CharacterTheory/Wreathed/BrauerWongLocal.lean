module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Wreathed.BrauerWong

universe u v

variable {G : Type u} [Group G]

theorem eq_of_normalizer_inf_le [Finite G] {p : ℕ} [Fact p.Prime] {B P : Subgroup G}
    (hP : IsPGroup p P) (hBP : B ≤ P)
    (hN : Subgroup.normalizer (B : Set G) ⊓ P ≤ B) : B = P := by
  apply le_antisymm hBP
  by_contra hne
  have hlt : B.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact hne
  let : Group.IsNilpotent P := hP.isNilpotent
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hBP] at hgrow
  obtain ⟨x, hxN, hxB⟩ := IsConcreteLE.exists_of_lt hgrow
  exact hxB (hN ⟨hxN, x.property⟩)

theorem mem_normalizer_of_conj_mem [Finite G] {B : Subgroup G} {y : G}
    (h : ∀ b ∈ B, y * b * y⁻¹ ∈ B) : y ∈ Subgroup.normalizer (B : Set G) := by
  let f : B → B := fun b => ⟨y * b * y⁻¹, h b b.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h' : y * a * y⁻¹ = y * b * y⁻¹ := congrArg Subtype.val hab
    simpa using h'
  have hs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    obtain ⟨b, hb⟩ := hs ⟨y * x * y⁻¹, hx⟩
    have h' : y * b * y⁻¹ = y * x * y⁻¹ := congrArg Subtype.val hb
    have hbx : (b : G) = x := by simpa using h'
    rw [← hbx]
    exact b.property

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {M : Subgroup G} (hM : IsPGroup p M) :
    ∃ k : G, ∀ m ∈ M, k⁻¹ * m * k ∈ (T : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hM.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G T Q
  refine ⟨k, fun m hm => ?_⟩
  have hmQ : m ∈ (Q : Subgroup G) := hQ hm
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmQ
  simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hmQ

theorem exists_conj_mem_sylow_in [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (T : Sylow p K) {M : Subgroup G} (hMK : M ≤ K) (hM : IsPGroup p M) :
    ∃ k ∈ K, ∀ m ∈ M, k⁻¹ * m * k ∈ (T : Subgroup K).map K.subtype := by
  have hM' : IsPGroup p (M.subgroupOf K) :=
    hM.of_equiv (Subgroup.subgroupOfEquivOfLe hMK).symm
  obtain ⟨k, hk⟩ := exists_conj_mem_sylow T hM'
  refine ⟨k, k.property, fun m hm => ?_⟩
  exact ⟨_, hk ⟨m, hMK hm⟩ hm, rfl⟩

theorem exists_mem_mul_mem_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (T : Sylow p K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ∃ c ∈ K, ∃ m ∈ Subgroup.normalizer (((T : Subgroup K).map K.subtype : Subgroup G) : Set G),
      g = c * m := by
  set B : Subgroup G := (T : Subgroup K).map K.subtype
  have hBK : B ≤ K := Subgroup.map_subtype_le _
  let M : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hMK : M ≤ K := by
    rintro _ ⟨b, hb, rfl⟩
    have := (Subgroup.mem_normalizer_iff''.mp hg b).mp (hBK hb)
    simpa [MulAut.conj_apply] using this
  have hMp : IsPGroup p M := (T.isPGroup'.map K.subtype).map _
  obtain ⟨c, hcK, hc⟩ := exists_conj_mem_sylow_in T hMK hMp
  have hy : (g * c)⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro b hb
    have h := hc (g⁻¹ * b * g) ⟨b, hb, by simp⟩
    have heq : c⁻¹ * (g⁻¹ * b * g) * c = (g * c)⁻¹ * b * (g * c)⁻¹⁻¹ := by group
    rw [heq] at h
    exact h
  refine ⟨g * c⁻¹ * g⁻¹, ?_, g * c, (Subgroup.normalizer _).inv_mem_iff.mp hy, by group⟩
  have := (Subgroup.mem_normalizer_iff.mp hg c⁻¹).mp (K.inv_mem hcK)
  exact this

end CFSG.Wreathed.BrauerWong
