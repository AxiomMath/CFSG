module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Bg.Iii2.FusionKleinProof

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def kleinSub (x y : G) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Subgroup G where
  carrier := {g | g = 1 ∨ g = x ∨ g = y ∨ g = x * y}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have hx' : ∀ z : G, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
    have hyx : y * x = x * y := hxy.symm
    have hyx' : ∀ z : G, y * (x * z) = x * (y * z) := fun z => by
      rw [← mul_assoc, hyx, mul_assoc]
    rintro a b (ha | ha | ha | ha) (hb | hb | hb | hb) <;> rw [ha, hb] <;>
      simp [mul_assoc, hx, hy, hyx, hx', hyx']
  inv_mem' := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    rintro a (ha | ha | ha | ha) <;> rw [ha] <;> simp [hxi, hyi, hxy]

theorem mem_kleinSub {x y : G} {hx : x * x = 1} {hy : y * y = 1} {hxy : x * y = y * x} {a : G} :
    a ∈ kleinSub x y hx hy hxy ↔ a = 1 ∨ a = x ∨ a = y ∨ a = x * y := Iff.rfl

theorem kleinSub_isPGroup {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    IsPGroup 2 (kleinSub x y hx hy hxy) := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : (a : G) * a = 1 := by
    rcases mem_kleinSub.1 a.2 with h | h | h | h <;> rw [h]
    · simp
    · exact hx
    · exact hy
    · rw [mul_assoc, ← mul_assoc y, ← hxy, mul_assoc x y, hy, mul_one, hx]
  simpa [pow_two] using h2

theorem kleinSub_mul_comm {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    {e : G} (he : e ∈ kleinSub x y hx hy hxy) : e * y = y * e := by
  rcases mem_kleinSub.1 he with h | h | h | h
  · rw [h, one_mul, mul_one]
  · rw [h]; exact hxy
  · rw [h]
  · rw [h, mul_assoc, hy, mul_one, ← mul_assoc, ← hxy, mul_assoc, hy, mul_one]

theorem mem_normalizer_of_forall_conj_mem [Finite G] (E : Subgroup G) (n : G)
    (h : ∀ e ∈ E, n * e * n⁻¹ ∈ E) : n ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨h e, fun he => ?_⟩
  let f : E → E := fun a => ⟨n * a * n⁻¹, h a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : n * (a : G) * n⁻¹ = n * (b : G) * n⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.mp hf ⟨n * e * n⁻¹, he⟩
  have h1 : n * (a : G) * n⁻¹ = n * e * n⁻¹ := congrArg Subtype.val ha
  have h2 : (a : G) = e := by simpa using h1
  exact h2 ▸ a.2

theorem mem_normalizer_kleinSub [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (n : G) (h1 : n * x * n⁻¹ ∈ kleinSub x y hx hy hxy)
    (h2 : n * y * n⁻¹ ∈ kleinSub x y hx hy hxy) :
    n ∈ Subgroup.normalizer (kleinSub x y hx hy hxy : Set G) := by
  apply mem_normalizer_of_forall_conj_mem
  intro e he
  rcases mem_kleinSub.1 he with h | h | h | h <;> rw [h]
  · simp only [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact h1
  · exact h2
  · have : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ h1 h2

theorem exists_conj_mem_of_isSylowOf [Finite G] {T K P : Subgroup G} (hT : IsSylowOf 2 T K)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) : ∃ c ∈ K, ∀ p ∈ P, c * p * c⁻¹ ∈ T := by
  obtain ⟨S, hS⟩ := hT
  have hP' : IsPGroup 2 (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q S
  refine ⟨g, g.2, fun p hp => ?_⟩
  have hpQ : (⟨p, hPK hp⟩ : K) ∈ (Q : Subgroup K) := hQ hp
  have hmem : MulAut.conj g (⟨p, hPK hp⟩ : K) ∈ ((g • Q : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hpQ
  rw [hg] at hmem
  rw [← hS]
  exact ⟨_, hmem, rfl⟩

theorem false_of_orbit_pair [Finite G] {N T : Subgroup G} (hT : IsSylowOf 2 T N) {x y : G}
    (hTx : ∀ t ∈ T, t * x * t⁻¹ = x) (hne : x ≠ y)
    (hN : ∀ n ∈ N, n * x * n⁻¹ = x ∨ n * x * n⁻¹ = y)
    {n₁ : G} (hn₁ : n₁ ∈ N) (hn₁x : n₁ * x * n₁⁻¹ = y) : False := by
  have hTC : T ≤ Subgroup.centralizer {x} ⊓ N := by
    intro t ht
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hT.le ht⟩
    have := hTx t ht
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have h2 : (Subgroup.centralizer {x}).relIndex N = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨n₁, hn₁⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_centralizer_singleton_iff]
    have hb : (b : G) ∈ N := b.2
    generalize (b : G) = β at hb ⊢
    have hN' : ∀ n ∈ N, n * x = x * n ∨ n * x = y * n := by
      intro n hn
      rcases hN n hn with h | h
      · exact Or.inl (mul_inv_eq_iff_eq_mul.1 h)
      · exact Or.inr (mul_inv_eq_iff_eq_mul.1 h)
    have e1 : n₁ * x = y * n₁ := mul_inv_eq_iff_eq_mul.1 hn₁x
    have hA : (β * n₁ * x = x * (β * n₁)) ↔ β * y = x * β := by
      rw [mul_assoc, e1, ← mul_assoc, ← mul_assoc, mul_left_inj]
    rw [hA]
    rcases hN' β hb with h | h
    · exact Or.inr ⟨h, fun h2 => hne (mul_left_cancel (h.trans h2.symm))⟩
    · have hnot : ¬ (β * x = x * β) := fun h1 => hne (mul_right_cancel (h.symm.trans h1)).symm
      refine Or.inl ⟨?_, hnot⟩
      rcases hN' β⁻¹ (N.inv_mem hb) with h' | h'
      · exfalso
        apply hnot
        have : x * β = β * x := by
          calc x * β = β * (β⁻¹ * x) * β := by group
            _ = β * (x * β⁻¹) * β := by rw [h']
            _ = β * x := by group
        exact this.symm
      · calc β * y = β * (y * β⁻¹) * β := by group
          _ = β * (β⁻¹ * x) * β := by rw [h']
          _ = x * β := by group
  have h3 := Subgroup.relIndex_mul_relIndex T (Subgroup.centralizer {x} ⊓ N) N hTC inf_le_right
  rw [Subgroup.inf_relIndex_right, h2] at h3
  exact (isSylowOf_iff.1 hT).2.2 ⟨_, by rw [← h3, mul_comm]⟩

end CFSG.GH74.GLS.Bg.Iii2.FusionKleinProof
