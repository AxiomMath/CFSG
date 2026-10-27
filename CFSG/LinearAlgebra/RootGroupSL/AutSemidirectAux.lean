module

public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.LinearAlgebra.RootGroupSL.AutSemidirect

variable {S G : Type} [Group S] [Group G] [Finite S]

section Helpers

variable (A K : Subgroup S)

lemma mem_sup_decomp
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {x : S} :
    x ∈ A ⊔ K ↔ ∃ a ∈ A, ∃ k ∈ K, a * k = x := by
  have hle : K ≤ Subgroup.normalizer (A : Set S) := Subgroup.le_normalizer_iff.mpr hKA
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A K hle]
  exact Set.mem_mul

lemma mul_eq_imp (hAK : A ⊓ K = ⊥) {a a' k k' : S} (ha : a ∈ A) (ha' : a' ∈ A)
    (hk : k ∈ K) (hk' : k' ∈ K) (h : a * k = a' * k') : a = a' ∧ k = k' := by
  have h1 : k * k'⁻¹ = a⁻¹ * a' := by
    calc k * k'⁻¹ = a⁻¹ * (a * k) * k'⁻¹ := by group
      _ = a⁻¹ * (a' * k') * k'⁻¹ := by rw [h]
      _ = a⁻¹ * a' := by group
  have hmemA : k * k'⁻¹ ∈ A := by rw [h1]; exact A.mul_mem (A.inv_mem ha) ha'
  have hmemK : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
  have hkk : k * k'⁻¹ = 1 := by
    have : k * k'⁻¹ ∈ A ⊓ K := ⟨hmemA, hmemK⟩
    rw [hAK] at this
    simpa using this
  have hk_eq : k = k' := mul_inv_eq_one.mp hkk
  have ha_eq : a = a' := by
    rw [hk_eq] at h
    exact mul_right_cancel h
  exact ⟨ha_eq, hk_eq⟩

lemma exists_k_of_mem_sup
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {x : S} (hx : x ∈ A ⊔ K) :
    ∃ k ∈ K, ∃ a ∈ A, a * k = x := by
  obtain ⟨a, ha, k, hk, h⟩ := (mem_sup_decomp A K hKA).mp hx
  exact ⟨k, hk, a, ha, h⟩

@[expose] noncomputable def projK
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (p : ↥(A ⊔ K)) : ↥K :=
  ⟨Classical.choose (exists_k_of_mem_sup A K hKA p.2),
   (Classical.choose_spec (exists_k_of_mem_sup A K hKA p.2)).1⟩

lemma projK_spec
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (p : ↥(A ⊔ K)) :
    ∃ a ∈ A, a * ((projK A K hKA p : ↥K) : S) = (p : S) :=
  (Classical.choose_spec (exists_k_of_mem_sup A K hKA p.2)).2

lemma projK_unique (hAK : A ⊓ K = ⊥)
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (p : ↥(A ⊔ K))
    {k : S} (hk : k ∈ K) (h : ∃ a ∈ A, a * k = (p : S)) :
    k = (projK A K hKA p : S) := by
  obtain ⟨a, ha, haeq⟩ := h
  obtain ⟨a', ha', haeq'⟩ := projK_spec A K hKA p
  exact (mul_eq_imp A K hAK ha ha' hk (projK A K hKA p).2 (haeq.trans haeq'.symm)).2

lemma projK_mul (hAK : A ⊓ K = ⊥)
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (p q : ↥(A ⊔ K)) :
    projK A K hKA (p * q) = projK A K hKA p * projK A K hKA q := by
  apply Subtype.ext
  obtain ⟨a, ha, haeq⟩ := projK_spec A K hKA p
  obtain ⟨a', ha', haeq'⟩ := projK_spec A K hKA q
  have hmem : ∃ b ∈ A,
      b * ((projK A K hKA p : S) * (projK A K hKA q : S)) =
        ((p * q : ↥(A ⊔ K)) : S) := by
    refine ⟨a * ((projK A K hKA p : S) * a' * (projK A K hKA p : S)⁻¹), ?_, ?_⟩
    · exact A.mul_mem ha (hKA _ (projK A K hKA p).2 a' ha')
    · have hpq : ((p * q : ↥(A ⊔ K)) : S) = (p : S) * (q : S) := rfl
      rw [hpq, ← haeq, ← haeq']
      group
  exact (projK_unique A K hAK hKA (p * q)
    (K.mul_mem (projK A K hKA p).2 (projK A K hKA q).2) hmem).symm

@[expose] noncomputable def projKHom (hAK : A ⊓ K = ⊥)
    (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) : ↥(A ⊔ K) →* ↥K :=
  MonoidHom.mk' (projK A K hKA) (projK_mul A K hAK hKA)

lemma conj_mem_sup (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {ε : S →* G} {s : G}
    (hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹)
    (hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹)
    {p : S} (hp : p ∈ A ⊔ K) : ∃ q ∈ A ⊔ K, ε q = s * ε p * s⁻¹ := by
  obtain ⟨a, ha, k, hk, rfl⟩ := (mem_sup_decomp A K hKA).mp hp
  obtain ⟨a', ha', haeq⟩ := hsA a ha
  obtain ⟨k', hk', hkeq⟩ := hsK k hk
  refine ⟨a' * k', Subgroup.mul_mem_sup ha' hk', ?_⟩
  rw [map_mul ε a' k', haeq, hkeq, map_mul ε a k]
  group

@[expose] noncomputable def conjFun (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {ε : S →* G} (s : G)
    (hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹)
    (hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹) (p : ↥(A ⊔ K)) : ↥(A ⊔ K) :=
  ⟨Classical.choose (conj_mem_sup A K hKA hsA hsK p.2),
   (Classical.choose_spec (conj_mem_sup A K hKA hsA hsK p.2)).1⟩

lemma conjFun_spec (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {ε : S →* G} {s : G}
    {hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹}
    {hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹} (p : ↥(A ⊔ K)) :
    ε ((conjFun A K hKA s hsA hsK p : ↥(A ⊔ K)) : S) = s * ε (p : S) * s⁻¹ :=
  (Classical.choose_spec (conj_mem_sup A K hKA hsA hsK p.2)).2

lemma conjFun_mul (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {ε : S →* G}
    (hε : Function.Injective ε) {s : G}
    {hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹}
    {hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹} (p q : ↥(A ⊔ K)) :
    conjFun A K hKA s hsA hsK (p * q) =
      conjFun A K hKA s hsA hsK p * conjFun A K hKA s hsA hsK q := by
  apply Subtype.ext
  apply hε
  have hpq : ((conjFun A K hKA s hsA hsK p * conjFun A K hKA s hsA hsK q :
      ↥(A ⊔ K)) : S) =
      (conjFun A K hKA s hsA hsK p : S) * (conjFun A K hKA s hsA hsK q : S) := rfl
  rw [hpq, map_mul, conjFun_spec, conjFun_spec, conjFun_spec]
  have hpq2 : ε ((p * q : ↥(A ⊔ K)) : S) = ε (p : S) * ε (q : S) := by
    rw [show ((p * q : ↥(A ⊔ K)) : S) = (p : S) * (q : S) from rfl, map_mul]
  rw [hpq2]
  group

@[expose] noncomputable def conjAut (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {ε : S →* G} (hε : Function.Injective ε) (s : G)
    (hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹)
    (hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹) : MulAut ↥(A ⊔ K) :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (conjFun A K hKA s hsA hsK)
      (conjFun_mul A K hKA hε (hsA := hsA) (hsK := hsK)))
    (Finite.injective_iff_bijective.mp (by
      intro p q hpq
      change conjFun A K hKA s hsA hsK p = conjFun A K hKA s hsA hsK q at hpq
      have h1 : ε (conjFun A K hKA s hsA hsK p : S) =
          ε (conjFun A K hKA s hsA hsK q : S) := by rw [hpq]
      rw [conjFun_spec, conjFun_spec] at h1
      have h2 : ε (p : S) = ε (q : S) :=
        mul_left_cancel (mul_right_cancel h1)
      exact Subtype.ext (hε h2)))

lemma conjAut_spec (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {ε : S →* G}
    (hε : Function.Injective ε) (s : G)
    {hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹}
    {hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹} (p : ↥(A ⊔ K)) :
    ε ((conjAut A K hKA hε s hsA hsK p : ↥(A ⊔ K)) : S) = s * ε (p : S) * s⁻¹ :=
  conjFun_spec A K hKA (ε := ε) (s := s) (hsA := hsA) (hsK := hsK) p

lemma conjAut_mem_A (hKA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {ε : S →* G}
    (hε : Function.Injective ε) (s : G)
    {hsA : ∀ a ∈ A, ∃ a' ∈ A, ε a' = s * ε a * s⁻¹}
    {hsK : ∀ g ∈ K, ∃ g' ∈ K, ε g' = s * ε g * s⁻¹} {y : ↥(A ⊔ K)}
    (hy : (y : S) ∈ A) :
    ((conjAut A K hKA hε s hsA hsK y : ↥(A ⊔ K)) : S) ∈ A := by
  obtain ⟨a', ha', ha'eq⟩ := hsA y hy
  have hval : ((conjAut A K hKA hε s hsA hsK y : ↥(A ⊔ K)) : S) = (a' : S) := by
    apply hε
    rw [conjAut_spec A K hKA hε s (hsA := hsA) (hsK := hsK) y, ha'eq]
  rw [hval]; exact ha'

end Helpers

end CFSG.LinearAlgebra.RootGroupSL.AutSemidirect
