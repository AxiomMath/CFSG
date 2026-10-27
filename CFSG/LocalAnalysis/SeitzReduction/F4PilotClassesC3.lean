module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)

section Transport


theorem canonicalRep_mul_mul_inv_mem_rootSpan {τ : Tag} {R : Type} [CommRing R]
    (w : WeylGroup τ) {S T : Set (Fin τ.rank → ℤ)} (hT : ∀ α ∈ T, IsRoot τ α ∧ w • α ∈ S)
    {z : (Module.End R (RootModule τ R))ˣ} (hz : z ∈ rootSpan τ R T) :
    canonicalRep (coxeterSystem τ) R w * z * (canonicalRep (coxeterSystem τ) R w)⁻¹ ∈
      rootSpan τ R S := by
  have h := (canonical_weyl_root_transport τ R).1 w T fun α hα => (hT α hα).1
  have hz' := Subgroup.mem_map_of_mem
    (MulAut.conj (canonicalRep (coxeterSystem τ) R w)).toMonoidHom hz
  rw [h] at hz'
  have hle : rootSpan τ R ((fun α => w • α) '' T) ≤ rootSpan τ R S := biSup_mono fun α hα => by
    obtain ⟨β, hβ, rfl⟩ := hα
    exact (hT β hβ).2
  exact hle hz'

end Transport

theorem orbitCertRoot_eq_rootR_rootS_root1221_root1242 :
    orbitCertRoot .F4 47 = rootR ∧ orbitCertRoot .F4 44 = rootS ∧
      orbitCertRoot .F4 41 = root1221 ∧ orbitCertRoot .F4 45 = root1242 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem dualRoot_rootR_rootS_root1221_root1242 :
    ReeTag.F4.dualRoot rootR = rootS ∧ ReeTag.F4.dualRoot rootS = rootR ∧
      ReeTag.F4.dualRoot root1221 = root1242 ∧ ReeTag.F4.dualRoot root1242 = root1221 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

section Roots


theorem isRoot_root1221_root1242 : IsRoot .F4 root1221 ∧ IsRoot .F4 root1242 :=
  ⟨mem_rootFinset.1 (by decide +kernel), mem_rootFinset.1 (by decide +kernel)⟩

theorem isRoot_dualRoot_mem_pair :
    (∀ α ∈ ({rootR, rootS} : Set (Fin (Tag.rank .F4) → ℤ)),
      IsRoot .F4 α ∧ ReeTag.F4.dualRoot α ∈ ({rootR, rootS} : Set (Fin (Tag.rank .F4) → ℤ))) ∧
    (∀ α ∈ ({root1221, root1242} : Set (Fin (Tag.rank .F4) → ℤ)),
      IsRoot .F4 α ∧
        ReeTag.F4.dualRoot α ∈ ({root1221, root1242} : Set (Fin (Tag.rank .F4) → ℤ))) := by
  obtain ⟨h1, h2, h3, h4⟩ := dualRoot_rootR_rootS_root1221_root1242
  refine ⟨?_, ?_⟩
  · rintro α (rfl | rfl)
    · exact ⟨isRoot_rootR, by rw [h1]; exact Set.mem_insert_of_mem _ rfl⟩
    · exact ⟨isRoot_rootS, by rw [h2]; exact Set.mem_insert _ _⟩
  · rintro α (rfl | rfl)
    · exact ⟨isRoot_root1221_root1242.1, by rw [h3]; exact Set.mem_insert_of_mem _ rfl⟩
    · exact ⟨isRoot_root1221_root1242.2, by rw [h4]; exact Set.mem_insert _ _⟩

end Roots

variable {K : Type} [Field K]

section Pairs


theorem pinnedX_mem_rootSpan_pair (a b : Fin Tag.F4.rank → ℤ) (c : K) :
    pinnedX .F4 K a c ∈ rootSpan .F4 K {a, b} ∧ pinnedX .F4 K b c ∈ rootSpan .F4 K {a, b} :=
  ⟨pinnedX_mem_rootSpan (Set.mem_insert a {b}) c,
    pinnedX_mem_rootSpan (Set.mem_insert_of_mem a (Set.mem_singleton b)) c⟩

theorem f4x_mem_rootSpan_pair :
    f4x K 47 1 ∈ rootSpan .F4 K {rootR, rootS} ∧
      f4x K 47 1 * f4x K 44 1 ∈ rootSpan .F4 K {rootR, rootS} ∧
      f4x K 41 1 * f4x K 45 1 ∈ rootSpan .F4 K {root1221, root1242} := by
  obtain ⟨e47, e44, e41, e45⟩ := orbitCertRoot_eq_rootR_rootS_root1221_root1242
  obtain ⟨hr, hs⟩ := pinnedX_mem_rootSpan_pair (K := K) rootR rootS 1
  obtain ⟨h1, h2⟩ := pinnedX_mem_rootSpan_pair (K := K) root1221 root1242 1
  simp only [f4x, e47, e44, e41, e45]
  exact ⟨hr, mul_mem hr hs, mul_mem h1 h2⟩

end Pairs

section Weyl


theorem exists_conj_mem_C3_of_smul_mem (w : WeylGroup .F4) {T : Set (Fin (Tag.rank .F4) → ℤ)}
    (hT : ∀ α ∈ T, IsRoot .F4 α ∧ w • α ∈ C3Set) {z : adjointGroup .F4 K}
    (hz : (z : ModGL .F4 K) ∈ rootSpan .F4 K T) :
    ∃ n : adjointGroup .F4 K,
      ((n * z * n⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set :=
  ⟨⟨canonicalRep (coxeterSystem .F4) K w, canonicalRep_mem_adjointGroup _ K w⟩,
    canonicalRep_mul_mul_inv_mem_rootSpan w hT hz⟩

theorem exists_conj_mem_C3_of_mem_rootSpan_pair {z : adjointGroup .F4 K}
    (hz : (z : ModGL .F4 K) ∈ rootSpan .F4 K {rootR, rootS} ∨
      (z : ModGL .F4 K) ∈ rootSpan .F4 K {root1221, root1242}) :
    ∃ n : adjointGroup .F4 K,
      ((n * z * n⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  obtain ⟨h1221, h1242⟩ := isRoot_root1221_root1242
  rcases hz with hz | hz
  · obtain ⟨hr, hs⟩ := weylOfWord_rootR_rootS_mem_C3Roots
    refine exists_conj_mem_C3_of_smul_mem (weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0])
      (fun α hα => ?_) hz
    rcases hα with rfl | rfl
    · exact ⟨isRoot_rootR, mem_C3Set_iff.2 ⟨IsRoot.smul isRoot_rootR _, by rw [hr]; rfl⟩⟩
    · exact ⟨isRoot_rootS, mem_C3Set_iff.2 ⟨IsRoot.smul isRoot_rootS _, by rw [hs]; rfl⟩⟩
  · obtain ⟨h1, h2⟩ := weylOfWord_endPair_mem_C3Roots
    refine exists_conj_mem_C3_of_smul_mem (weylOfWord .F4 [1, 2, 1, 3, 2, 1, 0])
      (fun α hα => ?_) hz
    rcases hα with rfl | rfl
    · exact ⟨h1221, mem_C3Set_iff.2 ⟨IsRoot.smul h1221 _, by rw [h1]; rfl⟩⟩
    · exact ⟨h1242, mem_C3Set_iff.2 ⟨IsRoot.smul h1242 _, by rw [h2]; rfl⟩⟩

end Weyl

section Phi


variable [Finite K] [CharP K 2]

theorem f4DescPhi_pow_mem_rootSpan {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot .F4 α ∧ ReeTag.F4.dualRoot α ∈ S) (k : ℕ) {u : adjointGroup .F4 K}
    (hu : (u : ModGL .F4 K) ∈ rootSpan .F4 K S) :
    (((f4DescPhi K) ^ k) u : ModGL .F4 K) ∈ rootSpan .F4 K S := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact f4Desc_phi_mem_rootSpan hS ih

end Phi

theorem exists_mulAut_mem_rootSpan_pair [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : y ^ 2 = 1) (hy1 : y ≠ 1) :
    ∃ β : MulAut (adjointGroup .F4 K),
      ((β y : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K {rootR, rootS} ∨
        ((β y : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K {root1221, root1242} := by
  obtain ⟨ψ, L, hL, he⟩ := exists_mulAut_eq_f4DescProd hy hy1
  have hL' : L ∈ f4FrameCandidates := hL
  obtain ⟨g, hg, hgL⟩ := exists_conj_of_mem_f4FrameCandidates (K := K) hL'
  set g' : adjointGroup .F4 K := ⟨g, hg⟩ with hg'
  have hβ : (((MulAut.conj g' * ψ) y : adjointGroup .F4 K) : ModGL .F4 K) =
      g * f4CollProd K L * g⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, he]
    rfl
  refine ⟨MulAut.conj g' * ψ, ?_⟩
  rw [hβ]
  obtain ⟨ht, htu, hv⟩ := f4x_mem_rootSpan_pair (K := K)
  rcases hgL with h | h | h
  · exact Or.inl (by rw [h]; exact ht)
  · exact Or.inl (by rw [h]; exact htu)
  · exact Or.inr (by rw [h]; exact hv)

theorem exists_conj_mem_C3 [Finite K] [CharP K 2] {y : adjointGroup .F4 K} (hy : orderOf y = 2) :
    ∃ g : adjointGroup .F4 K,
      ((g * y * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by decide)
  obtain ⟨β, hβ⟩ := exists_mulAut_mem_rootSpan_pair hy2 hy1
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form n.pos K hK
  obtain ⟨⟨h₀, k⟩, hhk₀, -⟩ := hnf β⁻¹
  set h : adjointGroup .F4 K := h₀
  have hhk : β⁻¹ = MulAut.conj h * (f4DescPhi K) ^ (k : ℕ) := hhk₀
  clear_value h
  clear hhk₀
  obtain ⟨hS₁, hS₂⟩ := isRoot_dualRoot_mem_pair
  obtain ⟨m, hm⟩ := exists_conj_mem_C3_of_mem_rootSpan_pair
    (hβ.imp (f4DescPhi_pow_mem_rootSpan hS₁ k) (f4DescPhi_pow_mem_rootSpan hS₂ k))
  have hy' : y = h * ((f4DescPhi K) ^ (k : ℕ)) (β y) * h⁻¹ := by
    have e : β⁻¹ (β y) = y := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← MulAut.conj_apply, ← MulAut.mul_apply, ← hhk, e]
  obtain ⟨w, hw⟩ : ∃ w, ((f4DescPhi K) ^ (k : ℕ)) (β y) = w := ⟨_, rfl⟩
  rw [hw] at hm hy'
  refine ⟨m * h⁻¹, ?_⟩
  have e : m * h⁻¹ * y * (m * h⁻¹)⁻¹ = m * w * m⁻¹ := by
    rw [hy']
    group
  rw [e]
  exact hm

theorem exists_conj_mem_C3_of_sq_eq_one [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : y ^ 2 = 1) :
    ∃ g : adjointGroup .F4 K,
      ((g * y * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  by_cases h1 : y = 1
  · refine ⟨1, ?_⟩
    rw [h1, mul_one, one_mul, inv_one, Subgroup.coe_one]
    exact one_mem _
  · exact exists_conj_mem_C3 (orderOf_eq_prime hy h1)

theorem exists_conj_mem_C3' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : adjointGroup .F4 K} (hy : orderOf y = 2) :
    ∃ g : adjointGroup .F4 K,
      ((g * y * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact exists_conj_mem_C3 hy


theorem exists_conj_mem_subgroupOf_C3 [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : orderOf y = 2) :
    ∃ g : adjointGroup .F4 K,
      g * y * g⁻¹ ∈ (rootSpan .F4 K C3Set).subgroupOf (adjointGroup .F4 K) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_C3 hy
  exact ⟨g, Subgroup.mem_subgroupOf.2 hg⟩

theorem exists_conj_mem_C3_of_mulEquiv [Finite K] [CharP K 2] {L : Type*} [Group L]
    (e : L ≃* adjointGroup .F4 K) {y : L} (hy : y ^ 2 = 1) :
    ∃ l : L, ((e (l * y * l⁻¹) : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  obtain ⟨g, hg⟩ := exists_conj_mem_C3_of_sq_eq_one (y := e y) (by rw [← map_pow, hy, map_one])
  refine ⟨e.symm g, ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg

end CFSG.SeitzReduction.F4Pilot
