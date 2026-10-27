module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def f4SimpleEuclid : Fin Tag.F4.rank → Fin 4 → ℚ :=
  ![![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 0, 1], ![1 / 2, -1 / 2, -1 / 2, -1 / 2]]

@[expose] def f4Euclid (v : Fin Tag.F4.rank → ℤ) : Fin 4 → ℚ :=
  ∑ i, (v i : ℚ) • f4SimpleEuclid i

@[expose] def euclidReflect (a x : Fin 4 → ℚ) : Fin 4 → ℚ :=
  x - (2 * (x ⬝ᵥ a) / (a ⬝ᵥ a)) • a

@[expose] def f4LongEuclid : Set (Fin 4 → ℚ) :=
  {x | ∃ i j : Fin 4, i < j ∧ ∃ a ∈ ({1, -1} : Finset ℚ), ∃ b ∈ ({1, -1} : Finset ℚ),
    x = a • Pi.single i 1 + b • Pi.single j 1}

@[expose] def f4ShortEuclid : Set (Fin 4 → ℚ) :=
  {x | (∃ i : Fin 4, ∃ a ∈ ({1, -1} : Finset ℚ), x = a • Pi.single i 1) ∨
    ∀ k, x k ∈ ({1 / 2, -1 / 2} : Finset ℚ)}

@[expose] def f4PosEuclid : Set (Fin 4 → ℚ) :=
  {x | (∃ i j : Fin 4, i < j ∧ ∃ b ∈ ({1, -1} : Finset ℚ), x = Pi.single i 1 + b • Pi.single j 1) ∨
    (∃ i : Fin 4, x = Pi.single i 1) ∨ (x 0 = 1 / 2 ∧ ∀ k, x k ∈ ({1 / 2, -1 / 2} : Finset ℚ))}

theorem f4Euclid_add (x y : Fin Tag.F4.rank → ℤ) : f4Euclid (x + y) = f4Euclid x + f4Euclid y := by
  simp only [f4Euclid, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

theorem f4Euclid_neg (x : Fin Tag.F4.rank → ℤ) : f4Euclid (-x) = -f4Euclid x := by
  simp only [f4Euclid, Pi.neg_apply, Int.cast_neg, neg_smul, Finset.sum_neg_distrib]

theorem f4Euclid_sub (x y : Fin Tag.F4.rank → ℤ) : f4Euclid (x - y) = f4Euclid x - f4Euclid y := by
  rw [sub_eq_add_neg, f4Euclid_add, f4Euclid_neg, ← sub_eq_add_neg]

theorem f4Euclid_zsmul (c : ℤ) (x : Fin Tag.F4.rank → ℤ) :
    f4Euclid (c • x) = (c : ℚ) • f4Euclid x := by
  simp only [f4Euclid, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul, Finset.smul_sum]

theorem f4Euclid_single (i : Fin Tag.F4.rank) :
    f4Euclid (Pi.single i 1) = f4SimpleEuclid i := by
  revert i
  decide +kernel

theorem f4SimpleEuclid_dotProduct (i j : Fin Tag.F4.rank) :
    f4SimpleEuclid i ⬝ᵥ f4SimpleEuclid j = (Tag.F4.symmetrizedCartan i j : ℚ) / 2 := by
  revert i j
  decide +kernel

theorem f4Euclid_dotProduct (x y : Fin Tag.F4.rank → ℤ) :
    f4Euclid x ⬝ᵥ f4Euclid y = (iform x y : ℚ) / 2 := by
  simp only [f4Euclid, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
    f4SimpleEuclid_dotProduct, iform, Int.cast_sum, Int.cast_mul, Finset.sum_div, smul_eq_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem f4Euclid_injective
    : Function.Injective f4Euclid := by
  intro x y h
  have h' : f4Euclid (x - y) = 0 := by rw [f4Euclid_sub, h, sub_self]
  have h0 : iform (x - y) (x - y) = 0 := by
    have := congrArg (fun z => z ⬝ᵥ f4Euclid (x - y)) h'
    simp only [zero_dotProduct, f4Euclid_dotProduct] at this
    exact_mod_cast (div_eq_zero_iff.1 this).resolve_right two_ne_zero
  by_contra hne
  exact (iform_self_pos (sub_ne_zero.2 hne)).ne' h0

theorem f4Euclid_smul_dotProduct
    (w : WeylGroup .F4) (x y : Fin Tag.F4.rank → ℤ) :
    f4Euclid (w • x) ⬝ᵥ f4Euclid (w • y) = f4Euclid x ⬝ᵥ f4Euclid y := by
  rw [f4Euclid_dotProduct, f4Euclid_dotProduct, iform_smul]

theorem f4Euclid_rootReflection
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (v : Fin Tag.F4.rank → ℤ) :
    f4Euclid (rootReflection β • v) = euclidReflect (f4Euclid β) (f4Euclid v) := by
  have hp := iform_self_pos_of_isRoot hβ
  have hc : (corootPair β v : ℚ) = 2 * (f4Euclid v ⬝ᵥ f4Euclid β) / (f4Euclid β ⬝ᵥ f4Euclid β) := by
    rw [f4Euclid_dotProduct, f4Euclid_dotProduct, iform_comm v β, eq_div_iff (by positivity)]
    have := corootPair_mul hβ v
    have hq : ((corootPair β v * iform β β : ℤ) : ℚ) = ((2 * iform β v : ℤ) : ℚ) := by rw [this]
    push_cast at hq
    linear_combination hq / 2
  rw [rootReflection_smul hβ, f4Euclid_sub, f4Euclid_zsmul, euclidReflect, hc]

theorem f4Euclid_reflect
    (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) :
    f4Euclid (reflect .F4 i v) = euclidReflect (f4SimpleEuclid i) (f4Euclid v) := by
  have h : rootReflection (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = simple .F4 i := by
    rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]
  rw [← simple_smul, ← h, f4Euclid_rootReflection (isRoot_single _ i), f4Euclid_single]

theorem f4_rootCertificate_length : Tag.F4.rootCertificate.roots.length = 48 := rfl

theorem f4Euclid_root_mem (k : Fin 48) :
    f4Euclid (Tag.F4.rootCertificate.root k) ∈ f4LongEuclid ∪ f4ShortEuclid := by
  revert k
  simp only [Set.mem_union, f4LongEuclid, f4ShortEuclid, Set.mem_ofPred_eq]
  decide +kernel

theorem exists_f4Euclid_root_long :
    ∀ i j : Fin 4, i < j → ∀ a ∈ ({1, -1} : Finset ℚ), ∀ b ∈ ({1, -1} : Finset ℚ),
      ∃ k : Fin 48, f4Euclid (Tag.F4.rootCertificate.root k) =
        a • Pi.single i 1 + b • Pi.single j 1 := by
  decide +kernel

theorem exists_f4Euclid_root_unit :
    ∀ i : Fin 4, ∀ a ∈ ({1, -1} : Finset ℚ),
      ∃ k : Fin 48, f4Euclid (Tag.F4.rootCertificate.root k) = a • Pi.single i 1 := by
  decide +kernel

theorem exists_f4Euclid_root_half :
    ∀ c₀ ∈ ({1 / 2, -1 / 2} : Finset ℚ), ∀ c₁ ∈ ({1 / 2, -1 / 2} : Finset ℚ),
      ∀ c₂ ∈ ({1 / 2, -1 / 2} : Finset ℚ), ∀ c₃ ∈ ({1 / 2, -1 / 2} : Finset ℚ),
      ∃ k : Fin 48, f4Euclid (Tag.F4.rootCertificate.root k) = ![c₀, c₁, c₂, c₃] := by
  decide +kernel

theorem isRoot_f4_iff {v : Fin Tag.F4.rank → ℤ} :
    IsRoot .F4 v ↔ ∃ k : Fin 48, Tag.F4.rootCertificate.root k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4), f4_rootCertificate_length]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩, fun ⟨k, h⟩ => ⟨k, k.2, h⟩⟩

theorem f4Euclid_image_roots :
    f4Euclid '' {v | IsRoot .F4 v} = f4LongEuclid ∪ f4ShortEuclid := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hv
    exact f4Euclid_root_mem k
  · intro hx
    have hroot : ∀ k : Fin 48, IsRoot .F4 (Tag.F4.rootCertificate.root k) :=
      fun k => isRoot_f4_iff.2 ⟨k, rfl⟩
    rcases hx with ⟨i, j, hij, a, ha, b, hb, rfl⟩ | ⟨i, a, ha, rfl⟩ | hx
    · obtain ⟨k, hk⟩ := exists_f4Euclid_root_long i j hij a ha b hb
      exact ⟨_, hroot k, hk⟩
    · obtain ⟨k, hk⟩ := exists_f4Euclid_root_unit i a ha
      exact ⟨_, hroot k, hk⟩
    · obtain ⟨k, hk⟩ := exists_f4Euclid_root_half _ (hx 0) _ (hx 1) _ (hx 2) _ (hx 3)
      refine ⟨_, hroot k, hk.trans ?_⟩
      funext m
      fin_cases m <;> rfl

theorem dotProduct_self_of_mem_f4LongEuclid {x : Fin 4 → ℚ} (hx : x ∈ f4LongEuclid) :
    x ⬝ᵥ x = 2 := by
  obtain ⟨i, j, hij, a, ha, b, hb, rfl⟩ := hx
  revert i j a b
  decide +kernel

theorem dotProduct_self_of_mem_f4ShortEuclid {x : Fin 4 → ℚ} (hx : x ∈ f4ShortEuclid) :
    x ⬝ᵥ x = 1 := by
  rcases hx with ⟨i, a, ha, rfl⟩ | hx
  · revert i a
    decide +kernel
  · have e : x = ![x 0, x 1, x 2, x 3] := by
      funext m
      fin_cases m <;> rfl
    have key : ∀ c₀ ∈ ({1 / 2, -1 / 2} : Finset ℚ), ∀ c₁ ∈ ({1 / 2, -1 / 2} : Finset ℚ),
        ∀ c₂ ∈ ({1 / 2, -1 / 2} : Finset ℚ), ∀ c₃ ∈ ({1 / 2, -1 / 2} : Finset ℚ),
        ![c₀, c₁, c₂, c₃] ⬝ᵥ ![c₀, c₁, c₂, c₃] = 1 := by decide +kernel
    rw [e]
    exact key _ (hx 0) _ (hx 1) _ (hx 2) _ (hx 3)

theorem f4Euclid_root_mem_pos (k : Fin 48) (hk : 0 < height (Tag.F4.rootCertificate.root k)) :
    f4Euclid (Tag.F4.rootCertificate.root k) ∈ f4PosEuclid := by
  revert k
  simp only [f4PosEuclid, Set.mem_ofPred_eq]
  decide +kernel

theorem exists_f4Euclid_posRoot_long :
    ∀ i j : Fin 4, i < j → ∀ b ∈ ({1, -1} : Finset ℚ),
      ∃ k : Fin 48, 0 < height (Tag.F4.rootCertificate.root k) ∧
        f4Euclid (Tag.F4.rootCertificate.root k) = Pi.single i 1 + b • Pi.single j 1 := by
  decide +kernel

theorem exists_f4Euclid_posRoot_unit :
    ∀ i : Fin 4, ∃ k : Fin 48, 0 < height (Tag.F4.rootCertificate.root k) ∧
      f4Euclid (Tag.F4.rootCertificate.root k) = Pi.single i 1 := by
  decide +kernel

theorem exists_f4Euclid_posRoot_half :
    ∀ c₁ ∈ ({1 / 2, -1 / 2} : Finset ℚ), ∀ c₂ ∈ ({1 / 2, -1 / 2} : Finset ℚ),
      ∀ c₃ ∈ ({1 / 2, -1 / 2} : Finset ℚ),
      ∃ k : Fin 48, 0 < height (Tag.F4.rootCertificate.root k) ∧
        f4Euclid (Tag.F4.rootCertificate.root k) = ![1 / 2, c₁, c₂, c₃] := by
  decide +kernel

theorem f4Euclid_image_posRoots :
    f4Euclid '' {v | IsRoot .F4 v ∧ 0 < height v} = f4PosEuclid := by
  ext x
  constructor
  · rintro ⟨v, ⟨hv, hh⟩, rfl⟩
    obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hv
    exact f4Euclid_root_mem_pos k hh
  · intro hx
    have hroot : ∀ k : Fin 48, IsRoot .F4 (Tag.F4.rootCertificate.root k) :=
      fun k => isRoot_f4_iff.2 ⟨k, rfl⟩
    rcases hx with ⟨i, j, hij, b, hb, rfl⟩ | ⟨i, rfl⟩ | ⟨h0, hx⟩
    · obtain ⟨k, hk, hk'⟩ := exists_f4Euclid_posRoot_long i j hij b hb
      exact ⟨_, ⟨hroot k, hk⟩, hk'⟩
    · obtain ⟨k, hk, hk'⟩ := exists_f4Euclid_posRoot_unit i
      exact ⟨_, ⟨hroot k, hk⟩, hk'⟩
    · obtain ⟨k, hk, hk'⟩ := exists_f4Euclid_posRoot_half _ (hx 1) _ (hx 2) _ (hx 3)
      refine ⟨_, ⟨hroot k, hk⟩, hk'.trans ?_⟩
      funext m
      fin_cases m
      · exact h0.symm
      all_goals rfl

theorem f4_rootCertificate_root_injective :
    Function.Injective fun k : Fin 48 => Tag.F4.rootCertificate.root k := by
  intro k l h
  revert k l
  decide +kernel

theorem ncard_f4_posRoots
    : {v : Fin Tag.F4.rank → ℤ | IsRoot .F4 v ∧ 0 < height v}.ncard = 24 := by
  have hS : {v : Fin Tag.F4.rank → ℤ | IsRoot .F4 v ∧ 0 < height v} =
      (fun k : Fin 48 => Tag.F4.rootCertificate.root k) ''
        ↑((Finset.univ : Finset (Fin 48)).filter
          fun k : Fin 48 => 0 < height (Tag.F4.rootCertificate.root k)) := by
    ext v
    constructor
    · rintro ⟨hv, hh⟩
      obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hv
      exact ⟨k, by simpa using hh, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨isRoot_f4_iff.2 ⟨k, rfl⟩, by simpa using hk⟩
  rw [hS, Set.ncard_image_of_injective _ f4_rootCertificate_root_injective, Set.ncard_coe_finset]
  decide +kernel

end CFSG.LieType.Chevalley
