module

public import CFSG.FeitThompson.Representations.CommonClassScaledQuadraticCongruence
import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
import CFSG.FeitThompson.Representations.DegreeQuotientCentralCharacterSum
import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger
import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {G : Type*} [Group G]

theorem carrier_mk_inv (u : G) :
    (ConjClasses.mk u⁻¹).carrier = (ConjClasses.mk u).carrier⁻¹ := by
  ext x
  simp only [Set.mem_inv, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨fun h => by simpa using Representation.isConj_inv_inv h,
    fun h => by simpa using Representation.isConj_inv_inv h⟩

theorem mk_inv_eq_of_carrier_eq_inv {K L : ConjClasses G} (hinv : L.carrier = K.carrier⁻¹)
    {u : G} (hu : ConjClasses.mk u = K) : ConjClasses.mk u⁻¹ = L := by
  rw [← ConjClasses.mem_carrier_iff_mk_eq, hinv, Set.mem_inv, inv_inv,
    ConjClasses.mem_carrier_iff_mk_eq]
  exact hu

theorem one_mem_Irr : (1 : G → ℂ) ∈ Irr G := by
  refine mem_Irr.2 ⟨FDRep.of (Representation.trivial ℂ G ℂ), ?_, ?_⟩
  · apply isIrreducible_of_forall_map_le (k := ℂ)
    intro W _
    exact eq_bot_or_eq_top W
  · funext g
    have h : (FDRep.of (Representation.trivial ℂ G ℂ)).ρ g = LinearMap.id := by
      rw [FDRep.of_ρ']
      · rfl
    rw [FDRep.character, h]
    simp

theorem mem_algIntegerMultiples_of_coprime {t n : ℕ} (h : Nat.Coprime n t) {x : ℂ}
    (hx : IsIntegral ℤ x) (hnx : (n : ℂ) * x ∈ algIntegerMultiples (t : ℂ)) :
    x ∈ algIntegerMultiples (t : ℂ) := by
  obtain ⟨a, b, hab⟩ : IsCoprime (n : ℤ) (t : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have hx' : x = (a : ℤ) • ((n : ℂ) * x) + (t : ℂ) * ((b : ℂ) * x) := by
    have h' : ((a * (n : ℤ) + b * (t : ℤ) : ℤ) : ℂ) * x = x := by rw [hab]; push_cast; ring
    push_cast at h'
    rw [zsmul_eq_mul]
    linear_combination -h'
  rw [hx']
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hnx)
    (mul_mem_algIntegerMultiples _ ((isIntegral_intCast b).mul hx))

theorem intCast_dvd_of_mem_algIntegerMultiples {t : ℕ} {a : ℤ}
    (h : (a : ℂ) ∈ algIntegerMultiples (t : ℂ)) : (t : ℤ) ∣ a := by
  obtain ⟨r, hr, hra⟩ := mem_algIntegerMultiples_iff.1 h
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [Nat.cast_zero, zero_mul] at hra
    have ha : a = 0 := by exact_mod_cast hra
    simp [ha]
  · have hq : ∃ q : ℚ, r = (q : ℂ) := by
      refine ⟨(a : ℚ) / (t : ℚ), ?_⟩
      have ht' : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ht
      push_cast
      field_simp
      linear_combination -hra
    obtain ⟨m, hm⟩ := (Complex.isIntegral_int_iff_exists_int_of_exists_rat hq).1 hr
    refine ⟨m, ?_⟩
    have h' : (a : ℂ) = ((t * m : ℤ) : ℂ) := by rw [hra, hm]; push_cast; ring
    exact_mod_cast h'

section Finite

variable [Fintype G] [DecidableEq G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem classStructureConstant_self_one_eq_zero {K L : ConjClasses G}
    (hinv : L.carrier = K.carrier⁻¹) (hKL : K ≠ L) : classStructureConstant K K 1 = 0 := by
  have hmk : (1 : ConjClasses G) = ConjClasses.mk (1 : G) := rfl
  rw [hmk, classStructureConstant_eq_card, Finset.card_eq_zero]
  refine Finset.eq_empty_iff_forall_notMem.2 fun p hp => ?_
  rw [mem_classProdPairs] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have h4 : p.1⁻¹ = p.2 := inv_eq_of_mul_eq_one_right h3
  exact hKL (by rw [← h2, ← h4, mk_inv_eq_of_carrier_eq_inv hinv h1])

theorem classStructureConstant_inv_one {K L : ConjClasses G} (hinv : L.carrier = K.carrier⁻¹) :
    classStructureConstant K L 1 = Nat.card K.carrier := by
  have hmk : (1 : ConjClasses G) = ConjClasses.mk (1 : G) := rfl
  rw [hmk, classStructureConstant_eq_card, Nat.card_eq_fintype_card, ← Set.toFinset_card]
  refine Finset.card_bij' (fun p _ => p.1) (fun u _ => (u, u⁻¹)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_classProdPairs] at hp
    simpa [ConjClasses.mem_carrier_iff_mk_eq] using hp.1
  · intro u hu
    simp only [Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq] at hu
    rw [mem_classProdPairs]
    exact ⟨hu, mk_inv_eq_of_carrier_eq_inv hinv hu, mul_inv_cancel u⟩
  · intro p hp
    rw [mem_classProdPairs] at hp
    exact Prod.ext rfl (inv_eq_of_mul_eq_one_right hp.2.2)
  · intro u _
    rfl

noncomputable def classStructureConstantDiffSum (I : Finset (ConjClasses G))
    (K L : ConjClasses G) : ℤ :=
  ∑ M ∈ I, ((classStructureConstant K K M : ℤ) - (classStructureConstant K L M : ℤ))

theorem classStructureConstantDiffSum_def (I : Finset (ConjClasses G)) (K L : ConjClasses G) :
    classStructureConstantDiffSum I K L
      = ∑ M ∈ I, ((classStructureConstant K K M : ℤ) - (classStructureConstant K L M : ℤ)) :=
  (rfl)

@[simp]
theorem classStructureConstantDiffSum_self (I : Finset (ConjClasses G)) (K : ConjClasses G) :
    classStructureConstantDiffSum I K K = 0 := by
  rw [classStructureConstantDiffSum_def]; simp

@[simp]
theorem classStructureConstantDiffSum_empty (K L : ConjClasses G) :
    classStructureConstantDiffSum (∅ : Finset (ConjClasses G)) K L = 0 := by
  rw [classStructureConstantDiffSum_def]; simp

theorem cast_classStructureConstantDiffSum (I : Finset (ConjClasses G)) (K L : ConjClasses G) :
    ((classStructureConstantDiffSum I K L : ℤ) : ℂ)
      = ((∑ M ∈ I, classStructureConstant K K M : ℕ) : ℂ)
        - ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ) := by
  rw [classStructureConstantDiffSum_def]
  push_cast
  rw [Finset.sum_sub_distrib]

theorem Representation.classStructureConstantDiffSum_mul_smodEq
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] {t n : ℕ}
    (hnt : Nat.Coprime n t) {I : Finset (ConjClasses G)} (hI1 : (1 : ConjClasses G) ∉ I)
    (hcard : ∀ M ∈ I, Nat.card M.carrier = n)
    (hdvd : ∀ K ∈ I, ∀ L ∈ I, ∀ M : ConjClasses G, M ∉ I → M ≠ 1 →
      t ∣ classStructureConstant K L M * Nat.card M.carrier)
    {c : ℂ} (hc : ∀ x : G, ConjClasses.mk x ∈ I → ρ.character x = c)
    {K L : ConjClasses G} (hK : K ∈ I) (hL : L ∈ I)
    (hinv : L.carrier = K.carrier⁻¹) (hKL : K ≠ L) :
    ((classStructureConstantDiffSum I K L : ℤ) : ℂ) * c ≡ ρ.character 1
      [SMOD algIntegerMultiples (t : ℂ)] := by
  have hD : ρ.character 1 ≠ 0 := character_one_ne_zero (k := ℂ) ρ
  have hc' : c = ρ.character (classRep K) := (hc _ (by rw [mk_classRep]; exact hK)).symm
  have hcint : IsIntegral ℤ c := hc' ▸ Representation.isIntegral_character ρ _
  have hBint : IsIntegral ℤ (((classStructureConstantDiffSum I K L : ℤ) : ℂ) * c
      - ρ.character 1) :=
    ((isIntegral_intCast _).mul hcint).sub (Representation.isIntegral_character ρ 1)
  refine SModEq.sub_mem.2 (mem_algIntegerMultiples_of_coprime (n := n) hnt hBint ?_)
  have h1 := Representation.character_one_mul_sq_smodEq ρ hI1 hcard hdvd hc hK hK
  have h2 := Representation.character_one_mul_sq_smodEq ρ hI1 hcard hdvd hc hK hL
  have hmem := SModEq.sub_mem.1 (h1.sub h2)
  have hw : ρ.character 1 * ((n : ℂ) * c / ρ.character 1) = (n : ℂ) * c :=
    mul_div_cancel₀ _ hD
  have hkey : (n : ℂ) * (((classStructureConstantDiffSum I K L : ℤ) : ℂ) * c - ρ.character 1)
      = -((ρ.character 1 * ((n : ℂ) * c / ρ.character 1) ^ 2
            - ρ.character 1 * ((n : ℂ) * c / ρ.character 1) ^ 2)
        - ((ρ.character 1 * (classStructureConstant K K 1 : ℂ)
            + ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
              ((∑ M ∈ I, classStructureConstant K K M : ℕ) : ℂ))
          - (ρ.character 1 * (classStructureConstant K L 1 : ℂ)
            + ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
              ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ)))) := by
    rw [classStructureConstant_self_one_eq_zero hinv hKL, classStructureConstant_inv_one hinv,
      hcard K hK, cast_classStructureConstantDiffSum]
    rw [show ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
          ((∑ M ∈ I, classStructureConstant K K M : ℕ) : ℂ)
          = ((n : ℂ) * c) * ((∑ M ∈ I, classStructureConstant K K M : ℕ) : ℂ) by rw [hw],
      show ρ.character 1 * ((n : ℂ) * c / ρ.character 1) *
          ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ)
          = ((n : ℂ) * c) * ((∑ M ∈ I, classStructureConstant K L M : ℕ) : ℂ) by rw [hw]]
    push_cast
    ring
  rw [hkey]
  exact Submodule.neg_mem _ hmem

theorem Irr.classStructureConstantDiffSum_mul_smodEq {φ : G → ℂ} (hφ : φ ∈ Irr G) {t n : ℕ}
    (hnt : Nat.Coprime n t) {I : Finset (ConjClasses G)} (hI1 : (1 : ConjClasses G) ∉ I)
    (hcard : ∀ M ∈ I, Nat.card M.carrier = n)
    (hdvd : ∀ K ∈ I, ∀ L ∈ I, ∀ M : ConjClasses G, M ∉ I → M ≠ 1 →
      t ∣ classStructureConstant K L M * Nat.card M.carrier)
    {c : ℂ} (hc : ∀ x : G, ConjClasses.mk x ∈ I → φ x = c)
    {K L : ConjClasses G} (hK : K ∈ I) (hL : L ∈ I)
    (hinv : L.carrier = K.carrier⁻¹) (hKL : K ≠ L) :
    ((classStructureConstantDiffSum I K L : ℤ) : ℂ) * c ≡ φ 1
      [SMOD algIntegerMultiples (t : ℂ)] := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hφ
  have _i : Representation.IsIrreducible W.ρ := hW
  exact Representation.classStructureConstantDiffSum_mul_smodEq _ hnt hI1 hcard hdvd hc hK hL
    hinv hKL

theorem dvd_classStructureConstantDiffSum_sub_one {t n : ℕ}
    (hnt : Nat.Coprime n t) {I : Finset (ConjClasses G)} (hI1 : (1 : ConjClasses G) ∉ I)
    (hcard : ∀ M ∈ I, Nat.card M.carrier = n)
    (hdvd : ∀ K ∈ I, ∀ L ∈ I, ∀ M : ConjClasses G, M ∉ I → M ≠ 1 →
      t ∣ classStructureConstant K L M * Nat.card M.carrier)
    {K L : ConjClasses G} (hK : K ∈ I) (hL : L ∈ I)
    (hinv : L.carrier = K.carrier⁻¹) (hKL : K ≠ L) :
    (t : ℤ) ∣ classStructureConstantDiffSum I K L - 1 := by
  have h := Irr.classStructureConstantDiffSum_mul_smodEq (φ := (1 : G → ℂ)) one_mem_Irr hnt hI1
    hcard hdvd (c := 1) (fun x _ => rfl) hK hL hinv hKL
  exact intCast_dvd_of_mem_algIntegerMultiples (by simpa using SModEq.sub_mem.1 h)

end Finite

end CFSG.FeitThompson
