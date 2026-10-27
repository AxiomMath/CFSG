module

public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockProjection
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.Inflation

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.LyonsUnitaryFour

universe u

section Transport

variable {A A' : Type u} [Group A] [Fintype A] [Group A'] [Fintype A']

theorem characterPairing_mulEquiv (e : A ≃* A') (f g : A' → ℂ) :
    characterPairing (fun x : A => f (e x)) (fun x : A => g (e x)) = characterPairing f g := by
  unfold characterPairing
  rw [Nat.card_congr e.toEquiv]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ fun x => by simp [map_inv]

noncomputable abbrev transportCharacterBasis (e : A ≃* A')
    (basis : FiniteIrreducibleCharacterBasis A') : FiniteIrreducibleCharacterBasis A where
  index := basis.index
  representation θ := inflatedFiniteComplexRepresentation e.toMonoidHom (basis.representation θ)
  irreducible θ := inflated_isIrreducible e.toMonoidHom e.surjective _ (basis.irreducible θ)
  distinct := by
    intro θ θ' h
    apply basis.distinct
    funext y
    have hy := congrFun h (e.symm y)
    simpa [inflatedFiniteComplexRepresentation_character] using hy
  separates := by
    intro function hclass hpair
    have hzero : (fun y : A' => function (e.symm y)) = 0 := by
      apply basis.separates
      · intro y c
        simp only [map_mul, map_inv, hclass]
      · intro θ
        rw [← characterPairing_mulEquiv e]
        simp only [MulEquiv.symm_apply_apply]
        exact hpair θ
    funext x
    simpa using congrFun hzero (e x)

theorem transportCharacterBasis_character (e : A ≃* A')
    (basis : FiniteIrreducibleCharacterBasis A') (θ : basis.index) (x : A) :
    ((transportCharacterBasis e basis).representation θ).character x =
      (basis.representation θ).character (e x) := rfl

theorem transportCharacterBasis_projection (e : A ≃* A')
    (basis : FiniteIrreducibleCharacterBasis A') (support : Finset basis.index)
    (function : A → ℂ) (x : A) :
    characterSubsetProjection (transportCharacterBasis e basis) support function x =
      characterSubsetProjection basis support (fun y => function (e.symm y)) (e x) := by
  rw [characterSubsetProjection_apply', characterSubsetProjection_apply']
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [transportCharacterBasis_character]
  congr 1
  rw [← characterPairing_mulEquiv e]
  simp only [MulEquiv.symm_apply_apply]
  rfl

theorem transportCharacterBasis_admissible_iff (e : A ≃* A')
    (basis : FiniteIrreducibleCharacterBasis A') (ring : Subring ℂ)
    (support : Finset basis.index) :
    characterSubsetAdmissible (transportCharacterBasis e basis) ring support ↔
      characterSubsetAdmissible basis ring support := by
  have hcoeff : ∀ x : A, (characterSubsetIdempotent (transportCharacterBasis e basis) support).coeff
      x = (characterSubsetIdempotent basis support).coeff (e x) := by
    intro x
    rw [characterSubsetIdempotent_coeff, characterSubsetIdempotent_coeff,
      Nat.card_congr e.toEquiv]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [transportCharacterBasis_character, transportCharacterBasis_character, map_one, map_inv]
  change (∀ x : A, _ ∈ ring) ↔ (∀ y : A', _ ∈ ring)
  constructor
  · intro h y
    have hx := h (e.symm y)
    rwa [hcoeff, MulEquiv.apply_symm_apply] at hx
  · intro h x
    rw [hcoeff]
    exact h (e x)

theorem transportCharacterBasis_coefficientBlock (e : A ≃* A')
    (basis : FiniteIrreducibleCharacterBasis A') (ring : Subring ℂ) (θ : basis.index) :
    coefficientBlock (transportCharacterBasis e basis) ring θ = coefficientBlock basis ring θ := by
  ext θ'
  rw [coefficientBlock_mem_iff, coefficientBlock_mem_iff]
  change (∀ support, characterSubsetAdmissible (transportCharacterBasis e basis) ring support →
      (θ ∈ support ↔ θ' ∈ support)) ↔
    (∀ support, characterSubsetAdmissible basis ring support → (θ ∈ support ↔ θ' ∈ support))
  simp only [transportCharacterBasis_admissible_iff]

end Transport

section Formula

variable {G : Type u} [Group G] [Fintype G]

@[expose] def localCentralizerEquiv (H : Subgroup G) (u : H)
    (hEH : extendedCentralizer (u : G) ≤ H) :
    Subgroup.centralizer (Subgroup.zpowers u : Set H) ≃*
      Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) where
  toFun c := ⟨((c : H) : G), mem_centralizer_zpowers_of_commute
    ((commute_of_mem_centralizer_zpowers u c).map H.subtype)⟩
  invFun c := ⟨⟨c, hEH (centralizer_le_extendedCentralizer (u : G) (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_centralizer_zpowers (u : G) c).eq.symm))⟩,
    mem_centralizer_zpowers_of_commute
      (Subtype.ext (commute_of_mem_centralizer_zpowers (u : G) c).eq)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem unique_local_block_projection_section_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (H : Subgroup G) (u : H) (e : ℕ)
    (hu : orderOf (u : G) ∣ p ^ e) (hEH : extendedCentralizer (u : G) ≤ H)
    (basisH : FiniteIrreducibleCharacterBasis H)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)))
    (block : basis.index) (blockH : basisH.index) (localBlock : localBasis.index)
    (hgroup : IsPGroup p (Subgroup.zpowers (u : G))) (hgroupH : IsPGroup p (Subgroup.zpowers u))
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers (u : G)) hgroup
      (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers (u : G)) hgroup
        (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (hbrauerH : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroupH
      (Subgroup.centralizer (Subgroup.zpowers u : Set H)) le_rfl
      (Subgroup.centralizer_le_normalizer _)
      (transportCharacterBasis (localCentralizerEquiv H u hEH) localBasis) localBlock =
        centralCharacterResidueHom basisH ideal blockH)
    (huniqueH : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroupH
        (Subgroup.centralizer (Subgroup.zpowers u : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _)
        (transportCharacterBasis (localCentralizerEquiv H u hEH) localBasis) θ =
          centralCharacterResidueHom basisH ideal blockH →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (F : G → ℂ) (hF : ∀ x c : G, F (c * x * c⁻¹) = F x) (F' : H → ℂ)
    (hF' : ∀ y c : H, F' (c * y * c⁻¹) = F' y)
    (hagree : ∀ w : H, Commute u w → Nat.Coprime p (orderOf w) →
      F (((u * w)⁻¹ : H) : G) = F' (u * w)⁻¹)
    (r : H) (hr : (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G))
    (hrp : Nat.Coprime p (orderOf r)) :
    characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) block) F
        (((u * r)⁻¹ : H) : G) =
      characterSubsetProjection basisH
        (coefficientBlock basisH (localizedComplexIntegerRing ideal) blockH) F' (u * r)⁻¹ := by
  set ι := localCentralizerEquiv H u hEH with hι
  have huH : orderOf u ∣ p ^ e := by rwa [← Subgroup.orderOf_coe]
  have hrcomm : Commute (u : G) (r : G) := (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
  have hrcommH : Commute u r := Subtype.ext hrcomm.eq
  set rC : Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) :=
    ⟨(r : G), mem_centralizer_zpowers_of_commute hrcomm⟩ with hrC
  set rC' : Subgroup.centralizer (Subgroup.zpowers u : Set H) :=
    ⟨r, mem_centralizer_zpowers_of_commute hrcommH⟩ with hrC'
  have hreg : Nat.Coprime p (orderOf rC.val) := by
    change Nat.Coprime p (orderOf (r : G))
    rw [Subgroup.orderOf_coe]
    exact hrp
  have hreg' : Nat.Coprime p (orderOf rC'.val) := hrp
  have hG := unique_local_block_projection basis ideal p (u : G) e hu hgroup localBasis block
    localBlock hbrauer hunique rC hreg F hF
  have hblock := transportCharacterBasis_coefficientBlock ι localBasis
    (localizedComplexIntegerRing ideal) localBlock
  have huniqueH' : ∀ θ : (transportCharacterBasis ι localBasis).index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroupH
        (Subgroup.centralizer (Subgroup.zpowers u : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) (transportCharacterBasis ι localBasis) θ =
          centralCharacterResidueHom basisH ideal blockH →
        θ ∈ coefficientBlock (transportCharacterBasis ι localBasis)
          (localizedComplexIntegerRing ideal) localBlock := fun θ hθ => by
    rw [hblock]
    exact huniqueH θ hθ
  have hH := unique_local_block_projection basisH ideal p u e huH hgroupH
    (transportCharacterBasis ι localBasis) blockH localBlock hbrauerH huniqueH' rC' hreg' F' hF'
  rw [hblock] at hH
  set q : Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) :=
    ((⟨(u : G), element_mem_centralizer_zpowers (u : G)⟩ :
      Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)) * rC)⁻¹ with hq
  set q' : Subgroup.centralizer (Subgroup.zpowers u : Set H) :=
    ((⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set H)) * rC')⁻¹ with hq'
  have hqG : (q : G) = (((u * r)⁻¹ : H) : G) := rfl
  have hq'H : (q' : H) = (u * r)⁻¹ := rfl
  have hιq : ι q' = q := rfl
  set Q := inverseSection p (u : G) with hQ
  set fG : Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) → ℂ := fun m => F m.val
    with hfG
  set fH : Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) → ℂ :=
    fun m => F' (ι.symm m : Subgroup.centralizer (Subgroup.zpowers u : Set H)).val with hfH
  have hagreeC : ∀ m ∈ Q, fG m = fH m := by
    intro m hm
    have hmcomm : Commute (u : G) (m : G) := commute_of_mem_centralizer_zpowers (u : G) m
    have hmp : Nat.Coprime p (orderOf ((u : G) * (m : G))) := by
      have h := hm
      change Nat.Coprime p (orderOf (centralizerSelf (u : G) * m)) at h
      rwa [← Subgroup.orderOf_coe] at h
    have hmH : (m : G) ∈ H := (ι.symm m : Subgroup.centralizer (Subgroup.zpowers u : Set H)).val.2
    set w : H := (u * ⟨(m : G), hmH⟩)⁻¹ with hw
    have hwcomm : Commute u w := by
      apply Commute.inv_right
      apply Commute.mul_right (Commute.refl u)
      exact Subtype.ext hmcomm.eq
    have hwp : Nat.Coprime p (orderOf w) := by
      rw [hw, orderOf_inv, ← Subgroup.orderOf_coe]
      exact hmp
    have h := hagree w hwcomm hwp
    have hpoint : (u * w)⁻¹ = (⟨(m : G), hmH⟩ : H) := by
      apply Subtype.ext
      change ((u : G) * ((u : G) * (m : G))⁻¹)⁻¹ = (m : G)
      rw [mul_inv_rev, inv_inv, mul_inv_eq_iff_eq_mul]
      exact hmcomm.eq
    change F (m : G) = F' (ι.symm m : Subgroup.centralizer (Subgroup.zpowers u : Set H)).val
    have hsymm : ((ι.symm m : Subgroup.centralizer (Subgroup.zpowers u : Set H)) : H) =
        (⟨(m : G), hmH⟩ : H) := rfl
    rw [hsymm, ← hpoint, ← h, hpoint]
  have hmaskeq : characterFunctionMask Q fG = characterFunctionMask Q fH := by
    funext m
    unfold characterFunctionMask
    by_cases hm : m ∈ Q
    · rw [ite_eq_left hm, ite_eq_left hm, hagreeC m hm]
    · rw [ite_eq_right hm, ite_eq_right hm]
  have hsec := inverseSection_primeSectionUnion p (u : G) e hu
  have hm1 := congrFun (coefficientBlock_section_mask_commute localBasis ideal p localBlock Q hsec
    fG) q
  have hm2 := congrFun (coefficientBlock_section_mask_commute localBasis ideal p localBlock Q hsec
    fH) q
  have hqQ : q ∈ Q := inv_mem_inverseSection p (u : G) rC (by
    rw [Subgroup.orderOf_coe] at hreg
    exact hreg)
  rw [hmaskeq] at hm1
  have hmm := hm1.symm.trans hm2
  unfold characterFunctionMask at hmm
  rw [ite_eq_left hqQ, ite_eq_left hqQ] at hmm
  have htrans := transportCharacterBasis_projection ι localBasis
    (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (fun m' : Subgroup.centralizer (Subgroup.zpowers u : Set H) => F' m'.val) q'
  rw [hιq] at htrans
  calc characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) block) F
        (((u * r)⁻¹ : H) : G) =
      characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) block) F (q : G) := by
        rw [hqG]
    _ = characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock) fG q :=
        hG.symm
    _ = characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock) fH q := hmm
    _ = characterSubsetProjection (transportCharacterBasis ι localBasis)
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
        (fun m' : Subgroup.centralizer (Subgroup.zpowers u : Set H) => F' m'.val) q' :=
        htrans.symm
    _ = characterSubsetProjection basisH
        (coefficientBlock basisH (localizedComplexIntegerRing ideal) blockH) F' (q' : H) := hH
    _ = characterSubsetProjection basisH
        (coefficientBlock basisH (localizedComplexIntegerRing ideal) blockH) F' (u * r)⁻¹ := by
        rw [hq'H]

theorem extendedCentralizer_inv_le {K : Type*} [Group K] (x : K) :
    extendedCentralizer x⁻¹ ≤ extendedCentralizer x := by
  intro g hg
  change g⁻¹ * x⁻¹ * g = x⁻¹ ∨ g⁻¹ * x⁻¹ * g = x⁻¹⁻¹ at hg
  change g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x⁻¹
  have hconj : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
  rw [hconj, inv_inv] at hg
  rcases hg with hg | hg
  · exact Or.inl (inv_injective hg)
  · exact Or.inr (inv_eq_iff_eq_inv.mp hg)

theorem conj_classWeight (H : Subgroup G) (data : FiniteComplexRepresentation H) {a : G}
    (ha : a * a = 1) :
    starRingEnd ℂ (classWeight H data.character a) = classWeight H data.character a := by
  unfold classWeight
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · have hxx : x * x = 1 := classInter_mul_self H ha x (by
      simp only [classInter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx)
    exact involution_character_is_real data x (by rw [pow_two]; exact hxx)
  · exact map_zero _

theorem conj_weighted_character_sum {K : Type u} [Group K] [Fintype K]
    (basisK : FiniteIrreducibleCharacterBasis K) (support : Finset basisK.index)
    (w : basisK.index → ℂ) (hw : ∀ l, starRingEnd ℂ (w l) = w l) (y : K) :
    starRingEnd ℂ (∑ l ∈ support, w l * (basisK.representation l).character y /
        (basisK.representation l).character 1) =
      ∑ l ∈ support, w l * (basisK.representation l).character y⁻¹ /
        (basisK.representation l).character 1 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_div₀, map_mul, hw, finite_character_conjugate_inverse,
    involution_character_is_real _ 1 (one_pow 2)]

theorem brauer_order_formula_with_unique_local_block (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (H : Subgroup G) (u : H) (e : ℕ) (hu : orderOf (u : G) ∣ p ^ e)
    (hEH : extendedCentralizer (u : G) ≤ H) (basisH : FiniteIrreducibleCharacterBasis H)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)))
    (block : basis.index) (blockH : basisH.index) (localBlock : localBasis.index)
    (hgroup : IsPGroup p (Subgroup.zpowers (u : G))) (hgroupH : IsPGroup p (Subgroup.zpowers u))
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers (u : G)) hgroup
      (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers (u : G)) hgroup
        (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (hbrauerH : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroupH
      (Subgroup.centralizer (Subgroup.zpowers u : Set H)) le_rfl
      (Subgroup.centralizer_le_normalizer _)
      (transportCharacterBasis (localCentralizerEquiv H u hEH) localBasis) localBlock =
        centralCharacterResidueHom basisH ideal blockH)
    (huniqueH : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroupH
        (Subgroup.centralizer (Subgroup.zpowers u : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _)
        (transportCharacterBasis (localCentralizerEquiv H u hEH) localBasis) θ =
          centralCharacterResidueHom basisH ideal blockH →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock) :
    (∀ r : H, (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) → Nat.Coprime p (orderOf r) →
      (Nat.card G : ℂ) *
          ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
            (basis.representation label).character a * (basis.representation label).character b *
              (basis.representation label).character ((u * r : H) : G) /
                (basis.representation label).character 1 =
        (Nat.card H : ℂ) * Nat.card (Subgroup.centralizer ({a} : Set G)) *
            Nat.card (Subgroup.centralizer ({b} : Set G)) *
          ∑ label ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) blockH,
            classWeight H (basisH.representation label).character a *
              classWeight H (basisH.representation label).character b *
                (basisH.representation label).character (u * r) /
                  (basisH.representation label).character 1) ∧
    ∀ ℓ : ({r : H // (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
        Nat.Coprime p (orderOf r)} → ℂ) →ₗ[ℂ] ℂ,
      (Nat.card G : ℂ) *
          ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
            (basis.representation label).character a * (basis.representation label).character b *
              ℓ (fun r => (basis.representation label).character ((u * r.val : H) : G)) /
                (basis.representation label).character 1 =
        (Nat.card H : ℂ) * Nat.card (Subgroup.centralizer ({a} : Set G)) *
            Nat.card (Subgroup.centralizer ({b} : Set G)) *
          ∑ label ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) blockH,
            classWeight H (basisH.representation label).character a *
              classWeight H (basisH.representation label).character b *
                ℓ (fun r => (basisH.representation label).character (u * r.val)) /
                  (basisH.representation label).character 1 := by
  classical
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) block with hB
  set BH := coefficientBlock basisH (localizedComplexIntegerRing ideal) blockH with hBH
  set ca : ℂ := ((Nat.card (Subgroup.centralizer ({a} : Set G)) : ℕ) : ℂ) with hca
  set cb : ℂ := ((Nat.card (Subgroup.centralizer ({b} : Set G)) : ℕ) : ℂ) with hcb
  have hca0 : ca ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcb0 : cb ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set FG : G → ℂ := fun x => (productCount (conjClassFinset a) (conjClassFinset b) x : ℂ)
    with hFGdef
  set FH : H → ℂ := fun y => (productCount (classInter H a) (classInter H b) y : ℂ)
    with hFHdef
  set cG : basis.index → ℂ := fun l => (ca * cb)⁻¹ * Nat.card G *
    ((basis.representation l).character a * (basis.representation l).character b /
      (basis.representation l).character 1) with hcG
  set cH : basisH.index → ℂ := fun l => (Nat.card H : ℂ) *
    (classWeight H (basisH.representation l).character a *
      classWeight H (basisH.representation l).character b /
        (basisH.representation l).character 1) with hcH
  have hFG : FG = fun g => ∑ l, cG l * (basis.representation l).character g := by
    funext g
    have h := involution_classes_product_character_formula basis a b ha hb g
    have h' : FG g = (ca * cb)⁻¹ * ((Nat.card G : ℂ) * ∑ l, (basis.representation l).character a *
        (basis.representation l).character b * (basis.representation l).character g /
          (basis.representation l).character 1) := by
      rw [← h, ← hca, ← hcb]
      field_simp
      rfl
    rw [h', Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcG]
    ring
  have hFH : FH = fun y => ∑ l, cH l * (basisH.representation l).character y := by
    funext y
    change (productCount (classInter H a) (classInter H b) y : ℂ) = _
    rw [productCount_classInter H basisH ha hb y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcH]
    ring
  have hclassG : ∀ x c : G, FG (c * x * c⁻¹) = FG x := by
    intro x c
    rw [hFG]
    exact Finset.sum_congr rfl fun l _ => by
      rw [show (basis.representation l).character (c * x * c⁻¹) =
        (basis.representation l).character x from Representation.char_conj _ x c]
  have hclassH : ∀ y c : H, FH (c * y * c⁻¹) = FH y := by
    intro y c
    rw [hFH]
    exact Finset.sum_congr rfl fun l _ => by
      rw [show (basisH.representation l).character (c * y * c⁻¹) =
        (basisH.representation l).character y from Representation.char_conj _ y c]
  have hPG : ∀ y : G, ca * cb * characterSubsetProjection basis B FG y =
      Nat.card G * ∑ l ∈ B, (basis.representation l).character a *
        (basis.representation l).character b * (basis.representation l).character y /
          (basis.representation l).character 1 := by
    intro y
    rw [hFG, projection_basis_expansion, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcG]
    field_simp
  have hPH : ∀ y : H, characterSubsetProjection basisH BH FH y =
      Nat.card H * ∑ l ∈ BH, classWeight H (basisH.representation l).character a *
        classWeight H (basisH.representation l).character b *
          (basisH.representation l).character y /
            (basisH.representation l).character 1 := by
    intro y
    rw [hFH, projection_basis_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcH]
    ring
  have hkey : ∀ r : H, (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) →
      Nat.Coprime p (orderOf r) →
      characterSubsetProjection basis B FG (((u * r)⁻¹ : H) : G) =
        characterSubsetProjection basisH BH FH (u * r)⁻¹ := by
    intro r hr hrp
    refine unique_local_block_projection_section_eq basis ideal p H u e hu hEH basisH localBasis
      block blockH localBlock hgroup hgroupH hbrauer hunique hbrauerH huniqueH FG hclassG FH
      hclassH (fun w hw hwp => ?_) r hr hrp
    have hwG : Commute (u : G) (w : G) := hw.map H.subtype
    have hwpG : Nat.Coprime p (orderOf (w : G)) := by rw [Subgroup.orderOf_coe]; exact hwp
    obtain ⟨-, -, -, -, -, hext⟩ := involution_product_extended_centralizer_localization
      ((u * w : H) : G) (∅ : Finset G) (∅ : Finset G) (by simp) (by simp)
    have hle : extendedCentralizer (((u * w)⁻¹ : H) : G) ≤ H := by
      rw [Subgroup.coe_inv]
      exact (extendedCentralizer_inv_le _).trans ((hext p (u : G) (w : G) e hu hwG hwpG).trans hEH)
    change (productCount (conjClassFinset a) (conjClassFinset b) (((u * w)⁻¹ : H) : G) : ℂ) =
      (productCount (classInter H a) (classInter H b) (u * w)⁻¹ : ℂ)
    exact_mod_cast productCount_conjClassFinset_eq H ha hb (u * w)⁻¹ hle
  have hpoint : ∀ r : H, (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) →
      Nat.Coprime p (orderOf r) →
      (Nat.card G : ℂ) * ∑ l ∈ B, (basis.representation l).character a *
          (basis.representation l).character b *
            (basis.representation l).character ((u * r : H) : G) /
              (basis.representation l).character 1 =
        ca * cb * ((Nat.card H : ℂ) * ∑ l ∈ BH,
          classWeight H (basisH.representation l).character a *
            classWeight H (basisH.representation l).character b *
              (basisH.representation l).character (u * r) /
                (basisH.representation l).character 1) := by
    intro r hr hrp
    have h1 := hPG (((u * r)⁻¹ : H) : G)
    rw [hkey r hr hrp, hPH] at h1
    have hwG : ∀ l : basis.index, starRingEnd ℂ ((basis.representation l).character a *
        (basis.representation l).character b) =
        (basis.representation l).character a * (basis.representation l).character b := fun l => by
      rw [map_mul, involution_character_is_real _ a (by rw [pow_two]; exact ha),
        involution_character_is_real _ b (by rw [pow_two]; exact hb)]
    have hwH : ∀ l : basisH.index,
        starRingEnd ℂ (classWeight H (basisH.representation l).character a *
          classWeight H (basisH.representation l).character b) =
        classWeight H (basisH.representation l).character a *
          classWeight H (basisH.representation l).character b := fun l => by
      rw [map_mul, conj_classWeight H _ ha, conj_classWeight H _ hb]
    have hcaR : starRingEnd ℂ ca = ca := by rw [hca, map_natCast]
    have hcbR : starRingEnd ℂ cb = cb := by rw [hcb, map_natCast]
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [map_mul, map_mul, map_mul, map_mul, hcaR, hcbR, map_natCast, map_natCast,
      conj_weighted_character_sum basisH BH _ hwH, conj_weighted_character_sum basis B _ hwG,
      inv_inv, ← Subgroup.coe_inv, inv_inv] at h2
    exact h2.symm
  refine ⟨fun r hr hrp => ?_, fun ℓ => ?_⟩
  · rw [hpoint r hr hrp]
    ring
  · have hfun : (∑ l ∈ B, ((Nat.card G : ℂ) * ((basis.representation l).character a *
          (basis.representation l).character b / (basis.representation l).character 1)) •
          (fun r : {r : H // (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
            Nat.Coprime p (orderOf r)} =>
            (basis.representation l).character ((u * r.val : H) : G))) =
        ∑ l ∈ BH, ((Nat.card H : ℂ) * ca * cb *
          (classWeight H (basisH.representation l).character a *
            classWeight H (basisH.representation l).character b /
              (basisH.representation l).character 1)) •
          (fun r : {r : H // (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
            Nat.Coprime p (orderOf r)} =>
            (basisH.representation l).character (u * r.val)) := by
      funext r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hpoint r.val r.property.1 r.property.2
      calc ∑ l ∈ B, (Nat.card G : ℂ) * ((basis.representation l).character a *
            (basis.representation l).character b / (basis.representation l).character 1) *
            (basis.representation l).character ((u * r.val : H) : G) =
          (Nat.card G : ℂ) * ∑ l ∈ B, (basis.representation l).character a *
            (basis.representation l).character b *
              (basis.representation l).character ((u * r.val : H) : G) /
                (basis.representation l).character 1 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
        _ = ca * cb * ((Nat.card H : ℂ) * ∑ l ∈ BH,
            classWeight H (basisH.representation l).character a *
              classWeight H (basisH.representation l).character b *
                (basisH.representation l).character (u * r.val) /
                  (basisH.representation l).character 1) := h1
        _ = ∑ l ∈ BH, (Nat.card H : ℂ) * ca * cb *
            (classWeight H (basisH.representation l).character a *
              classWeight H (basisH.representation l).character b /
                (basisH.representation l).character 1) *
            (basisH.representation l).character (u * r.val) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
    have h := congrArg ℓ hfun
    rw [map_sum, map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    calc (Nat.card G : ℂ) * ∑ l ∈ B, (basis.representation l).character a *
          (basis.representation l).character b *
            ℓ (fun r => (basis.representation l).character ((u * r.val : H) : G)) /
              (basis.representation l).character 1 =
        ∑ l ∈ B, (Nat.card G : ℂ) * ((basis.representation l).character a *
          (basis.representation l).character b / (basis.representation l).character 1) *
            ℓ (fun r => (basis.representation l).character ((u * r.val : H) : G)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
      _ = _ := h
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring

end Formula

end CFSG.Wreathed
