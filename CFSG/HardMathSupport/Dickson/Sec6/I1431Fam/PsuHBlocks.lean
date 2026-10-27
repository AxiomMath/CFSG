module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslHb
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

section Abstract

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem t6psuh_finite_gl (hK : UnitaryFieldData ℓ f K) :
    Finite (LinearMap.GeneralLinearGroup K V) := by
  have := hK.finite
  have : Finite V := Module.finite_of_finite K
  have : Finite (Module.End K V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[K] V))
  exact Finite.of_injective _ Units.val_injective

theorem t6psuh_specialBlockFacts_of_mult_le_one (hq : 2 ≤ ℓ ^ f)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (hm : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1) : SpecialBlockFacts B x a := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
      (fun h2 => absurd hm (by omega))
  · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))

theorem t6psuh_isSolvable_orbitFactor_of_not_good (hq : 2 ≤ ℓ ^ f)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (ha : ¬ IsGoodBlock hK x a) : Group.IsSolvable ↥(orbitFactor B x (a : K[X])) := by
  have := t6psuh_finite_gl (V := V) hK
  by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
  · have hself : dualPoly hK.bar (a : K[X]) = a := by
      by_contra hne
      exact ha ⟨hm, fun h => absurd h hne⟩
    have hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
        ℓ ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
      by_contra hnot
      exact ha ⟨hm, fun _ => hnot⟩
    obtain ⟨h1, h2, h3⟩ := card_orbitFactor_exceptional H a hself
    apply isSolvable_of_card_primeFactors_le_two
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hbad
    rcases hbad with ⟨hm', hQ⟩ | ⟨hm', hQ⟩ | ⟨hm', hQ⟩
    · rw [h1 hm' hQ, show (18 : ℕ) = 2 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three,
        Nat.Prime.primeFactors Nat.prime_two]
      decide
    · rw [h2 hm' hQ, show (96 : ℕ) = 2 ^ 5 * 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      decide
    · rw [h3 hm' hQ, show (648 : ℕ) = 2 ^ 3 * 3 ^ 4 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide
  · have hm1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 := by omega
    have hS := (t6psuh_specialBlockFacts_of_mult_le_one hq H a hm1).abelian hm1
    exact Group.isSolvable_of_comm fun g g' => Subtype.ext (hS g g.2 g' g'.2).eq

theorem t6psuh_isSolvable_range_blockRestrict_of_not_good (hq : 2 ≤ ℓ ^ f)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (ha : ¬ IsGoodBlock hK x a) {G : Type*} [Group G] (φ : G →* gl_centralizer x)
    (hφ : ∀ g, (φ g : LinearMap.GeneralLinearGroup K V) ∈ unitaryCentralizer B x) :
    Group.IsSolvable ↥((blockRestrict x (a : K[X])).comp φ).range := by
  have hsolv := t6psuh_isSolvable_orbitFactor_of_not_good hq H a ha
  let κ : ↥(orbitFactor B x (a : K[X])) →* blockGL (x : Module.End K V) (a : K[X]) :=
    (blockRestrict x (a : K[X])).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)
  have hκ : Group.IsSolvable ↥κ.range :=
    Group.isSolvable_of_surjective (f := κ.rangeRestrict) κ.rangeRestrict_surjective
  have hle : ((blockRestrict x (a : K[X])).comp φ).range ≤ κ.range := by
    rintro _ ⟨g, rfl⟩
    have hO : ∀ b ∈ primaryFactors (x : Module.End K V),
        b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) →
          dualPoly hK.bar b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) := by
      intro b hb hbO
      rcases hbO with rfl | hbO
      · exact Or.inr rfl
      · rw [Set.mem_singleton_iff] at hbO
        subst hbO
        exact Or.inl (dualPoly_dualPoly_of_mem H a.2)
    obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO (hφ g)
    refine ⟨⟨gO, hgO⟩, ?_⟩
    refine blockGL_ext fun v hv => ?_
    change ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      ((φ g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
    exact hgOeq (a : K[X]) a.2 (Or.inl rfl) v hv
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem t6psuh_mem_iSup_specialBlock_of_blocks (H : UnitaryPrimaryData hK.bar B x)
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hdet : ∀ b : primaryFactors (x : Module.End K V),
      blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1)
    (hbad : ∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
      blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) :
    y ∈ ⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
      specialBlock B x (a.1 : K[X]) := by
  classical
  have hsq := H.squarefree
  set M := ⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
    specialBlock B x (a.1 : K[X]) with hM
  suffices key : ∀ F : Finset K[X], ∀ (y : LinearMap.GeneralLinearGroup K V)
      (hy : y ∈ unitaryCentralizer B x),
      (∀ b : primaryFactors (x : Module.End K V), blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
        blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (y : Module.End K V) v = v) → y ∈ M by
    exact key (primaryFactors (x : Module.End K V)) y hy hdet hbad fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro y hy _ _ h
    have : y = 1 := eq_one_of_forall_apply_eq hsq fun b hb v hv => h b hb (by simp) v hv
    rw [this]
    exact M.one_mem
  | insert b F hbF ih =>
    intro y hy hdet hbad h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · set O : Set K[X] := {b, dualPoly hK.bar b} with hOdef
      have hbO : b ∈ O := Or.inl rfl
      have hO : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O → dualPoly hK.bar c ∈ O := by
        intro c hc hcO
        rcases hcO with rfl | hcO
        · exact Or.inr rfl
        · rw [Set.mem_singleton_iff] at hcO
          subst hcO
          exact Or.inl (dualPoly_dualPoly_of_mem H hbΦ)
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO hy
      have hgOc : gO ∈ gl_centralizer x := hgO.1.2
      have hres : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∈ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = blockRestrict x (c : K[X]) ⟨y, hy.2⟩ :=
        fun c hc => blockGL_ext fun v hv => hgOeq c c.2 hc v hv
      have hres1 : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∉ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 :=
        fun c hc => blockGL_ext fun v hv => hgO.2 c c.2 hc v hv
      have hdetO : ∀ c : primaryFactors (x : Module.End K V),
          blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c
        by_cases hc : (c : K[X]) ∈ O
        · have : blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = blockDetHom x (c : K[X]) ⟨y, hy.2⟩ := by
            simp only [blockDetHom, MonoidHom.comp_apply]
            rw [hres c hc]
          rw [this]
          exact hdet c
        · simp only [blockDetHom, MonoidHom.comp_apply]
          rw [hres1 c hc, map_one]
      have hbadO : ∀ c : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x c →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c hcb
        by_cases hc : (c : K[X]) ∈ O
        · rw [hres c hc]
          exact hbad c hcb
        · exact hres1 c hc
      have hgOM : gO ∈ M := by
        by_cases hgood : IsGoodBlock hK x ⟨b, hbΦ⟩
        · refine Subgroup.mem_iSup_of_mem
            (⟨⟨b, hbΦ⟩, hgood⟩ : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a})
            (mem_specialBlock.mpr ⟨hgO, hgOc, hdetO ⟨b, hbΦ⟩⟩)
        · have h1 : gO = 1 := by
            refine eq_one_of_paired H hbΦ hgO fun v hv => ?_
            have := congrArg (fun γ : blockGL (x : Module.End K V) b => blockApply γ v hv)
              (hbadO ⟨b, hbΦ⟩ hgood)
            exact this
          rw [h1]
          exact M.one_mem
      have hy' : gO⁻¹ * y ∈ unitaryCentralizer B x := mul_mem (inv_mem hgO.1) hy
      have hdet' : ∀ c : primaryFactors (x : Module.End K V),
          blockDetHom x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hdetO c, hdet c, inv_one, mul_one]
      have hbad' : ∀ c : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x c →
          blockRestrict x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c hcb
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hbadO c hcb, hbad c hcb, inv_one, mul_one]
      have hinv : ∀ u, ((gO⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((gO : Module.End K V) u) = u := fun u => by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
        rfl
      have h' : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((gO⁻¹ * y : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        by_cases hcO : c ∈ O
        · rw [Units.val_mul, Module.End.mul_apply, ← hgOeq c hc hcO v hv, hinv]
        · have hgo : (gO : Module.End K V) v = v := hgO.2 c hc hcO v hv
          have hcb : c ∉ insert b F := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hcO (h ▸ hbO), hcF⟩
          rw [Units.val_mul, Module.End.mul_apply, h c hc hcb v hv, ← hgo, hinv, hgo]
      have hrest := ih _ hy' hdet' hbad' h'
      have hg_eq : y = gO * (gO⁻¹ * y) := by simp
      rw [hg_eq]
      exact M.mul_mem hgOM hrest
    · refine ih y hy hdet hbad fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbΦ (h ▸ hc), hcF⟩

end Abstract

section Concrete

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem t6psuh_squarefree_minpoly_toLin_of_pow_scalar {n p : ℕ} (hpK : (p : K) ≠ 0)
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((Matrix.GeneralLinearGroup.toLin a :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))) := by
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C (c : K))
    (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree ?_
  have h1 : ((Matrix.GeneralLinearGroup.toLin a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val,
    hap]
  ext v i
  by_cases hi : i = v <;> simp [hi]

theorem t6psuh_primaryData_toLin' {n : ℕ} (h : UnitaryFieldData ℓ f K) {P : GL (Fin n) K}
    (hP : P ∈ primeFormUnitary h (idGram K n)) {c : Kˣ} {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hap : P ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P) := by
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have hsq := t6psuh_squarefree_minpoly_toLin_of_pow_scalar hpK hap
  have hX : ((Matrix.GeneralLinearGroup.toLin P : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  refine ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n,
    (toLin_mem_sesqUnitaryGroup_iff P).mpr hP, ?_⟩
  rw [hX]
  exact hsq

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

@[expose] noncomputable def t6psuh_toLinSU :
    ↥(gramSU h (idGram K n)) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
    ).toMonoidHom.comp (gramSU h (idGram K n)).subtype

variable {h n}

theorem t6psuh_toLinSU_apply (g : ↥(gramSU h (idGram K n))) :
    t6psuh_toLinSU h n g = Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) := rfl

theorem t6psuh_toLinSU_injective : Function.Injective (t6psuh_toLinSU h n) := fun _ _ e =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)

theorem t6psuh_toLinSU_mem_sesqSpecialUnitaryGroup (g : ↥(gramSU h (idGram K n))) :
    t6psuh_toLinSU h n g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (g : GL (Fin n) K)).mpr g.2

theorem t6psuh_mem_range_toLinSU {g' : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg' : g' ∈ sesqSpecialUnitaryGroup (idForm h n)) : g' ∈ (t6psuh_toLinSU h n).range := by
  have hmem : Matrix.GeneralLinearGroup.toLin.symm g' ∈ gramSU h (idGram K n) := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n), MulEquiv.apply_symm_apply]
    exact hg'
  exact ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g', hmem⟩, by
    show Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g') = g'
    exact MulEquiv.apply_symm_apply _ _⟩

theorem t6psuh_mem_centralizer_iff (a g : ↥(gramSU h (idGram K n))) :
    g ∈ Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n))) ↔
      t6psuh_toLinSU h n g ∈ gl_centralizer (t6psuh_toLinSU h n a) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul]
  exact (t6psuh_toLinSU_injective (h := h) (n := n)).eq_iff.symm

theorem t6psuh_toLinSU_mem_unitaryCentralizer (a : ↥(gramSU h (idGram K n)))
    {g : ↥(gramSU h (idGram K n))}
    (hg : g ∈ Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n)))) :
    t6psuh_toLinSU h n g ∈ unitaryCentralizer (idForm h n) (t6psuh_toLinSU h n a) :=
  Subgroup.mem_inf.mpr ⟨sesqSpecialUnitaryGroup_le _ (t6psuh_toLinSU_mem_sesqSpecialUnitaryGroup g),
    (t6psuh_mem_centralizer_iff a g).mp hg⟩

theorem t6psuh_primaryData (hℓ3 : ℓ ≠ 3) (a : ↥(gramSU h (idGram K n))) (ha3 : a ^ 3 = 1) :
    UnitaryPrimaryData h.bar (idForm h n) (t6psuh_toLinSU h n a) := by
  have hap : (a : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [map_one, ← Subgroup.coe_pow, ha3, Subgroup.coe_one]
  exact t6psuh_primaryData_toLin' h a.2.1 Nat.prime_three (Ne.symm hℓ3) hap

variable (h n) in
abbrev PsuIdx (a : ↥(gramSU h (idGram K n))) : Type :=
  {b : primaryFactors ((t6psuh_toLinSU h n a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) // IsGoodBlock h (t6psuh_toLinSU h n a) b}

variable (h n) in
@[expose] noncomputable def psuBlock (a : ↥(gramSU h (idGram K n))) (i : PsuIdx h n a) :
    Subgroup ↥(gramSU h (idGram K n)) :=
  (specialBlock (idForm h n) (t6psuh_toLinSU h n a) (i.1 : K[X])).comap (t6psuh_toLinSU h n)

theorem t6psuh_hq (h : UnitaryFieldData ℓ f K) : 2 ≤ ℓ ^ f := by
  have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
  omega

theorem t6psuh_specialBlock_le_range (hℓ3 : ℓ ≠ 3) (a : ↥(gramSU h (idGram K n)))
    (ha3 : a ^ 3 = 1) (i : PsuIdx h n a) :
    specialBlock (idForm h n) (t6psuh_toLinSU h n a) (i.1 : K[X]) ≤ (t6psuh_toLinSU h n).range :=
  fun _ hg => t6psuh_mem_range_toLinSU
    (specialBlock_le_sesqSpecialUnitaryGroup_of_good (t6psuh_primaryData hℓ3 a ha3) (t6psuh_hq h)
      i.1 i.2 hg)

theorem t6psuh_map_psuBlock (hℓ3 : ℓ ≠ 3) (a : ↥(gramSU h (idGram K n))) (ha3 : a ^ 3 = 1)
    (i : PsuIdx h n a) :
    (psuBlock h n a i).map (t6psuh_toLinSU h n) =
      specialBlock (idForm h n) (t6psuh_toLinSU h n a) (i.1 : K[X]) :=
  Subgroup.map_comap_eq_self (t6psuh_specialBlock_le_range hℓ3 a ha3 i)

theorem psuBlock_le_centralizer (a : ↥(gramSU h (idGram K n))) (i : PsuIdx h n a) :
    psuBlock h n a i ≤ Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n))) := fun g hg =>
  (t6psuh_mem_centralizer_iff a g).mpr
    (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2

theorem psuBlock_normal (a : ↥(gramSU h (idGram K n))) (i : PsuIdx h n a) :
    ∀ c ∈ Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n))), ∀ m ∈ psuBlock h n a i,
      c * m * c⁻¹ ∈ psuBlock h n a i := by
  intro c hc g hg
  have hcU := t6psuh_toLinSU_mem_unitaryCentralizer a hc
  have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
  rw [psuBlock, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact this

theorem isQuasisimple_psuBlock (hℓ3 : ℓ ≠ 3) (a : ↥(gramSU h (idGram K n))) (ha3 : a ^ 3 = 1)
    (i : PsuIdx h n a) : CFSG.IsQuasisimple (psuBlock h n a i) := by
  have e : ↥(psuBlock h n a i) ≃*
      ↥(specialBlock (idForm h n) (t6psuh_toLinSU h n a) (i.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (psuBlock h n a i) (t6psuh_toLinSU h n)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psuh_map_psuBlock hℓ3 a ha3 i))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    ((specialBlockFacts_of_good (t6psuh_primaryData hℓ3 a ha3) (t6psuh_hq h) i.1 i.2).quasisimple
      i.2.1)

theorem t6psuh_derived (hℓ3 : ℓ ≠ 3) (a : ↥(gramSU h (idGram K n))) (ha3 : a ^ 3 = 1) :
    ∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n)))) k,
      (g : ↥(gramSU h (idGram K n))) ∈ ⨆ i : PsuIdx h n a, psuBlock h n a i := by
  classical
  have H := t6psuh_primaryData hℓ3 a ha3
  have hq := t6psuh_hq h
  set x := t6psuh_toLinSU h n a with hx
  set C := Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n))) with hC
  let φ : ↥C →* gl_centralizer x :=
    ((t6psuh_toLinSU h n).comp C.subtype).codRestrict (gl_centralizer x) fun g =>
      (t6psuh_mem_centralizer_iff a g.1).mp g.2
  have hφU : ∀ g, (φ g : LinearMap.GeneralLinearGroup K (Fin n → K)) ∈
      unitaryCentralizer (idForm h n) x := fun g => t6psuh_toLinSU_mem_unitaryCentralizer a g.2
  let ρ : (b : {b : primaryFactors (x : Module.End K (Fin n → K)) // ¬ IsGoodBlock h x b}) →
      ↥C →* blockGL (x : Module.End K (Fin n → K)) (b.1 : K[X]) :=
    fun b => (blockRestrict x (b.1 : K[X])).comp φ
  haveI : ∀ b, Group.IsSolvable ↥(ρ b).range := fun b =>
    t6psuh_isSolvable_range_blockRestrict_of_not_good hq H b.1 b.2 φ hφU
  haveI : Group.IsSolvable ((b : {b : primaryFactors (x : Module.End K (Fin n → K)) //
      ¬ IsGoodBlock h x b}) → ↥(ρ b).range) := t6psl_isSolvable_pi
  haveI : Group.IsSolvable ((b : primaryFactors (x : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  let ψ : ↥C →* ((b : primaryFactors (x : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) × ((b : {b : primaryFactors (x : Module.End K (Fin n → K)) //
      ¬ IsGoodBlock h x b}) → ↥(ρ b).range) :=
    MonoidHom.prod (MonoidHom.pi fun b => (blockDetHom x (b : K[X])).comp φ)
      (MonoidHom.pi fun b => (ρ b).rangeRestrict)
  have hSBle : ∀ a' : {a' : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a'},
      specialBlock (idForm h n) x (a'.1 : K[X]) ≤ (t6psuh_toLinSU h n).range := fun a' =>
    t6psuh_specialBlock_le_range hℓ3 a ha3 a'
  have hker : ∀ g : ↥C, ψ g = 1 → (g : ↥(gramSU h (idGram K n))) ∈
      ⨆ i : PsuIdx h n a, psuBlock h n a i := by
    intro g hg
    have hy := hφU g
    have hdet : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
        blockDetHom x (b : K[X]) ⟨t6psuh_toLinSU h n g, hy.2⟩ = 1 := fun b =>
      congrFun (congrArg Prod.fst hg) b
    have hbad : ∀ b : primaryFactors (x : Module.End K (Fin n → K)), ¬ IsGoodBlock h x b →
        blockRestrict x (b : K[X]) ⟨t6psuh_toLinSU h n g, hy.2⟩ = 1 := fun b hb =>
      congrArg Subtype.val (congrFun (congrArg Prod.snd hg) ⟨b, hb⟩)
    have hmem := t6psuh_mem_iSup_specialBlock_of_blocks H hy hdet hbad
    have hmapsup : (⨆ i : PsuIdx h n a, psuBlock h n a i).map (t6psuh_toLinSU h n) =
        ⨆ a' : {a' : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a'},
          specialBlock (idForm h n) x (a'.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => t6psuh_map_psuBlock hℓ3 a ha3 i
    have hk : t6psuh_toLinSU h n g ∈ (⨆ i : PsuIdx h n a, psuBlock h n a i).map
        (t6psuh_toLinSU h n) := by
      rw [hmapsup]
      exact hmem
    obtain ⟨s, hs, hs'⟩ := hk
    have : s = g := t6psuh_toLinSU_injective hs'
    rw [← this]
    exact hs
  obtain ⟨k, hk⟩ := t6psl_derived_le_ker ψ
  exact ⟨k, fun g hg => hker g (MonoidHom.mem_ker.1 (hk hg))⟩

end Concrete

end CFSG.HardMathSupport.Dickson.Sec6.I1431
