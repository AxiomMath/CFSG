module

public import CFSG.RankThree.PartOne.FOC.PSUSetup
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.RankThree.PartOne.FOC.ComponentFact
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem two_le_pow (h : UnitaryFieldData ℓ f K) : 2 ≤ ℓ ^ f :=
  h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) ℓ)

theorem not_isSolvable_of_perfect_ne_bot {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) (hne : H ≠ ⊥) : ¬ Group.IsSolvable H := by
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  exact Group.IsPerfect.not_isSolvable H

theorem not_isSolvable_autFix_of_quasisimple (y : primeFormUnitary h (idGram K n))
    (Q : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)))
    (hQc : Q ≤ unitaryCentralizer (idForm h n) (toLinU h n y))
    (hQd : ∀ g ∈ Q, LinearMap.det (g : Module.End K (Fin n → K)) = 1)
    (hQ : CFSG.IsQuasisimple ↥Q) :
    ¬ Group.IsSolvable (autFix (primeFormConjHom h (idGram K n) y)) := by
  classical
  have hrange : Q ≤ (phiS h (n := n)).range := by
    intro g hg
    exact mem_range_phiS (mem_sesqSpecialUnitaryGroup.mpr
      ⟨(mem_unitaryCentralizer.mp (hQc hg)).1, hQd g hg⟩)
  set Bq : Subgroup ↥(gramSU h (idGram K n)) := Q.comap (phiS h) with hBq
  have hmap : Bq.map (phiS h) = Q := Subgroup.map_comap_eq_self hrange
  have hBqq : CFSG.IsQuasisimple ↥Bq := by
    have e : ↥Bq ≃* ↥Q := (Subgroup.equivMapOfInjective Bq (phiS h) phiS_injective).trans
      (MulEquiv.subgroupCongr hmap)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  let π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h (idGram K n)) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hg' : g ∈ normOneScalars h (gramSU h (idGram K n)) n := by
      have := hg
      rwa [show π.ker = normOneScalars h (gramSU h (idGram K n)) n from
        QuotientGroup.ker_mk' _] at this
    obtain ⟨c, -, -, hc⟩ := hg'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (GeneralLinearGroup.scalar_commute c _).symm
  set R : Subgroup (primeFormP h (idGram K n)) := Bq.map π with hR
  have hfix : R ≤ autFix (primeFormConjHom h (idGram K n) y) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_autFix]
    change primeFormConjHom h (idGram K n) y (g : primeFormP h (idGram K n)) =
      (g : primeFormP h (idGram K n))
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    have hcomm := (mem_unitaryCentralizer.mp (hQc (show phiS h g ∈ Q from hg))).2
    have hc : (y : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * y := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul]
      exact Units.ext hcomm.eq.symm
    change (y : GL (Fin n) K) * g * (y : GL (Fin n) K)⁻¹ = g
    rw [hc, mul_inv_cancel_right]
  have hperf : Group.IsPerfect R := by
    have h1 : ⁅Bq, Bq⁆ = Bq := commutator_eq_of_isPerfect hBqq.1
    have h2 : ⁅R, R⁆ = R := by rw [hR, ← Subgroup.map_commutator, h1]
    exact Subgroup.isPerfect_iff.2 h2
  have hne : R ≠ ⊥ := by
    intro hR0
    have hle : Bq ≤ π.ker := by
      intro g hg
      have : π g ∈ R := ⟨g, hg, rfl⟩
      rw [hR0] at this
      exact this
    exact not_le_center_of_isQuasisimple hBqq (hle.trans hker)
  intro hs
  have hs' : Group.IsSolvable R :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hfix)
      (Subgroup.inclusion_injective hfix)
  exact not_isSolvable_of_perfect_ne_bot hperf hne hs'

section Block

variable (y : primeFormUnitary h (idGram K n))

theorem squarefree_minpoly_toLinU_of_pow_scalar {p : ℕ} (hpK : (p : K) ≠ 0) {c : Kˣ}
    (hyp : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) := by
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  rw [hX]
  exact squarefree_minpoly_toLin'_of_pow_scalar hpK hyp

theorem primaryData_toLinU
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))) :
    UnitaryPrimaryData h.bar (idForm h n) (toLinU h n y) :=
  ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem y, hx⟩

variable {y}

theorem not_isSolvable_autFix_of_good_block
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))))
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toLinU h n y) a) :
    ¬ Group.IsSolvable (autFix (primeFormConjHom h (idGram K n) y)) := by
  have HU := primaryData_toLinU y hx
  have hF := specialBlockFacts_of_good HU (two_le_pow h) a ha
  exact not_isSolvable_autFix_of_quasisimple y
    (specialBlock (idForm h n) (toLinU h n y) (a : K[X])) specialBlock_le_unitaryCentralizer
    hF.detK (hF.quasisimple ha.1)

theorem isGoodBlock_of_numeric'
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (hm : 2 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]))
    (h2 : primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) = 2 → 4 ≤ ℓ ^ (f * (a : K[X]).natDegree))
    (h3 : primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) = 3 → 3 ≤ ℓ ^ (f * (a : K[X]).natDegree)) :
    IsGoodBlock h (toLinU h n y) a := by
  refine ⟨hm, fun _ => ?_⟩
  generalize primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) = m at hm h2 h3 ⊢
  generalize ℓ ^ (f * (a : K[X]).natDegree) = Q at h2 h3 ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
  refine ⟨fun ⟨e1, e2⟩ => ?_, fun ⟨e1, e2⟩ => ?_, fun ⟨e1, e2⟩ => ?_⟩
  · have := h2 e1; omega
  · have := h2 e1; omega
  · have := h3 e1; omega

theorem isGoodBlock_of_numeric
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (hm : 2 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]))
    (h2 : primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) = 2 → 4 ≤ ℓ ^ f)
    (h3 : primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) = 3 → 3 ≤ ℓ ^ f) :
    IsGoodBlock h (toLinU h n y) a :=
  isGoodBlock_of_numeric' a hm (fun e => (h2 e).trans (le_pow_natDegree h a))
    (fun e => (h3 e).trans (le_pow_natDegree h a))

theorem not_isSolvable_autFix_of_mult_four
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))))
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : 4 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X])) :
    ¬ Group.IsSolvable (autFix (primeFormConjHom h (idGram K n) y)) :=
  not_isSolvable_autFix_of_good_block hx a
    (isGoodBlock_of_numeric a (by omega) (fun e => by omega) (fun e => by omega))

theorem not_isSolvable_autFix_of_mult_two (hq : 4 ≤ ℓ ^ f)
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))))
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : 2 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X])) :
    ¬ Group.IsSolvable (autFix (primeFormConjHom h (idGram K n) y)) :=
  not_isSolvable_autFix_of_good_block hx a
    (isGoodBlock_of_numeric a ha (fun _ => hq) (fun _ => by omega))

end Block

section Commutative

universe u

theorem commute_of_mult_le_one {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : LinearMap.GeneralLinearGroup K V} (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (hm : ∀ a : primaryFactors (x : Module.End K V),
      primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1)
    {Y b : LinearMap.GeneralLinearGroup K V} (hY : Y ∈ gl_centralizer x)
    (hb : b ∈ gl_centralizer x) : Commute Y b := by
  have hYc : Commute (Y : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hY
  have hbc : Commute (b : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hb
  refine Units.ext (ext_primaryComponent hsq fun c hc v hv => ?_)
  change (Y : Module.End K V) ((b : Module.End K V) v) =
    (b : Module.End K V) ((Y : Module.End K V) v)
  have : Fact (Irreducible c) := ⟨irreducible_of_mem_primaryFactors hc⟩
  have hYr : (Y : Module.End K V) ∈ commutant (x : Module.End K V) := (mem_commutant _).mpr hYc
  have hbr : (b : Module.End K V) ∈ commutant (x : Module.End K V) := (mem_commutant _).mpr hbc
  have hcomm := End_commute_of_finrank_le_one (E := AdjoinRoot c)
    (W := primaryComponent (x : Module.End K V) c) (hm ⟨c, hc⟩)
    (commutantRestrict c ⟨Y, hYr⟩) (commutantRestrict c ⟨b, hbr⟩)
  exact congrArg (fun T : Module.End (AdjoinRoot c) (primaryComponent (x : Module.End K V) c) =>
    ((T ⟨v, hv⟩ : primaryComponent (x : Module.End K V) c) : V)) hcomm.eq

variable {y : primeFormUnitary h (idGram K n)}

theorem toLinU_mem_gl_centralizer {A : primeFormUnitary h (idGram K n)}
    (hA : A ∈ Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))) :
    toLinU h n A ∈ gl_centralizer (toLinU h n y) := by
  rw [mem_gl_centralizer]
  have h1 : A * y = y * A := Subgroup.mem_centralizer_singleton_iff.mp hA
  have := congrArg (toLinU h n) h1
  rw [map_mul, map_mul] at this
  exact congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (g : Module.End K (Fin n → K))) this

theorem centralizer_commute_of_mult_le_one
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))))
    (hm : ∀ a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)),
      primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (a : K[X]) ≤ 1)
    {A B : primeFormUnitary h (idGram K n)}
    (hA : A ∈ Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))))
    (hB : B ∈ Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))) :
    A * B = B * A := by
  have hc := commute_of_mult_le_one hx hm (toLinU_mem_gl_centralizer hA)
    (toLinU_mem_gl_centralizer hB)
  exact toLinU_injective (by rw [map_mul, map_mul]; exact hc.eq)

theorem autFix_not_isSolvable_or_centralizer_commute (hq : 4 ≤ ℓ ^ f)
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))) :
    ¬ Group.IsSolvable (autFix (primeFormConjHom h (idGram K n) y)) ∨
      ∀ A ∈ Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))),
        ∀ B ∈ Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))), A * B = B * A := by
  by_cases hex : ∃ a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)),
      2 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (a : K[X])
  · obtain ⟨a, ha⟩ := hex
    exact Or.inl (not_isSolvable_autFix_of_mult_two hq hx a ha)
  · push Not at hex
    exact Or.inr fun A hA B hB =>
      centralizer_commute_of_mult_le_one hx (fun a => by have := hex a; omega) hA hB

end Commutative

section CaseII

universe u

theorem natDegree_mul_mult_eq {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : Module.End K V} {a : K[X]} (hmin : minpoly K x = a) (hirr : Irreducible a)
    (b : primaryFactors x) :
    (b : K[X]) = a ∧
      a.natDegree * primaryMultiplicity x (b : K[X]) = Module.finrank K V := by
  have hba : (b : K[X]) = a := by
    obtain ⟨hbi, hbm, hbd⟩ := mem_primaryFactors.mp b.2
    rw [hmin] at hbd
    exact eq_of_monic_of_associated hbm (by
      have := minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) x)
      rwa [hmin] at this) (hbi.associated_of_dvd hirr hbd)
  refine ⟨hba, ?_⟩
  have htop : primaryComponent x (b : K[X]) = ⊤ := by
    rw [primaryComponent, hba, ← hmin, minpoly.aeval]
    exact LinearMap.ker_zero
  have h1 := finrank_primaryComponent (x := x) (a := (b : K[X]))
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofTop _ htop)] at h1
  have hd : (b : K[X]).natDegree = a.natDegree := by rw [hba]
  rw [hd] at h1
  exact h1.symm

variable {y : primeFormUnitary h (idGram K n)}

theorem minpoly_eq_of_pow_scalar_irreducible [Nonempty (Fin n)] {p : ℕ} (hp : p.Prime) {c : Kˣ}
    (hc : ∀ b : K, b ^ p ≠ (c : K)) {y : GL (Fin n) K}
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    minpoly K (Matrix.toLin' (y : Matrix (Fin n) (Fin n) K)) = X ^ p - C (c : K) := by
  have hirr : Irreducible (X ^ p - C (c : K)) := X_pow_sub_C_irreducible_of_prime hp hc
  have hMp : (y : Matrix (Fin n) (Fin n) K) ^ p =
      algebraMap K (Matrix (Fin n) (Fin n) K) (c : K) := by
    have h1 : ((y ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (y : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hyp, GeneralLinearGroup.coe_scalar]
    rfl
  have haeval : aeval (Matrix.toLin' (y : Matrix (Fin n) (Fin n) K)) (X ^ p - C (c : K)) = 0 := by
    have hX : Matrix.toLin' (y : Matrix (Fin n) (Fin n) K) =
        Matrix.toLinAlgEquiv' (y : Matrix (Fin n) (Fin n) K) :=
      (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
    rw [hX]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval (monic_X_pow_sub_C _ hp.ne_zero)).symm

theorem cast_ne_zero_of_ne_char (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpℓ : p ≠ ℓ) : (p : K) ≠ 0 := by
  have := h.finite
  have : CharP K ℓ := h.charP
  intro h0
  have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm

theorem not_isSolvable_autFix_of_scalar_pow_irreducible {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) {c : Kˣ} (hc : ∀ b : K, b ^ p ≠ (c : K))
    (hyp : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c) (hn : 2 * p ≤ n) :
    ¬ Group.IsSolvable (autFix (primeFormConjHom h (idGram K n) y)) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have := h.finite
  have hpK := cast_ne_zero_of_ne_char h hp hpℓ
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y hpK hyp
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  have hmin : minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = X ^ p - C (c : K) := by
    rw [hX]
    exact minpoly_eq_of_pow_scalar_irreducible hp hc hyp
  have hirr : Irreducible (X ^ p - C (c : K)) := X_pow_sub_C_irreducible_of_prime hp hc
  have hmem : (X ^ p - C (c : K)) ∈ primaryFactors ((toLinU h n y :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) :=
    mem_primaryFactors.mpr ⟨hirr, monic_X_pow_sub_C _ hp.ne_zero, by rw [hmin]⟩
  let a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) := ⟨_, hmem⟩
  obtain ⟨-, hdim⟩ := natDegree_mul_mult_eq hmin hirr a
  rw [natDegree_X_pow_sub_C, Module.finrank_fin_fun] at hdim
  have hm : 2 ≤ primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) := by
    by_contra hlt
    push Not at hlt
    have : p * primaryMultiplicity ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (a : K[X]) ≤ p * 1 := Nat.mul_le_mul_left p (by omega)
    omega
  have hQ : 8 ≤ ℓ ^ (f * (a : K[X]).natDegree) := by
    have hd : (a : K[X]).natDegree = p := natDegree_X_pow_sub_C
    rw [hd]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (f * p) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [h.one_le])
      _ ≤ ℓ ^ (f * p) := Nat.pow_le_pow_left h.prime.two_le _
  exact not_isSolvable_autFix_of_good_block hx a
    (isGoodBlock_of_numeric' a hm (fun _ => by omega) (fun _ => by omega))

theorem exists_smul_id_of_finrank_le_one {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [Module.Finite E W] (hW : Module.finrank E W ≤ 1) (γ : Module.End E W) : ∃ t : E, γ = t • LinearMap.id := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hW
  obtain ⟨t, ht⟩ := hv (γ v)
  refine ⟨t, LinearMap.ext fun w => ?_⟩
  obtain ⟨s, rfl⟩ := hv w
  simp only [map_smul, ← ht, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]

theorem isCyclic_centralizer_of_scalar_pow_irreducible [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {c : Kˣ} (hc : ∀ b : K, b ^ p ≠ (c : K)) {y : GL (Fin n) K}
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) (hn : n = p) :
    IsCyclic (Subgroup.centralizer ({y} : Set (GL (Fin n) K))) := by
  have : Nonempty (Fin n) := ⟨⟨0, by have := hp.pos; omega⟩⟩
  let x : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin y
  have hX : (x : Module.End K (Fin n → K)) =
      Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  have hsq : Squarefree (minpoly K (x : Module.End K (Fin n → K))) := by
    rw [hX]
    exact squarefree_minpoly_toLin'_of_pow_scalar hpK hyp
  have hmin : minpoly K (x : Module.End K (Fin n → K)) = X ^ p - C (c : K) := by
    rw [hX]
    exact minpoly_eq_of_pow_scalar_irreducible hp hc hyp
  have hirr : Irreducible (X ^ p - C (c : K)) := X_pow_sub_C_irreducible_of_prime hp hc
  have hmem : (X ^ p - C (c : K)) ∈ primaryFactors (x : Module.End K (Fin n → K)) :=
    mem_primaryFactors.mpr ⟨hirr, monic_X_pow_sub_C _ hp.ne_zero, by rw [hmin]⟩
  let a : primaryFactors (x : Module.End K (Fin n → K)) := ⟨_, hmem⟩
  have hfact : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  obtain ⟨-, hdim⟩ := natDegree_mul_mult_eq hmin hirr a
  rw [natDegree_X_pow_sub_C, Module.finrank_fin_fun] at hdim
  have hm1 : primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) = 1 := by
    have := hp.pos
    have h1 : p * primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) = p * 1 := by
      rw [hdim, hn, mul_one]
    exact Nat.eq_of_mul_eq_mul_left this h1
  have hcomm : ∀ g ∈ Subgroup.centralizer ({y} : Set (GL (Fin n) K)),
      Matrix.GeneralLinearGroup.toLin g ∈ gl_centralizer x := by
    intro g hg
    rw [mem_gl_centralizer]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
    have := congrArg (Matrix.GeneralLinearGroup.toLin :
      GL (Fin n) K → LinearMap.GeneralLinearGroup K (Fin n → K)) h1
    simp only [map_mul] at this
    exact congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) this
  let ι : Subgroup.centralizer ({y} : Set (GL (Fin n) K)) →* gl_centralizer x :=
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
      (Subgroup.centralizer ({y} : Set (GL (Fin n) K))).subtype).codRestrict _
      (fun g => hcomm g g.2)
  let ρ : Subgroup.centralizer ({y} : Set (GL (Fin n) K)) →* AdjoinRoot (a : K[X]) :=
    (Units.coeHom (AdjoinRoot (a : K[X]))).comp ((blockDetHom x (a : K[X])).comp ι)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg1 : blockDetHom x (a : K[X]) (ι g) = 1 := Units.ext hg
    obtain ⟨t, ht⟩ := exists_smul_id_of_finrank_le_one (E := AdjoinRoot (a : K[X]))
      (W := primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])) hm1.le
      ((blockRestrict x (a : K[X]) (ι g) :
        blockGL (x : Module.End K (Fin n → K)) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K (Fin n → K)) a))
    have hdet : LinearMap.det ((blockRestrict x (a : K[X]) (ι g) :
        blockGL (x : Module.End K (Fin n → K)) (a : K[X])) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K (Fin n → K)) a))
        = 1 := congrArg Units.val hg1
    rw [ht, LinearMap.det_smul, LinearMap.det_id, mul_one,
      show Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])) = 1 from hm1, pow_one] at hdet
    subst hdet
    have hall : ∀ b ∈ primaryFactors (x : Module.End K (Fin n → K)),
        ∀ v ∈ primaryComponent (x : Module.End K (Fin n → K)) b,
          ((ι g : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v = v := by
      intro b hb v hv
      obtain ⟨hba, -⟩ := natDegree_mul_mult_eq hmin hirr ⟨b, hb⟩
      have hv' : v ∈ primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]) := by
        have e : b = (a : K[X]) := hba.trans rfl
        exact e ▸ hv
      have := blockApply_blockRestrict x (a : K[X]) (ι g) v hv'
      rw [← this]
      simp only [blockApply, ht, LinearMap.id_apply, one_smul]
    have h1 : (ι g : LinearMap.GeneralLinearGroup K (Fin n → K)) = 1 :=
      eq_one_of_forall_apply_eq hsq hall
    have h2 : Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) = 1 := h1
    exact Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective (h2.trans
      (map_one Matrix.GeneralLinearGroup.toLin).symm))
  exact isCyclic_of_injective_ringHom ρ hinj

theorem isCyclic_centralizer_unitary_of_scalar_pow_irreducible {p : ℕ} (hp : p.Prime)
    (hpℓ : p ≠ ℓ) {c : Kˣ} (hc : ∀ b : K, b ^ p ≠ (c : K))
    (hyp : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c) (hn : n = p) :
    IsCyclic (Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))) := by
  have := h.finite
  have hcyc := isCyclic_centralizer_of_scalar_pow_irreducible hp (cast_ne_zero_of_ne_char h hp hpℓ)
    hc hyp hn
  let ι : Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))) →*
      Subgroup.centralizer ({(y : GL (Fin n) K)} : Set (GL (Fin n) K)) :=
    ((primeFormUnitary h (idGram K n)).subtype.comp
      (Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))).subtype).codRestrict _
      (fun g => by
        have := Subgroup.mem_centralizer_singleton_iff.mp g.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this))
  refine isCyclic_of_injective ι (fun a b hab => ?_)
  have h1 := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h1)

end CaseII

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni
