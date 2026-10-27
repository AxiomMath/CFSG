module

public import CFSG.CharacterTheory.Wreathed.NormalCentralizerBlockOrbits
public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.ResidueCentralIdempotents

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.BlockOrbits

namespace OrbitIdempotents

variable {H : Type*} [Group H]

theorem le_centralizer_self_of_comm (P : Subgroup H) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    P ≤ Subgroup.centralizer (P : Set H) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hPab b hb a ha

variable [Finite H]

omit [Finite H] in
theorem complement_normal {p : ℕ} [Fact p.Prime] (P E : Subgroup H) [P.Normal]
    (hPp : IsPGroup p P) (hEW : E ≤ Subgroup.centralizer (P : Set H)) (hEp : ¬ p ∣ Nat.card E)
    (hPE : P ⊓ E = ⊥)
    (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E, w = a * x) : E.Normal := by
  refine ⟨fun x hx h => ?_⟩
  have hy : h * x * h⁻¹ ∈ Subgroup.centralizer (P : Set H) :=
    (Subgroup.normal_centralizer (H := P)).conj_mem x (hEW hx) h
  obtain ⟨a, ha, z, hz, hyz⟩ := hW _ hy
  set n := orderOf x with hn
  have hncop : Nat.Coprime p n := by
    have hdvd : orderOf x ∣ Nat.card E := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : E)
      rwa [Subgroup.orderOf_mk] at this
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hp => hEp (hp.trans hdvd)
  have hcomm : Commute a z := (Subgroup.mem_centralizer_iff.mp (hEW hz) a ha)
  have hpow : (h * x * h⁻¹) ^ n = 1 := by
    rw [conj_pow, hn, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  rw [hyz, hcomm.mul_pow] at hpow
  have han : a ^ n ∈ P ⊓ E := by
    refine ⟨P.pow_mem ha n, ?_⟩
    have : a ^ n = (z ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [this]
    exact E.inv_mem (E.pow_mem hz n)
  rw [hPE, Subgroup.mem_bot] at han
  have ha1 : a = 1 := by
    obtain ⟨k, hk⟩ := hPp ⟨a, ha⟩
    have hk' : a ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd1 : orderOf a ∣ n := orderOf_dvd_of_pow_eq_one han
    have hdvd2 : orderOf a ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
    have hcop : Nat.Coprime (orderOf a) n := by
      rw [hj]
      exact Nat.Coprime.pow_left _ hncop
    have hone : orderOf a = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd1
    exact orderOf_eq_one_iff.mp hone
  rw [hyz, ha1, one_mul]
  exact hz

@[expose] def normalSubgroupConj (E : Subgroup H) [E.Normal] (h : H) : E ≃* E where
  toFun x := ⟨h * (x : H) * h⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : E.Normal) (x : H) x.property h⟩
  invFun x := ⟨h⁻¹ * (x : H) * h, by
    have hmem := Subgroup.Normal.conj_mem (inferInstance : E.Normal) (x : H) x.property h⁻¹
    simpa only [inv_inv] using hmem⟩
  left_inv x := Subtype.ext (by dsimp; group)
  right_inv x := Subtype.ext (by dsimp; group)
  map_mul' x y := Subtype.ext (by dsimp; group)

omit [Finite H] in
theorem normalSubgroupConj_apply (E : Subgroup H) [E.Normal] (h : H) (x : E) :
    (normalSubgroupConj E h x : H) = h * x * h⁻¹ := rfl

end OrbitIdempotents

open OrbitIdempotents

@[expose] def ConjugateLabel {H : Type*} [Group H] [Fintype H] (E : Subgroup H)
    (basis : FiniteIrreducibleCharacterBasis E) (h : H) (μ μ' : basis.index) : Prop :=
  ∀ x y : E, (y : H) = h * x * h⁻¹ →
    (basis.representation μ').character y = (basis.representation μ).character x

namespace OrbitIdempotents

variable {H : Type*} [Group H] [Fintype H]

theorem conjugateLabel_iff (E : Subgroup H) [E.Normal] (basis : FiniteIrreducibleCharacterBasis E)
    (h : H) (μ μ' : basis.index) :
    ConjugateLabel E basis h μ μ' ↔ LabelTransport basis basis (normalSubgroupConj E h) μ μ' := by
  constructor
  · intro hconj x
    exact hconj x _ rfl
  · intro htransport x y hxy
    have hy : y = normalSubgroupConj E h x := Subtype.ext hxy
    rw [hy]
    exact htransport x

theorem conjugateLabel_mul (E : Subgroup H) [E.Normal] (eb : FiniteIrreducibleCharacterBasis E)
    {h k : H} {μ μ' μ'' : eb.index} (h₁ : ConjugateLabel E eb h μ μ')
    (h₂ : ConjugateLabel E eb k μ' μ'') : ConjugateLabel E eb (k * h) μ μ'' := by
  intro x y hxy
  have hy : (y : H) = k * (normalSubgroupConj E h x : H) * k⁻¹ := by
    rw [hxy, normalSubgroupConj_apply]
    group
  rw [h₂ _ y hy, h₁ x _ (normalSubgroupConj_apply E h x)]

omit [Fintype H] in
theorem conjugateLabel_inv {H : Type*} [Group H] [Fintype H] (E : Subgroup H)
    (eb : FiniteIrreducibleCharacterBasis E) {k : H} {μ' μ'' : eb.index}
    (h₂ : ConjugateLabel E eb k μ' μ'') : ConjugateLabel E eb k⁻¹ μ'' μ' := by
  intro y x hxy
  have hy : (y : H) = k * x * k⁻¹ := by
    rw [hxy]
    group
  exact (h₂ x y hy).symm

theorem conjugateLabel_existsUnique (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) (h : H) (μ : eb.index) :
    ∃! μ', ConjugateLabel E eb h μ μ' := by
  obtain ⟨μ', hμ'⟩ := labelTransport_exists eb eb (normalSubgroupConj E h) μ
  refine ⟨μ', (conjugateLabel_iff E eb h μ μ').mpr hμ', fun ν hν => ?_⟩
  exact labelTransport_unique ((conjugateLabel_iff E eb h μ ν).mp hν) hμ'

section Product

variable (P E : Subgroup H) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
  (hEW : E ≤ Subgroup.centralizer (P : Set H)) (hPE : P ⊓ E = ⊥)
  (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E, w = a * x)

abbrev toW (a : P) : Subgroup.centralizer (P : Set H) :=
  ⟨a, le_centralizer_self_of_comm P hPab a.property⟩

omit [Fintype H] in
include hPab in
theorem toW_commute (a : P) (w : Subgroup.centralizer (P : Set H)) :
    toW P hPab a * w = w * toW P hPab a := by
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp w.property a a.property

theorem single_toW_central (a : P) :
    ∀ other : MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H)),
      Commute (MonoidAlgebra.single (toW P hPab a) (1 : ℂ)) other := by
  apply groupAlgebra_central_of_coeff_conjugation
  intro v w
  have hconj : w⁻¹ * toW P hPab a * w = toW P hPab a := by
    rw [mul_assoc, toW_commute P hPab a w, ← mul_assoc, inv_mul_cancel, one_mul]
  have hiff : toW P hPab a = w * v * w⁻¹ ↔ toW P hPab a = v := by
    constructor
    · intro h
      calc toW P hPab a = w⁻¹ * toW P hPab a * w := hconj.symm
        _ = w⁻¹ * (w * v * w⁻¹) * w := by rw [← h]
        _ = v := by group
    · intro h
      rw [← h, ← toW_commute P hPab a w, mul_inv_cancel_right]
  change (Finsupp.single (toW P hPab a) (1 : ℂ)) (w * v * w⁻¹) =
    (Finsupp.single (toW P hPab a) (1 : ℂ)) v
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hv : toW P hPab a = v
  · rw [ite_eq_left hv, ite_eq_left (hiff.mpr hv)]
  · rw [ite_eq_right hv, ite_eq_right fun h => hv (hiff.mp h)]

omit [Fintype H] in
include hW in
theorem conj_inclusion_eq (w : Subgroup.centralizer (P : Set H)) :
    ∃ y : E, ∀ x : E,
      w * Subgroup.inclusion hEW x * w⁻¹ = Subgroup.inclusion hEW (y * x * y⁻¹) := by
  obtain ⟨a, ha, y, hy, hw⟩ := hW w w.property
  refine ⟨⟨y, hy⟩, fun x => Subtype.ext ?_⟩
  change (w : H) * x * (w : H)⁻¹ = y * x * y⁻¹
  have hcomm : ∀ u ∈ Subgroup.centralizer (P : Set H), a * u = u * a := fun u hu =>
    Subgroup.mem_centralizer_iff.mp hu a ha
  have hyx : y * (x : H) * y⁻¹ ∈ Subgroup.centralizer (P : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hEW hy) (hEW x.property)) (Subgroup.inv_mem _ (hEW hy))
  rw [hw]
  calc a * y * x * (a * y)⁻¹ = a * (y * x * y⁻¹) * a⁻¹ := by group
    _ = (y * x * y⁻¹) * a * a⁻¹ := by rw [hcomm _ hyx]
    _ = y * x * y⁻¹ := by group

include hW in
theorem inclusion_central (z : MonoidAlgebra ℂ E) (hz : ∀ other, Commute z other) :
    ∀ other : MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H)),
      Commute (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) z) other := by
  have hι : Function.Injective (Subgroup.inclusion hEW) := Subgroup.inclusion_injective hEW
  apply groupAlgebra_central_of_coeff_conjugation
  intro v w
  obtain ⟨y, hy⟩ := conj_inclusion_eq P E hEW hW w
  by_cases hv : v ∈ Set.range (Subgroup.inclusion hEW)
  · obtain ⟨x, rfl⟩ := hv
    rw [hy, embedded_coeff _ hι, embedded_coeff _ hι]
    exact central_groupAlgebra_coeff_conjugation z hz x y
  · have hv' : w * v * w⁻¹ ∉ Set.range (Subgroup.inclusion hEW) := by
      rintro ⟨x, hx⟩
      apply hv
      obtain ⟨y', hy'⟩ := conj_inclusion_eq P E hEW hW w⁻¹
      refine ⟨y' * x * y'⁻¹, ?_⟩
      rw [← hy', hx]
      group
    rw [embedded_coeff_zero _ _ _ hv', embedded_coeff_zero _ _ _ hv]

@[expose] noncomputable def component (z : MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H)))
    (a : P) : MonoidAlgebra ℂ E :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun x : E =>
    z.coeff (toW P hPab a * Subgroup.inclusion hEW x))

theorem component_coeff (z : MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H))) (a : P)
    (x : E) : (component P E hPab hEW z a).coeff x =
      z.coeff (toW P hPab a * Subgroup.inclusion hEW x) := rfl

omit [Fintype H] in
include hPE in
theorem mem_inclusion_range_iff (a b : P) (x : E) :
    (toW P hPab a)⁻¹ * (toW P hPab b * Subgroup.inclusion hEW x) ∈
        Set.range (Subgroup.inclusion hEW) ↔ a = b := by
  constructor
  · rintro ⟨y, hy⟩
    have hval := congrArg Subtype.val hy
    change (y : H) = (a : H)⁻¹ * (b * x) at hval
    have hab : (a : H)⁻¹ * b = y * (x : H)⁻¹ := by
      calc (a : H)⁻¹ * b = (a : H)⁻¹ * (b * x) * (x : H)⁻¹ := by group
        _ = y * (x : H)⁻¹ := by rw [hval]
    have hmem : (a : H)⁻¹ * b ∈ P ⊓ E := ⟨P.mul_mem (P.inv_mem a.property) b.property, by
      rw [hab]
      exact E.mul_mem y.property (E.inv_mem x.property)⟩
    rw [hPE, Subgroup.mem_bot] at hmem
    apply Subtype.ext
    calc (a : H) = a * ((a : H)⁻¹ * b) := by rw [hmem, mul_one]
      _ = b := by group
  · rintro rfl
    refine ⟨x, Subtype.ext ?_⟩
    change (x : H) = (a : H)⁻¹ * (a * x)
    group

include hPE hW in
theorem decomposition (z : MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H))) :
    z = ∑ a : P, MonoidAlgebra.single (toW P hPab a) (1 : ℂ) *
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) (component P E hPab hEW z a) := by
  have hι : Function.Injective (Subgroup.inclusion hEW) := Subgroup.inclusion_injective hEW
  ext v
  obtain ⟨b, hb, x, hx, hv⟩ := hW v v.property
  have hv' : v = toW P hPab ⟨b, hb⟩ * Subgroup.inclusion hEW ⟨x, hx⟩ := Subtype.ext hv
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply' (s := Finset.univ)]
  rw [Finset.sum_eq_single (⟨b, hb⟩ : P)]
  · rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, hv']
    have hmem := (mem_inclusion_range_iff P E hPab hEW hPE ⟨b, hb⟩ ⟨b, hb⟩ ⟨x, hx⟩).mpr rfl
    obtain ⟨y, hy⟩ := hmem
    rw [← hy, embedded_coeff _ hι, component_coeff]
    congr 1
    rw [hy]
    group
  · intro a _ hab
    rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, hv']
    apply embedded_coeff_zero
    intro hmem
    exact hab ((mem_inclusion_range_iff P E hPab hEW hPE a ⟨b, hb⟩ ⟨x, hx⟩).mp hmem)
  · intro h
    exact absurd (Finset.mem_univ _) h

include hPab in
theorem component_central (z : MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H)))
    (hz : ∀ other, Commute z other) (a : P) :
    ∀ other : MonoidAlgebra ℂ E, Commute (component P E hPab hEW z a) other := by
  apply groupAlgebra_central_of_coeff_conjugation
  intro x c
  rw [component_coeff, component_coeff]
  have hconj : toW P hPab a * Subgroup.inclusion hEW (c * x * c⁻¹) =
      Subgroup.inclusion hEW c * (toW P hPab a * Subgroup.inclusion hEW x) *
        (Subgroup.inclusion hEW c)⁻¹ := by
    rw [map_mul (Subgroup.inclusion hEW), map_mul (Subgroup.inclusion hEW),
      map_inv (Subgroup.inclusion hEW)]
    calc toW P hPab a * (Subgroup.inclusion hEW c * Subgroup.inclusion hEW x *
          (Subgroup.inclusion hEW c)⁻¹) =
        (toW P hPab a * Subgroup.inclusion hEW c) * Subgroup.inclusion hEW x *
          (Subgroup.inclusion hEW c)⁻¹ := by group
      _ = (Subgroup.inclusion hEW c * toW P hPab a) * Subgroup.inclusion hEW x *
          (Subgroup.inclusion hEW c)⁻¹ := by rw [toW_commute P hPab a]
      _ = _ := by group
  rw [hconj]
  exact central_groupAlgebra_coeff_conjugation z hz _ _

include hPab in
theorem single_toW_mem (ring : Subring ℂ) (a : P) :
    MonoidAlgebra.single (toW P hPab a) (1 : ℂ) ∈
      centralCoefficientSubring (G := Subgroup.centralizer (P : Set H)) ring := by
  refine Subring.mem_inf.mpr ⟨fun w => ?_, Subring.mem_center_iff.mpr fun o =>
    (single_toW_central P hPab a o).eq.symm⟩
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs
  · exact ring.one_mem
  · exact ring.zero_mem

include hW in
theorem inclusion_mem (ring : Subring ℂ) (z : MonoidAlgebra ℂ E) (hz : ∀ o, Commute z o)
    (hcoeff : ∀ x, z.coeff x ∈ ring) :
    MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) z ∈
      centralCoefficientSubring (G := Subgroup.centralizer (P : Set H)) ring := by
  have hι : Function.Injective (Subgroup.inclusion hEW) := Subgroup.inclusion_injective hEW
  refine Subring.mem_inf.mpr ⟨fun w => ?_, Subring.mem_center_iff.mpr fun o =>
    (inclusion_central P E hEW hW z hz o).eq.symm⟩
  by_cases hw : w ∈ Set.range (Subgroup.inclusion hEW)
  · obtain ⟨x, rfl⟩ := hw
    rw [embedded_coeff _ hι]
    exact hcoeff x
  · rw [embedded_coeff_zero _ _ _ hw]
    exact ring.zero_mem

include hPab in
theorem residue_single_eq_one (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H))) (θ : wb.index)
    (a : P) (s : centralCoefficientSubring (G := Subgroup.centralizer (P : Set H))
      (localizedComplexIntegerRing ideal))
    (hs : s.val = MonoidAlgebra.single (toW P hPab a) (1 : ℂ)) :
    centralCharacterResidueHom wb ideal θ s = 1 := by
  obtain ⟨k, hk⟩ := hPp a
  have hak : toW P hPab a ^ (p ^ k) = 1 := Subtype.ext (by
    have hval := congrArg Subtype.val hk
    simpa using hval)
  have hpow : s ^ (p ^ k) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hs, MonoidAlgebra.single_pow, one_pow, hak]
    rfl
  have hres := congrArg (centralCharacterResidueHom wb ideal θ) hpow
  rw [map_pow, map_one] at hres
  have hsub : (centralCharacterResidueHom wb ideal θ s - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow, hres, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)).mp hsub)

include hPab hPE hW in
theorem residue_eq_of_scalar_eq (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H))) {θ θ' : wb.index}
    (hscalar : ∀ z : MonoidAlgebra ℂ E, (∀ o, Commute z o) →
      centralCharacterScalar wb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) z) θ =
        centralCharacterScalar wb
          (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) z) θ') :
    centralCharacterResidueHom wb ideal θ = centralCharacterResidueHom wb ideal θ' := by
  apply RingHom.ext
  intro z
  have hzc := centralCoefficientSubring_commutes _ z
  let s : P → centralCoefficientSubring (G := Subgroup.centralizer (P : Set H))
      (localizedComplexIntegerRing ideal) :=
    fun a => ⟨_, single_toW_mem P hPab _ a⟩
  let t : P → centralCoefficientSubring (G := Subgroup.centralizer (P : Set H))
      (localizedComplexIntegerRing ideal) :=
    fun a => ⟨_, inclusion_mem P E hEW hW _ (component P E hPab hEW z.val a)
      (component_central P E hPab hEW z.val hzc a)
      (fun x => by rw [component_coeff]; exact centralCoefficientSubring_coefficients _ z _)⟩
  have hz : z = ∑ a, s a * t a := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
    exact decomposition P E hPab hEW hPE hW z.val
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, residue_single_eq_one P hPab ideal hPp wb θ a (s a) rfl,
    residue_single_eq_one P hPab ideal hPp wb θ' a (s a) rfl, one_mul, one_mul]
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom wb ideal θ (t a)) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom wb ideal θ' (t a))
  congr 1
  apply Subtype.ext
  rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
  exact hscalar _ (component_central P E hPab hEW z.val hzc a)

end Product

section Scalars

variable {G : Type*} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem scalar_mul (x y : MonoidAlgebra ℂ G) (hx : ∀ o, Commute x o) (hy : ∀ o, Commute y o)
    (θ : basis.index) :
    centralCharacterScalar basis (x * y) θ =
      centralCharacterScalar basis x θ * centralCharacterScalar basis y θ := by
  apply irreducible_scalar_identity_injective (basis.representation θ) (basis.irreducible θ)
  dsimp only
  rw [← centralCharacterScalar_action basis _ fun o => (hx o).mul_left (hy o), map_mul,
    centralCharacterScalar_action basis _ hx, centralCharacterScalar_action basis _ hy,
    smul_mul_smul_comm, one_mul]

theorem scalar_smul (c : ℂ) (x : MonoidAlgebra ℂ G) (hx : ∀ o, Commute x o) (θ : basis.index) :
    centralCharacterScalar basis (c • x) θ = c * centralCharacterScalar basis x θ := by
  apply irreducible_scalar_identity_injective (basis.representation θ) (basis.irreducible θ)
  dsimp only
  rw [← centralCharacterScalar_action basis _ fun o => (hx o).smul_left c, map_smul,
    centralCharacterScalar_action basis _ hx, smul_smul]

theorem scalar_sum {κ : Type*} (s : Finset κ) (x : κ → MonoidAlgebra ℂ G)
    (hx : ∀ i, ∀ o, Commute (x i) o) (θ : basis.index) :
    centralCharacterScalar basis (∑ i ∈ s, x i) θ =
      ∑ i ∈ s, centralCharacterScalar basis (x i) θ := by
  apply irreducible_scalar_identity_injective (basis.representation θ) (basis.irreducible θ)
  dsimp only
  rw [← centralCharacterScalar_action basis _
      fun o => Commute.sum_left _ _ _ fun i _ => hx i o, map_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => centralCharacterScalar_action basis _ (hx i) θ

theorem scalar_zero (θ : basis.index) : centralCharacterScalar basis 0 θ = 0 := by
  apply irreducible_scalar_identity_injective (basis.representation θ) (basis.irreducible θ)
  dsimp only
  rw [← centralCharacterScalar_action basis _ fun o => Commute.zero_left o, map_zero, zero_smul]

theorem scalar_one (θ : basis.index) : centralCharacterScalar basis 1 θ = 1 := by
  apply irreducible_scalar_identity_injective (basis.representation θ) (basis.irreducible θ)
  dsimp only
  rw [← centralCharacterScalar_action basis _ fun o => Commute.one_left o, map_one, one_smul]

theorem scalar_characterSubsetIdempotent (support : Finset basis.index) (θ : basis.index) :
    centralCharacterScalar basis (characterSubsetIdempotent basis support) θ =
      if θ ∈ support then 1 else 0 := by
  apply irreducible_scalar_identity_injective (basis.representation θ) (basis.irreducible θ)
  dsimp only
  rw [← centralCharacterScalar_action basis _ (characterSubsetIdempotent_central basis support)]
  exact characterIdempotentExpansion_action basis _ θ

theorem characterSubsetIdempotent_singleton (μ : basis.index) :
    characterSubsetIdempotent basis {μ} =
      complexCharacterIdempotent (basis.representation μ).character := by
  unfold characterSubsetIdempotent characterIdempotentExpansion
  rw [Finset.sum_eq_single μ]
  · simp only [Finset.mem_singleton, ite_true, one_smul]
  · intro ν _ hν
    simp only [Finset.mem_singleton, hν, ite_false, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ μ) h

theorem characterSubsetIdempotent_eq_sum (support : Finset basis.index) :
    characterSubsetIdempotent basis support =
      ∑ μ ∈ support, complexCharacterIdempotent (basis.representation μ).character := by
  unfold characterSubsetIdempotent characterIdempotentExpansion
  simp only [ite_smul, one_smul, zero_smul]
  exact Fintype.sum_ite_mem support _

theorem complexCharacterIdempotent_mul_central (μ : basis.index) (z : MonoidAlgebra ℂ G)
    (hz : ∀ o, Commute z o) :
    complexCharacterIdempotent (basis.representation μ).character * z =
      centralCharacterScalar basis z μ •
        complexCharacterIdempotent (basis.representation μ).character := by
  apply sub_eq_zero.mp
  apply central_groupAlgebra_eq_zero_of_basis_actions basis
  · intro other
    exact ((complexCharacterIdempotent_central _ other).mul_left (hz other)).sub_left
      ((complexCharacterIdempotent_central _ other).smul_left _)
  · intro ν
    rw [map_sub, map_mul, map_smul, centralCharacterScalar_action basis z hz,
      complexCharacterIdempotent_irreducible_action _ _ (basis.irreducible μ)
        (basis.irreducible ν)]
    by_cases hμν : μ = ν
    · subst hμν
      simp
    · rw [ite_eq_right fun h => hμν (basis.distinct h)]
      simp

theorem transport_central (e : G ≃* G) (z : MonoidAlgebra ℂ G) (hz : ∀ o, Commute z o) :
    ∀ o, Commute (MonoidAlgebra.mapDomainRingHom ℂ e.toMonoidHom z) o := by
  apply groupAlgebra_central_of_coeff_conjugation
  intro x c
  have hconj : e.symm (c * x * c⁻¹) = e.symm c * e.symm x * (e.symm c)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [groupAlgebra_transport_coeff, groupAlgebra_transport_coeff, hconj]
  exact central_groupAlgebra_coeff_conjugation z hz _ _

end Scalars

omit [Fintype H] in
theorem mapDomainRingHom_smul {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (c : ℂ)
    (x : MonoidAlgebra ℂ M) :
    MonoidAlgebra.mapDomainRingHom ℂ f (c • x) = c • MonoidAlgebra.mapDomainRingHom ℂ f x := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomain_smul]

section Blocks

variable (P E : Subgroup H) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
  (hEW : E ≤ Subgroup.centralizer (P : Set H)) (hPE : P ⊓ E = ⊥)
  (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E, w = a * x)
  (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
  (eb : FiniteIrreducibleCharacterBasis E)

@[expose] noncomputable def embeddedIdempotent (μ : eb.index) :
    MonoidAlgebra ℂ (Subgroup.centralizer (P : Set H)) :=
  MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
    (complexCharacterIdempotent (eb.representation μ).character)

include hW in
theorem embeddedIdempotent_central (μ : eb.index) :
    ∀ o, Commute (embeddedIdempotent P E hEW eb μ) o :=
  inclusion_central P E hEW hW _ (complexCharacterIdempotent_central _)

theorem embeddedIdempotent_isIdempotent (μ : eb.index) :
    IsIdempotentElem (embeddedIdempotent P E hEW eb μ) := by
  have h := characterSubsetIdempotent_isIdempotent eb {μ}
  rw [characterSubsetIdempotent_singleton] at h
  unfold embeddedIdempotent
  rw [IsIdempotentElem, ← map_mul, h.eq]

theorem embeddedIdempotent_mul_of_ne {μ ν : eb.index} (h : μ ≠ ν) :
    embeddedIdempotent P E hEW eb μ * embeddedIdempotent P E hEW eb ν = 0 := by
  have hinter : ({μ} : Finset eb.index) ∩ {ν} = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro rfl
    exact h
  unfold embeddedIdempotent
  rw [← map_mul, ← characterSubsetIdempotent_singleton, ← characterSubsetIdempotent_singleton,
    ← characterSubsetIdempotent_inter, hinter, characterSubsetIdempotent_empty, map_zero]

theorem embeddedIdempotent_injective : Function.Injective (embeddedIdempotent P E hEW eb) := by
  intro μ ν h
  have h' : complexCharacterIdempotent (eb.representation μ).character =
      complexCharacterIdempotent (eb.representation ν).character :=
    MonoidAlgebra.mapDomain_injective (R := ℂ) (Subgroup.inclusion_injective hEW) h
  rw [← characterSubsetIdempotent_singleton, ← characterSubsetIdempotent_singleton] at h'
  exact Finset.singleton_injective (characterSubsetIdempotent_injective eb h')

theorem embeddedIdempotent_coeff_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hEp : ¬ p ∣ Nat.card E) (μ : eb.index) (w : Subgroup.centralizer (P : Set H)) :
    (embeddedIdempotent P E hEW eb μ).coeff w ∈ localizedComplexIntegerRing ideal := by
  have hadm := singleton_admissible_of_full_prime_part_dvd_degree eb ideal p μ (by
    rw [Nat.factorization_eq_zero_of_not_dvd hEp, pow_zero]
    exact one_dvd _)
  have hadm' : ∀ x, (characterSubsetIdempotent eb {μ}).coeff x ∈
      localizedComplexIntegerRing ideal := hadm
  unfold embeddedIdempotent
  by_cases hw : w ∈ Set.range (Subgroup.inclusion hEW)
  · obtain ⟨x, rfl⟩ := hw
    rw [embedded_coeff _ (Subgroup.inclusion_injective hEW), ← characterSubsetIdempotent_singleton]
    exact hadm' x
  · rw [embedded_coeff_zero _ _ _ hw]
    exact (localizedComplexIntegerRing ideal).zero_mem

include hW in
theorem scalar_embedded_of_scalar_eq_one {μ : eb.index} {θ : wb.index}
    (hθ : centralCharacterScalar wb (embeddedIdempotent P E hEW eb μ) θ = 1)
    (z : MonoidAlgebra ℂ E) (hz : ∀ o, Commute z o) :
    centralCharacterScalar wb (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) z) θ =
      centralCharacterScalar eb z μ := by
  have hεc := embeddedIdempotent_central P E hEW hW eb μ
  have hprod : embeddedIdempotent P E hEW eb μ *
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) z =
      centralCharacterScalar eb z μ • embeddedIdempotent P E hEW eb μ := by
    unfold embeddedIdempotent
    rw [← map_mul, complexCharacterIdempotent_mul_central eb μ z hz, mapDomainRingHom_smul]
  have h1 := congrArg (fun x => centralCharacterScalar wb x θ) hprod
  rw [scalar_mul wb _ _ hεc (inclusion_central P E hEW hW z hz), scalar_smul wb _ _ hεc, hθ,
    one_mul, mul_one] at h1
  exact h1

@[expose] noncomputable def idempotentSupport (μ : eb.index) : Finset wb.index :=
  Finset.univ.filter fun θ => centralCharacterScalar wb (embeddedIdempotent P E hEW eb μ) θ = 1

theorem mem_idempotentSupport (μ : eb.index) (θ : wb.index) :
    θ ∈ idempotentSupport P E hEW wb eb μ ↔
      centralCharacterScalar wb (embeddedIdempotent P E hEW eb μ) θ = 1 := by
  simp only [idempotentSupport, Finset.mem_filter, Finset.mem_univ, true_and]

include hW in
theorem embeddedIdempotent_eq_support (μ : eb.index) :
    embeddedIdempotent P E hEW eb μ =
      characterSubsetIdempotent wb (idempotentSupport P E hEW wb eb μ) := by
  obtain ⟨T, hT, -⟩ := central_idempotent_eq_character_subset wb _
    (embeddedIdempotent_central P E hEW hW eb μ) (embeddedIdempotent_isIdempotent P E hEW eb μ)
  have hTS : T = idempotentSupport P E hEW wb eb μ := by
    ext θ
    rw [mem_idempotentSupport, hT, scalar_characterSubsetIdempotent]
    by_cases hθ : θ ∈ T
    · simp [hθ]
    · simp [hθ]
  rw [hT, hTS]

include hW in
theorem idempotentSupport_admissible (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hEp : ¬ p ∣ Nat.card E) (μ : eb.index) :
    characterSubsetAdmissible wb (localizedComplexIntegerRing ideal)
      (idempotentSupport P E hEW wb eb μ) := by
  change characterSubsetIdempotent wb _ ∈ groupAlgebraCoefficientSubring _
  rw [← embeddedIdempotent_eq_support P E hEW hW wb eb μ]
  exact fun w => embeddedIdempotent_coeff_mem P E hEW eb ideal p hEp μ w

include hPab hPE hW in
theorem residue_eq_of_mem_support (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P)
    {μ : eb.index} {θ θ' : wb.index} (hθ : θ ∈ idempotentSupport P E hEW wb eb μ)
    (hθ' : θ' ∈ idempotentSupport P E hEW wb eb μ) :
    centralCharacterResidueHom wb ideal θ = centralCharacterResidueHom wb ideal θ' :=
  residue_eq_of_scalar_eq P E hPab hEW hPE hW ideal hPp wb fun z hz =>
    (scalar_embedded_of_scalar_eq_one P E hEW hW wb eb
      ((mem_idempotentSupport P E hEW wb eb μ θ).mp hθ) z hz).trans
    (scalar_embedded_of_scalar_eq_one P E hEW hW wb eb
      ((mem_idempotentSupport P E hEW wb eb μ θ').mp hθ') z hz).symm

include hPab hPE hW in
theorem coefficientBlock_eq_support (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P)
    (hEp : ¬ p ∣ Nat.card E) {μ : eb.index} {θ : wb.index}
    (hθ : θ ∈ idempotentSupport P E hEW wb eb μ) :
    coefficientBlock wb (localizedComplexIntegerRing ideal) θ =
      idempotentSupport P E hEW wb eb μ := by
  apply Finset.Subset.antisymm
  · exact coefficientBlock_subset_admissible wb _ _
      (idempotentSupport_admissible P E hEW hW wb eb ideal p hEp μ) θ hθ
  · intro θ' hθ'
    rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    exact residue_eq_of_mem_support P E hPab hEW hPE hW wb eb ideal hPp hθ hθ'

include hW in
theorem exists_mem_support (θ : wb.index) : ∃ μ, θ ∈ idempotentSupport P E hEW wb eb μ := by
  have hsum : ∑ μ, embeddedIdempotent P E hEW eb μ = 1 := by
    unfold embeddedIdempotent
    rw [← map_sum, ← characterSubsetIdempotent_eq_sum eb, characterSubsetIdempotent_univ,
      map_one]
  have h1 := congrArg (fun x => centralCharacterScalar wb x θ) hsum
  rw [scalar_sum wb _ _ (fun μ => embeddedIdempotent_central P E hEW hW eb μ), scalar_one] at h1
  by_contra hnone
  have hzero : ∀ μ, centralCharacterScalar wb (embeddedIdempotent P E hEW eb μ) θ = 0 := by
    intro μ
    rcases central_idempotent_scalar_zero_or_one wb _ (embeddedIdempotent_central P E hEW hW eb μ)
      (embeddedIdempotent_isIdempotent P E hEW eb μ) θ with h | h
    · exact h
    · exact absurd ⟨μ, (mem_idempotentSupport P E hEW wb eb μ θ).mpr h⟩ hnone
  rw [Finset.sum_congr rfl fun μ _ => hzero μ, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

include hW in
theorem support_unique {μ ν : eb.index} {θ : wb.index}
    (hμ : θ ∈ idempotentSupport P E hEW wb eb μ) (hν : θ ∈ idempotentSupport P E hEW wb eb ν) :
    μ = ν := by
  by_contra hne
  have h0 := congrArg (fun x => centralCharacterScalar wb x θ)
    (embeddedIdempotent_mul_of_ne P E hEW eb hne)
  rw [scalar_mul wb _ _ (embeddedIdempotent_central P E hEW hW eb μ)
      (embeddedIdempotent_central P E hEW hW eb ν),
    (mem_idempotentSupport P E hEW wb eb μ θ).mp hμ,
    (mem_idempotentSupport P E hEW wb eb ν θ).mp hν, one_mul, scalar_zero] at h0
  exact one_ne_zero h0

include hW in
theorem support_nonempty (μ : eb.index) : (idempotentSupport P E hEW wb eb μ).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have h := embeddedIdempotent_eq_support P E hEW hW wb eb μ
  rw [hempty, characterSubsetIdempotent_empty] at h
  have h' : embeddedIdempotent P E hEW eb μ =
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
        (characterSubsetIdempotent eb ∅) := by
    rw [h, characterSubsetIdempotent_empty, map_zero]
  unfold embeddedIdempotent at h'
  rw [← characterSubsetIdempotent_singleton] at h'
  exact Finset.singleton_ne_empty μ (characterSubsetIdempotent_injective eb
    (MonoidAlgebra.mapDomain_injective (R := ℂ) (Subgroup.inclusion_injective hEW) h'))

include hPab hPE hW in
theorem blockIdempotent_eq_iff_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P)
    (hEp : ¬ p ∣ Nat.card E) (μ : eb.index) (θ : wb.index) :
    characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) θ) =
        embeddedIdempotent P E hEW eb μ ↔ θ ∈ idempotentSupport P E hEW wb eb μ := by
  constructor
  · intro h
    rw [mem_idempotentSupport, ← h, scalar_characterSubsetIdempotent,
      ite_eq_left (coefficientBlock_self_mem _ _ _)]
  · intro hθ
    rw [coefficientBlock_eq_support P E hPab hEW hPE hW wb eb ideal hPp hEp hθ,
      ← embeddedIdempotent_eq_support P E hEW hW wb eb μ]

theorem embeddedIdempotent_transport [P.Normal] [E.Normal] (h : H) {μ μ' : eb.index}
    (hμ : ConjugateLabel E eb h μ μ') :
    MonoidAlgebra.mapDomainRingHom ℂ (normalCentralizerConj P h).toMonoidHom
        (embeddedIdempotent P E hEW eb μ) = embeddedIdempotent P E hEW eb μ' := by
  have hι : Function.Injective (Subgroup.inclusion hEW) := Subgroup.inclusion_injective hEW
  have ht := (conjugateLabel_iff E eb h μ μ').mp hμ
  have hconj : ∀ x : E, normalCentralizerConj P h (Subgroup.inclusion hEW x) =
      Subgroup.inclusion hEW (normalSubgroupConj E h x) := fun x => Subtype.ext rfl
  ext w
  rw [groupAlgebra_transport_coeff]
  unfold embeddedIdempotent
  by_cases hw : w ∈ Set.range (Subgroup.inclusion hEW)
  · obtain ⟨y, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := (normalSubgroupConj E h).surjective y
    conv_lhs => rw [← hconj, MulEquiv.symm_apply_apply]
    rw [embedded_coeff _ hι, embedded_coeff _ hι, complexCharacterIdempotent_coeff,
      complexCharacterIdempotent_coeff, ← map_inv (normalSubgroupConj E h) x, ht x⁻¹]
    have h1 := ht 1
    rw [map_one] at h1
    rw [h1]
  · have hw' : (normalCentralizerConj P h).symm w ∉ Set.range (Subgroup.inclusion hEW) := by
      rintro ⟨x, hx⟩
      apply hw
      refine ⟨normalSubgroupConj E h x, ?_⟩
      rw [← hconj, hx, MulEquiv.apply_symm_apply]
    rw [embedded_coeff_zero _ _ _ hw', embedded_coeff_zero _ _ _ hw]

include hPab hPE hW in
theorem block_transport [P.Normal] [E.Normal] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hPp : IsPGroup p P) (hEp : ¬ p ∣ Nat.card E) (h : H) {μ μ' : eb.index}
    (hμ : ConjugateLabel E eb h μ μ') {β β' : wb.index}
    (hβ : characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
      embeddedIdempotent P E hEW eb μ)
    (htrans : LabelTransport wb wb (normalCentralizerConj P h) β β') :
    characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β') =
      embeddedIdempotent P E hEW eb μ' := by
  rw [blockIdempotent_eq_iff_mem P E hPab hEW hPE hW wb eb ideal hPp hEp] at hβ ⊢
  rw [mem_idempotentSupport] at hβ ⊢
  rw [← embeddedIdempotent_transport P E hEW eb h hμ,
    centralCharacterScalar_labelTransport wb wb _ htrans]
  exact hβ

include hPab hPE hW in
theorem brauer_eq_iff [P.Normal] [E.Normal] (hb : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {p : ℕ} [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P) (hEp : ¬ p ∣ Nat.card E)
    {μ μ' : eb.index} {β β' : wb.index}
    (hβ : characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
      embeddedIdempotent P E hEW eb μ)
    (hβ' : characterSubsetIdempotent wb
      (coefficientBlock wb (localizedComplexIntegerRing ideal) β') =
        embeddedIdempotent P E hEW eb μ') :
    brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) wb β =
      brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) wb β' ↔
    ∃ h : H, ConjugateLabel E eb h μ μ' := by
  rw [(normal_p_centralizer_brauer_fibers_are_block_orbits hb ideal p P hPp wb).2.2 β β']
  constructor
  · rintro ⟨h, θ', hθ', hsame⟩
    obtain ⟨μ'', hμ''⟩ := (conjugateLabel_existsUnique E eb h μ).exists
    have hθ'idem := block_transport P E hPab hEW hPE hW wb eb ideal hPp hEp h hμ'' hβ hθ'
    have hcb : coefficientBlock wb (localizedComplexIntegerRing ideal) θ' =
        coefficientBlock wb (localizedComplexIntegerRing ideal) β' :=
      (coefficientBlock_eq_of_mem wb _ ((coefficientBlock_mem_iff _ _ _ _).mpr hsame)).symm
    rw [hcb, hβ'] at hθ'idem
    obtain rfl := embeddedIdempotent_injective P E hEW eb hθ'idem
    exact ⟨h, hμ''⟩
  · rintro ⟨h, hμ⟩
    obtain ⟨θ', hθ'⟩ := labelTransport_exists wb wb (normalCentralizerConj P h) β
    have hθ'idem := block_transport P E hPab hEW hPE hW wb eb ideal hPp hEp h hμ hβ hθ'
    rw [← hβ'] at hθ'idem
    have hcb := characterSubsetIdempotent_injective wb hθ'idem
    refine ⟨h, θ', hθ', ?_⟩
    rw [← coefficientBlock_mem_iff, hcb]
    exact coefficientBlock_self_mem _ _ _

omit [Fintype H] in
theorem orbitSum_transport {H : Type*} [Group H] [Fintype H] (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) (μ : eb.index) (k : H) :
    MonoidAlgebra.mapDomainRingHom ℂ (normalSubgroupConj E k).toMonoidHom
        (characterSubsetIdempotent eb
          (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ')) =
      characterSubsetIdempotent eb
        (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ') := by
  set Ω := Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ' with hΩ
  have hq := characterSubsetIdempotent_central eb Ω
  have hT := transport_central (normalSubgroupConj E k) _ hq
  have hscalar : ∀ θ', centralCharacterScalar eb
      (MonoidAlgebra.mapDomainRingHom ℂ (normalSubgroupConj E k).toMonoidHom
        (characterSubsetIdempotent eb Ω)) θ' =
      centralCharacterScalar eb (characterSubsetIdempotent eb Ω) θ' := by
    intro θ'
    obtain ⟨θ, hθ⟩ := (conjugateLabel_existsUnique E eb k⁻¹ θ').exists
    have htrans : ConjugateLabel E eb k θ θ' := by
      have hinv := conjugateLabel_inv E eb hθ
      rwa [inv_inv] at hinv
    rw [centralCharacterScalar_labelTransport eb eb _ ((conjugateLabel_iff E eb k θ θ').mp htrans),
      scalar_characterSubsetIdempotent, scalar_characterSubsetIdempotent]
    have hiff : θ ∈ Ω ↔ θ' ∈ Ω := by
      simp only [hΩ, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, hh⟩
        exact ⟨k * h, conjugateLabel_mul E eb hh htrans⟩
      · rintro ⟨h, hh⟩
        exact ⟨k⁻¹ * h, conjugateLabel_mul E eb hh hθ⟩
    simp only [hiff]
  calc _ = characterIdempotentExpansion eb (centralCharacterScalar eb
        (MonoidAlgebra.mapDomainRingHom ℂ (normalSubgroupConj E k).toMonoidHom
          (characterSubsetIdempotent eb Ω))) :=
        centralCharacterScalar_reconstruction eb _ hT
    _ = characterIdempotentExpansion eb
        (centralCharacterScalar eb (characterSubsetIdempotent eb Ω)) :=
        congrArg _ (funext hscalar)
    _ = _ := (centralCharacterScalar_reconstruction eb _ hq).symm

omit [Fintype H] in
theorem orbitSum_central {H : Type*} [Group H] [Fintype H] (E : Subgroup H) [E.Normal]
    (eb : FiniteIrreducibleCharacterBasis E) (μ : eb.index) :
    ∀ o : MonoidAlgebra ℂ H, Commute (MonoidAlgebra.mapDomainRingHom ℂ E.subtype
      (characterSubsetIdempotent eb
        (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ'))) o := by
  have hι : Function.Injective E.subtype := Subgroup.subtype_injective E
  apply groupAlgebra_central_of_coeff_conjugation
  intro y k
  by_cases hy : y ∈ Set.range E.subtype
  · obtain ⟨x, rfl⟩ := hy
    have hk : k * E.subtype x * k⁻¹ = E.subtype (normalSubgroupConj E k x) := rfl
    rw [hk, embedded_coeff _ hι, embedded_coeff _ hι]
    have hfix := congrArg (fun v => v.coeff (normalSubgroupConj E k x))
      (orbitSum_transport E eb μ k)
    rw [groupAlgebra_transport_coeff, MulEquiv.symm_apply_apply] at hfix
    exact hfix.symm
  · have hy' : k * y * k⁻¹ ∉ Set.range E.subtype := by
      rintro ⟨x, hx⟩
      apply hy
      refine ⟨normalSubgroupConj E k⁻¹ x, ?_⟩
      change k⁻¹ * (x : H) * k⁻¹⁻¹ = y
      have hx' : (x : H) = k * y * k⁻¹ := hx
      rw [hx']
      group
    rw [embedded_coeff_zero _ _ _ hy', embedded_coeff_zero _ _ _ hy]

omit [Fintype H] in
theorem orbitSum_coeff_mem {H : Type*} [Group H] [Fintype H] (E : Subgroup H)
    (eb : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hEp : ¬ p ∣ Nat.card E) (Ω : Finset eb.index) (y : H) :
    (MonoidAlgebra.mapDomainRingHom ℂ E.subtype (characterSubsetIdempotent eb Ω)).coeff y ∈
      localizedComplexIntegerRing ideal := by
  have hblock : ∀ ν, coefficientBlock eb (localizedComplexIntegerRing ideal) ν = {ν} := fun ν =>
    (full_prime_part_character_degree_singleton_block_singular_vanishing eb ideal p ν (by
      rw [Nat.factorization_eq_zero_of_not_dvd hEp, pow_zero]
      exact one_dvd _)).1
  have hadm : characterSubsetAdmissible eb (localizedComplexIntegerRing ideal) Ω :=
    (characterSubsetAdmissible_iff_union_blocks eb _ Ω).mpr fun ν hν => by
      rw [hblock ν]
      exact Finset.singleton_subset_iff.mpr hν
  have hadm' : ∀ x, (characterSubsetIdempotent eb Ω).coeff x ∈
      localizedComplexIntegerRing ideal := hadm
  by_cases hy : y ∈ Set.range E.subtype
  · obtain ⟨x, rfl⟩ := hy
    rw [embedded_coeff _ (Subgroup.subtype_injective E)]
    exact hadm' x
  · rw [embedded_coeff_zero _ _ _ hy]
    exact (localizedComplexIntegerRing ideal).zero_mem

theorem brauerProjection_embedded (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (q : MonoidAlgebra ℂ E)
    (qH : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal))
    (hqH : qH.val = MonoidAlgebra.mapDomainRingHom ℂ E.subtype q) :
    (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal) P
      (Subgroup.centralizer (P : Set H)) le_rfl (Subgroup.centralizer_le_normalizer _) qH).val =
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW) q := by
  ext w
  rw [centralNormalizerCoefficientProjection_coeff, ite_eq_left w.property, hqH]
  have hιW : Function.Injective (Subgroup.inclusion hEW) := Subgroup.inclusion_injective hEW
  by_cases hw : w ∈ Set.range (Subgroup.inclusion hEW)
  · obtain ⟨x, rfl⟩ := hw
    rw [embedded_coeff _ hιW]
    exact embedded_coeff _ (Subgroup.subtype_injective E) q x
  · rw [embedded_coeff_zero _ _ _ hw]
    apply embedded_coeff_zero
    rintro ⟨x, hx⟩
    exact hw ⟨x, Subtype.ext hx⟩

include hPab hPE hW in
theorem orbit_blockIdempotent [P.Normal] [E.Normal] (hb : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {p : ℕ} [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hPp : IsPGroup p P) (hEp : ¬ p ∣ Nat.card E)
    {χ : hb.index} {μ : eb.index} {β : wb.index}
    (hβ : characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
      embeddedIdempotent P E hEW eb μ)
    (hχ : brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H))
      le_rfl (Subgroup.centralizer_le_normalizer _) wb β = centralCharacterResidueHom hb ideal χ) :
    characterSubsetIdempotent hb (coefficientBlock hb (localizedComplexIntegerRing ideal) χ) =
      MonoidAlgebra.mapDomainRingHom ℂ E.subtype (characterSubsetIdempotent eb
        (Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ')) := by
  set Ω := Finset.univ.filter fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ' with hΩ
  set q := MonoidAlgebra.mapDomainRingHom ℂ E.subtype (characterSubsetIdempotent eb Ω) with hq
  have hqc : ∀ o, Commute q o := orbitSum_central E eb μ
  have hqcoeff : ∀ y, q.coeff y ∈ localizedComplexIntegerRing ideal :=
    orbitSum_coeff_mem E eb ideal p hEp Ω
  have hqidem : IsIdempotentElem q := by
    rw [hq, IsIdempotentElem, ← map_mul, (characterSubsetIdempotent_isIdempotent eb Ω).eq]
  obtain ⟨T, hT, -⟩ := central_idempotent_eq_character_subset hb q hqc hqidem
  let qH : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal) :=
    ⟨q, Subring.mem_inf.mpr ⟨hqcoeff, Subring.mem_center_iff.mpr fun o => (hqc o).eq.symm⟩⟩
  have hfiber := normal_p_centralizer_brauer_fibers_are_block_orbits hb ideal p P hPp wb
  have hTiff : ∀ χ', χ' ∈ T ↔ sameCoefficientBlock hb (localizedComplexIntegerRing ideal) χ χ' := by
    intro χ'
    obtain ⟨β', hβ'⟩ := hfiber.2.1 χ'
    obtain ⟨μ'', hμ''⟩ := exists_mem_support P E hEW hW wb eb β'
    have hβ'idem :=
      (blockIdempotent_eq_iff_mem P E hPab hEW hPE hW wb eb ideal hPp hEp μ'' β').mpr hμ''
    have h1 : centralCharacterResidueHom hb ideal χ' qH = if χ' ∈ T then 1 else 0 := by
      have hloc : localCentralCharacterHom hb ideal χ' qH = if χ' ∈ T then 1 else 0 := by
        apply Subtype.ext
        rw [localCentralCharacterHom_coe]
        change centralCharacterScalar hb q χ' = _
        rw [hT, scalar_characterSubsetIdempotent]
        split_ifs <;> simp
      change localizedComplexIntegerResidue ideal (localCentralCharacterHom hb ideal χ' qH) = _
      rw [hloc]
      split_ifs <;> simp
    have h2 : centralCharacterResidueHom hb ideal χ' qH = if μ'' ∈ Ω then 1 else 0 := by
      rw [← hβ']
      change centralCharacterResidueHom wb ideal β' (centralNormalizerCoefficientProjection _ P _
        le_rfl (Subgroup.centralizer_le_normalizer _) qH) = _
      have hloc : localCentralCharacterHom wb ideal β' (centralNormalizerCoefficientProjection _ P
          _ le_rfl (Subgroup.centralizer_le_normalizer _) qH) = if μ'' ∈ Ω then 1 else 0 := by
        apply Subtype.ext
        rw [localCentralCharacterHom_coe, brauerProjection_embedded P E hEW ideal _ qH rfl]
        have hsum : MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (characterSubsetIdempotent eb Ω) = ∑ μ' ∈ Ω, embeddedIdempotent P E hEW eb μ' := by
          rw [characterSubsetIdempotent_eq_sum, map_sum]
          rfl
        rw [hsum, scalar_sum wb _ _ fun μ' => embeddedIdempotent_central P E hEW hW eb μ']
        have hterm : ∀ μ', centralCharacterScalar wb (embeddedIdempotent P E hEW eb μ') β' =
            if μ' = μ'' then 1 else 0 := by
          intro μ'
          by_cases hμ' : μ' = μ''
          · rw [ite_eq_left hμ', hμ']
            exact (mem_idempotentSupport P E hEW wb eb μ'' β').mp hμ''
          · rw [ite_eq_right hμ']
            rcases central_idempotent_scalar_zero_or_one wb _
              (embeddedIdempotent_central P E hEW hW eb μ')
              (embeddedIdempotent_isIdempotent P E hEW eb μ') β' with h | h
            · exact h
            · exact absurd (support_unique P E hEW hW wb eb
                ((mem_idempotentSupport P E hEW wb eb μ' β').mpr h) hμ'') hμ'
        rw [Finset.sum_congr rfl fun μ' _ => hterm μ', Finset.sum_ite_eq']
        split_ifs <;> simp
      change localizedComplexIntegerResidue ideal (localCentralCharacterHom wb ideal β' _) = _
      rw [hloc]
      split_ifs <;> simp
    have h3 : χ' ∈ T ↔ μ'' ∈ Ω := by
      have h12 := h1.symm.trans h2
      by_cases hT' : χ' ∈ T <;> by_cases hΩ' : μ'' ∈ Ω <;> simp [hT', hΩ'] at h12 ⊢
    rw [h3, sameCoefficientBlock_iff_centralCharacterResidueHom_eq, ← hχ, ← hβ',
      brauer_eq_iff P E hPab hEW hPE hW wb eb hb ideal hPp hEp hβ hβ'idem]
    simp only [hΩ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hTeq : T = coefficientBlock hb (localizedComplexIntegerRing ideal) χ := by
    ext χ'
    rw [coefficientBlock_mem_iff]
    exact hTiff χ'
  rw [← hTeq, ← hT]

end Blocks

omit [Fintype H] in
theorem subtype_mapDomain {M N : Type*} [Monoid M] [Monoid N] (ring : Subring ℂ) (f : M →* N)
    (x : MonoidAlgebra ring M) :
    MonoidAlgebra.mapRingHom N ring.subtype (MonoidAlgebra.mapDomainRingHom ring f x) =
      MonoidAlgebra.mapDomainRingHom ℂ f (MonoidAlgebra.mapRingHom M ring.subtype x) := by
  have hcomp : (MonoidAlgebra.mapRingHom N ring.subtype).comp
      (MonoidAlgebra.mapDomainRingHom ring f) =
      (MonoidAlgebra.mapDomainRingHom ℂ f).comp (MonoidAlgebra.mapRingHom M ring.subtype) := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
    · intro m
      simp only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
  exact RingHom.congr_fun hcomp x

end OrbitIdempotents

theorem normal_abelian_p_centralizer_orbit_idempotents {H : Type*} [Group H] [Fintype H]
    (hb : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Subgroup H) [P.Normal] (hPp : IsPGroup p P) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (E : Subgroup H) (hEW : E ≤ Subgroup.centralizer (P : Set H)) (hEp : ¬ p ∣ Nat.card E)
    (hPE : P ⊓ E = ⊥)
    (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E, w = a * x)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (eb : FiniteIrreducibleCharacterBasis E) :
    E.Normal ∧
    (∀ (h : H) (μ : eb.index), ∃! μ' : eb.index, ConjugateLabel E eb h μ μ') ∧
    (∀ μ : eb.index, coefficientBlock eb (localizedComplexIntegerRing ideal) μ = {μ} ∧
      MonoidAlgebra.mapRingHom E (localizedComplexIntegerRing ideal).subtype
          (blockIdempotent ideal eb μ) =
        complexCharacterIdempotent (eb.representation μ).character) ∧
    (∀ (μ : eb.index) (β : wb.index),
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) ↔
        MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal) (Subgroup.inclusion hEW)
          (blockIdempotent ideal eb μ) = blockIdempotent ideal wb β) ∧
    (∀ μ : eb.index, ∃ β : wb.index,
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) ∧
        ∀ β' : wb.index,
          characterSubsetIdempotent wb
              (coefficientBlock wb (localizedComplexIntegerRing ideal) β') =
            MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
              (complexCharacterIdempotent (eb.representation μ).character) →
          sameCoefficientBlock wb (localizedComplexIntegerRing ideal) β β') ∧
    (∀ β : wb.index, ∃ μ : eb.index,
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
        MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
          (complexCharacterIdempotent (eb.representation μ).character)) ∧
    (∀ (h : H) (μ μ' : eb.index) (β β' : wb.index), ConjugateLabel E eb h μ μ' →
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) →
      LabelTransport wb wb (normalCentralizerConj P h) β β' →
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β') =
        MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
          (complexCharacterIdempotent (eb.representation μ').character)) ∧
    (∀ β : wb.index, ∃ χ : hb.index,
      brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) wb β = centralCharacterResidueHom hb ideal χ) ∧
    (∀ (μ μ' : eb.index) (β β' : wb.index),
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) →
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β') =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ').character) →
      (brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) wb β =
        brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H))
          le_rfl (Subgroup.centralizer_le_normalizer _) wb β' ↔
        ∃ h : H, ConjugateLabel E eb h μ μ')) ∧
    (∀ χ : hb.index, ∃ (μ : eb.index) (β : wb.index),
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) ∧
        brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) wb β = centralCharacterResidueHom hb ideal χ) ∧
    (∀ (χ : hb.index) (μ : eb.index) (β : wb.index),
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) →
      brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) wb β = centralCharacterResidueHom hb ideal χ →
      characterSubsetIdempotent hb (coefficientBlock hb (localizedComplexIntegerRing ideal) χ) =
          ∑ μ' ∈ Finset.univ.filter (fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ'),
            MonoidAlgebra.mapDomainRingHom ℂ E.subtype
              (complexCharacterIdempotent (eb.representation μ').character) ∧
        blockIdempotent ideal hb χ =
          ∑ μ' ∈ Finset.univ.filter (fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ'),
            MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal) E.subtype
              (blockIdempotent ideal eb μ')) := by
  have hEnormal : E.Normal := complement_normal P E hPp hEW hEp hPE hW
  have hfiber := normal_p_centralizer_brauer_fibers_are_block_orbits hb ideal p P hPp wb
  have hiff : ∀ μ β, characterSubsetIdempotent wb
      (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
        MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
          (complexCharacterIdempotent (eb.representation μ).character) ↔
      β ∈ idempotentSupport P E hEW wb eb μ :=
    fun μ β => blockIdempotent_eq_iff_mem P E hPab hEW hPE hW wb eb ideal hPp hEp μ β
  have hsingle : ∀ μ, coefficientBlock eb (localizedComplexIntegerRing ideal) μ = {μ} := fun μ =>
    (full_prime_part_character_degree_singleton_block_singular_vanishing eb ideal p μ (by
      rw [Nat.factorization_eq_zero_of_not_dvd hEp, pow_zero]
      exact one_dvd _)).1
  have hblockE : ∀ μ, MonoidAlgebra.mapRingHom E (localizedComplexIntegerRing ideal).subtype
      (blockIdempotent ideal eb μ) = complexCharacterIdempotent (eb.representation μ).character :=
    fun μ => by rw [blockIdempotent_map_subtype, hsingle μ, characterSubsetIdempotent_singleton]
  have hformula : ∀ (χ : hb.index) (μ : eb.index) (β : wb.index),
      characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
          MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
            (complexCharacterIdempotent (eb.representation μ).character) →
      brauerNormalizerCharacterResidueHom ideal p P hPp (Subgroup.centralizer (P : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) wb β = centralCharacterResidueHom hb ideal χ →
      characterSubsetIdempotent hb (coefficientBlock hb (localizedComplexIntegerRing ideal) χ) =
        ∑ μ' ∈ Finset.univ.filter (fun μ' => ∃ h : H, ConjugateLabel E eb h μ μ'),
          MonoidAlgebra.mapDomainRingHom ℂ E.subtype
            (complexCharacterIdempotent (eb.representation μ').character) := by
    intro χ μ β hβ hχ
    rw [orbit_blockIdempotent P E hPab hEW hPE hW wb eb hb ideal hPp hEp hβ hχ,
      characterSubsetIdempotent_eq_sum, map_sum]
  refine ⟨hEnormal, fun h μ => conjugateLabel_existsUnique E eb h μ,
    fun μ => ⟨hsingle μ, hblockE μ⟩, ?_, ?_, ?_, ?_, hfiber.1, ?_, ?_, ?_⟩
  · intro μ β
    constructor
    · intro h
      apply groupAlgebraCoefficientEmbedding_injective (localizedComplexIntegerRing ideal)
      rw [subtype_mapDomain, hblockE, blockIdempotent_map_subtype, h]
    · intro h
      have h' := congrArg
        (MonoidAlgebra.mapRingHom _ (localizedComplexIntegerRing ideal).subtype) h
      rw [subtype_mapDomain, hblockE, blockIdempotent_map_subtype] at h'
      exact h'.symm
  · intro μ
    obtain ⟨β, hβ⟩ := support_nonempty P E hEW hW wb eb μ
    refine ⟨β, (hiff μ β).mpr hβ, fun β' hβ' => ?_⟩
    rw [← coefficientBlock_mem_iff,
      coefficientBlock_eq_support P E hPab hEW hPE hW wb eb ideal hPp hEp hβ]
    exact (hiff μ β').mp hβ'
  · intro β
    obtain ⟨μ, hμ⟩ := exists_mem_support P E hEW hW wb eb β
    exact ⟨μ, (hiff μ β).mpr hμ⟩
  · intro h μ μ' β β' hμ hβ htrans
    exact block_transport P E hPab hEW hPE hW wb eb ideal hPp hEp h hμ hβ htrans
  · intro μ μ' β β' hβ hβ'
    exact brauer_eq_iff P E hPab hEW hPE hW wb eb hb ideal hPp hEp hβ hβ'
  · intro χ
    obtain ⟨β, hβ⟩ := hfiber.2.1 χ
    obtain ⟨μ, hμ⟩ := exists_mem_support P E hEW hW wb eb β
    exact ⟨μ, β, (hiff μ β).mpr hμ, hβ⟩
  · intro χ μ β hβ hχ
    refine ⟨hformula χ μ β hβ hχ, ?_⟩
    apply groupAlgebraCoefficientEmbedding_injective (localizedComplexIntegerRing ideal)
    rw [blockIdempotent_map_subtype, map_sum, hformula χ μ β hβ hχ]
    refine Finset.sum_congr rfl fun μ' _ => ?_
    rw [subtype_mapDomain, hblockE]

end CFSG.Semidihedral.Principal
