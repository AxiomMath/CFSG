module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CentralExtensions
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem mem_fixedSubgroup_iff {a : MulAut G} {x : G} : x ∈ fixedSubgroup a ↔ a x = x :=
  Iff.rfl

theorem apply_mem_center (a : MulAut G) {z : G} (hz : z ∈ center G) : a z ∈ center G :=
  mem_center_iff.mpr fun g => by
    obtain ⟨y, rfl⟩ := a.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]

@[expose] def centralDisplacement (a : MulAut G) {T : Subgroup G}
    (hT : ∀ x ∈ T, x⁻¹ * a x ∈ center G) : T →* G where
  toFun x := (x : G)⁻¹ * a x
  map_one' := by simp
  map_mul' x y := by
    have hc := mem_center_iff.mp (hT x x.2) (y : G)⁻¹
    change ((x : G) * y)⁻¹ * a ((x : G) * y) = ((x : G)⁻¹ * a x) * ((y : G)⁻¹ * a y)
    rw [map_mul, mul_inv_rev]
    calc (y : G)⁻¹ * (x : G)⁻¹ * (a x * a y) = (y : G)⁻¹ * ((x : G)⁻¹ * a x) * a y := by group
      _ = (x : G)⁻¹ * a x * (y : G)⁻¹ * a y := by rw [hc]
      _ = (x : G)⁻¹ * a x * ((y : G)⁻¹ * a y) := by group

theorem centralDisplacement_apply (a : MulAut G) {T : Subgroup G}
    (hT : ∀ x ∈ T, x⁻¹ * a x ∈ center G) (x : T) :
    centralDisplacement a hT x = (x : G)⁻¹ * a x :=
  rfl

@[expose] def centralNorm {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) : K →* G where
  toFun k := (k : G) * a k
  map_one' := by simp
  map_mul' x y := by
    have hy := mem_center_iff.mp (hK y.2) (a x)
    change (x : G) * y * a ((x : G) * y) = (x : G) * a x * ((y : G) * a y)
    rw [map_mul]
    calc (x : G) * y * (a x * a y) = (x : G) * (a x * y) * a y := by rw [hy]; group
      _ = (x : G) * a x * ((y : G) * a y) := by group

@[expose] def centralSquare {F : Subgroup G} (hF : F ≤ center G) : F →* G where
  toFun f := (f : G) ^ 2
  map_one' := by simp
  map_mul' x y := by
    change ((x : G) * y) ^ 2 = (x : G) ^ 2 * (y : G) ^ 2
    exact Commute.mul_pow (mem_center_iff.mp (hF y.2) x) 2

@[expose] def normKernel {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) : Subgroup G :=
  (centralNorm hK a).ker.map K.subtype

@[expose] def centralDifference {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) : K →* G :=
  centralDisplacement a fun _ hk => mul_mem (inv_mem (hK hk)) (apply_mem_center a (hK hk))

@[expose] def differenceImage {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) :
    Subgroup G :=
  (centralDifference hK a).range

@[expose] def squareImage {F : Subgroup G} (hF : F ≤ center G) : Subgroup G :=
  (centralSquare hF).range

variable {K : Subgroup G} {hK : K ≤ center G} {a : MulAut G}

theorem mem_normKernel {x : G} : x ∈ normKernel hK a ↔ x ∈ K ∧ x * a x = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_differenceImage {x : G} : x ∈ differenceImage hK a ↔ ∃ k ∈ K, k⁻¹ * a k = x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem mem_squareImage {F : Subgroup G} {hF : F ≤ center G} {x : G} :
    x ∈ squareImage hF ↔ ∃ f ∈ F, f ^ 2 = x := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, f.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

theorem normKernel_le : normKernel hK a ≤ K := fun _ hx => (mem_normKernel.mp hx).1

instance isMulCommutative_normKernel (hK : K ≤ center G) (a : MulAut G) :
    IsMulCommutative (normKernel hK a) :=
  isMulCommutative_iff.mpr fun x y =>
    Subtype.ext (mem_center_iff.mp (hK (normKernel_le y.2)) x)

theorem sq_mem_differenceImage {j : G} (hj : j ∈ normKernel hK a) :
    j ^ 2 ∈ differenceImage hK a := by
  obtain ⟨hjK, hj1⟩ := mem_normKernel.mp hj
  have haj : a j = j⁻¹ := eq_inv_of_mul_eq_one_right hj1
  refine mem_differenceImage.mpr ⟨j⁻¹, inv_mem hjK, ?_⟩
  rw [inv_inv, map_inv, haj, inv_inv, sq]

theorem isElementaryAbelian_normKernel_quotient :
    IsElementaryAbelian 2
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) := by
  have hcomm : IsMulCommutative
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) := by
    refine isMulCommutative_iff.mpr fun x y => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      isMulCommutative_iff.mp inferInstance x y]
  refine
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_ }
  induction x using QuotientGroup.induction_on with | H j => ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact sq_mem_differenceImage j.2

theorem card_normKernel_quotient_eq_two_pow [Finite G] :
    ∃ n : ℕ, Nat.card
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) = 2 ^ n := by
  have := isElementaryAbelian_normKernel_quotient (hK := hK) (a := a)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (IsElementaryAbelian.isPGroup 2 _).exists_card_eq

theorem relIndex_squareImage_eq_card [Finite G] {F : Subgroup G} (hF : F ≤ center G) :
    (squareImage hF).relIndex F = Nat.card {f : F // (f : G) ^ 2 = 1} := by
  have hle : squareImage hF ≤ F := by
    rintro _ ⟨f, rfl⟩
    exact pow_mem f.2 2
  have h1 := relIndex_mul_card (squareImage hF) F
  rw [inf_eq_left.mpr hle] at h1
  have h2 := card_mul_index (centralSquare hF).ker
  rw [index_ker] at h2
  have hker : Nat.card (centralSquare hF).ker = Nat.card {f : F // (f : G) ^ 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [hker] at h2
  have hpos : 0 < Nat.card (squareImage hF) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem not_sylow_map_le_of_mem [Finite G] {p : ℕ} [Fact p.Prime] {H Z : Subgroup G}
    (hZ : Z ≤ center G) {x : G} (hxH : x ∈ H) (hx : ∃ n : ℕ, orderOf x = p ^ n) (hxZ : x ∉ Z)
    (R : Sylow p H) : ¬ (R : Subgroup H).map H.subtype ≤ Z := by
  intro hR
  have hRc : (R : Subgroup H) ≤ center H := fun r hr =>
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hZ (hR (mem_map_of_mem _ hr))) g)
  have : (R : Subgroup H).Normal := normal_of_le_center hRc
  obtain ⟨n, hn⟩ := hx
  have hp : IsPGroup p (zpowers (⟨x, hxH⟩ : H)) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, orderOf_mk, hn])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R Q
  rw [Sylow.smul_eq_of_normal] at hg
  subst hg
  exact hxZ (hR (mem_map_of_mem _ (hQ (mem_zpowers _))))

theorem exists_odd_pow_orderOf_eq_two_pow [Finite G] (z : G) :
    ∃ m : ℕ, Odd m ∧ ∃ n : ℕ, orderOf (z ^ m) = 2 ^ n := by
  obtain ⟨n, m, hm, h⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨m, hm, n, ?_⟩
  rw [orderOf_pow_of_dvd hm.pos.ne' (Dvd.intro_left _ h.symm), h, Nat.mul_div_cancel _ hm.pos]

theorem pow_ne_one_of_odd {y : G} {n : ℕ} (hy : y ^ 2 ^ n = 1) (hy1 : y ≠ 1) {m : ℕ}
    (hm : Odd m) : y ^ m ≠ 1 := by
  intro h
  apply hy1
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (orderOf_dvd_of_pow_eq_one h)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
  exact orderOf_eq_one_iff.mp hdvd

theorem isElementaryAbelian_of_injective {p : ℕ} {H : Type*} [Group H]
    [hH : IsElementaryAbelian p H] {f : G →* H} (hf : Function.Injective f) :
    IsElementaryAbelian p G := by
  have hcomm : IsMulCommutative G := isMulCommutative_iff.mpr fun x y =>
    hf (by rw [map_mul, map_mul, isMulCommutative_iff.mp inferInstance (f x) (f y)])
  refine
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => hf ?_ }
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hH.exponent_dvd_p (f x)

theorem mem_ker_centralDifference {k : K} : k ∈ (centralDifference hK a).ker ↔ a k = k := by
  rw [MonoidHom.mem_ker]
  change (k : G)⁻¹ * a k = 1 ↔ _
  rw [inv_mul_eq_one, eq_comm]

theorem card_normKernel_mul_card_range [Finite G] :
    Nat.card (normKernel hK a) * Nat.card (centralNorm hK a).range = Nat.card K := by
  rw [normKernel, card_map_of_injective K.subtype_injective, ← index_ker, card_mul_index]

theorem card_fixed_mul_card_differenceImage [Finite G] :
    Nat.card (K ⊓ fixedSubgroup a : Subgroup G) * Nat.card (differenceImage hK a) = Nat.card K := by
  have hmap : (centralDifference hK a).ker.map K.subtype = K ⊓ fixedSubgroup a := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, mem_ker_centralDifference.mp hk⟩
    · rintro ⟨hxK, hxa⟩
      exact ⟨⟨x, hxK⟩, mem_ker_centralDifference.mpr hxa, rfl⟩
  rw [← hmap, card_map_of_injective K.subtype_injective, differenceImage, ← index_ker,
    card_mul_index]

theorem range_centralNorm_le (ha : ∀ x, a (a x) = x) (hKa : ∀ k ∈ K, a k ∈ K) :
    (centralNorm hK a).range ≤ K ⊓ fixedSubgroup a := by
  rintro _ ⟨k, rfl⟩
  refine ⟨mul_mem k.2 (hKa k k.2), ?_⟩
  change a ((k : G) * a k) = k * a k
  rw [map_mul, ha]
  exact mem_center_iff.mp (hK k.2) (a k)

theorem squareImage_le_range_centralNorm :
    squareImage (F := K ⊓ fixedSubgroup a) (inf_le_left.trans hK) ≤
      (centralNorm hK a).range := by
  rintro _ ⟨f, rfl⟩
  refine ⟨⟨f, f.2.1⟩, ?_⟩
  change (f : G) * a f = (f : G) ^ 2
  rw [mem_fixedSubgroup_iff.mp f.2.2, sq]

theorem differenceImage_le_normKernel_of (ha : ∀ x, a (a x) = x) (hKa : ∀ k ∈ K, a k ∈ K) :
    differenceImage hK a ≤ normKernel hK a := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := mem_differenceImage.mp hb
  refine mem_normKernel.mpr ⟨mul_mem (inv_mem hk) (hKa k hk), ?_⟩
  rw [map_mul, map_inv, ha]
  group

theorem relIndex_differenceImage_le_of [Finite G] (ha : ∀ x, a (a x) = x)
    (hKa : ∀ k ∈ K, a k ∈ K) :
    (differenceImage hK a).relIndex (normKernel hK a) ≤
      (squareImage (F := K ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
        (K ⊓ fixedSubgroup a) := by
  have hBJ := differenceImage_le_normKernel_of ha hKa (hK := hK)
  have hsq : squareImage (F := K ⊓ fixedSubgroup a) (inf_le_left.trans hK) ≤
      K ⊓ fixedSubgroup a :=
    (squareImage_le_range_centralNorm (hK := hK)).trans (range_centralNorm_le ha hKa)
  have e1 := relIndex_mul_card (differenceImage hK a) (normKernel hK a)
  rw [inf_eq_left.mpr hBJ] at e1
  have e2 := card_normKernel_mul_card_range (hK := hK) (a := a)
  have e3 := card_fixed_mul_card_differenceImage (hK := hK) (a := a)
  have e4 := relIndex_mul_card (squareImage (F := K ⊓ fixedSubgroup a) (inf_le_left.trans hK))
    (K ⊓ fixedSubgroup a)
  rw [inf_eq_left.mpr hsq] at e4
  have e5 := card_le_of_le (squareImage_le_range_centralNorm (hK := hK) (a := a))
  have hb : 0 < Nat.card (differenceImage hK a) := Nat.card_pos
  have hn : 0 < Nat.card (centralNorm hK a).range := Nat.card_pos
  have h6 : (differenceImage hK a).relIndex (normKernel hK a) * Nat.card (centralNorm hK a).range =
      Nat.card (K ⊓ fixedSubgroup a : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_right hb
    rw [mul_right_comm, e1, e2, e3]
  refine Nat.le_of_mul_le_mul_right ?_ hn
  rw [h6, ← e4]
  exact Nat.mul_le_mul_left _ e5

end General

section CentralKernel

variable {L S : Type*} [Group L] [Group S] {π : L →* S} {a : MulAut L} {α : MulAut S}

theorem apply_mem_ker (hcomm : ∀ x, π (a x) = α (π x)) {k : L} (hk : k ∈ π.ker) :
    a k ∈ π.ker := by
  rw [MonoidHom.mem_ker] at hk ⊢
  rw [hcomm, hk, map_one]

theorem inv_mul_apply_mem_ker (hcomm : ∀ x, π (a x) = α (π x)) {x : L} (hx : α (π x) = π x) :
    x⁻¹ * a x ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, hx, inv_mul_cancel]

theorem fixedPerfectLift (hπ : Function.Surjective π) (hK : π.ker ≤ center L)
    (hcomm : ∀ x, π (a x) = α (π x)) (P : Subgroup S) [Group.IsPerfect P]
    (hP : ∀ s ∈ P, α s = s) :
    Group.IsPerfect ↥⁅P.comap π, P.comap π⁆ ∧ ⁅P.comap π, P.comap π⁆.map π = P ∧
      ∀ x ∈ ⁅P.comap π, P.comap π⁆, a x = x := by
  set D := P.comap π with hD
  have hdisp : ∀ x ∈ D, x⁻¹ * a x ∈ center L := fun x hx =>
    hK (inv_mul_apply_mem_ker hcomm (hP _ hx))
  have hfix : ⁅D, D⁆ ≤ fixedSubgroup a := by
    rw [commutator_le]
    intro x hx y hy
    change a ⁅x, y⁆ = ⁅x, y⁆
    calc a ⁅x, y⁆ = ⁅a x, a y⁆ := map_commutatorElement a x y
      _ = ⁅x * (x⁻¹ * a x), y * (y⁻¹ * a y)⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
      _ = ⁅x, y⁆ := by
        rw [commutator_mul_center_left _ _ _ (hdisp x hx),
          commutator_mul_center_right _ _ _ (hdisp y hy)]
  have hmap : ⁅D, D⁆.map π = P := by
    rw [map_commutator, map_comap_eq_self_of_surjective hπ, commutator_eq_self]
  have hsup : ⁅D, D⁆ ⊔ π.ker = D := by
    rw [← comap_map_eq, hmap]
  have hperf : ⁅⁅D, D⁆, ⁅D, D⁆⁆ = ⁅D, D⁆ := by
    conv_rhs => rw [← hsup]
    exact (commutator_sup_central _ _ hK).symm
  exact ⟨isPerfect_iff.mpr hperf, hmap, fun x hx => hfix hx⟩

theorem not_sylow_le_ker_of_even [Finite L] (hπ : Function.Surjective π)
    (hK : π.ker ≤ center L) (hcomm : ∀ x, π (a x) = α (π x)) (P : Subgroup S)
    [Group.IsPerfect P] (hP : ∀ s ∈ P, α s = s) (heven : Even (Nat.card P))
    (R : Sylow 2 (fixedSubgroup a)) :
    ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker := by
  obtain ⟨-, hmap, hfix⟩ := fixedPerfectLift hπ hK hcomm P hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := Finite.of_surjective _ (π.subgroupComap_surjective P hπ)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (even_iff_two_dvd.mp heven)
  have hsmem : (s : S) ∈ ⁅P.comap π, P.comap π⁆.map π := by
    rw [hmap]
    exact s.2
  obtain ⟨y, hy, hys⟩ := mem_map.mp hsmem
  obtain ⟨m, hm, n, hn⟩ := exists_odd_pow_orderOf_eq_two_pow y
  have hs2 : (s : S) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hs, ← orderOf_coe, pow_orderOf_eq_one]
  have hs1 : (s : S) ≠ 1 := by
    intro h
    have h' : s = 1 := Subtype.ext h
    rw [h', orderOf_one] at hs
    exact absurd hs (by norm_num)
  refine not_sylow_map_le_of_mem hK (hfix _ (pow_mem hy m)) ⟨n, hn⟩ ?_ R
  rw [MonoidHom.mem_ker, map_pow, hys]
  exact pow_ne_one_of_odd hs2 hs1 hm

theorem not_sylow_le_center_of_even [Finite L] (hπ : Function.Surjective π)
    (hK : π.ker = center L) (hcomm : ∀ x, π (a x) = α (π x)) (P : Subgroup S)
    [Group.IsPerfect P] (hP : ∀ s ∈ P, α s = s) (heven : Even (Nat.card P))
    (R : Sylow 2 (fixedSubgroup a)) :
    ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ center L := by
  rw [← hK]
  exact not_sylow_le_ker_of_even hπ hK.le hcomm P hP heven R

variable (hK : π.ker ≤ center L)

theorem inv_mul_apply_mem_normKernel (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    {x : L} (hx : π x ∈ fixedSubgroup α) : x⁻¹ * a x ∈ normKernel hK a := by
  refine mem_normKernel.mpr ⟨inv_mul_apply_mem_ker hcomm hx, ?_⟩
  rw [map_mul, map_inv, ha]
  group

theorem differenceImage_le_normKernel (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) : differenceImage hK a ≤ normKernel hK a :=
  differenceImage_le_normKernel_of ha fun _ hk => apply_mem_ker hcomm hk

theorem exists_fixedImageHom (hπ : Function.Surjective π) (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    ∃ θ : fixedSubgroup α →*
        normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a),
      (∀ (x : L) (hx : π x ∈ fixedSubgroup α) (hxJ : x⁻¹ * a x ∈ normKernel hK a),
        θ ⟨π x, hx⟩ = ((⟨x⁻¹ * a x, hxJ⟩ : normKernel hK a) :
          normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a))) ∧
      θ.ker = ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α) := by
  set T := (fixedSubgroup α).comap π
  have hT : ∀ x ∈ T, x⁻¹ * a x ∈ center L := fun x hx => hK (inv_mul_apply_mem_ker hcomm hx)
  let δ : T →* normKernel hK a := (centralDisplacement a hT).codRestrict _
    fun x => inv_mul_apply_mem_normKernel hK ha hcomm x.2
  let q := QuotientGroup.mk' ((differenceImage hK a).subgroupOf (normKernel hK a))
  let πT := π.subgroupComap (fixedSubgroup α)
  have hsurj : Function.Surjective πT := π.subgroupComap_surjective _ hπ
  have hker : πT.ker ≤ (q.comp δ).ker := by
    intro x hx
    have hxK : (x : L) ∈ π.ker := congrArg Subtype.val hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact mem_differenceImage.mpr ⟨x, hxK, rfl⟩
  let θ := πT.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
    ⟨q.comp δ, hker⟩
  have hθ : ∀ x : T, θ (πT x) = q (δ x) := fun x =>
    πT.liftOfRightInverse_comp_apply _ _ ⟨q.comp δ, hker⟩ x
  refine ⟨θ, fun x hx _ => hθ ⟨x, hx⟩, ?_⟩
  ext c
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := hsurj c
    rw [hθ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    obtain ⟨k, hk, hkx⟩ := mem_differenceImage.mp h
    have hkx' : k⁻¹ * a k = (x : L)⁻¹ * a x := hkx
    refine ⟨x * k⁻¹, ?_, ?_⟩
    · have hax : a x = x * (k⁻¹ * a k) := by rw [hkx']; group
      change a ((x : L) * k⁻¹) = x * k⁻¹
      rw [map_mul, map_inv, hax]
      group
    · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, mul_one]
      rfl
  · rintro ⟨y, hy, hyc⟩
    have hyT : y ∈ T := by
      change α (π y) = π y
      rw [← hcomm, mem_fixedSubgroup_iff.mp hy]
    have hc : c = πT ⟨y, hyT⟩ := Subtype.ext hyc.symm
    rw [hc, hθ]
    have hδ : δ ⟨y, hyT⟩ = 1 := Subtype.ext (by
      change y⁻¹ * a y = 1
      rw [mem_fixedSubgroup_iff.mp hy, inv_mul_cancel])
    rw [hδ, map_one]

theorem fixedImage_normal (hK : π.ker ≤ center L) (hπ : Function.Surjective π)
    (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    (((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)).Normal := by
  obtain ⟨θ, -, hθ⟩ := exists_fixedImageHom hK hπ ha hcomm
  rw [← hθ]
  infer_instance

theorem fixedImage_quotient_embedding (hπ : Function.Surjective π) (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    ∃ _ : (((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)).Normal,
      (∃ φ : fixedSubgroup α ⧸ ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α) →*
          normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a),
        Function.Injective φ) ∧
      IsElementaryAbelian 2
        (fixedSubgroup α ⧸ ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)) := by
  obtain ⟨θ, -, hθ⟩ := exists_fixedImageHom hK hπ ha hcomm
  have hN := fixedImage_normal hK hπ ha hcomm
  refine ⟨hN, ?_⟩
  let φ := (QuotientGroup.kerLift θ).comp (QuotientGroup.quotientMulEquivOfEq hθ.symm).toMonoidHom
  have hφ : Function.Injective φ :=
    (QuotientGroup.kerLift_injective θ).comp (MulEquiv.injective _)
  have := isElementaryAbelian_normKernel_quotient (hK := hK) (a := a)
  exact ⟨⟨φ, hφ⟩, isElementaryAbelian_of_injective hφ⟩

theorem relIndex_fixedImage_le [Finite L] (hπ : Function.Surjective π) (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    ((fixedSubgroup a).map π).relIndex (fixedSubgroup α) ≤
      (differenceImage hK a).relIndex (normKernel hK a) := by
  obtain ⟨θ, -, hθ⟩ := exists_fixedImageHom hK hπ ha hcomm
  rw [relIndex, ← hθ, index_ker, relIndex, index_eq_card]
  exact card_le_card_group θ.range

theorem relIndex_differenceImage_le [Finite L] (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    (differenceImage hK a).relIndex (normKernel hK a) ≤
      (squareImage (F := π.ker ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
        (π.ker ⊓ fixedSubgroup a) :=
  relIndex_differenceImage_le_of ha fun _ hk => apply_mem_ker hcomm hk

theorem exists_fixed_two_element [Finite L] (hπ : Function.Surjective π)
    (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x)) {V : Subgroup S}
    (hV : IsPGroup 2 V) (hVfix : ∀ v ∈ V, α v = v)
    (hcard : (squareImage (F := π.ker ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
      (π.ker ⊓ fixedSubgroup a) < Nat.card V) :
    ∃ x ∈ fixedSubgroup a, (∃ n : ℕ, orderOf x = 2 ^ n) ∧ π x ∈ V ∧ π x ≠ 1 ∧ x ∉ π.ker := by
  obtain ⟨θ, -, hθ⟩ := exists_fixedImageHom hK hπ ha hcomm
  have : Finite S := Finite.of_surjective _ hπ
  have hVC : V ≤ fixedSubgroup α := fun v hv => hVfix v hv
  let θV := θ.comp (inclusion hVC)
  have hnotinj : ¬ Function.Injective θV := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective θV hinj
    have h2 := relIndex_differenceImage_le hK ha hcomm
    rw [relIndex, index_eq_card] at h2
    omega
  rw [injective_iff_map_eq_one] at hnotinj
  push Not at hnotinj
  obtain ⟨v, hθv, hv1⟩ := hnotinj
  have hvI : inclusion hVC v ∈ θ.ker := hθv
  rw [hθ, mem_subgroupOf] at hvI
  obtain ⟨z, hz, hzv⟩ := hvI
  obtain ⟨m, hm, n, hn⟩ := exists_odd_pow_orderOf_eq_two_pow z
  have hvS : (v : S) ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨e, he⟩ := hV v
  have hve : (v : S) ^ 2 ^ e = 1 := by
    rw [← coe_pow, he, coe_one]
  have hzm : π (z ^ m) = (v : S) ^ m := by
    rw [map_pow, hzv]
    rfl
  have hne : π (z ^ m) ≠ 1 := by
    rw [hzm]
    exact pow_ne_one_of_odd hve hvS hm
  refine ⟨z ^ m, pow_mem hz m, ⟨n, hn⟩, ?_, hne, fun h => hne (MonoidHom.mem_ker.mp h)⟩
  rw [hzm]
  exact pow_mem v.2 m

theorem exists_fixed_two_element' [Finite L] (hK : π.ker ≤ center L)
    (hπ : Function.Surjective π) (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    {V : Subgroup S} (hV : IsPGroup 2 V) (hVfix : ∀ v ∈ V, α v = v)
    (hcard : Nat.card {f : (π.ker ⊓ fixedSubgroup a : Subgroup L) // (f : L) ^ 2 = 1} <
      Nat.card V) :
    ∃ x ∈ fixedSubgroup a, (∃ n : ℕ, orderOf x = 2 ^ n) ∧ π x ∈ V ∧ π x ≠ 1 ∧ x ∉ π.ker :=
  exists_fixed_two_element hK hπ ha hcomm hV hVfix
    ((relIndex_squareImage_eq_card (inf_le_left.trans hK)).trans_lt hcard)

theorem not_sylow_le_ker_of_card_lt [Finite L] (hπ : Function.Surjective π)
    (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x)) {V : Subgroup S}
    (hV : IsPGroup 2 V) (hVfix : ∀ v ∈ V, α v = v)
    (hcard : (squareImage (F := π.ker ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
      (π.ker ⊓ fixedSubgroup a) < Nat.card V)
    (R : Sylow 2 (fixedSubgroup a)) :
    ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxa, hx2, -, -, hxK⟩ := exists_fixed_two_element hK hπ ha hcomm hV hVfix hcard
  exact not_sylow_map_le_of_mem hK hxa hx2 hxK R

theorem fixed_perfect_quotient_subgroup_lifts_through_full_center [Finite L] [Finite S]
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) (hcomm : ∀ x, π (a x) = α (π x))
    (P : Subgroup S) [Group.IsPerfect P] (hP : ∀ s ∈ P, α s = s) :
    (Group.IsPerfect ↥⁅P.comap π, P.comap π⁆ ∧ ⁅P.comap π, P.comap π⁆.map π = P ∧
      ∀ x ∈ ⁅P.comap π, P.comap π⁆, a x = x) ∧
    (Even (Nat.card P) → ∀ R : Sylow 2 (fixedSubgroup a),
      ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker) ∧
    (π.ker = center L → Even (Nat.card P) → ∀ R : Sylow 2 (fixedSubgroup a),
      ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ center L) :=
  ⟨fixedPerfectLift hπ hK hcomm P hP, not_sylow_le_ker_of_even hπ hK hcomm P hP,
    fun hZ => not_sylow_le_center_of_even hπ hZ hcomm P hP⟩

theorem full_central_kernel_involution_fixed_image_quotient [Finite L] [Finite S]
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) (ha : ∀ x, a (a x) = x)
    (_hα : ∀ s, α (α s) = s) (hcomm : ∀ x, π (a x) = α (π x)) :
    differenceImage hK a ≤ normKernel hK a ∧
    IsElementaryAbelian 2
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) ∧
    (∃ n : ℕ, Nat.card
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) = 2 ^ n) ∧
    (∃ θ : fixedSubgroup α →*
        normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a),
      (∀ (x : L) (hx : π x ∈ fixedSubgroup α) (hxJ : x⁻¹ * a x ∈ normKernel hK a),
        θ ⟨π x, hx⟩ = ((⟨x⁻¹ * a x, hxJ⟩ : normKernel hK a) :
          normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a))) ∧
      θ.ker = ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)) ∧
    (∃ _ : (((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)).Normal,
      (∃ φ : fixedSubgroup α ⧸ ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α) →*
          normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a),
        Function.Injective φ) ∧
      IsElementaryAbelian 2
        (fixedSubgroup α ⧸ ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α))) ∧
    ((fixedSubgroup a).map π).relIndex (fixedSubgroup α) ≤
      (differenceImage hK a).relIndex (normKernel hK a) ∧
    (differenceImage hK a).relIndex (normKernel hK a) ≤
      (squareImage (F := π.ker ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
        (π.ker ⊓ fixedSubgroup a) :=
  ⟨differenceImage_le_normKernel hK ha hcomm, isElementaryAbelian_normKernel_quotient,
    card_normKernel_quotient_eq_two_pow, exists_fixedImageHom hK hπ ha hcomm,
    fixedImage_quotient_embedding hK hπ ha hcomm, relIndex_fixedImage_le hK hπ ha hcomm,
    relIndex_differenceImage_le hK ha hcomm⟩

theorem central_kernel_involution_fixed_quotient_rank_obstruction [Finite L] [Finite S]
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) {V : Subgroup S} (hV : IsPGroup 2 V)
    (hVfix : ∀ v ∈ V, α v = v) :
    (squareImage (F := π.ker ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
        (π.ker ⊓ fixedSubgroup a) =
      Nat.card {f : (π.ker ⊓ fixedSubgroup a : Subgroup L) // (f : L) ^ 2 = 1} ∧
    ((squareImage (F := π.ker ⊓ fixedSubgroup a) (inf_le_left.trans hK)).relIndex
        (π.ker ⊓ fixedSubgroup a) < Nat.card V →
      (∃ x ∈ fixedSubgroup a, (∃ n : ℕ, orderOf x = 2 ^ n) ∧ π x ∈ V ∧ π x ≠ 1 ∧
        x ∉ π.ker) ∧
      ∀ R : Sylow 2 (fixedSubgroup a),
        ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker) :=
  ⟨relIndex_squareImage_eq_card _, fun hcard =>
    ⟨exists_fixed_two_element hK hπ ha hcomm hV hVfix hcard,
      not_sylow_le_ker_of_card_lt hK hπ ha hcomm hV hVfix hcard⟩⟩

end CentralKernel

end CFSG.LocalAnalysis.ComponentInitial
