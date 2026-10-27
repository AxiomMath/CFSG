module

public import CFSG.ClassicalInvolution.Balance.FuzzyAdj
public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  finite_perfectResidual_surjects_to_perfect_image perfectResidualOf_normalizer_contains)
open scoped commutatorElement

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_oddCoreIn_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {y : G} (hy : y ∈ oddCoreIn X) :
    g * y * g⁻¹ ∈ oddCoreIn X := by
  have h1 : g * y * g⁻¹ ∈ conjSub g (oddCoreIn X) := by
    rw [mem_conjSub_iff]
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e]
    exact hy
  rwa [← oddCoreIn_conjSub_eq, conjSub_eq_of_mem_normalizer hg] at h1

end Normalizer

section Coset

variable {G : Type} [Group G]

theorem exists_fixed_mem_coset_of_isPGroup {A N : Subgroup G} (hA : IsPGroup 2 A)
    (hN : Odd (Nat.card N))
    (hAN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) {x : G}
    (hx : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ a ∈ A, a * (x * n) * a⁻¹ = x * n := by
  classical
  set S : Set G := {y | x⁻¹ * y ∈ N} with hS
  have hAS : ∀ a ∈ A, ∀ y ∈ S, a * y * a⁻¹ ∈ S := by
    intro a ha y hy
    have h1 := hx a ha
    have h2 := hAN a ha _ hy
    have e : x⁻¹ * (a * y * a⁻¹) = (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * y) * a⁻¹) := by group
    show x⁻¹ * (a * y * a⁻¹) ∈ N
    rw [e]
    exact N.mul_mem h1 h2
  have hcard : Nat.card S = Nat.card N :=
    Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨x * n.1, by show x⁻¹ * (x * n.1) ∈ N; simp⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Nat.card S := by
    rw [hcard]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)
  let _ : MulAction A S :=
    { smul := fun a y => ⟨(a : G) * y * (a : G)⁻¹, hAS a a.2 y y.2⟩
      one_smul := fun u => Subtype.ext
        (show ((1 : A) : G) * (u : G) * ((1 : A) : G)⁻¹ = u by simp)
      mul_smul := fun a b u => Subtype.ext
        (show ((a * b : A) : G) * (u : G) * ((a * b : A) : G)⁻¹ =
          (a : G) * ((b : G) * (u : G) * (b : G)⁻¹) * (a : G)⁻¹ by simp [mul_assoc]) }
  obtain ⟨u, hu⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hodd
  refine ⟨x⁻¹ * u, u.2, fun a ha => ?_⟩
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hu ⟨a, ha⟩)
  have h' : a * (u : G) * a⁻¹ = u := h
  rw [mul_inv_cancel_left]
  exact h'

end Coset

section Axis

variable {G : Type} [Group G] [Finite G]

@[expose] def trivialOnQuot (J : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ Subgroup.normalizer (J : Set G) ∧ ∀ x ∈ J, ⁅a, x⁆ ∈ oddCoreIn J}
  one_mem' := ⟨one_mem _, fun x _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (conj_mem_oddCoreIn_of_mem_normalizer ha (hb' x hx)) (ha' x hx)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅x, a⁆ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, ← commutatorElement_inv a x]
    exact conj_mem_oddCoreIn_of_mem_normalizer (inv_mem ha) (inv_mem (ha' x hx))

theorem mem_trivialOnQuot_iff {J : Subgroup G} {a : G} :
    a ∈ trivialOnQuot J ↔
      a ∈ Subgroup.normalizer (J : Set G) ∧ ∀ x ∈ J, ⁅a, x⁆ ∈ oddCoreIn J :=
  Iff.rfl

theorem exists_mem_inf_centralizer_mul {J A : Subgroup G} (hA : IsPGroup 2 A)
    (hAJ : A ≤ trivialOnQuot J) {x : G} (hx : x ∈ J) :
    ∃ h ∈ J ⊓ Subgroup.centralizer (A : Set G), ∃ n ∈ oddCoreIn J, x = h * n := by
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset_of_isPGroup (A := A) (N := oddCoreIn J) hA
    (odd_card_oddCoreIn J)
    (fun a ha m hm => conj_mem_oddCoreIn_of_mem_normalizer (hAJ ha).1 hm) (x := x)
    (fun a ha => by
      have h1 := (oddCoreIn J).inv_mem ((hAJ ha).2 x⁻¹ (J.inv_mem hx))
      rw [commutatorElement_inv] at h1
      have e : x⁻¹ * (a * x * a⁻¹) = ⁅x⁻¹, a⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h1)
  refine ⟨x * n, ?_, n⁻¹, (oddCoreIn J).inv_mem hn, by group⟩
  refine Subgroup.mem_inf.mpr ⟨J.mul_mem hx (oddCoreIn_le J hn), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact mul_inv_eq_iff_eq_mul.mp (hfix a ha)

end Axis

section Supplement

variable {G : Type} [Group G] [Finite G]

@[expose] def toOddQuot {J S : Subgroup G} (hSJ : S ≤ J) :
    S →* J ⧸ classicalInvolutionOddCore J :=
  (QuotientGroup.mk' (classicalInvolutionOddCore J)).comp (Subgroup.inclusion hSJ)

omit [Finite G] in
theorem mem_classicalInvolutionOddCore_of_mem_oddCoreIn {J : Subgroup G} {n : G}
    (hn : n ∈ oddCoreIn J) : (⟨n, oddCoreIn_le J hn⟩ : J) ∈ classicalInvolutionOddCore J := by
  have hnJ := oddCoreIn_le J hn
  obtain ⟨m, hm, hmn⟩ := hn
  have : m = ⟨n, hnJ⟩ := Subtype.ext hmn
  rw [← this]
  exact hm

omit [Finite G] in
theorem mem_oddCoreIn_of_mem_classicalInvolutionOddCore {J : Subgroup G} {y : J}
    (hy : y ∈ classicalInvolutionOddCore J) : (y : G) ∈ oddCoreIn J :=
  ⟨y, hy, rfl⟩

omit [Finite G] in
theorem toOddQuot_surjective {J S : Subgroup G} (hSJ : S ≤ J)
    (hcov : ∀ x ∈ J, ∃ s ∈ S, ∃ n ∈ oddCoreIn J, x = s * n) :
    Function.Surjective (toOddQuot hSJ) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore J) q
  obtain ⟨s, hs, n, hn, hxsn⟩ := hcov x x.2
  refine ⟨⟨s, hs⟩, ?_⟩
  show QuotientGroup.mk' _ (Subgroup.inclusion hSJ ⟨s, hs⟩) = QuotientGroup.mk' _ x
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have e : (Subgroup.inclusion hSJ ⟨s, hs⟩)⁻¹ * x = ⟨n, oddCoreIn_le J hn⟩ := by
    apply Subtype.ext
    simp [hxsn]
  rw [e]
  exact mem_classicalInvolutionOddCore_of_mem_oddCoreIn hn

omit [Finite G] in
theorem ker_toOddQuot {J S : Subgroup G} (hSJ : S ≤ J) :
    (toOddQuot hSJ).ker = (classicalInvolutionOddCore J).comap (Subgroup.inclusion hSJ) := by
  ext s
  simp [toOddQuot, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem classicalInvolutionOddCore_eq_ker {J S : Subgroup G} (hSJ : S ≤ J)
    (hsurj : Function.Surjective (toOddQuot hSJ)) :
    classicalInvolutionOddCore S = (toOddQuot hSJ).ker := by
  apply le_antisymm
  · intro s hs
    have hN : ((classicalInvolutionOddCore S).map (toOddQuot hSJ)).Normal :=
      Subgroup.Normal.map inferInstance (toOddQuot hSJ) hsurj
    have hodd : Odd (Nat.card ((classicalInvolutionOddCore S).map (toOddQuot hSJ))) :=
      (CFSG.ComponentClassification.OddCore.odd_card S).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hle := CFSG.ComponentClassification.OddCore.maximal _ _ hN hodd
    have hcf : CFSG.Open.componentClassificationOddCore (J ⧸ classicalInvolutionOddCore J) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree J
    have hle' : (classicalInvolutionOddCore S).map (toOddQuot hSJ) ≤ ⊥ := hle.trans hcf.le
    have := hle' (Subgroup.mem_map_of_mem _ hs)
    rwa [Subgroup.mem_bot] at this
  · rw [ker_toOddQuot]
    refine CFSG.ComponentClassification.OddCore.maximal S _
      (Subgroup.Normal.comap inferInstance _) ?_
    exact (CFSG.ComponentClassification.OddCore.odd_card J).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hSJ))

theorem nonempty_quotEquiv_of_surjective {J S : Subgroup G} (hSJ : S ≤ J)
    (hsurj : Function.Surjective (toOddQuot hSJ)) :
    Nonempty (S ⧸ classicalInvolutionOddCore S ≃* J ⧸ classicalInvolutionOddCore J) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (classicalInvolutionOddCore_eq_ker hSJ hsurj)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)⟩

theorem oddCoreIn_eq_inf_of_surjective {J S : Subgroup G} (hSJ : S ≤ J)
    (hsurj : Function.Surjective (toOddQuot hSJ)) : oddCoreIn S = S ⊓ oddCoreIn J := by
  have hker := classicalInvolutionOddCore_eq_ker hSJ hsurj
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ (toOddQuot hSJ).ker := by rw [← hker]; exact hy
    rw [ker_toOddQuot] at hy'
    exact ⟨y.2, mem_oddCoreIn_of_mem_classicalInvolutionOddCore hy'⟩
  · rintro ⟨hxS, hxJ⟩
    have hmem : (⟨x, hxS⟩ : S) ∈ (toOddQuot hSJ).ker := by
      rw [ker_toOddQuot]
      exact mem_classicalInvolutionOddCore_of_mem_oddCoreIn hxJ
    rw [← hker] at hmem
    exact ⟨⟨x, hxS⟩, hmem, rfl⟩

theorem mem_of_cover_of_central {J S : Subgroup G} {z : G} (hzJ : z ∈ J) (hz2 : z * z = 1)
    (hzc : ∀ x ∈ J, x * z = z * x)
    (hcov : ∀ x ∈ J, ∃ s ∈ S, ∃ n ∈ oddCoreIn J, x = s * n) : z ∈ S := by
  obtain ⟨s, hs, n, hn, hzsn⟩ := hcov z hzJ
  have hnJ := oddCoreIn_le J hn
  have hzn : Commute z n := (hzc n hnJ).symm
  have hs' : s = z * n⁻¹ := by
    calc s = s * n * n⁻¹ := by group
      _ = z * n⁻¹ := by rw [← hzsn]
  have hcomm : Commute s n := by
    rw [hs']
    exact hzn.mul_left (Commute.inv_left (Commute.refl n))
  have hodd : Odd (orderOf n) :=
    (odd_card_oddCoreIn J).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn J) hn)
  have hzpow : z ^ orderOf n = z := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, show z ^ 2 = 1 by rw [pow_two]; exact hz2, one_pow, one_mul]
  have hz : z = s ^ orderOf n := by
    calc z = z ^ orderOf n := hzpow.symm
      _ = (s * n) ^ orderOf n := by rw [← hzsn]
      _ = s ^ orderOf n * n ^ orderOf n := hcomm.mul_pow _
      _ = s ^ orderOf n := by rw [pow_orderOf_eq_one, mul_one]
  rw [hz]
  exact S.pow_mem hs _

end Supplement

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_perfectResidual_mul {J A : Subgroup G} (hJ : Group.IsPerfect J)
    (hA : IsPGroup 2 A) (hAJ : A ≤ trivialOnQuot J) :
    ∀ x ∈ J, ∃ i ∈ perfectResidualOf (J ⊓ Subgroup.centralizer (A : Set G)),
      ∃ n ∈ oddCoreIn J, x = i * n := by
  set H : Subgroup G := J ⊓ Subgroup.centralizer (A : Set G) with hH
  have hHJ : H ≤ J := inf_le_left
  have hsurj : Function.Surjective (toOddQuot hHJ) :=
    toOddQuot_surjective hHJ fun x hx => exists_mem_inf_centralizer_mul hA hAJ hx
  have : Group.IsPerfect J := hJ
  have : Group.IsPerfect (J ⧸ classicalInvolutionOddCore J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (classicalInvolutionOddCore J))
      (QuotientGroup.mk'_surjective _)
  have htop := finite_perfectResidual_surjects_to_perfect_image (toOddQuot hHJ) hsurj
  intro x hx
  have hq : QuotientGroup.mk' (classicalInvolutionOddCore J) ⟨x, hx⟩ ∈
      Subgroup.map (toOddQuot hHJ) (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual H) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨i, hi, hix⟩ := Subgroup.mem_map.mp hq
  refine ⟨(i : G), ⟨i, hi, rfl⟩, (i : G)⁻¹ * x, ?_, by group⟩
  have hmk : ((Subgroup.inclusion hHJ i)⁻¹ * ⟨x, hx⟩ : J) ∈ classicalInvolutionOddCore J :=
    QuotientGroup.eq.mp hix
  exact mem_oddCoreIn_of_mem_classicalInvolutionOddCore hmk

theorem mem_perfectResidual_axis {J A : Subgroup G} {z : G} (hJ : Group.IsPerfect J)
    (hA : IsPGroup 2 A) (hAJ : A ≤ trivialOnQuot J) (hzJ : z ∈ J) (hz2 : z * z = 1)
    (hzc : ∀ x ∈ J, x * z = z * x) :
    z ∈ perfectResidualOf (J ⊓ Subgroup.centralizer (A : Set G)) :=
  mem_of_cover_of_central hzJ hz2 hzc (exists_perfectResidual_mul hJ hA hAJ)

omit [Finite G] in
theorem isSubnormal_perfectResidual_axis {J A : Subgroup G} {z : G}
    (hsub : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) :
    IsSubnormal (perfectResidualOf (J ⊓ Subgroup.centralizer (A : Set G)))
      (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (A : Set G)) := by
  set Y := Subgroup.centralizer (A : Set G)
  set H := J ⊓ Y
  have hIH : perfectResidualOf H ≤ H := Subgroup.map_subtype_le _
  have hnorm : ((perfectResidualOf H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).mpr
      (Subgroup.le_normalizer.trans (perfectResidualOf_normalizer_contains H))
  exact isSubnormal_trans (isSubnormal_of_normal_subgroupOf hIH hnorm) (isSubnormal_inf hsub Y)

@[expose] def IsClassicalMemberIn (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Y L : Subgroup G)
    (z : G) : Prop :=
  ∃ hz : z ∈ Y, IsClassicalMember p f (L.subgroupOf Y) (⟨z, hz⟩ : Y)

omit [Finite G] in
theorem inClass_of_isClassicalMemberIn {H : Subgroup G} {𝒮 : Set (Subgroup G)}
    (hne : 𝒮.Nonempty) (hle : ∀ L ∈ 𝒮, L ≤ H) (hconj : ∀ n ∈ H, ∀ L ∈ 𝒮, conjSub n L ∈ 𝒮)
    (hgen : (⨆ L ∈ 𝒮, L) = H) (hcl : ∀ L ∈ 𝒮, ∃ z, IsClassicalMemberIn p f H L z) :
    InClass p f (restrictFamily 𝒮 H) where
  nonempty := by
    obtain ⟨L, hL⟩ := hne
    exact ⟨L.subgroupOf H, L, hL, hle L hL, rfl⟩
  conjInvariant := by
    rintro n _ ⟨L, hL, hLH, rfl⟩
    exact ⟨conjSub (n : G) L, hconj n n.2 L hL, hle _ (hconj n n.2 L hL),
      conjSub_subgroupOf _ n L⟩
  generated := by
    have key := iSup_subgroupOf_self (G := G) (fun i : 𝒮 => (i : Subgroup G))
    have hsup : (⨆ i : 𝒮, (i : Subgroup G)) = H := by
      rw [← hgen, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup H) (_ : L' ∈ restrictFamily 𝒮 H) => L')
      ((i : Subgroup G).subgroupOf H) ⟨i, i.2, hle i i.2, rfl⟩
  classical := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    obtain ⟨z, hz, hcl'⟩ := hcl L hL
    exact ⟨⟨z, hz⟩, hcl'⟩

structure AxisResidual (J A I : Subgroup G) (z : G) : Prop where
  le_inf : I ≤ J ⊓ Subgroup.centralizer (A : Set G)
  mem : z ∈ I
  cover : ∀ x ∈ J, ∃ i ∈ I, ∃ n ∈ oddCoreIn J, x = i * n
  oddCoreIn_eq : oddCoreIn I = I ⊓ oddCoreIn J
  nonempty_equiv : Nonempty (I ⧸ classicalInvolutionOddCore I ≃* J ⧸ classicalInvolutionOddCore J)
  subnormal : IsSubnormal I (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (A : Set G))

theorem AxisResidual.of_cover {J A I : Subgroup G} {z : G} (hzJ : z ∈ J) (hz2 : z * z = 1)
    (hzc : ∀ x ∈ J, x * z = z * x) (hI : I ≤ J ⊓ Subgroup.centralizer (A : Set G))
    (hcov : ∀ x ∈ J, ∃ i ∈ I, ∃ n ∈ oddCoreIn J, x = i * n)
    (hsub : IsSubnormal I (Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer (A : Set G))) : AxisResidual J A I z := by
  have hIJ : I ≤ J := hI.trans inf_le_left
  have hsurj : Function.Surjective (toOddQuot hIJ) := toOddQuot_surjective hIJ hcov
  exact ⟨hI, mem_of_cover_of_central hzJ hz2 hzc hcov, hcov,
    oddCoreIn_eq_inf_of_surjective hIJ hsurj, nonempty_quotEquiv_of_surjective hIJ hsurj, hsub⟩

theorem axisResidual_centralizer {J A : Subgroup G} {z : G} (hzJ : z ∈ J) (hz2 : z * z = 1)
    (hzc : ∀ x ∈ J, x * z = z * x) (hsub : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hA : IsPGroup 2 A) (hAJ : A ≤ trivialOnQuot J) :
    AxisResidual J A (J ⊓ Subgroup.centralizer (A : Set G)) z :=
  AxisResidual.of_cover hzJ hz2 hzc le_rfl
    (fun x hx => by
      obtain ⟨h, hh, n, hn, hxhn⟩ := exists_mem_inf_centralizer_mul hA hAJ hx
      exact ⟨h, hh, n, hn, hxhn⟩)
    (isSubnormal_inf hsub _)

theorem axisResidual_perfectResidual {J A : Subgroup G} {z : G} (hJ : Group.IsPerfect J)
    (hzJ : z ∈ J) (hz2 : z * z = 1) (hzc : ∀ x ∈ J, x * z = z * x)
    (hsub : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (hA : IsPGroup 2 A)
    (hAJ : A ≤ trivialOnQuot J) :
    AxisResidual J A (perfectResidualOf (J ⊓ Subgroup.centralizer (A : Set G))) z :=
  AxisResidual.of_cover hzJ hz2 hzc
    ((Subgroup.map_subtype_le _ : perfectResidualOf (J ⊓ Subgroup.centralizer (A : Set G)) ≤ _))
    (exists_perfectResidual_mul hJ hA hAJ) (isSubnormal_perfectResidual_axis hsub)

omit [Finite G] in
theorem AxisResidual.isClassicalMemberIn {J A I : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) (hAz : ∀ a ∈ A, a * z = z * a)
    (h : AxisResidual J A I z) (hperf : Group.IsPerfect I) :
    IsClassicalMemberIn p f (Subgroup.centralizer (A : Set G)) I z := by
  set Y := Subgroup.centralizer (A : Set G) with hY
  have hzY : z ∈ Y := Subgroup.mem_centralizer_iff.mpr hAz
  have hIY : I ≤ Y := h.le_inf.trans inf_le_right
  have hIJ : I ≤ J := h.le_inf.trans inf_le_left
  have hsurj : Function.Surjective (toOddQuot hIJ) := toOddQuot_surjective hIJ h.cover
  have e : I.subgroupOf Y ≃* I := Subgroup.subgroupOfEquivOfLe hIY
  refine ⟨hzY, ?_, Subgroup.mem_subgroupOf.mpr h.mem, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact hJ.orderOf_eq_two
  · exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y =
        Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h.subnormal Y
  · obtain ⟨e'⟩ := hJ.nonempty_equiv
    obtain ⟨φ⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore (I.subgroupOf Y)).map e.toMonoidHom =
        classicalInvolutionOddCore I :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨((QuotientGroup.congr _ _ e hO).trans φ).trans e'⟩

theorem isClassicalMemberIn_perfectResidual_axis {J A : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) (hA : IsPGroup 2 A) (hAJ : A ≤ trivialOnQuot J)
    (hAz : ∀ a ∈ A, a * z = z * a) :
    IsClassicalMemberIn p f (Subgroup.centralizer (A : Set G))
      (perfectResidualOf (J ⊓ Subgroup.centralizer (A : Set G))) z := by
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hJ.orderOf_eq_two]
    exact pow_orderOf_eq_one z
  have hzc : ∀ x ∈ J, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hJ.subnormal hx)
  exact (axisResidual_perfectResidual hJ.perfect hJ.mem hz2 hzc hJ.subnormal hA
    hAJ).isClassicalMemberIn hJ hAz (finite_perfectResidualOf_isPerfect _)

end Vertex

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def FuzzyEdge (J K : Subgroup G) : Prop :=
  ∀ x ∈ J, ∀ y ∈ K, ⁅x, y⁆ ∈ oddCoreIn J ∧ ⁅x, y⁆ ∈ oddCoreIn K

omit [Finite G] in
theorem FuzzyEdge.symm {J K : Subgroup G} (h : FuzzyEdge J K) : FuzzyEdge K J :=
  fun y hy x hx => by
    have hxy := h x hx y hy
    rw [← commutatorElement_inv x y]
    exact ⟨inv_mem hxy.2, inv_mem hxy.1⟩

omit [Finite G] in
theorem FuzzyEdge.of_commutes {J K : Subgroup G} (h : Commutes J K) : FuzzyEdge J K :=
  fun x hx y hy => by
    rw [(commutatorElement_eq_one_iff_mul_comm).mpr (h x hx y hy)]
    exact ⟨one_mem _, one_mem _⟩

theorem commute_of_fuzzyEdge {J K : Subgroup G} {x y : G} (hxJ : x ∈ J) (hyK : y ∈ K)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hKy : ∀ k ∈ K, k * y = y * k)
    (hJK : FuzzyEdge J K) : x * y = y * x := by
  have hc := (hJK x hxJ y hyK).2
  have hcK : ⁅x, y⁆ ∈ K := oddCoreIn_le K hc
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hcomm : ⁅x, y⁆ * y = y * ⁅x, y⁆ := hKy _ hcK
  have hinv : ⁅x, y⁆⁻¹ = y * ⁅x, y⁆ * y⁻¹ := by
    have e1 : ⁅x, y⁆⁻¹ = y * x * y * x := by
      calc ⁅x, y⁆⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := rfl
        _ = y * x * y⁻¹ * x⁻¹ := by group
        _ = y * x * y * x := by rw [hxi, hyi]
    have e2 : y * ⁅x, y⁆ * y⁻¹ = y * x * y * x := by
      calc y * ⁅x, y⁆ * y⁻¹ = y * (x * y * x⁻¹ * y⁻¹) * y⁻¹ := rfl
        _ = y * (x * y * x * y) * y := by rw [hxi, hyi]
        _ = y * x * y * x * (y * y) := by group
        _ = y * x * y * x := by rw [hy2, mul_one]
    rw [e1, e2]
  have h1 : y * ⁅x, y⁆ * y⁻¹ = ⁅x, y⁆ := by
    rw [← hcomm, mul_inv_cancel_right]
  have hsq : ⁅x, y⁆ * ⁅x, y⁆ = 1 := mul_eq_one_iff_eq_inv.mpr (hinv.trans h1).symm
  have hodd : Odd (orderOf ⁅x, y⁆) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn K) hc)
  have hdvd : orderOf ⁅x, y⁆ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hord : orderOf ⁅x, y⁆ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd hodd (by rw [h]; decide)
  exact (commutatorElement_eq_one_iff_mul_comm).mp (orderOf_eq_one_iff.mp hord)

theorem mem_trivialOnQuot_of_fuzzyEdge {J K : Subgroup G} {y : G} (hyK : y ∈ K)
    (hy2 : y * y = 1) (hJK : FuzzyEdge J K) : y ∈ trivialOnQuot J := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have key : ∀ h ∈ J, y * h * y⁻¹ ∈ J := by
    intro h hh
    have h1 := (hJK h hh y hyK).1
    have e : y * h * y⁻¹ = ⁅y, h⁆ * h := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine J.mul_mem ?_ hh
    rw [← commutatorElement_inv h y]
    exact J.inv_mem (oddCoreIn_le J h1)
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key h hh, fun hh => ?_⟩
    have h2 := key _ hh
    have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
      calc y * (y * h * y⁻¹) * y⁻¹ = (y * y) * h * (y⁻¹ * y⁻¹) := by group
        _ = h := by rw [hy2, hyi, hy2, one_mul, mul_one]
    rwa [e] at h2
  · rw [← commutatorElement_inv x y]
    exact (oddCoreIn J).inv_mem (hJK x hx y hyK).1

theorem mem_trivialOnQuot_self {J : Subgroup G} {z : G} (hzJ : z ∈ J)
    (hzc : ∀ x ∈ J, x * z = z * x) : z ∈ trivialOnQuot J :=
  ⟨Subgroup.le_normalizer hzJ, fun x hx => by
    rw [(commutatorElement_eq_one_iff_mul_comm).mpr (hzc x hx).symm]
    exact one_mem _⟩

omit [Finite G] in
theorem closure_commute_of_commute {S : Set G} (hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
  have h1 : ∀ s ∈ S, ∀ b ∈ Subgroup.closure S, s * b = b * s := by
    intro s hs b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set G) :=
      (Subgroup.closure_le _).mpr fun t ht => by
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hSc s hs t ht).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
  intro a ha b hb
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.closure_le _).mpr fun s hs => by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h1 s hs b hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

omit [Finite G] in
theorem mul_self_of_mem_closure {S : Set G} (hS2 : ∀ s ∈ S, s * s = 1)
    (hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) : ∀ a ∈ Subgroup.closure S, a * a = 1 := by
  intro a ha
  refine Subgroup.closure_induction (p := fun a _ => a * a = 1) ?_ ?_ ?_ ?_ ha
  · exact fun s hs => hS2 s hs
  · simp
  · intro a b ha hb iha ihb
    have hab := closure_commute_of_commute hSc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  · intro a ha iha
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [iha, inv_one]

@[expose] def triangleAxis (z₁ z₂ z₃ : G) : Subgroup G := Subgroup.closure {z₁, z₂, z₃}

theorem triangleAxis_data {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (h₁ : IsCentralInvolution J₁ z₁) (h₂ : IsCentralInvolution J₂ z₂)
    (h₃ : IsCentralInvolution J₃ z₃) (e₁₂ : FuzzyEdge J₁ J₂) (e₁₃ : FuzzyEdge J₁ J₃)
    (e₂₃ : FuzzyEdge J₂ J₃) :
    (∀ a ∈ triangleAxis z₁ z₂ z₃, ∀ b ∈ triangleAxis z₁ z₂ z₃, a * b = b * a) ∧
    (∀ a ∈ triangleAxis z₁ z₂ z₃, a * a = 1) ∧
    triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J₁ ∧ triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J₂ ∧
    triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J₃ := by
  have hcen : ∀ {J : Subgroup G} {z : G}, IsCentralInvolution J z → ∀ x ∈ J, x * z = z * x :=
    fun h x hx => (h.central x hx).symm
  have c₁₂ : z₁ * z₂ = z₂ * z₁ :=
    commute_of_fuzzyEdge h₁.mem h₂.mem h₁.sq h₂.sq (hcen h₂) e₁₂
  have c₁₃ : z₁ * z₃ = z₃ * z₁ :=
    commute_of_fuzzyEdge h₁.mem h₃.mem h₁.sq h₃.sq (hcen h₃) e₁₃
  have c₂₃ : z₂ * z₃ = z₃ * z₂ :=
    commute_of_fuzzyEdge h₂.mem h₃.mem h₂.sq h₃.sq (hcen h₃) e₂₃
  have hSc : ∀ s ∈ ({z₁, z₂, z₃} : Set G), ∀ t ∈ ({z₁, z₂, z₃} : Set G), s * t = t * s := by
    intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | rfl | exact c₁₂ | exact c₁₃ | exact c₂₃ | exact c₁₂.symm | exact c₁₃.symm |
        exact c₂₃.symm
  have hS2 : ∀ s ∈ ({z₁, z₂, z₃} : Set G), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    exacts [h₁.sq, h₂.sq, h₃.sq]
  refine ⟨closure_commute_of_commute hSc, mul_self_of_mem_closure hS2 hSc, ?_, ?_, ?_⟩
  · refine (Subgroup.closure_le _).mpr fun s hs => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact mem_trivialOnQuot_self h₁.mem (hcen h₁)
    · exact mem_trivialOnQuot_of_fuzzyEdge h₂.mem h₂.sq e₁₂
    · exact mem_trivialOnQuot_of_fuzzyEdge h₃.mem h₃.sq e₁₃
  · refine (Subgroup.closure_le _).mpr fun s hs => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact mem_trivialOnQuot_of_fuzzyEdge h₁.mem h₁.sq e₁₂.symm
    · exact mem_trivialOnQuot_self h₂.mem (hcen h₂)
    · exact mem_trivialOnQuot_of_fuzzyEdge h₃.mem h₃.sq e₂₃
  · refine (Subgroup.closure_le _).mpr fun s hs => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact mem_trivialOnQuot_of_fuzzyEdge h₁.mem h₁.sq e₁₃.symm
    · exact mem_trivialOnQuot_of_fuzzyEdge h₂.mem h₂.sq e₂₃.symm
    · exact mem_trivialOnQuot_self h₃.mem (hcen h₃)

theorem isElemAbelian_triangleAxis {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (h₁ : IsCentralInvolution J₁ z₁) (h₂ : IsCentralInvolution J₂ z₂)
    (h₃ : IsCentralInvolution J₃ z₃) (e₁₂ : FuzzyEdge J₁ J₂) (e₁₃ : FuzzyEdge J₁ J₃)
    (e₂₃ : FuzzyEdge J₂ J₃) : IsElemAbelian 2 (triangleAxis z₁ z₂ z₃) := by
  obtain ⟨hcomm, hsq, -⟩ := triangleAxis_data h₁ h₂ h₃ e₁₂ e₁₃ e₂₃
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact hsq x hx

omit [Finite G] in
theorem isCentralInvolution_of_isClassicalMember {J : Subgroup G} {z : G}
    (h : IsClassicalMember p f J z) : IsCentralInvolution J z where
  mem := h.mem
  ne_one := by
    intro h1
    have := h.orderOf_eq_two
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  sq := by
    rw [← pow_two, ← h.orderOf_eq_two]
    exact pow_orderOf_eq_one z
  central := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hk)).symm

theorem triangle_axisResidual {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G} {A : Subgroup G}
    (h₁ : IsClassicalMember p f J₁ z₁) (h₂ : IsClassicalMember p f J₂ z₂)
    (h₃ : IsClassicalMember p f J₃ z₃) (e₁₂ : FuzzyEdge J₁ J₂) (e₁₃ : FuzzyEdge J₁ J₃)
    (e₂₃ : FuzzyEdge J₂ J₃) (hA : A ≤ triangleAxis z₁ z₂ z₃) :
    AxisResidual J₁ A (perfectResidualOf (J₁ ⊓ Subgroup.centralizer (A : Set G))) z₁ ∧
    AxisResidual J₂ A (perfectResidualOf (J₂ ⊓ Subgroup.centralizer (A : Set G))) z₂ ∧
    AxisResidual J₃ A (perfectResidualOf (J₃ ⊓ Subgroup.centralizer (A : Set G))) z₃ := by
  have c₁ := isCentralInvolution_of_isClassicalMember h₁
  have c₂ := isCentralInvolution_of_isClassicalMember h₂
  have c₃ := isCentralInvolution_of_isClassicalMember h₃
  obtain ⟨hcomm, hsq, hA₁, hA₂, hA₃⟩ := triangleAxis_data c₁ c₂ c₃ e₁₂ e₁₃ e₂₃
  have hA2 : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun x hx => hsq x (hA hx)
  exact ⟨axisResidual_perfectResidual h₁.perfect h₁.mem c₁.sq (fun x hx => (c₁.central x hx).symm)
      h₁.subnormal hA2 (hA.trans hA₁),
    axisResidual_perfectResidual h₂.perfect h₂.mem c₂.sq (fun x hx => (c₂.central x hx).symm)
      h₂.subnormal hA2 (hA.trans hA₂),
    axisResidual_perfectResidual h₃.perfect h₃.mem c₃.sq (fun x hx => (c₃.central x hx).symm)
      h₃.subnormal hA2 (hA.trans hA₃)⟩

theorem triangle_isClassicalMemberIn {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G} {A : Subgroup G}
    (h₁ : IsClassicalMember p f J₁ z₁) (h₂ : IsClassicalMember p f J₂ z₂)
    (h₃ : IsClassicalMember p f J₃ z₃) (e₁₂ : FuzzyEdge J₁ J₂) (e₁₃ : FuzzyEdge J₁ J₃)
    (e₂₃ : FuzzyEdge J₂ J₃) (hA : A ≤ triangleAxis z₁ z₂ z₃) :
    IsClassicalMemberIn p f (Subgroup.centralizer (A : Set G))
      (perfectResidualOf (J₁ ⊓ Subgroup.centralizer (A : Set G))) z₁ ∧
    IsClassicalMemberIn p f (Subgroup.centralizer (A : Set G))
      (perfectResidualOf (J₂ ⊓ Subgroup.centralizer (A : Set G))) z₂ ∧
    IsClassicalMemberIn p f (Subgroup.centralizer (A : Set G))
      (perfectResidualOf (J₃ ⊓ Subgroup.centralizer (A : Set G))) z₃ := by
  obtain ⟨r₁, r₂, r₃⟩ := triangle_axisResidual h₁ h₂ h₃ e₁₂ e₁₃ e₂₃ hA
  obtain ⟨hcomm, -, -⟩ := triangleAxis_data (isCentralInvolution_of_isClassicalMember h₁)
    (isCentralInvolution_of_isClassicalMember h₂) (isCentralInvolution_of_isClassicalMember h₃)
    e₁₂ e₁₃ e₂₃
  have hz : ∀ z ∈ ({z₁, z₂, z₃} : Set G), ∀ a ∈ A, a * z = z * a :=
    fun z hz a ha => hcomm a (hA ha) z (Subgroup.subset_closure hz)
  exact ⟨r₁.isClassicalMemberIn h₁ (hz z₁ (by simp)) (finite_perfectResidualOf_isPerfect _),
    r₂.isClassicalMemberIn h₂ (hz z₂ (by simp)) (finite_perfectResidualOf_isPerfect _),
    r₃.isClassicalMemberIn h₃ (hz z₃ (by simp)) (finite_perfectResidualOf_isPerfect _)⟩

end Triangle

section Three

variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Q3 (IsClassicalMember3)

@[expose] def IsClassicalMember3In (Y L : Subgroup G) (z : G) : Prop :=
  ∃ hz : z ∈ Y, IsClassicalMember3 (L.subgroupOf Y) (⟨z, hz⟩ : Y)

omit [Finite G] in
theorem isCentralInvolution_of_isClassicalMember3 {J : Subgroup G} {z : G}
    (h : IsClassicalMember3 J z) : IsCentralInvolution J z where
  mem := h.mem
  ne_one := by
    intro h1
    have := h.orderOf_eq_two
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  sq := by
    rw [← pow_two, ← h.orderOf_eq_two]
    exact pow_orderOf_eq_one z
  central := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hk)).symm

omit [Finite G] in
theorem AxisResidual.isClassicalMember3In {J A I : Subgroup G} {z : G}
    (hJ : IsClassicalMember3 J z) (hAz : ∀ a ∈ A, a * z = z * a) (h : AxisResidual J A I z) :
    IsClassicalMember3In (Subgroup.centralizer (A : Set G)) I z := by
  set Y := Subgroup.centralizer (A : Set G) with hY
  have hzY : z ∈ Y := Subgroup.mem_centralizer_iff.mpr hAz
  have hIY : I ≤ Y := h.le_inf.trans inf_le_right
  have e : I.subgroupOf Y ≃* I := Subgroup.subgroupOfEquivOfLe hIY
  refine ⟨hzY, ?_, Subgroup.mem_subgroupOf.mpr h.mem, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact hJ.orderOf_eq_two
  · have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y =
        Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h.subnormal Y
  · obtain ⟨e'⟩ := hJ.nonempty_equiv
    obtain ⟨φ⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore (I.subgroupOf Y)).map e.toMonoidHom =
        classicalInvolutionOddCore I :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨((QuotientGroup.congr _ _ e hO).trans φ).trans e'⟩

theorem isClassicalMember3In_centralizer_axis {J A : Subgroup G} {z : G}
    (hJ : IsClassicalMember3 J z) (hA : IsPGroup 2 A) (hAJ : A ≤ trivialOnQuot J)
    (hAz : ∀ a ∈ A, a * z = z * a) :
    IsClassicalMember3In (Subgroup.centralizer (A : Set G))
      (J ⊓ Subgroup.centralizer (A : Set G)) z := by
  have hc := isCentralInvolution_of_isClassicalMember3 hJ
  exact (axisResidual_centralizer hJ.mem hc.sq (fun x hx => (hc.central x hx).symm)
    hJ.subnormal hA hAJ).isClassicalMember3In hJ hAz

theorem triangle_isClassicalMember3In {J₁ J₂ J₃ : Subgroup G} {z₁ z₂ z₃ : G} {A : Subgroup G}
    (h₁ : IsClassicalMember3 J₁ z₁) (h₂ : IsClassicalMember3 J₂ z₂)
    (h₃ : IsClassicalMember3 J₃ z₃) (e₁₂ : FuzzyEdge J₁ J₂) (e₁₃ : FuzzyEdge J₁ J₃)
    (e₂₃ : FuzzyEdge J₂ J₃) (hA : A ≤ triangleAxis z₁ z₂ z₃) :
    IsClassicalMember3In (Subgroup.centralizer (A : Set G))
      (J₁ ⊓ Subgroup.centralizer (A : Set G)) z₁ ∧
    IsClassicalMember3In (Subgroup.centralizer (A : Set G))
      (J₂ ⊓ Subgroup.centralizer (A : Set G)) z₂ ∧
    IsClassicalMember3In (Subgroup.centralizer (A : Set G))
      (J₃ ⊓ Subgroup.centralizer (A : Set G)) z₃ := by
  obtain ⟨hcomm, hsq, hA₁, hA₂, hA₃⟩ := triangleAxis_data
    (isCentralInvolution_of_isClassicalMember3 h₁) (isCentralInvolution_of_isClassicalMember3 h₂)
    (isCentralInvolution_of_isClassicalMember3 h₃) e₁₂ e₁₃ e₂₃
  have hA2 : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun x hx => hsq x (hA hx)
  have hz : ∀ z ∈ ({z₁, z₂, z₃} : Set G), ∀ a ∈ A, a * z = z * a :=
    fun z hz a ha => hcomm a (hA ha) z (Subgroup.subset_closure hz)
  exact ⟨isClassicalMember3In_centralizer_axis h₁ hA2 (hA.trans hA₁) (hz z₁ (by simp)),
    isClassicalMember3In_centralizer_axis h₂ hA2 (hA.trans hA₂) (hz z₂ (by simp)),
    isClassicalMember3In_centralizer_axis h₃ hA2 (hA.trans hA₃) (hz z₃ (by simp))⟩

end Three

section EdgeNAdj

variable {G : Type} [Group G] [Finite G]

theorem FuzzyEdge.nadj {z : G} {J K : Subgroup G}
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (h : FuzzyEdge J K) :
    NAdj z J K := fun x hx y hy => oddCoreIn_le_of_isSubnormal hJ ((h x hx y hy).1)

end EdgeNAdj

end CFSG.ClassicalInvolution.Balance.Bootstrap
