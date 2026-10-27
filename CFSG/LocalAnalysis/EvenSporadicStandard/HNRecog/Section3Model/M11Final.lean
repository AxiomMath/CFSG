module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.M11Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.M11Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Transport
public import CFSG.ClassicalInvolution.Q3.M11Kernel

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open scoped commutatorElement

open Equiv Equiv.Perm CFSG.Holt.SmallGroups CFSG.Adapters.RankTwoModelTransports
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic

noncomputable def nativeEquivOpen : ↥NativeSporadic.M11 ≃* ↥CFSG.Open.M11 :=
  (NativeSporadic.M11.equivMapOfInjective (MulAut.conj m11Conj).toMonoidHom
    (MulAut.conj m11Conj).injective).trans (MulEquiv.subgroupCongr nativeM11_map_conj)

theorem commutator_eq_top_of_simple {M : Type} [Group M] [IsSimpleGroup M]
    (h : ∃ a b : M, a * b ≠ b * a) : _root_.commutator M = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator M) with hb | ht
  · obtain ⟨a, b, hab⟩ := h
    exfalso
    apply hab
    have hmem : ⁅a, b⁆ ∈ _root_.commutator M :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact ht

theorem eq_one_of_central_of_simple {M : Type} [Group M] [IsSimpleGroup M]
    (h : ∃ a b : M, a * b ≠ b * a) {t : M} (ht : ∀ s : M, s * t = t * s) : t = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with hb | htop
  · have : t ∈ Subgroup.center M := Subgroup.mem_center_iff.mpr fun s => by rw [ht s]
    rw [hb, Subgroup.mem_bot] at this
    exact this
  · obtain ⟨a, b, hab⟩ := h
    exfalso
    apply hab
    have : b ∈ Subgroup.center M := by rw [htop]; trivial
    exact Subgroup.mem_center_iff.mp this a

theorem m11_noncomm : ∃ a b : ↥CFSG.Open.M11, a * b ≠ b * a :=
  ⟨⟨m11a1, m11a1_mem⟩, ⟨m11b1, m11b1_mem⟩, fun h => by
    have h' := congrArg Subtype.val h
    exact absurd h' (by decide +kernel)⟩

theorem exists_noncomm_of_mulEquiv {M N : Type} [Group M] [Group N] (e : M ≃* N)
    (h : ∃ a b : N, a * b ≠ b * a) : ∃ a b : M, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
  have := congrArg e hc
  simpa using this

theorem exists_conj_m11zG (s : ↥CFSG.Open.M11) (hs : s * s = 1)
    (hs1 : s ≠ 1) : ∃ h : ↥CFSG.Open.M11, h * m11zG * h⁻¹ = s := by
  obtain ⟨g, hg, hgz⟩ := m11_exists_conj_of_involutions m11zG.2 m11_sq_one.2.2.2.2
    m11z_facts.2.1 s.2 (congrArg Subtype.val hs) (fun h => hs1 (Subtype.ext h))
  exact ⟨⟨g, hg⟩, Subtype.ext hgz⟩

theorem isConj_of_involutions {M : Type} [Group M]
    (φ : M ≃* ↥CFSG.Open.M11) {s t : M} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) : IsConj s t := by
  have key : ∀ x : M, x ^ 2 = 1 → x ≠ 1 → ∃ h : ↥CFSG.Open.M11, h * m11zG * h⁻¹ = φ x :=
    fun x hx hx1 => exists_conj_m11zG (φ x) (by rw [← pow_two, ← map_pow, hx, map_one])
      (fun h => hx1 (φ.injective (by rw [h, map_one])))
  obtain ⟨h, hh⟩ := key s hs hs1
  obtain ⟨k, hk⟩ := key t ht ht1
  refine isConj_iff.mpr ⟨φ.symm (k * h⁻¹), φ.injective ?_⟩
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply, ← hh, ← hk]
  group

theorem centralizer_equiv_gl23 {M : Type} [Group M]
    (φ : M ≃* ↥CFSG.Open.M11) {t : M} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    Nonempty (↥(Subgroup.centralizer ({t} : Set M)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨h, hh⟩ := exists_conj_m11zG (φ t) (by rw [← pow_two, ← map_pow, ht, map_one])
    (fun h => ht1 (φ.injective (by rw [h, map_one])))
  have hψ : (φ.trans (MulAut.conj h⁻¹)) t = m11zG := by
    change h⁻¹ * φ t * h⁻¹⁻¹ = m11zG
    rw [← hh]
    group
  obtain ⟨c⟩ := m11_centralizer_z_equiv
  exact ⟨(TwoHS.centralizerMulEquiv (φ.trans (MulAut.conj h⁻¹)) hψ).trans c⟩

theorem exists_order_five_of_mulEquiv {M : Type} [Group M]
    (φ : M ≃* ↥CFSG.Open.M11) {s : M} (hs : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ∃ t : M, t ^ 2 = 1 ∧ orderOf (s * t) = 5 := by
  obtain ⟨h, hh⟩ := exists_conj_m11zG (φ s) (by rw [← pow_two, ← map_pow, hs, map_one])
    (fun h => hs1 (φ.injective (by rw [h, map_one])))
  set t₁ : ↥CFSG.Open.M11 := ⟨m11t1, m11t1_mem⟩ with ht₁
  have hz5 : orderOf (m11zG * t₁) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have e5 : (m11zG * t₁) ^ 5 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
      exact m11_zt1_five.1
    have e1 : m11zG * t₁ ≠ 1 := fun hc => m11_zt1_five.2 (by
      have := congrArg Subtype.val hc
      rw [Subgroup.coe_mul, Subgroup.coe_one] at this
      exact this)
    exact orderOf_eq_prime e5 e1
  refine ⟨φ.symm (h * t₁ * h⁻¹), ?_, ?_⟩
  · apply φ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    refine Subtype.ext ?_
    have h2 : (m11t1 * m11t1 : Perm (Fin 11)) = 1 := m11_sq_one.2.2.2.1
    have ht₁v : (t₁ : Perm (Fin 11)) = m11t1 := rfl
    calc ((h * t₁ * h⁻¹) ^ 2 : ↥CFSG.Open.M11).1
        = (h : Perm (Fin 11)) * (m11t1 * m11t1) * (h : Perm (Fin 11))⁻¹ := by
          simp [pow_two, mul_assoc, ht₁v]
      _ = 1 := by rw [h2]; group
  · have : φ (s * φ.symm (h * t₁ * h⁻¹)) = h * (m11zG * t₁) * h⁻¹ := by
      rw [map_mul, MulEquiv.apply_symm_apply, ← hh]
      group
    rw [← MulEquiv.orderOf_eq φ, this]
    have hc := MulEquiv.orderOf_eq (MulAut.conj h) (m11zG * t₁)
    rw [MulAut.conj_apply] at hc
    rw [hc, hz5]

theorem inv_not_two_group_gl23 : ¬ IsPGroup 2 ↥(Subgroup.closure
    {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) | g ^ 2 = 1}) := by
  intro hp
  have hA : CFSG.Semidihedral.FourPointMatrices.A ∈ Subgroup.closure
      {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) | g ^ 2 = 1} :=
    Subgroup.subset_closure CFSG.Semidihedral.FourPointMatrices.A_square
  have hB : CFSG.Semidihedral.FourPointMatrices.B ∈ Subgroup.closure
      {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) | g ^ 2 = 1} :=
    Subgroup.subset_closure CFSG.Semidihedral.FourPointMatrices.B_square
  obtain ⟨k, hk⟩ := hp ⟨_, Subgroup.mul_mem _ hA hB⟩
  have hk' : (CFSG.Semidihedral.FourPointMatrices.A * CFSG.Semidihedral.FourPointMatrices.B) ^
      (2 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have hne : CFSG.Semidihedral.FourPointMatrices.A * CFSG.Semidihedral.FourPointMatrices.B ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    change CFSG.Semidihedral.FourPointMatrices.matrixA * CFSG.Semidihedral.FourPointMatrices.matrixB
      = 1 at h'
    exact absurd h' (by decide)
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one CFSG.Semidihedral.FourPointMatrices.AB_cube)
    (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num))] at hdvd
  exact hne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

end CFSG.EvenSporadicStandard.HNRecog.Section3Model

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem m11Facts_holds : M11Facts where
  perfect := fun M _ h => by
    obtain ⟨e⟩ := h
    haveI : IsSimpleGroup M :=
      e.isSimpleGroup_congr.mpr CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    exact commutator_eq_top_of_simple
      (exists_noncomm_of_mulEquiv (e.trans nativeEquivOpen) m11_noncomm)
  center_trivial := fun M _ h t ht => by
    obtain ⟨e⟩ := h
    haveI : IsSimpleGroup M :=
      e.isSimpleGroup_congr.mpr CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    exact eq_one_of_central_of_simple
      (exists_noncomm_of_mulEquiv (e.trans nativeEquivOpen) m11_noncomm) ht
  one_class := fun M _ h s t hs ht hs1 ht1 => by
    obtain ⟨e⟩ := h
    exact isConj_of_involutions (e.trans nativeEquivOpen) hs ht hs1 ht1
  centralizer_GL23 := fun M _ h t ht ht1 => by
    obtain ⟨e⟩ := h
    exact centralizer_equiv_gl23 (e.trans nativeEquivOpen) ht ht1
  inv_not_two_group := inv_not_two_group_gl23
  exists_order_five := fun M _ h s hs hs1 => by
    obtain ⟨e⟩ := h
    exact exists_order_five_of_mulEquiv (e.trans nativeEquivOpen) hs hs1

end CFSG.EvenSporadicStandard.HNRecog.Section3
