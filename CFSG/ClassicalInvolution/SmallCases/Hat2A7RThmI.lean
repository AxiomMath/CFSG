module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RTwin
public import CFSG.ClassicalInvolution.Generic.StepPerfect
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Member
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Quaternion

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

section Hyp

variable {F : Type*} [Group F]

@[expose] def TwoElementsNormalize (K : Subgroup F) (z : F) : Prop :=
  ∀ k ∈ K, IsPGroup 2 (Subgroup.zpowers k) → k ∉ Subgroup.zpowers z →
    ∀ g : F, g * k * g⁻¹ ∈ Subgroup.centralizer ({z} : Set F) →
      g * k * g⁻¹ ∈ Subgroup.normalizer (K : Set F)

@[expose] def TwinsCommuteModOdd (K : Subgroup F) (z : F) : Prop :=
  ∀ g ∈ Subgroup.centralizer ({z} : Set F), g ∉ Subgroup.normalizer (K : Set F) →
    ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ ≤
      (classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set F))).map
        (Subgroup.centralizer ({z} : Set F)).subtype

structure ThmIHyp (K : Subgroup F) (z : F) : Prop where
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ K
  subnormal : IsSubnormal K (Subgroup.centralizer ({z} : Set F))
  unique_involution : ∀ w ∈ K, orderOf w = 2 → w = z
  nonabelian_sylow : ∀ Q : Sylow 2 ↥K,
    ∃ x ∈ (Q : Subgroup ↥K), ∃ y ∈ (Q : Subgroup ↥K), x * y ≠ y * x
  two_elements : TwoElementsNormalize K z
  twins_commute : TwinsCommuteModOdd K z

end Hyp

section Classical

variable {F : Type*} [Group F] [Finite F] {K : Subgroup F} {z : F}

theorem quaternionGroup_a_one_xa_zero_not_comm {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (QuaternionGroup.a 1 : QuaternionGroup n) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  intro h
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
  have h1 : (0 : ZMod (2 * n)) - 1 = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    linear_combination -h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem nonabelian_sylow_of_witness (hw : A7Witness K) (Q : Sylow 2 ↥K) :
    ∃ x ∈ (Q : Subgroup ↥K), ∃ y ∈ (Q : Subgroup ↥K), x * y ≠ y * x := by
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_quaternion_sylow_of_witness hw Q
  have h2 : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥(Q : Subgroup ↥K)) : ↥K),
    (e.symm (QuaternionGroup.a 1)).2,
    ((e.symm (QuaternionGroup.xa 0) : ↥(Q : Subgroup ↥K)) : ↥K),
    (e.symm (QuaternionGroup.xa 0)).2, fun hc => ?_⟩
  have hc' : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
      e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext hc
  rw [← map_mul, ← map_mul] at hc'
  exact quaternionGroup_a_one_xa_zero_not_comm h2 (e.symm.injective hc')

theorem thmIHyp_of_classical2A7 (hK : IsClassical2A7 ⊤ K z) (h3 : TwoElementsNormalize K z) :
    ThmIHyp K z where
  orderOf_eq_two := hK.orderOf_eq_two
  mem := hK.mem
  subnormal := by
    have h1 := hK.subnormal
    rwa [top_inf_eq] at h1
  unique_involution := fun w hw hw2 => hK.eq_of_orderOf_eq_two hw hw2
  nonabelian_sylow := nonabelian_sylow_of_witness hK.witness
  two_elements := h3
  twins_commute := fun g hg hgn => by
    have hK' : K.map (MulAut.conj g).toMonoidHom ∈ omegaAt K z z := map_conj_mem_omegaAt_self hg
    have hne : K.map (MulAut.conj g).toMonoidHom ≠ K := fun h =>
      hgn (map_conj_eq_iff_mem_normalizer.mp h)
    exact (twins_of_classical2A7 hK hK' hne).2.2.2

end Classical

@[expose] def A7Omega5 : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (K : Subgroup F) (z : F), IsClassical2A7 ⊤ K z → TwoElementsNormalize K z

@[expose] def A7ThmI : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (K : Subgroup F) (z : F), A7Witness K → ThmIHyp K z →
      CFSG.Blueprint.OddLieType F ∨ CFSG.Blueprint.NativeSporadic.IsSporadic F .M11

theorem cit2A7Case_of_thmI (T : A7ThmI) (O5 : A7Omega5) : Generic.CIT2A7Case := by
  intro F _ _ _ hnab z hz K hzK hK hw _
  obtain ⟨L, hL⟩ := exists_isClassical2A7_of_witness hz hzK hK hw
  exact T F hnab L z hL.witness (thmIHyp_of_classical2A7 hL (O5 F hnab L z hL))

theorem citSimplePerfect_of_thmI (h1 : Generic.CITSimplePerfectSL2) (T : A7ThmI)
    (O5 : A7Omega5) : CITSimplePerfect :=
  Generic.citSimplePerfect_of_cases h1 (cit2A7Case_of_thmI T O5)

end CFSG.ClassicalInvolution.Hat2A7R
