module

public import CFSG.ClassicalInvolution.Q3.Q3T6BTrivEx
public import CFSG.ClassicalInvolution.Q3.Q3T6YTwinP

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem exists_involution_of_isPGroup {A : Subgroup F} (hA : IsPGroup 2 A) {d : F} (hd : d ∈ A)
    (hd1 : d ≠ 1) : ∃ e ∈ A, e ≠ 1 ∧ e * e = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨d, hd⟩
  have hk' : orderOf d = 2 ^ k := (Subgroup.orderOf_coe (⟨d, hd⟩ : A)).trans hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hd1 (orderOf_eq_one_iff.mp (by simpa using hk'))
  have hlt : 2 ^ (k - 1) < orderOf d := by
    rw [hk']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨d ^ 2 ^ (k - 1), A.pow_mem hd _, pow_ne_one_of_lt_orderOf (by positivity) hlt, ?_⟩
  rw [← pow_add, ← two_mul, ← pow_succ', show k - 1 + 1 = k by omega, ← hk']
  exact pow_orderOf_eq_one d

theorem abstract_dichotomy {K J : Subgroup F} {z t : F} (hJ : Mem3 J t) (htex : ExAt t)
    (hz2 : z * z = 1) (hzJ : z ∈ Subgroup.normalizer (J : Set F))
    (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) (htK : ∀ k ∈ K, k * t = t * k)
    (hzK : ∀ k ∈ K, k * z = z * k)
    (hKgen : K ≤ Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)})
    (hKsub : IsSubnormal K
      (Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.centralizer ({t} : Set F))) :
    (∀ k ∈ K, k ∈ Subgroup.normalizer (J : Set F) ∧ ∀ j ∈ J, ⁅k, j⁆ ∈ oddCoreOf J) ∨
      ∃ d ∈ K, d ≠ 1 ∧ d * d = 1 ∧ d ∈ twinProd K J ⊓ Subgroup.centralizer ({z} : Set F) := by
  classical
  have hOJ : oddCoreOf J = ⊥ := Mem3.oddCoreOf_eq_bot hJ htex
  have hnt' : ∃ j ∈ J, z * j ≠ j * z := by
    by_contra hcon
    push Not at hcon
    apply hnt
    intro j hj
    rw [hOJ, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon j hj)
  set P : Subgroup F := twinProd K J with hP
  set A : Subgroup F := P ⊓ Subgroup.centralizer ({z} : Set F) with hA
  have hA2 : IsPGroup 2 A := isPGroup_twinProd_centralizer hJ htK htex hz2 hzJ hzK hnt'
  have hKA : K ≤ Subgroup.normalizer (A : Set F) := le_normalizer_twinProd_inf_centralizer hzK
  have hKD : K ≤ Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.centralizer ({t} : Set F) :=
    fun k hk => ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hzK k hk),
      Subgroup.mem_centralizer_singleton_iff.mpr (htK k hk)⟩
  have hAD : A ≤ Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.centralizer ({t} : Set F) :=
    fun a ha => ⟨ha.2, twinProd_le_centralizer' hJ htK ha.1⟩
  have hM : ∀ m ∈ K ⊔ A, ∃ k ∈ K, ∃ a ∈ A, m = k * a := by
    intro m hm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K A hKA] at hm
    obtain ⟨k, hk, a, ha, rfl⟩ := hm
    exact ⟨k, hk, a, ha, rfl⟩
  have hKM : IsSubnormal K (K ⊔ A) :=
    isSubnormal_of_le_of_le hKsub (sup_le hKD hAD) le_sup_left
  have hAN : A ≤ Subgroup.normalizer (K : Set F) :=
    subnormal_odd_normalizer hKgen hA2 hKM le_sup_right hM
  by_cases hKA1 : ∀ d ∈ K, d ∈ A → d = 1
  · left
    have hcomm : ∀ g ∈ K, ∀ a ∈ A, g * a = a * g := by
      intro g hg a ha
      have h1 : ⁅g, a⁆ ∈ K := by
        have h0 : a * g⁻¹ * a⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha) g⁻¹).mp (K.inv_mem hg)
        have : ⁅g, a⁆ = g * (a * g⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
        rw [this]
        exact K.mul_mem hg h0
      have h2 : ⁅g, a⁆ ∈ A := by
        have h0 : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hg) a).mp ha
        rw [commutatorElement_def]
        exact A.mul_mem h0 (A.inv_mem ha)
      exact commutatorElement_eq_one_iff_mul_comm.mp (hKA1 _ h1 h2)
    have hoddN : ∀ g ∈ K, Odd (orderOf g) → g ∈ Subgroup.normalizer (J : Set F) := fun g hg hodd =>
      odd_mem_normalizer_of_centralizes hJ htex hz2 hzJ hnt htK hzK
        (fun g' hg' _ a ha => hcomm g' hg' a ha) hg hodd
    have hKN : K ≤ Subgroup.normalizer (J : Set F) :=
      hKgen.trans ((Subgroup.closure_le _).mpr fun g hg => hoddN g hg.1 hg.2)
    obtain ⟨ρ, hρ⟩ := exists_action hJ
    have hρz : ρ ⟨z, hzJ⟩ ≠ 1 := fun h1 => hnt ((hρ ⟨z, hzJ⟩).mp h1)
    have hS : ∀ g ∈ {g : F | g ∈ K ∧ Odd (orderOf g)},
        ∃ hg : g ∈ Subgroup.normalizer (J : Set F), ρ ⟨g, hg⟩ = 1 := by
      intro g hg
      exact ⟨hoddN g hg.1 hg.2, act_trivial_of_odd ρ hzJ hz2 hρz (hoddN g hg.1 hg.2)
        (hzK g hg.1) hg.2⟩
    intro k hk
    obtain ⟨hd, h1⟩ := closure_act_trivial ρ hS k (hKgen hk)
    exact ⟨hd, (hρ ⟨k, hd⟩).mp h1⟩
  · right
    push Not at hKA1
    obtain ⟨d, hdK, hdA, hd1⟩ := hKA1
    have hKA2 : IsPGroup 2 (K ⊓ A : Subgroup F) := hA2.to_le inf_le_right
    obtain ⟨e, heKA, he1, he2⟩ := exists_involution_of_isPGroup hKA2 ⟨hdK, hdA⟩ hd1
    exact ⟨e, heKA.1, he1, he2, heKA.2⟩

end CFSG.ClassicalInvolution.Q3.Q3T6Y
