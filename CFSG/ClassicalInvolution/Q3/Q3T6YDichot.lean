module

public import CFSG.ClassicalInvolution.Q3.Q3T6YAD
public import CFSG.ClassicalInvolution.Q3.Q3T6XQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
  CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

section Lift

theorem mem_of_piz_mem_imgz {z : F} {L : Subgroup F} (hO : oddCoreOf (Cz z) ≤ L) {k : F}
    (hk : k ∈ Cz z) (h : piz z ⟨k, hk⟩ ∈ imgz z L) : k ∈ L := by
  obtain ⟨w, hw, hwk⟩ := (mem_imgz_iff' z).mp h
  have h1 : w⁻¹ * ⟨k, hk⟩ ∈ classicalInvolutionOddCore ↥(Cz z) := (piz_eq_iff z).mp hwk
  have h2 : (w : F)⁻¹ * k ∈ oddCoreOf (Cz z) := ⟨_, h1, rfl⟩
  have h3 : (w : F) * ((w : F)⁻¹ * k) ∈ L := L.mul_mem hw (hO h2)
  simpa using h3

theorem exists_pow_lift_involution (z : F) {a₀ : ↥(Cz z)} (hx : piz z a₀ * piz z a₀ = 1) :
    ∃ m : ℕ, a₀ ^ m * a₀ ^ m = 1 ∧ piz z (a₀ ^ m) = piz z a₀ := by
  have h1 : piz z (a₀ * a₀) = 1 := by rw [map_mul]; exact hx
  have h2 : a₀ * a₀ ∈ classicalInvolutionOddCore ↥(Cz z) := (piz_eq_one_iff z).mp h1
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥(Cz z))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have h3 : (a₀ * a₀) ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ h2)
  refine ⟨Nat.card (classicalInvolutionOddCore ↥(Cz z)), ?_, ?_⟩
  · calc a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) *
          a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z))
        = a₀ ^ (Nat.card (classicalInvolutionOddCore ↥(Cz z)) +
            Nat.card (classicalInvolutionOddCore ↥(Cz z))) :=
          (pow_add _ _ _).symm
      _ = (a₀ * a₀) ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) := by
          rw [← two_mul, pow_mul, pow_two]
      _ = 1 := h3
  · obtain ⟨k, hk⟩ := hN
    rw [map_pow, hk, pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

theorem twinProd_imgz_le {z : F} {K J : Subgroup F} :
    twinProd (imgz z K) (imgz z J) ≤ imgz z (twinProd K J) := by
  refine iSup₂_le fun L hL => ?_
  obtain ⟨k', hk', rfl⟩ := hL
  obtain ⟨k, hC, hkK, rfl⟩ := (mem_imgz_iff z).mp hk'
  rw [imgz_conjSub z J ⟨k, hC⟩]
  exact imgz_mono z (le_twinProd ⟨k, hkK, rfl⟩)

theorem commutator_mem_oddCoreOf_Cz {z a b : F} (ha : a ∈ Cz z) (hb : b ∈ Cz z)
    (h : piz z ⟨a, ha⟩ * piz z ⟨b, hb⟩ = piz z ⟨b, hb⟩ * piz z ⟨a, ha⟩) :
    ⁅a, b⁆ ∈ oddCoreOf (Cz z) := by
  have hc : ⁅a, b⁆ ∈ Cz z := by
    rw [commutatorElement_def]
    exact (Cz z).mul_mem ((Cz z).mul_mem ((Cz z).mul_mem ha hb) ((Cz z).inv_mem ha))
      ((Cz z).inv_mem hb)
  refine (mem_oddCoreOf_Cz_iff z).mpr ⟨hc, ?_⟩
  have e : (⟨⁅a, b⁆, hc⟩ : ↥(Cz z)) = ⁅(⟨a, ha⟩ : ↥(Cz z)), ⟨b, hb⟩⁆ := rfl
  rw [e, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr h

end Lift

section Members

variable {J : Subgroup F} {t : F}

theorem oddCoreOf_eq_Cz (hJ : Mem3 J t) : oddCoreOf J = oddCoreOf (Cz t) :=
  oddCoreOf_eq_oddCoreIn hJ

theorem oddCoreOf_Cz_le (hJ : Mem3 J t) : oddCoreOf (Cz t) ≤ J :=
  (oddCoreOf_eq_Cz hJ) ▸ oddCoreOf_le_self J

theorem commutator_mem_oddCoreOf_of_img (hJ : Mem3 J t) {a b : F} (ha : a ∈ Cz t) (hb : b ∈ J)
    (h : ⁅piz t ⟨a, ha⟩, piz t ⟨b, hJ.le_centralizer hb⟩⁆ ∈ oddCoreOf (imgz t J)) :
    ⁅a, b⁆ ∈ oddCoreOf J := by
  have hOJ : oddCoreOf (imgz t J) = ⊥ := Mem3.oddCoreOf_eq_bot (Mem3.imgz hJ) (exAt_zb t)
  rw [hOJ, Subgroup.mem_bot] at h
  have h1 := commutator_mem_oddCoreOf_Cz ha (hJ.le_centralizer hb)
    (commutatorElement_eq_one_iff_mul_comm.mp h)
  rw [oddCoreOf_eq_Cz hJ]
  exact h1

end Members

theorem abstract_dichotomy' {K J : Subgroup F} {z t : F} (hJ : Mem3 J t)
    (hz2 : z * z = 1) (hzJ : z ∈ Subgroup.normalizer (J : Set F))
    (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) (htK : ∀ k ∈ K, k * t = t * k)
    (hzK : ∀ k ∈ K, k * z = z * k)
    (hKgen : K ≤ Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)})
    (hKsub : IsSubnormal K
      (Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.centralizer ({t} : Set F))) :
    (∀ k ∈ K, k ∈ Subgroup.normalizer (J : Set F) ∧ ∀ j ∈ J, ⁅k, j⁆ ∈ oddCoreOf J) ∨
      ∃ d ∈ K, d ≠ 1 ∧ d * d = 1 ∧ d ∈ twinProd K J ⊓ Subgroup.centralizer ({z} : Set F) := by
  classical
  have hJt : J ≤ Cz t := hJ.le_centralizer
  have hOJ : oddCoreOf (Cz t) ≤ J := oddCoreOf_Cz_le hJ
  have hzt : z * t = t * z := by
    have h1 : z * t * z⁻¹ = t := hJ.isUniqueInvolution.conj_eq (conjSub_eq_of_mem_normalizer hzJ)
    calc z * t = (z * t * z⁻¹) * z := by group
      _ = t * z := by rw [h1]
  have hz : z ∈ Cz t := Subgroup.mem_centralizer_singleton_iff.mpr hzt
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hnt
    intro j _
    rw [commutatorElement_one_left]
    exact (oddCoreOf J).one_mem
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hJ' : Mem3 (imgz t J) (zb t) := Mem3.imgz hJ
  have hz2' : piz t ⟨z, hz⟩ * piz t ⟨z, hz⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥(Cz t)) = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hzJ' : piz t ⟨z, hz⟩ ∈ Subgroup.normalizer (imgz t J : Set (Qz t)) :=
    AscHypOmega.mem_normalizer_of_conjSub_eq
      ((conjSub_eq_iff_imgz t hJt hOJ ⟨z, hz⟩).mp (conjSub_eq_of_mem_normalizer hzJ))
  have hnt' : ¬ ∀ j ∈ imgz t J, ⁅piz t ⟨z, hz⟩, j⁆ ∈ oddCoreOf (imgz t J) := by
    intro h
    apply hnt
    intro j hj
    exact commutator_mem_oddCoreOf_of_img hJ hz hj (h _ (piz_mem_imgz (hJt hj) hj))
  have htK' : ∀ k ∈ imgz t K, k * zb t = zb t * k := by
    intro k _
    have : k ∈ Subgroup.centralizer ({zb t} : Set (Qz t)) := by
      rw [centralizer_zb]
      exact Subgroup.mem_top k
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hzK' : ∀ k ∈ imgz t K, k * piz t ⟨z, hz⟩ = piz t ⟨z, hz⟩ * k := by
    intro k hk
    obtain ⟨a, hC, haK, rfl⟩ := (mem_imgz_iff t).mp hk
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzK a haK)
  have hKgen' : imgz t K ≤
      Subgroup.closure {g : Qz t | g ∈ imgz t K ∧ Odd (orderOf g)} := by
    intro x hx
    obtain ⟨a, hC, haK, rfl⟩ := (mem_imgz_iff t).mp hx
    have key : ∀ k ∈ Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)}, ∃ hk : k ∈ Cz t,
        piz t ⟨k, hk⟩ ∈ Subgroup.closure {g : Qz t | g ∈ imgz t K ∧ Odd (orderOf g)} := by
      intro k hk
      refine Subgroup.closure_induction
        (p := fun k _ => ∃ hk : k ∈ Cz t,
          piz t ⟨k, hk⟩ ∈ Subgroup.closure {g : Qz t | g ∈ imgz t K ∧ Odd (orderOf g)})
        ?_ ?_ ?_ ?_ hk
      · rintro g ⟨hgK, hgodd⟩
        have hgC : g ∈ Cz t := Subgroup.mem_centralizer_singleton_iff.mpr (htK g hgK)
        refine ⟨hgC, Subgroup.subset_closure ⟨piz_mem_imgz hgC hgK, ?_⟩⟩
        have hd : orderOf (piz t ⟨g, hgC⟩) ∣ orderOf g := by
          have := orderOf_map_dvd (piz t) (⟨g, hgC⟩ : ↥(Cz t))
          rwa [Subgroup.orderOf_mk] at this
        exact hgodd.of_dvd_nat hd
      · refine ⟨(Cz t).one_mem, ?_⟩
        have : (⟨1, (Cz t).one_mem⟩ : ↥(Cz t)) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      · rintro k₁ k₂ - - ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨(Cz t).mul_mem h₁ h₂, ?_⟩
        have : (⟨k₁ * k₂, (Cz t).mul_mem h₁ h₂⟩ : ↥(Cz t)) = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := rfl
        rw [this, map_mul]
        exact Subgroup.mul_mem _ h₁' h₂'
      · rintro k₁ - ⟨h₁, h₁'⟩
        refine ⟨(Cz t).inv_mem h₁, ?_⟩
        have : (⟨k₁⁻¹, (Cz t).inv_mem h₁⟩ : ↥(Cz t)) = (⟨k₁, h₁⟩)⁻¹ := rfl
        rw [this, map_inv]
        exact Subgroup.inv_mem _ h₁'
    obtain ⟨_, h⟩ := key a (hKgen haK)
    exact h
  have hKsub' : IsSubnormal (imgz t K)
      (Subgroup.centralizer ({piz t ⟨z, hz⟩} : Set (Qz t)) ⊓
        Subgroup.centralizer ({zb t} : Set (Qz t))) := by
    have h := isSubnormal_imgz t hKsub
    rw [inf_comm (Subgroup.centralizer ({z} : Set F)), ← centralizer_piz t hz hzord] at h
    rwa [centralizer_zb, inf_top_eq]
  rcases abstract_dichotomy (z := piz t ⟨z, hz⟩) (t := zb t) hJ' (exAt_zb t) hz2' hzJ' hnt' htK'
      hzK' hKgen' hKsub' with hI | ⟨d', hd'K, hd'1, hd'2, hd'P⟩
  · left
    intro k hk
    have hkC : k ∈ Cz t := Subgroup.mem_centralizer_singleton_iff.mpr (htK k hk)
    obtain ⟨hkN, hkc⟩ := hI _ (piz_mem_imgz hkC hk)
    refine ⟨?_, fun j hj => ?_⟩
    · exact AscHypOmega.mem_normalizer_of_conjSub_eq
        ((conjSub_eq_iff_imgz t hJt hOJ ⟨k, hkC⟩).mpr (conjSub_eq_of_mem_normalizer hkN))
    · exact commutator_mem_oddCoreOf_of_img hJ hkC hj (hkc _ (piz_mem_imgz (hJt hj) hj))
  · right
    obtain ⟨k, hC, hkK, hkd⟩ := (mem_imgz_iff t).mp hd'K
    obtain ⟨m, hm2, hmπ⟩ := exists_pow_lift_involution t (a₀ := ⟨k, hC⟩) (by rw [hkd]; exact hd'2)
    have hdK : k ^ m ∈ K := K.pow_mem hkK m
    have hdC : k ^ m ∈ Cz t := (Cz t).pow_mem hC m
    have hπd : piz t ⟨k ^ m, hdC⟩ = d' := by
      rw [← hkd, ← hmπ]
      rfl
    refine ⟨k ^ m, hdK, ?_, ?_, ?_, ?_⟩
    · intro h1
      apply hd'1
      rw [← hπd]
      have : (⟨k ^ m, hdC⟩ : ↥(Cz t)) = 1 := Subtype.ext h1
      rw [this, map_one]
    · exact congrArg Subtype.val hm2
    · have h1 : piz t ⟨k ^ m, hdC⟩ ∈ imgz t (twinProd K J) := by
        rw [hπd]
        exact twinProd_imgz_le hd'P.1
      exact mem_of_piz_mem_imgz
        (hOJ.trans (le_twinProd ⟨1, K.one_mem, (conjSub_one J).symm⟩)) hdC h1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzK _ hdK)

end CFSG.ClassicalInvolution.Q3.Q3T6Y
