module

public import CFSG.ClassicalInvolution.Uniform.U4Delta
public import CFSG.ClassicalInvolution.Asc77.AscFusionS5
public import CFSG.ClassicalInvolution.Uniform.U4Fix

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement Pointwise

variable {F : Type} [Group F] [Finite F]

theorem commutator_mem_of_product {K₁ K₃ K' : Subgroup F} {z : F} (h₁ : Mem3 K₁ z)
    (h₃ : Mem3 K₃ z) (h' : Mem3 K' z) (h₁' : K₁ ≠ K') (h₃' : K₃ ≠ K')
    {x y : F} (hx : x ∈ K₁) (hy : y ∈ K₃) : ∀ k ∈ K', ⁅x * y, k⁆ ∈ oddCoreOf K' := by
  intro k hk
  obtain ⟨-, hKN, -⟩ := h₁.twin_facts h' h₁'
  have h1 : ⁅y, k⁆ ∈ oddCoreOf K' := h'.commutator_mem_of_twin h₃ (Ne.symm h₃') hy k hk
  have h2 : ⁅x, k⁆ ∈ oddCoreOf K' := h'.commutator_mem_of_twin h₁ (Ne.symm h₁') hx k hk
  have h3 : x * ⁅y, k⁆ * x⁻¹ ∈ oddCoreOf K' :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (hKN hx) h1
  have e : ⁅x * y, k⁆ = (x * ⁅y, k⁆ * x⁻¹) * ⁅x, k⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreOf K').mul_mem h3 h2

theorem exists_fixed_of_product {K B R : Subgroup F} {z t : F} (hK : Mem3 K z)
    (hB : Mem3 B z) (hKB : K ≠ B) (hR2 : IsPGroup 2 R) (hRK : IsSylow2In (R ⊓ K) K)
    (htR : t ∈ R) (ht2 : t * t = 1) (htN : t ∈ Subgroup.normalizer (K : Set F))
    (hnt : ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K) {u w : F} (hu : u ∈ K) (hw : w ∈ B)
    (htuw : t = u * w) : ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  have hact : ∀ y ∈ K, t * y * t⁻¹ * (u * y * u⁻¹)⁻¹ ∈ oddCoreOf K :=
    AscFusion.inner_of_mul_trivial hu (hK.commutator_mem_of_twin hB hKB hw) htuw
  have hnc : ¬ ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K := by
    intro hc
    apply hnt
    intro k hk
    have e1 : ⁅t, k⁆ = (t * k * t⁻¹ * (u * k * u⁻¹)⁻¹) * ⁅u, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact (oddCoreOf K).mul_mem (hact k hk) (hc k hk)
  exact exists_fixed_of_inner hK hR2 hRK htR ht2 htN hu hact hnc

theorem noQuasidihedral {K : Subgroup F} {z : F} (hK : Mem3 K z)
    {J : Subgroup F}
    {t : F} (hJ : Mem3 J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) {R : Subgroup F} (hR2 : IsPGroup 2 R)
    (htR : t ∈ R) (hRK : IsSylow2In (R ⊓ K) K) : ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  classical
  have hJt : IsUniqueInvolution J t := hJ.isUniqueInvolution
  have hz2 : z * z = 1 := hK.mul_self
  have ht2 : t * t = 1 := hJ.mul_self
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_four hv4
  have hvv : v * v = t := mul_self_eq_of_orderOf_four hJt hvJ hv4
  have htK : t ∈ Subgroup.normalizer (K : Set F) := hvv ▸ hvK
  have hzt : z * t = t * z := by
    rw [← hvv]
    calc z * (v * v) = (z * v) * v := by group
      _ = (v * z) * v := by rw [hvz]
      _ = v * (z * v) := by group
      _ = v * (v * z) := by rw [hvz]
      _ = (v * v) * z := by group
  have hv3 : 3 ≤ Nat.card (Subgroup.zpowers v) := by rw [Nat.card_zpowers, hv4]; omega
  have hzJ : z ∈ Subgroup.normalizer (J : Set F) :=
    hJ.mem_normalizer_of_commute_of_mem_noncentral hvJ hv2 hv3 hvz.symm
  have hnt := nontrivAction hK hJ hne hvJ hv4 hvz hvK hv
  have hnt' : ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by rwa [← hvv]
  obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ := exists_kappa hK hv4 hvz hv hvK hnt
  obtain ⟨hδ2, hnδ, hδvδ⟩ := AscFusion.kappa_delta_facts hz2 hvz hκ2 hκn hcomm
  set δ : F := κ * (v⁻¹ * κ * v) with hδ
  have hδt : t * δ = δ * t := by rw [← hvv]; exact hnδ
  have hδt' : δ * t * δ⁻¹ = t := by
    calc δ * t * δ⁻¹ = (t * δ) * δ⁻¹ := by rw [← hδt]
      _ = t := by group
  have hδJ : J ≠ conjSub δ J := by
    intro h
    have h1 : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
    rw [← h, hδvδ] at h1
    have h2 : z ∈ J := by
      have := J.mul_mem (J.inv_mem hvJ) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases hJt.unique z h2 hz2 with h3 | h3
    · exact (hK.isUniqueInvolution).ne_one h3
    · exact hne h3.symm
  have hznt : ¬ ∀ k ∈ J, ⁅z, k⁆ ∈ oddCoreOf J :=
    z_acts_nontrivially hK hJ hne hvJ hv4 hvz hvK hv hnt
  have hzI2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hz2 (hK.isUniqueInvolution).ne_one
  obtain ⟨RJ, hRJ2, hERJ, hRJJ⟩ := AscFusion.exists_sylow_normalized (J := J)
    (E := Subgroup.zpowers z) hzI2 (Subgroup.zpowers_le.mpr hzJ)
  have hzRJ : z ∈ RJ := hERJ (Subgroup.mem_zpowers z)
  obtain ⟨j, hjJ, hj2, hjz⟩ := hJ.exists_inverted hRJ2 hRJJ hzRJ hz2 hzJ hznt
  have hjz' : j⁻¹ * z * j = z * t := AscFusion.kappa_conj_eq hz2 ht2 hzt hj2 hjz
  have hjt : j * t = t * j := hJ.mul_comm_of_mem hjJ.2
  have hκt : t⁻¹ * κ * t = κ⁻¹ := by rw [← hvv]; exact hκn
  have hkz : κ * z = z * κ := hK.mul_comm_of_mem hκK
  have hkt : κ⁻¹ * t * κ = t * z := AscFusion.kappa_conj_eq ht2 hz2 hzt.symm hκ2 hκt
  obtain ⟨hxz, hxt⟩ := AscFusion.swap_element hz2 ht2 hzt hjt hjz' hkz hkt
  set x : F := j * κ * j with hx
  have hxtz : x * t * x⁻¹ = z := by rw [← hxz]; group
  have hxzt : x * z * x⁻¹ = t := by rw [← hxt]; group
  set J₂ : Subgroup F := conjSub x J with hJ₂
  set J₂' : Subgroup F := conjSub (x * δ) J with hJ₂'
  have hJ₂z : Mem3 J₂ z := by
    have := hJ.conj x
    rwa [hxtz] at this
  have hJ₂'z : Mem3 J₂' z := by
    have := hJ.conj (x * δ)
    have e : (x * δ) * t * (x * δ)⁻¹ = z := by
      calc (x * δ) * t * (x * δ)⁻¹ = x * (δ * t * δ⁻¹) * x⁻¹ := by group
        _ = x * t * x⁻¹ := by rw [hδt']
        _ = z := hxtz
    rwa [e] at this
  have hJ₂ne : J₂ ≠ J₂' := by
    intro h
    apply hδJ
    have := congrArg (conjSub x⁻¹) h
    rwa [hJ₂, hJ₂', ← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one,
      show x⁻¹ * (x * δ) = δ by group] at this
  have htM : t ∈ J₂ ⊔ J₂' := by
    have e1 : x * v⁻¹ * x⁻¹ ∈ J₂ := conj_mem_conjSub (J.inv_mem hvJ)
    have e2 : (x * δ) * v * (x * δ)⁻¹ ∈ J₂' := conj_mem_conjSub hvJ
    have : t = (x * v⁻¹ * x⁻¹) * ((x * δ) * v * (x * δ)⁻¹) := by
      calc t = x * z * x⁻¹ := hxzt.symm
        _ = x * (v⁻¹ * (v * z)) * x⁻¹ := by group
        _ = x * (v⁻¹ * (δ * v * δ⁻¹)) * x⁻¹ := by rw [hδvδ]
        _ = (x * v⁻¹ * x⁻¹) * ((x * δ) * v * (x * δ)⁻¹) := by group
    rw [this]
    exact (J₂ ⊔ J₂').mul_mem (Subgroup.mem_sup_left e1) (Subgroup.mem_sup_right e2)
  obtain ⟨hJ₂₁, hJ₂₂, -⟩ := hJ₂z.twin_facts hJ₂'z hJ₂ne
  have hset : ((J₂ ⊔ J₂' : Subgroup F) : Set F) = (J₂ : Set F) * (J₂' : Set F) :=
    Subgroup.coe_mul_of_right_le_normalizer_left J₂ J₂' hJ₂₁
  have htM' : t ∈ (J₂ : Set F) * (J₂' : Set F) := by
    rw [← hset]
    exact htM
  obtain ⟨u₁, hu₁, u₂, hu₂, htu⟩ := htM'
  by_cases hKJ₂ : K = J₂
  · subst hKJ₂
    exact exists_fixed_of_product hK hJ₂'z hJ₂ne hR2 hRK htR ht2 htK hnt' hu₁ hu₂ htu.symm
  · by_cases hKJ₂' : K = J₂'
    · subst hKJ₂'
      have hw : u₂⁻¹ * u₁ * u₂ ∈ J₂ := by
        have := (Subgroup.mem_normalizer_iff.mp (hJ₂₁ (J₂'.inv_mem hu₂)) u₁).mp hu₁
        rwa [inv_inv] at this
      have hu21 : t = u₂ * (u₂⁻¹ * u₁ * u₂) := by rw [← htu]; group
      exact exists_fixed_of_product hK hJ₂z (Ne.symm hJ₂ne) hR2 hRK htR ht2 htK hnt' hu₂ hw hu21
    · exfalso
      apply hnt'
      intro k hk
      rw [← htu]
      exact commutator_mem_of_product hJ₂z hJ₂'z hK (Ne.symm hKJ₂) (Ne.symm hKJ₂') hu₁ hu₂ k hk

theorem typeI {K : Subgroup F} {z : F} (hK : Mem3 K z)
    {J : Subgroup F} {t : F}
    (hJ : Mem3 J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J) (hv4 : orderOf v = 4)
    (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) :
    ∃ k ∈ K, k * k = z ∧ ∀ x ∈ K, t * x * t⁻¹ * (k * x * k⁻¹)⁻¹ ∈ oddCoreOf K := by
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_four hv4
  have hvv : v * v = t := mul_self_eq_of_orderOf_four (hJ.isUniqueInvolution) hvJ hv4
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ :=
    exists_twin_sylow hK hv2 hvz (conjSub_inv_ne hv) hvK
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  obtain ⟨a₀, ha₀, ha₀2, hta₀⟩ := noQuasidihedral hK hJ hne hvJ hv4 hvz hvK hv hR2 htR hRK
  have hnt := nontrivAction hK hJ hne hvJ hv4 hvz hvK hv
  exact exists_inner_order_four hK hJ hne hvJ hv2 hv4 hvz hv hRcomm hRinv ha₀ ha₀2 hta₀
    (z_acts_nontrivially hK hJ hne hvJ hv4 hvz hvK hv hnt)

end CFSG.ClassicalInvolution.Uniform.U4
