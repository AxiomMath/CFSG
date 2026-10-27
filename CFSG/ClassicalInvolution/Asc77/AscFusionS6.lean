module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS5
public import CFSG.ClassicalInvolution.Asc77.AscFusionR2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem prop370_chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K J : Subgroup G} {z t : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hJ : J ∈ CoreAssembly.conjClass K₀)
    (hKz : IsUniqueInvolution K z) (hJt : IsUniqueInvolution J t) (hne : t ≠ z)
    (hzt : z * t = t * z) (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hA3 : ∀ q ∈ K, IsPGroup 2 (Subgroup.zpowers q) → q * (t * q * t⁻¹) = (t * q * t⁻¹) * q →
      ∀ j ∈ J, ⁅q * (t * q * t⁻¹), j⁆ ∈ oddCoreOf J) : False := by
  classical
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hKm : IsClassicalMember p f K z := isClassicalMember_of_mem_conjClass hp2 hq h₀ hK hKz
  have hJm : IsClassicalMember p f J t := isClassicalMember_of_mem_conjClass hp2 hq h₀ hJ hJt
  have hJK : J ∈ CoreAssembly.conjClass K := conjClass_trans (conjClass_symm hK) hJ
  have ht2' : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_zpowers_of_sq_sq (by rw [ht2, one_mul])
  have hznt : ¬ ∀ k ∈ J, ⁅z, k⁆ ∈ oddCoreOf J := by
    intro hζ
    exact htK (mem_normalizer_of_trivial_action hp2 hq hKm hJK hJt hzt.symm hzJ hζ hJt.mem ht2'
      hzt.symm)
  have hKne : K ≠ conjSub t K := fun h =>
    htK (AscHypOmega.mem_normalizer_of_conjSub_eq h.symm)
  obtain ⟨hK'mem, hK'z, hK'N, hKN', hcomm⟩ := twin_facts_conj hp2 hq h₀ hK hKz hzt.symm hKne
  obtain ⟨a, haK, ha2, haa'⟩ := exists_twin_diag_element hp2 hq h₀ hK hKz ht2 hzt htK
  set a' : G := t * a * t⁻¹ with ha'def
  obtain ⟨ha'2, hd2, hzd, htd, hat, hai', hta, hta'⟩ :=
    twin_diag_identities hz2 ht2 hzt ha2 ha'def haa'
  set d : G := a * a' with hd
  have haa'' : a * a' = a' * a := haa'
  have ha'K' : a' ∈ conjSub t K := conj_mem_conjSub haK
  have ha4 : orderOf a = 4 := orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha2
  have ha2' : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq hz2 ha2
  have had : a * d = d * a := by
    rw [hd]
    calc a * (a * a') = a * (a' * a) := by rw [haa'']
      _ = a * a' * a := by group
  have hza : a * z = z * a := by
    calc a * z = a * (a * a) := by rw [ha2]
      _ = (a * a) * a := by group
      _ = z * a := by rw [ha2]
  have hdN : d ∈ Subgroup.normalizer (J : Set G) :=
    diag_mem_normalizer_of_classical hp2 hq h₀ hK hKz ht2 hzt.symm hKne hJ hJt haK ha2' haa'
  have hdtriv : ∀ j ∈ J, ⁅d, j⁆ ∈ oddCoreOf J := hA3 a haK ha2' haa'
  obtain ⟨κ, hκJ, hκ2, hκz, hκd⟩ :=
    exists_kappa_centralized hp2 hq hJm hz2 hd2 hzd hzJ hdN hznt hdtriv
  have hainv2 : a⁻¹ * a⁻¹ = z := by
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = z := by rw [ha2]; exact inv_eq_of_mul_eq_one_right hz2
  have hcommi : a⁻¹ * a' = a' * a⁻¹ := by
    calc a⁻¹ * a' = a⁻¹ * (a' * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * a') * a⁻¹ := by rw [haa'']
      _ = a' * a⁻¹ := by group
  obtain ⟨c, hcM, hc⟩ := exists_conj_of_twin_pairs hp2 hq h₀ hK hK'mem hKz hK'z hKne haK
    (K.inv_mem haK) ha'K' ha'K' ha2 ha'2 haa'' hainv2 ha'2 hcommi
  have hc' : c * d * c⁻¹ = z * d := hc.trans hai'
  have hKm' : IsClassicalMember p f (conjSub t K) z :=
    isClassicalMember_of_mem_conjClass hp2 hq h₀ hK'mem hK'z
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hKm.subnormal
  have hK'C : conjSub t K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hKm'.subnormal
  have hcz : c * z = z * c :=
    Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hKC hK'C) hcM)
  set y : G := a * κ * c with hy
  have hyt : y⁻¹ * t * y = d := conj_chain_t_to_d hz2 ht2 hzt hzd htd hat hκ2 hκz hκd hc'
  set I : Subgroup G := conjSub y⁻¹ J with hI
  have hIc : I ∈ CoreAssembly.conjClass K₀ := conjSub_mem_conjClass hJ _
  have hId : IsUniqueInvolution I d := by
    have := hJt.conj y⁻¹
    rwa [show y⁻¹ * t * y⁻¹⁻¹ = d by rw [inv_inv]; exact hyt] at this
  have hIm : IsClassicalMember p f I d := isClassicalMember_of_mem_conjClass hp2 hq h₀ hIc hId
  have hzI : z ∈ Subgroup.normalizer (I : Set G) := bstar hp2 hq h₀ hK hIc hKz hId haK ha4 had
  have hznt_I : ¬ ∀ k ∈ I, ⁅z, k⁆ ∈ oddCoreOf I := by
    intro hT
    have hxt : ∀ u ∈ K, ⁅a', u⁆ ∈ oddCoreOf K := by
      intro u hu
      have := (hcomm (Subgroup.commutator_mem_commutator hu ha'K')).1
      rw [← commutatorElement_inv]
      exact (oddCoreOf K).inv_mem this
    have hgact := inner_of_mul_trivial haK hxt (show d = a * a' from rfl)
    have hg2 : ∀ y ∈ K, ⁅a * a, y⁆ ∈ oddCoreOf K := by
      intro y hy
      rw [ha2]
      have : ⁅z, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hKz.commute_of_mem hy)
      rw [this]
      exact (oddCoreOf K).one_mem
    exact inner_action_false hp2 hq h₀ hK hIc hKz hId hzd hzI hT haK hgact hg2
      (not_forall_comm_of_sq_eq hp2 hq hKm haK ha2)
  have hzI2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_sq_sq (by rw [hz2, one_mul])
  obtain ⟨R, hR2, hER, hRI⟩ := exists_sylow_normalized (J := I) (E := Subgroup.zpowers z) hzI2
    (Subgroup.zpowers_le.mpr hzI)
  have hzR : z ∈ R := hER (Subgroup.mem_zpowers z)
  obtain ⟨ι, hι, hι2, hιz⟩ :=
    exists_inverted_involution_member hp2 hIm hq hR2 hRI hzR hz2 hzI hznt_I
  have hιd : ι * d = d * ι := (hId.commute_of_mem hι.2).symm
  obtain ⟨hc0z, hc0d⟩ := conj_chain_c0 hz2 hd2 hzd hι2 hιz hιd hcz hc'
  set c₀ : G := ι * c with hc₀
  set I₁ : Subgroup G := conjSub c₀⁻¹ K with hI₁
  set I₂ : Subgroup G := conjSub c₀⁻¹ (conjSub t K) with hI₂
  have hI₁c : I₁ ∈ CoreAssembly.conjClass K₀ := conjSub_mem_conjClass hK _
  have hI₂c : I₂ ∈ CoreAssembly.conjClass K₀ := conjSub_mem_conjClass hK'mem _
  have hI₁d : IsUniqueInvolution I₁ d := by
    have := hKz.conj c₀⁻¹
    rwa [show c₀⁻¹ * z * c₀⁻¹⁻¹ = d by rw [inv_inv]; exact hc0z] at this
  have hI₂d : IsUniqueInvolution I₂ d := by
    have := hK'z.conj c₀⁻¹
    rwa [show c₀⁻¹ * z * c₀⁻¹⁻¹ = d by rw [inv_inv]; exact hc0z] at this
  have hne12 : I₁ ≠ I₂ := by
    intro h
    apply hKne
    have := congrArg (conjSub c₀) h
    rwa [hI₁, hI₂, ← conjSub_mul, ← conjSub_mul, mul_inv_cancel, conjSub_one, conjSub_one] at this
  have hzdM : z * d ∈ I₁ ⊔ I₂ := by
    have e1 : c₀⁻¹ * a * c₀ ∈ I₁ := by
      have := conj_mem_conjSub (n := c₀⁻¹) haK
      simpa using this
    have e2 : c₀⁻¹ * a' * c₀ ∈ I₂ := by
      have := conj_mem_conjSub (n := c₀⁻¹) ha'K'
      simpa using this
    have : z * d = (c₀⁻¹ * a * c₀) * (c₀⁻¹ * a' * c₀) := by
      rw [← hc0d, hd]
      group
    rw [this]
    exact (I₁ ⊔ I₂).mul_mem (Subgroup.mem_sup_left e1) (Subgroup.mem_sup_right e2)
  have hzM : z ∈ I₁ ⊔ I₂ := by
    have : z = d * (z * d) := by
      calc z = (d * d) * z := by rw [hd2, one_mul]
        _ = d * (d * z) := by rw [mul_assoc]
        _ = d * (z * d) := by rw [hzd]
    rw [this]
    exact (I₁ ⊔ I₂).mul_mem (Subgroup.mem_sup_left hI₁d.mem) hzdM
  have hκ2' : IsPGroup 2 (Subgroup.zpowers κ) :=
    isPGroup_zpowers_of_sq_sq (by rw [hκ2, ht2])
  have htd' : t * d = d * t := htd
  have hI₁m : IsClassicalMember p f I₁ d := isClassicalMember_of_mem_conjClass hp2 hq h₀ hI₁c hI₁d
  have hI₂m : IsClassicalMember p f I₂ d := isClassicalMember_of_mem_conjClass hp2 hq h₀ hI₂c hI₂d
  have hJI₁ : J ∈ CoreAssembly.conjClass I₁ := conjClass_trans (conjClass_symm hI₁c) hJ
  have hJI₂ : J ∈ CoreAssembly.conjClass I₂ := conjClass_trans (conjClass_symm hI₂c) hJ
  have hκI₁ : κ ∈ Subgroup.normalizer (I₁ : Set G) :=
    mem_normalizer_of_trivial_action hp2 hq hI₁m hJI₁ hJt htd' hdN hdtriv hκJ hκ2' hκd
  have hκI₂ : κ ∈ Subgroup.normalizer (I₂ : Set G) :=
    mem_normalizer_of_trivial_action hp2 hq hI₂m hJI₂ hJt htd' hdN hdtriv hκJ hκ2' hκd
  have hconj : conjSub κ⁻¹ (I₁ ⊔ I₂) = I₁ ⊔ I₂ := by
    show Subgroup.map (MulAut.conj κ⁻¹).toMonoidHom (I₁ ⊔ I₂) = I₁ ⊔ I₂
    rw [Subgroup.map_sup]
    show conjSub κ⁻¹ I₁ ⊔ conjSub κ⁻¹ I₂ = I₁ ⊔ I₂
    rw [conjSub_eq_of_mem_normalizer ((Subgroup.normalizer (I₁ : Set G)).inv_mem hκI₁),
      conjSub_eq_of_mem_normalizer ((Subgroup.normalizer (I₂ : Set G)).inv_mem hκI₂)]
  have hztM : z * t ∈ I₁ ⊔ I₂ := by
    have h1 := conj_mem_conjSub (n := κ⁻¹) hzM
    rw [hconj, inv_inv] at h1
    rwa [kappa_conj_eq hz2 ht2 hzt hκ2 hκz] at h1
  have htM : t ∈ I₁ ⊔ I₂ := by
    have : t = z * (z * t) := by rw [← mul_assoc, hz2, one_mul]
    rw [this]
    exact (I₁ ⊔ I₂).mul_mem hzM hztM
  have htd'' : t ≠ d := by
    intro h
    apply hne
    rw [← h, ht2, one_mul] at hat
    calc t = a * (a⁻¹ * t * a) * a⁻¹ := by group
      _ = a * z * a⁻¹ := by rw [hat]
      _ = z := by rw [hza]; group
  exact false_of_mem_twin_product hp2 hq h₀ hI₁c hI₂c hJ hI₁d hI₂d hne12 hJt htd.symm htd'' hdN
    hdtriv htM




@[expose] def DiagCentral (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K₀ : Subgroup G) (z₀ : G), IsClassicalMember p f K₀ z₀ →
      CITBelowU p f (Nat.card G) →
      ∀ K ∈ CoreAssembly.conjClass K₀, ∀ z : G, IsUniqueInvolution K z →
        ∀ J ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
          z * t = t * z → z ∈ Subgroup.normalizer (J : Set G) →
            t ∉ Subgroup.normalizer (K : Set G) →
              ∀ q ∈ K, IsPGroup 2 (Subgroup.zpowers q) →
                q * (t * q * t⁻¹) = (t * q * t⁻¹) * q →
                  ∀ j ∈ J, ⁅q * (t * q * t⁻¹), j⁆ ∈ oddCoreOf J

theorem prop370_of_diagCentral (p f : ℕ) [Fact p.Prime] (h : DiagCentral p f) : Prop370 p f := by
  intro G _ _ _ hnab hp2 hq K₀ z₀ h₀ hbelow K hK z hKz J hJ t hJt hne hzt hzJ
  by_contra htK
  exact prop370_chain hp2 hq h₀ hK hJ hKz hJt hne hzt hzJ htK
    (h G hnab hp2 hq K₀ z₀ h₀ hbelow K hK z hKz J hJ t hJt hne hzt hzJ htK)

end CFSG.ClassicalInvolution.Asc77.AscFusion
