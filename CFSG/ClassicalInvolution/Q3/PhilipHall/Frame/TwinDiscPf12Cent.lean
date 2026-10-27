module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9M

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace TwinDisc


section Cent

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {K K' J : Subgroup Y}
  {z u t : Y}

theorem twin_le_centralizer_t_gen (hs : AlphaSteps Ω) (hf : TwinFrameData Ω K K' z u J t)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥) {L : Subgroup Y}
    (hL : L ∈ twinSet Ω K) : L ≤ Subgroup.centralizer ({t} : Set Y) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hzt : z * t = t * z := comm_zt hΩ hf
  have hz := hf.hz
  have hzL := isUniqueInvolution_of_mem_twinSet hz hL
  have hαzt : alphaOf (Subgroup.closure ({z, t} : Set Y)) = ⊥ := by
    rw [hs.alpha_zt hf]
    exact hα
  have hO : ∀ x ∈ oddCoreOf (Subgroup.centralizer ({z} : Set Y)), x * t = t * x :=
    T8.oddCoreOf_centralizer_commutes hαzt (Subgroup.subset_closure (by simp)) hz.ne_one
      (Subgroup.subset_closure (by simp))
  have hsub := isSubnormal_of_hypOmegaGen hΩ hL.1 hzL
  intro ℓ hℓ
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hℓ).symm
  have htC : t ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hc' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set Y)) := by
    have := A7Q.Gen.commutator_twin_mem_oddCoreOf hΩ hf hL hsub ℓ hℓ
    rwa [commutatorElement_def] at this
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set Y)))
    hf.ht.sq (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ htC)
    (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hℓC) hc'
  have h1 : t * (ℓ * o) = (ℓ * o) * t := mul_inv_eq_iff_eq_mul.mp hfix
  have h2 : o * t = t * o := hO o hoO
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h3 : (t * ℓ) * o = (ℓ * t) * o := by
    calc (t * ℓ) * o = t * (ℓ * o) := by rw [mul_assoc]
      _ = (ℓ * o) * t := h1
      _ = ℓ * (o * t) := by rw [mul_assoc]
      _ = ℓ * (t * o) := by rw [h2]
      _ = (ℓ * t) * o := by rw [mul_assoc]
  exact (mul_right_cancel h3).symm

theorem involution_eq_of_sylow_gen (hP : Q3CL.PartIHypG Ω) (hf : TwinFrameData Ω K K' z u J t)
    (hne : dComp Ω K ≠ dstarComp Ω K) (hKt : K ≤ Subgroup.centralizer ({t} : Set Y))
    (hK't : K' ≤ Subgroup.centralizer ({t} : Set Y)) {J₁ R₁ : Subgroup Y} {t₁ : Y}
    (hJ₁Ω : J₁ ∈ Ω) (hR₁ : R₁ ∈ RSet Ω) (hR₁J₁ : R₁ ≤ J₁)
    (hR₁N : R₁ ≤ Subgroup.normalizer (K : Set Y))
    (hR₁t : R₁ ≤ Subgroup.centralizer ({t} : Set Y)) (ht₁ : IsUniqueInvolution J₁ t₁)
    (hJ₁K : J₁ ≠ K) (hJ₁K' : J₁ ≠ K') (hJ₁J : J₁ ≠ J) : t₁ = t := by
  classical
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hK : K ∈ Ω := hf.mem
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  have hz : IsUniqueInvolution K z := hf.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hf.hK'
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJK : J ∈ omegaNbr Ω K := hf.hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := hf.hJ.2 K' hf.hK'
  have hK'K : K' ∈ omegaNbr Ω K := Q3CL.T3.twin_mem_omegaNbr hΩ hK hK'Ω hf.hne hz hzK'
  have hJ₁K_nbr : J₁ ∈ omegaNbr Ω K := ⟨hJ₁Ω, hJ₁K, R₁, hR₁, hR₁J₁, hR₁N⟩
  have hR₁S : IsSylow2In R₁ J₁ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ₁Ω hR₁ hR₁J₁
  have hR₁2 : IsPGroup 2 R₁ := hR₁S.2.1
  have h8₁ : 8 ≤ Nat.card R₁ := Sec6Gen.eight_le_of_mem_RSet hΩ hR₁
  have hR₁z : R₁ ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
  have hR₁K' : R₁ ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hJ₁Ω (fun e => hJ₁K' e.symm) hzK' hR₁J₁ hR₁2
      (by omega) hR₁z
  have hR₁J : R₁ ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hJ₁Ω (fun e => hJ₁J e.symm) hf.ht hR₁J₁ hR₁2
      (by omega) hR₁t
  obtain ⟨R_K, hRKS, hP₁⟩ := exists_isPGroup_sup_sylow hR₁2 hR₁N
  have hKN : K ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hf.hne.symm hz hzK'
  have hP₁N : R₁ ⊔ R_K ≤ Subgroup.normalizer (K' : Set Y) := sup_le hR₁K' (hRKS.1.trans hKN)
  obtain ⟨R_K', hRK'S, hP₂⟩ := exists_isPGroup_sup_sylow hP₁ hP₁N
  have hRKset : R_K ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRKS
  have hRK'set : R_K' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hRK'S
  have h8K : 8 ≤ Nat.card R_K := Sec6Gen.eight_le_of_mem_RSet hΩ hRKset
  have h8K' : 8 ≤ Nat.card R_K' := Sec6Gen.eight_le_of_mem_RSet hΩ hRK'set
  have hRKJ : R_K ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hK hJK.2.1 hf.ht hRKS.1 hRKS.2.1 (by omega)
      (hRKS.1.trans hKt)
  have hRK'J : R_K' ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hK'Ω hJK'.2.1 hf.ht hRK'S.1 hRK'S.2.1
      (by omega) (hRK'S.1.trans hK't)
  have hP₂N : R₁ ⊔ R_K ⊔ R_K' ≤ Subgroup.normalizer (J : Set Y) :=
    sup_le (sup_le hR₁J hRKJ) hRK'J
  obtain ⟨R_J, hRJS, hP₃⟩ := exists_isPGroup_sup_sylow hP₂ hP₂N
  have hRJset : R_J ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hRJS
  obtain ⟨W₁, hW₁, hD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ hP₃
  have hR₁D : R₁ ∈ DSet Ω W₁ :=
    hD R₁ hR₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hRKD : R_K ∈ DSet Ω W₁ :=
    hD R_K hRKset (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hRK'D : R_K' ∈ DSet Ω W₁ := hD R_K' hRK'set (le_sup_right.trans le_sup_left)
  have hRJD : R_J ∈ DSet Ω W₁ := hD R_J hRJset le_sup_right
  obtain ⟨ρK, hρK, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hK hRKS hRKD
  obtain ⟨ρK', hρK', -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hK'Ω hRK'S hRK'D
  obtain ⟨ρJ, hρJ, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hJΩ hRJS hRJD
  obtain ⟨ρJ₁, hρJ₁, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hJ₁Ω hR₁S hR₁D
  have c₁ : Q3CL.Thompson.Ctx Ω W₁ := Q3CL.T8.ctxOf hP hW₁
  have hnc₁ : ¬ DbarConnected Ω W₁ := Q3T6.Mu.thompsonGraphAll hP hK hne hW₁
  have h4 := c₁.mul_four_eq_one hP.cls hnc₁ ρK ρK' ρJ ρJ₁ (by rw [hρK, hρK']; exact hK'K)
    (by rw [hρK, hρJ]; exact hJK) (by rw [hρK', hρJ]; exact hJK')
    (by rw [hρK, hρJ₁]; exact hJ₁K_nbr)
    (by rw [hρK', hρJ₁]; exact hJ₁K')
    (by rw [hρJ, hρJ₁]; exact hJ₁J)
    (by rw [hρK]; exact hz) (by rw [hρK']; exact hzK') (by rw [hρJ]; exact hf.ht)
    (by rw [hρJ₁]; exact ht₁)
  rw [hz.sq, one_mul] at h4
  have h5 : t₁ = t⁻¹ := eq_inv_of_mul_eq_one_right h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_left hf.ht.sq

end Cent

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
