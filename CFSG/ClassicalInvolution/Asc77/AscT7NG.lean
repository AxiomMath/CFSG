module

public import CFSG.ClassicalInvolution.Asc77.AscT7FI

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7N

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.involution_eq_of_sylow (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) (hKt : K ≤ Subgroup.centralizer ({t} : Set G))
    (hK't : K' ≤ Subgroup.centralizer ({t} : Set G)) {J₁ R₁ : Subgroup G} {t₁ : G}
    (hJ₁Ω : J₁ ∈ Ω) (hR₁ : R₁ ∈ RSet Ω) (hR₁J₁ : R₁ ≤ J₁)
    (hR₁N : R₁ ≤ Subgroup.normalizer (K : Set G))
    (hR₁t : R₁ ≤ Subgroup.centralizer ({t} : Set G)) (ht₁ : IsUniqueInvolution J₁ t₁)
    (hJ₁K : J₁ ≠ K) (hJ₁K' : J₁ ≠ K') (hJ₁J : J₁ ≠ J) : t₁ = t := by
  classical
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJK : J ∈ omegaNbr Ω K := h.hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := h.hJ.2 K' h.std.hK'
  have hK'K : K' ∈ omegaNbr Ω K := T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
  have hJ₁K_nbr : J₁ ∈ omegaNbr Ω K := ⟨hJ₁Ω, hJ₁K, R₁, hR₁, hR₁J₁, hR₁N⟩
  have hR₁S : IsSylow2In R₁ J₁ := hΩ.isSylow2In_of_mem_RSet_of_le hp hJ₁Ω hR₁ hR₁J₁
  have hR₁2 : IsPGroup 2 R₁ := hR₁S.2.1
  have h8₁ : 8 ≤ Nat.card R₁ := hΩ.eight_le_of_mem_RSet hp hR₁
  have hR₁z : R₁ ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
  have hR₁K' : R₁ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK'Ω hJ₁Ω (fun e => hJ₁K' e.symm) hzK' hR₁J₁ hR₁2
      (by omega) hR₁z
  have hR₁J : R₁ ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hJ₁Ω (fun e => hJ₁J e.symm) h.ht hR₁J₁ hR₁2
      (by omega) hR₁t
  obtain ⟨R_K, hRKS, hP₁⟩ := exists_isPGroup_sup_sylow hR₁2 hR₁N
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω h.std.hne.symm hz hzK'
  have hP₁N : R₁ ⊔ R_K ≤ Subgroup.normalizer (K' : Set G) := sup_le hR₁K' (hRKS.1.trans hKN)
  obtain ⟨R_K', hRK'S, hP₂⟩ := exists_isPGroup_sup_sylow hP₁ hP₁N
  have hRKset : R_K ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRKS
  have hRK'set : R_K' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hRK'S
  have h8K : 8 ≤ Nat.card R_K := hΩ.eight_le_of_mem_RSet hp hRKset
  have h8K' : 8 ≤ Nat.card R_K' := hΩ.eight_le_of_mem_RSet hp hRK'set
  have hRKJ : R_K ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hK hJK.2.1 h.ht hRKS.1 hRKS.2.1 (by omega)
      (hRKS.1.trans hKt)
  have hRK'J : R_K' ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hK'Ω hJK'.2.1 h.ht hRK'S.1 hRK'S.2.1
      (by omega) (hRK'S.1.trans hK't)
  have hP₂N : R₁ ⊔ R_K ⊔ R_K' ≤ Subgroup.normalizer (J : Set G) :=
    sup_le (sup_le hR₁J hRKJ) hRK'J
  obtain ⟨R_J, hRJS, hP₃⟩ := exists_isPGroup_sup_sylow hP₂ hP₂N
  have hRJset : R_J ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hRJS
  obtain ⟨W₁, hW₁, hD⟩ := exists_W_of_isPGroup hp hq hΩ hP₃
  have hR₁D : R₁ ∈ DSet Ω W₁ :=
    hD R₁ hR₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hRKD : R_K ∈ DSet Ω W₁ :=
    hD R_K hRKset (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hRK'D : R_K' ∈ DSet Ω W₁ := hD R_K' hRK'set (le_sup_right.trans le_sup_left)
  have hRJD : R_J ∈ DSet Ω W₁ := hD R_J hRJset le_sup_right
  obtain ⟨ρK, hρK, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hK hRKS hRKD
  obtain ⟨ρK', hρK', -⟩ := T7D.exists_rep hp hq hΩ hW₁ hK'Ω hRK'S hRK'D
  obtain ⟨ρJ, hρJ, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hJΩ hRJS hRJD
  obtain ⟨ρJ₁, hρJ₁, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hJ₁Ω hR₁S hR₁D
  have c₁ : Thompson.Ctx p f Ω W₁ := T7D.ctx_of_stand hst hW₁
  have hnc₁ : ¬ DbarConnected Ω W₁ :=
    thompsonGraphAll G Ω ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩ hst.mem hne hW₁
  have h4 := c₁.mul_four_eq_one hnc₁ ρK ρK' ρJ ρJ₁ (by rw [hρK, hρK']; exact hK'K)
    (by rw [hρK, hρJ]; exact hJK) (by rw [hρK', hρJ]; exact hJK')
    (by rw [hρK, hρJ₁]; exact hJ₁K_nbr)
    (by rw [hρK', hρJ₁]; exact hJ₁K') (by rw [hρJ, hρJ₁]; exact hJ₁J)
    (by rw [hρK]; exact hz) (by rw [hρK']; exact hzK') (by rw [hρJ]; exact h.ht)
    (by rw [hρJ₁]; exact ht₁)
  rw [hz.sq, one_mul] at h4
  have h5 : t₁ = t⁻¹ := eq_inv_of_mul_eq_one_right h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_left h.ht.sq

end Frame

end T7N

end CFSG.ClassicalInvolution.Asc77
