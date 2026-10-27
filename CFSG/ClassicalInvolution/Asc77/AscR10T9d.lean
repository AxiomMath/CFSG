module

public import CFSG.ClassicalInvolution.Asc77.AscR10T9c
public import CFSG.ClassicalInvolution.Asc77.AscR10Aux

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



open CFSG.ClassicalInvolution.Uniform

omit [Finite G] in
theorem t9_fac720 : (3 ^ 2 * ((3 ^ 2) ^ 2 - 1)).factorization 2 = 4 := by
  have : (3 ^ 2 * ((3 ^ 2) ^ 2 - 1) : ℕ) = 2 ^ 4 * 45 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 45)]
  simp

omit [Finite G] in
theorem t9_fac24 : (3 * (3 ^ 2 - 1)).factorization 2 = 3 := by
  have : (3 * (3 ^ 2 - 1) : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  simp

theorem Std20.t9_k_eq_two (d : Std20 3 2 K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) : k = 2 := by
  have hq : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨zK, hzK⟩ := d.hyp.classical K hK
  obtain ⟨eK⟩ := hzK.nonempty_equiv
  have hRcard : Nat.card ↥R = 2 ^ ((3 ^ 2 * ((3 ^ 2) ^ 2 - 1)).factorization 2) := by
    rw [Uniform.natCard_isSylow2In_eq d.hR, Nat.card_congr eK.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]
  have hRu : Nat.card ↥R = 2 * Nat.card ↥(K ⊓ W) :=
    Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp d.late_KW d.late_mem_K d.hR
  have hKW : Nat.card ↥(K ⊓ W) = 2 ^ (k + 1) := by rw [← hu, Nat.card_zpowers, huo]
  rw [hRcard, hKW, t9_fac720] at hRu
  have hpow : 2 ^ 4 = 2 ^ (k + 2) := by rw [hRu]; ring
  have := Nat.pow_right_injective (le_refl 2) hpow
  omega

theorem t9_natCard_sylow {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {w : Y}
    (hL : IsClassicalMemberU (.sl2 3 1) L w) (P : Sylow 2 ↥L) :
    Nat.card ↥(P : Subgroup ↥L) = 8 := by
  have h3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hw : ∃ _ : Fact (Nat.Prime 3),
      Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, GaloisField 3 1)) := hL.witness
  obtain ⟨hp3, ⟨eL⟩⟩ := hw
  rw [Uniform.natCard_sylow_eq P, Nat.card_congr eL.toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h3, t9_fac24]
  norm_num

theorem Std20.t9_aViol [IsSimpleGroup G] (d : Std20 3 2 K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    {b : G} (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1))
    (hzA : z ∈ Subgroup.centralizer ({b} : Set G)) :
    ∃ htA : t ∈ Subgroup.centralizer ({b} : Set G),
      ∃ J_b : Subgroup ↥(Subgroup.centralizer ({b} : Set G)),
        AViol (conjFamily (crossIn K b)) (crossIn K b) J_b ⟨z, hzA⟩ ⟨t, htA⟩ := by
  have hk2 : k = 2 := d.t9_k_eq_two hu huo
  have hmem := d.t9_isClassicalMember c9 h8 hb hzA
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  have htA : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hb.comm_t.symm
  obtain ⟨c, hcb, hcK, hcz⟩ := d.r_exists_c c7 c9 h8 hb
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcb
  obtain ⟨v₀, hv₀, hv₀o, hv₀t, hbv⟩ := d.r_v0 c9 h8 hb hu huo hact
  set K_b := crossIn K b with hKb
  set cY : ↥C := ⟨c, hcC⟩ with hcY
  set J_b := conjSub cY K_b with hJb
  refine ⟨htA, J_b, ?_⟩
  have hzKa : z ∈ (K ⊓ C) := Subgroup.mem_subgroupOf.mp hmem.mem
  have hu₁ : IsUniqueInvolution K_b ⟨z, hzA⟩ := by
    have := d.t9_isUniqueInvolution_conjSub hzA hzKa 1
    rwa [conjSub_one, one_mul, inv_one, mul_one] at this
  have hu₂ : IsUniqueInvolution J_b ⟨t, htA⟩ := by
    have := d.t9_isUniqueInvolution_conjSub hzA hzKa cY
    have e : cY * ⟨z, hzA⟩ * cY⁻¹ = ⟨t, htA⟩ := Subtype.ext hcz
    rwa [e] at this
  have hΩ₀ := d.t9_hypOmegaModU c9 h8 hb hzA
  have hΩg : HypOmegaGen (conjFamily K_b) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ₀
  have hJbΛ : J_b ∈ conjFamily K_b := ⟨cY, rfl⟩
  have hKbΛ : K_b ∈ conjFamily K_b := ⟨1, conjSub_one _⟩
  have hvJW : v₀ ∈ J ⊓ W := hv₀ ▸ Subgroup.mem_zpowers v₀
  have hv2C : v₀ ^ 2 ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hbv.symm
  set y₀ : ↥C := ⟨v₀ ^ 2, hv2C⟩ with hy₀
  have hv2J : v₀ ^ 2 ∈ J := J.pow_mem hvJW.1 2
  have h2v : 2 ∣ orderOf v₀ := by
    rw [hv₀o]
    exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have hy₀o : orderOf y₀ = 2 ^ k := by
    rw [hy₀, Subgroup.orderOf_mk, orderOf_pow_of_dvd (by norm_num) h2v, hv₀o, pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]
  have hy₀J : y₀ ∈ J_b := by
    have hmap : (y₀ : G) ∈ J_b.map C.subtype := by
      rw [hJb, map_conjSub_crossIn]
      rw [mem_conjSub_iff]
      refine ⟨?_, ?_⟩
      · have : v₀ ^ 2 ∈ conjSub c K := hcK ▸ hv2J
        exact mem_conjSub_iff.mp this
      · have h1 : (c⁻¹ * v₀ ^ 2 * c) * b = b * (c⁻¹ * v₀ ^ 2 * c) := by
          calc c⁻¹ * v₀ ^ 2 * c * b = c⁻¹ * v₀ ^ 2 * (c * b) := by group
            _ = c⁻¹ * v₀ ^ 2 * (b * c) := by rw [hcb]
            _ = c⁻¹ * (v₀ ^ 2 * b) * c := by group
            _ = c⁻¹ * (b * v₀ ^ 2) * c := by rw [hbv]
            _ = (c⁻¹ * b) * v₀ ^ 2 * c := by group
            _ = (b * c⁻¹) * v₀ ^ 2 * c := by
              have : c⁻¹ * b = b * c⁻¹ := by
                calc c⁻¹ * b = c⁻¹ * b * c * c⁻¹ := by group
                  _ = c⁻¹ * (b * c) * c⁻¹ := by group
                  _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hcb]
                  _ = b * c⁻¹ := by group
              rw [this]
            _ = b * (c⁻¹ * v₀ ^ 2 * c) := by group
        exact Subgroup.mem_centralizer_singleton_iff.mpr h1
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).mp hmap
  set U : Subgroup ↥C := Subgroup.zpowers y₀ with hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := k) (by rw [hU, Nat.card_zpowers, hy₀o])
  have hUJ : U ≤ J_b := Subgroup.zpowers_le.mpr hy₀J
  have hUcard : Nat.card ↥U = 2 ^ k := by rw [hU, Nat.card_zpowers, hy₀o]
  have hU2' : IsPGroup 2 (U.subgroupOf J_b) := hU2.comap_subtype
  obtain ⟨Q, hQ⟩ := hU2'.exists_le_sylow
  set R₁ : Subgroup ↥C := (Q : Subgroup ↥J_b).map J_b.subtype with hR₁
  have hR₁Λ : R₁ ∈ RSet (conjFamily K_b) := ⟨J_b, hJbΛ, Q, rfl⟩
  have hUR₁ : U ≤ R₁ := by
    have h1 : (U.subgroupOf J_b).map J_b.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUJ
    rw [← h1]
    exact Subgroup.map_mono hQ
  have hQcard : Nat.card ↥(Q : Subgroup ↥J_b) = 2 ^ (k + 1) := by
    rw [t9_natCard_sylow (hmem.conj cY) Q, hk2]
    norm_num
  have hR₁card : Nat.card ↥R₁ = 2 ^ (k + 1) := by
    rw [hR₁, ← hQcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ J_b.subtype_injective).toEquiv).symm
  have hrel : U.relIndex R₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R₁
    rw [inf_eq_left.mpr hUR₁, hR₁card, hUcard] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have : U.relIndex R₁ * 2 ^ k = 2 * 2 ^ k := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hUstar : U ∈ USet (conjFamily K_b) :=
    ⟨R₁, hR₁Λ, hUR₁, inferInstance, hrel⟩
  have hy₀N : y₀ ∈ Subgroup.normalizer (K_b : Set ↥C) := by
    have hv2N : v₀ ^ 2 ∈ Subgroup.normalizer (K : Set G) :=
      d.late_JW_le_N_K d.late_JW ((J ⊓ W).pow_mem hvJW 2)
    have := mem_normalizer_conjSub_of_cross (K := K) (a := b) (1 : ↥C) y₀ (by
      rw [show (((1 : ↥C)) : G) = 1 from rfl, conjSub_one]
      exact hv2N)
    rwa [conjSub_one] at this
  have hUN : U ≤ Subgroup.normalizer (K_b : Set ↥C) :=
    (Subgroup.zpowers_le).mpr hy₀N
  have hJbne : J_b ≠ K_b := by
    intro h
    have h1 := hu₂
    rw [h] at h1
    have h2 := h1.eq hu₁
    exact d.late_ne_inv (congrArg Subtype.val h2)
  have hstar : J_b ∈ omegaStarNbr (conjFamily K_b) K_b := ⟨hJbΛ, hJbne, U, hUstar, hUJ, hUN⟩
  have hKbmap : K_b.map C.subtype = (K ⊓ C) := by
    have h1 := map_conjSub_crossIn (K := K) (a := b) (1 : ↥C)
    rw [conjSub_one, Subgroup.coe_one, conjSub_one] at h1
    exact h1
  have hnotnbr : J_b ∉ omegaNbr (conjFamily K_b) K_b := by
    rintro ⟨-, hne, R₀, hR, hRle, hRN⟩
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8'⟩ := exists_ne_comm_of_mem_rSetGen hΩg hR
    have hR2 := isPGroup_of_mem_rSet hR
    have hne' : conjSub (1 : G) ((K ⊓ C)) ≠
        conjSub c ((K ⊓ C)) := by
      intro h
      apply hne
      apply Subgroup.map_injective C.subtype_injective
      rw [hJb, map_conjSub_crossIn cY, hKbmap]
      simpa [conjSub_one] using h.symm
    have htw : conjSub c K ∉ twinSet (CoreAssembly.conjClass K) (conjSub (1 : G) K) := by
      rw [conjSub_one, hcK]
      exact d.late_J_not_twin
    refine d.t9_false_of_le_normalizer hzKa (c₁ := (1 : G)) (c₂ := c) (Subgroup.one_mem _)
      hcC hne' htw (hR2.map C.subtype)
      ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _ C.subtype_injective).toEquiv]
      omega
    · rw [← map_conjSub_crossIn cY]
      exact Subgroup.map_mono hRle
    · rw [conjSub_one, ← hKbmap]
      exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)
  have hnoconj : ∀ g ∈ pairNormalizers K_b J_b ⟨z, hzA⟩ ⟨t, htA⟩, conjSub g K_b ≠ J_b := by
    intro g hg hgJ
    have hg1 : (g : G) ∈ pairNormalizers (K_b.map C.subtype) (J_b.map C.subtype) z t :=
      T3Typed.map_pairNormalizers_le C.subtype K_b J_b ⟨z, hzA⟩ ⟨t, htA⟩ ⟨g, hg, rfl⟩
    have hJbmap : J_b.map C.subtype = conjSub c ((K ⊓ C)) := by
      rw [hJb]
      exact map_conjSub_crossIn cY
    have hKbK : K_b.map C.subtype ≤ K := by
      rw [hKbmap]
      exact inf_le_left
    have hJbJ : J_b.map C.subtype ≤ J := by
      rw [hJbmap, ← hcK]
      exact Subgroup.map_mono inf_le_left
    have hg2 : (g : G) ∈ pairNormalizers K J z t := r_pairNormalizers_mono hKbK hJbJ z t hg1
    have hgmap : conjSub (g : G) ((K ⊓ C)) =
        conjSub c ((K ⊓ C)) := by
      rw [← hJbmap, ← hgJ, ← hKbmap]
      exact (AscQuot.map_conjSub C.subtype g K_b).symm
    have hUG : Subgroup.zpowers (v₀ ^ 2) ≤ conjSub (g : G) K ⊓ J := by
      refine le_inf ?_ ?_
      · rw [Subgroup.zpowers_le]
        have h1 : v₀ ^ 2 ∈ conjSub c ((K ⊓ C)) := by
          rw [← hJbmap]
          exact ⟨y₀, hy₀J, rfl⟩
        rw [← hgmap] at h1
        exact Subgroup.map_mono inf_le_left h1
      · exact Subgroup.zpowers_le.mpr hv2J
    have hK1 : conjSub (g : G) K = J := by
      by_contra hne1
      have hK1Ω : conjSub (g : G) K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
      have h4 := (d.hyp.omega4 _ hK1Ω J d.late_mem_J hne1).1
      have hdvd : 2 ^ k ∣ Nat.card ↥(conjSub (g : G) K ⊓ J) := by
        have := Subgroup.card_dvd_of_le hUG
        rwa [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) h2v, hv₀o, pow_succ,
          Nat.mul_div_cancel _ (by norm_num)] at this
      have := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
      omega
    exact d.viol.no_conj (g : G) hg2 hK1
  exact ⟨hstar, hnotnbr, hu₁, hu₂, hnoconj⟩


end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
