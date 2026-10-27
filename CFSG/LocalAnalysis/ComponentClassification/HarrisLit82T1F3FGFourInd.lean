module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourSub
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools
public import CFSG.GH74.GLS.Balance.OResidual

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSolvableTwoComponentIn_subgroupOf_le {J A M : Subgroup G} (hJA : J ≤ A)
    (hAM : A ≤ M) (h : IsSolvableTwoComponentIn J A) :
    IsSolvableTwoComponentIn (J.subgroupOf M) (A.subgroupOf M) := by
  have hJM : J ≤ M := hJA.trans hAM
  let eA : ↥(A.subgroupOf M) ≃* ↥A := subgroupOfEquivOfLe hAM
  let eJ : ↥(J.subgroupOf M) ≃* ↥J := subgroupOfEquivOfLe hJM
  refine ⟨fun x hx => hJA hx, ?_, ?_, ?_⟩
  · have hmap : (J.subgroupOf A).map eA.symm.toMonoidHom =
        (J.subgroupOf M).subgroupOf (A.subgroupOf M) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨eA x, hx, eA.symm_apply_apply x⟩
    rw [← hmap]
    exact h.2.1.map eA.symm.surjective
  · apply map_injective M.subtype_injective
    rw [map_map, map_map]
    have h1 : M.subtype.comp (J.subgroupOf M).subtype = J.subtype.comp eJ.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    have h2 : M.subtype.comp (A.subgroupOf M).subtype = A.subtype.comp eA.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [h1, h2, ← map_map, ← map_map, pPrimeCore_map_iso 2 eJ, pPrimeCore_map_iso 2 eA]
    exact h.2.2.1
  · rcases h.2.2.2 with h1 | h1
    · obtain ⟨e⟩ := h1
      exact .inl ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans e⟩
    · obtain ⟨e⟩ := h1
      exact .inr ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans e⟩

theorem map_pPrimeCore_of_isSubnormal {D M : Subgroup G} (hDM : D ≤ M)
    (hD : (D.subgroupOf M).IsSubnormal) :
    (pPrimeCore 2 ↥D).map D.subtype = D ⊓ (pPrimeCore 2 ↥M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 (D.subgroupOf M) hD
  let e : ↥(D.subgroupOf M) ≃* ↥D := subgroupOfEquivOfLe hDM
  have h2 : M.subtype.comp (D.subgroupOf M).subtype = D.subtype.comp e.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  calc (pPrimeCore 2 ↥D).map D.subtype
      = ((pPrimeCore 2 ↥(D.subgroupOf M)).map e.toMonoidHom).map D.subtype := by
        rw [pPrimeCore_map_iso 2 e]
    _ = ((pPrimeCore 2 ↥(D.subgroupOf M)).map (D.subgroupOf M).subtype).map M.subtype := by
        rw [map_map, map_map, h2]
    _ = (((pPrimeCore 2 ↥M).subgroupOf (D.subgroupOf M)).map (D.subgroupOf M).subtype).map
          M.subtype := by rw [key]
    _ = (pPrimeCore 2 ↥M ⊓ D.subgroupOf M).map M.subtype := by rw [subgroupOf_map_subtype]
    _ = (pPrimeCore 2 ↥M).map M.subtype ⊓ D := by
        rw [Subgroup.map_inf_eq _ _ _ M.subtype_injective, subgroupOf_map_subtype,
          inf_eq_left.mpr hDM]
    _ = D ⊓ (pPrimeCore 2 ↥M).map M.subtype := inf_comm _ _

theorem oPrimeResidual_sup_eq {K L : Subgroup G} (hKp : Group.IsPerfect ↥K)
    (hLK : L ≤ normalizer (K : Set G)) (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K) :
    GH74.GLS.oPrimeResidual 2 ↥(K ⊔ L) = K.subgroupOf (K ⊔ L) := by
  have hKn : (K.subgroupOf (K ⊔ L)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hLK)
  apply le_antisymm
  · unfold GH74.GLS.oPrimeResidual
    rw [closure_le]
    rintro x ⟨k, hk⟩
    set ψ : ↥L →* ↥(K ⊔ L) ⧸ K.subgroupOf (K ⊔ L) :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right) with hψ
    have hψs : Function.Surjective ψ := by
      have h1 : K.subgroupOf (K ⊔ L) ⊔ L.subgroupOf (K ⊔ L) ≤
          ψ.range.comap (QuotientGroup.mk' _) := by
        apply sup_le
        · intro y hy
          rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
          exact one_mem _
        · intro y hy
          exact ⟨⟨y, hy⟩, rfl⟩
      rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self] at h1
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact h1 (mem_top y)
    obtain ⟨l, hl⟩ := hψs (QuotientGroup.mk x)
    obtain ⟨a, -, b, -, rfl, ⟨j, hj⟩, hbo⟩ := exists_pow_mul_coprime Nat.prime_two l
    have haK : ((a : ↥L) : G) ∈ K :=
      hO (GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element a.2
        ⟨j, by rw [← Subgroup.coe_pow, hj, Subgroup.coe_one]⟩)
    have hψa : ψ a = 1 := by
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact haK
    rw [map_mul, hψa, one_mul] at hl
    have h1 : orderOf (QuotientGroup.mk x : ↥(K ⊔ L) ⧸ K.subgroupOf (K ⊔ L)) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    have h2 : Nat.Coprime 2 (orderOf (QuotientGroup.mk x : ↥(K ⊔ L) ⧸ K.subgroupOf (K ⊔ L))) := by
      rw [← hl]
      exact Nat.Coprime.coprime_dvd_right (orderOf_map_dvd ψ b) hbo
    have h3 : orderOf (QuotientGroup.mk x : ↥(K ⊔ L) ⧸ K.subgroupOf (K ⊔ L)) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k h2).symm h1
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)
  · intro x hx
    have htop := T23.oPrimeResidual_two_eq_top hKp
    have hmem : (⟨(x : G), hx⟩ : ↥K) ∈ GH74.GLS.oPrimeResidual 2 ↥K := htop ▸ mem_top _
    have hle : (GH74.GLS.oPrimeResidual 2 ↥K).map (Subgroup.inclusion le_sup_left) ≤
        GH74.GLS.oPrimeResidual 2 ↥(K ⊔ L) := by
      unfold GH74.GLS.oPrimeResidual
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    exact hle ⟨⟨(x : G), hx⟩, hmem, rfl⟩

theorem isSimpleChevalleyOver_or_m11 (hK3 : KnownRowThree)
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) {z₁ z₂ : G} (hz₁ : orderOf z₁ = 2)
    (hz₂ : orderOf z₂ = 2) {L₂ K : Subgroup G}
    (hL₂ : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hz₂L : z₂ ∈ L₂) (hI : InductionType 3 ↥L₂) (hKc : IsTwoComponentIn K (centralizer {z₁}))
    (hO₂ : GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K)
    (hN : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G)) :
    IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) ∨
      Nonempty (↥K ⧸ pPrimeCore 2 ↥K ≃* ↥Blueprint.NativeSporadic.M11) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := centralizer ({z₁} : Set G) ⊓ centralizer {z₂} with hW
  have hL₂W : L₂ ≤ W := hL₂.elim (·.1) (·.1)
  have hKN : K ≤ K ⊔ L₂ := le_sup_left
  have hL₂N : L₂ ≤ K ⊔ L₂ := le_sup_right
  have hNC : K ⊔ L₂ ≤ centralizer {z₁} := sup_le hKc.1 (hL₂W.trans inf_le_left)
  have hNnorm : K ⊔ L₂ ≤ normalizer (K : Set G) := sup_le le_normalizer (hL₂W.trans hN)
  have hKn : (K.subgroupOf (K ⊔ L₂)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKN).mpr hNnorm
  have hz₂K : z₂ ∈ K := hO₂ (GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element hz₂L
    ⟨1, by rw [pow_one, ← hz₂, pow_orderOf_eq_one]⟩)
  have hON := oPrimeResidual_sup_eq hKc.2.2.1 (hL₂W.trans hN) hO₂
  let eK : ↥(GH74.GLS.oPrimeResidual 2 ↥(K ⊔ L₂)) ≃* ↥K :=
    (MulEquiv.subgroupCongr hON).trans (subgroupOfEquivOfLe hKN)
  have hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 ↥(K ⊔ L₂)) :=
    isTwoQuasisimple_of_mulEquiv eK.symm hKc.2.2
  have hKtop : K ≠ ⊤ := by
    intro h
    have hz₁Z : z₁ ∈ center G := by
      rw [mem_center_iff]
      intro g
      exact mem_centralizer_singleton_iff.mp (hKc.1 (h ▸ mem_top g))
    rw [CatLeaf.center_eq_bot_of_simple hnonab, mem_bot] at hz₁Z
    rw [hz₁Z, orderOf_one] at hz₁
    exact absurd hz₁ (by norm_num)
  obtain ⟨eKZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K
  have hq := hKc.2.2.2
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have : IsSimpleGroup (↥K ⧸ Open.fusionZStar ↥K) := eKZ.isSimpleGroup
  have hnab : ∃ a b : ↥K ⧸ Open.fusionZStar ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨eKZ.symm a, eKZ.symm b, fun h => hab (eKZ.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hcatK : Blueprint.Catalog (↥K ⧸ Open.fusionZStar ↥K) :=
    QuasithinUnique.catalog_of_kProper_of_surjective hKP K hKtop _ hnab
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv eK
  have hcatN := SectionRank.catalog_of_mulEquiv eZ hcatK
  have hz₂N : z₂ ∈ K ⊔ L₂ := hL₂N hz₂L
  have hz₂' : orderOf (⟨z₂, hz₂N⟩ : ↥(K ⊔ L₂)) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₂
  have hCN : (K ⊔ L₂) ⊓ centralizer {z₂} ≤ W := le_inf (inf_le_left.trans hNC) inf_le_right
  have hL₂NC : L₂ ≤ (K ⊔ L₂) ⊓ centralizer {z₂} := le_inf hL₂N (hL₂W.trans inf_le_right)
  have hcen : centralizer ({(⟨z₂, hz₂N⟩ : ↥(K ⊔ L₂))} : Set ↥(K ⊔ L₂)) =
      ((K ⊔ L₂) ⊓ centralizer {z₂}).subgroupOf (K ⊔ L₂) := by
    ext x
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  have hL₂' : IsTwoComponentIn (L₂.subgroupOf (K ⊔ L₂))
        (centralizer {(⟨z₂, hz₂N⟩ : ↥(K ⊔ L₂))}) ∨
      IsSolvableTwoComponentIn (L₂.subgroupOf (K ⊔ L₂))
        (centralizer {(⟨z₂, hz₂N⟩ : ↥(K ⊔ L₂))}) := by
    rcases hL₂ with hL₂ | hL₂
    · exact .inl (isTwoComponentIn_subgroupOf_inf hz₂N
        ⟨hL₂NC, L219.isSubnormal_subgroupOf_of_le hCN hL₂.2.1, hL₂.2.2⟩)
    · right
      rw [hcen]
      apply isSolvableTwoComponentIn_subgroupOf_le hL₂NC inf_le_left
      refine ⟨hL₂NC, L219.isSubnormal_subgroupOf_of_le hCN hL₂.2.1, ?_, hL₂.2.2.2⟩
      have hsplit : (K ⊔ L₂) ⊓ centralizer {z₂} = (K ⊓ W) ⊔ L₂ := by
        apply le_antisymm
        · rintro x ⟨hxN, hxz⟩
          have hxN' : (⟨x, hxN⟩ : ↥(K ⊔ L₂)) ∈
              ((K.subgroupOf (K ⊔ L₂) ⊔ L₂.subgroupOf (K ⊔ L₂) : Subgroup ↥(K ⊔ L₂)) :
                Set ↥(K ⊔ L₂)) := by
            rw [← subgroupOf_sup hKN hL₂N, subgroupOf_self]
            exact mem_top _
          rw [normal_mul] at hxN'
          obtain ⟨k, hk, l, hl, hkl⟩ := hxN'
          have hk' : (k : G) ∈ K := hk
          have hl' : (l : G) ∈ L₂ := hl
          have hx : x = (k : G) * l := (congrArg Subtype.val hkl).symm
          have hlz : (l : G) ∈ Subgroup.centralizer {z₂} := (hL₂W hl').2
          have hkz : (k : G) ∈ Subgroup.centralizer {z₂} := by
            have h1 : (k : G) = x * (l : G)⁻¹ := by rw [hx]; group
            rw [h1]
            exact mul_mem hxz (inv_mem hlz)
          rw [hx]
          exact mul_mem (mem_sup_left ⟨hk', hKc.1 hk', hkz⟩) (mem_sup_right hl')
        · exact sup_le (le_inf (inf_le_left.trans hKN) (inf_le_right.trans inf_le_right))
            hL₂NC
      have hKWn : ((K ⊓ W).subgroupOf W).Normal := by
        rw [normal_subgroupOf_iff inf_le_right]
        intro h k hh hk
        refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hN hk) h).mp (mem_inf.mp hh).1, ?_⟩
        exact W.mul_mem (W.mul_mem hk (mem_inf.mp hh).2) (W.inv_mem hk)
      have hAs : (((K ⊔ L₂) ⊓ centralizer {z₂}).subgroupOf W).IsSubnormal := by
        rw [hsplit, subgroupOf_sup inf_le_right hL₂W]
        exact CFSG.GroupTheory.isSubnormal_sup hKWn.isSubnormal hL₂.2.1
      rw [map_pPrimeCore_of_isSubnormal hCN hAs, ← hL₂.2.2.1]
      apply le_antisymm
      · exact le_inf ((map_subtype_le _).trans hL₂NC) le_rfl
      · exact inf_le_right
  have hz₂L' : (⟨z₂, hz₂N⟩ : ↥(K ⊔ L₂)) ∈ L₂.subgroupOf (K ⊔ L₂) := hz₂L
  let eL : ↥(L₂.subgroupOf (K ⊔ L₂)) ≃* ↥L₂ := subgroupOfEquivOfLe hL₂N
  have hI' : InductionType 3 ↥(L₂.subgroupOf (K ⊔ L₂)) :=
    inductionType_of_bar_equiv (QuotientGroup.congr _ _ eL.symm (pPrimeCore_map_iso 2 eL.symm)) hI
  rcases hK3 ↥(K ⊔ L₂) hY hcatN ⟨z₂, hz₂N⟩ hz₂' (L₂.subgroupOf (K ⊔ L₂)) hL₂' hz₂L' hI' with
    hch | ⟨⟨eM⟩⟩
  · exact .inl (isSimpleChevalleyOver_of_isChevalleyOver hKc.2.2
      (T23.isChevalleyOver_of_mulEquiv (QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)) hch))
  ·
    right
    set ψ : ↥(K ⊔ L₂) →* ↥Blueprint.NativeSporadic.M11 :=
      eM.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥(K ⊔ L₂))) with hψ
    have hψs : Function.Surjective ψ := eM.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψk : ∀ x, ψ x = 1 ↔ x ∈ pPrimeCore 2 ↥(K ⊔ L₂) := by
      intro x
      rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ eM.injective,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have : IsSimpleGroup ↥Blueprint.NativeSporadic.M11 :=
      ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    have hmap : (K.subgroupOf (K ⊔ L₂)).map ψ = ⊤ := by
      have := hKn.map ψ hψs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K.subgroupOf (K ⊔ L₂)).map ψ) with h | h
      · exfalso
        have h1 : ψ ⟨z₂, hz₂N⟩ = 1 := by
          rw [← mem_bot, ← h]
          exact mem_map_of_mem ψ (show (⟨z₂, hz₂N⟩ : ↥(K ⊔ L₂)) ∈ K.subgroupOf (K ⊔ L₂) from hz₂K)
        have h2 := Subgroup.orderOf_dvd_natCard _ ((hψk _).mp h1)
        rw [hz₂'] at h2
        exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp
          (pPrimeCore_coprime_card : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(K ⊔ L₂))))))
          (even_iff_two_dvd.mpr h2)
      · exact h
    set ψK := ψ.comp (K.subgroupOf (K ⊔ L₂)).subtype with hψK
    have hψKs : Function.Surjective ψK := by
      intro m
      have hm : m ∈ (K.subgroupOf (K ⊔ L₂)).map ψ := hmap ▸ mem_top m
      obtain ⟨x, hx, rfl⟩ := hm
      exact ⟨⟨x, hx⟩, rfl⟩
    have hkerK : ψK.ker = pPrimeCore 2 ↥(K.subgroupOf (K ⊔ L₂)) := by
      rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 _ hKn.isSubnormal]
      ext x
      rw [MonoidHom.mem_ker, hψK, MonoidHom.comp_apply, hψk, mem_subgroupOf]
      rfl
    let e1 : ↥(K.subgroupOf (K ⊔ L₂)) ⧸ pPrimeCore 2 ↥(K.subgroupOf (K ⊔ L₂)) ≃*
        ↥Blueprint.NativeSporadic.M11 :=
      (QuotientGroup.quotientMulEquivOfEq hkerK.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψK hψKs)
    let eKK : ↥(K.subgroupOf (K ⊔ L₂)) ≃* ↥K := subgroupOfEquivOfLe hKN
    exact ⟨(QuotientGroup.congr _ _ eKK.symm (pPrimeCore_map_iso 2 eKK.symm)).trans e1⟩

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
