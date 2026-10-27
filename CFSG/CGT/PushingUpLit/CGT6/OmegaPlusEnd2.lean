module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Glauberman
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceCore
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.ComponentClassification CFSG.CGT.PushingUpLit.CGT6
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pLayer_le_centralizer_of_normal_two {M : Type*} [Group M] [Finite M] (P : Subgroup M)
    [P.Normal] (hP : IsPGroup 2 P) : pLayer M 2 ≤ Subgroup.centralizer (P : Set M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact sSup_le fun J hJ => CatalogueBAlternating.pComponent_le_centralizer_normal_p 2 J P hJ hP

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem outer_isSolvable_of_proper_image (hS : SchreierFor Assembly.InCatalog)
    (hKP : Assembly.KProper Assembly.InCatalog Γ) {K : Subgroup Γ} (hKtop : K ≠ ⊤) {X : Type}
    [Group X] [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (f : K →* X)
    (hf : Function.Surjective f) : Group.IsSolvable (Outer X) := by
  set Z : Subgroup Γ := f.ker.map K.subtype with hZ
  have hZeq : Z.subgroupOf K = f.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective f.ker
  have : (Z.subgroupOf K).Normal := by
    rw [hZeq]
    infer_instance
  let e : K ⧸ Z.subgroupOf K ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZeq).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have : IsSimpleGroup (K ⧸ Z.subgroupOf K) := MulEquiv.isSimpleGroup e
  have hnab' : ∃ a b : K ⧸ Z.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hcat := hKP K Z hKtop (Subgroup.map_subtype_le _) ‹IsSimpleGroup _› hnab'
  have hout := hS (K ⧸ Z.subgroupOf K) hnab' hcat
  exact Group.isSolvable_of_isSolvable_injective
    (f := (OuterAutomorphisms.equivalence e).symm.toMonoidHom)
    (OuterAutomorphisms.equivalence e).symm.injective

theorem pLayer_centralizer_le_of_kProper (hS : SchreierFor Assembly.InCatalog)
    (hKP : Assembly.KProper Assembly.InCatalog Γ) {x : Γ} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    (pLayer (Subgroup.centralizer ({x} : Set Γ)) 2).map
      (Subgroup.centralizer ({x} : Set Γ)).subtype ≤ pLayer Γ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LBalance.pLayer_centralizer_le_pLayer_of_quotient hx fun L hLC hL => ?_
  by_cases hE : layer (Γ ⧸ pPrimeCore 2 Γ) = ⊤
  · rw [hE]
    exact le_top
  refine LBalance.pComponent_centralizer_le_layer (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    (LBalance.Quot.exists_mk_pow_eq_one hx) (fun K hK => ?_) hLC hL
  set π := QuotientGroup.mk' (pPrimeCore 2 Γ)
  have hKE : K ≤ layer (Γ ⧸ pPrimeCore 2 Γ) := le_sSup hK
  have hKtop : K.comap π ≠ ⊤ := by
    intro h
    apply hE
    refine eq_top_iff.mpr fun y _ => hKE ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Γ) y
    have hz : z ∈ K.comap π := h ▸ Subgroup.mem_top z
    exact hz
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2.1
  let g : K.comap π →* K := (π.comp (K.comap π).subtype).codRestrict K fun y => y.2
  have hg : Function.Surjective g := by
    rintro ⟨k, hk⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Γ) k
    exact ⟨⟨z, hk⟩, rfl⟩
  exact outer_isSolvable_of_proper_image hS hKP hKtop hK.1.2.2
    ((QuotientGroup.mk' (Subgroup.center K)).comp g)
    ((QuotientGroup.mk'_surjective _).comp hg)

theorem subnormal_of_subnormal_comm (hS : SchreierFor Assembly.InCatalog)
    (hKP : Assembly.KProper Assembly.InCatalog Γ) {D B : Subgroup Γ} (hDqs : Nine7.QS D)
    (hBqs : Nine7.QS B) (hDZ : Subgroup.center ↥D = ⊥) (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d)
    (hStarB : Nine7.Star B) {t : Γ} (ht : orderOf t = 2)
    (htB : B ≤ Subgroup.centralizer ({t} : Set Γ)) (hD : D.IsSubnormal) : B.IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqB : CFSG.IsQuasisimple ↥B :=
    ⟨⟨hBqs.1⟩, hBqs.2, Nine7.exists_noncomm_center_quotient hBqs⟩
  have hBL : B ≤ pLayer Γ 2 :=
    (Sol76.le_pLayer_of_isQuasisimple htB hqB (hStarB t ht htB)).trans
      (pLayer_centralizer_le_of_kProper hS hKP ⟨1, by rw [pow_one, ← ht, pow_orderOf_eq_one]⟩)
  have hqD : CFSG.IsQuasisimple ↥D :=
    ⟨⟨hDqs.1⟩, hDqs.2, Nine7.exists_noncomm_center_quotient hDqs⟩
  have hDp : IsPComponent 2 D := by
    refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 ⟨hqD, hD⟩ ?_
    intro hle
    have h1 : 2 ∣ Nat.card (pPrimeCore 2 Γ) :=
      (Nine7.even_card_of_qs hDqs).two_dvd.trans (Subgroup.card_dvd_of_le hle)
    exact absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card h1) (by norm_num)
  set K' : Subgroup Γ := sSup {J : Subgroup Γ | IsPComponent 2 J ∧ J ≠ D} with hK'
  have hK'D : K' ≤ Subgroup.centralizer (D : Set Γ) := by
    refine sSup_le fun J hJ => ?_
    have h := ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two D J
      hDp hJ.1).2 (Ne.symm hJ.2)).2.2.2 (Or.inl hqD)
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hL : pLayer Γ 2 = D ⊔ K' := by
    refine le_antisymm (sSup_le fun J hJ => ?_)
      (sup_le (le_sSup hDp) (sSup_le fun J hJ => le_sSup hJ.1))
    by_cases hJD : J = D
    · exact hJD ▸ le_sup_left
    · exact le_sup_of_le_right (le_sSup ⟨hJ, hJD⟩)
  have hDN : D ≤ Subgroup.normalizer (K' : Set Γ) :=
    (Subgroup.le_centralizer_iff.mp hK'D).trans (Subgroup.centralizer_le_normalizer _)
  have hBK' : B ≤ K' := by
    intro b hb
    have hbL : b ∈ ((D ⊔ K' : Subgroup Γ) : Set Γ) := hL ▸ hBL hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D K' hDN] at hbL
    obtain ⟨d, hd, k, hk, rfl⟩ := hbL
    have hdc : (⟨d, hd⟩ : D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro d'
      apply Subtype.ext
      have h1 : (d' : Γ) * (d * k) = d * k * d' := hDB d' d'.2 _ hb
      have h2 : (d' : Γ) * k = k * d' := Subgroup.mem_centralizer_iff.mp (hK'D hk) d' d'.2
      show (d' : Γ) * d = d * d'
      calc (d' : Γ) * d = (d' * (d * k)) * k⁻¹ := by group
        _ = (d * (k * d')) * k⁻¹ := by rw [h1]; group
        _ = (d * (d' * k)) * k⁻¹ := by rw [← h2]
        _ = d * d' := by group
    rw [hDZ, Subgroup.mem_bot] at hdc
    have hd1 : d = 1 := congrArg Subtype.val hdc
    show d * k ∈ K'
    rw [hd1, one_mul]
    exact hk
  obtain ⟨d₀, hd₀, hd₀2⟩ := Nine7.exists_involution_of_qs hDqs
  have hBd₀ : B ≤ Subgroup.centralizer ({d₀} : Set Γ) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDB d₀ hd₀ b hb).symm
  have hK'd₀ : K' ≤ Subgroup.centralizer ({d₀} : Set Γ) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hK'D hk) d₀ hd₀).symm
  have hBK's := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hK'd₀ (hStarB d₀ hd₀2 hBd₀)
  have hpn : (pLayer Γ 2).Normal := by
    have := CatalogueBPrimeJoin.pLayer_characteristic (G := Γ) (p := 2)
    infer_instance
  have hK'L : K' ≤ pLayer Γ 2 := hL ▸ le_sup_right
  have hK'n : (K'.subgroupOf (pLayer Γ 2)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK'L, hL]
    exact sup_le hDN Subgroup.le_normalizer
  exact Subgroup.IsSubnormal.trans hBK' hBK's
    (Subgroup.IsSubnormal.trans hK'L hK'n.isSubnormal hpn.isSubnormal)

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
