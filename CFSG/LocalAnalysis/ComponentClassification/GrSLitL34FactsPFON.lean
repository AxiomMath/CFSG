module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFSpor
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.Sporadic.ONOddCore.ONan

public section

namespace CFSG.ComponentClassification.GrSLit.L34PF

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem pRank_two_le_one_of_card_le_two {Y : Type*} [Group Y] [Finite Y]
    (h : Nat.card Y ≤ 2) : pRank 2 Y ≤ 1 := by
  apply csSup_le'
  rintro r ⟨A, -, hA⟩
  have h1 : Nat.card A ≤ 2 := (Subgroup.card_le_card_group A).trans h
  rw [hA] at h1
  by_contra hr
  have h4 : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem pRank_two_le_one_of_isCyclic {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y] :
    pRank 2 Y ≤ 1 := by
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hexp : Monoid.exponent A ∣ 2 := @IsElementaryAbelian.exponent_dvd_p 2 A _ hA
  rw [IsCyclic.exponent_eq_card] at hexp
  have h1 : Nat.card A ≤ 2 := Nat.le_of_dvd (by norm_num) hexp
  rw [hcard] at h1
  by_contra hr
  have h4 : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega


theorem exists_centralizer_map_eq_onM {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .ONan) {t : S} (ht : orderOf t = 2) :
    ∃ φ : S →* Equiv.Perm (Fin ONSchreier.N), Function.Injective φ ∧
      (centralizer ({t} : Set S)).map φ = ONSchreier.onM := by
  set ψ : S ≃* ↥ONSchreier.Pv := (e : S ≃* NativeSporadic.ON).trans ONSchreier.onEquivPv
  have ht' : orderOf ((ψ t : ↥ONSchreier.Pv) : Equiv.Perm (Fin ONSchreier.N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨g, hg, hgt⟩ := Sporadic.ONOddCore.cti_on_all_involutions_conjugate _ (ψ t).2 ht'
  set φ : S →* Equiv.Perm (Fin ONSchreier.N) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (ONSchreier.Pv.subtype.comp ψ.toMonoidHom) with hφdef
  have hφ : ∀ x : S, φ x = g⁻¹ * ((ψ x : ↥ONSchreier.Pv) : Equiv.Perm (Fin ONSchreier.N)) * g := by
    intro x
    simp [hφdef]
  have hinj : Function.Injective φ := by
    intro x y hxy
    rw [hφ, hφ] at hxy
    have h1 : ((ψ x : ↥ONSchreier.Pv) : Equiv.Perm (Fin ONSchreier.N)) = ψ y := by
      have := congrArg (fun w => g * w * g⁻¹) hxy
      simpa [mul_assoc] using this
    exact ψ.injective (Subtype.ext h1)
  have hφt : φ t = ONSchreier.onz := by
    rw [hφ, hgt]
    group
  have hmemP : ∀ x : S, φ x ∈ ONSchreier.Pv := fun x => by
    rw [hφ]
    exact mul_mem (mul_mem (inv_mem hg) (ψ x).2) hg
  refine ⟨φ, hinj, ?_⟩
  rw [ONSchreier.onM_eq_centralizer_z]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨hmemP x, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff]
    rw [← hφt, ← map_mul, ← map_mul, hx]
  · intro hy
    obtain ⟨hyP, hyc⟩ := mem_inf.mp hy
    have hw : g * y * g⁻¹ ∈ ONSchreier.Pv := mul_mem (mul_mem hg hyP) (inv_mem hg)
    refine ⟨ψ.symm ⟨g * y * g⁻¹, hw⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply hinj
      have hφy : φ (ψ.symm ⟨g * y * g⁻¹, hw⟩) = y := by
        rw [hφ, MulEquiv.apply_symm_apply]
        group
      rw [map_mul, map_mul, hφy, hφt]
      rw [mem_centralizer_singleton_iff] at hyc
      exact hyc
    · rw [hφ, MulEquiv.apply_symm_apply]
      group

theorem rank_le_one_of_ON_inner {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .ONan) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hcomp : IsComponent (P.subgroupOf (fixedSubgroup σ)))
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) {t : S} (ht : σ = MulAut.conj t)
    (ht2 : orderOf t = 2) : pRank 2 ↥(Open.fusionZStar P) ≤ 1 := by
  have hZP := fusionZStar_eq_center_of_comp h hcomp htype
  have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
    rw [ht]
    ext x
    rw [mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  set C := centralizer ({t} : Set S) with hCdef
  have hPC : P ≤ C := hfix ▸ h.2.1
  have eP := subgroupOfEquivOfLe h.2.1
  have hq : IsQuasisimple P := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eP).1 hcomp.1
  have hperf : ⁅P, P⁆ = P := (Subgroup.isPerfect_iff).mp hq.1
  have hPL : P ≤ ⁅C, C⁆ := hperf ▸ Subgroup.commutator_mono hPC hPC
  obtain ⟨φ, hinj, hCmap⟩ := exists_centralizer_map_eq_onM e ht2
  have hLmap : (⁅C, C⁆).map φ = ONSchreier.onL := by
    rw [Subgroup.map_commutator, hCmap, ← ONSchreier.onL_eq_commutator]
  have hcardL : Nat.card ↥⁅C, C⁆ = 80640 := by
    rw [← Subgroup.card_map_of_injective hinj, hLmap, ONSchreier.card_onL]
  have hcardP : Nat.card P = 20160 * Nat.card ↥(Open.fusionZStar P) := by
    rw [← card_of_isL34Type htype]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  by_cases hsmall : Nat.card ↥(Open.fusionZStar P) ≤ 2
  · exact pRank_two_le_one_of_card_le_two hsmall
  ·
    have hdvd : Nat.card P ∣ 80640 := hcardL ▸ Subgroup.card_dvd_of_le hPL
    have hPeq : P = ⁅C, C⁆ := by
      refine Subgroup.eq_of_le_of_card_ge hPL ?_
      rw [hcardL]
      obtain ⟨m, hm⟩ := hdvd
      have hm1 : m = 1 := by
        rcases m with _ | _ | m
        · omega
        · rfl
        · exfalso
          have : 20160 * Nat.card ↥(Open.fusionZStar P) * 2 ≤ 80640 := by
            calc 20160 * Nat.card ↥(Open.fusionZStar P) * 2
                ≤ 20160 * Nat.card ↥(Open.fusionZStar P) * (m + 1 + 1) :=
                  Nat.mul_le_mul_left _ (by omega)
              _ = 80640 := by rw [← hcardP, ← hm]
          omega
      rw [hm, hm1, mul_one]
    have hcyc : IsCyclic ↥(center ↥P) := by
      let e1 : ↥P ≃* ↥ONSchreier.onL :=
        (MulEquiv.subgroupCongr hPeq).trans ((⁅C, C⁆.equivMapOfInjective φ hinj).trans
          (MulEquiv.subgroupCongr hLmap))
      have hZL : (center ↥ONSchreier.onL).map ONSchreier.onL.subtype = ONSchreier.onQ := by
        rw [← CFSG.centerIn_eq_map_center, ONSchreier.onL_centerIn]
      have hQc : IsCyclic ↥ONSchreier.onQ := by
        rw [ONSchreier.onQ]
        infer_instance
      let e2 : ↥(center ↥ONSchreier.onL) ≃* ↥ONSchreier.onQ :=
        ((center ↥ONSchreier.onL).equivMapOfInjective _ ONSchreier.onL.subtype_injective).trans
          (MulEquiv.subgroupCongr hZL)
      let e3 : ↥(center ↥P) ≃* ↥(center ↥ONSchreier.onL) :=
        (MulEquiv.subgroupMap e1 (center ↥P)).trans
          (MulEquiv.subgroupCongr (Subgroup.map_center_eq e1))
      exact isCyclic_of_surjective (e3.trans e2).symm.toMonoidHom (e3.trans e2).symm.surjective
    rw [hZP]
    exact pRank_two_le_one_of_isCyclic

theorem rank_le_one_of_ON (hONO : SolMax.ONOuterComponentsInput) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .ONan)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : pRank 2 ↥(Open.fusionZStar P) ≤ 1 := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree Sporadic.ONOddCore.sporadicOddCoreFree_ONan hna
      e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    exact rank_le_one_of_ON_inner e h hcomp htype ht ht2
  · exfalso
    have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
      ext x
      exact Iff.rfl
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    set φ := MulEquiv.subgroupCongr hfix
    have hB : IsComponent (L.map φ.toMonoidHom) :=
      ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
        Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩
    have hcB := hONO S ⟨e⟩ σ (MulEquiv.ext fun y => h.1 y) hout' _ hB
    have eL := L.equivMapOfInjective φ.toMonoidHom φ.injective
    have hq : Nat.card (↥(L.map φ.toMonoidHom) ⧸ center ↥(L.map φ.toMonoidHom)) =
        Nat.card (↥P ⧸ Open.fusionZStar ↥P) := by
      rw [Nat.card_congr eZ.toEquiv]
      exact Nat.card_congr (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).symm.toEquiv
    rw [hq, card_of_isL34Type htype] at hcB
    omega

end CFSG.ComponentClassification.GrSLit.L34PF
