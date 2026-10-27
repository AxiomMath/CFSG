module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporHS
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporJ2Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovJ2
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporM22

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem mem_of_pow_odd {S : Type*} [Group S] [Finite S] {C N : Subgroup S} (hNC : N ≤ C)
    (hn : (N.subgroupOf C).Normal) {k : ℕ} (hidx : (N.subgroupOf C).index ∣ 2 ^ k) {y : S}
    (hyC : y ∈ C) {m : ℕ} (hm : Odd m) (hy : y ^ m = 1) : y ∈ N := by
  set q := QuotientGroup.mk' (N.subgroupOf C) (⟨y, hyC⟩ : C)
  have h1 : orderOf q ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨y, hyC⟩ : C) ^ m = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  have h2 : orderOf q ∣ 2 ^ k := by
    refine (orderOf_dvd_natCard q).trans ?_
    rw [← Subgroup.index_eq_card]
    exact hidx
  have h3 : orderOf q = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj, pow_succ] at h1
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 ((dvd_mul_left 2 _).trans h1))
  have h4 : QuotientGroup.mk' (N.subgroupOf C) (⟨y, hyC⟩ : C) = 1 := orderOf_eq_one_iff.1 h3
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h4
  exact h4


set_option maxHeartbeats 1000000 in
theorem card_centralizer_of_component_j2 {S : Type} [Group S] (e : S ≃* NativeSporadic.J2)
    {s : S} (hs : orderOf s = 2) {P : Subgroup S} (hPle : P ≤ centralizer ({s} : Set S))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({s} : Set S)))) :
    Nat.card (centralizer ({s} : Set S)) = 240 := by
  have hc1 : CFSG.Assembly.IsComponentOf P (centralizer ({s} : Set S)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hPle).2 hcomp
  have hc2 := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := e.toMonoidHom)
    e.injective).2 hc1
  have hmapc : (centralizer ({s} : Set S)).map e.toMonoidHom =
      centralizer ({e s} : Set NativeSporadic.J2) := by
    rw [Sporadic.SmallOddCore.map_centralizer_eq_inf e.injective,
      MonoidHom.range_eq_top.2 e.surjective, top_inf_eq, Set.image_singleton]
    rfl
  rw [hmapc] at hc2
  have h240 := GSThmB.CovJ2.card_centralizer_of_component ((MulEquiv.orderOf_eq e s).trans hs) hc2
  rw [← h240, ← hmapc, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem false_of_j2 (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hfree : CatalogueU.SporadicOddCoreFree .J2)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .J2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (Quot Y) := isSimpleGroup_quot h.quasisimple h.oddCore
  have hna := nonabelian_quot h.quasisimple h.oddCore
  set e' := (quotEquiv h.oddCore).trans e
  set θ : Quot Y ≃* ↥J2Cover.P := e'.trans J2Cover.nativeEquivP
  obtain ⟨σ, hI⟩ := exists_image_of_oddCore h hTtop (oddCore_fixed_eq_bot hfree hna e')
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hI.proper.1 y) hI.proper.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => hI.proper.1 y
  have hCard := SporFix.card_fixedSubgroup_j2 e' hσ2
  set P := T.map (rho Y) with hPdef
  set C := fixedSubgroup σ with hCdef
  have hPC : Nat.card P ∣ Nat.card C := Subgroup.card_dvd_of_le hI.proper.2.1
  have hcP : Nat.card (P ⧸ center P) ∣ Nat.card P := Subgroup.card_quotient_dvd_card _
  have hdvd : Nat.card (T ⧸ center T) ∣ Nat.card C := hI.card ▸ hcP.trans hPC
  have hZT : Open.fusionZStar T = center T :=
    fusionZStar_eq_center_of_quasisimple hI.quasiT (by
      have := LocalCores.isQuasisimple_nontrivial hI.quasiT
      rw [hI.oddCoreT]; exact bot_ne_top)
  have hcT : Nat.card (T ⧸ Open.fusionZStar T) = Nat.card (T ⧸ center T) :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZT).toEquiv
  have hle : Nat.card (T ⧸ center T) ≤ 1920 := by
    have := Nat.le_of_dvd Nat.card_pos hdvd
    rcases hCard with h1 | h1 | h1 <;> omega
  obtain ⟨p, hp, hp2, hLp, hcp⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      LieModel (T ⧸ center T) .PSL 2 p 1 ∧
      (Nat.card (T ⧸ center T) = 60 ∨ Nat.card (T ⧸ center T) = 168) := by
    rcases h.typC with ⟨τ, n, p, f, hp, hp2, -, hLm⟩ | ⟨n, hn, -, -, ⟨eA⟩⟩ | ⟨hL, -⟩
    · have hLm' := Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZT) hLm
      rcases hCard with h1 | h1 | h1
      · have ht := SporLie.tuple_of_dvd_1920 hp2 hLm' ((h1 ▸ hdvd).trans (by norm_num))
        simp only [Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        exact ⟨5, by norm_num, by norm_num, hLm', Or.inl (card_of_lieModel_psl_two_five hLm')⟩
      · have ht := SporLie.tuple_of_dvd_21504 hp2 hLm' ((h1 ▸ hdvd).trans (by norm_num))
        simp only [Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        exact ⟨7, by norm_num, by norm_num, hLm', Or.inr (card_of_lieModel_psl_two_seven hLm')⟩
      · have ht := SporLie.tuple_of_dvd_1920 hp2 hLm' (h1 ▸ hdvd)
        simp only [Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        exact ⟨5, by norm_num, by norm_num, hLm', Or.inl (card_of_lieModel_psl_two_five hLm')⟩
    · exfalso
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have hcn : Nat.card (T ⧸ center T) = n.factorial / 2 := by
        rw [← hcT, card_fusionZStar_eq, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card,
          card_alternatingGroup, Fintype.card_fin]
      have h7 : Nat.factorial 7 / 2 ≤ n.factorial / 2 :=
        Nat.div_le_div_right (Nat.factorial_le hn)
      have h2520 : Nat.factorial 7 / 2 = 2520 := by decide
      omega
    · exfalso
      have h20160 : Nat.card (T ⧸ center T) = 20160 := by
        rw [← hcT, card_fusionZStar_eq]
        exact OddStandard.GlueL34.card_eq_of_lieModel_psl34 hL
      omega
  obtain ⟨t, hSL, -⟩ := exists_sl2Facts hGA hGC hI.quasiT
    (isPGroup_center_of_pPrimeCore_eq_bot hI.oddCoreT) hI.centerT hp hp2 hLp
  have hT2 : Nat.card T = 2 * Nat.card (T ⧸ center T) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [hSL.card_center] at h1
    rw [h1, mul_comm]
  obtain ⟨z, hz⟩ : ∃ z : center Y, z ≠ 1 := by
    have : Nontrivial (center Y) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hZ]
      norm_num
    exact exists_ne 1
  have hz2 : orderOf (z : Y) = 2 := by
    rw [Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ hz
    have h1 : orderOf z ∣ 2 := hZ ▸ orderOf_dvd_natCard z
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hZz : center Y = zpowers (z : Y) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [zpowers_le]
      exact z.2
    · rw [hZ, Nat.card_zpowers, hz2]
  set π₁ : Y →* ↥J2Cover.P := θ.toMonoidHom.comp (rho Y) with hπ₁def
  have hπ₁ : Function.Surjective π₁ := θ.surjective.comp (rho_surjective Y)
  have hker : π₁.ker = zpowers (z : Y) := by
    rw [← hZz, ← ker_rho h.oddCore]
    ext v
    simp only [hπ₁def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hLq : CFSG.Assembly.IsQuasisimple Y :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Y).2 h.quasisimple
  obtain ⟨hl1, hl11, hl15⟩ :=
    J2Cover.j2_double_cover_involution_lift_orders_fixCount hLq hz2 hZz π₁ hπ₁ hker
  have hπθ : ∀ v : Y, π₁ v = θ (rho Y v) := fun v => rfl
  have hinner : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range →
      ∃ s : Quot Y, orderOf s = 2 ∧ fixedSubgroup σ = centralizer ({s} : Set (Quot Y)) ∧
        Nat.card (centralizer ({s} : Set (Quot Y))) = 240 := by
    rintro ⟨s, rfl⟩
    have hs : orderOf s = 2 :=
      SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj (inferInstance) hna hσ2
    have hfix : fixedSubgroup (MulAut.conj s) = centralizer ({s} : Set (Quot Y)) := by
      ext x
      rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, MulAut.conj_apply,
        mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
      exact eq_comm
    refine ⟨s, hs, hfix, ?_⟩
    have hcomp := hI.compP
    rw [hfix] at hcomp
    exact card_centralizer_of_component_j2 (θ.trans J2Cover.nativeEquivP.symm) hs
      (hfix ▸ hI.proper.2.1) hcomp
  by_cases ht : rho Y t = 1
  ·
    have hPc : Nat.card P = Nat.card (T ⧸ center T) := by
      have h1 : Nat.card T = 2 * Nat.card P := hSL.card_map_rho h.oddCore ht
      omega
    have hno11 : ∀ x ∈ P, orderOf x = 2 →
        J2Cover.Models.fixCount (θ x : Equiv.Perm (Fin 315)) ≠ 11 := by
      rintro _ ⟨y, hy, rfl⟩ hx h11
      have h1 : orderOf (π₁ y) = 2 := by rw [hπθ, MulEquiv.orderOf_eq]; exact hx
      have h2 := hl11 y h1 (by rw [hπθ]; exact h11)
      have h3 : (⟨y, hy⟩ : T) * ⟨y, hy⟩ = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, ← sq, ← h2, pow_orderOf_eq_one]
        rfl)
      rcases hSL.unique _ h3 with h4 | h4
      · rw [show y = 1 from congrArg Subtype.val h4, orderOf_one] at h2
        norm_num at h2
      · rw [show y = (t : Y) from congrArg Subtype.val h4, ht, orderOf_one] at hx
        norm_num at hx
    have hZP : center P = ⊥ := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
      rw [hPc, ← hI.card] at h1
      have h0 : 0 < Nat.card (T ⧸ center T) := Nat.card_pos
      exact Subgroup.eq_bot_of_card_eq _ (by nlinarith)
    have hPs : IsSimpleGroup P := isSimpleGroup_of_quasisimple hI.quasiP hZP
    set P' := P.subgroupOf C with hP'def
    have ePP' : P ≃* P' := (subgroupOfEquivOfLe hI.proper.2.1).symm
    have : Nontrivial P' := LocalCores.isQuasisimple_nontrivial hI.compP.1
    have hP's : IsSimpleGroup P' := isSimpleGroup_of_mulEquiv' ePP'
    have hnab : ∃ a b : P', a * b ≠ b * a := exists_ne_of_quasisimple hI.compP.1
    have hP'card : Nat.card P' = Nat.card (T ⧸ center T) := by
      rw [← Nat.card_congr ePP'.toEquiv, hPc]
    by_cases hσin : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range
    · obtain ⟨s, hs, hfix, h240⟩ := hinner hσin
      have hC240 : Nat.card C = 240 := by rw [hCdef, hfix, h240]
      have hc60 : Nat.card (T ⧸ center T) = 60 := by
        rcases hcp with h1 | h1
        · exact h1
        · exfalso
          have h2 := hC240 ▸ hdvd
          rw [h1] at h2
          norm_num at h2
      have hnorm : P'.Normal := SolMax.FiveFHe.normal_of_isSubnormal_simple hI.compP.2 hnab
        (by rw [hP'card, hC240, hc60]; norm_num)
      have hidx : P'.index = 4 := by
        have h1 := P'.card_mul_index
        rw [hP'card, hc60, hC240] at h1
        omega
      obtain ⟨a, b, ha, hb, ha5, hb3, hx1, hx1f, -, -, -⟩ := j2_2B_elems_of_equiv θ hs h240
      have haC : a ∈ C := by rw [hCdef, hfix]; exact ha
      have hbC : b ∈ C := by rw [hCdef, hfix]; exact hb
      have haP := mem_of_pow_odd hI.proper.2.1 hnorm (k := 2) (by rw [hidx]; norm_num) haC
        (by decide) ha5
      have hbP := mem_of_pow_odd hI.proper.2.1 hnorm (k := 2) (by rw [hidx]; norm_num) hbC
        (by decide) hb3
      exact hno11 _ (mul_mem (mul_mem haP haP) hbP) hx1 hx1f
    · obtain ⟨h336, a, b, ha, hb, ha3, hb3, hx, hxf⟩ := j2_outer_elems_of_equiv θ hσσ hσin
      have hc168 : Nat.card (T ⧸ center T) = 168 := by
        rcases hcp with h1 | h1
        · exfalso
          have h2 := h336 ▸ hdvd
          rw [h1] at h2
          norm_num at h2
        · exact h1
      have hidx : P'.index = 2 := by
        have h1 := P'.card_mul_index
        rw [hP'card, hc168, h336] at h1
        omega
      have hnorm : P'.Normal := Subgroup.normal_of_index_eq_two hidx
      have haC : a ∈ C := (LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff).2 ha
      have hbC : b ∈ C := (LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff).2 hb
      have haP := mem_of_pow_odd hI.proper.2.1 hnorm (k := 1) (by rw [hidx]; norm_num) haC
        (by decide) ha3
      have hbP := mem_of_pow_odd hI.proper.2.1 hnorm (k := 1) (by rw [hidx]; norm_num) hbC
        (by decide) hb3
      exact hno11 _ (mul_mem (mul_mem (mul_mem haP haP) hbP) (mul_mem (mul_mem haP haP) hbP))
        hx hxf
  ·
    set d := rho Y t with hddef
    have hd : orderOf d = 2 := hSL.orderOf_rho ht
    have ht2 : orderOf (t : Y) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq]; exact hSL.mul_self) hSL.ne_one
    have h11 : J2Cover.Models.fixCount (θ d : Equiv.Perm (Fin 315)) = 11 := by
      have h1 : orderOf (π₁ t) = 2 := by rw [hπθ, MulEquiv.orderOf_eq]; exact hd
      rcases hl1 (θ d) (by rw [MulEquiv.orderOf_eq]; exact hd) with h | h
      · exact h
      · have := (hl15 t h1 (by rw [hπθ]; exact h)).2
        omega
    have h1920 := card_centralizer_of_eleven θ hd h11
    have hPle : P ≤ centralizer ({d} : Set (Quot Y)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact hSL.rho_commute ⟨x, hx⟩
    have hPT : Nat.card P = Nat.card T := by
      have hinj : ((rho Y).subgroupMap T).ker = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        rw [mem_bot]
        exact hSL.rho_injective h.oddCore ht (congrArg Subtype.val hx)
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((rho Y).subgroupMap T).ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        ((rho Y).subgroupMap_surjective T)).toEquiv, hinj, Subgroup.card_bot, mul_one] at h1
      exact h1.symm
    have hc60 : Nat.card (T ⧸ center T) = 60 := by
      have h1 := Subgroup.card_dvd_of_le hPle
      rw [hPT, hT2, h1920] at h1
      rcases hcp with h2 | h2
      · exact h2
      · rw [h2] at h1
        norm_num at h1
    have hP120 : Nat.card P = 120 := by rw [hPT, hT2, hc60]
    by_cases hσin : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range
    · obtain ⟨s, hs, hfix, h240⟩ := hinner hσin
      obtain ⟨a, b, ha, hb, ha5, hb3, hx1, -, hx2, -, hne⟩ := j2_2B_elems_of_equiv θ hs h240
      set P' := P.subgroupOf C
      have hP'card : Nat.card P' = 120 := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hI.proper.2.1).symm.toEquiv, hP120]
      have hC240 : Nat.card C = 240 := by rw [hCdef, hfix, h240]
      have hidx : P'.index = 2 := by
        have h1 := P'.card_mul_index
        rw [hP'card, hC240] at h1
        omega
      have hnorm : P'.Normal := Subgroup.normal_of_index_eq_two hidx
      have haC : a ∈ C := by rw [hCdef, hfix]; exact ha
      have hbC : b ∈ C := by rw [hCdef, hfix]; exact hb
      have haP := mem_of_pow_odd hI.proper.2.1 hnorm (k := 1) (by rw [hidx]; norm_num) haC
        (by decide) ha5
      have hbP := mem_of_pow_odd hI.proper.2.1 hnorm (k := 1) (by rw [hidx]; norm_num) hbC
        (by decide) hb3
      have huniq : ∀ x ∈ P, orderOf x = 2 → x = d := by
        rintro _ ⟨y, hy, rfl⟩ hx
        have hy2 : rho Y y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hx)
        have h1 : (⟨y, hy⟩ : T) * ⟨y, hy⟩ = 1 := hSL.rho_injective h.oddCore ht (by
          rw [Subgroup.coe_mul, map_mul, ← sq]
          exact hy2)
        rcases hSL.unique _ h1 with h2 | h2
        · exfalso
          rw [show y = 1 from congrArg Subtype.val h2, map_one, orderOf_one] at hx
          norm_num at hx
        · rw [show y = (t : Y) from congrArg Subtype.val h2]
      exact hne ((huniq _ (mul_mem (mul_mem haP haP) hbP) hx1).trans
        (huniq _ (mul_mem (mul_mem haP hbP) haP) hx2).symm)
    · obtain ⟨h336, -⟩ := j2_outer_elems_of_equiv θ hσσ hσin
      have h1 := hP120 ▸ hPC
      rw [hCdef, h336] at h1
      norm_num at h1

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
