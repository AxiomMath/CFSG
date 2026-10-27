module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256c2
import CFSG.Dihedral.GorensteinWalter.PGL2CharTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section PSL64

variable {F : Type} [Field F] [Finite F]

theorem charP_two_of_card_sixtyfour (hF : Nat.card F = 64) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (p := 2) (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem card_psl2_sixtyfour (hF : Nat.card F = 64) : Nat.card (PSL2 F) = 262080 := by
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num), hF]
  decide

theorem card_psl2_galoisField_two {m : ℕ} (hm : m ∣ 6) :
    Nat.card (PSL2 (GaloisField 2 m)) = 6 ∨ Nat.card (PSL2 (GaloisField 2 m)) = 60 ∨
      Nat.card (PSL2 (GaloisField 2 m)) = 504 ∨ Nat.card (PSL2 (GaloisField 2 m)) = 262080 := by
  have hm6 : m ≤ 6 := Nat.le_of_dvd (by norm_num) hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear _ 2 (by norm_num),
    GaloisField.card 2 m hm0]
  interval_cases m <;> first | exact absurd hm (by decide) | norm_num

theorem card_pgl2_galoisField_two {m : ℕ} (hm : 2 * m ∣ 6) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) = 6 ∨
      Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) = 504 := by
  have hm3 : m ≤ 3 := by
    have := Nat.le_of_dvd (by norm_num) hm
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  rw [CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm0]
  interval_cases m <;> first | exact absurd hm (by decide) | norm_num

theorem dickson_card_cases (hF : Nat.card F = 64) (H : Subgroup (PSL2 F)) :
    (∃ m : ℕ, Nat.card H = 2 ^ m) ∨ (IsCyclic H ∧ (Nat.card H ∣ 65 ∨ Nat.card H ∣ 63)) ∨
      (∃ z : ℕ, Nat.card H = 2 * z ∧ (z ∣ 65 ∨ z ∣ 63)) ∨ Nat.card H = 12 ∨ Nat.card H = 24 ∨
      Nat.card H = 60 ∨ (∃ m t : ℕ, 1 ≤ m ∧ t ∣ 63 ∧ Nat.card H = 2 ^ m * t) ∨
      Nat.card H = 6 ∨ Nat.card H = 504 ∨ Nat.card H = 262080 := by
  have hF' : Nat.card F = 2 ^ 6 := by rw [hF]; norm_num
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF' H with
    ⟨m, -, hc, -⟩ | ⟨z, hz, hc, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, hm1, -, -, ht, E, C, hEn, -, hEc, -, hCc, hdisj, hsup, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact Or.inl ⟨m, hc⟩
  · norm_num at hz
    exact Or.inr (Or.inl ⟨hcyc, hc ▸ hz⟩)
  · norm_num at hz
    refine Or.inr (Or.inr (Or.inl ⟨z, ?_, hz⟩))
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · norm_num at ht
    haveI := hEn
    have hcomp : E.IsComplement' C := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, t, hm1, ht, ?_⟩))))))
    rw [← hcomp.card_mul_card, hEc, hCc]
  · rw [Nat.card_congr e.toEquiv]
    rcases card_psl2_galoisField_two (m := m) (by simpa using hm) with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
  · rw [Nat.card_congr e.toEquiv]
    rcases card_pgl2_galoisField_two (m := m) (by simpa using hm) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem eq_top_of_sixty_dvd (hF : Nat.card F = 64) (H : Subgroup (PSL2 F))
    (h60 : 60 ∣ Nat.card H) (hne : Nat.card H ≠ 60) : H = ⊤ := by
  rcases dickson_card_cases hF H with ⟨m, hc⟩ | ⟨-, hc⟩ | ⟨z, hc, hz⟩ | hc | hc | hc | ⟨m, t, -, ht, hc⟩ |
      hc | hc | hc
  · exfalso
    rw [hc] at h60
    have h3 : 3 ∣ 2 ^ m := (by norm_num : 3 ∣ 60).trans h60
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · exfalso
    rcases hc with hc | hc
    · have := h60.trans hc
      norm_num at this
    · have := h60.trans hc
      norm_num at this
  · exfalso
    rw [hc] at h60
    have h30 : 30 ∣ z := by omega
    rcases hz with hz | hz
    · have := h30.trans hz
      norm_num at this
    · have := h30.trans hz
      norm_num at this
  · rw [hc] at h60
    norm_num at h60
  · rw [hc] at h60
    norm_num at h60
  · exact absurd hc hne
  · exfalso
    have h5 : 5 ∣ 2 ^ m * t := (by norm_num : 5 ∣ 60).trans (hc ▸ h60)
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5 with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h) (by norm_num)
    · have := h.trans ht
      norm_num at this
  · rw [hc] at h60
    norm_num at h60
  · rw [hc] at h60
    norm_num at h60
  · exact Subgroup.eq_top_of_card_eq H (by rw [hc, card_psl2_sixtyfour hF])

theorem isCyclic_of_card_nine (hF : Nat.card F = 64) (H : Subgroup (PSL2 F))
    (h9 : Nat.card H = 9) : IsCyclic H := by
  rcases dickson_card_cases hF H with ⟨m, hc⟩ | ⟨hcyc, -⟩ | ⟨z, hc, -⟩ | hc | hc | hc | ⟨m, t, hm1, -, hc⟩ |
      hc | hc | hc
  · exfalso
    rw [h9] at hc
    rcases m with _ | m
    · norm_num at hc
    · rw [pow_succ] at hc
      omega
  · exact hcyc
  · omega
  · omega
  · omega
  · omega
  · exfalso
    have h2 : 2 ∣ Nat.card H := hc ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) t
    rw [h9] at h2
    norm_num at h2
  · omega
  · omega
  · omega

theorem isCyclic_of_isPGroup_three (hF : Nat.card F = 64) (R : Subgroup (PSL2 F))
    (hR : IsPGroup 3 R) : IsCyclic R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : 3 ^ k ∣ 262080 := by
    rw [← hk, ← card_psl2_sixtyfour hF]
    exact Subgroup.card_subgroup_dvd_card R
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ∣ 262080 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  interval_cases k
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hk]; norm_num)
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hk]; norm_num)
  · exact isCyclic_of_card_nine hF R (by rw [hk]; norm_num)

theorem fixSubgroup_conj_map {S : Type*} [Group S] (γ α : MulAut S) :
    fixSubgroup (γ * α * γ⁻¹) = (fixSubgroup α).map γ.toMonoidHom := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSubgroup]
  simp only [MulAut.mul_apply]
  constructor
  · intro h
    have h1 := congrArg (fun z => γ.symm z) h
    simpa using h1
  · intro h
    have h1 := congrArg (fun z => γ z) h
    simpa using h1

theorem nonempty_fixSubgroup_psl2FieldAut (hF : Nat.card F = 64) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    Nonempty (fixSubgroup (psl2FieldAut F σ) ≃* alternatingGroup (Fin 5)) := by
  have hodd : Odd (orderOf σ) := by rw [hσ]; decide
  have heq : fixSubgroup (psl2FieldAut F σ) = (CFSG.GH74.GLS.IVK.pslIncl σ).range := by
    ext y
    rw [mem_fixSubgroup, CFSG.GH74.GLS.IVK.mem_range_pslIncl_iff σ hodd]
  have hcard4 : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) = 4 := by
    have h := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ, hF] at h
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) (h.trans (by norm_num))
  let e0 : fixSubgroup (psl2FieldAut F σ) ≃* (CFSG.GH74.GLS.IVK.pslIncl σ).range := MulEquiv.subgroupCongr heq
  let e1 : (CFSG.GH74.GLS.IVK.pslIncl σ).range ≃* PSL2 (CFSG.GH74.GLS.IVK.fixedField σ) :=
    (MonoidHom.ofInjective (CFSG.GH74.GLS.IVK.pslIncl_injective σ)).symm
  have : Fintype (CFSG.GH74.GLS.IVK.fixedField σ) := Fintype.ofFinite _
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (CFSG.GH74.GLS.IVK.fixedField σ) = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard4, GaloisField.card 2 2 (by norm_num)]
    norm_num
  let e2 := CFSG.Glauberman.Dickson.h826_pslEquiv (FiniteField.ringEquivOfCardEq hcard)
  obtain ⟨e3⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  exact ⟨e0.trans (e1.trans (e2.trans e3))⟩

theorem aut_order_three_cases (hF : Nat.card F = 64) (β : MulAut (PSL2 F)) (hβ : orderOf β = 3) :
    (∃ t : PSL2 F, β = MulAut.conj t) ∨ Nonempty (fixSubgroup β ≃* alternatingGroup (Fin 5)) := by
  haveI := charP_two_of_card_sixtyfour hF
  by_cases hD : β ∈ (pglAction F).range
  · left
    obtain ⟨g, rfl⟩ := hD
    obtain ⟨t, rfl⟩ := CFSG.GorensteinWalter.toPGL_surjective_of_charTwo' F g
    exact ⟨t, pglAction_toPGL F t⟩
  · right
    obtain ⟨σ, hσ, g, hβ'⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three β hβ hD
    obtain ⟨e⟩ := nonempty_fixSubgroup_psl2FieldAut hF hσ
    rw [hβ', fixSubgroup_conj_map]
    exact ⟨(((fixSubgroup (psl2FieldAut F σ)).equivMapOfInjective _
      (pglAction F g).injective).symm).trans e⟩

end PSL64

section Generic

variable {G : Type*} [Group G]

theorem commutator_eq_top_of_self {J : Subgroup G} (hJ : ⁅J, J⁆ = J) : commutator J = ⊤ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subtype_commutator, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem sixty_dvd_card_of_isAltType [Finite G] {L : Subgroup G} (hL5 : IsAltType 5 (barOf 3 L)) :
    60 ∣ Nat.card L := by
  obtain ⟨eL⟩ := hL5
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)
  rw [Nat.card_congr eL.toEquiv, Inputs256b.card_alt5] at h
  exact ⟨_, h⟩

theorem fixSubgroup_congr {S T : Type*} [Group S] [Group T] (e : S ≃* T) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map e.toMonoidHom := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.apply_eq_iff_eq_symm_apply

theorem center_eq_bot_of_isCyclic {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hperf : commutator Y = ⊤) (hO : GLAPPrimeCore p Y = ⊥)
    (hcyc : ∀ R : Subgroup (Y ⧸ Subgroup.center Y), IsPGroup p R → IsCyclic R) :
    Subgroup.center Y = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hpg := SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp hO
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (SchurFacts.prime_dvd_card_of_isPGroup hp hpg hne)
  have hz1 : (z : Y) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : Y) ^ p = 1 := by
    have h1 : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact congrArg Subtype.val h1
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p Y))
  refine CFSG.LocalAnalysis.RankThreeTheoremC.not_isMulCommutative_sylow_of_isPerfect ⟨hperf⟩ S
    z.2 hz1 hzp ?_
  have hRc : IsCyclic ((S : Subgroup Y).map (QuotientGroup.mk' (Subgroup.center Y))) :=
    hcyc _ (S.isPGroup'.map _)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  exact (CFSG.Timmesfeld.RankOne.commute_of_mem_comap_of_isCyclic le_rfl hRc
    (Subgroup.le_comap_map _ _ a.2) (Subgroup.le_comap_map _ _ b.2)).eq

theorem three_dvd_card_of_glaPComponent {G : Type} [Group G] [Finite G] {X J : Subgroup G} (hJ : GLAPComponent 3 X J) :
    3 ∣ Nat.card J := by
  by_contra h
  have hq := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have htop : GLAPPrimeCore 3 ↥J = ⊤ := by
    refine le_antisymm le_top (le_sSup ⟨inferInstance, ?_⟩)
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h
  haveI : Subsingleton (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  haveI : Subsingleton (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 J ⧸
      Subgroup.center (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 J)) :=
    QuotientGroup.mk_surjective.subsingleton
  haveI := hq.2
  exact not_subsingleton (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 J ⧸
    Subgroup.center (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 J)) inferInstance

end Generic

section Field64K

variable {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]

theorem card_of_equiv (hF : Nat.card F = 64) (e : K ≃* PSL2 F) : Nat.card K = 262080 :=
  (Nat.card_congr e.toEquiv).trans (card_psl2_sixtyfour hF)

theorem isCyclic_of_card_nine_of_equiv (hF : Nat.card F = 64) (e : K ≃* PSL2 F)
    (H : Subgroup K) (h9 : Nat.card H = 9) : IsCyclic H := by
  haveI := isCyclic_of_card_nine hF (H.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, h9])
  exact isCyclic_of_surjective (H.equivMapOfInjective e.toMonoidHom e.injective).symm
    (MulEquiv.surjective _)

theorem eq_top_of_sixty_dvd_of_equiv (hF : Nat.card F = 64) (e : K ≃* PSL2 F)
    (H : Subgroup K) (h60 : 60 ∣ Nat.card H) (hne : Nat.card H ≠ 60) : H = ⊤ := by
  have h := eq_top_of_sixty_dvd hF (H.map e.toMonoidHom)
    (by rwa [Subgroup.card_map_of_injective e.injective])
    (by rwa [Subgroup.card_map_of_injective e.injective])
  rw [eq_top_iff]
  intro k _
  have hk : e k ∈ H.map e.toMonoidHom := h ▸ Subgroup.mem_top _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hk
  exact hk

theorem aut_order_three_cases_of_equiv (hF : Nat.card F = 64) (e : K ≃* PSL2 F) (a : MulAut K)
    (ha : orderOf a = 3) :
    (∃ k : K, a = MulAut.conj k) ∨ Nonempty (fixSubgroup a ≃* alternatingGroup (Fin 5)) := by
  have hβ : orderOf (MulAut.congr e a) = 3 := by
    rw [MulEquiv.orderOf_eq, ha]
  rcases aut_order_three_cases hF _ hβ with ⟨t, ht⟩ | hf
  · left
    refine ⟨e.symm t, (MulAut.congr e).injective ?_⟩
    rw [ht]
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · right
    obtain ⟨f⟩ := hf
    exact ⟨((fixSubgroup a).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (fixSubgroup_congr e a).symm).trans f)⟩

theorem false_of_inner_comp (hF : Nat.card F = 64) (e : K ≃* PSL2 F)
    (hZ : Subgroup.center K = ⊥) {k : K} (ha : orderOf (MulAut.conj k) = 3) {J : Subgroup K}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj k)) J) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk3 : k ^ 3 = 1 := by
    have h1 : MulAut.conj (k ^ 3) = 1 := by rw [map_pow, ← ha, pow_orderOf_eq_one]
    have h2 : k ^ 3 ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut K => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * k ^ 3 = k ^ 3 * g * (k ^ 3)⁻¹ * k ^ 3 := by rw [h3]
        _ = k ^ 3 * g := by group
    rw [hZ] at h2
    exact h2
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ha
    norm_num at ha
  have hkJ : ∀ j ∈ J, k * j = j * k := by
    intro j hj
    have h1 : MulAut.conj k j = j := mem_fixSubgroup.1 (hJ.1 hj)
    rw [MulAut.conj_apply] at h1
    calc k * j = k * j * k⁻¹ * k := by group
      _ = j * k := by rw [h1]
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have h3J : 3 ∣ Nat.card J := three_dvd_card_of_glaPComponent hJ
  by_cases hkJm : k ∈ J
  · set z : ↥J := ⟨k, hkJm⟩ with hzdef
    have hz : z ∈ Subgroup.center ↥J :=
      Subgroup.mem_center_iff.2 fun j => Subtype.ext (hkJ j j.2).symm
    have hz1 : z ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
    have hzp : z ^ 3 = 1 := Subtype.ext (by simp [z, hk3])
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥J))
    apply CFSG.LocalAnalysis.RankThreeTheoremC.not_isMulCommutative_sylow_of_isPerfect
      ⟨commutator_eq_top_of_self hperf⟩ S hz hz1 hzp
    obtain ⟨j, hj⟩ := S.isPGroup'.exists_card_eq
    have hdvd : 3 ^ j ∣ 262080 := by
      rw [← hj, ← card_of_equiv hF e]
      exact (Subgroup.card_subgroup_dvd_card (S : Subgroup ↥J)).trans (Subgroup.card_subgroup_dvd_card J)
    have hj2 : j ≤ 2 := by
      by_contra h
      have : 3 ^ 3 ∣ 262080 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at this
    interval_cases j
    · haveI := isCyclic_of_card_dvd_prime (α := ↥(S : Subgroup ↥J)) (p := 3) (by rw [hj]; norm_num)
      exact IsCyclic.isMulCommutative
    · haveI := isCyclic_of_card_dvd_prime (α := ↥(S : Subgroup ↥J)) (p := 3) (by rw [hj]; norm_num)
      exact IsCyclic.isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hj
  · obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 h3J
    have hs3 : (s : K) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one s
      rw [hs] at h1
      exact congrArg Subtype.val h1
    have hs1 : (s : K) ≠ 1 := by
      intro h
      have h1 : s = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hs
      norm_num at hs
    have hcomm : Commute (s : K) k := (hkJ s s.2).symm
    have hkz : k ∉ Subgroup.zpowers (s : K) := fun h => hkJm ((Subgroup.zpowers_le.2 s.2) h)
    have h9 := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hs3 hk3 hcomm hs1 hkz
    have hcyc := isCyclic_of_card_nine_of_equiv hF e _ h9
    have hel := Inputs256c.isElemAbelian_closure_pair_three hs3 hk3 hcomm
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgo : orderOf g = 9 := by rw [← h9]; exact orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hel.2 g g.2)
    have h93 := orderOf_dvd_of_pow_eq_one hg3
    rw [hgo] at h93
    norm_num at h93

end Field64K

section Field64

theorem glaPComponent_self_of_alt5 {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (e : ↥J ≃* alternatingGroup (Fin 5)) :
    GLAPComponent 3 J J ∧ IsAltType 5 (barOf 3 J) := by
  haveI : IsSimpleGroup ↥J := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have h60 : Nat.card ↥J = 60 := (Nat.card_congr e.toEquiv).trans Inputs256b.card_alt5
  have hnc : ∃ a b : ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Inputs256b.alt5_noncomm
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have h3 : 3 ∣ Nat.card ↥J := by rw [h60]; norm_num
  refine ⟨Claims126.glaPComponent_of_simple_normal Nat.prime_three le_rfl
    (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) inferInstance hnc h3, ?_⟩
  have hO : GLAPPrimeCore 3 ↥J = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup Nat.prime_three h3
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩

theorem exists_equiv_psl2 {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hcore : GLAPPrimeCore 3 K = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hd64 : Inputs256c.IsL2Sixtyfour d)
    (hθ : Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 64 ∧ Subgroup.center K = ⊥ ∧
      Nonempty (K ≃* PSL2 F) := by
  obtain ⟨θ⟩ := hθ
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hdq, hq64⟩ := hd64
  dsimp only at hdq
  subst hdq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF : Nat.card (GaloisField q.p q.exponent) = 64 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, hq64]
  let e : (K ⧸ Subgroup.center K) ≃* PSL2 (GaloisField q.p q.exponent) :=
    θ.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hZ : Subgroup.center K = ⊥ := by
    refine center_eq_bot_of_isCyclic Nat.prime_three hK.1.1 hcore fun R hR => ?_
    haveI := isCyclic_of_isPGroup_three hF (R.map e.toMonoidHom) (hR.map _)
    exact isCyclic_of_surjective (R.equivMapOfInjective e.toMonoidHom e.injective).symm
      (MulEquiv.surjective _)
  refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hF, hZ, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))).trans e

theorem chev2Field64_holds : Inputs256c.Chev2Field64 := by
  intro K _ _ hK hcore _ _ d _ hd64 hθ x hx L hL hL5 y hyL hy
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, _, hF, hZ, ⟨e⟩⟩ := exists_equiv_psl2 hK hcore hd64 hθ
  have hLx : L ≤ fixSubgroup x := hL.1
  have hL' : GLAPComponent 3 (fixSubgroup x) L := by rwa [Inputs256b.fixedSub_eq] at hL
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hnotinner : ∀ k : K, x ≠ MulAut.conj k := by
    rintro k rfl
    exact false_of_inner_comp hF e hZ hx hL'
  obtain ⟨fx⟩ : Nonempty (fixSubgroup x ≃* alternatingGroup (Fin 5)) := by
    rcases aut_order_three_cases_of_equiv hF e x hx with ⟨k, hk⟩ | h
    · exact absurd hk (hnotinner k)
    · exact h
  have hfx60 : Nat.card (fixSubgroup x) = 60 := (Nat.card_congr fx.toEquiv).trans Inputs256b.card_alt5
  have hL60 : 60 ∣ Nat.card L := sixty_dvd_card_of_isAltType hL5
  have hLeq : L = fixSubgroup x :=
    Subgroup.eq_of_le_of_card_ge hLx (hfx60 ▸ Nat.le_of_dvd Nat.card_pos hL60)
  have hLcard : Nat.card L = 60 := by rw [hLeq, hfx60]
  obtain ⟨hAel, -⟩ := Inputs256c.agrp_facts hx hL hL5 hyL hy
  have hxA : x ∈ Prop1310a5b.Agrp x y := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyA : MulAut.conj y ∈ Prop1310a5b.Agrp x y :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set x' : MulAut K := x * MulAut.conj y with hx'def
  have hx'A : x' ∈ Prop1310a5b.Agrp x y := Subgroup.mul_mem _ hxA hyA
  obtain ⟨l₀, hl₀L, hl₀⟩ := Inputs256c.exists_not_commute hL5 hyL hy
  have hx'L : ∀ l ∈ L, x' l = y * l * y⁻¹ := by
    intro l hl
    show x (MulAut.conj y l) = _
    rw [MulAut.conj_apply]
    exact mem_fixSubgroup.1 (hLx (L.mul_mem (L.mul_mem hyL hl) (L.inv_mem hyL)))
  have hyl₀ : y * l₀ * y⁻¹ ≠ l₀ := by
    intro h
    apply hl₀
    calc l₀ * y = y * l₀ * y⁻¹ * y := by rw [h]
      _ = y * l₀ := by group
  have hx'1 : x' ≠ 1 := by
    intro h
    have h1 := hx'L l₀ hl₀L
    rw [h, MulAut.one_apply] at h1
    exact hyl₀ h1.symm
  have hx'3 : orderOf x' = 3 := orderOf_eq_prime (hAel.2 x' hx'A) hx'1
  have hx'out : ∀ k : K, x' ≠ MulAut.conj k := by
    intro k hk
    apply hnotinner (k * y⁻¹)
    have h1 : x = x' * (MulAut.conj y)⁻¹ := by rw [hx'def]; group
    rw [h1, hk, map_mul, map_inv]
  obtain ⟨fx'⟩ : Nonempty (fixSubgroup x' ≃* alternatingGroup (Fin 5)) := by
    rcases aut_order_three_cases_of_equiv hF e x' hx'3 with ⟨k, hk⟩ | h
    · exact absurd hk (hx'out k)
    · exact h
  set J : Subgroup K := fixSubgroup x' with hJdef
  obtain ⟨hJcomp, hJ5⟩ := glaPComponent_self_of_alt5 fx'
  have hJ60 : Nat.card J = 60 := (Nat.card_congr fx'.toEquiv).trans Inputs256b.card_alt5
  have hJL : ¬ J ≤ L := by
    intro hle
    have hJeq : J = L := Subgroup.eq_of_le_of_card_ge hle (by rw [hJ60, hLcard])
    have h1 : x' l₀ = l₀ := mem_fixSubgroup.1 (show l₀ ∈ J from hJeq ▸ hl₀L)
    rw [hx'L l₀ hl₀L] at h1
    exact hyl₀ h1
  let S : MulAut K → Set (Subgroup K) := fun a => {J' | (a = x ∧ J' = L) ∨ (a = x' ∧ J' = J)}
  have hLS : L ∈ S x := Or.inl ⟨rfl, rfl⟩
  have hJS : J ∈ S x' := Or.inr ⟨rfl, rfl⟩
  have hLK : L ≤ Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S := Inputs256c.le_kstar hxA hx1 hLS
  have hJK : J ≤ Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S := Inputs256c.le_kstar hx'A hx'1 hJS
  have htop : Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S = ⊤ := by
    refine eq_top_of_sixty_dvd_of_equiv hF e _ (hL60.trans (Subgroup.card_dvd_of_le hLK)) ?_
    intro h
    apply hJL
    have hKL : Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S = L :=
      (Subgroup.eq_of_le_of_card_ge hLK (by rw [h, hLcard])).symm
    exact hKL ▸ hJK
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · rintro a - - J' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hL
    · rw [Inputs256b.fixedSub_eq]
      exact hJcomp
  · intro Y hY hLY
    rw [htop] at hY
    exact Inputs256b.not_alt5_of_subnormal_top hK.1 hcore hx1 hLx hL5 hY hLY
  · rintro a - - J' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl hL5
    · exact Or.inl hJ5
  · exact le_iSup₂_of_le (f := fun (J' : Subgroup K) (_ : J' ∈ S x) => J') L hLS le_rfl

end Field64

section Vacuous

open CFSG.Yardstones.Md0ec50421ce4 (PSimple)

@[expose] def NoA5On (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (¬ ∃ (n : ℕ) (ε : Bool), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) S ∧ HasFixedPointFreeOrder ε n 3) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 → P d →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ β : MulAut S, β ^ 3 = 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
        ¬ IsAltType 5 (PSimple 3 J)

theorem NoA5On.mono {P Q : TauCeti.ValidLieTypeIndex → Prop} (h : NoA5On P) (hQP : ∀ d, Q d → P d) :
    NoA5On Q := fun S _ _ hs hnc hPi d hd hQ => h S hs hnc hPi d hd (hQP d hQ)

theorem NoA5On.or {P Q : TauCeti.ValidLieTypeIndex → Prop} (hP : NoA5On P) (hQ : NoA5On Q) :
    NoA5On fun d => P d ∨ Q d := by
  intro S _ _ hs hnc hPi d hd hPQ
  rcases hPQ with h | h
  · exact hP S hs hnc hPi d hd h
  · exact hQ S hs hnc hPi d hd h

theorem chev2On_of_noA5On {P : TauCeti.ValidLieTypeIndex → Prop} (h : NoA5On P) : Inputs256c.Chev2On P := by
  intro K _ _ hK hcore hnotPi _ d hd2 hP hθ x hx L hL hL5 y _ _
  exfalso
  have hq := hK.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hL' : GLAPComponent 3 (fixSubgroup x) L := by rwa [Inputs256b.fixedSub_eq] at hL
  obtain ⟨hJ', ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three x hL'
  obtain ⟨eA⟩ := Inputs256b.isAltType_pSimple hL5
  have hPi : ¬ ∃ (n : ℕ) (ε : Bool), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (K ⧸ Subgroup.center K) ∧
      HasFixedPointFreeOrder ε n 3 := fun hO => hnotPi ⟨hq, hcore, Or.inr (Or.inl hO)⟩
  exact h (K ⧸ Subgroup.center K) inferInstance hnab hPi d hd2 hP hθ _
    (Inputs1415.centerQuotientHom_pow_eq_one hx3) _ hJ' ⟨eJ.symm.trans eA⟩

end Vacuous

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256d

end
