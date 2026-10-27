module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotAut
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem two_mul_add_one_le_pow (r : ℕ) : 2 * r + 1 ≤ 3 ^ r := by
  induction r with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem add_five_le_pow {r : ℕ} (hr : 2 ≤ r) : r + 5 ≤ 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem master_arith_trivial {r a m w : ℕ} (hr : 1 ≤ r) (ha : a ≤ 3) (hm : 2 ≤ m) (hw : 1 ≤ w)
    (h : 0 + w + 3 ^ r * m ≤ r + a + 0 + 3 ^ r * 0 + m) : False := by
  have hP := two_mul_add_one_le_pow r
  have h1 : (2 * r + 1) * m ≤ 3 ^ r * m := Nat.mul_le_mul_right m hP
  have h2 : (2 * r + 1) * 2 ≤ (2 * r + 1) * m := Nat.mul_le_mul_left _ hm
  nlinarith

theorem master_arith_center {r a m w mZ c z : ℕ} (hr : 1 ≤ r) (ha : a ≤ 3) (hm : 2 ≤ m)
    (hw : 1 ≤ w) (hz : z ≤ 1) (hc : c ≤ mZ)
    (h : mZ + w + 3 ^ r * m ≤ r + a + c + 3 ^ r * z + m) : r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hP := add_five_le_pow hr2
  have h1 : 3 ^ r * z ≤ 3 ^ r := by
    calc 3 ^ r * z ≤ 3 ^ r * 1 := Nat.mul_le_mul_left _ hz
      _ = 3 ^ r := mul_one _
  have h2 : 3 ^ r * 2 ≤ 3 ^ r * m := Nat.mul_le_mul_left _ hm
  nlinarith

section Facts

variable {S : Type*} [Group S] {J : Type} [Group J] [Finite J]

theorem isElemAbelian_of_le_closure_range {G : Type*} [Group G] {p : ℕ} {ι : Type*} {x : ι → G}
    (hc : ∀ i j, x i * x j = x j * x i) {E : Subgroup G}
    (hE : E ≤ Subgroup.closure (Set.range x)) (hE3 : ∀ g ∈ E, g ^ p = 1) :
    CFSG.Open.IsElemAbelian p E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hE3⟩
  refine closure_commute (s := Set.range x) ?_ a.1 (hE a.2) b.1 (hE b.2)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact hc i j

theorem rot_twoLocal_pos (d : RotData S) (π : S →* J) (hπ : π.ker ≤ Subgroup.center S) :
    1 ≤ CFSG.Open.GLATwoLocalRank 3 J ∧ ∃ t : J, orderOf t = 2 := by
  have ht1 : π d.t ≠ 1 := fun h1 => d.t_not_central (hπ (MonoidHom.mem_ker.2 h1))
  have ht2 : (π d.t) ^ 2 = 1 := by rw [← map_pow, d.t_sq, map_one]
  refine ⟨?_, π d.t, orderOf_eq_prime ht2 ht1⟩
  have hcomm : ∀ i j : Fin 1, (fun _ => π (d.g₁ * d.g₂ ^ 2)) i * (fun _ => π (d.g₁ * d.g₂ ^ 2)) j =
      (fun _ => π (d.g₁ * d.g₂ ^ 2)) j * (fun _ => π (d.g₁ * d.g₂ ^ 2)) i := fun _ _ => rfl
  obtain ⟨E, hE3, hEcl, hEcard⟩ := exists_elemAbelian_of_commute (k := 1)
    (fun _ => π (d.g₁ * d.g₂ ^ 2)) hcomm (by
      intro e he i
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at he
      have hmem : (d.g₁ * d.g₂ ^ 2) ^ e 0 ∈ Subgroup.center S :=
        hπ (MonoidHom.mem_ker.2 (by rw [map_zpow]; exact he))
      rw [zpow_u] at hmem
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact (d.g_indep _ _ hmem).1)
  have hEel : CFSG.Open.IsElemAbelian 3 E :=
    isElemAbelian_of_le_closure_range hcomm hEcl hE3
  have hEN : E ≤ Subgroup.normalizer ((Subgroup.zpowers (π d.t) : Subgroup J) : Set J) := by
    intro e he
    refine mem_normalizer_zpowers_of_commute ?_
    have : Subgroup.closure (Set.range fun _ : Fin 1 => π (d.g₁ * d.g₂ ^ 2)) ≤
        Subgroup.centralizer ({π d.t} : Set J) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, d.t_comm]
    exact Subgroup.mem_centralizer_singleton_iff.1 (this (hEcl he))
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian Nat.prime_three hEel
  have hk1 : 1 ≤ k := by
    have := hEcard
    rw [hk] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 this
  exact hk1.trans (le_glaTwoLocalRank_of_le_normalizer (by norm_num : 1 < 3)
    (by rw [Ne, Subgroup.zpowers_eq_bot]; exact ht1) (isPGroup_two_zpowers ht1 ht2) hEel hEN hk)

theorem rot_pRank_two (d : RotData S) (π : S →* J) (hπ : π.ker ≤ Subgroup.center S) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup J) := by
  have hcomm : ∀ i j : Fin 2, (![π d.g₁, π d.g₂] : Fin 2 → J) i *
      (![π d.g₁, π d.g₂] : Fin 2 → J) j =
      (![π d.g₁, π d.g₂] : Fin 2 → J) j * (![π d.g₁, π d.g₂] : Fin 2 → J) i := by
    have : π d.g₁ * π d.g₂ = π d.g₂ * π d.g₁ := by rw [← map_mul, ← map_mul, d.g_comm]
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · simpa using this
    · simpa using this.symm
    · rfl
  obtain ⟨E, hE3, hEcl, hEcard⟩ := exists_elemAbelian_of_commute (k := 2)
    (![π d.g₁, π d.g₂]) hcomm (by
      intro e he i
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at he
      have hmem : d.g₁ ^ e 0 * d.g₂ ^ e 1 ∈ Subgroup.center S :=
        hπ (MonoidHom.mem_ker.2 (by rw [map_mul, map_zpow, map_zpow]; simpa using he))
      fin_cases i
      · exact (d.g_indep _ _ hmem).1
      · exact (d.g_indep _ _ hmem).2)
  have hEel : CFSG.Open.IsElemAbelian 3 E :=
    isElemAbelian_of_le_closure_range hcomm hEcl hE3
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian Nat.prime_three hEel
  have hk2 : 2 ≤ k := by
    have := hEcard
    rw [hk] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 this
  exact hk2.trans (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hEel hk)

end Facts

section Reduced


theorem normalized_of_u3_component_reduced
    {X : Type} [Group X] [Finite X] (hO : CFSG.Open.GLAPPrimeCore 3 X = ⊥) {B J : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian 3 B)
    (hrank : CFSG.Open.GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B)
    (hJ : CFSG.Open.GLAPComponent 3 ⊤ J) {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* unitaryPSU h 3) :
    B ≤ Subgroup.normalizer (J : Set X) := by
  by_contra hnL
  have hLc : CFSG.Open.IsComponentOf J ⊤ := i116pI_isComponentOf hO hJ
  have hperf : commutator ↥J = ⊤ := hLc.2.2.1
  have hq8 : 2 < 2 ^ 3 := by norm_num
  have hcenter : Subgroup.center (unitarySU 2 3 F 3) = unitaryScalars h 3 :=
    center_unitarySU_three (h := h) hq8
  have hp3 : (1 : ℕ) < 3 := by norm_num
  by_cases hZ : Subgroup.center ↥J = ⊥
  ·
    let eJ : ↥J ≃* unitaryPSU h 3 :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
    let π : unitarySU 2 3 F 3 →* ↥J := eJ.symm.toMonoidHom.comp (unitaryProj h 3)
    have hπ : π.ker ≤ Subgroup.center (unitarySU 2 3 F 3) := by
      intro s hs
      rw [hcenter, ← ker_unitaryProj]
      have : eJ.symm (unitaryProj h 3 s) = 1 := hs
      exact (map_eq_one_iff _ eJ.symm.injective).1 this
    obtain ⟨hw, ht⟩ := rot_twoLocal_pos (rotDataSU h) π hπ
    have hm := rot_pRank_two (rotDataSU h) π hπ
    obtain ⟨r, a, hr1, hrel, hHa, hHr, hmaster⟩ :=
      i112_master Nat.prime_three hO hB hrank hJ hnL ht
    have ha : a ≤ 3 := by
      have hH' := (i112_isElemAbelian_H (L := J) hB).map (MulAut.congr eJ).toMonoidHom
      have := card_le_27_psu h _ hH'
      rw [Subgroup.card_map_of_injective (MulAut.congr eJ).injective, hHa] at this
      exact (Nat.pow_le_pow_iff_right hp3).1 (by simpa using this)
    have hcard1 : Nat.card ↥(Subgroup.center ↥J) = 1 := by rw [hZ]; exact Subgroup.card_bot
    have hZJ := i112_card_Z_eq_one (B := B) hLc hcard1
    have hz0 : CFSG.Open.pRank 3 (Subgroup.center ↥J) = 0 :=
      i112_pRank_eq_zero_of_card_le_one hp3 hcard1.le
    have hmZ0 : CFSG.Open.pRank 3 (i112J B J ⊓ Subgroup.centralizer (i112J B J : Set X)) = 0 :=
      i112_pRank_eq_zero_of_card_le_one hp3 hZJ.le
    have hc0 : CFSG.Open.pRank 3
        ((i112J B J ⊓ Subgroup.centralizer (i112J B J : Set X)) ⊓ B) = 0 :=
      i112_pRank_eq_zero_of_card_le_one hp3 ((Subgroup.card_le_of_le inf_le_left).trans hZJ.le)
    rw [hmZ0, hz0, hc0] at hmaster
    exact master_arith_trivial hr1 ha hm hw hmaster
  ·
    obtain ⟨ψ, hψ⟩ := KSU3Core.exists_mulEquiv_unitarySU_three_compat h hq8 hperf e hZ
    let π : unitarySU 2 3 F 3 →* ↥J := ψ.toMonoidHom
    have hπ : π.ker ≤ Subgroup.center (unitarySU 2 3 F 3) := by
      intro s hs
      have : ψ s = 1 := hs
      have hs1 : s = 1 := ψ.injective (by rw [this, map_one])
      rw [hs1]
      exact (Subgroup.center _).one_mem
    obtain ⟨hw, ht⟩ := rot_twoLocal_pos (rotDataSU h) π hπ
    have hm := rot_pRank_two (rotDataSU h) π hπ
    obtain ⟨r, a, hr1, hrel, hHa, hHr, hmaster⟩ :=
      i112_master Nat.prime_three hO hB hrank hJ hnL ht
    have hHel : CFSG.Open.IsElemAbelian 3 (i112H B J) := i112_isElemAbelian_H hB
    have hH' := hHel.map (MulAut.congr ψ.symm).toMonoidHom
    have hcardH' : Nat.card ↥((i112H B J).map (MulAut.congr ψ.symm).toMonoidHom) = 3 ^ a := by
      rw [Subgroup.card_map_of_injective (MulAut.congr ψ.symm).injective, hHa]
    have ha : a ≤ 3 := by
      have := card_le_27_su h _ hH'
      rw [hcardH'] at this
      exact (Nat.pow_le_pow_iff_right hp3).1 (by simpa using this)
    have hcenJ : Nat.card ↥(Subgroup.center ↥J) ≤ 3 := by
      have h1 := Subgroup.map_center_eq ψ
      have h2 : Nat.card ↥((Subgroup.center (unitarySU 2 3 F 3)).map (ψ : _ →* ↥J)) =
          Nat.card ↥(Subgroup.center (unitarySU 2 3 F 3)) :=
        Subgroup.card_map_of_injective ψ.injective
      rw [h1] at h2
      rw [h2]
      exact (rotDataSU h).center_card
    have hz1 : CFSG.Open.pRank 3 (Subgroup.center ↥J) ≤ 1 :=
      CFSG.SectionRank.pRank_le hp3 fun E hE _ => by
        simpa using (Subgroup.card_le_of_le hE).trans hcenJ
    have hc : CFSG.Open.pRank 3
        ((i112J B J ⊓ Subgroup.centralizer (i112J B J : Set X)) ⊓ B) ≤
        CFSG.Open.pRank 3 (i112J B J ⊓ Subgroup.centralizer (i112J B J : Set X)) :=
      CFSG.SectionRank.pRank_mono hp3 inf_le_left
    have hr : r = 1 := master_arith_center hr1 ha hm hw hz1 hc hmaster
    subst hr
    obtain ⟨r', a', -, hrel', hHa', -, hBrank⟩ := i112_pRank_formula Nat.prime_three hB hnL
    have hrr : r' = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hrel'.symm.trans hrel)
    have haa : a' = a := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hHa'.symm.trans hHa)
    subst hrr haa
    obtain ⟨x, hxB, hxn⟩ := SetLike.not_le_iff_exists.1 hnL
    let ψX : unitarySU 2 3 F 3 →* X := J.subtype.comp ψ.toMonoidHom
    have hψX : Function.Injective ψX := J.subtype_injective.comp ψ.injective
    have hψXr : ψX.range = J := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ.surjective, Subgroup.map_top,
        Subgroup.range_subtype]
    rcases Nat.lt_or_ge a' 3 with ha3 | ha3
    · obtain ⟨F', T, hT1, hT2, hFel, hFN, hFcard⟩ :=
        rot_rank_four (rotDataSU h) hB hLc hxB hxn ψX hψX hψXr
      obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian Nat.prime_three hFel
      have hk2 : CFSG.Open.pRank 3 (i112Bc B J) + 4 ≤ k := by
        rw [hk] at hFcard
        exact (Nat.pow_le_pow_iff_right hp3).1 hFcard
      have hk3 : k ≤ CFSG.Open.GLATwoLocalRank 3 X :=
        le_glaTwoLocalRank_of_le_normalizer hp3 hT1 hT2 hFel hFN hk
      omega
    · have ha3' : a' = 3 := le_antisymm ha ha3
      subst ha3'
      have hex : ∃ φ ∈ (i112H B J).map (MulAut.congr ψ.symm).toMonoidHom,
          φ ∉ (suConj h).range := by
        by_contra hcon
        push Not at hcon
        have hle : (i112H B J).map (MulAut.congr ψ.symm).toMonoidHom ≤ (suConj h).range := hcon
        have := KSU3Core.card_inf_range_suConj_le_nine h _ hH'
        rw [inf_eq_left.2 hle, hcardH'] at this
        norm_num at this
      obtain ⟨φ, hφH, hφ⟩ := hex
      obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.1 hφH
      obtain ⟨y', rfl⟩ := MonoidHom.mem_range.1 hα
      have hyB : (y' : X) ∈ B := i112A_le_B y'.2
      have hα3 : (i112Act B J y') ^ 3 = 1 := by
        rw [← map_pow]
        have : y' ^ 3 = 1 := Subtype.ext (by simpa using hB.2 _ hyB)
        rw [this, map_one]
      obtain ⟨ψ', σ, hσ3, hψ'⟩ := exists_field_model h ψ (i112Act B J y') hα3 hφ
      let ψ'X : unitarySU 2 3 F 3 →* X := J.subtype.comp ψ'.toMonoidHom
      have hψ'X : Function.Injective ψ'X := J.subtype_injective.comp ψ'.injective
      have hψ'Xr : ψ'X.range = J := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ'.surjective, Subgroup.map_top,
          Subgroup.range_subtype]
      have hy : ∀ s, (y' : X) * ψ'X s * (y' : X)⁻¹ = ψ'X (suField h σ s) := by
        intro s
        have := congrArg Subtype.val (hψ' s)
        rw [i112Act_apply] at this
        exact this
      obtain ⟨k, hk₁, hk₂, hkt⟩ := rotDataSU_field h σ
      have hσ1 : σ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hσ3
        omega
      have hnin : ∀ s, suField h σ ≠ MulAut.conj s := by
        intro s hs
        refine KSU3Core.suField_not_mem_range h hσ1 ?_
        rw [hs]
        exact ⟨⟨s, unitarySU_le_unitaryIsom3 s.2⟩,
          (CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.conj_eq_suConj s).symm⟩
      obtain ⟨F', T, hT1, hT2, hFel, hFN, hFcard⟩ :=
        rot_rank_five (rotDataSU h) hB hLc hxB hxn ψ'X hψ'X hψ'Xr hyB (suField h σ) hy k hk₁
          hk₂ hkt hnin
      obtain ⟨k', hk'⟩ := exists_card_eq_of_isElemAbelian Nat.prime_three hFel
      have hk2 : CFSG.Open.pRank 3 (i112Bc B J) + 5 ≤ k' := by
        rw [hk'] at hFcard
        exact (Nat.pow_le_pow_iff_right hp3).1 hFcard
      have hk3 : k' ≤ CFSG.Open.GLATwoLocalRank 3 X :=
        le_glaTwoLocalRank_of_le_normalizer hp3 hT1 hT2 hFel hFN hk'
      omega

end Reduced

end KSFourU
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
