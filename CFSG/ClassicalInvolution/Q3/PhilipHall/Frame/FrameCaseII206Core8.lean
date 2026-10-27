module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Dec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement

theorem inv_eq_mul_of_sq {G : Type} [Group G] {z x : G} (hz : z * z = 1) (hx : x * x = z) :
    x⁻¹ = z * x := by
  have h : x * (z * x) = 1 := by
    rw [← hx]
    calc x * (x * x * x) = (x * x) * (x * x) := by group
      _ = 1 := by rw [hx, hz]
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem inZ_of_signs {G : Type} [Group G] {z t x x' a a' : G} (hz2 : z * z = 1) (hx2 : x * x = z)
    (hx'2 : x' * x' = z) (hzx : z * x = x * z) (hxx' : x * x' = t) (ha : a = x ∨ a = x⁻¹)
    (ha' : a' = x' ∨ a' = x'⁻¹) : InZ z t (a * a') := by
  have hxi : x⁻¹ = z * x := inv_eq_mul_of_sq hz2 hx2
  have hx'i : x'⁻¹ = z * x' := inv_eq_mul_of_sq hz2 hx'2
  unfold InZ
  rcases ha with ha | ha <;> rcases ha' with ha' | ha' <;> rw [ha, ha']
  · exact Or.inr (Or.inr (Or.inl hxx'))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [hx'i]
    calc x * (z * x') = (x * z) * x' := by group
      _ = (z * x) * x' := by rw [hzx]
      _ = z * t := by rw [mul_assoc, hxx']
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [hxi, mul_assoc, hxx']
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [hxi, hx'i]
    calc z * x * (z * x') = z * (x * z) * x' := by group
      _ = z * (z * x) * x' := by rw [hzx]
      _ = (z * z) * (x * x') := by group
      _ = t := by rw [hz2, one_mul, hxx']

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Core8

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem Std20Frame.not_mem_K_of_sq {a : G} (ha : a ∈ R') (ha2 : a * a = z) : a ∉ K := fun h =>
  TwinExact.not_mem_inf_of_sq d.late_hΩ d.late_mem_K d.late_mem_K' d.K_ne_K' d.viol.hzK ha2
    ⟨h, d.hR'.1 ha⟩

theorem Std20Frame.not_innerOn_of_sq_eq {w b : G} (hwX : w ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (hwb : w * w = b) (hbKK : b ∈ K ⊔ K') (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbz : b ≠ z) :
    ¬ InnerOn K w ∧ ¬ InnerOn K' w := by
  obtain ⟨g, hg, hgK⟩ := d.swap
  have hwN := (sec20X_le_normalizers_frame d) hwX
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := sq_mem_trivialOnQuot_of_innerOn d hwN.1 h
    rw [hwb] at this
    exact not_trivialOnQuot_of_invol d hbKK hb2 hb1 hbz this
  · have hw' : g⁻¹ * w * g ∈ Subgroup.normalizer (K : Set G) :=
      conj_swap_mem_normalizer d hg hgK hwN.2
    rw [← hgK] at h
    have h' := innerOn_swap' h
    have := sq_mem_trivialOnQuot_of_innerOn d hw' h'
    have e : (g⁻¹ * w * g) * (g⁻¹ * w * g) = g⁻¹ * b * g := by
      rw [← hwb]; group
    rw [e] at this
    refine not_trivialOnQuot_of_invol d (conj_swap_sup d hg hgK hbKK) ?_ ?_ ?_ this
    · calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
        _ = 1 := by rw [hb2]; group
    · intro h1
      apply hb1
      have : b = g * 1 * g⁻¹ := by rw [← h1]; group
      simpa using this
    · intro h1
      apply hbz
      have hgz : g * z = z * g := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm.symm
      have : b = g * z * g⁻¹ := by rw [← h1]; group
      rw [this, hgz]; group

theorem Std20Frame.inZ_of_sq_eq (c3 : Concl20_3 K K' V z) {a a' w : G} (ha : a ∈ R) (ha' : a' ∈ R')
    (ha2 : a * a = z) (ha'2 : a' * a' = z)
    (hwX : w ∈ sec20X (CoreAssembly.conjClass K) z K K') (hwb : w * w = a * a') :
    InZ z t (a * a') := by
  obtain ⟨eK⟩ := kbar_equiv_q8 d
  obtain ⟨eK'⟩ := d.kbar_equiv_q8'
  have hzK := d.viol.hzK
  have hz2 : z * z = 1 := hzK.sq
  have hRK : R ≤ K := d.hR.1
  have hR'K' : R' ≤ K' := d.hR'.1
  have hcomm : a * a' = a' * a := d.late_R_R'_comm ha ha'
  have hb2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a' a a', ← hcomm]; group
      _ = 1 := by rw [ha2, ha'2, hz2]
  have hbKK : a * a' ∈ K ⊔ K' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (hRK ha)) (Subgroup.mem_sup_right (hR'K' ha'))
  have hb1 : a * a' ≠ 1 := by
    intro h
    have e : a' = a⁻¹ := eq_inv_of_mul_eq_one_right h
    exact d.not_mem_K_of_sq ha' ha'2 (e ▸ K.inv_mem (hRK ha))
  have hbz : a * a' ≠ z := by
    intro h
    have e : a' = a⁻¹ * z := by rw [← h]; group
    exact d.not_mem_K_of_sq ha' ha'2 (e ▸ K.mul_mem (K.inv_mem (hRK ha)) hzK.mem)
  obtain ⟨hwout, hwout'⟩ := d.not_innerOn_of_sq_eq hwX hwb hbKK hb2 hb1 hbz
  have hXN := frameX_le_N d
  have hXN' : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (K' : Set G) :=
    fun _ hx => ((sec20X_le_normalizers_frame d) hx).2
  obtain ⟨v₀, hv₀V, -, hv₀1, hv₀t⟩ := exists_gen_V d
  have hv₀X := d.V_le_X hv₀V
  obtain ⟨hv₀o, hv₀o'⟩ := frame203Outer G K K' J S R R' W V z t d v₀ hv₀V hv₀1
  obtain ⟨x, hxKW, x', hx'KW, hx2, hx'2, hxx'⟩ := d.exists_four_gens_eq_t
  have hxR : x ∈ R := by rw [d.late_R_eq]; exact ⟨hxKW.1, d.hWS hxKW.2⟩
  have hx'R' : x' ∈ R' := by rw [d.late_R'_eq]; exact ⟨hx'KW.1, d.hWS hx'KW.2⟩
  have hv₀W : v₀ ∈ W := d.hVW hv₀V
  have hv₀x : v₀ * x * v₀⁻¹ = x := by
    rw [d.late_hWc v₀ hv₀W x hxKW.2]; group
  have hv₀x' : v₀ * x' * v₀⁻¹ = x' := by
    rw [d.late_hWc v₀ hv₀W x' hx'KW.2]; group
  have hwba : w * (a * a') * w⁻¹ = a * a' := by
    rw [← hwb]; group
  have hwba' : w * (a' * a) * w⁻¹ = a' * a := by
    rw [← hcomm]; exact hwba
  have htK : t ∈ kerG K := d.M_le_kerG (Subgroup.mem_sup_right d.htKK)
  have htK' : t ∈ kerG K' := d.M_le_kerG' (Subgroup.mem_sup_right d.htKK)
  have hσ1 : psiK K ⟨v₀, hXN hv₀X⟩ ≠ 1 := fun h => hv₀o ((psiK_eq_one_iff K eK _).mp h)
  have hσ1' : psiK K' ⟨v₀, hXN' hv₀X⟩ ≠ 1 := fun h => hv₀o' ((psiK_eq_one_iff K' eK' _).mp h)
  have hσ2 : psiK K ⟨v₀, hXN hv₀X⟩ * psiK K ⟨v₀, hXN hv₀X⟩ = 1 := by
    obtain ⟨htN, h3⟩ := mem_kerG.mp htK
    rw [← map_mul]
    have e2 : (⟨v₀, hXN hv₀X⟩ * ⟨v₀, hXN hv₀X⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨t, htN⟩ := Subtype.ext hv₀t
    rw [e2]
    exact h3
  have hσ2' : psiK K' ⟨v₀, hXN' hv₀X⟩ * psiK K' ⟨v₀, hXN' hv₀X⟩ = 1 := by
    obtain ⟨htN, h3⟩ := mem_kerG.mp htK'
    rw [← map_mul]
    have e2 : (⟨v₀, hXN' hv₀X⟩ * ⟨v₀, hXN' hv₀X⟩ : ↥(Subgroup.normalizer (K' : Set G))) =
        ⟨t, htN⟩ := Subtype.ext hv₀t
    rw [e2]
    exact h3
  have hσ := d.psiK_eq_of_not_innerOn c3 eK hXN d.M_le_kerG hv₀V hv₀t hwX hwout
  have hσ' := d.psiK_eq_of_not_innerOn c3 eK' hXN' d.M_le_kerG' hv₀V hv₀t hwX hwout'
  have hzO : z ∉ oddCoreOf K := not_mem_oddCoreOf_of_invol hzK.ne_one hz2
  have hzO' : z ∉ oddCoreOf K' := not_mem_oddCoreOf_of_invol hzK.ne_one hz2
  have hax := eq_or_eq_inv_of_psiK_eq eK d.hR.2.1 hRK (le_trivialOnQuot_K d) hzO hxR hx2 ha ha2
    (hR'K' ha') (hXN hwX) (hXN' hwX) hwba (hXN hv₀X) hv₀x hσ hσ1 hσ2
  have hax' := eq_or_eq_inv_of_psiK_eq eK' d.hR'.2.1 hR'K' (le_trivialOnQuot_K' d) hzO' hx'R' hx'2
    ha' ha'2 (hRK ha) (hXN' hwX) (hXN hwX) hwba' (hXN' hv₀X) hv₀x' hσ' hσ1' hσ2'
  have hzx : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff.mp
    (d.hSz (d.hWS hxKW.2))).symm
  have hzx' : z * x' = x' * z := (Subgroup.mem_centralizer_singleton_iff.mp
    (d.hSz (d.hWS hx'KW.2))).symm
  exact inZ_of_signs hz2 hx2 hx'2 hzx hxx' hax hax'

theorem Std20Frame.inZ_of_mem_sup_of_conj (c3 : Concl20_3 K K' V z) {b g : G} (hb : b ∈ R ⊔ R')
    (hb2 : b * b = 1) (hg : g * z * g⁻¹ = b) : InZ z t b := by
  obtain ⟨eR⟩ := d.nonempty_R_equiv
  obtain ⟨eR'⟩ := d.nonempty_R'_equiv
  obtain ⟨eK⟩ := kbar_equiv_q8 d
  have hzK := d.viol.hzK
  have hzK' := d.late_hzK'
  have hRK : R ≤ K := d.hR.1
  have hR'K' : R' ≤ K' := d.hR'.1
  have hsmall : ∀ y ∈ K, y * y = 1 → InZ z t y := fun y hy hy2 => by
    rcases hzK.unique y hy hy2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hsmall' : ∀ y ∈ K', y * y = 1 → InZ z t y := fun y hy hy2 => by
    rcases hzK'.unique y hy hy2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hb' : b ∈ ((R ⊔ R' : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R R' d.late_R'_le_N_R] at hb'
  obtain ⟨a, ha, a', ha', hab⟩ := hb'
  replace hab : a * a' = b := hab
  replace ha : a ∈ R := ha
  replace ha' : a' ∈ R' := ha'
  subst hab
  rcases mem_cases_of_equiv_q8 hzK hRK eR ha with h | h | ha2
  · rw [h, one_mul] at hb2 ⊢
    exact hsmall' a' (hR'K' ha') hb2
  · rw [h] at hb2 ⊢
    exact hsmall' _ (K'.mul_mem hzK'.mem (hR'K' ha')) hb2
  rcases mem_cases_of_equiv_q8 hzK' hR'K' eR' ha' with h | h | ha'2
  · rw [h, mul_one] at hb2 ⊢
    exact hsmall a (hRK ha) hb2
  · rw [h] at hb2 ⊢
    exact hsmall _ (K.mul_mem (hRK ha) hzK.mem) hb2
  have hbKK : a * a' ∈ K ⊔ K' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (hRK ha)) (Subgroup.mem_sup_right (hR'K' ha'))
  have hb1 : a * a' ≠ 1 := by
    intro h
    have e : a' = a⁻¹ := eq_inv_of_mul_eq_one_right h
    exact d.not_mem_K_of_sq ha' ha'2 (e ▸ K.inv_mem (hRK ha))
  have hbz : a * a' ≠ z := by
    intro h
    have e : a' = a⁻¹ * z := by rw [← h]; group
    exact d.not_mem_K_of_sq ha' ha'2 (e ▸ K.mul_mem (K.inv_mem (hRK ha)) hzK.mem)
  have hBb : IsUniqueInvolution (conjSub g K) (a * a') := by
    have := hzK.conj g
    rwa [hg] at this
  have hBΩ : conjSub g K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
  have hBtw : conjSub g K ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, w, hw1, hw2⟩
    exact hbz ((hBb.eq hw2).trans (hzK.eq hw1).symm)
  have hbC : a * a' ∈ Subgroup.centralizer ({z} : Set G) :=
    d.hSz ((S : Subgroup G).mul_mem (d.hRS ha) (d.hR'S ha'))
  obtain ⟨V₀, hV₀, hbV₀⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self hb2)
    (Subgroup.zpowers_le.mpr ⟨hBb.mem, hbC⟩ :
      Subgroup.zpowers (a * a') ≤ conjSub g K ⊓ Subgroup.centralizer ({z} : Set G))
  have hbV₀' : a * a' ∈ V₀ := hbV₀ (Subgroup.mem_zpowers _)
  have hbN : a * a' ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer (hRK ha)) (d.late_K'_le (hR'K' ha'))
  have hbtr : a * a' ∉ trivialOnQuot K := not_trivialOnQuot_of_invol d hbKK hb2 hb1 hbz
  have hbin : InnerOn K (a * a') := innerOn_of_mem_kerG eK
    ((kerG K).mul_mem (K_le_kerG d (hRK ha)) (K'_le_kerG d (hR'K' ha')))
  rcases Sec6Gen.l6_2Gen G (CoreAssembly.conjClass K) d.late_hΩ K d.late_mem_K z hzK
      (conjSub g K) hBΩ hBtw (a * a') hBb V₀ hV₀ hbV₀' with
    ⟨-, hne⟩ | ⟨hV₀e, -, R₀, hR₀, hR₀K, hV₀R₀, hsd⟩ | ⟨hV₀U, -, -⟩ | ⟨-, hcm⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp hbN) hne
  · exfalso
    obtain ⟨eR₀⟩ := nonempty_equiv_q8' (Sec6Gen.isQuatSub_of_mem_RSet d.late_hΩ hR₀)
      (d.card_RSet _ hR₀)
    have hR₀s : IsSylow2In R₀ K :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le d.late_hΩ d.late_mem_K hR₀ hR₀K
    have hbR₀ : a * a' ∈ Subgroup.normalizer (R₀ : Set G) := hV₀R₀ hbV₀'
    rw [hV₀e] at hsd
    have hout : TL4.LinkDisc.B2b.Outer R₀ (a * a') :=
      TL4.LinkDisc.B2b.outer_of_isSemidihedral (r := 3) le_rfl eR₀ hb2 hbR₀ hsd
    exact not_innerOn_of_outer (isPGroup_kbar_of_equiv eK) hR₀s eR₀ hbR₀ hout hbin
  ·
    obtain ⟨-, -, -, hcyc, -⟩ := id hV₀U
    have hcR := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hV₀U d.late_mem_K d.hR
    have hV₀4 : Nat.card V₀ = 4 := by rw [d.card8] at hcR; omega
    obtain ⟨w', hw'⟩ := hcyc.exists_generator
    have hord : orderOf (w' : G) = 4 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hw', hV₀4]
    have hw1 : (w' : G) * (w' : G) ≠ 1 := by
      rw [← pow_two]
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
    have hw4 : ((w' : G) * (w' : G)) * ((w' : G) * (w' : G)) = 1 := by
      have : (w' : G) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
      calc ((w' : G) * (w' : G)) * ((w' : G) * (w' : G)) = (w' : G) ^ 4 := by
            simp [pow_succ, mul_assoc]
        _ = 1 := this
    have hwB : (w' : G) ∈ conjSub g K := (hV₀.1 w'.2).1
    have hww : (w' : G) * (w' : G) = a * a' :=
      (hBb.unique _ ((conjSub g K).mul_mem hwB hwB) hw4).resolve_left hw1
    have hV₀C : V₀ ≤ Subgroup.centralizer ({z} : Set G) := fun _ hx => (hV₀.1 hx).2
    have hV₀X : V₀ ≤ sec20X (CoreAssembly.conjClass K) z K K' := by
      unfold sec20X
      exact le_trans (le_iSup₂_of_le (f := fun U (_ : U ∈ {U : Subgroup G | U ∈ USet
        (CoreAssembly.conjClass K) ∧ U ≤ Subgroup.centralizer ({z} : Set G)}) => U) V₀
        ⟨hV₀U, hV₀C⟩ le_rfl) (le_sup_left.trans le_sup_left)
    exact d.inZ_of_sq_eq c3 ha ha' ha2 ha'2 (hV₀X w'.2) hww
  · exfalso
    refine hbtr ⟨hbN, fun y hy => ?_⟩
    have := hcm (Subgroup.commutator_mem_commutator hbV₀' hy)
    rw [oddCoreIn_eq_oddCoreOf]
    exact this

end Core8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
