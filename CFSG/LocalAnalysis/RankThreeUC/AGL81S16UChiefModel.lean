module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankA
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix CFSG.Open CFSG.ABGLocalTools
open CFSG.LieType.Universal.Unitary (SUid)

section ChiefModel

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem exists_fix_of_invariant_pgroup {E : Subgroup (SUid σ 4)} (hP : IsPGroup 2 ↥E)
    (hFev : Even (Nat.card F)) (T : Submodule F (Fin 4 → F))
    (hT : ∀ a ∈ E, ∀ y ∈ T, a • y ∈ T) (hT0 : T ≠ ⊥) :
    ∃ y ∈ T, y ≠ 0 ∧ ∀ a ∈ E, a • y = y := by
  letI : MulAction ↥E ↥T :=
    { smul := fun a y => ⟨(a : SUid σ 4) • (y : Fin 4 → F), hT a a.2 y y.2⟩
      one_smul := fun y => Subtype.ext (one_smul _ _)
      mul_smul := fun a b y => Subtype.ext (mul_smul (a : SUid σ 4) (b : SUid σ 4) _) }
  have hev : Even (Nat.card ↥T) := by
    haveI : Nontrivial ↥T := Submodule.nontrivial_iff_ne_bot.mpr hT0
    have hpos : 0 < Module.finrank F ↥T := Module.finrank_pos
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥T)]
    exact Nat.even_pow.mpr ⟨hFev, by omega⟩
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_fixed hP hev (MulAction.toPermHom ↥E ↥T)
    (fun a => Subtype.ext (smul_zero (a : SUid σ 4)))
  refine ⟨y, y.2, fun h => hy0 (Subtype.ext h), fun a ha => ?_⟩
  exact congrArg Subtype.val (hy ⟨a, ha⟩)

theorem exists_isotropic_fixed (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hFev : Even (Nat.card F)) {E : Subgroup (SUid σ 4)} (hP : IsPGroup 2 ↥E) :
    ∃ w : Fin 4 → F, w ≠ 0 ∧ herm σ w w = 0 ∧ ∀ g ∈ E, g • w = w := by
  by_cases hE1 : ∀ g ∈ E, g = 1
  · obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
    refine ⟨![1, u, 0, 0], ?_, ?_, fun g hg => by rw [hE1 g hg, one_smul]⟩
    · intro h
      simpa using congrFun h 0
    · simp only [herm, Fin.sum_univ_four]
      simp
      linear_combination hu
  · push Not at hE1
    obtain ⟨g₀, hg₀E, hg₀⟩ := hE1
    haveI : Nontrivial ↥E := ⟨⟨⟨g₀, hg₀E⟩, 1, fun h => hg₀ (congrArg Subtype.val h)⟩⟩
    haveI : Nontrivial ↥(Subgroup.center ↥E) := hP.center_nontrivial
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPc : IsPGroup 2 ↥(Subgroup.center ↥E) := hP.to_subgroup _
    have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥E) :=
      hPc.card_eq_or_dvd.resolve_left (Finite.one_lt_card (α := ↥(Subgroup.center ↥E))).ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥E)) 2 hdvd
    have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz
      omega
    set zG : SUid σ 4 := ((z : ↥E) : SUid σ 4) with hzG
    have hzGsq : zG * zG = 1 := by
      have := congrArg (fun t : ↥(Subgroup.center ↥E) => ((t : ↥E) : SUid σ 4)) hz2
      simpa [pow_two] using this
    have hzG1 : zG ≠ 1 := by
      intro h
      exact hz1 (Subtype.ext (Subtype.ext h))
    have hzGE : zG ∈ E := (z : ↥E).2
    have hzc : ∀ g ∈ E, zG * g = g * zG := by
      intro g hg
      have := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
      exact (congrArg Subtype.val this).symm
    let Uz : Submodule F (Fin 4 → F) :=
      { carrier := {y | ∃ x, y = zG • x - x}
        add_mem' := by
          rintro _ _ ⟨x, rfl⟩ ⟨x', rfl⟩
          exact ⟨x + x', by rw [smul_add]; abel⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c _ ⟨x, rfl⟩
          exact ⟨c • x, by rw [smul_sub, smul_comm zG c x]⟩ }
    have hUne : Uz ≠ ⊥ := by
      intro h
      apply hzG1
      refine ext_smul σ fun x => ?_
      have : zG • x - x ∈ Uz := ⟨x, rfl⟩
      rw [h, Submodule.mem_bot, sub_eq_zero] at this
      rw [this, one_smul]
    have hUinv : ∀ a ∈ E, ∀ y ∈ Uz, a • y ∈ Uz := by
      rintro a ha _ ⟨x, rfl⟩
      refine ⟨a • x, ?_⟩
      rw [smul_sub, ← mul_smul, ← mul_smul, ← hzc a ha]
    have hUiso : ∀ y ∈ Uz, herm σ y y = 0 := by
      rintro _ ⟨x, rfl⟩
      have h1 := herm_nil hzGsq x (zG • x - x)
      rw [sub_eq_zero.mpr (smul_nil hzGsq h2 x), herm_zero_right] at h1
      exact h1
    obtain ⟨y, hyU, hy0, hyfix⟩ := exists_fix_of_invariant_pgroup hP hFev Uz hUinv hUne
    exact ⟨y, hy0, hUiso y hyU, hyfix⟩

def Q1 (w : Fin 4 → F) (hw : herm σ w w = 0) : Subgroup (SUid σ 4) where
  carrier := {g | g • w = w ∧ (∀ y, herm σ w y = 0 → g • y - y ∈ Submodule.span F {w}) ∧
    ∀ x, herm σ w (g • x - x) = 0}
  mul_mem' := fun {g g'} hg hg' => by
    refine ⟨by rw [mul_smul, hg'.1, hg.1], fun y hy => ?_, fun x => ?_⟩
    · have h1 := hg'.2.1 y hy
      have hy' : herm σ w (g' • y) = 0 := by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
        have : g' • y = y + c • w := by rw [hc]; abel
        rw [this, herm_add_right, herm_smul_right, hy, hw, mul_zero, add_zero]
      have h2 := hg.2.1 (g' • y) hy'
      rw [mul_smul]
      have : g • g' • y - y = (g • g' • y - g' • y) + (g' • y - y) := by abel
      rw [this]
      exact Submodule.add_mem _ h2 h1
    · rw [mul_smul]
      have : g • g' • x - x = (g • g' • x - g' • x) + (g' • x - x) := by abel
      rw [this, herm_add_right, hg.2.2 (g' • x), hg'.2.2 x, add_zero]
  one_mem' := ⟨one_smul _ _, fun y _ => by simp, fun x => by simp⟩
  inv_mem' := fun {g} hg => by
    have hgw : g⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hg.1.symm
    have hperp : ∀ y, herm σ w (g⁻¹ • y) = herm σ w y := fun y => by
      calc herm σ w (g⁻¹ • y) = herm σ (g • w) (g • g⁻¹ • y) :=
            (herm_smul_smul σ g w (g⁻¹ • y)).symm
        _ = herm σ w y := by rw [smul_inv_smul, hg.1]
    refine ⟨hgw, fun y hy => ?_, fun x => ?_⟩
    · have hy' : herm σ w (g⁻¹ • y) = 0 := by rw [hperp, hy]
      have h1 := hg.2.1 (g⁻¹ • y) hy'
      rw [smul_inv_smul] at h1
      have := Submodule.neg_mem _ h1
      simpa using this
    · rw [herm_sub_right, hperp, sub_self]

theorem herm_perp_of_fix {w : Fin 4 → F} {h : SUid σ 4} (hh : h • w = w) (y : Fin 4 → F) :
    herm σ w (h • y) = herm σ w y := by
  have hhi : h⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hh.symm
  calc herm σ w (h • y) = herm σ (h⁻¹ • w) y := (herm_inv_smul_left h w y).symm
    _ = herm σ w y := by rw [hhi]

theorem Q1_conj {w : Fin 4 → F} {hw : herm σ w w = 0} {h : SUid σ 4} (hh : h • w = w)
    {q : SUid σ 4} (hq : q ∈ Q1 w hw) : h * q * h⁻¹ ∈ Q1 w hw := by
  have hhi : h⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hh.symm
  refine ⟨by rw [mul_smul, mul_smul, hhi, hq.1, hh], fun y hy => ?_, fun x => ?_⟩
  · have hy' : herm σ w (h⁻¹ • y) = 0 := by
      rw [herm_perp_of_fix hhi, hy]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq.2.1 _ hy')
    have e : (h * q * h⁻¹) • y - y = h • (q • h⁻¹ • y - h⁻¹ • y) := by
      rw [smul_sub, smul_smul, smul_smul, smul_inv_smul h y, mul_smul]
    rw [e, ← hc, smul_comm, hh]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)
  · have e : (h * q * h⁻¹) • x - x = h • (q • h⁻¹ • x - h⁻¹ • x) := by
      rw [smul_sub, smul_smul, smul_smul, smul_inv_smul h x, mul_smul]
    rw [e, herm_perp_of_fix hh]
    exact hq.2.2 _

theorem Q1_pow_four (h2 : (2 : F) = 0) {w : Fin 4 → F} {hw : herm σ w w = 0} {q : SUid σ 4}
    (hq : q ∈ Q1 w hw) : q * q * q * q = 1 := by
  refine ext_smul σ fun x => ?_
  have h4 : ∀ y : Fin 4 → F, y + y = 0 := fun y => by rw [← two_smul F y, h2, zero_smul]
  set a := q • x - x with hadef
  have ha : herm σ w a = 0 := hq.2.2 x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq.2.1 a ha)
  have hqb : q • (c • w) = c • w := by rw [smul_comm, hq.1]
  have e1 : q • x = x + a := by rw [hadef]; abel
  have e2 : q • a = a + c • w := by rw [hc]; abel
  have e3 : q • q • x = x + c • w := by
    rw [e1, smul_add, e1, e2]
    calc x + a + (a + c • w) = x + (a + a) + c • w := by abel
      _ = x + c • w := by rw [h4 a, add_zero]
  have e4 : q • q • (x + c • w) = x := by
    rw [smul_add, smul_add, e3, hqb, hqb]
    calc x + c • w + c • w = x + (c • w + c • w) := by abel
      _ = x := by rw [h4, add_zero]
  calc (q * q * q * q) • x = q • q • (q • q • x) := by simp only [mul_smul]
    _ = x := by rw [e3, e4]
    _ = (1 : SUid σ 4) • x := (one_smul _ _).symm

theorem fix_Q1_subset (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) {w : Fin 4 → F}
    (hw0 : w ≠ 0) (hw : herm σ w w = 0) {y : Fin 4 → F} (hy : ∀ s ∈ Q1 w hw, s • y = y) :
    y ∈ Submodule.span F {w} := by
  have hc1 : (1 : F) + σ 1 = 0 := by rw [map_one, one_add_one_eq_two, h2]
  have hT : tv hσ.invol hw hc1 ∈ Q1 w hw := by
    refine ⟨by rw [tv_smul, hw, mul_zero, zero_smul, add_zero], fun y' hy' => ?_, fun x => ?_⟩
    · rw [tv_smul, hy', mul_zero, zero_smul, add_zero, sub_self]
      exact Submodule.zero_mem _
    · rw [tv_smul, add_sub_cancel_left, herm_smul_right, hw, mul_zero]
  have hwy : herm σ w y = 0 := by
    have h := hy _ hT
    rw [tv_smul] at h
    have h3 : (1 * herm σ w y) • w = 0 := add_eq_left.mp h
    rcases smul_eq_zero.mp h3 with h | h
    · rwa [one_mul] at h
    · exact absurd h hw0
  have hperp : ∀ z, herm σ w z = 0 → herm σ y z = 0 := by
    intro z hz
    have hzf : σ (-herm σ z z) = -herm σ z z := by rw [map_neg, herm_self_fixed σ hσ.invol z]
    obtain ⟨c, hc⟩ := hσ.trace_surj (-herm σ z z) hzf
    have hE : eichler hσ.invol hw hz hc ∈ Q1 w hw := by
      refine ⟨eichler_smul_self hσ.invol hw hz hc, fun y' hy' => ?_, fun x => ?_⟩
      · have e : eichler hσ.invol hw hz hc • y' - y' = -(herm σ z y' • w) := by
          rw [eichler_smul, hy', zero_smul, add_zero]
          abel
        rw [e]
        exact Submodule.neg_mem _
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
      · have e : eichler hσ.invol hw hz hc • x - x =
            herm σ w x • (z + c • w) - herm σ z x • w := by
          rw [eichler_smul]
          abel
        rw [e, herm_sub_right, herm_smul_right, herm_add_right, herm_smul_right, herm_smul_right,
          hz, hw]
        simp
    have h := hy _ hE
    rw [eichler_smul, hwy, zero_smul, add_zero] at h
    have h3 : herm σ z y • w = 0 := sub_eq_self.mp h
    have h4 : herm σ z y = 0 := by
      rcases smul_eq_zero.mp h3 with h5 | h5
      · exact h5
      · exact absurd h5 hw0
    rw [herm_conj σ hσ.invol z y, h4, map_zero]
  obtain ⟨x₀, hx₀⟩ := exists_herm_eq_one σ hw0
  obtain ⟨d, hd⟩ : ∃ d : F, σ d = herm σ y x₀ := ⟨σ.symm (herm σ y x₀), σ.apply_symm_apply _⟩
  have hyd : y = d • w := by
    rw [← sub_eq_zero]
    apply eq_zero_of_herm σ
    intro z
    have hz' : herm σ w (z - herm σ w z • x₀) = 0 := by
      rw [herm_sub_right, herm_smul_right, hx₀, mul_one, sub_self]
    have h1 := hperp _ hz'
    rw [herm_sub_right, herm_smul_right] at h1
    rw [herm_sub_left, herm_smul_left, hd]
    linear_combination h1
  rw [hyd]
  exact Submodule.smul_mem _ d (Submodule.mem_span_singleton_self w)

theorem le_of_isPGroup_of_le_normalizer' {G : Type*} [Group G] [Finite G] {T M N : Subgroup G}
    (hT : IsSylowOf 2 T M) (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hN : IsPGroup 2 ↥N) : N ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup := hT.isPGroup.to_sup_of_normal_right' hN (hT.le.trans hMN)
  have h := hT.eq_of_le le_sup_left (sup_le hT.le hNM) hsup
  exact (le_sup_right : N ≤ T ⊔ N).trans h.le

theorem chief_model (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) {n p : ℕ}
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (SUid σ 4)} (hE : IsSylowOf 2 E ⊤) :
    ∃ Q : Subgroup (SUid σ 4), Q ≤ E ∧ ∃ x : SUid σ 4,
      x ∈ Subgroup.normalizer (Q : Set (SUid σ 4)) ∧ x ≠ 1 ∧ x ^ p = 1 ∧
      ∀ y : Fin 4 → F, (∀ s ∈ Q, s • y = y) → x • y = y := by
  have hFev : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw0, hw, hwfix⟩ := exists_isotropic_fixed hσ h2 hFev hE.isPGroup
  have hst : ∀ g ∈ E, g ∈ MulAction.stabilizer (SUid σ 4) w := fun g hg =>
    MulAction.mem_stabilizer_iff.mpr (hwfix g hg)
  have hE' : IsSylowOf 2 E (MulAction.stabilizer (SUid σ 4) w) := hE.of_le hst le_top
  have hQst : Q1 w hw ≤ MulAction.stabilizer (SUid σ 4) w := fun q hq =>
    MulAction.mem_stabilizer_iff.mpr hq.1
  have hnorm : MulAction.stabilizer (SUid σ 4) w ≤
      Subgroup.normalizer (Q1 w hw : Set (SUid σ 4)) := by
    intro h hh
    have hh' := MulAction.mem_stabilizer_iff.mp hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact Q1_conj hh' hk
    · intro hk
      have hhi : h⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hh'.symm
      have := Q1_conj hhi hk
      simpa [mul_assoc] using this
  have hQ2 : IsPGroup 2 ↥(Q1 w hw) := fun q => ⟨2, Subtype.ext (by
    have h4 : (q : SUid σ 4) ^ (2 ^ 2) = q * q * q * q := by norm_num [pow_succ, mul_assoc]
    show (q : SUid σ 4) ^ (2 ^ 2) = 1
    rw [h4]
    exact Q1_pow_four h2 q.2)⟩
  have hQE : Q1 w hw ≤ E := le_of_isPGroup_of_le_normalizer' hE' hQst hnorm hQ2
  obtain ⟨Ep, hEpS, hEpa, hEpc, hEpfix⟩ := exists_stab_elemAbelian_ne_zero hp hpq hF hw0
  have hnt : Nontrivial ↥Ep := by
    have : 1 < Nat.card ↥Ep := by rw [hEpc, pow_one]; exact hp.one_lt
    exact Finite.one_lt_card_iff_nontrivial.mp this
  obtain ⟨g, hg1⟩ := exists_ne (1 : ↥Ep)
  let x : SUid σ 4 := ⟨(g : GL (Fin 4) F), hS.symm ▸ hEpS g.2⟩
  have hxw : x • w = w := hEpfix g g.2
  refine ⟨Q1 w hw, hQE, x, hnorm (MulAction.mem_stabilizer_iff.mpr hxw), ?_, ?_, ?_⟩
  · intro hx
    apply hg1
    exact Subtype.ext (congrArg (fun t : ↥(SUid σ 4) => (t : GL (Fin 4) F)) hx)
  · refine Subtype.ext ?_
    simpa using hEpa.2 (g : GL (Fin 4) F) g.2
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (fix_Q1_subset hσ h2 hw0 hw hy)
    rw [smul_comm, hxw]

end ChiefModel

end CFSG.LocalAnalysis.RankThreeUC
