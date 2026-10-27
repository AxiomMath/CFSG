module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35LMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem asc_eq_one_of_sq {A : Subgroup S.O} (hAM : A ≤ S.Mbar)
    (hAn : ∀ m ∈ S.Mbar, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {a : S.O} (ha : a ∈ A) (ha2 : a * a = 1) : a = 1 := by
  let T : Subgroup S.O :=
    { carrier := {x | x ∈ A ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1, by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hAc y hy.1 x hx.1]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨A.one_mem, one_mul 1⟩
      inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [← mul_inv_rev, hx.2, inv_one]⟩ }
  have hT2 : IsPGroup 2 T := fun x => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_one, sq]
    exact x.2.2)⟩
  have hTM : T ≤ S.Mbar := fun x hx => hAM hx.1
  have hTn : S.Mbar ≤ normalizer (T : Set S.O) := by
    intro m hm
    rw [mem_normalizer_iff]
    have key : ∀ m ∈ S.Mbar, ∀ x ∈ T, m * x * m⁻¹ ∈ T := fun m hm x hx =>
      ⟨hAn m hm x hx.1, by
        calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
          _ = 1 := by rw [hx.2, mul_one, mul_inv_cancel]⟩
    intro x
    refine ⟨key m hm x, fun h => ?_⟩
    have := key m⁻¹ (S.Mbar.inv_mem hm) _ h
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at this
  have hbot := S.eq_bot_of_normalized_L hTM hTn hT2
  have : a ∈ T := ⟨ha, ha2⟩
  rwa [hbot, mem_bot] at this

theorem asc_odd_orderOf {A : Subgroup S.O} (hAM : A ≤ S.Mbar)
    (hAn : ∀ m ∈ S.Mbar, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {a : S.O} (ha : a ∈ A) : ¬ 2 ∣ orderOf a := by
  rintro ⟨k, hk⟩
  have hpos : 0 < orderOf a := orderOf_pos a
  have hk0 : 0 < k := by omega
  have h1 : a ^ k * a ^ k = 1 := by rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
  have h2 := asc_eq_one_of_sq hAM hAn hAc (A.pow_mem ha k) h1
  have h3 := orderOf_le_of_pow_eq_one hk0 h2
  omega

theorem asc_Lbar_le_Mbar : S.LbarAsc ≤ S.Mbar := by
  rw [LbarAsc, closure_le]
  rintro _ ⟨t, -, htM, rfl⟩
  exact ⟨⟨t, htM⟩, rfl⟩

theorem asc_mul_self_of_mem {d : S.O} (hd : d ∈ S.DbarAsc) : d * d = 1 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

theorem asc_conj_mem_centralizer {m : S.O} (hm : m ∈ S.Mbar) {c : S.O}
    (hc : ∀ d ∈ S.DbarAsc, c * d = d * c) :
    ∀ d ∈ S.DbarAsc, m * c * m⁻¹ * d = d * (m * c * m⁻¹) := by
  intro d hd
  have h1 := hc _ (S.conj_mem_DbarAsc_L (S.Mbar.inv_mem hm) hd)
  rw [inv_inv] at h1
  calc m * c * m⁻¹ * d = m * (c * (m⁻¹ * d * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * d * m) * c) * m⁻¹ := by rw [h1]
    _ = d * (m * c * m⁻¹) := by group

theorem asc_commute_of_centralizes {c : S.O} (hc : ∀ d ∈ S.DbarAsc, c * d = d * c) {x : S.O}
    (hx : x ∈ S.LbarAsc) : c * x = x * c := by
  have hcen : c ∈ centralizer (S.LbarAsc : Set S.O) := by
    rw [LbarAsc, centralizer_closure, mem_centralizer_iff]
    exact fun d hd => (hc d hd).symm
  exact ((mem_centralizer_iff.mp hcen) x hx).symm

variable (hst : S.Asc512Standing)
include hst

theorem asc_center_eq_one {x : S.LbarAsc} (hx : x ∈ center S.LbarAsc) (hx2 : x * x = 1) :
    x = 1 := by
  let A : Subgroup S.O := (center S.LbarAsc).map S.LbarAsc.subtype
  have hAM : A ≤ S.Mbar := (map_subtype_le _).trans asc_Lbar_le_Mbar
  have hAn : ∀ m ∈ S.Mbar, ∀ a ∈ A, m * a * m⁻¹ ∈ A := by
    rintro m hm _ ⟨y, hy, rfl⟩
    have hmy : m * (y : S.O) * m⁻¹ ∈ S.LbarAsc := hst.normal m hm y y.2
    refine ⟨⟨_, hmy⟩, mem_center_iff.mpr fun w => Subtype.ext ?_, rfl⟩
    have hw : m⁻¹ * (w : S.O) * m ∈ S.LbarAsc := by
      simpa using hst.normal m⁻¹ (S.Mbar.inv_mem hm) w w.2
    have h1 := congrArg Subtype.val (mem_center_iff.mp hy ⟨_, hw⟩)
    simp only [Subgroup.coe_mul] at h1 ⊢
    calc (w : S.O) * (m * y * m⁻¹) = m * ((m⁻¹ * w * m) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * w * m)) * m⁻¹ := by rw [h1]
      _ = m * y * m⁻¹ * w := by group
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, -, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp ha b).symm
  have h := asc_eq_one_of_sq hAM hAn hAc ⟨x, hx, rfl⟩ (congrArg Subtype.val hx2)
  exact Subtype.ext h

theorem asc_center_odd {x : S.LbarAsc} (hx : x ∈ center S.LbarAsc) : ¬ 2 ∣ orderOf x := by
  rintro ⟨k, hk⟩
  have hpos : 0 < orderOf x := orderOf_pos x
  have hk0 : 0 < k := by omega
  have h1 : x ^ k * x ^ k = 1 := by rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
  have h2 := asc_center_eq_one hst ((center S.LbarAsc).pow_mem hx k) h1
  have h3 := orderOf_le_of_pow_eq_one hk0 h2
  omega

theorem asc_mk_injOn {d e : S.LbarAsc} (hd : (d : S.O) ∈ S.DbarAsc) (he : (e : S.O) ∈ S.DbarAsc)
    (h : (QuotientGroup.mk d : S.LbarAsc ⧸ center S.LbarAsc) = QuotientGroup.mk e) : d = e := by
  have hu : d⁻¹ * e ∈ center S.LbarAsc := QuotientGroup.eq.mp h
  have hd2 : d * d = 1 := Subtype.ext (asc_mul_self_of_mem hd)
  have he2 : e * e = 1 := Subtype.ext (asc_mul_self_of_mem he)
  have hde : d * e = e * d := by
    have h1 := mem_center_iff.1 hu d
    calc d * e = d * (d * (d⁻¹ * e)) * d⁻¹ * d := by group
      _ = d * ((d⁻¹ * e) * d) * d⁻¹ * d := by rw [h1]
      _ = e * d := by group
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hu2 : (d⁻¹ * e) * (d⁻¹ * e) = 1 := by
    rw [hdinv]
    calc d * e * (d * e) = d * (e * d) * e := by group
      _ = d * (d * e) * e := by rw [hde]
      _ = (d * d) * (e * e) := by group
      _ = 1 := by rw [hd2, he2, one_mul]
  have := asc_center_eq_one hst hu hu2
  calc d = d * (d⁻¹ * e) := by rw [this, mul_one]
    _ = e := by group

theorem asc_commute_of_mk_commute {d c : S.LbarAsc} (hd : (d : S.O) ∈ S.DbarAsc)
    (h : (QuotientGroup.mk c : S.LbarAsc ⧸ center S.LbarAsc) * QuotientGroup.mk d =
      QuotientGroup.mk d * QuotientGroup.mk c) : c * d = d * c := by
  have hcd : ((c * d * c⁻¹ : S.LbarAsc) : S.O) ∈ S.DbarAsc := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact S.conj_mem_DbarAsc_L (asc_Lbar_le_Mbar c.2) hd
  have h1 : (QuotientGroup.mk (c * d * c⁻¹) : S.LbarAsc ⧸ center S.LbarAsc) =
      QuotientGroup.mk d := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel_right]
  have h2 := asc_mk_injOn hst hcd hd h1
  calc c * d = c * d * c⁻¹ * c := by group
    _ = d * c := by rw [h2]

noncomputable def ascConjL (m : S.Mbar) : S.LbarAsc ≃* S.LbarAsc :=
  AS35L.conjRestrict S.LbarAsc m (fun x hx => hst.normal m m.2 x hx)
    (fun x hx => by simpa using hst.normal _ (S.Mbar.inv_mem m.2) x hx)

theorem ascConjL_apply (m : S.Mbar) (x : S.LbarAsc) :
    ((ascConjL hst m x : S.LbarAsc) : S.O) = m * x * m⁻¹ :=
  AS35L.conjRestrict_apply _ _ _ _ x

noncomputable def ascAct (m : S.Mbar) : MulAut (S.LbarAsc ⧸ center S.LbarAsc) :=
  QuotientGroup.congr (center S.LbarAsc) (center S.LbarAsc) (ascConjL hst m)
    (map_center_eq (ascConjL hst m))

theorem ascAct_mk (m : S.Mbar) (x : S.LbarAsc) :
    ascAct hst m (QuotientGroup.mk x) = QuotientGroup.mk (ascConjL hst m x) := by
  unfold ascAct
  exact QuotientGroup.congr_mk _ _ _ _ x

theorem ascAct_mul_apply (m m' : S.Mbar) (x : S.LbarAsc) :
    ascAct hst (m * m') (QuotientGroup.mk x) =
      ascAct hst m (ascAct hst m' (QuotientGroup.mk x)) := by
  simp only [ascAct_mk]
  congr 1

theorem ascAct_mul (m m' : S.Mbar) : ascAct hst (m * m') = ascAct hst m * ascAct hst m' := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x => exact ascAct_mul_apply hst m m' x

theorem ascAct_one_apply (x : S.LbarAsc) :
    ascAct hst 1 (QuotientGroup.mk x) = QuotientGroup.mk x := by
  simp only [ascAct_mk]
  congr 1

@[expose] noncomputable def ascActHom : S.Mbar →* MulAut (S.LbarAsc ⧸ center S.LbarAsc) where
  toFun := ascAct hst
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => exact ascAct_one_apply hst x
  map_mul' := ascAct_mul hst

omit hst in
theorem asc_Pbar_le_Mbar (g : G) : S.PbarAsc g ≤ S.Mbar := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

omit hst in
theorem asc_rho_ne_one (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) (htM : t ∈ S.M) :
    S.ρ ⟨t, htM⟩ ≠ 1 := by
  intro h
  have htQ : t ∈ S.QG := ⟨⟨t, htM⟩, S.mem_Q_of_ρ_eq_one h, rfl⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  have hcz := hS.weak c (by rw [hc]; exact htQ)
  exact S.ne_z_of_mem_ESet ht.1 (by rw [← hc, hcz])

theorem asc_not_centralizes (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) (htM : t ∈ S.M) :
    ¬ ∀ d ∈ S.DbarAsc, S.ρ ⟨t, htM⟩ * d = d * S.ρ ⟨t, htM⟩ := by
  intro h
  have htD := S.ρ_mem_DbarAsc ht htM
  set tL : S.LbarAsc := ⟨S.ρ ⟨t, htM⟩, subset_closure htD⟩
  have hZ : tL ∈ center S.LbarAsc := mem_center_iff.mpr fun y =>
    Subtype.ext (asc_commute_of_centralizes h y.2).symm
  have h1 := asc_center_eq_one hst hZ (Subtype.ext (asc_mul_self_of_mem htD))
  exact asc_rho_ne_one hS ht htM (congrArg Subtype.val h1)

theorem asc_eq_one_of_mem_Pbar_of_centralizes (hP : S14.Asc512PbarStmt) (hS : S.SixHyp)
    {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {y : S.O}
    (hy : y ∈ S.PbarAsc g) (hyD : ∀ d ∈ S.DbarAsc, y * d = d * y) : y = 1 := by
  obtain ⟨-, hext, -, hZ, -, -, -⟩ := hP G S hS g htD htM
  have hnot := asc_not_centralizes hst hS htD htM
  by_contra hy1
  have hyt : y ≠ S.ρ ⟨_, htM⟩ := fun h => hnot (h ▸ hyD)
  have hnc : ¬ ∀ x ∈ S.PbarAsc g, y * x = x * y := fun h => (hZ y hy h).elim hy1 hyt
  push Not at hnc
  obtain ⟨p, hp, hpy⟩ := hnc
  have hpM := asc_Pbar_le_Mbar g hp
  have hcP : p * y * p⁻¹ * y⁻¹ ∈ S.PbarAsc g :=
    mul_mem (mul_mem (mul_mem hp hy) (inv_mem hp)) (inv_mem hy)
  have hcD : ∀ d ∈ S.DbarAsc, p * y * p⁻¹ * y⁻¹ * d = d * (p * y * p⁻¹ * y⁻¹) := by
    intro d hd
    have h1 := asc_conj_mem_centralizer hpM hyD d hd
    have h2 : y⁻¹ * d = d * y⁻¹ := by
      calc y⁻¹ * d = y⁻¹ * (d * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * d) * y⁻¹ := by rw [hyD d hd]
        _ = d * y⁻¹ := by group
    calc p * y * p⁻¹ * y⁻¹ * d = p * y * p⁻¹ * (y⁻¹ * d) := by group
      _ = p * y * p⁻¹ * (d * y⁻¹) := by rw [h2]
      _ = (p * y * p⁻¹ * d) * y⁻¹ := by group
      _ = d * (p * y * p⁻¹) * y⁻¹ := by rw [h1]
      _ = d * (p * y * p⁻¹ * y⁻¹) := by group
  have hc1 : p * y * p⁻¹ * y⁻¹ ≠ 1 := by
    intro h
    apply hpy
    calc y * p = (p * y * p⁻¹ * y⁻¹)⁻¹ * (p * y) := by group
      _ = p * y := by rw [h, inv_one, one_mul]
  have hcZ : ∀ x ∈ S.PbarAsc g, p * y * p⁻¹ * y⁻¹ * x = x * (p * y * p⁻¹ * y⁻¹) := by
    have hmem : (⟨p * y * p⁻¹ * y⁻¹, hcP⟩ : S.PbarAsc g) ∈ center (S.PbarAsc g) := by
      rw [← hext.2.1, _root_.commutator_def]
      have h := Subgroup.commutator_mem_commutator (mem_top (⟨p, hp⟩ : S.PbarAsc g))
        (mem_top (⟨y, hy⟩ : S.PbarAsc g))
      have e : (⟨p * y * p⁻¹ * y⁻¹, hcP⟩ : S.PbarAsc g) = ⁅(⟨p, hp⟩ : S.PbarAsc g), ⟨y, hy⟩⁆ :=
        Subtype.ext (by rw [commutatorElement_def]; simp)
      rw [e]
      exact h
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hmem ⟨x, hx⟩).symm
  rcases hZ _ hcP hcZ with h | h
  · exact hc1 h
  · exact hnot (h ▸ hcD)

theorem asc_Pbar_commute (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {p : S.O} (hp : p ∈ S.PbarAsc g)
    {c : S.O} (hcM : c ∈ S.Mbar) (hcD : ∀ d ∈ S.DbarAsc, c * d = d * c) : p * c = c * p := by
  obtain ⟨-, -, -, -, hn, -, -⟩ := hP G S hS g htD htM
  have hct : c * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * c := hcD _ (S.ρ_mem_DbarAsc htD htM)
  have hpM := asc_Pbar_le_Mbar g hp
  have hk : p * c * p⁻¹ * c⁻¹ ∈ S.PbarAsc g := by
    have h1 := hn c hcM hct p⁻¹ (inv_mem hp)
    have h2 := mul_mem hp h1
    rwa [show p * (c * p⁻¹ * c⁻¹) = p * c * p⁻¹ * c⁻¹ by group] at h2
  have hkD : ∀ d ∈ S.DbarAsc, p * c * p⁻¹ * c⁻¹ * d = d * (p * c * p⁻¹ * c⁻¹) := by
    intro d hd
    have h1 := asc_conj_mem_centralizer hpM hcD d hd
    have h2 : c⁻¹ * d = d * c⁻¹ := by
      calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hcD d hd]
        _ = d * c⁻¹ := by group
    calc p * c * p⁻¹ * c⁻¹ * d = p * c * p⁻¹ * (c⁻¹ * d) := by group
      _ = p * c * p⁻¹ * (d * c⁻¹) := by rw [h2]
      _ = (p * c * p⁻¹ * d) * c⁻¹ := by group
      _ = d * (p * c * p⁻¹) * c⁻¹ := by rw [h1]
      _ = d * (p * c * p⁻¹ * c⁻¹) := by group
  have h1 := asc_eq_one_of_mem_Pbar_of_centralizes hst hP hS htD htM hk hkD
  calc p * c = (p * c * p⁻¹ * c⁻¹) * (c * p) := by group
    _ = c * p := by rw [h1, one_mul]

theorem asc_conj_eq_of_ascAct {m : S.Mbar} {x : S.LbarAsc}
    (hx : ascAct hst m = MulAut.conj (QuotientGroup.mk x)) {d : S.O} (hd : d ∈ S.DbarAsc) :
    (m : S.O) * d * (m : S.O)⁻¹ = x * d * (x : S.O)⁻¹ := by
  have hdL : d ∈ S.LbarAsc := subset_closure hd
  have h1 : ascAct hst m (QuotientGroup.mk ⟨d, hdL⟩) =
      MulAut.conj (QuotientGroup.mk x : S.LbarAsc ⧸ center S.LbarAsc) (QuotientGroup.mk ⟨d, hdL⟩) :=
    DFunLike.congr_fun hx _
  rw [MulAut.conj_apply] at h1
  have h1' := (ascAct_mk hst m ⟨d, hdL⟩).symm.trans h1
  have h2 : (QuotientGroup.mk (ascConjL hst m ⟨d, hdL⟩) : S.LbarAsc ⧸ center S.LbarAsc) =
      QuotientGroup.mk (x * ⟨d, hdL⟩ * x⁻¹) := h1'
  have hxM : (x : S.O) ∈ S.Mbar := asc_Lbar_le_Mbar x.2
  have h3 := asc_mk_injOn hst (by rw [ascConjL_apply]; exact S.conj_mem_DbarAsc_L m.2 hd)
    (by simpa using S.conj_mem_DbarAsc_L hxM hd) h2
  have h4 := congrArg Subtype.val h3
  rw [ascConjL_apply] at h4
  simpa using h4

theorem asc_mem_Lbar_of_inner (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {p : S.Mbar}
    (hp : (p : S.O) ∈ S.PbarAsc g) {x : S.LbarAsc}
    (hx : ascAct hst p = MulAut.conj (QuotientGroup.mk x)) : (p : S.O) ∈ S.LbarAsc := by
  obtain ⟨-, hext, -, -, -, -, -⟩ := hP G S hS g htD htM
  have hxM : (x : S.O) ∈ S.Mbar := asc_Lbar_le_Mbar x.2
  have hpx : ∀ d ∈ S.DbarAsc, (p : S.O) * d * (p : S.O)⁻¹ = x * d * (x : S.O)⁻¹ :=
    fun d hd => asc_conj_eq_of_ascAct hst hx hd
  obtain ⟨c, hc⟩ : ∃ c : S.O, c = (x : S.O)⁻¹ * p := ⟨_, rfl⟩
  have hcM : c ∈ S.Mbar := by rw [hc]; exact mul_mem (inv_mem hxM) p.2
  have hcD : ∀ d ∈ S.DbarAsc, c * d = d * c := by
    intro d hd
    calc c * d = (x : S.O)⁻¹ * ((p : S.O) * d * (p : S.O)⁻¹) * p := by rw [hc]; group
      _ = (x : S.O)⁻¹ * (x * d * (x : S.O)⁻¹) * p := by rw [hpx d hd]
      _ = d * c := by rw [hc]; group
  have hcK : ∀ k ∈ S.Mbar, (∀ d ∈ S.DbarAsc, k * d = d * k) → c * k = k * c := by
    intro k hkM hkD
    have h1 := asc_Pbar_commute hst hP hS htD htM hp hkM hkD
    have h2 : k * x = x * k := asc_commute_of_centralizes hkD x.2
    have h3 : (x : S.O)⁻¹ * k = k * (x : S.O)⁻¹ := by
      calc (x : S.O)⁻¹ * k = (x : S.O)⁻¹ * (k * x) * (x : S.O)⁻¹ := by group
        _ = (x : S.O)⁻¹ * (x * k) * (x : S.O)⁻¹ := by rw [h2]
        _ = k * (x : S.O)⁻¹ := by group
    calc c * k = (x : S.O)⁻¹ * (p * k) := by rw [hc]; group
      _ = (x : S.O)⁻¹ * (k * p) := by rw [h1]
      _ = ((x : S.O)⁻¹ * k) * p := by group
      _ = (k * (x : S.O)⁻¹) * p := by rw [h3]
      _ = k * c := by rw [hc]; group
  let A : Subgroup S.O :=
    { carrier := {a | a ∈ S.Mbar ∧ (∀ d ∈ S.DbarAsc, a * d = d * a) ∧
        ∀ k ∈ S.Mbar, (∀ d ∈ S.DbarAsc, k * d = d * k) → a * k = k * a}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun d hd => by
          rw [mul_assoc, hb.2.1 d hd, ← mul_assoc, ha.2.1 d hd, mul_assoc],
        fun k hk hkD => by rw [mul_assoc, hb.2.2 k hk hkD, ← mul_assoc, ha.2.2 k hk hkD,
          mul_assoc]⟩
      one_mem' := ⟨one_mem _, fun d _ => by rw [one_mul, mul_one],
        fun k _ _ => by rw [one_mul, mul_one]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun d hd => by
          calc a⁻¹ * d = a⁻¹ * (d * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * d) * a⁻¹ := by rw [ha.2.1 d hd]
            _ = d * a⁻¹ := by group,
        fun k hk hkD => by
          calc a⁻¹ * k = a⁻¹ * (k * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * k) * a⁻¹ := by rw [ha.2.2 k hk hkD]
            _ = k * a⁻¹ := by group⟩ }
  have hAM : A ≤ S.Mbar := fun a ha => ha.1
  have hAn : ∀ m ∈ S.Mbar, ∀ a ∈ A, m * a * m⁻¹ ∈ A := by
    intro m hm a ha
    refine ⟨mul_mem (mul_mem hm ha.1) (inv_mem hm), asc_conj_mem_centralizer hm ha.2.1,
      fun k hk hkD => ?_⟩
    have hk' : m⁻¹ * k * m ∈ S.Mbar := mul_mem (mul_mem (inv_mem hm) hk) hm
    have hkD' : ∀ d ∈ S.DbarAsc, m⁻¹ * k * m * d = d * (m⁻¹ * k * m) := by
      have := asc_conj_mem_centralizer (inv_mem hm) hkD
      simpa using this
    have h1 := ha.2.2 _ hk' hkD'
    calc m * a * m⁻¹ * k = m * (a * (m⁻¹ * k * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * k * m) * a) * m⁻¹ := by rw [h1]
      _ = k * (m * a * m⁻¹) := by group
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => ha.2.2 b hb.1 hb.2.1
  have hcA : c ∈ A := ⟨hcM, hcD, hcK⟩
  have hodd := asc_odd_orderOf hAM hAn hAc hcA
  obtain ⟨k, hk⟩ := hext.1 ⟨p, hp⟩
  have hpk : (p : S.O) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxc : (x : S.O) * c = c * x := (asc_commute_of_centralizes hcD x.2).symm
  have hpxc : (p : S.O) = x * c := by rw [hc]; group
  have hck : c ^ 2 ^ k ∈ S.LbarAsc := by
    have h1 : (x : S.O) ^ 2 ^ k * c ^ 2 ^ k = 1 := by
      have hcm : Commute (x : S.O) c := hxc
      rw [← hcm.mul_pow, ← hpxc, hpk]
    have h2 : c ^ 2 ^ k = ((x : S.O) ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_mem (pow_mem x.2 _)
  have hcop : (2 ^ k).Coprime (orderOf c) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  have hcL : c ∈ S.LbarAsc := by
    rw [← hn]
    exact pow_mem hck n
  rw [hpxc]
  exact mul_mem x.2 hcL

omit hst in
theorem asc_mem_Lbar_of_mem_DSet {t : G} (ht : t ∈ S.DSet) (htM : t ∈ S.M) :
    S.ρ ⟨t, htM⟩ ∈ S.LbarAsc :=
  subset_closure ⟨t, ht, htM, rfl⟩

omit hst in
noncomputable abbrev ascTL {t : G} (ht : t ∈ S.DSet) (htM : t ∈ S.M) : S.LbarAsc :=
  ⟨S.ρ ⟨t, htM⟩, asc_mem_Lbar_of_mem_DSet ht htM⟩

omit hst in
theorem asc_commute_tbar (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {y : S.O}
    (hy : y ∈ S.PbarAsc g) : y * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * y := by
  obtain ⟨htP, hext, -, hZ, -, -, -⟩ := hP G S hS g htD htM
  have h2 : Nat.card (center (S.PbarAsc g)) = 2 := hext.2.2.2
  obtain ⟨⟨w, hw⟩, hw1⟩ : ∃ w : center (S.PbarAsc g), w ≠ 1 := by
    have : Nontrivial (center (S.PbarAsc g)) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  have hwc : ∀ x ∈ S.PbarAsc g, (w : S.O) * x = x * w := fun x hx =>
    congrArg Subtype.val (mem_center_iff.mp hw ⟨x, hx⟩).symm
  rcases hZ w w.2 hwc with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hw1
  · rw [← h]
    exact (hwc y hy).symm

noncomputable abbrev ascPhat (g : G) : Subgroup (S.LbarAsc ⧸ center S.LbarAsc) :=
  ((S.PbarAsc g).subgroupOf S.LbarAsc).map (QuotientGroup.mk' (center S.LbarAsc))

omit hst in
theorem ascPhat_isPGroup (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) : IsPGroup 2 (S.ascPhat g) :=
  (((hP G S hS g htD htM).2.1.1).comap_of_injective S.LbarAsc.subtype
    S.LbarAsc.subtype_injective).map _

omit [Finite G] hst in
theorem asc_eq_one_of_two_pow_of_odd {H : Type*} [Group H] {K : Subgroup H} {x : K}
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) (hodd : ¬ 2 ∣ orderOf (x : H)) : (x : H) = 1 := by
  rcases h2 with ⟨k, hk⟩
  have hk' : (x : H) ^ 2 ^ k = 1 := by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
  have hdvd : orderOf (x : H) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨j, -, hj⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  · exact absurd (hj ▸ dvd_pow_self 2 hpos.ne') hodd

theorem card_ascPhat (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    Nat.card (S.ascPhat g) = Nat.card ((S.PbarAsc g).subgroupOf S.LbarAsc) := by
  have h2 : IsPGroup 2 ((S.PbarAsc g).subgroupOf S.LbarAsc) :=
    ((hP G S hS g htD htM).2.1.1).comap_of_injective S.LbarAsc.subtype
      S.LbarAsc.subtype_injective
  have hinj : Function.Injective ((QuotientGroup.mk' (center S.LbarAsc)).comp
      ((S.PbarAsc g).subgroupOf S.LbarAsc).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : S.LbarAsc) ∈ center S.LbarAsc := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact hx
    have hodd := asc_center_odd hst hx'
    have hx1 : (x : S.LbarAsc) = 1 := asc_eq_one_of_two_pow_of_odd (h2 x) hodd
    rw [mem_bot]
    exact Subtype.ext hx1
  have hrange : S.ascPhat g = ((QuotientGroup.mk' (center S.LbarAsc)).comp
      ((S.PbarAsc g).subgroupOf S.LbarAsc).subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit hst in
theorem mem_ascPhat (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    (QuotientGroup.mk (ascTL htD htM) : S.LbarAsc ⧸ center S.LbarAsc) ∈ S.ascPhat g :=
  ⟨ascTL htD htM, (hP G S hS g htD htM).1, rfl⟩

omit hst in
theorem ascPhat_commute (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {y : S.LbarAsc ⧸ center S.LbarAsc}
    (hy : y ∈ S.ascPhat g) :
    y * QuotientGroup.mk (ascTL htD htM) = QuotientGroup.mk (ascTL htD htM) * y := by
  rw [Subgroup.mem_map] at hy
  rcases hy with ⟨x, hx, hxy⟩
  have hxt : x * ascTL htD htM = ascTL htD htM * x :=
    Subtype.ext (asc_commute_tbar hP hS htD htM (Subgroup.mem_subgroupOf.mp hx))
  rw [← hxy, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxt]

theorem ascPhat_normalized (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (c : S.LbarAsc)
    (hc : (QuotientGroup.mk c : S.LbarAsc ⧸ center S.LbarAsc) * QuotientGroup.mk (ascTL htD htM) =
      QuotientGroup.mk (ascTL htD htM) * QuotientGroup.mk c)
    {y : S.LbarAsc ⧸ center S.LbarAsc} (hy : y ∈ S.ascPhat g) :
    QuotientGroup.mk c * y * (QuotientGroup.mk c)⁻¹ ∈ S.ascPhat g := by
  have hn := (hP G S hS g htD htM).2.2.2.2.1
  have htLD : ((ascTL htD htM : S.LbarAsc) : S.O) ∈ S.DbarAsc := S.ρ_mem_DbarAsc htD htM
  have hct : c * ascTL htD htM = ascTL htD htM * c := asc_commute_of_mk_commute hst htLD hc
  rw [Subgroup.mem_map] at hy
  rcases hy with ⟨x, hx, hxy⟩
  refine Subgroup.mem_map.mpr ⟨c * x * c⁻¹, ?_, ?_⟩
  · have hcM : (c : S.O) ∈ S.Mbar := asc_Lbar_le_Mbar c.2
    have := hn c hcM (congrArg Subtype.val hct) x (Subgroup.mem_subgroupOf.mp hx)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  · rw [← hxy]
    simp only [map_mul, map_inv, QuotientGroup.mk'_apply]
end Setting

end CFSG.LargeExtraspecial
