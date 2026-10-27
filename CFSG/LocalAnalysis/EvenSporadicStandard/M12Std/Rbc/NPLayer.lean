module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.KDNP
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Step
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section OddQuot

variable {G : Type} [Group G]

abbrev OddQuot (D : Subgroup G) : Type := ↥D ⧸ CFSG.oddCore ↥D

abbrev oddProj (D : Subgroup G) : ↥D →* OddQuot D :=
  QuotientGroup.mk' (CFSG.oddCore ↥D)

abbrev oddBar (D A : Subgroup G) : Subgroup (OddQuot D) :=
  (A.subgroupOf D).map (oddProj D)

theorem oddProj_surjective (D : Subgroup G) : Function.Surjective (oddProj D) :=
  QuotientGroup.mk'_surjective _

theorem ker_oddProj (D : Subgroup G) : (oddProj D).ker = CFSG.oddCore ↥D :=
  QuotientGroup.ker_mk' _

variable [Finite G]

theorem not_two_dvd_natCard_oddCore (D : Subgroup G) : ¬ 2 ∣ Nat.card (CFSG.oddCore ↥D) :=
  fun h => (Nat.not_even_iff_odd.2 (odd_card_oddCore' ↥D)) (even_iff_two_dvd.2 h)

theorem oddCore_oddQuot (D : Subgroup G) : CFSG.oddCore (OddQuot D) = ⊥ :=
  CFSG.ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot ↥D

theorem kProper_oddQuot (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (D : Subgroup G) : CFSG.Assembly.KProper CFSG.Blueprint.Catalog (OddQuot D) :=
  Hyp.kProper_of_section hkp D (oddProj D) (oddProj_surjective D)

theorem centralizer_map_oddProj (D : Subgroup G) {Q : Subgroup ↥D} (hQ : IsPGroup 2 ↥Q) :
    centralizer ((Q.map (oddProj D) : Subgroup (OddQuot D)) : Set (OddQuot D)) =
      (centralizer (Q : Set ↥D)).map (oddProj D) :=
  CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (not_two_dvd_natCard_oddCore D) hQ

theorem oddProj_comp_subtype_injective (D : Subgroup G) {Q : Subgroup ↥D} (hQ : IsPGroup 2 ↥Q) :
    Function.Injective ((oddProj D).comp Q.subtype) :=
  CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (not_two_dvd_natCard_oddCore D) hQ

end OddQuot

section Transport

variable {G : Type} [Group G]

theorem centralizer_subgroupOf_of_le {D T : Subgroup G} (hTD : T ≤ D) :
    centralizer ((T.subgroupOf D : Subgroup ↥D) : Set ↥D) =
      (centralizer (T : Set G)).subgroupOf D := by
  ext z
  simp only [mem_centralizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTD ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h t ht)

theorem centralizer_singleton_subgroupOf {D : Subgroup G} {g : G} (hg : g ∈ D) :
    centralizer ({(⟨g, hg⟩ : ↥D)} : Set ↥D) = (centralizer ({g} : Set G)).subgroupOf D := by
  ext z
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isCompIn_map_of_not_le_ker {P Q : Type} [Group P] [Group Q] {f : P →* Q}
    (hf : Function.Surjective f) {M X : Subgroup P} (h : IsCompIn M X) (hM : ¬ M ≤ f.ker) :
    IsCompIn (M.map f) (X.map f) := by
  have hq : CFSG.IsQuasisimple ↥(M.map f) :=
    CFSG.LocalCores.isQuasisimple_map h.isQuasisimple f hM
  refine isCompIn_of_subnormal (Subgroup.map_mono h.1) hq ?_
  have hg : Function.Surjective (f.subgroupMap X) := f.subgroupMap_surjective X
  have h1 := h.2.2.map hg
  have heq : (M.subgroupOf X).map (f.subgroupMap X) = (M.map f).subgroupOf (X.map f) := by
    ext ⟨w, hw⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨z, hz, hzw⟩
      exact ⟨z, hz, congrArg Subtype.val hzw⟩
    · rintro ⟨a, ha, haw⟩
      exact ⟨⟨a, h.1 ha⟩, ha, Subtype.ext haw⟩
  rwa [heq] at h1

variable [Finite G]

theorem isCompIn_map_conj_eq_of_commutative_centralizer {H : Type} [Group H] [Finite H] {w : H}
    (hw : w * w = 1)
    (hC : ∀ a ∈ centralizer ({w} : Set H), ∀ b ∈ centralizer ({w} : Set H), a * b = b * a)
    {E : Subgroup H} (hE : IsCompIn E ⊤) :
    E.map (MulAut.conj w).toMonoidHom = E ∧ ¬ E ≤ centralizer ({w} : Set H) := by
  have hq := hE.isQuasisimple
  refine ⟨?_, fun hle => not_forall_commute_of_isQuasisimple hq fun a ha b hb =>
    hC a (hle ha) b (hle hb)⟩
  by_contra hne
  have hE' : IsCompIn (E.map (MulAut.conj w).toMonoidHom) ⊤ := hE.map_conj (Subgroup.mem_top w)
  have hc : ∀ a ∈ E, ∀ b ∈ E.map (MulAut.conj w).toMonoidHom, a * b = b * a :=
    hE.commute_of_ne hE' (Ne.symm hne)
  have hsq : ∀ a ∈ E, w * w * a = a * (w * w) := fun a _ => by rw [hw, one_mul, mul_one]
  have hker := foldHom_ker_le_center hc
  have hrange := range_foldHom_le_centralizer_of_sq hsq hc
  have hcomm : ∀ a b : ↥E, ⁅a, b⁆ ∈ center ↥E := by
    intro a b
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hC _ (hrange (MonoidHom.mem_range.2 ⟨a, rfl⟩)) _
      (hrange (MonoidHom.mem_range.2 ⟨b, rfl⟩))
  have hle : commutator ↥E ≤ center ↥E := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    exact fun a _ b _ => hcomm a b
  have htop : center ↥E = ⊤ := by
    rw [eq_top_iff]
    have := hq.1.commutator_eq_top
    rwa [this] at hle
  refine not_forall_commute_of_isQuasisimple hq fun a ha b hb => ?_
  have h2 := Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top (⟨a, ha⟩ : ↥E)) ⟨b, hb⟩
  exact congrArg Subtype.val h2.symm

theorem isPGroup_center_of_isCompIn {H : Type} [Group H] [Finite H] (hO : CFSG.oddCore H = ⊥)
    {E : Subgroup H} (hE : IsCompIn E ⊤) : IsPGroup 2 ↥(center ↥E) := by
  have hs : E.IsSubnormal := (HSStd.Prop13.isCompIn_top_iff.1 hE).2
  have hO2 : CFSG.pPrimeCore 2 H = ⊥ := by rw [← oddCore_eq_pPrimeCore_two', hO]
  have hle := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hs
  rw [hO2, le_bot_iff] at hle
  have hcore : CFSG.oddCore ↥E = ⊥ := by
    rw [oddCore_eq_pPrimeCore_two']
    exact (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).1 hle
  intro g
  have hg : orderOf (g : ↥E) ≠ 0 := orderOf_ne_zero_iff.2 (isOfFinOrder_of_finite _)
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hg
  refine ⟨k, ?_⟩
  set y : ↥E := (g : ↥E) ^ 2 ^ k with hy
  have hyc : y ∈ center ↥E := pow_mem g.2 _
  have hord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm, Nat.mul_div_cancel_left _
      (by positivity)]
  have hnorm : (zpowers y).Normal := ⟨fun n hn x => by
    have hnc : n ∈ center ↥E := Subgroup.zpowers_le.2 hyc hn
    rw [mem_center_iff.1 hnc x, mul_inv_cancel_right]
    exact hn⟩
  have hodd : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, hord]
    exact hm
  have hle' : zpowers y ≤ CFSG.oddCore ↥E := le_sSup ⟨hnorm, hodd⟩
  rw [hcore, le_bot_iff, zpowers_eq_bot] at hle'
  have hm1 : m = 1 := by rw [← hord, hle', orderOf_one]
  have : (g : ↥E) ^ 2 ^ k = 1 := by
    rw [← hy, ← orderOf_eq_one_iff, hord, hm1]
  exact Subtype.ext this

end Transport

structure NPSetting (G : Type) [Group G] [Finite G] (X : Subgroup G) (u x : G)
    (T₀ : Subgroup G) (s₀ : G) : Prop where
  out : Out G X u
  xmem : x ∈ X
  xinv : orderOf x = 2
  x240 : Nat.card ↥(X ⊓ centralizer ({x} : Set G)) = 240
  cent : X ⊓ centralizer (jOf X x : Set G) = zpowers x
  facts : PropA.Facts X u x
  rbc : RbcFacts X u x
  T_ne : T₀ ≠ ⊥
  T_two : IsPGroup 2 T₀
  comp : IsCompIn (jOf X x) (centralizer (T₀ : Set G))
  s_two : IsPGroup 2 (zpowers s₀)
  s_norm : s₀ ∈ normalizer (T₀ : Set G)
  s_sq : s₀ ^ 2 ∈ T₀
  swap : jOf X x ≠ (jOf X x).map (MulAut.conj s₀).toMonoidHom

section NPNotation

variable {G : Type} [Group G]

abbrev npD (X : Subgroup G) (x : G) : Subgroup G := centralizer (jOf X x : Set G)

abbrev npY (X : Subgroup G) (u x : G) : Subgroup G := npD X x ⊓ centralizer ({u} : Set G)

abbrev npA (X : Subgroup G) (x s₀ : G) : Subgroup G :=
  (jOf X x).map (MulAut.conj s₀).toMonoidHom

theorem npY_le_npD (X : Subgroup G) (u x : G) : npY X u x ≤ npD X x := inf_le_left

end NPNotation

namespace NPSetting

section Basic

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}

theorem u_mem_D (hS : NPSetting G X u x T₀ s₀) : u ∈ npD X x := by
  rw [mem_centralizer_iff]
  intro j hj
  exact ((mem_centralizer_iff.1 (hS.facts.J_le hj).2) u (Set.mem_singleton u)).symm

theorem T_le_D (hS : NPSetting G X u x T₀ s₀) : T₀ ≤ npD X x :=
  le_centralizer_iff.1 hS.comp.1

theorem isCompIn_A (hS : NPSetting G X u x T₀ s₀) :
    IsCompIn (npA X x s₀) (centralizer (T₀ : Set G)) :=
  isCompIn_map_conj_of_mem_normalizer hS.comp
    (mem_normalizer_centralizer_of_mem_normalizer hS.s_norm)

theorem T_le_centralizer_A (hS : NPSetting G X u x T₀ s₀) :
    T₀ ≤ centralizer (npA X x s₀ : Set G) :=
  le_centralizer_iff.1 hS.isCompIn_A.1

theorem A_le_D (hS : NPSetting G X u x T₀ s₀) : npA X x s₀ ≤ npD X x := by
  intro b hb
  rw [mem_centralizer_iff]
  intro a ha
  exact hS.comp.commute_of_ne hS.isCompIn_A hS.swap a ha b hb

theorem card_A (hS : NPSetting G X u x T₀ s₀) : Nat.card ↥(npA X x s₀) = 60 :=
  (Subgroup.card_map_of_injective (fun a b h => (MulAut.conj s₀).injective h)).trans
    hS.facts.card_J

theorem conj_conj_of_mem_J (hS : NPSetting G X u x T₀ s₀) {j : G} (hj : j ∈ jOf X x) :
    (MulAut.conj s₀) ((MulAut.conj s₀) j) = j := by
  have hc : j * s₀ ^ 2 = s₀ ^ 2 * j := mem_centralizer_iff.1 (hS.T_le_D hS.s_sq) j hj
  simp only [MulAut.conj_apply]
  calc s₀ * (s₀ * j * s₀⁻¹) * s₀⁻¹ = (s₀ * s₀) * j * (s₀ * s₀)⁻¹ := by group
    _ = j := by rw [← pow_two, ← hc, mul_inv_cancel_right]

theorem map_conj_A (hS : NPSetting G X u x T₀ s₀) :
    (npA X x s₀).map (MulAut.conj s₀).toMonoidHom = jOf X x := by
  ext g
  constructor
  · rintro ⟨a, ⟨j, hj, rfl⟩, rfl⟩
    exact (hS.conj_conj_of_mem_J hj).symm ▸ hj
  · intro hg
    exact ⟨(MulAut.conj s₀) g, ⟨g, hg, rfl⟩, hS.conj_conj_of_mem_J hg⟩

theorem Y_eq (hS : NPSetting G X u x T₀ s₀) :
    npY X u x = centralizer (jOf X x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)) := by
  ext g
  constructor
  · rintro ⟨hgD, hgu⟩
    have hN : g ∈ centralizer ({u} : Set G) ⊓ normalizer (jOf X x : Set G) :=
      ⟨hgu, Subgroup.centralizer_le_normalizer _ hgD⟩
    rw [hS.rbc.normalizer_J] at hN
    exact ⟨hgD, hN⟩
  · rintro ⟨hgD, -, hgu⟩
    exact ⟨hgD, hgu⟩

theorem card_Y (hS : NPSetting G X u x T₀ s₀) : Nat.card ↥(npY X u x) = 8 := by
  rw [hS.Y_eq]
  exact hS.facts.card_Y

theorem isPGroup_Y (hS : NPSetting G X u x T₀ s₀) : IsPGroup 2 ↥(npY X u x) :=
  IsPGroup.of_card (n := 3) (by rw [hS.card_Y]; norm_num)

theorem Y_comm (hS : NPSetting G X u x T₀ s₀) :
    ∀ a ∈ npY X u x, ∀ b ∈ npY X u x, a * b = b * a := by
  rw [hS.Y_eq]
  exact hS.rbc.Y_comm

@[expose] def ubar (hS : NPSetting G X u x T₀ s₀) : OddQuot (npD X x) :=
  oddProj (npD X x) ⟨u, hS.u_mem_D⟩

theorem ubar_mul_self (hS : NPSetting G X u x T₀ s₀) : hS.ubar * hS.ubar = 1 := by
  have hu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hS.out.inv, pow_two] at this
  change oddProj (npD X x) ⟨u, hS.u_mem_D⟩ * oddProj (npD X x) ⟨u, hS.u_mem_D⟩ = 1
  rw [← map_mul]
  have h : (⟨u, hS.u_mem_D⟩ * ⟨u, hS.u_mem_D⟩ : ↥(npD X x)) = 1 := Subtype.ext hu
  rw [h, map_one]

theorem ubar_ne_one (hS : NPSetting G X u x T₀ s₀) : hS.ubar ≠ 1 := by
  intro h
  have h1 : (⟨u, hS.u_mem_D⟩ : ↥(npD X x)) ∈ CFSG.oddCore ↥(npD X x) :=
    (QuotientGroup.eq_one_iff _).1 h
  have h2 : orderOf (⟨u, hS.u_mem_D⟩ : ↥(npD X x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hS.out.inv
  exact CFSG.ClassicalInvolution.QuaternionStructure.not_mem_oddCore_of_orderOf_eq_two h2 h1

theorem orderOf_ubar (hS : NPSetting G X u x T₀ s₀) : orderOf hS.ubar = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hS.ubar_mul_self) hS.ubar_ne_one

end Basic

section FixedBar

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}

theorem centralizer_ubar (hS : NPSetting G X u x T₀ s₀) :
    centralizer ({hS.ubar} : Set (OddQuot (npD X x))) = oddBar (npD X x) (npY X u x) := by
  have ha2 : orderOf (⟨u, hS.u_mem_D⟩ : ↥(npD X x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hS.out.inv
  have hQ : IsPGroup 2 ↥(zpowers (⟨u, hS.u_mem_D⟩ : ↥(npD X x))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2]; norm_num)
  have h1 := centralizer_map_oddProj (npD X x) hQ
  rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure, zpowers_eq_closure,
    centralizer_closure, centralizer_singleton_subgroupOf hS.u_mem_D] at h1
  change centralizer ({oddProj (npD X x) ⟨u, hS.u_mem_D⟩} : Set (OddQuot (npD X x))) =
    ((npD X x ⊓ centralizer ({u} : Set G)).subgroupOf (npD X x)).map (oddProj (npD X x))
  rw [Subgroup.inf_subgroupOf_left]
  exact h1

theorem injective_oddProj_Y (hS : NPSetting G X u x T₀ s₀) :
    Function.Injective
      ((oddProj (npD X x)).comp (Subgroup.inclusion (npY_le_npD X u x))) := by
  have hle := npY_le_npD X u x
  have hQ : IsPGroup 2 ↥((npY X u x).subgroupOf (npD X x)) :=
    hS.isPGroup_Y.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hinj := oddProj_comp_subtype_injective (npD X x) hQ
  have heq : (oddProj (npD X x)).comp (Subgroup.inclusion hle) =
      ((oddProj (npD X x)).comp ((npY X u x).subgroupOf (npD X x)).subtype).comp
        (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom := by
    ext y
    rfl
  rw [heq]
  exact hinj.comp (Subgroup.subgroupOfEquivOfLe hle).symm.injective

theorem range_oddProj_Y (hS : NPSetting G X u x T₀ s₀) :
    ((oddProj (npD X x)).comp (Subgroup.inclusion (npY_le_npD X u x))).range =
      centralizer ({hS.ubar} : Set (OddQuot (npD X x))) := by
  rw [hS.centralizer_ubar, MonoidHom.range_comp, Subgroup.inclusion_range]

@[expose] noncomputable def fixedBarEquiv (hS : NPSetting G X u x T₀ s₀) :
    ↥(npY X u x) ≃* ↥(centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) :=
  (MonoidHom.ofInjective hS.injective_oddProj_Y).trans
    (MulEquiv.subgroupCongr hS.range_oddProj_Y)

theorem coe_fixedBarEquiv (hS : NPSetting G X u x T₀ s₀) (y : ↥(npY X u x)) :
    ((hS.fixedBarEquiv y : ↥(centralizer ({hS.ubar} : Set (OddQuot (npD X x))))) :
      OddQuot (npD X x)) = oddProj (npD X x) ⟨y, npY_le_npD X u x y.2⟩ :=
  rfl

theorem card_fixed_bar (hS : NPSetting G X u x T₀ s₀) :
    Nat.card ↥(centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) = 8 :=
  (Nat.card_congr hS.fixedBarEquiv.toEquiv.symm).trans hS.card_Y

theorem isPGroup_fixed_bar (hS : NPSetting G X u x T₀ s₀) :
    IsPGroup 2 ↥(centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) :=
  hS.isPGroup_Y.of_equiv hS.fixedBarEquiv

theorem fixed_bar_comm (hS : NPSetting G X u x T₀ s₀) :
    ∀ a ∈ centralizer ({hS.ubar} : Set (OddQuot (npD X x))),
      ∀ b ∈ centralizer ({hS.ubar} : Set (OddQuot (npD X x))), a * b = b * a := by
  intro a ha b hb
  obtain ⟨y₁, hy₁⟩ := hS.fixedBarEquiv.surjective ⟨a, ha⟩
  obtain ⟨y₂, hy₂⟩ := hS.fixedBarEquiv.surjective ⟨b, hb⟩
  have h := congrArg Subtype.val
    (show hS.fixedBarEquiv (y₁ * y₂) = hS.fixedBarEquiv (y₂ * y₁) from
      congrArg _ (Subtype.ext (hS.Y_comm _ y₁.2 _ y₂.2)))
  rw [map_mul, map_mul, hy₁, hy₂] at h
  exact h

end FixedBar

section Abar

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}

theorem not_le_ker_A (hS : NPSetting G X u x T₀ s₀) :
    ¬ (npA X x s₀).subgroupOf (npD X x) ≤ (oddProj (npD X x)).ker := by
  intro hle
  rw [ker_oddProj] at hle
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.A_le_D).toEquiv, hS.card_A] at h1
  exact not_two_dvd_natCard_oddCore (npD X x) (dvd_trans (by norm_num) h1)

theorem isPGroup_oddBar_T (hS : NPSetting G X u x T₀ s₀) :
    IsPGroup 2 ↥(oddBar (npD X x) T₀) :=
  (hS.T_two.of_equiv (Subgroup.subgroupOfEquivOfLe hS.T_le_D).symm).map (oddProj (npD X x))

theorem isCompIn_Abar (hS : NPSetting G X u x T₀ s₀) :
    IsCompIn (oddBar (npD X x) (npA X x s₀))
      (centralizer ((oddBar (npD X x) T₀ : Subgroup (OddQuot (npD X x))) :
        Set (OddQuot (npD X x)))) := by
  have hAD : npA X x s₀ ≤ npD X x := hS.A_le_D
  have hTD : T₀ ≤ npD X x := hS.T_le_D
  have hAC : npA X x s₀ ≤ centralizer (T₀ : Set G) ⊓ npD X x := le_inf hS.isCompIn_A.1 hAD
  have hcomp1 : IsCompIn (npA X x s₀) (centralizer (T₀ : Set G) ⊓ npD X x) :=
    isCompIn_of_le hS.isCompIn_A hAC inf_le_left
  have hcomp2 := isCompIn_subgroupOf hcomp1 (inf_le_right : centralizer (T₀ : Set G) ⊓ npD X x ≤
    npD X x)
  rw [Subgroup.inf_subgroupOf_right, ← centralizer_subgroupOf_of_le hTD] at hcomp2
  have hQ2 : IsPGroup 2 ↥(T₀.subgroupOf (npD X x)) :=
    hS.T_two.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm
  change IsCompIn (oddBar (npD X x) (npA X x s₀))
    (centralizer (((T₀.subgroupOf (npD X x)).map (oddProj (npD X x)) :
      Subgroup (OddQuot (npD X x))) : Set (OddQuot (npD X x))))
  rw [centralizer_map_oddProj (npD X x) hQ2]
  exact isCompIn_map_of_not_le_ker (oddProj_surjective (npD X x)) hcomp2 hS.not_le_ker_A

theorem center_A_eq_bot (hS : NPSetting G X u x T₀ s₀) : center ↥(npA X x s₀) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨j, hj, hjz⟩ := z.2
  have h1 : j = 1 := by
    refine hS.facts.J_center j hj fun j' hj' => ?_
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz
      ⟨(MulAut.conj s₀) j', ⟨j', hj', rfl⟩⟩)
    have h3 : (MulAut.conj s₀) (j' * j) = (MulAut.conj s₀) (j * j') := by
      rw [map_mul, map_mul]
      change (MulAut.conj s₀) j' * (z : G) = (z : G) * (MulAut.conj s₀) j' at h2
      rw [← hjz] at h2
      exact h2
    exact ((MulAut.conj s₀).injective h3).symm
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [← hjz, h1]
  exact map_one _

theorem injective_oddProj_A (hS : NPSetting G X u x T₀ s₀) :
    Function.Injective ((oddProj (npD X x)).comp (Subgroup.inclusion hS.A_le_D)) := by
  set f := (oddProj (npD X x)).comp (Subgroup.inclusion hS.A_le_D) with hf
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hS.isCompIn_A.isQuasisimple
      (MonoidHom.normal_ker f) with h | h
  · exfalso
    refine hS.not_le_ker_A fun a ha => ?_
    have h1 : (⟨(a : G), ha⟩ : ↥(npA X x s₀)) ∈ f.ker := h ▸ Subgroup.mem_top _
    exact h1
  · rw [hS.center_A_eq_bot, le_bot_iff] at h
    exact (MonoidHom.ker_eq_bot_iff f).1 h

theorem range_oddProj_A (hS : NPSetting G X u x T₀ s₀) :
    ((oddProj (npD X x)).comp (Subgroup.inclusion hS.A_le_D)).range =
      oddBar (npD X x) (npA X x s₀) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

@[expose] noncomputable def oddBarEquivA (hS : NPSetting G X u x T₀ s₀) :
    ↥(npA X x s₀) ≃* ↥(oddBar (npD X x) (npA X x s₀)) :=
  (MonoidHom.ofInjective hS.injective_oddProj_A).trans
    (MulEquiv.subgroupCongr hS.range_oddProj_A)

theorem card_Abar (hS : NPSetting G X u x T₀ s₀) :
    Nat.card ↥(oddBar (npD X x) (npA X x s₀)) = 60 :=
  (Nat.card_congr hS.oddBarEquivA.toEquiv.symm).trans hS.card_A

end Abar

section Layer

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}

theorem Abar_le_layer (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    oddBar (npD X x) (npA X x s₀) ≤ layerIn (⊤ : Subgroup (OddQuot (npD X x))) := by
  have hĀ := hS.isCompIn_Abar
  have hkp := kProper_oddQuot hS.out.std.kProper (npD X x)
  have hO := oddCore_oddQuot (npD X x)
  have hST : ⁅(T₀.subgroupOf (npD X x)).map (oddProj (npD X x)),
      (⊥ : Subgroup (OddQuot (npD X x)))⁆ ≤
      (T₀.subgroupOf (npD X x)).map (oddProj (npD X x)) ⊓ ⊥ := by
    rw [Subgroup.commutator_bot_right]
    exact bot_le
  have h1 := Junction.layerIn_inf_le_of_lemma15At
    (h15 (OddQuot (npD X x)) ⟨npD X x, oddProj (npD X x), oddProj_surjective (npD X x)⟩)
    hkp hO hS.isPGroup_oddBar_T (IsPGroup.of_bot) hST hĀ
  have htop : centralizer (((⊥ : Subgroup (OddQuot (npD X x))) : Subgroup _) :
      Set (OddQuot (npD X x))) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    simp
  rw [htop, inf_top_eq] at h1
  exact (Junction.le_layerIn_of_isCompIn (isCompIn_of_le hĀ le_rfl hĀ.1)).trans h1

theorem comp_invariant (hS : NPSetting G X u x T₀ s₀) {E₁ : Subgroup (OddQuot (npD X x))}
    (hE : IsCompIn E₁ ⊤) :
    E₁.map (MulAut.conj hS.ubar).toMonoidHom = E₁ ∧
      ¬ E₁ ≤ centralizer ({hS.ubar} : Set (OddQuot (npD X x))) :=
  isCompIn_map_conj_eq_of_commutative_centralizer hS.ubar_mul_self hS.fixed_bar_comm hE

end Layer

section KDNPInterface

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}
  {E₁ : Subgroup (OddQuot (npD X x))}

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] noncomputable def compAut (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    MulAut ↥E₁ :=
  ((MulAut.conj hS.ubar).subgroupMap E₁).trans (MulEquiv.subgroupCongr (hS.comp_invariant hE).1)

theorem coe_compAut (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) (e : ↥E₁) :
    ((hS.compAut hE e : ↥E₁) : OddQuot (npD X x)) = hS.ubar * e * hS.ubar⁻¹ :=
  rfl

theorem compAut_compAut (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) (e : ↥E₁) :
    hS.compAut hE (hS.compAut hE e) = e := by
  apply Subtype.ext
  have hinv : hS.ubar⁻¹ = hS.ubar := inv_eq_of_mul_eq_one_right hS.ubar_mul_self
  rw [coe_compAut, coe_compAut, hinv]
  calc hS.ubar * (hS.ubar * (e : OddQuot (npD X x)) * hS.ubar) * hS.ubar
      = (hS.ubar * hS.ubar) * (e : OddQuot (npD X x)) * (hS.ubar * hS.ubar) := by
        simp only [mul_assoc]
    _ = e := by rw [hS.ubar_mul_self, one_mul, mul_one]

theorem compAut_ne_one (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    hS.compAut hE ≠ 1 := by
  intro h
  refine (hS.comp_invariant hE).2 fun e he => ?_
  rw [mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have h1 := congrArg (fun σ : MulAut ↥E₁ => ((σ ⟨e, he⟩ : ↥E₁) : OddQuot (npD X x))) h
  simp only [coe_compAut, MulAut.one_apply] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem orderOf_compAut (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    orderOf (hS.compAut hE) = 2 :=
  orderOf_eq_prime (by
    rw [pow_two]
    exact MulEquiv.ext fun e => hS.compAut_compAut hE e) (hS.compAut_ne_one hE)

theorem mem_fixedSubgroup_compAut_iff (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤)
    (e : ↥E₁) : e ∈ fixedSubgroup (hS.compAut hE) ↔
      (e : OddQuot (npD X x)) ∈ centralizer ({hS.ubar} : Set (OddQuot (npD X x))) := by
  rw [mem_centralizer_iff]
  change hS.compAut hE e = e ↔ _
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have h1 := congrArg Subtype.val h
    rw [coe_compAut] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  · intro h
    apply Subtype.ext
    rw [coe_compAut]
    exact mul_inv_eq_iff_eq_mul.2 (h _ (Set.mem_singleton _))

@[expose] noncomputable def fixedToCentralizer (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    ↥(fixedSubgroup (hS.compAut hE)) →*
      ↥(centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) :=
  ((E₁.subtype).comp (fixedSubgroup (hS.compAut hE)).subtype).codRestrict _
    fun e => (hS.mem_fixedSubgroup_compAut_iff hE e).1 e.2

theorem fixedToCentralizer_injective (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    Function.Injective (hS.fixedToCentralizer hE) := fun a b h => by
  have h1 := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h1)

theorem fixedSubgroup_compAut_eq (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    fixedSubgroup (hS.compAut hE) =
      (E₁ ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x)))).subgroupOf E₁ := by
  ext e
  rw [hS.mem_fixedSubgroup_compAut_iff hE, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩

theorem card_fixedSubgroup_compAut (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    Nat.card ↥(fixedSubgroup (hS.compAut hE)) =
      Nat.card ↥(E₁ ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) := by
  rw [hS.fixedSubgroup_compAut_eq hE]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem isPGroup_fixedSubgroup_compAut (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    IsPGroup 2 ↥(fixedSubgroup (hS.compAut hE)) :=
  hS.isPGroup_fixed_bar.of_injective _ (hS.fixedToCentralizer_injective hE)

theorem card_fixedSubgroup_compAut_le (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    Nat.card ↥(fixedSubgroup (hS.compAut hE)) ≤ 8 :=
  (Nat.card_le_card_of_injective _ (hS.fixedToCentralizer_injective hE)).trans_eq
    hS.card_fixed_bar

theorem kdnp_comp (hNP : KDNP) (hS : NPSetting G X u x T₀ s₀) (hE : IsCompIn E₁ ⊤) :
    (Nonempty ((↥E₁ ⧸ center ↥E₁) ≃* alternatingGroup (Fin 5)) ∧
        Nat.card ↥(E₁ ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) = 4) ∨
      Nat.card ↥(E₁ ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) = 8 := by
  rw [← hS.card_fixedSubgroup_compAut hE]
  obtain ⟨n, hn⟩ := (hS.isPGroup_fixedSubgroup_compAut hE).exists_card_eq
  have hle := hS.card_fixedSubgroup_compAut_le hE
  by_cases h4 : Nat.card ↥(fixedSubgroup (hS.compAut hE)) ≤ 4
  · exact Or.inl (hNP.1 ↥E₁ hE.isQuasisimple
      (isPGroup_center_of_isCompIn (oddCore_oddQuot (npD X x)) hE) (hS.compAut hE)
      (hS.orderOf_compAut hE) (hS.isPGroup_fixedSubgroup_compAut hE) h4)
  · refine Or.inr ?_
    have hn3 : n < 4 := by
      by_contra h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 h)
      omega
    interval_cases n <;> omega

end KDNPInterface

end NPSetting

theorem npSetting_of_fiveALink {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G}
    {L' : Subgroup G} (hO : Out G X u) (hxX : x ∈ X) (hx2 : orderOf x = 2)
    (hx240 : Nat.card ↥(X ⊓ centralizer ({x} : Set G)) = 240)
    (hcent : X ⊓ centralizer (jOf X x : Set G) = zpowers x) (hF : PropA.Facts X u x)
    (hR : RbcFacts X u x) (h : FiveALink (jOf X x) L') :
    ∃ (T₀ : Subgroup G) (s₀ : G), NPSetting G X u x T₀ s₀ := by
  obtain ⟨T₀, s₀, hT, hT2, hK, hs2, hsN, hs, -, -, -, hswap, -⟩ := h
  exact ⟨T₀, s₀, hO, hxX, hx2, hx240, hcent, hF, hR, hT, hT2, hK, hs2, hsN, hs, hswap⟩

end CFSG.EvenSporadicStandard.M12Std.Rbc
