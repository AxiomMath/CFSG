module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.KleinOrder156
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Thirteen
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open

section Generic

variable {G Q : Type*} [Group G] [Finite G] [Group Q]

theorem eq_or_eq_of_card_le_two {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : Nat.card T ≤ 2) {a b x : X} (ha : a ∈ T) (hb : b ∈ T) (hx : x ∈ T) (hab : a ≠ b) :
    x = a ∨ x = b := by
  by_contra hcon
  rw [not_or] at hcon
  have h3 : ({a, b, x} : Set X).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨a, b, x, hab, Ne.symm hcon.1, Ne.symm hcon.2, rfl⟩
  have hsub : ({a, b, x} : Set X) ⊆ (T : Set X) := by
    intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hT' : (T : Set X).ncard ≤ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hT
  omega

theorem exists_lift_centralizer (E : Subgroup G) [E.Normal] (e : G ⧸ E ≃* Q) {p : ℕ}
    [Fact p.Prime] (hE : ¬ p ∣ Nat.card E) {c : G} (hc : orderOf c = p) {a : Q}
    (ha : a * e (QuotientGroup.mk c) = e (QuotientGroup.mk c) * a) :
    ∃ x : G, x * c = c * x ∧ e (QuotientGroup.mk x) = a := by
  have hQ : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hcent := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := p) (N := E) hE hQ
  have hb : e.symm a ∈ Subgroup.centralizer
      (((Subgroup.zpowers c).map (QuotientGroup.mk' E) : Subgroup (G ⧸ E)) : Set (G ⧸ E)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have h1 : QuotientGroup.mk c * e.symm a = e.symm a * QuotientGroup.mk c := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact ha.symm
    have h2 : Commute (QuotientGroup.mk c : G ⧸ E) (e.symm a) := h1
    simpa using (h2.zpow_left k).eq
  rw [hcent] at hb
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 hb
  refine ⟨x, (Subgroup.mem_centralizer_iff.1 hx c (Subgroup.mem_zpowers _)).symm, ?_⟩
  change e (QuotientGroup.mk x) = a
  rw [show (QuotientGroup.mk x : G ⧸ E) = e.symm a from hxa, MulEquiv.apply_symm_apply]

theorem eq_one_or_eq_of_involution_of_quotient (E : Subgroup G) [E.Normal] (e : G ⧸ E ≃* Q)
    (hE : ¬ 13 ∣ Nat.card E) {c v w t : G} (hc : orderOf c = 13)
    (hy : orderOf (e (QuotientGroup.mk c)) = 13)
    (hv1 : v ≠ 1) (hv2 : v * v = 1) (hvE : v ∈ E) (hvG : ∀ g : G, g * v = v * g)
    (hvc : c * v = v * c)
    (hEc : Nat.card ↥(E ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 2)
    (hA : Nat.card (Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q)) = 156)
    (hNE : ∀ g ∈ Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q),
      ∀ z ∈ Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q), orderOf z = 3 →
        g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1)
    (hw4 : w ^ 4 = 1) (hw2 : w ^ 2 ≠ 1) (hwc : w * c = c * w)
    (ht : t * t = 1) (htc : t * c = c * t) : t = 1 ∨ t = v := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Finite (Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q)) :=
    Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  let φ : G →* Q := (e : G ⧸ E →* Q).comp (QuotientGroup.mk' E)
  have hφ : ∀ x, φ x = e (QuotientGroup.mk x) := fun x => rfl
  have hφC : ∀ x : Subgroup.centralizer ({c} : Set G),
      φ x ∈ Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q) := by
    intro x
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hφ, ← map_mul, ← map_mul, hx]
  let π : Subgroup.centralizer ({c} : Set G) →*
      Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q) :=
    ((φ.comp (Subgroup.centralizer ({c} : Set G)).subtype).codRestrict _ hφC)
  have hπval : ∀ x : Subgroup.centralizer ({c} : Set G), ((π x : _) : Q) = e (QuotientGroup.mk (x : G)) :=
    fun x => rfl
  have hπ : Function.Surjective π := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, hxa⟩ := exists_lift_centralizer E e hE hc (Subgroup.mem_centralizer_singleton_iff.1 ha)
    exact ⟨⟨x, Subgroup.mem_centralizer_singleton_iff.2 hx⟩, Subtype.ext hxa⟩
  have hvC : v ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hvc.symm
  have hv1' : (⟨v, hvC⟩ : Subgroup.centralizer ({c} : Set G)) ≠ 1 := fun h =>
    hv1 (congrArg Subtype.val h)
  have hv2' : (⟨v, hvC⟩ : Subgroup.centralizer ({c} : Set G)) * ⟨v, hvC⟩ = 1 :=
    Subtype.ext hv2
  have hvc' : ∀ g : Subgroup.centralizer ({c} : Set G), g * ⟨v, hvC⟩ = ⟨v, hvC⟩ * g := fun g =>
    Subtype.ext (hvG g)
  have hker : ∀ x : Subgroup.centralizer ({c} : Set G), π x = 1 →
      x = 1 ∨ x = ⟨v, hvC⟩ := by
    intro x hx
    have h1 : e (QuotientGroup.mk (x : G)) = 1 := congrArg Subtype.val hx
    have h2 : (x : G) ∈ E := (QuotientGroup.eq_one_iff _).1 ((MulEquiv.map_eq_one_iff e).1 h1)
    have hxT : (x : G) ∈ E ⊓ Subgroup.centralizer ({c} : Set G) := Subgroup.mem_inf.2 ⟨h2, x.2⟩
    have hvT : v ∈ E ⊓ Subgroup.centralizer ({c} : Set G) := Subgroup.mem_inf.2 ⟨hvE, hvC⟩
    have h1T : (1 : G) ∈ E ⊓ Subgroup.centralizer ({c} : Set G) := Subgroup.one_mem _
    rcases eq_or_eq_of_card_le_two hEc h1T hvT hxT (Ne.symm hv1) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hcA : e (QuotientGroup.mk c) ∈ Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hAord : orderOf (⟨e (QuotientGroup.mk c), hcA⟩ :
      Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q)) = 13 := by
    rw [Subgroup.orderOf_mk]
    exact hy
  have hAcentral : ∀ g : Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q),
      g * (⟨e (QuotientGroup.mk c), hcA⟩ : Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q)) =
        ⟨e (QuotientGroup.mk c), hcA⟩ * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hANE : ∀ g z : Subgroup.centralizer ({e (QuotientGroup.mk c)} : Set Q), orderOf z = 3 →
      g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1 := by
    intro g z hz hgz
    have hz' : orderOf (z : Q) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgz
    have hgz' : (g : Q) * z * (g : Q)⁻¹ ∈ Subgroup.zpowers (z : Q) := by
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have h39 := hNE g g.2 z z.2 hz' hgz'
    exact Subtype.ext (by simpa using h39)
  haveI := hA
  obtain ⟨hα, hβ⟩ := klein_of_card_156 hA hAord hAcentral hANE
  have hwC : w ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hwc
  have hw4' : (⟨w, hwC⟩ : Subgroup.centralizer ({c} : Set G)) ^ 4 = 1 :=
    Subtype.ext (by simpa using hw4)
  have hw2' : (⟨w, hwC⟩ : Subgroup.centralizer ({c} : Set G)) ^ 2 ≠ 1 := fun h =>
    hw2 (by simpa using congrArg Subtype.val h)
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 htc
  have ht' : (⟨t, htC⟩ : Subgroup.centralizer ({c} : Set G)) * ⟨t, htC⟩ = 1 :=
    Subtype.ext ht
  rcases eq_one_or_eq_of_mul_self_eq_one π hπ hv1' hv2' hvc' hker hα hβ hw4' hw2' ht' with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem eq_bot_of_normal_of_core_eq_bot {X : Type*} [Group X] [Finite X] {p : ℕ} {C : Subgroup X}
    (hC : GLAPPrimeCoreOf p C = ⊥) (K : Subgroup C) [hK : K.Normal]
    (hcop : Nat.Coprime p (Nat.card K)) : K = ⊥ := by
  have hS := le_GLAPPrimeCoreOf_of_normal (p := p) (C := C) (S := K.map C.subtype)
    (Subgroup.map_subtype_le K)
    (by
      intro g hg x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_map.2 ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, hK.conj_mem k hk _, by simp⟩)
    (by rw [Subgroup.card_map_of_injective C.subtype_injective]; exact hcop)
  rw [hC, le_bot_iff] at hS
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hS

theorem card_le_of_isPGroup_of_factorization {X : Type*} [Group X] [Finite X] {p k : ℕ}
    [Fact p.Prime] (hX : (Nat.card X).factorization p = k) (C : Subgroup X) (R : Subgroup C)
    (hR : IsPGroup p R) : Nat.card R ≤ p ^ k := by
  have hR' : IsPGroup p (R.map C.subtype) := hR.map C.subtype
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hR'
  have hdvd : p ^ m ∣ Nat.card X := hm ▸ Subgroup.card_subgroup_dvd_card _
  have hmk : m ≤ k := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime) Nat.card_pos.ne').1 hdvd
    rwa [hX] at this
  rw [← Subgroup.card_map_of_injective (K := R) C.subtype_injective, hm]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hmk

theorem card_centralizer_subtype_eq {X : Type*} [Group X] {u c : X}
    (hu : u ∈ Subgroup.centralizer ({c} : Set X)) :
    Nat.card (Subgroup.centralizer
        ({(⟨u, hu⟩ : Subgroup.centralizer ({c} : Set X))} : Set (Subgroup.centralizer ({c} : Set X)))) =
      Nat.card ↥(Subgroup.centralizer ({u} : Set X) ⊓ Subgroup.centralizer ({c} : Set X)) :=
  Nat.card_congr
    { toFun := fun y => ⟨(y.1 : X), Subgroup.mem_inf.2 ⟨
        Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)), y.1.2⟩⟩
      invFun := fun z => ⟨⟨z.1, (Subgroup.mem_inf.1 z.2).2⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 z.2).1))⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }

theorem isolated_of_unique_involution {X : Type*} [Group X] {x c : X} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxc : x * c = c * x) (hxC : x ∈ Subgroup.centralizer ({c} : Set X))
    (huniq : ∀ t : X, t * t = 1 → t * x = x * t → t * c = c * t → t = 1 ∨ t = x)
    (g : Subgroup.centralizer ({c} : Set X))
    (hg : (g * (⟨x, hxC⟩ : Subgroup.centralizer ({c} : Set X)) * g⁻¹) * ⟨x, hxC⟩ =
      ⟨x, hxC⟩ * (g * ⟨x, hxC⟩ * g⁻¹)) :
    g * (⟨x, hxC⟩ : Subgroup.centralizer ({c} : Set X)) * g⁻¹ = ⟨x, hxC⟩ := by
  have hg' : ((g : X) * x * (g : X)⁻¹) * x = x * ((g : X) * x * (g : X)⁻¹) := congrArg Subtype.val hg
  have hgc : Commute (g : X) c := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hxc' : Commute x c := hxc
  have htc : ((g : X) * x * (g : X)⁻¹) * c = c * ((g : X) * x * (g : X)⁻¹) :=
    ((hgc.mul_left hxc').mul_left hgc.inv_left).eq
  have ht2 : ((g : X) * x * (g : X)⁻¹) * ((g : X) * x * (g : X)⁻¹) = 1 := by
    calc ((g : X) * x * (g : X)⁻¹) * ((g : X) * x * (g : X)⁻¹) =
        (g : X) * (x * x) * (g : X)⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  rcases huniq _ ht2 hg' htc with h | h
  · exfalso
    apply hx1
    have := congrArg (fun a => (g : X)⁻¹ * a * (g : X)) h
    simpa [mul_assoc] using this
  · exact Subtype.ext h

theorem xGmat_mul_self' : xGmat * xGmat = 1 := by
  rw [← pow_two, ← orderOf_xGmat, pow_orderOf_eq_one]

theorem xGmat_ne_one' : xGmat ≠ 1 := by
  intro h
  have := orderOf_xGmat
  rw [h, orderOf_one] at this
  omega

end Generic

section Monster


@[expose] noncomputable def xH : cent xGmat := ⟨xGmat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem xH_mem_pCore : xH ∈ CFSG.pCore 2 (cent xGmat) := by
  rw [mem_pCore_cent_xGmat_iff]
  have h := rhoG_mem (true, 0, 0)
  rw [rhoG_z_eq_xGmat, Subgroup.mem_subgroupOf] at h
  exact h

theorem c13H_mul_xH : c13H * xH = xH * c13H :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c_mem_cent)

theorem not_dvd_card_pCore_thirteen : ¬ 13 ∣ Nat.card (CFSG.pCore 2 (cent xGmat)) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := cent xGmat))
  rw [hn]
  intro h
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 13) h)
  omega

theorem orderOf_image_c13H
    (e : cent xGmat ⧸ CFSG.pCore 2 (cent xGmat) ≃* CFSG.Blueprint.NativeSporadic.Co1) :
    orderOf (e (QuotientGroup.mk c13H)) = 13 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_image_co1 e (by norm_num) orderOf_c13H

theorem co1_facts_c13H
    (e : cent xGmat ⧸ CFSG.pCore 2 (cent xGmat) ≃* CFSG.Blueprint.NativeSporadic.Co1) :
    Nat.card (Subgroup.centralizer
      ({e (QuotientGroup.mk c13H)} : Set CFSG.Blueprint.NativeSporadic.Co1)) = 156 ∧
    NoEvenNormalizer (e (QuotientGroup.mk c13H)) :=
  co1_thirteen_facts _ (orderOf_image_c13H e)

theorem exists_order_four_c13 :
    ∃ w : cent xGmat, w ^ 4 = 1 ∧ w ^ 2 ≠ 1 ∧ w * c13H = c13H * w := by
  obtain ⟨-, -, -, -, -, -, -, -, hw4, hwv, hwc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw2, -, -⟩ :=
    thirteen_b_facts
  have hwK : gw wvW13 ∈ cent xGmat := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← gw_vW13_eq]
    exact hwv.symm
  refine ⟨⟨gw wvW13, hwK⟩, Subtype.ext (by simpa using hw4), fun h => hw2 ?_, Subtype.ext hwc.symm⟩
  simpa [pow_two] using congrArg Subtype.val h

theorem eq_one_or_eq_xGmat_of_involution {t : Gmat} (ht : t * t = 1)
    (htx : t * xGmat = xGmat * t) (htc : t * gw genD13W1 = gw genD13W1 * t) :
    t = 1 ∨ t = xGmat := by
  haveI : Finite (cent xGmat) := finite_cent_xGmat
  obtain ⟨e⟩ := twoB_xGmat₁₃.2.2.2.1
  obtain ⟨h156, hNE⟩ := co1_facts_c13H e
  obtain ⟨w, hw4, hw2, hwc⟩ := exists_order_four_c13
  have htK : t ∈ cent xGmat := Subgroup.mem_centralizer_singleton_iff.2 htx
  have key := @eq_one_or_eq_of_involution_of_quotient (cent xGmat)
    CFSG.Blueprint.NativeSporadic.Co1 _ _ Units.instGroup (CFSG.pCore 2 (cent xGmat)) _ e
    not_dvd_card_pCore_thirteen c13H xH w ⟨t, htK⟩ orderOf_c13H (orderOf_image_c13H e)
    (fun h => xGmat_ne_one' (congrArg Subtype.val h)) (Subtype.ext xGmat_mul_self')
    xH_mem_pCore
    (fun g => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2))
    c13H_mul_xH (card_pCore_inf_centralizer_le_two orderOf_c13H) h156 hNE
    hw4 hw2 hwc (Subtype.ext ht) (Subtype.ext htc)
  rcases key with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end Monster

end CFSG.HardMathSupport.Dickson.Sec6.I1431
