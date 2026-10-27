module

public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45K
public import CFSG.GH74.Generic.BProg.B1.PilotS4

public section

namespace CFSG.GH74.Generic.BProg.B3.FalseCtxS45

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS4
open scoped commutatorElement

@[expose] def KCentIn (Kt : Type) [Group Kt] : Prop :=
  ∀ s : Kt, orderOf s = 2 →
    IsSimpleGroup ↥⁅centralizer ({s} : Set Kt), centralizer ({s} : Set Kt)⁆ ∧
      (∃ a b : ↥⁅centralizer ({s} : Set Kt), centralizer ({s} : Set Kt)⁆, a * b ≠ b * a) ∧
        HasL2Model ↥⁅centralizer ({s} : Set Kt), centralizer ({s} : Set Kt)⁆ Odd

section Small

theorem isPerfect_of_simple_nonab {S : Type*} [Group S] (hS : IsSimpleGroup S) (hn : ∃ a b : S, a * b ≠ b * a) :
    Group.IsPerfect S := by
  rcases (inferInstance : (_root_.commutator S).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have h1 : ⁅a, b⁆ ∈ _root_.commutator S := commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · exact ⟨h⟩

theorem commutator_self_of_simple_nonab {Kt : Type} [Group Kt] {S : Subgroup Kt}
    (hS : IsSimpleGroup ↥S) (hn : ∃ a b : ↥S, a * b ≠ b * a) : ⁅S, S⁆ = S :=
  Subgroup.isPerfect_iff.mp (isPerfect_of_simple_nonab hS hn)

theorem false_of_odd_surjection {S V : Type} [Group S] [Group V] [Finite V] (hS : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) (g : V →* S) (hg : Function.Surjective g) (hodd : Odd (Nat.card V)) :
    False := by
  have hsolv : Group.IsSolvable V := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolv' : Group.IsSolvable S := Group.isSolvable_of_surjective hg
  have hnt : Nontrivial S := hS.toNontrivial
  have hp : Group.IsPerfect S := isPerfect_of_simple_nonab hS hn
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial S
  have h2 : _root_.commutator S = ⊤ := Group.IsPerfect.commutator_eq_top (G := S)
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem false_of_odd_image {V Kt : Type} [Group V] [Finite V] [Group Kt] (f : V →* Kt) (hodd : Odd (Nat.card V))
    {S : Subgroup Kt} (hS : f.range = S) (hperf : ⁅S, S⁆ = S) (hne : S ≠ ⊥) : False := by
  have hsolv : Group.IsSolvable V := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolv' : Group.IsSolvable ↥f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  rw [hS] at hsolv'
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥S
  have hp : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hperf
  have h2 : _root_.commutator ↥S = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

end Small

section Decomp

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

omit [Finite G] in
theorem inf_centralizer_mul_eq {K : Subgroup G} {x e : G} (hK : K ≤ centralizer ({x} : Set G)) :
    K ⊓ centralizer ({e * x} : Set G) = K ⊓ centralizer ({e} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hgK, h⟩
    refine ⟨hgK, ?_⟩
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hK hgK)
    have h1 : g * e * x = e * g * x := by
      calc g * e * x = g * (e * x) := by rw [mul_assoc]
        _ = e * x * g := h
        _ = e * (x * g) := by rw [mul_assoc]
        _ = e * (g * x) := by rw [hgx]
        _ = e * g * x := by rw [mul_assoc]
    exact mul_right_cancel h1
  · rintro ⟨hgK, h⟩
    refine ⟨hgK, ?_⟩
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hK hgK)
    calc g * (e * x) = g * e * x := by rw [mul_assoc]
      _ = e * g * x := by rw [h]
      _ = e * (g * x) := by rw [mul_assoc]
      _ = e * (x * g) := by rw [hgx]
      _ = e * x * g := by rw [mul_assoc]

theorem exists_E (hc : Ctx21 G x K A a D J)
    (hcen : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g : ↥K ⧸ pPrimeCore 2 ↥K, g * z = z * g) → z = 1) :
    ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 4 := by
  obtain ⟨-, -, -, hcase⟩ := hc.src
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, hxE, hEel, hE4, -⟩
  · exact (not_qShape1_of_center_trivial h1 hcen).elim
  · exact ⟨E, hEK, hAE, hxE, hEel, hE4⟩

theorem exists_e (hc : Ctx21 G x K A a D J) (hax : a ≠ x) {E : Subgroup G} (hEK : E ≤ K)
    (hAE : A = E ⊔ zpowers x) (hEel : CFSG.IsElementaryAbelian 2 ↥E) :
    ∃ e ∈ E, orderOf e = 2 ∧ K ⊓ centralizer ({a} : Set G) = K ⊓ centralizer ({e} : Set G) := by
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hKx : K ≤ centralizer ({x} : Set G) := hK.1
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have ha1 : a ≠ 1 := fun h => by simp [h] at ha2
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hcommEx : ∀ g ∈ E, ∀ h ∈ zpowers x, g * h = h * g := by
    intro g hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hKx (hEK hg))
    exact (Commute.zpow_right (show Commute g x from hgx) k).eq
  have haA : a ∈ E ⊔ zpowers x := hAE ▸ hc.a_mem
  obtain ⟨e, heE, z, hz, hae⟩ := mem_sup_of_commute hcommEx haA
  rcases mem_zpowers_of_two hx hz with hz1 | hz1
  · have hae' : a = e := by rw [hae, hz1, mul_one]
    refine ⟨e, heE, ?_, by rw [hae']⟩
    rw [← hae']
    exact ha2
  · have hae' : a = e * x := by rw [hae, hz1]
    have he1 : e ≠ 1 := by
      intro h
      apply hax
      rw [hae', h, one_mul]
    refine ⟨e, heE, orderOf_eq_prime (by rw [sq]; exact hEsq e heE) he1, ?_⟩
    rw [hae']
    exact inf_centralizer_mul_eq hKx

end Decomp

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_pumpup {K : Subgroup G} {a e f : G} {J H : Subgroup G}
    (hKC : KCentIn (↥K ⧸ pPrimeCore 2 ↥K)) (heK : e ∈ K) (he2 : orderOf e = 2)
    (hWe : K ⊓ centralizer ({a} : Set G) = K ⊓ centralizer ({e} : Set G))
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hH : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H) (hHJ : H ≤ J)
    (hfK : f ∈ K) (hfa : f ∈ centralizer ({a} : Set G)) : f ∈ normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hfn
  set c := (MulAut.conj f).toMonoidHom with hc
  set J' : Subgroup G := J.map c with hJ'def
  set H' : Subgroup G := H.map c with hH'def
  have hfW : f ∈ K ⊓ centralizer ({a} : Set G) := ⟨hfK, hfa⟩
  have hH' : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H' := FalseCtxS45Comp.isPCompIn_conj hH hfW
  have hJ'c : IsPCompIn 2 (centralizer ({a} : Set G)) J' := FalseCtxS45Comp.isPCompIn_conj hJ hfa
  have hne : J ≠ J' := fun h => hfn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcs : J' ≤ centralizerSection J (pPrimeCoreOf 2 J) := FalseCtxS45Comp.le_cSec_of_ne hJ hJ'c hne
  have hH'J' : H' ≤ J' := Subgroup.map_mono hHJ
  have hcomm : ⁅H, H'⁆ ≤ pPrimeCoreOf 2 J :=
    Subgroup.commutator_le.mpr fun h hh h' hh' => (hcs (hH'J' hh')).2.2 h (hHJ hh)
  set N : Subgroup ↥K := pPrimeCore 2 ↥K with hN
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set ψ : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N with hψ
  have hHK : H ≤ K := hH.1.trans inf_le_left
  have hH'K : H' ≤ K := hH'.1.trans inf_le_left
  have hordK : orderOf (⟨e, heK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact he2
  have hord : orderOf (ψ ⟨e, heK⟩) = 2 := UnbalancedLayer.orderOf_mk_eq_two hNodd hordK
  obtain ⟨hS, hSn, -⟩ := hKC _ hord
  have hHe : IsPCompIn 2 (K ⊓ centralizer ({e} : Set G)) H := by rw [← hWe]; exact hH
  have hH'e : IsPCompIn 2 (K ⊓ centralizer ({e} : Set G)) H' := by rw [← hWe]; exact hH'
  have h1 := FalseCtxS45K.map_eq_derived heK he2 hS hHe
  have h2 := FalseCtxS45K.map_eq_derived heK he2 hS hH'e
  set S : Subgroup (↥K ⧸ N) := ⁅FalseCtxS45K.cent K e heK, FalseCtxS45K.cent K e heK⁆ with hSdef
  set T : Subgroup ↥K := ⁅H.subgroupOf K, H'.subgroupOf K⁆ with hT
  have hTmap : T.map ψ = S := by
    rw [hT, Subgroup.map_commutator, h1, h2]
    exact commutator_self_of_simple_nonab hS hSn
  have hTodd : Odd (Nat.card T) := by
    have h3 : T.map K.subtype = ⁅H, H'⁆ := by
      rw [hT, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHK,
        Subgroup.map_subgroupOf_eq_of_le hH'K]
    have h4 : Nat.card T = Nat.card (T.map K.subtype) :=
      (Subgroup.card_map_of_injective K.subtype_injective).symm
    have h5 : Nat.card (T.map K.subtype) ∣ Nat.card (pPrimeCoreOf 2 J) :=
      Subgroup.card_dvd_of_le (h3 ▸ hcomm)
    rw [h4]
    exact (card_pPrimeCoreOf_odd J).of_dvd_nat h5
  have hS1 : ⁅S, S⁆ = S := commutator_self_of_simple_nonab hS hSn
  have hSne : S ≠ ⊥ := by
    have : Nontrivial ↥S := hS.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot S).mp this
  have : Finite ↥T := inferInstance
  exact false_of_odd_image (ψ.comp T.subtype) hTodd (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hTmap) hS1 hSne

end Normalizer

section Lift

theorem exists_pGroup_lift {M Q : Type} [Group M] [Finite M] [Group Q] (f : M →* Q) (T : Subgroup Q)
    (hT : IsPGroup 2 ↥T) (hTf : T ≤ f.range) : ∃ P : Subgroup M, IsPGroup 2 ↥P ∧ P.map f = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup M := T.comap f with hU
  set fU : ↥U →* ↥T := (f.comp U.subtype).codRestrict T (fun u => u.2) with hfU
  have hfUs : Function.Surjective fU := by
    rintro ⟨t, ht⟩
    obtain ⟨m, hm⟩ := hTf ht
    exact ⟨⟨m, show f m ∈ T by rw [hm]; exact ht⟩, Subtype.ext hm⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 ↥U) := inferInstance
  have h1 := (S₀.mapSurjective hfUs).is_maximal' (hT.to_subgroup ⊤) le_top
  rw [Sylow.coe_mapSurjective] at h1
  refine ⟨(S₀ : Subgroup ↥U).map U.subtype, S₀.isPGroup'.map _, ?_⟩
  have h2 : ((S₀ : Subgroup ↥U).map fU).map T.subtype = T := by
    rw [← h1, Subgroup.map_top, Subgroup.range_subtype] 
  rw [← h2, Subgroup.map_map, Subgroup.map_map]
  rfl

end Lift

section JBar

variable {G : Type} [Group G] [Finite G] {x a : G} {J H : Subgroup G}

noncomputable abbrev tbar (a x : G) (hxY : x ∈ centralizer ({a} : Set G)) :
    barQ ↥(centralizer ({a} : Set G)) :=
  barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩

@[expose] noncomputable def yAut (hJa : J ≤ centralizer ({a} : Set G)) (hxY : x ∈ centralizer ({a} : Set G))
    (hxJ : x ∈ normalizer (J : Set G)) : MulAut ↥(PumpCalc.bar a J) :=
  normalizerConjHom (PumpCalc.bar a J) ⟨tbar a x hxY, ObsPump.bar_mem_normalizer hJa hxY hxJ⟩

omit [Finite G] in
theorem coe_yAut (hJa : J ≤ centralizer ({a} : Set G)) (hxY : x ∈ centralizer ({a} : Set G))
    (hxJ : x ∈ normalizer (J : Set G)) (j : ↥(PumpCalc.bar a J)) :
    ((yAut hJa hxY hxJ j : ↥(PumpCalc.bar a J)) : barQ ↥(centralizer ({a} : Set G))) =
      tbar a x hxY * j * (tbar a x hxY)⁻¹ := rfl

omit [Finite G] in
theorem yAut_mul_self (hJa : J ≤ centralizer ({a} : Set G)) (hxY : x ∈ centralizer ({a} : Set G))
    (hxJ : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) :
    yAut hJa hxY hxJ * yAut hJa hxY hxJ = 1 := by
  have h1 : (⟨tbar a x hxY, ObsPump.bar_mem_normalizer hJa hxY hxJ⟩ :
      ↥(normalizer ((PumpCalc.bar a J : Subgroup _) : Set _))) *
      ⟨tbar a x hxY, ObsPump.bar_mem_normalizer hJa hxY hxJ⟩ = 1 := by
    apply Subtype.ext
    show barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ * barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ = 1
    rw [← map_mul]
    have : (⟨x, hxY⟩ : ↥(centralizer ({a} : Set G))) * ⟨x, hxY⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  unfold yAut
  rw [← map_mul, h1, map_one]

theorem yAut_ne_one (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hxY : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G))
    (hnc : x ∉ centralizerSection J (pPrimeCoreOf 2 J)) : yAut hJ.1 hxY hxJ ≠ 1 := by
  intro h
  apply hnc
  refine ObsPump.mem_cSec_of_bar_comm hJ hxY fun l hl => ?_
  have h1 := congrArg (fun σ : MulAut ↥(PumpCalc.bar a J) =>
    ((σ ⟨l, hl⟩ : ↥(PumpCalc.bar a J)) : barQ ↥(centralizer ({a} : Set G)))) h
  simp only [MulAut.one_apply, coe_yAut] at h1
  calc tbar a x hxY * l = (tbar a x hxY * l * (tbar a x hxY)⁻¹) * tbar a x hxY := by group
    _ = l * tbar a x hxY := by rw [h1]

theorem orderOf_yAut (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hxY : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1)
    (hnc : x ∉ centralizerSection J (pPrimeCoreOf 2 J)) : orderOf (yAut hJ.1 hxY hxJ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact yAut_mul_self hJ.1 hxY hxJ hx2) (yAut_ne_one hJ hxY hxJ hnc)

@[expose] noncomputable def piH (hHJ : H ≤ J) (hJa : J ≤ centralizer ({a} : Set G)) :
    ↥H →* ↥(PumpCalc.bar a J) :=
  ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion (hHJ.trans hJa))).codRestrict
    (PumpCalc.bar a J)
    (fun h => ⟨⟨h, (hHJ.trans hJa) h.2⟩, Subgroup.mem_subgroupOf.mpr (hHJ h.2), rfl⟩)

omit [Finite G] in
theorem coe_piH (hHJ : H ≤ J) (hJa : J ≤ centralizer ({a} : Set G)) (v : ↥H) :
    ((piH hHJ hJa v : ↥(PumpCalc.bar a J)) : barQ ↥(centralizer ({a} : Set G))) =
      barMk ↥(centralizer ({a} : Set G)) ⟨v, (hHJ.trans hJa) v.2⟩ := rfl

omit [Finite G] in
theorem yAut_piH (hHJ : H ≤ J) (hJa : J ≤ centralizer ({a} : Set G)) (hxY : x ∈ centralizer ({a} : Set G))
    (hxJ : x ∈ normalizer (J : Set G)) (hHx : ∀ h ∈ H, h * x = x * h) (v : ↥H) :
    yAut hJa hxY hxJ (piH hHJ hJa v) = piH hHJ hJa v := by
  apply Subtype.ext
  rw [coe_yAut, coe_piH]
  show barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ * barMk ↥(centralizer ({a} : Set G)) ⟨v, _⟩ *
    (barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩)⁻¹ = barMk ↥(centralizer ({a} : Set G)) ⟨v, _⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show x * (v : G) * x⁻¹ = v
  rw [← hHx v v.2]
  group

end JBar

section WeakL

variable {G : Type} [Group G] [Finite G] {a : G} {J H K : Subgroup G}

@[expose] noncomputable def psiH (hHK : H ≤ K) : ↥H →* ↥K ⧸ pPrimeCore 2 ↥K :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hHK)

theorem odd_card_ker_piH (hHJ : H ≤ J) (hJa : J ≤ centralizer ({a} : Set G)) :
    Odd (Nat.card (piH hHJ hJa).ker) := by
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({a} : Set G)))) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have h1 : (piH hHJ hJa).ker =
      ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion (hHJ.trans hJa))).ker :=
    MonoidHom.ker_codRestrict _ _ _
  have h2 : ¬ 2 ∣ Nat.card
      ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion (hHJ.trans hJa))).ker :=
    B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion (hHJ.trans hJa))
      (Subgroup.inclusion_injective _) (pPrimeCore 2 ↥(centralizer ({a} : Set G))) hNodd
  rw [h1]
  exact Nat.odd_iff.2 (by omega)

theorem odd_card_ker_psiH (hHK : H ≤ K) : Odd (Nat.card (psiH hHK).ker) := by
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have h2 : ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hHK)).ker :=
    B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hHK) (Subgroup.inclusion_injective _)
      (pPrimeCore 2 ↥K) hNodd
  exact Nat.odd_iff.2 (by unfold psiH; omega)

theorem ker_piH_le (hHK : H ≤ K) (hHJ : H ≤ J) (hJa : J ≤ centralizer ({a} : Set G))
    {S : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)} (hS : IsSimpleGroup ↥S) (hn : ∃ a b : ↥S, a * b ≠ b * a)
    (hmem : ∀ v : ↥H, psiH hHK v ∈ S) (hsurj : ∀ s ∈ S, ∃ v : ↥H, psiH hHK v = s) :
    (piH hHJ hJa).ker ≤ (psiH hHK).ker := by
  classical
  intro v hv
  set f : ↥H →* ↥S := (psiH hHK).codRestrict S hmem with hf
  have hfs : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨w, hw⟩ := hsurj s hs
    exact ⟨w, Subtype.ext hw⟩
  have hnorm : (((piH hHJ hJa).ker).map f).Normal := (MonoidHom.normal_ker (piH hHJ hJa)).map f hfs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((piH hHJ hJa).ker).map f) with h | h
  · have h1 : f v ∈ ((piH hHJ hJa).ker).map f := ⟨v, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    refine false_of_odd_surjection hS hn (f.comp (piH hHJ hJa).ker.subtype) ?_
      (odd_card_ker_piH hHJ hJa)
    intro s
    have h1 : s ∈ ((piH hHJ hJa).ker).map f := h ▸ Subgroup.mem_top s
    obtain ⟨w, hw, hws⟩ := h1
    exact ⟨⟨w, hw⟩, hws⟩

end WeakL

section Abelian

variable {G : Type} [Group G] [Finite G] {x a : G} {J : Subgroup G}

theorem comm_of_fixed (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) (hx : orderOf x = 2)
    (hxY : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G))
    (hab : ∀ P : Sylow 2 ↥(centralizer ({x} : Set G)),
      IsMulCommutative ↥(P : Subgroup ↥(centralizer ({x} : Set G))))
    (T : Subgroup ↥(PumpCalc.bar a J)) (hT : IsPGroup 2 ↥T)
    (hfix : ∀ t ∈ T, yAut hJ.1 hxY hxJ t = t) : ∀ s ∈ T, ∀ r ∈ T, s * r = r * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := centralizer ({a} : Set G) with hY
  set R : Subgroup ↥Y := pPrimeCore 2 ↥Y with hR
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set M₀ : Subgroup G := centralizer ({x} : Set G) ⊓ Y with hM₀
  have hM₀Y : M₀ ≤ Y := inf_le_right
  have hM₀x : M₀ ≤ centralizer ({x} : Set G) := inf_le_left
  set f : ↥M₀ →* barQ ↥Y := (barMk ↥Y).comp (Subgroup.inclusion hM₀Y) with hf
  set T' : Subgroup (barQ ↥Y) := T.map (PumpCalc.bar a J).subtype with hT'
  have hT'p : IsPGroup 2 ↥T' := hT.map _
  have hordY : orderOf (⟨x, hxY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hT'f : T' ≤ f.range := by
    rintro _ ⟨τ, hτ, rfl⟩
    have hcomm0 : tbar a x hxY * (τ : barQ ↥Y) = (τ : barQ ↥Y) * tbar a x hxY := by
      have h1 := congrArg (fun σ : ↥(PumpCalc.bar a J) => (σ : barQ ↥Y)) (hfix τ hτ)
      simp only [coe_yAut] at h1
      calc tbar a x hxY * (τ : barQ ↥Y) = (tbar a x hxY * τ * (tbar a x hxY)⁻¹) * tbar a x hxY := by group
        _ = (τ : barQ ↥Y) * tbar a x hxY := by rw [h1]
    have hcomm : ∀ a' ∈ zpowers (⟨x, hxY⟩ : ↥Y),
        QuotientGroup.mk' R a' * (τ : barQ ↥Y) = (τ : barQ ↥Y) * QuotientGroup.mk' R a' := by
      intro a' ha'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (tbar a x hxY) (τ : barQ ↥Y) from hcomm0) k).eq
    obtain ⟨g, hgψ, hgc⟩ := B1.centralizer_quotient_of_pGroup R hRodd
      (B1.isPGroup_two_zpowers_of_orderOf hordY) hcomm
    have hge : (⟨x, hxY⟩ : ↥Y) * g = g * ⟨x, hxY⟩ := hgc _ (mem_zpowers _)
    have hgM : (g : G) ∈ M₀ := ⟨Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val hge).symm, g.2⟩
    exact ⟨⟨g, hgM⟩, hgψ⟩
  obtain ⟨P, hPp, hPmap⟩ := exists_pGroup_lift f T' hT'p hT'f
  set P' : Subgroup ↥(centralizer ({x} : Set G)) := P.map (Subgroup.inclusion hM₀x) with hP'
  have hP'p : IsPGroup 2 ↥P' := hPp.map _
  obtain ⟨S₂, hS₂⟩ := hP'p.exists_le_sylow
  have hcommP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
    intro p hp q hq
    have h1 : (Subgroup.inclusion hM₀x p) ∈ (S₂ : Subgroup ↥(centralizer ({x} : Set G))) :=
      hS₂ ⟨p, hp, rfl⟩
    have h2 : (Subgroup.inclusion hM₀x q) ∈ (S₂ : Subgroup ↥(centralizer ({x} : Set G))) :=
      hS₂ ⟨q, hq, rfl⟩
    have h3 := (hab S₂).is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩
    apply Subgroup.inclusion_injective hM₀x
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h3
  intro s hs r hr
  have hs' : (s : barQ ↥Y) ∈ T' := ⟨s, hs, rfl⟩
  have hr' : (r : barQ ↥Y) ∈ T' := ⟨r, hr, rfl⟩
  rw [← hPmap] at hs' hr'
  obtain ⟨p, hp, hps⟩ := hs'
  obtain ⟨q, hq, hqr⟩ := hr'
  apply Subtype.ext
  show (s : barQ ↥Y) * r = r * s
  rw [← hps, ← hqr, ← map_mul, ← map_mul, hcommP p hp q hq]

end Abelian

section Final

variable {G : Type} [Group G] [Finite G]

@[expose] def S45Table : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionalTwoRankLE (X ⧸ Subgroup.center X) 3 → IsQuasisimple X →
    IsPGroup 2 ↥(Subgroup.center X) → GHList (X ⧸ Subgroup.center X) → ∀ y : MulAut X, orderOf y = 2 →
    (∃ (V Q : Type) (_ : Group V) (_ : Group Q) (π : V →* X) (ψ : V →* Q),
      (∀ v, y (π v) = π v) ∧ π.ker ≤ ψ.ker ∧ Function.Surjective ψ ∧ Odd (Nat.card ψ.ker) ∧
        HasL2Model Q Odd) →
    (∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) →
    QShape4 (X ⧸ Subgroup.center X) ∨ QShape5 (X ⧸ Subgroup.center X)

theorem qshape_transport {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape4 A ∨ QShape5 A) :
    QShape4 B ∨ QShape5 B := by
  rcases h with ⟨f, hf⟩ | h5
  · exact Or.inl ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hf⟩
  · obtain ⟨e'⟩ := h5
    exact Or.inr ⟨e.symm.trans e'⟩

omit [Finite G] in
theorem exponent_two_image {Y : Type} [Group Y] {L T : Subgroup Y} (hT : ∀ t ∈ T, t * t = 1) :
    ∀ b ∈ (T.subgroupOf (normalizer (L : Set Y))).map (rhoL L), b * b = 1 := by
  rintro _ ⟨n, hn, rfl⟩
  rw [← map_mul]
  have : n * n = 1 := Subtype.ext (hT n (Subgroup.mem_subgroupOf.mp hn))
  rw [this, map_one]

omit [Finite G] in
theorem bar_sq_of_sq {T : Subgroup G} (hT : ∀ d ∈ T, d * d = 1) {a : G} :
    ∀ t ∈ PumpCalc.bar a T, t * t = 1 := by
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul]
  have : d * d = 1 := Subtype.ext (hT d (Subgroup.mem_subgroupOf.mp hd))
  rw [this, map_one]

variable {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem false_of_locBal (hc : Ctx21 G x K A a D J) (hAJ : A ≤ normalizer (J : Set G))
    (hLoc : ∀ B : Subgroup (MulAut (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J))),
      (∀ b ∈ B, b * b = 1) → IsLocBal32 (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) B) :
    False := by
  obtain ⟨-, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hc.src.2.1
  obtain ⟨hDA, hDel, hDrk⟩ := hc.obs.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  rcases hc.obs_cases with h2 | ⟨h1, -⟩ | ⟨-, e', he'A, he'N, -⟩
  · exact hc.obs.not_locBal32_rank2 h2 (hLoc _ (exponent_two_image (bar_sq_of_sq hDsq)))
  · exact hc.obs.not_locBal32_rank1 h1 hAJ (hLoc _ (exponent_two_image (bar_sq_of_sq hAsq)))
  · exact he'N (hAJ he'A)

end Final

section Branches

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem orderOf_psi {K : Subgroup G} {e : G} (heK : e ∈ K) (he2 : orderOf e = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨e, heK⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  exact UnbalancedLayer.orderOf_mk_eq_two hNodd (by rw [Subgroup.orderOf_mk]; exact he2)

theorem qshape_of_eq (hc : Ctx21 G x K A a D J) (hax : a = x)
    (hcen : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g : ↥K ⧸ pPrimeCore 2 ↥K, g * z = z * g) → z = 1)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K))
    (hnotK : ¬ K ≤ centralizerSection J (pPrimeCoreOf 2 J)) :
    A ≤ normalizer (J : Set G) ∧
      (QShape4 (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) ∨
        QShape5 (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J))) := by
  classical
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hKx : K ≤ centralizer ({x} : Set G) := hK.1
  have hK' : IsPCompIn 2 (centralizer ({a} : Set G)) K := by rw [hax]; exact hK
  have hJK : J = K := FalseCtxS45Comp.eq_of_not_le_cSec hc.obs.comp hK' hnotK
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := exists_E hc hcen
  have hxN : x ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hKx hg)
      have : x * g * x⁻¹ = g := by rw [← hgx]; group
      rw [this]
      exact hg
    · intro hg
      have hyc : (x * g * x⁻¹) * x = x * (x * g * x⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.1 (hKx hg)
      have h4 : x * g = x * (x * g * x⁻¹) := by rw [← hyc]; group
      have h5 : g = x * g * x⁻¹ := mul_left_cancel h4
      rw [h5]
      exact hg
  have hAK : A ≤ normalizer (K : Set G) := by
    rw [hAE]
    exact sup_le (fun f hf => Subgroup.le_normalizer (hEK hf)) (Subgroup.zpowers_le.2 hxN)
  subst hJK
  refine ⟨hAK, ?_⟩
  obtain ⟨e₁⟩ := PumpCalc.kBar_equiv_bar hK'
  have hZ : Subgroup.center ↥(PumpCalc.bar a J) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply e₁.symm.injective
    rw [map_one]
    apply hcen
    intro g
    apply e₁.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz (e₁ g)
  let e₂ : ↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J) ≃* ↥(PumpCalc.bar a J) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact qshape_transport e₂.symm (qshape_transport e₁ hP)

end Branches

section Assembly

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

omit [Finite G] in
theorem le_pumpUp_self {H : Subgroup G} {a : G} (hPself : pLayerOf 2 H = H) (hH : H ≤ centralizer ({a} : Set G)) :
    H ≤ pumpUp 2 H a := by
  intro h hh
  have h1 : h ∈ pLayerOf 2 (H ⊓ centralizer ({a} : Set G)) := by
    rw [inf_eq_left.2 hH, hPself]; exact hh
  refine Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem (one_mem _) ?_)
  exact ⟨h, h1, by simp⟩

end Assembly

end CFSG.GH74.Generic.BProg.B3.FalseCtxS45
