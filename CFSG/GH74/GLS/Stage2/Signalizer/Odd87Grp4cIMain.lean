module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIG
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cILift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cICent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIOrd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIAut
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage1.Main CFSG.ABGLocalTools
open scoped commutatorElement

section Transfer

theorem isElementaryAbelian_two_of_forall {G : Type} [Group G] {A : Subgroup G}
    (h₁ : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h₂ : ∀ a ∈ A, a * a = 1) :
    IsElementaryAbelian 2 ↥A := CFSG.IsElementaryAbelian.two_of_forall_mul_self h₁ h₂

theorem map_inf_centralizer_subtype {G : Type} [Group G] (H₀ : Subgroup G) (S T : Subgroup ↥H₀) :
    (S.map H₀.subtype) ⊓ centralizer ((T.map H₀.subtype : Subgroup G) : Set G) =
      (S ⊓ centralizer (T : Set ↥H₀)).map H₀.subtype := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgS, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨s, hs, rfl⟩ := hgS
    refine ⟨s, Subgroup.mem_inf.mpr ⟨hs, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC (t : G) ⟨t, ht, rfl⟩)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.mp hs
    refine Subgroup.mem_inf.mpr ⟨⟨s, hsS, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hsC t ht)

theorem relIndex_centralizer_subtype {G : Type} [Group G] (H₀ : Subgroup G)
    (W' X' : Subgroup ↥H₀) :
    (centralizer ((W'.map H₀.subtype : Subgroup G) : Set G)).relIndex (X'.map H₀.subtype) =
      (centralizer (W' : Set ↥H₀)).relIndex X' := by
  have hXle : X'.map H₀.subtype ≤ H₀ := Subgroup.map_subtype_le _
  have h1 := Subgroup.relIndex_subgroupOf
    (H := centralizer ((W'.map H₀.subtype : Subgroup G) : Set G)) hXle
  rw [← h1]
  have e1 : (centralizer ((W'.map H₀.subtype : Subgroup G) : Set G)).subgroupOf H₀ =
      centralizer (W' : Set ↥H₀) := by
    ext u
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      exact Subtype.ext (h (w : G) ⟨w, hw, rfl⟩)
    · rintro h _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (h w hw)
  have e2 : (X'.map H₀.subtype).subgroupOf H₀ = X' :=
    Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective X'
  rw [e1, e2]

theorem isSylowOf_centralizer_subtype {G : Type} [Group G] [Finite G] (H₀ : Subgroup G)
    (W' U' : Subgroup ↥H₀)
    (h : IsSylowOf 2 (U'.map H₀.subtype)
      (centralizer ((W'.map H₀.subtype : Subgroup G) : Set G)))
    (hU : U' ≤ centralizer (W' : Set ↥H₀)) : IsSylowOf 2 U' (centralizer (W' : Set ↥H₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (centralizer (W' : Set ↥H₀)).map H₀.subtype ≤
      centralizer ((W'.map H₀.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc w hw)
  have h2 := h.of_le (Subgroup.map_mono hU) hle
  exact (isSylowOf_map_subtype_iff H₀).mp h2

theorem autOrd_dvd_natCard_mulAut {A : Type} [Group A] (W : Subgroup A) :
    AutOrd (⊤ : Subgroup A) W ∣ Nat.card (MulAut ↥W) := by
  have hker := actOnKHom_ker W (normalizer (W : Set A)) le_rfl
  have h1 := Subgroup.index_ker (actOnKHom W (normalizer (W : Set A)) le_rfl)
  rw [hker] at h1
  have h2 : Nat.card (actOnKHom W (normalizer (W : Set A)) le_rfl).range ∣ Nat.card (MulAut ↥W) :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : AutOrd (⊤ : Subgroup A) W =
      ((centralizer (W : Set A)).subgroupOf (normalizer (W : Set A))).index := by
    unfold AutOrd
    rw [inf_top_eq, inf_top_eq]
    rfl
  rw [h3, h1]
  exact h2

end Transfer

section Main

theorem prop4_1c_i_of (hL29 : Lemma29First) : Prop4_1c_i := by
  intro G _ _ z k S hctx H₀ H₁ _ hz p X hsig W hW hXW hzW hcomm hne h4
  have hp : p.Prime := hsig.A.prime
  have hodd : p ≠ 2 := hsig.A.odd
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hctx.central.1] at h
  have hz2 : zSec z H₀ hz H₁ * zSec z H₀ hz H₁ = 1 := by
    rw [zSec, ← QuotientGroup.mk_mul]
    have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥H₀) = 1 := Subtype.ext (by simpa [pow_two] using hzord)
    rw [this]
    rfl
  have hcen : zSec z H₀ hz H₁ ∈ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsetup : Setup412 p W X (zSec z H₀ hz H₁) :=
    { prime := hp
      odd := hodd
      W2 := hW
      Xp := hsig.A.pgroup
      XW := hXW
      zW := hzW
      z2 := hz2
      zX := hsig.A.inv _ (Subgroup.mem_top _) hcen
      comm := hsig.A.comm
      Cz := fun c _ hc => hsig.A.inv c (Subgroup.mem_top _)
        (Subgroup.mem_centralizer_singleton_iff.mpr hc) }
  have hP1 : Part1 p W X (zSec z H₀ hz H₁) := part1_of_setup hsetup hcomm hne
  have hC : Core412 W X (zSec z H₀ hz H₁) := core412_of_part1 hP1
  set Z : Subgroup (Sec H₀ H₁) := W ⊓ centralizer (W : Set (Sec H₀ H₁)) with hZ
  have hZ4 : 4 ≤ Nat.card ↥Z := h4.trans (Subgroup.card_le_of_le inf_le_left)
  have hZ2 : IsPGroup 2 ↥Z := hW.to_le inf_le_left
  obtain ⟨i, hi⟩ := hZ2.exists_card_eq
  have h4Z : 2 ^ 2 ∣ Nat.card ↥Z := by
    rw [hi]
    apply pow_dvd_pow
    by_contra hlt
    push Not at hlt
    have hi1 : i ≤ 1 := by omega
    interval_cases i
    · rw [pow_zero] at hi
      omega
    · rw [pow_one] at hi
      omega
  obtain ⟨U₀', hU₀'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4Z
  set U₀ : Subgroup (Sec H₀ H₁) := U₀'.map Z.subtype with hU₀def
  have hU₀card : Nat.card ↥U₀ = 4 := by
    rw [hU₀def, Subgroup.card_map_of_injective Z.subtype_injective, hU₀']
    norm_num
  have hU₀Z : U₀ ≤ Z := Subgroup.map_subtype_le _
  have hU₀W : U₀ ≤ W := hU₀Z.trans inf_le_left
  have hU₀c : U₀ ≤ centralizer (W : Set (Sec H₀ H₁)) := hU₀Z.trans inf_le_right
  have hXU₀ : X ≤ centralizer (U₀ : Set (Sec H₀ H₁)) :=
    hC.X_cent_Z.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU₀Z))
  have hU₀sq : ∀ g ∈ U₀, g * g = 1 := fun g hg => hC.Z_exp2 g (hU₀Z hg)
  obtain ⟨W', X', U', hW'2, hX'p, hW'map, hX'map, hU'map, hW'N, hX'N, hcomm', hU'W', hU'c, hXU',
    hU'sq, hU'card, hZfix', hZder'⟩ :=
    exists_lift_l34 H₁ hsig.odd hodd W X U₀ hW hsig.A.pgroup hXW hcomm hU₀W hU₀c hXU₀ hU₀sq
      hC.Z_eq_fix hC.Z_eq_derived
  set π := QuotientGroup.mk' H₁ with hπ
  obtain ⟨u, huW, v, hvW, hu4, hv4, huv⟩ := exists_noncomm_order_four hP1 hC
  have hliftW : ∀ a ∈ W, ∃ a' ∈ W', π a' = a := by
    intro a ha
    rw [← hW'map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a', ha', rfl⟩
  obtain ⟨u', hu'W', rfl⟩ := hliftW u huW
  obtain ⟨v', hv'W', rfl⟩ := hliftW v hvW
  have hu'4 : orderOf u' = 4 := orderOf_eq_four_of_map H₁ hW'N hu'W' hu4
  have hv'4 : orderOf v' = 4 := orderOf_eq_four_of_map H₁ hW'N hv'W' hv4
  have hu'v' : u' * v' ≠ v' * u' := fun h => huv (by rw [← map_mul, ← map_mul, h])
  set WG : Subgroup G := W'.map H₀.subtype with hWG
  set XG : Subgroup G := X'.map H₀.subtype with hXG
  set UG : Subgroup G := U'.map H₀.subtype with hUG
  have hWG2 : IsPGroup 2 ↥WG := hW'2.map H₀.subtype
  have hXGp : IsPGroup p ↥XG := hX'p.map H₀.subtype
  have hXGW : XG ≤ normalizer (WG : Set G) :=
    (Subgroup.map_mono hX'N).trans (Subgroup.le_normalizer_map _)
  have hcommG : ⁅WG, XG⁆ = WG := by rw [hWG, hXG, ← Subgroup.map_commutator, hcomm']
  have hneG : WG ≠ ⊥ := by
    intro hb
    apply hne
    have : W' = ⊥ := (Subgroup.map_eq_bot_iff_of_injective W' H₀.subtype_injective).mp hb
    rw [← hW'map, this, Subgroup.map_bot]
  have hUWG : UG ≤ WG := Subgroup.map_mono hU'W'
  have hUcG : UG ≤ centralizer (WG : Set G) := by
    rintro _ ⟨u₁, hu₁, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w₁, hw₁, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hU'c hu₁) w₁ hw₁)
  have hWCG : WG ≤ centralizer (UG : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hUcG hu) w hw).symm
  have hXUG : XG ≤ centralizer (UG : Set G) := by
    rintro _ ⟨x₁, hx₁, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u₁, hu₁, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hXU' hx₁) u₁ hu₁)
  have hZfixG : WG ⊓ centralizer (WG : Set G) = WG ⊓ centralizer (XG : Set G) := by
    rw [hWG, hXG, map_inf_centralizer_subtype, map_inf_centralizer_subtype, hZfix']
  have hZderG : WG ⊓ centralizer (WG : Set G) = ⁅WG, WG⁆ := by
    rw [hWG, map_inf_centralizer_subtype, hZder', Subgroup.map_commutator]
  have hUG4 : IVK.IsFourSubgroup UG := by
    refine ⟨isElementaryAbelian_two_of_forall ?_ ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hU'c hb) a (hU'W' ha))
    · rintro _ ⟨a, ha, rfl⟩
      have := congrArg Subtype.val (hU'sq a ha)
      simpa using this
    · rw [hUG, Subgroup.card_map_of_injective H₀.subtype_injective, hU'card, hU₀card]
  obtain ⟨hk, h29b⟩ := lemma29_mcl_ly (hL29 G z k S hctx) hp hodd hUG4 hWG2 hXGp hcommG hneG hWCG
    hXUG (u' : G) (v' : G) ⟨u', hu'W', rfl⟩ ⟨v', hv'W', rfl⟩
    ((Subgroup.orderOf_coe u').trans hu'4) ((Subgroup.orderOf_coe v').trans hv'4)
    (fun h => hu'v' (Subtype.ext h))
  obtain ⟨hp3, hL34G, hrelG, hZUG, hsylG⟩ := l34_of_lemma29b hp hodd hUG4 hWG2 hXGp hXGW hcommG
    hneG hUWG hUcG hXUG hZfixG hZderG h29b
  have hrelA : (centralizer (W : Set (Sec H₀ H₁))).relIndex X = 3 := by
    have h1 := relIndex_centralizer_subtype H₀ W' X'
    have h2 := relIndex_centralizer_map H₁ hW'N hX'N
    rw [hW'map, hX'map] at h2
    rw [h2, ← h1]
    exact hrelG
  have hZW' : W' ⊓ centralizer (W' : Set ↥H₀) = U' := by
    have h1 := hZUG
    rw [hWG, hUG, map_inf_centralizer_subtype] at h1
    exact Subgroup.map_injective H₀.subtype_injective h1
  have hzOfW : zOf W = U₀ := by
    show W ⊓ centralizer (W : Set (Sec H₀ H₁)) = U₀
    rw [← hW'map, ← map_inf_centralizer_eq H₁ hW'N Subgroup.le_normalizer, hZW', hU'map]
  have hsylA : IsSylowOf 2 (zOf W) (centralizer (W : Set (Sec H₀ H₁))) := by
    have h2 : IsSylowOf 2 U' (centralizer (W' : Set ↥H₀)) :=
      isSylowOf_centralizer_subtype H₀ W' U' hsylG hU'c
    have h3 := isSylowOf_map_mk_of_odd H₁ hsig.odd h2
    rw [hU'map] at h3
    rw [hzOfW, ← hW'map, centralizer_map_two_lift H₁ hsig.odd W' hW'2 hW'N]
    exact h3
  have hL34W : IsL34Two ↥W := by
    obtain ⟨eG⟩ := hL34G
    obtain ⟨e₂⟩ := nonempty_equiv_map_of_inf_eq_bot H₁ hW'N
    let e₃ : ↥(W'.map π) ≃* ↥W := MulEquiv.subgroupCongr hW'map
    let e₄ : ↥W' ≃* ↥WG := Subgroup.equivMapOfInjective W' H₀.subtype H₀.subtype_injective
    exact ⟨(e₂.trans e₃).symm.trans (e₄.trans eG)⟩
  have hodd9 : oddPart (AutOrd (⊤ : Subgroup (Sec H₀ H₁)) W) ∣ 9 := by
    have h1 := autOrd_dvd_natCard_mulAut W
    have h2 := Nat.ordCompl_dvd_ordCompl_of_dvd h1 2
    exact h2.trans (aut34Odd ↥W hL34W)
  exact ⟨hk, hL34W, hrelA, hsylA, hodd9⟩

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
