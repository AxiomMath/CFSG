module

public import CFSG.ClassicalInvolution.SmallCases.NDB1Shape
public import CFSG.ClassicalInvolution.SmallCases.NDB1Lift
public import CFSG.ClassicalInvolution.Asc77.WP3FrameData
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec
public import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
public import CFSG.ClassicalInvolution.Asc77.AscFusionS14
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.SmallCases.DSplitEdge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Axis

variable {G : Type} [Group G]

theorem comm_sq {a b : G} (h : a * b = b * a) : a * a * b = b * (a * a) := by
  rw [mul_assoc, h, ← mul_assoc, h, mul_assoc]

variable [Finite G]

theorem comm_of_mem_map {z : G} {P : Subgroup ↥(Subgroup.centralizer ({z} : Set G))}
    (hP : IsPGroup 2 P) {a b : G} (ha : a ∈ P.map (Subgroup.centralizer ({z} : Set G)).subtype)
    (hb : b ∈ P.map (Subgroup.centralizer ({z} : Set G)).subtype)
    (h : ∀ (ha' : a ∈ Subgroup.centralizer ({z} : Set G))
      (hb' : b ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨a, ha'⟩ * oddQuotMk z ⟨b, hb'⟩ = oddQuotMk z ⟨b, hb'⟩ * oddQuotMk z ⟨a, ha'⟩) :
    a * b = b * a := by
  obtain ⟨a', ha'P, rfl⟩ := ha
  obtain ⟨b', hb'P, rfl⟩ := hb
  have h2 : a' * b' = b' * a' :=
    Lift.injOn_of_isPGroup _ (OddCore.odd_card _) hP (P.mul_mem ha'P hb'P) (P.mul_mem hb'P ha'P)
      (by rw [map_mul, map_mul]; exact h a'.2 b'.2)
  exact congrArg Subtype.val h2

theorem eq_of_mem_map {z : G} {P : Subgroup ↥(Subgroup.centralizer ({z} : Set G))}
    (hP : IsPGroup 2 P) {a b : G} (ha : a ∈ P.map (Subgroup.centralizer ({z} : Set G)).subtype)
    (hb : b ∈ P.map (Subgroup.centralizer ({z} : Set G)).subtype)
    (h : ∀ (ha' : a ∈ Subgroup.centralizer ({z} : Set G))
      (hb' : b ∈ Subgroup.centralizer ({z} : Set G)), oddQuotMk z ⟨a, ha'⟩ = oddQuotMk z ⟨b, hb'⟩) :
    a = b := by
  obtain ⟨a', ha'P, rfl⟩ := ha
  obtain ⟨b', hb'P, rfl⟩ := hb
  exact congrArg Subtype.val
    (Lift.injOn_of_isPGroup _ (OddCore.odd_card _) hP ha'P hb'P (h a'.2 b'.2))

variable {p f : ℕ} [Fact p.Prime]

theorem exists_conj_sylow {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {z : G}
    (hz2 : z * z = 1) {M : Subgroup G} {u : G} (hM : M ∈ tqMembers Ω z)
    (hu : IsClassicalMember p f M u) {P : Subgroup ↥(Subgroup.centralizer ({z} : Set G))}
    (hP : IsPGroup 2 P) {V : Subgroup G} (hV : Asc77.IsSylow2In V (exactCore z M))
    (hVP : (V.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) ≤
      P.map (oddQuotMk z)) :
    ∃ g : G, ∃ hg : g ∈ Subgroup.centralizer ({z} : Set G), oddQuotMk z ⟨g, hg⟩ = 1 ∧
      ∃ S : Subgroup G, Asc77.IsSylow2In S (conjSub g M) ∧
        S ≤ P.map (Subgroup.centralizer ({z} : Set G)).subtype ∧
        ∀ s ∈ S, ∀ hs : s ∈ Subgroup.centralizer ({z} : Set G),
          oddQuotMk z ⟨s, hs⟩ ∈ modOdd z (exactCore z M) := by
  classical
  set N : Subgroup ↥(Subgroup.centralizer ({z} : Set G)) :=
    componentClassificationOddCore ↥(Subgroup.centralizer ({z} : Set G)) with hN
  have hNodd : Odd (Nat.card N) := OddCore.odd_card _
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz2
  have hπ : oddQuotMk z = QuotientGroup.mk' N := rfl
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans (exactCore_le_centralizer z M)
  set Vc : Subgroup ↥(Subgroup.centralizer ({z} : Set G)) :=
    V.subgroupOf (Subgroup.centralizer ({z} : Set G)) with hVc
  set Xc : Subgroup ↥(Subgroup.centralizer ({z} : Set G)) :=
    (exactCore z M).subgroupOf (Subgroup.centralizer ({z} : Set G)) with hXc
  have hVX : Vc ≤ Xc := fun x hx => hV.1 hx
  set S' : Subgroup ↥(Subgroup.centralizer ({z} : Set G)) :=
    P ⊓ (Vc.map (oddQuotMk z)).comap (oddQuotMk z) with hS'
  have hS'2 : IsPGroup 2 S' := hP.to_le inf_le_left
  have hS'X : S' ≤ Xc ⊔ N := by
    intro s hs
    have h1 : oddQuotMk z s ∈ Xc.map (oddQuotMk z) := Subgroup.map_mono hVX hs.2
    have h2 : s ∈ (Xc.map (oddQuotMk z)).comap (oddQuotMk z) := h1
    rwa [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h2
  obtain ⟨n, hnN, hS'n⟩ := Lift.exists_conj_le_of_le_sup hNodd hS'2 hS'X
  have hS'map : S'.map (oddQuotMk z) = Vc.map (oddQuotMk z) := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun y hy => ?_
    obtain ⟨s, hsP, rfl⟩ := hVP hy
    exact ⟨s, ⟨hsP, hy⟩, rfl⟩
  refine ⟨(n : G), n.2, (QuotientGroup.eq_one_iff n).mpr hnN,
    S'.map (Subgroup.centralizer ({z} : Set G)).subtype, ?_, Subgroup.map_mono inf_le_left, ?_⟩
  · have hS'G2 : IsPGroup 2 ↥(S'.map (Subgroup.centralizer ({z} : Set G)).subtype) := hS'2.map _
    have hle : S'.map (Subgroup.centralizer ({z} : Set G)).subtype ≤ conjSub (n : G) M := by
      rintro _ ⟨s, hs, rfl⟩
      have h1 := hS'n hs
      rw [mem_conjSub_iff] at h1
      rw [mem_conjSub_iff]
      have h2 : ((n⁻¹ * s * n : ↥(Subgroup.centralizer ({z} : Set G))) : G) ∈ exactCore z M :=
        Subgroup.mem_subgroupOf.mp h1
      exact exactCore_le_left z M (by simpa using h2)
    have hcard : Nat.card ↥(S'.map (Subgroup.centralizer ({z} : Set G)).subtype) = Nat.card V := by
      calc Nat.card ↥(S'.map (Subgroup.centralizer ({z} : Set G)).subtype) = Nat.card S' :=
            Subgroup.card_map_of_injective (Subgroup.centralizer ({z} : Set G)).subtype_injective
        _ = Nat.card ↥(S'.map (QuotientGroup.mk' N)) :=
            (Lift.natCard_map_of_isPGroup N hNodd hS'2).symm
        _ = Nat.card ↥(Vc.map (QuotientGroup.mk' N)) := by rw [← hπ, hS'map]
        _ = Nat.card Vc := Lift.natCard_map_of_isPGroup N hNodd hV.2.1.comap_subtype
        _ = Nat.card V := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv
    have hVM : Asc77.IsSylow2In V M :=
      ((ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hM.1 hM.2).mp hV).1
    have hcl := hu.conj (n : G)
    obtain ⟨W, hW, -⟩ := Asc77.IsSylow2In.exists_ge (P := conjSub (n : G) M) (T := ⊥)
      (IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])) bot_le
    have hWV := Disconnected.natCard_sylow_eq_of_classical hcl hu hW hVM
    exact hW.of_natCard_le hS'G2 hle (by rw [hWV, hcard])
  · rintro _ ⟨s, hs, rfl⟩ hsC
    exact Subgroup.map_mono hVX hs.2

omit [Finite G] in
theorem ne_of_conj_eq {w s z y : G} (hz1 : z ≠ 1) (hws : w * s = z * s * w)
    (hy : w * y = y * w) : s ≠ y := by
  rintro rfl
  apply hz1
  have h3 : s = z * s := mul_right_cancel (hy.symm.trans hws)
  exact (mul_right_cancel ((one_mul s).trans h3)).symm

theorem axis_elem_card {z z₂ z₃ t₁ t₂ t₃ w : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hz₂1 : z₂ ≠ 1) (hz₂2 : z₂ * z₂ = 1) (hz₃1 : z₃ ≠ 1) (hprod : z * z₂ = z₃)
    (hsq₁ : t₁ * t₁ = z) (hsq₂ : t₂ * t₂ = z₂) (hsq₃ : t₃ * t₃ = z₃)
    (c₁₂ : t₁ * t₂ = t₂ * t₁) (c₁₃ : t₁ * t₃ = t₃ * t₁) (c₂₃ : t₂ * t₃ = t₃ * t₂)
    (hw₁ : w * t₁ = t₁ * z * w) (hw₂ : w * t₂ = t₂ * w) (hw₃ : w * t₃ = t₃ * w)
    (hwz : w * z = z * w) :
    CFSG.Open.IsElemAbelian 2 (TypeCSetup.axis z z₂ t₁ t₂ t₃) ∧
      Nat.card (TypeCSetup.axis z z₂ t₁ t₂ t₃) = 8 := by
  have hzt₁ : Commute z t₁ := by
    rw [← hsq₁]
    exact (Commute.refl t₁).mul_left (Commute.refl t₁)
  have hzt₂ : Commute z t₂ := by
    rw [← hsq₁]
    exact comm_sq c₁₂
  have hzt₃ : Commute z t₃ := by
    rw [← hsq₁]
    exact comm_sq c₁₃
  have hz₂t₁ : Commute z₂ t₁ := by
    rw [← hsq₂]
    exact comm_sq c₁₂.symm
  have hz₂t₃ : Commute z₂ t₃ := by
    rw [← hsq₂]
    exact comm_sq c₂₃
  have hzz₂ : z * z₂ = z₂ * z := by
    rw [← hsq₂]
    exact (comm_sq hzt₂.eq.symm).symm
  have hwz₂ : w * z₂ = z₂ * w := by
    rw [← hsq₂]
    exact (comm_sq hw₂.symm).symm
  have hzs : Commute z (t₁ * t₂ * t₃) := (hzt₁.mul_right hzt₂).mul_right hzt₃
  have hz₂t₂ : Commute z₂ t₂ := by
    rw [← hsq₂]
    exact (Commute.refl t₂).mul_left (Commute.refl t₂)
  have hz₂s : Commute z₂ (t₁ * t₂ * t₃) := (hz₂t₁.mul_right hz₂t₂).mul_right hz₂t₃
  have h123 : Commute (t₁ * t₂) t₃ := Commute.mul_left c₁₃ c₂₃
  have hz₃2 : z₃ * z₃ = 1 := by
    rw [← hprod]
    calc z * z₂ * (z * z₂) = z * (z₂ * z) * z₂ := by group
      _ = z * (z * z₂) * z₂ := by rw [hzz₂]
      _ = (z * z) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz2, hz₂2, one_mul]
  have hss : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := by
    rw [← pow_two, h123.mul_pow, (show Commute t₁ t₂ from c₁₂).mul_pow, pow_two, pow_two,
      pow_two, hsq₁, hsq₂, hsq₃, hprod, hz₃2]
  have hws : w * (t₁ * t₂ * t₃) = z * (t₁ * t₂ * t₃) * w := by
    calc w * (t₁ * t₂ * t₃) = w * t₁ * t₂ * t₃ := by group
      _ = t₁ * z * w * t₂ * t₃ := by rw [hw₁]
      _ = t₁ * z * (w * t₂) * t₃ := by group
      _ = t₁ * z * (t₂ * w) * t₃ := by rw [hw₂]
      _ = t₁ * z * t₂ * (w * t₃) := by group
      _ = t₁ * z * t₂ * (t₃ * w) := by rw [hw₃]
      _ = z * t₁ * t₂ * t₃ * w := by rw [← hzt₁.eq]; group
      _ = z * (t₁ * t₂ * t₃) * w := by group
  have hz₂z : z₂ ≠ z := by
    intro h
    apply hz₃1
    rw [← hprod, h, hz2]
  have hs1 := ne_of_conj_eq hz1 hws (y := 1) (by rw [one_mul, mul_one])
  have hsz := ne_of_conj_eq hz1 hws hwz
  have hsz₂ := ne_of_conj_eq hz1 hws hwz₂
  have hszz₂ := ne_of_conj_eq hz1 hws (y := z * z₂) (by
    rw [← mul_assoc, hwz, mul_assoc, hwz₂, ← mul_assoc])
  refine ⟨Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_,
    ChainFrame.card_closure_triple_eq_eight hz2 hz₂2 hss hzz₂ hzs.eq hz₂s.eq hz1 hz₂1 hz₂z
      hs1 hsz hsz₂ hszz₂⟩
  · rintro x (rfl | rfl | rfl)
    exacts [hz2, hz₂2, hss]
  · rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl)
    exacts [rfl, hzz₂, hzs.eq, hzz₂.symm, rfl, hz₂s.eq, hzs.eq.symm, hz₂s.eq.symm, rfl]

end Axis


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem pspAxis_of_seed {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    {M₂ M₃ : Subgroup G} {u₂ u₃ : G} (hs : AxisSeed p f Ω K z M₂ M₃ u₂ u₃) :
    ∃ (K₂ K₃ : Subgroup G) (z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
      PSpAxis p f Ω K K₂ K₃ z z₂ z₃ t₁ t₂ t₃ w₁ w₂ := by
  classical
  have hzc := isCentralInvolution_of_isClassicalMember hz
  have hz2 : z * z = 1 := hzc.sq
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz2
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) :=
    RouteD.le_centralizer_of_isClassicalMember hz
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hNodd := OddCore.odd_card ↥(Subgroup.centralizer ({z} : Set G))
  have hbot : IsPGroup 2 (⊥ : Subgroup G) :=
    IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])
  obtain ⟨T₁, hT₁, -⟩ := Asc77.IsSylow2In.exists_ge (P := K) hbot bot_le
  obtain ⟨V₂, hV₂, -⟩ := Asc77.IsSylow2In.exists_ge (P := exactCore z M₂) hbot bot_le
  obtain ⟨V₃, hV₃, -⟩ := Asc77.IsSylow2In.exists_ge (P := exactCore z M₃) hbot bot_le
  set Tb := (T₁.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) with hTb
  set Vb₂ := (V₂.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) with hVb₂
  set Vb₃ := (V₃.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) with hVb₃
  have hTbK : Tb ≤ modOdd z K := Subgroup.map_mono fun x hx => hT₁.1 hx
  have hVb₂X : Vb₂ ≤ modOdd z (exactCore z M₂) := Subgroup.map_mono fun x hx => hV₂.1 hx
  have hVb₃X : Vb₃ ≤ modOdd z (exactCore z M₃) := Subgroup.map_mono fun x hx => hV₃.1 hx
  have hTb2 : IsPGroup 2 Tb := hT₁.2.1.comap_subtype.map _
  have hVb₂2 : IsPGroup 2 Vb₂ := hV₂.2.1.comap_subtype.map _
  have hVb₃2 : IsPGroup 2 Vb₃ := hV₃.2.1.comap_subtype.map _
  have c13 : ∀ a ∈ Tb, ∀ b ∈ Vb₃, a * b = b * a := fun a ha b hb =>
    hs.comm₁₃ a (hTbK ha) b (hVb₃X hb)
  have c23 : ∀ a ∈ Vb₂, ∀ b ∈ Vb₃, a * b = b * a := fun a ha b hb =>
    hs.comm₂₃ a (hVb₂X ha) b (hVb₃X hb)
  have hQ12 := Lift.isPGroup_sup_of_commute hTb2 hVb₂2 fun a ha b hb =>
    hs.comm₁₂ a (hTbK ha) b (hVb₂X hb)
  have c123 : ∀ a ∈ Tb ⊔ Vb₂, ∀ b ∈ Vb₃, a * b = b * a := by
    intro a ha b hb
    have hle : Tb ⊔ Vb₂ ≤ Subgroup.centralizer (Vb₃ : Set (OddQuot z)) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (c13 x hx y hy).symm)
        (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (c23 x hx y hy).symm)
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm
  have hQ := Lift.isPGroup_sup_of_commute hQ12 hVb₃2 c123
  obtain ⟨P, hP2, hTP, hPQ⟩ := Lift.exists_lift_ge _ hNodd hQ hT₁.2.1.comap_subtype
    (le_sup_left.trans le_sup_left)
  have hPQ' : P.map (oddQuotMk z) = Tb ⊔ Vb₂ ⊔ Vb₃ := hPQ
  have hV₂P : Vb₂ ≤ P.map (oddQuotMk z) := by
    rw [hPQ']
    exact le_sup_right.trans le_sup_left
  have hV₃P : Vb₃ ≤ P.map (oddQuotMk z) := by
    rw [hPQ']
    exact le_sup_right
  obtain ⟨g₂, hg₂C, hg₂1, S₂, hS₂, hS₂P, hS₂img⟩ :=
    Axis.exists_conj_sylow hΩ hz2 hs.tq₂ hs.cls₂ hP2 hV₂ hV₂P
  obtain ⟨g₃, hg₃C, hg₃1, S₃, hS₃, hS₃P, hS₃img⟩ :=
    Axis.exists_conj_sylow hΩ hz2 hs.tq₃ hs.cls₃ hP2 hV₃ hV₃P
  have hT₁P : T₁ ≤ P.map (Subgroup.centralizer ({z} : Set G)).subtype := fun a ha =>
    ⟨⟨a, hKC (hT₁.1 ha)⟩, hTP ha, rfl⟩
  have hcl₂ := hs.cls₂.conj g₂
  have hcl₃ := hs.cls₃.conj g₃
  obtain ⟨t₁, w₁, ht₁, hw₁, hsq₁, hinv₁⟩ := Lift.exists_sq_eq_of_isSylow2In hp hq hz hT₁
  obtain ⟨t₂, w₂, ht₂, hw₂, hsq₂, hinv₂⟩ := Lift.exists_sq_eq_of_isSylow2In hp hq hcl₂ hS₂
  obtain ⟨t₃, -, ht₃, -, hsq₃, -⟩ := Lift.exists_sq_eq_of_isSylow2In hp hq hcl₃ hS₃
  have d12 : ∀ a ∈ T₁, ∀ b ∈ S₂, a * b = b * a := fun a ha b hb =>
    Axis.comm_of_mem_map hP2 (hT₁P ha) (hS₂P hb) fun ha' hb' =>
      hs.comm₁₂ _ (oddQuotMk_mem_modOdd (hT₁.1 ha) ha') _ (hS₂img b hb hb')
  have d13 : ∀ a ∈ T₁, ∀ b ∈ S₃, a * b = b * a := fun a ha b hb =>
    Axis.comm_of_mem_map hP2 (hT₁P ha) (hS₃P hb) fun ha' hb' =>
      hs.comm₁₃ _ (oddQuotMk_mem_modOdd (hT₁.1 ha) ha') _ (hS₃img b hb hb')
  have d23 : ∀ a ∈ S₂, ∀ b ∈ S₃, a * b = b * a := fun a ha b hb =>
    Axis.comm_of_mem_map hP2 (hS₂P ha) (hS₃P hb) fun ha' hb' =>
      hs.comm₂₃ _ (hS₂img a ha ha') _ (hS₃img b hb hb')
  have hzT : z ∈ T₁ := Lift.mem_of_isSylow2In hp hq hz hT₁
  have hz₂S : g₂ * u₂ * g₂⁻¹ ∈ S₂ := Lift.mem_of_isSylow2In hp hq hcl₂ hS₂
  have hz₃S : g₃ * u₃ * g₃⁻¹ ∈ S₃ := Lift.mem_of_isSylow2In hp hq hcl₃ hS₃
  have hu₂C : u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    exactCore_le_centralizer z M₂ (mem_exactCore hs.cls₂ hc2 hs.tq₂.2)
  have hu₃C : u₃ ∈ Subgroup.centralizer ({z} : Set G) :=
    exactCore_le_centralizer z M₃ (mem_exactCore hs.cls₃ hc2 hs.tq₃.2)
  have hbar : ∀ (g u : G) (hg : g ∈ Subgroup.centralizer ({z} : Set G))
      (hu : u ∈ Subgroup.centralizer ({z} : Set G)), oddQuotMk z ⟨g, hg⟩ = 1 →
      ∀ h : g * u * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G),
        oddQuotMk z ⟨g * u * g⁻¹, h⟩ = oddQuotMk z ⟨u, hu⟩ := by
    intro g u hg hu hg1 h
    have e : (⟨g * u * g⁻¹, h⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨g, hg⟩ * ⟨u, hu⟩ * (⟨g, hg⟩ : ↥(Subgroup.centralizer ({z} : Set G)))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hg1, one_mul, inv_one, mul_one]
  have hprod : z * (g₂ * u₂ * g₂⁻¹) = g₃ * u₃ * g₃⁻¹ := by
    refine Axis.eq_of_mem_map hP2 (Subgroup.mul_mem _ (hT₁P hzT) (hS₂P hz₂S)) (hS₃P hz₃S)
      fun ha hb => ?_
    have h₂C : g₂ * u₂ * g₂⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₂C hu₂C) (Subgroup.inv_mem _ hg₂C)
    have e : (⟨z * (g₂ * u₂ * g₂⁻¹), ha⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨z, hzC⟩ * ⟨g₂ * u₂ * g₂⁻¹, h₂C⟩ := rfl
    rw [e, map_mul, hbar g₂ u₂ hg₂C hu₂C hg₂1, hbar g₃ u₃ hg₃C hu₃C hg₃1]
    exact hs.prod hzC hu₂C hu₃C
  have hc₂ := isCentralInvolution_of_isClassicalMember hcl₂
  have hc₃ := isCentralInvolution_of_isClassicalMember hcl₃
  have hzK : z ∈ trivialOnQuot K := mem_trivialOnQuot_of_le_centralizer hKC
  have tq₁₂ : g₂ * u₂ * g₂⁻¹ ∈ trivialOnQuot K :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ (isPGroup_zpowers_of_sq_eq_one hc₂.sq) hK).mpr
      ⟨T₁, hT₁, fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (d12 a ha _ hz₂S)⟩
  have tq₂₁ : z ∈ trivialOnQuot (conjSub g₂ M₂) :=
    (conjSub_mem_tqMembers hΩ.conjInvariant hg₂C hs.tq₂).2
  have tq₃₁ : z ∈ trivialOnQuot (conjSub g₃ M₃) :=
    (conjSub_mem_tqMembers hΩ.conjInvariant hg₃C hs.tq₃).2
  have hz₂K₂ : g₂ * u₂ * g₂⁻¹ ∈ trivialOnQuot (conjSub g₂ M₂) :=
    mem_trivialOnQuot_of_le_centralizer (RouteD.le_centralizer_of_isClassicalMember hcl₂)
  have hz₃K₃ : g₃ * u₃ * g₃⁻¹ ∈ trivialOnQuot (conjSub g₃ M₃) :=
    mem_trivialOnQuot_of_le_centralizer (RouteD.le_centralizer_of_isClassicalMember hcl₃)
  have hz₂eq : g₂ * u₂ * g₂⁻¹ = z * (g₃ * u₃ * g₃⁻¹) := by
    rw [← hprod, ← mul_assoc, hz2, one_mul]
  have hwz : w₁ * z = z * w₁ := Subgroup.mem_centralizer_singleton_iff.mp (hKC (hT₁.1 hw₁))
  obtain ⟨helem, hcard⟩ := Axis.axis_elem_card hzc.ne_one hz2 hc₂.ne_one hc₂.sq hc₃.ne_one hprod
    hsq₁ hsq₂ hsq₃ (d12 t₁ ht₁ t₂ ht₂) (d13 t₁ ht₁ t₃ ht₃) (d23 t₂ ht₂ t₃ ht₃) hinv₁
    (d12 w₁ hw₁ t₂ ht₂) (d13 w₁ hw₁ t₃ ht₃) hwz
  exact ⟨conjSub g₂ M₂, conjSub g₃ M₃, g₂ * u₂ * g₂⁻¹, g₃ * u₃ * g₃⁻¹, t₁, t₂, t₃, w₁, w₂,
    { mem₁ := hK
      mem₂ := hΩ.conjInvariant g₂ M₂ hs.tq₂.1
      mem₃ := hΩ.conjInvariant g₃ M₃ hs.tq₃.1
      cls₁ := hz
      cls₂ := hcl₂
      cls₃ := hcl₃
      prod := hprod
      tq₁₂ := tq₁₂
      tq₁₃ := hprod ▸ Subgroup.mul_mem _ hzK tq₁₂
      tq₂₁ := tq₂₁
      tq₂₃ := hprod ▸ Subgroup.mul_mem _ tq₂₁ hz₂K₂
      tq₃₁ := tq₃₁
      tq₃₂ := hz₂eq ▸ Subgroup.mul_mem _ tq₃₁ hz₃K₃
      ht₁ := hT₁.1 ht₁
      ht₂ := hS₂.1 ht₂
      ht₃ := hS₃.1 ht₃
      sq₁ := hsq₁
      sq₂ := hsq₂
      sq₃ := hsq₃
      ct₁₂ := d12 t₁ ht₁ t₂ ht₂
      ct₁₃ := d13 t₁ ht₁ t₃ ht₃
      ct₂₃ := d23 t₂ ht₂ t₃ ht₃
      hw₁ := hT₁.1 hw₁
      hw₂ := hS₂.1 hw₂
      inv₁ := hinv₁
      inv₂ := hinv₂
      cw₁₂ := d12 w₁ hw₁ t₂ ht₂
      cw₁₃ := d13 w₁ hw₁ t₃ ht₃
      cw₂₁ := (d12 t₁ ht₁ w₂ hw₂).symm
      cw₂₃ := d23 w₂ hw₂ t₃ ht₃
      elem := helem
      card := hcard }⟩

variable (p f)

theorem axisExistsCore : AxisExistsCore p f := by
  intro G _ _ _ K z hS hpsp
  have hΩ : HypOmegaMod p f (𝒞 K) :=
    Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f) G hS.nonabelian
      hS.odd hS.five K z hS.member hS.below
  have hK : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  obtain ⟨M₂, M₃, u₂, u₃, hseed⟩ :=
    exists_axisSeed hΩ hS.odd hS.five hK hS.member (hpsp K hK z hS.member)
  exact pspAxis_of_seed hΩ hS.odd hS.five hK hS.member hseed

theorem axisExists : AxisExists p f :=
  AxisExists.of_core p f (axisExistsCore p f)

end CFSG.ClassicalInvolution.NDB
