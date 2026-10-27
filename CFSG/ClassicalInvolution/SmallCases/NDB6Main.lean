module

public import CFSG.ClassicalInvolution.SmallCases.NDB3Main
public import CFSG.ClassicalInvolution.Generic.TypeCSetup2P1
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Generic.TypeCSetup

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace P1

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem closure_pair_conj (g a b : G) :
    Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) =
      conjSub g (Subgroup.closure ({a, b} : Set G)) := by
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  rfl

omit [Finite G] [IsSimpleGroup G] in
theorem le_centralizer_pair {L : Subgroup G} {z₁ z₂ : G} (hL : IsClassicalMember p f L z₁)
    (h₂ : ∀ x ∈ L, z₂ * x = x * z₂) :
    L ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  rintro x (rfl | hx)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember hL hk)).symm
  · rw [Set.mem_singleton_iff.mp hx]
    exact h₂ k hk

end P1

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem alphaCore_pair_axis {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G}
    (hA : PSpAxis p f Ω K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂) (hsh : PSpShape p f Ω z₁)
    (hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥) {L : Subgroup G}
    (hL : L ∈ centMembers Ω z₁) {w : G} (hw : IsClassicalMember p f L w) (hwz : w ≠ z₁) :
    alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥ := by
  have hLtq : L ∈ tqMembers Ω z₁ := ⟨hL.1, mem_trivialOnQuot_of_le_centralizer hL.2⟩
  have hlink := link_axis_vertex (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) hΩ hp hq hA.mem₁ hA.cls₁ hsh
    ⟨hA.mem₂, hA.tq₂₁⟩ hA.cls₂ hA.cls₃ hA.prod (S := {K₁, K₂}) (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K', hK', z', -, hz', h, hh, hwh⟩ :=
    hlink L hL.1 w hw (Or.inl (mem_trivialOnQuot_iff_actsTrivOnQuot.mp hLtq.2))
  have hhz : h * z₁ * h⁻¹ = z₁ :=
    conj_eq_of_mem_centralizer_singleton (exactLayer_le_centralizer Ω z₁ hh)
  have hu := fun {M : Subgroup G} {b : G} (hb : IsClassicalMember p f M b) =>
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hb
  rcases hK' with rfl | hK'
  · have h1 : z' = z₁ := (hu hz').eq (hu hA.cls₁)
    exact absurd (hwh.trans (by rw [h1, hhz])) hwz
  · rw [Set.mem_singleton_iff] at hK'
    subst hK'
    have h2 : z' = z₂ := (hu hz').eq (hu hA.cls₂)
    subst h2
    have e : Subgroup.closure ({z₁, w} : Set G) =
        conjSub h (Subgroup.closure ({z₁, z'} : Set G)) := by
      rw [← P1.closure_pair_conj, hhz, ← hwh]
    rw [e]
    exact alphaCore_conjSub_eq_bot hα h

end Pair

section Member

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem member_commutes_oddCoreIn_axis (hnab : ∃ x y : G, x * y ≠ y * x) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hBelow : CITBelowU p f (Nat.card G)) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hΩ : HypOmegaMod p f (𝒞 K)) {K₁ K₂ K₃ : Subgroup G}
    {z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G} (hA : PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂)
    (hsh : PSpShape p f (𝒞 K) z₁) (hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥)
    {L : Subgroup G} (hL : L ∈ centMembers (𝒞 K) z₁) :
    ∀ n ∈ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)), ∀ l ∈ L, n * l = l * n := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΩc : InClass p f (𝒞 K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩc hBelow
  have hz₁c := isCentralInvolution_of_isClassicalMember hA.cls₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hA.cls₂
  have hK₁F := P1.le_centralizer_pair hA.cls₁
    (Theorem5.mem_centralizer_of_alphaCore_eq_bot hA.cls₁ hA.tq₁₂ hz₂c.sq hz₁c.ne_one hα)
  have hpair : Subgroup.closure ({z₁, z₂} : Set G) ≤ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.mpr
      (Set.mem_insert _ _)))
  have hB : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({z₁, z₂} : Set G)) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA.elem hpair
  obtain ⟨w, hw⟩ := hΩc.classical L hL.1
  by_cases hwz : w = z₁
  · obtain ⟨a, ha⟩ := hL.1
    obtain ⟨b, hb⟩ := hA.mem₁
    have ha' : conjSub a K = L := ha
    have hb' : conjSub b K = K₁ := hb
    set g : G := a * b⁻¹ with hg
    have hLg : L = conjSub g K₁ := by
      rw [← hb', ← ha', ← conjSub_mul, hg]
      group
    have hw' : IsCentralInvolution (conjSub g K₁) w := hLg ▸ hw.isCentralInvolution
    have hwg : w = g * z₁ * g⁻¹ := (hA.cls₁.conj g).eq_of_isCentralInvolution hp hf hw'
    have hgx : g * z₁ * g⁻¹ = z₁ := hwg.symm.trans hwz
    have hα' := alphaCore_conjSub_eq_bot hα g
    have hΔ : deltaCore (conjSub g (Subgroup.closure ({z₁, z₂} : Set G))) = ⊥ := by
      have hle := deltaCore_le_alphaCore (F := conjSub g (Subgroup.closure ({z₁, z₂} : Set G)))
      rw [hα'] at hle
      exact le_bot_iff.mp hle
    have hxF : z₁ ∈ conjSub g (Subgroup.closure ({z₁, z₂} : Set G)) := by
      have := conj_mem_conjSub (n := g) (Subgroup.subset_closure
        (by simp : z₁ ∈ ({z₁, z₂} : Set G)))
      rwa [hgx] at this
    have hLF : L ≤ Subgroup.centralizer
        (conjSub g (Subgroup.closure ({z₁, z₂} : Set G)) : Set G) := by
      rw [hLg]
      exact BootRank3.conjSub_le_centralizer hK₁F g
    exact member_commutes_oddCoreIn_of_deltaCore_eq_bot hnab hp hq hΩc hIH hxF
      (hwz ▸ hxF) (BootRank3.isElemAbelian_two_conjSub hB g) hL.1 hw hLF hΔ
      (oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot hxF hz₁c.ne_one hα')
  · have hα' := alphaCore_pair_axis hΩ hp hq hA hsh hα hL hw hwz
    have hwC : w ∈ Subgroup.centralizer ({z₁} : Set G) := hL.2 hw.mem
    have hcomm : z₁ * w = w * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp hwC).symm
    have hF : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({z₁, w} : Set G)) := by
      refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
      · rintro s (rfl | hs)
        · exact hz₁c.sq
        · rw [Set.mem_singleton_iff.mp hs]
          exact hw.isCentralInvolution.sq
      · rintro s (rfl | hs) t (rfl | ht)
        · rfl
        · rw [Set.mem_singleton_iff.mp ht]
          exact hcomm
        · rw [Set.mem_singleton_iff.mp hs]
          exact hcomm.symm
        · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht]
    have hΔ : deltaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥ := by
      have hle := deltaCore_le_alphaCore (F := Subgroup.closure ({z₁, w} : Set G))
      rw [hα'] at hle
      exact le_bot_iff.mp hle
    have hxF : z₁ ∈ Subgroup.closure ({z₁, w} : Set G) := Subgroup.subset_closure (by simp)
    have hwF : w ∈ Subgroup.closure ({z₁, w} : Set G) := Subgroup.subset_closure (by simp)
    have hLF : L ≤ Subgroup.centralizer (Subgroup.closure ({z₁, w} : Set G) : Set G) := by
      rw [Subgroup.centralizer_closure]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      rintro x (rfl | hx)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hL.2 hk)).symm
      · rw [Set.mem_singleton_iff.mp hx]
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember hw hk)).symm
    exact member_commutes_oddCoreIn_of_deltaCore_eq_bot hnab hp hq hΩc hIH hxF hwF hF hL.1 hw hLF
      hΔ (oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot hxF hz₁c.ne_one hα')

end Member

variable (p f : ℕ) [Fact p.Prime]

theorem axisP1Core : AxisP1Core p f := by
  intro G _ _ _ K z hS hpsp K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA hbal hgen
  have hp := hS.odd
  have hq := hS.five
  have hΩ : HypOmegaMod p f (𝒞 K) :=
    Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f) G hS.nonabelian
      hp hq K z hS.member hS.below
  have hΩc : InClass p f (𝒞 K) := inClass_conjugates hS.member
  have hz₁c := isCentralInvolution_of_isClassicalMember hA.cls₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hA.cls₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hA.cls₃
  have hct : Commute t₁ t₂ := hA.ct₁₂
  have hcomm12 : z₁ * z₂ = z₂ * z₁ := by
    rw [← hA.sq₁, ← hA.sq₂]
    exact ((hct.mul_left hct).mul_right (hct.mul_left hct)).eq
  have hz₁₂ : z₁ ≠ z₂ := fun h => hz₃c.ne_one (by rw [← hA.prod, ← h, hz₁c.sq])
  have hpair : Subgroup.closure ({z₁, z₂} : Set G) ≤ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.mpr
      (Set.mem_insert _ _)))
  have hcard4 : Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 :=
    card_closure_pair_eq_four hz₁c.sq hz₂c.sq hz₁c.ne_one hz₂c.ne_one hz₁₂ hcomm12
  have hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ :=
    alphaCore_eq_bot_of_rankTwoSpan_eq_top
      (componentClassificationOddCore_eq_bot_of_simple hS.nonabelian) hbal hgen
      ⟨hpair, by rw [hcard4]; norm_num⟩
  have hsh := hpsp K₁ hA.mem₁ z₁ hA.cls₁
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hne : (centralizingMembers (𝒞 K) {z₁}).Nonempty
  · have hgen' := (inClass_local hΩc {z₁} hne).generated
    have hle : (⨆ L ∈ restrictFamily (centralizingMembers (𝒞 K) {z₁})
        (centralizingLayer (𝒞 K) {z₁}), L) ≤
        Subgroup.centralizer ({d} : Set ↥(centralizingLayer (𝒞 K) {z₁})) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨M, hM, hMY, rfl⟩ := hL
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hdO : (d : G) ∈ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)) :=
        ⟨Subgroup.inclusion (centLayer_le_centralizer (𝒞 K) z₁) d,
          map_inclusion_oddCore_le hΩc.conjInvariant ⟨d, hd, rfl⟩, rfl⟩
      exact Subtype.ext (member_commutes_oddCoreIn_axis hS.nonabelian hp hq hS.below hS.member
        hΩ hA hsh hα hM _ hdO k (Subgroup.mem_subgroupOf.mp hk)).symm
    have hy : y ∈ (⨆ L ∈ restrictFamily (centralizingMembers (𝒞 K) {z₁})
        (centralizingLayer (𝒞 K) {z₁}), L) := hgen' ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  · have hY : centLayer (𝒞 K) z₁ = ⊥ := by
      refine le_bot_iff.mp (centLayer_le fun L hL => ?_)
      exact absurd ⟨L, hL⟩ hne
    have htriv : ∀ u : ↥(centLayer (𝒞 K) z₁), u = 1 := fun u =>
      Subtype.ext (by
        have := u.2
        simpa only [hY, Subgroup.mem_bot, Subgroup.coe_one] using this)
    rw [htriv y, htriv d]

theorem axisP1 : AxisP1 p f :=
  AxisP1.of_core p f (axisP1Core p f)

end CFSG.ClassicalInvolution.NDB
