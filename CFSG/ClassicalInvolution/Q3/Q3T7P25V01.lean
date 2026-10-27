module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25VH00
public import CFSG.ClassicalInvolution.Asc77.AscCX6
import CFSG.ClassicalInvolution.Asc77.AscCX6Eng
public import CFSG.ClassicalInvolution.Asc77.AscS22C

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace C25W
open CFSG.ClassicalInvolution.Asc77.C25W
section Def

@[expose] def CentExtMix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            y * a = a * y → InFour a z (y * y) →
            (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) →
            (∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
              x ∉ Subgroup.zpowers z ∧ z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) ∧
                z ∈ zStarOf (Subgroup.centralizer ({x * z} : Set G))) →
            InFour a z y

@[expose] def CentExtNoMix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            y * a = a * y → InFour a z (y * y) →
            (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) →
            ¬ (∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
              x ∉ Subgroup.zpowers z ∧ z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) ∧
                z ∈ zStarOf (Subgroup.centralizer ({x * z} : Set G))) →
            InFour a z y

theorem centExt_of_parts (hM : CentExtMix) (hN : CentExtNoMix) : CentExt := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc
  by_cases hm : ∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      x ∉ Subgroup.zpowers z ∧ z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) ∧
        z ∈ zStarOf (Subgroup.centralizer ({x * z} : Set G))
  · exact hM G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc hm
  · exact hN G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc hm
end Def
end C25W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem mem_trivialOnQuot_of_mem_A (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) :
    x ∈ trivialOnQuot K ∧ x ∈ trivialOnQuot K' := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hcpg : IsPGroup 2 (Subgroup.zpowers x) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx.1)
  have hcent := Subgroup.mem_centralizer_iff.mp hx.2
  have hRc : R ≤ Subgroup.centralizer ({x} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent r (Subgroup.mem_sup_left hr))
  have hR'c : R' ≤ Subgroup.centralizer ({x} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent r (Subgroup.mem_sup_right hr))
  have hK₂ : K ∈ ExactLayer.tqMembers Ω x :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hst.modU hcpg).mpr
      ⟨hst.mem, R, h.hRsyl, hRc⟩
  have hK₂' : K' ∈ ExactLayer.tqMembers Ω x :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hst.modU hcpg).mpr
      ⟨hs.hK'.1, R', h.hR'syl, hR'c⟩
  exact ⟨hK₂.2, hK₂'.2⟩
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem exists_layer_conj_of_member (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (hzY : z ∈ ExactLayer.exactLayer Ω a) (hK : K ∈ ExactLayer.tqMembers Ω a)
    (D : LieSystemData 3 1 (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))
      (oddQuotientFamily (ExactLayer.exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {M : Subgroup G} (hM : M ∈ ExactLayer.tqMembers Ω a) {b : G} (hb : IsUniqueInvolution M b) :
    ∃ h ∈ ExactLayer.exactLayer Ω a, h * z * h⁻¹ = b := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  
  obtain ⟨i, R₁, hR₁, hKbar⟩ := D.fundamental _ (T7H.exactImg_mem hK)
  obtain ⟨i', R₂, hR₂, hMbar⟩ := D.fundamental _ (T7H.exactImg_mem hM)
  have hii : i' = i := Fin.ext (by have h1 := i.2; have h2 := i'.2; omega)
  subst hii
  obtain ⟨g, hg⟩ := RouteD.Gaps.fundamentalSingleClass_of_ne D i' (hD4 i').1 (hD4 i').2
    R₁ hR₁ R₂ hR₂
  have hMK : T7H.exactImg Ω a M = conjSub (D.hom i' g) (T7H.exactImg Ω a K) := by
    rw [hMbar, hKbar, hg, AscQuot.map_conjSub]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (D.hom i' g)
  have hxC : (x : G) ∈ Subgroup.centralizer ({a} : Set G) := ExactLayer.exactLayer_le_centralizer Ω
      a x.2
  have hK₁ : conjSub (x : G) K ∈ ExactLayer.tqMembers Ω a :=
    ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hxC hK
  have hb₁ : IsUniqueInvolution (conjSub (x : G) K) ((x : G) * z * (x : G)⁻¹) := hz.conj _
  have hb₁Y : (x : G) * z * (x : G)⁻¹ ∈ ExactLayer.exactLayer Ω a :=
    (ExactLayer.exactLayer Ω a).mul_mem ((ExactLayer.exactLayer Ω a).mul_mem x.2 hzY)
        ((ExactLayer.exactLayer Ω a).inv_mem x.2)
  have hbY : b ∈ ExactLayer.exactLayer Ω a :=
    ExactLayer.exactCore_le_exactLayer hM (T7H.isUniqueInvolution_exactCore hΩ hcpg hM hb).mem
  have hbarM := T7H.exactImg_isUnique hΩ hcpg hM hb hbY
  have hbar₁ := T7H.exactImg_isUnique hΩ hcpg hK₁ hb₁ hb₁Y
  have hEq : T7H.exactImg Ω a (conjSub (x : G) K) = T7H.exactImg Ω a M := by
    rw [C25Y.exactImg_conjSub_layer, hMK, hx]
  rw [hEq] at hbar₁
  have hbb : T7H.toBar Ω a b hbY = T7H.toBar Ω a ((x : G) * z * (x : G)⁻¹) hb₁Y :=
    hbarM.eq hbar₁
  
  set u : ↥(ExactLayer.exactLayer Ω a) := ⟨(x : G) * z * (x : G)⁻¹, hb₁Y⟩ with hu
  set v : ↥(ExactLayer.exactLayer Ω a) := ⟨b, hbY⟩ with hv
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    show ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = 1
    calc ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = (x : G) * (z * z) * (x : G)⁻¹ := by
          group
      _ = 1 := by rw [hz.sq]; group
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    exact hb.sq
  have huv : u * v ∈ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a) := by
    have h1 : u⁻¹ * v ∈ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a) :=
      QuotientGroup.eq.mp hbb.symm
    rwa [inv_eq_of_mul_eq_one_right hu2] at h1
  obtain ⟨n, hn, hnv⟩ := C25Y.exists_conj_of_involutions_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥(ExactLayer.exactLayer Ω a)) hu2 hv2 huv
  refine ⟨(n : G) * (x : G), (ExactLayer.exactLayer Ω a).mul_mem n.2 x.2, ?_⟩
  have h1 : b = (n : G) * ((x : G) * z * (x : G)⁻¹) * (n : G)⁻¹ := congrArg Subtype.val hnv
  rw [h1]
  group

theorem c25_8_one_layer (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (hzY : z ∈ ExactLayer.exactLayer Ω a) (hK : K ∈ ExactLayer.tqMembers Ω a)
    (D : LieSystemData 3 1 (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))
      (oddQuotientFamily (ExactLayer.exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    {J : Subgroup (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))}
    (hJ : J ∈ oddQuotientFamily (ExactLayer.exactPair Ω a))
    {y : ↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a)}
    (hyJ : y ∈ J) (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1)
    (hfix : C25Y.layerAut (ExactLayer.exactLayer Ω a)
      (ExactLayer.conjSub_exactLayer hyp.std.setting.stand.modU.conjInvariant hbC) y = y) :
    ∃ h ∈ ExactLayer.exactLayer Ω a, h * z * h⁻¹ = c * z * c⁻¹ := by
  obtain ⟨M, hM, hMb⟩ := C25Y.nc4_lift hyp ha2 hbC hJ hyJ hy4 hy2 hfix
  exact exists_layer_conj_of_member hyp ha2 hzY hK D hD1 hD4 hM hMb

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem sq_mem_zConj_layer (hM6 : C25Y.Layer6Cen4 3 1) (h5 : C25W.Layer5Sq)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    {g x : G} (hgC : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    (hxC : x ∈ Subgroup.centralizer ({a} : Set G)) (hxx : x * x = g * z * g⁻¹)
    (hx4' : x * x * x * x = 1) :
    ∃ h ∈ ExactLayer.exactLayer Ω a, h * z * h⁻¹ = g * z * g⁻¹ := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hz2 : z * z = 1 := hs.hz.sq
  obtain ⟨hzY, _hu₁Y, _hu₂Y, hK₂, _hK₂', _hgen, _hlt, htw⟩ :=
    C25X.layer_a_frame hyp ha2 ha1 haR haR'
  have hxY : conjSub x (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hxC
  have htY : conjSub (g * z * g⁻¹) (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hgC
  have hΦ : ∀ J ∈ oddQuotientFamily (ExactLayer.exactPair Ω a), ∀ y : ↥(ExactLayer.exactLayer Ω a) ⧸
      classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a),
      conjSub y J ∈ oddQuotientFamily (ExactLayer.exactPair Ω a) := by
    intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← C25Y.exactImg_conjSub_layer x']
    exact T7H.exactImg_mem (ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant
      (ExactLayer.exactLayer_le_centralizer Ω a x'.2) hMtq)
  have htt : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  rcases C25X.layer_a_typed_proved Facts25V.nc4 hyp ha2 ha1 haR haR' with h1 | h1 | h1
  · exact absurd h1 hbad
  ·
    obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h1
    have htag : t' = .PSp := by
      rcases hT with ⟨_, ht, _⟩ | ⟨h6, _⟩ | ⟨h6, _⟩ | ⟨h7, _⟩ | ⟨h8, _⟩ | ⟨h8, _⟩
      · exact ht
      all_goals omega
    have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
      intro i
      have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
      subst hi
      rw [hDt, htag]
      simp
    obtain ⟨J', hJ', y, hyJ', hy4, hy2, hβy⟩ := h5 _ _ D _ _ _ _ _ hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (C25Y.layerAut (ExactLayer.exactLayer Ω a) hxY)
      (C25W.layerAut_four _ hxY hx4')
    have hfix : C25Y.layerAut (ExactLayer.exactLayer Ω a)
        (ExactLayer.conjSub_exactLayer hΩ.conjInvariant hgC) y = y := by
      rw [← C25W.layerAut_sq _ hxY htY hxx y]
      exact hβy
    exact c25_8_one_layer hyp ha2 hzY hK₂ D hD1 hD4 hgC hJ' hyJ' hy4 hy2 hfix
  ·
    obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h1
    have htag : t' = .PSL ∨ t' = .PSU := by
      rcases hT with ⟨h5, _⟩ | ⟨_, _, ht, _⟩ | ⟨_, _, ht, _⟩ | ⟨h7, _⟩ | ⟨h8, _⟩ | ⟨h8, _⟩
      · omega
      · exact Or.inl ht
      · exact Or.inr ht
      · omega
      · omega
      · omega
    have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
      intro i
      have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
      subst hi
      rw [hDt]
      rcases htag with rfl | rfl <;> simp
    obtain ⟨J', hJ', y, hyJ', hy4, hy2, hβy⟩ := hM6 _ _ D _ _ _ _ _ hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (C25Y.layerAut (ExactLayer.exactLayer Ω a) htY)
      (C25Y.layerAut_involutive _ htY htt)
    exact c25_8_one_layer hyp ha2 hzY hK₂ D hD1 hD4 hgC hJ' hyJ' hy4 hy2 hβy
end Asc77.CX

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Action
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_odd_mul (hΩ : HypOmegaModT Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} (hJ : J ∈ ExactLayer.tqMembers Ω c) {v : G}
    (hvc : v ∈ Subgroup.centralizer ({c} : Set G)) (hvJ : v ∈ trivialOnQuot J) {k : G}
    (hk : k ∈ ExactLayer.exactCore c J) (hkY : k ∈ ExactLayer.exactLayer Ω c) (hvk : v * k * v⁻¹ ∈
        ExactLayer.exactLayer Ω c) :
    ∃ n ∈ oddCoreOf (T7H.exactImg Ω c J),
      T7H.toBar Ω c (v * k * v⁻¹) hvk = n * T7H.toBar Ω c k hkY := by
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ.1
  have hcore : v ∈ trivialOnQuot (ExactLayer.exactCore c J) :=
    ExactLayer.mem_trivialOnQuot_exactCore hzJ hc2 hJ.2 hvJ hvc
  have ho : ⁅v, k⁆ ∈ oddCoreIn (ExactLayer.exactCore c J) := hcore.2 k hk
  have hoQ : ⁅v, k⁆ ∈ ExactLayer.exactCore c J := oddCoreIn_le _ ho
  have hoY : ⁅v, k⁆ ∈ ExactLayer.exactLayer Ω c := ExactLayer.exactCore_le_exactLayer hJ hoQ
  set Y := ExactLayer.exactLayer Ω c with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  refine ⟨T7H.toBar Ω c ⁅v, k⁆ hoY, ?_, ?_⟩
  · have hP : oddCoreOf (T7H.exactImg Ω c J) =
        (oddCoreOf ((ExactLayer.exactCore c J).subgroupOf Y)).map (QuotientGroup.mk' N₀) :=
      oddCoreOf_map_mk_of_odd (odd_natCard_inf hN₀odd _)
    rw [hP]
    have ho' : ⁅v, k⁆ ∈ oddCoreOf (ExactLayer.exactCore c J) := ho
    obtain ⟨hx, hxo⟩ := mem_oddCoreOf_iff.mp ho'
    refine Subgroup.mem_map.mpr ⟨⟨⁅v, k⁆, hoY⟩, ?_, rfl⟩
    rw [mem_oddCoreOf_iff]
    exact ⟨Subgroup.mem_subgroupOf.mpr hoQ,
      mem_oddCore_subgroupOf (ExactLayer.exactCore_le_exactLayer hJ) hoQ hxo⟩
  · unfold T7H.toBar
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show v * k * v⁻¹ = ⁅v, k⁆ * k
    simp only [commutatorElement_def]
    group
end Action
end S22
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Action
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layerAut_fix_exactImg (hΩ : HypOmegaModT Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G} (hJ : J ∈ ExactLayer.tqMembers Ω c)
    (hO : oddCoreOf (T7H.exactImg Ω c J) = ⊥) {v : G}
    (hvc : v ∈ Subgroup.centralizer ({c} : Set G)) (hvJ : v ∈ trivialOnQuot J) :
    ∀ y ∈ T7H.exactImg Ω c J,
      C25Y.layerAut (ExactLayer.exactLayer Ω c) (ExactLayer.conjSub_exactLayer hΩ.conjInvariant
          hvc) y = y := by
  intro y hy
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hy
  have hk : (k₀ : G) ∈ ExactLayer.exactCore c J := Subgroup.mem_subgroupOf.mp hk₀
  have hvk : v * (k₀ : G) * v⁻¹ ∈ ExactLayer.exactLayer Ω c := by
    have h1 : v * (k₀ : G) * v⁻¹ ∈ conjSub v (ExactLayer.exactLayer Ω c) :=
        Generic.conj_mem_conjSub k₀.2
    rwa [ExactLayer.conjSub_exactLayer hΩ.conjInvariant hvc] at h1
  obtain ⟨n, hn, heq⟩ := S22.exists_odd_mul hΩ hc2 hJ hvc hvJ hk k₀.2 hvk
  rw [hO, Subgroup.mem_bot] at hn
  rw [hn, one_mul] at heq
  rw [QuotientGroup.mk'_apply, C25Y.layerAut_mk]
  exact heq

theorem mem_zStarOf_of_layerAut_eq_conj (hΩ : HypOmegaModT Ω) {b d z : G}
    (hdb : d ∈ Subgroup.centralizer ({b} : Set G)) (hzb : z ∈ Subgroup.centralizer ({b} : Set G))
    (hzd : z ∈ Subgroup.centralizer ({d} : Set G)) (hzY : z ∈ ExactLayer.exactLayer Ω b)
    (hcen : Subgroup.center (↥(ExactLayer.exactLayer Ω b) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω b)) =
      ⊥)
    (hd : ∀ y, C25Y.layerAut (ExactLayer.exactLayer Ω b) (ExactLayer.conjSub_exactLayer
        hΩ.conjInvariant hdb) y =
      T7H.toBar Ω b z hzY * y * (T7H.toBar Ω b z hzY)⁻¹) :
    z ∈ zStarOf (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set Y := ExactLayer.exactLayer Ω b with hY
  set H := Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) with hHdef
  have hHY : ∀ h ∈ H, conjSub h Y = Y := fun h hh =>
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hh.1
  rw [C25W.mem_zStarOf_iff]
  refine ⟨⟨hzb, hzd⟩, fun y hy => ?_⟩
  have hyi : y⁻¹ ∈ H := H.inv_mem hy
  set w := y⁻¹ * z * y⁻¹⁻¹ with hw
  have hwY : w ∈ Y := by
    have h1 : w ∈ conjSub y⁻¹ Y := Generic.conj_mem_conjSub hzY
    rwa [hHY _ hyi] at h1
  set α := C25Y.layerAut Y (hHY _ hyi) with hα
  set δ := C25Y.layerAut Y (ExactLayer.conjSub_exactLayer hΩ.conjInvariant hdb) with hδ
  have hαz : α (T7H.toBar Ω b z hzY) = T7H.toBar Ω b w hwY := by
    rw [hα]
    unfold T7H.toBar
    rw [QuotientGroup.mk'_apply, C25Y.layerAut_mk]
    rfl
  have hcomm : ∀ u, α (δ u) = δ (α u) := by
    intro u
    refine QuotientGroup.induction_on u fun u => ?_
    rw [hα, hδ, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp only [C25Y.coe_conjOnSub]
    have hyd : y⁻¹ * d = d * y⁻¹ := Subgroup.mem_centralizer_singleton_iff.mp hyi.2
    calc y⁻¹ * (d * (u : G) * d⁻¹) * y⁻¹⁻¹ = (y⁻¹ * d) * (u : G) * (y⁻¹ * d)⁻¹ := by group
      _ = (d * y⁻¹) * (u : G) * (d * y⁻¹)⁻¹ := by rw [hyd]
      _ = d * (y⁻¹ * (u : G) * y⁻¹⁻¹) * d⁻¹ := by group
  have hwz : T7H.toBar Ω b w hwY = T7H.toBar Ω b z hzY := by
    set zb := T7H.toBar Ω b z hzY with hzbdef
    set wb := T7H.toBar Ω b w hwY with hwbdef
    have hc : zb⁻¹ * wb ∈ Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y) := by
      rw [Subgroup.mem_center_iff]
      intro v
      obtain ⟨u, rfl⟩ := α.surjective v
      have h1 : α (δ u) = wb * α u * wb⁻¹ := by
        rw [hd u, map_mul, map_mul, map_inv, hαz]
      rw [hcomm u, hd (α u)] at h1
      have h2 : wb⁻¹ * zb * α u = α u * (wb⁻¹ * zb) := by
        calc wb⁻¹ * zb * α u = wb⁻¹ * (zb * α u * zb⁻¹) * zb := by group
          _ = wb⁻¹ * (wb * α u * wb⁻¹) * zb := by rw [h1]
          _ = α u * (wb⁻¹ * zb) := by group
      calc α u * (zb⁻¹ * wb) = (wb⁻¹ * zb)⁻¹ * ((wb⁻¹ * zb) * α u) * (zb⁻¹ * wb) := by group
        _ = (wb⁻¹ * zb)⁻¹ * (α u * (wb⁻¹ * zb)) * (zb⁻¹ * wb) := by rw [← h2]
        _ = zb⁻¹ * wb * α u := by group
    rw [hcen, Subgroup.mem_bot] at hc
    calc wb = zb * (zb⁻¹ * wb) := by group
      _ = zb := by rw [hc, mul_one]
  have hO : z⁻¹ * w ∈ oddCoreOf Y := by
    unfold T7H.toBar at hwz
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwz
    refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥Y).inv_mem hwz, ?_⟩
    simp
  have hmem : z⁻¹ * w ∈ H := by
    refine H.mul_mem (H.inv_mem ⟨hzb, hzd⟩) ?_
    rw [hw]
    exact H.mul_mem (H.mul_mem hyi ⟨hzb, hzd⟩) (H.inv_mem hyi)
  have h3 := mem_oddCore_of_mem_oddCoreOf hHY (c := ⟨z⁻¹ * w, hmem⟩) hO
  have e : z⁻¹ * y⁻¹ * z * y = z⁻¹ * w := by rw [hw]; group
  rw [e]
  exact Subgroup.mem_map.mpr ⟨_, h3, rfl⟩

theorem le_trivialOnQuot_of_layerAut_trivial (hΩ : HypOmegaModT Ω) {b : G} {F : Subgroup G}
    (hFb : F ≤ Subgroup.centralizer ({b} : Set G))
    (htriv : ∀ e (he : e ∈ F), ∀ y, C25Y.layerAut (ExactLayer.exactLayer Ω b)
      (ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hFb he)) y = y) :
    F ≤ trivialOnQuot (ExactLayer.exactLayer Ω b) := by
  intro e he
  have hY := ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hFb he)
  refine ⟨mem_normalizer_iff_conjSub_eq.mpr hY, fun x hx => ?_⟩
  have h1 := htriv e he (QuotientGroup.mk ⟨x, hx⟩)
  rw [C25Y.layerAut_mk, QuotientGroup.eq] at h1
  have h2 := (inferInstance : (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
      b)).Normal).conj_mem _
    ((classicalInvolutionOddCore _).inv_mem h1) ⟨x, hx⟩
  refine Subgroup.mem_map.mpr ⟨_, h2, ?_⟩
  simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, C25Y.coe_conjOnSub,
    commutatorElement_def]
  group

theorem not_mem_zStarOf_of_layerAut_trivial (hΩ : HypOmegaModT Ω) {b z : G}
    {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFb : F ≤ Subgroup.centralizer ({b} : Set G))
    (hzF : z ∈ Subgroup.centralizer (F : Set G)) (hzY : z ∈ ExactLayer.exactLayer Ω b)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcen : Subgroup.center (↥(ExactLayer.exactLayer Ω b) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω b)) =
      ⊥)
    (htriv : ∀ e (he : e ∈ F), ∀ y, C25Y.layerAut (ExactLayer.exactLayer Ω b)
      (ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hFb he)) y = y) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
  classical
  intro hz
  set Y := ExactLayer.exactLayer Ω b with hY
  set N := classicalInvolutionOddCore ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set C := Subgroup.centralizer (F : Set G) with hC
  have hFY := le_trivialOnQuot_of_layerAut_trivial hΩ hFb htriv
  obtain ⟨-, hzc⟩ := (C25W.mem_zStarOf_iff C).mp hz
  set M : Subgroup (↥Y ⧸ N) :=
    ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y).map π with hM
  have hcover : ∀ x : ↥Y, ∃ h : ↥Y, (h : G) ∈ C ∧ π h = π x := by
    intro x
    obtain ⟨h, hh, n, hn, hxhn⟩ := exists_mem_inf_centralizer_mul hF2 hFY x.2
    refine ⟨⟨h, hh.1⟩, hh.2, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨h, hh.1⟩ : ↥Y)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥Y) : G) = n from hn'n, hxhn]
      group
    rw [e]
    exact hn'
  have hMnorm : M.Normal := by
    refine ⟨fun m hm y => ?_⟩
    obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨h, hhC, hhy⟩ := hcover y₀
    rw [← hhy]
    refine Subgroup.mem_map.mpr ⟨h * m₀ * h⁻¹, ?_, by simp [hπ]⟩
    rw [Subgroup.mem_subgroupOf] at hm₀ ⊢
    obtain ⟨hmO, hmY, hmC⟩ := hm₀
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (h : G) * m₀ * (h : G)⁻¹ ∈ conjSub (h : G) (oddCoreOf C) :=
        Generic.conj_mem_conjSub hmO
      rwa [← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_self_of_mem hhC] at h1
    · exact (h * m₀ * h⁻¹).2
    · exact C.mul_mem (C.mul_mem hhC hmC) (C.inv_mem hhC)
  have hModd : Odd (Nat.card M) := by
    have hO : Odd (Nat.card (oddCoreOf C)) := by
      unfold oddCoreOf
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥C
    have h1 : Nat.card M ∣ Nat.card ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y) ∣ Nat.card (oddCoreOf C) := by
      rw [← Subgroup.card_map_of_injective Y.subtype_injective]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx).1
    exact Odd.of_dvd_nat hO (h1.trans h2)
  have hMbot : M = ⊥ := by
    have h1 : M ≤ classicalInvolutionOddCore (↥Y ⧸ N) :=
      le_sSup (show M ∈ {K : Subgroup (↥Y ⧸ N) | K.Normal ∧ Odd (Nat.card K)} from
        ⟨hMnorm, hModd⟩)
    have h2 : classicalInvolutionOddCore (↥Y ⧸ N) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
    rw [h2] at h1
    exact le_bot_iff.mp h1
  have hzcen : π ⟨z, hzY⟩ ∈ Subgroup.center (↥Y ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨h, hhC, hhy⟩ := hcover y₀
    rw [← hhy]
    have hcom : (⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h ∈
        (oddCoreOf C ⊓ (Y ⊓ C)).subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      refine ⟨by simpa using hzc (h : G) hhC, SetLike.coe_mem _, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hzF) (C.inv_mem hhC)) hzF) hhC
    have h1 : π ((⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h) = 1 := by
      have : π ((⟨z, hzY⟩ : ↥Y)⁻¹ * h⁻¹ * ⟨z, hzY⟩ * h) ∈ M := Subgroup.mem_map_of_mem _ hcom
      rwa [hMbot, Subgroup.mem_bot] at this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π h * π ⟨z, hzY⟩ =
          π h * π ⟨z, hzY⟩ * ((π ⟨z, hzY⟩)⁻¹ * (π h)⁻¹ * π ⟨z, hzY⟩ * π h) := by
            rw [h1, mul_one]
      _ = π ⟨z, hzY⟩ * π h := by group
  rw [hcen, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzcen
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : orderOf (⟨⟨z, hzY⟩, hzcen⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzo] at hdvd
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem not_mem_zStarOf_of_layerAut_fix (hΩ : HypOmegaModT Ω) {b z : G}
    {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFb : F ≤ Subgroup.centralizer ({b} : Set G))
    (hzY : z ∈ ExactLayer.exactLayer Ω b) (hz2 : z * z = 1)
    {x : ↥(ExactLayer.exactLayer Ω b) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω b)}
    (hfix : ∀ e (he : e ∈ F), C25Y.layerAut (ExactLayer.exactLayer Ω b)
      (ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hFb he)) x = x)
    (hxz : x * T7H.toBar Ω b z hzY * x⁻¹ ≠ T7H.toBar Ω b z hzY)
    (hxzc : (x * T7H.toBar Ω b z hzY * x⁻¹) * T7H.toBar Ω b z hzY =
      T7H.toBar Ω b z hzY * (x * T7H.toBar Ω b z hzY * x⁻¹)) :
    z ∉ zStarOf (Subgroup.centralizer (F : Set G)) :=
  not_mem_zStarOf_of_fix_of_normalizes hF2
    (fun _ he => ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hFb he)) hzY hz2 hfix hxz hxzc
end Action
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Core
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem twinFacts_of_bad (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {b : G} (hbA : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G))) :
    ∃ hzY : z ∈ ExactLayer.exactLayer Ω b, K ∈ ExactLayer.tqMembers Ω b ∧ K' ∈ ExactLayer.tqMembers
        Ω b ∧
      LayerTwinFacts (T7H.exactImg Ω b K) (T7H.exactImg Ω b K') (T7H.toBar Ω b z hzY) := by
  have hst := hyp.std.setting.stand
  have hcent := Subgroup.mem_centralizer_iff.mp hbA.2
  have haR : ∀ x ∈ R, b * x = x * b := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', b * x = x * b := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -, -, htw⟩ := C25X.layer_a_frame hyp hb2 hb1 haR haR'
  rcases C25X.layer_a_typed_proved Facts25V.nc4 hyp hb2 hb1 haR haR' with h | h | h
  · exact absurd h hbad
  · obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    exact ⟨hzY, hK₂, hK₂', layerTwinFacts_five D hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw⟩
  · obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    exact ⟨hzY, hK₂, hK₂', h6 _ _ D _ _ _ _ _ hD1 ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw⟩

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem false_of_growth (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {D₀ D : Subgroup G}
    (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hD₀D : D₀ ≤ D) (hbad : z ∉ zStarOf (Subgroup.centralizer (D : Set G)))
    (hmax : ∀ F : Subgroup G,
      F ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) → D₀ ≤ F →
        z ∉ zStarOf (Subgroup.centralizer (F : Set G)) → Nat.card F ≤ Nat.card D)
    {x b : G}
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hxD : x ∉ D) (hxzD : x * z ∉ D) (hbD : b ∈ D) (hb1 : b ≠ 1) (hb2 : b * b = 1)
    (hbx : x * b = b * x) (hbc : ∀ d ∈ D, d * b = b * d) : False := by
  classical
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    T7T.z_mem_centralizer_of_hyp hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaModT Ω := hyp.std.setting.stand.modU
  set E := D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z with hE
  have hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    sup_le (sup_le hDA (Subgroup.zpowers_le.mpr hxA)) (Subgroup.zpowers_le.mpr hzA)
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hbc d hd)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbx)
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (hzS b (hDA hbD).1).symm)
  have hbbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G)) :=
    C25W.not_mem_zStarOf_of_mem_badSub hbD (fun y hy => hzS y (hDA hy).1) hbad
  obtain ⟨hzY, hK₂, hK₂', hcen, hO, hO', hT2, hT3⟩ :=
    twinFacts_of_bad h6 hyp (hDA hbD) hb2 hb1 hbbad
  have hEY : ∀ e ∈ E, conjSub e (ExactLayer.exactLayer Ω b) = ExactLayer.exactLayer Ω b := fun e he
      =>
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant (hEb he)
  set lam := layerHom (ExactLayer.exactLayer Ω b) E hEY with hlam
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  have hfixK : ∀ e : E, ∀ y ∈ T7H.exactImg Ω b K, lam e y = y := fun e y hy =>
    layerAut_fix_exactImg hΩ hb2' hK₂ hO (hEb e.2) (mem_trivialOnQuot_of_mem_A hyp (hEA e.2)).1
      y hy
  have hfixK' : ∀ e : E, ∀ y ∈ T7H.exactImg Ω b K', lam e y = y := fun e y hy =>
    layerAut_fix_exactImg hΩ hb2' hK₂' hO' (hEb e.2) (mem_trivialOnQuot_of_mem_A hyp (hEA e.2)).2
      y hy
  have hP2 : IsPGroup 2 lam.range := by
    rw [MonoidHom.range_eq_map]
    exact (hE2.to_subgroup ⊤).map lam
  obtain ⟨hexpP, hcardP⟩ := hT2 lam.range hP2 fun β hβ => by
    obtain ⟨e, rfl⟩ := hβ
    exact ⟨hfixK e, hfixK' e⟩
  let z₀ : E := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hlamz : lam z₀ = MulAut.conj (T7H.toBar Ω b z hzY) := by
    ext y
    refine QuotientGroup.induction_on y fun y => ?_
    rw [hlam, layerHom_apply, C25Y.layerAut_mk, MulAut.conj_apply]
    unfold T7H.toBar
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
  have hζ1 : lam z₀ ≠ 1 := by
    rw [hlamz]
    exact conj_ne_one_of_center_eq_bot hcen (mk_ne_one_of_involution hzY hz2 hz1)
  have hD : ∀ d ∈ D.subgroupOf E, lam d ≠ lam z₀ := by
    intro d hd heq
    apply hbad
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hzd : z ∈ Subgroup.centralizer ({(d : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzS d (hDA hdD).1).symm
    have h1 := mem_zStarOf_of_layerAut_eq_conj hΩ (hEb d.2)
      (hEb (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))) hzd hzY hcen fun y => by
        have := congrArg (fun φ => φ y) heq
        simp only [hlamz, MulAut.conj_apply] at this
        exact this
    refine T7T.mem_zStarOf_of_le ?_ h1 ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hg b hbD).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr (hg d hdD).symm⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hDA hg).1
  obtain ⟨β, hβ2, hβζ, hβr, hβD, hcov⟩ := exists_beta lam (fun e => hexpP _ ⟨e, rfl⟩)
    hcardP hζ1 hD
  set F := ((Subgroup.zpowers β).comap lam).map E.subtype with hF
  have hzpow : ∀ γ ∈ Subgroup.zpowers β, γ = 1 ∨ γ = β := by
    intro γ hγ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
    rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
    · left
      rw [hk, zpow_mul, zpow_two, hβ2, one_zpow]
    · right
      rw [hk, zpow_add_one, zpow_mul, zpow_two, hβ2, one_zpow, one_mul]
  have hmemF : ∀ e : E, (lam e = 1 ∨ lam e = β) → (e : G) ∈ F := by
    intro e he
    refine ⟨e, ?_, rfl⟩
    show lam e ∈ Subgroup.zpowers β
    rcases he with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers β
  have hFprop : ∀ g ∈ F, ∃ e : E, (e : G) = g ∧ (lam e = 1 ∨ lam e = β) := by
    rintro g ⟨e, he, rfl⟩
    exact ⟨e, rfl, hzpow _ he⟩
  have hDF : D ≤ F := fun d hd =>
    hmemF ⟨d, Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)⟩
      (hβD _ (Subgroup.mem_subgroupOf.mpr hd))
  have hFE : F ≤ E := Subgroup.map_subtype_le _
  have hFA := hFE.trans hEA
  have hFb := hFE.trans hEb
  have hF2 : IsPGroup 2 F := hE2.to_le hFE
  let x₀ : E := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))⟩
  have hxF : x ∈ F ∨ x * z ∈ F := by
    rcases hcov x₀ with h | h
    · exact Or.inl (hmemF x₀ h)
    · exact Or.inr (hmemF (x₀ * z₀) h)
  have hDltF : Nat.card D < Nat.card F := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hDF fun hDFeq => ?_)
    rcases hxF with h | h
    · exact hxD (hDFeq ▸ h)
    · exact hxzD (hDFeq ▸ h)
  have hzC : z ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hzS g (hFA hg).1
  have hFbad : z ∉ zStarOf (Subgroup.centralizer (F : Set G)) := by
    by_cases hβ1 : β = 1
    · refine not_mem_zStarOf_of_layerAut_trivial hΩ hF2 hFb hzC hzY hz2 hz1 hcen ?_
      intro g hg y
      obtain ⟨e, rfl, he⟩ := hFprop g hg
      have h1 : lam e = 1 := by
        rcases he with h | h
        · exact h
        · rw [h, hβ1]
      have := congrArg (fun φ => φ y) h1
      simpa [hlam, layerHom_apply] using this
    · obtain ⟨e₁, he₁⟩ := hβr.resolve_left hβ1
      obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hT3 β (he₁ ▸ hfixK e₁) (he₁ ▸ hfixK' e₁) hβ2 hβ1
        (by rw [← hlamz]; exact hβζ)
      refine not_mem_zStarOf_of_layerAut_fix hΩ hF2 hFb hzY hz2 (x := xb) ?_ hxbz hxbc
      intro g hg
      obtain ⟨e, rfl, he⟩ := hFprop g hg
      rcases he with h | h
      · have := congrArg (fun φ => φ xb) h
        simpa [hlam, layerHom_apply] using this
      · have := congrArg (fun φ => φ xb) h
        simp only [hlam, layerHom_apply] at this
        rw [this, hxbfix]
  exact absurd (hmax F hFA (hD₀D.trans hDF) hFbad) (not_le.mpr hDltF)

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem exists_bad_complement (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {D₀ : Subgroup G}
    (hD₀A : D₀ ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hD₀bad : z ∉ zStarOf (Subgroup.centralizer (D₀ : Set G))) (hD₀1 : D₀ ≠ ⊥)
    (hsmall : Nat.card D₀ < 4 → ∃ x ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), x ∉ D₀ ∧ x * z ∉ D₀ ∧
        (∀ d ∈ D₀, x * d = d * x) ∧ (x * x ∈ D₀ ∨ x * x * z ∈ D₀)) :
    ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      D₀ ≤ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
      ∀ g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g ∈ D ∨ g * z ∈ D := by
  exact CFSG.ClassicalInvolution.Asc77.CX6Eng.exists_bad_complement_gen hyp.std.setting.hz.sq
    hyp.hzS (T7T.z_mem_centralizer_of_hyp hyp) (false_of_growth h6 hyp)
    CFSG.ClassicalInvolution.Asc77.CX.exists_mem_normalizer_sq_mem
    CFSG.ClassicalInvolution.Asc77.CX.exists_central_involution
    CFSG.ClassicalInvolution.Asc77.CX.inf_conjSub_ne_bot
    CFSG.ClassicalInvolution.Asc77.CX.exists_sup_central hD₀A hD₀bad hD₀1 hsmall
end Core
end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
