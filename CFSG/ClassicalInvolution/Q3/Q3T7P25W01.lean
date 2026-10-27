module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25X03
public import CFSG.ClassicalInvolution.Asc77.AscC25W3
public import CFSG.ClassicalInvolution.Asc77.AscC25W4

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
namespace C25Y
open CFSG.ClassicalInvolution.Asc77.C25Y
section Exceptional
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem c25_8_one (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
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
    (hfix : layerAut (ExactLayer.exactLayer Ω a)
      (ExactLayer.conjSub_exactLayer hyp.std.setting.stand.modU.conjInvariant hbC) y = y) :
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = c * z * c⁻¹ := by
  obtain ⟨M, hM, hMb⟩ := nc4_lift hyp ha2 hbC hJ hyJ hy4 hy2 hfix
  exact exists_centralizer_conj_of_member hyp ha2 hzY hK D hD1 hD4 hM hMb
end Exceptional
end C25Y
end Asc77

end

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
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

structure FourData (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (a : G) : Prop where
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haz : a ≠ z
  haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z
  hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
    b = 1 ∨ b = a ∨ b = z ∨ b = a * z
namespace FourData
open CFSG.ClassicalInvolution.Asc77.C25W.FourData
variable {hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G}

theorem haS (h : FourData hyp a) : a ∈ (S : Subgroup G) := h.haA.1

theorem haz_comm (h : FourData hyp a) : a * z = z * a := hyp.hzS a h.haS

theorem hz2 (_h : FourData hyp a) : z * z = 1 := hyp.std.setting.hz.sq

theorem hz1 (_h : FourData hyp a) : z ≠ 1 := hyp.std.setting.hz.ne_one

theorem haR (h : FourData hyp a) : ∀ x ∈ R, a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp h.haA.2) x (Subgroup.mem_sup_left hx)).symm

theorem haR' (h : FourData hyp a) : ∀ x ∈ R', a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp h.haA.2) x (Subgroup.mem_sup_right hx)).symm

theorem haK (h : FourData hyp a) : a ∈ trivialOnQuot K ∧ a ∈ trivialOnQuot K' := by
  obtain ⟨-, -, -, hK₂, hK₂', -⟩ := C25X.layer_a_frame hyp h.ha2 h.ha1 h.haR h.haR'
  exact ⟨hK₂.2, hK₂'.2⟩

theorem mem_center (h : FourData hyp a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G))) :
    ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a := by
  intro s hs
  rcases h.hconj s hs with h1 | h1
  · exact h1
  · exfalso
    have hsz : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
        _ = z := by group
    have h2 := (mem_zStarOf_centralizer_conj_iff (z := z) (a := a) (c := s) hsz).mp
      (by rw [h1]; exact hgood)
    exact hbad h2
end FourData

theorem comm_of_mem_sylow {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G}
    (h : FourData hyp a) (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G)))
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (haV : a ∈ V) (hzV : z ∈ V) :
    ∀ y ∈ V, (y * z = z * y ∨ y * (a * z) = (a * z) * y) → y * a = a * y := by
  intro y hy hyc
  have hz2 := h.hz2
  have hcen := h.mem_center hbad hgood
  have haz' := h.haz_comm
  rcases hyc with hyz | hyaz
  ·
    have hSH : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS s hs)
    have hT2 : IsPGroup 2 (V ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :=
      hV2.to_le inf_le_left
    obtain ⟨c, hc, hcT⟩ := exists_conj_ge_sylow hSH hT2 inf_le_right
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hczc : c * z * c⁻¹ = z := by
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [hcz]
        _ = z := by group
    have hczc' : c⁻¹ * z * c⁻¹⁻¹ = z := by
      calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ := by rw [hczc]
        _ = z := by group
    have haT : a ∈ V ⊓ Subgroup.centralizer ({z} : Set G) :=
      ⟨haV, Subgroup.mem_centralizer_singleton_iff.mpr haz'⟩
    have ha'S : c⁻¹ * a * c ∈ (S : Subgroup G) := hcT a haT
    have ha'A := C25Y.conj_mem_Csub hyp h.haK.1 h.haK.2 hczc'
      (by simpa using ha'S : c⁻¹ * a * c⁻¹⁻¹ ∈ (S : Subgroup G))
    have ha'eq : c⁻¹ * a * c = a := by
      have ha'A' : c⁻¹ * a * c ∈ (S : Subgroup G) ⊓
          Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by simpa using ha'A
      rcases h.hA0 _ ha'A' with h1 | h1 | h1 | h1
      · exfalso
        apply h.ha1
        calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · exact h1
      · exfalso
        apply h.haz
        calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
          _ = c * z * c⁻¹ := by rw [h1]
          _ = z := hczc
      · exfalso
        have := (mem_zStarOf_centralizer_conj_iff (z := z) (a := a) (c := c⁻¹) hczc').mp
          (by rw [show c⁻¹ * a * c⁻¹⁻¹ = a * z by simpa using h1]; exact hgood)
        exact hbad this
    have hac : a * c = c * a := by
      calc a * c = c * (c⁻¹ * a * c) := by group
        _ = c * a := by rw [ha'eq]
    have hy' : c⁻¹ * y * c ∈ (S : Subgroup G) :=
      hcT y ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩
    have h2 : (c⁻¹ * y * c) * a * (c⁻¹ * y * c)⁻¹ = a := hcen _ hy'
    have h3 : (c⁻¹ * y * c) * a = a * (c⁻¹ * y * c) := by
      calc (c⁻¹ * y * c) * a = (c⁻¹ * y * c) * a * (c⁻¹ * y * c)⁻¹ * (c⁻¹ * y * c) := by group
        _ = a * (c⁻¹ * y * c) := by rw [h2]
    calc y * a = c * ((c⁻¹ * y * c) * (c⁻¹ * a * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * a) * c⁻¹ := by rw [ha'eq]
      _ = c * (a * (c⁻¹ * y * c)) * c⁻¹ := by rw [h3]
      _ = c * ((c⁻¹ * a * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [ha'eq]
      _ = a * y := by group
  ·
    have hTV : Subgroup.closure ({y, z} : Set G) ≤ V := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hy
      · exact hzV
    have hT2 : IsPGroup 2 (Subgroup.closure ({y, z} : Set G)) := hV2.to_le hTV
    have hzaz : z * (a * z) = (a * z) * z := by
      calc z * (a * z) = (z * a) * z := by group
        _ = (a * z) * z := by rw [haz']
    have hTC : Subgroup.closure ({y, z} : Set G) ≤ Subgroup.centralizer ({a * z} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyaz
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzaz
    have hzT : z ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyT : y ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyz : y * z = z * y :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (T7T.le_centralizer_of_mem_zStarOf hgood hzT hTC hT2 hyT)
    calc y * a = y * ((a * z) * z) := by rw [mul_assoc, hz2, mul_one]
      _ = (y * (a * z)) * z := by group
      _ = ((a * z) * y) * z := by rw [hyaz]
      _ = (a * z) * (y * z) := by group
      _ = (a * z) * (z * y) := by rw [hyz]
      _ = ((a * z) * z) * y := by group
      _ = a * y := by rw [mul_assoc a z z, hz2, mul_one]
end C25W
end Asc77

end

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
section ModelFact

@[expose] def Layer5Sq : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData 3 1 Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ → (∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) →
    ∀ β : Y ≃* Y, (∀ x : Y, β (β (β (β x))) = x) →
      ∃ J ∈ Φ, ∃ y ∈ J, y * y * y * y = 1 ∧ y * y ≠ 1 ∧ β (β y) = y
end ModelFact
section NoMixed
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem sq_mem_zConj (hnc4 : C25X.NC4Fact) (hM6 : C25Y.Layer6Cen4 3 1) (h5 : Layer5Sq)
    {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    {g x : G} (hgC : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    (hxC : x ∈ Subgroup.centralizer ({a} : Set G)) (hxx : x * x = g * z * g⁻¹)
    (hx4' : x * x * x * x = 1) :
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hz2 : z * z = 1 := hs.hz.sq
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hgen, hlt, htw⟩ := C25X.layer_a_frame hyp ha2 ha1 haR haR'
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
  rcases C25X.layer_a_typed_proved hnc4 hyp ha2 ha1 haR haR' with h1 | h1 | h1
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
      (layerAut_four _ hxY hx4')
    have hfix : C25Y.layerAut (ExactLayer.exactLayer Ω a)
        (ExactLayer.conjSub_exactLayer hΩ.conjInvariant hgC) y = y := by
      rw [← layerAut_sq _ hxY htY hxx y]
      exact hβy
    exact C25Y.c25_8_one hyp ha2 hzY hK₂ D hD1 hD4 hgC hJ' hyJ' hy4 hy2 hfix
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
    exact C25Y.c25_8_one hyp ha2 hzY hK₂ D hD1 hD4 hgC hJ' hyJ' hy4 hy2 hβy

theorem no_mixed (hnc4 : C25X.NC4Fact) (hM6 : C25Y.Layer6Cen4 3 1) (h5 : Layer5Sq)
    {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G} (h : FourData hyp a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G))) : False := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hz2 := h.hz2
  have hz1 := h.hz1
  have haz' := h.haz_comm
  
  have hcen := h.mem_center hbad hgood
  obtain ⟨g, hgS, hgC, hgn⟩ := exists_exceptional_in_S hcen hz2
    (C25Y.not_goodFusion hyp h.ha2 h.ha1 h.haz h.haA h.hconj h.hA0)
  have htz : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := hyp.hzS _ hgS
  have hta : (g * z * g⁻¹) * a = a * (g * z * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hgC
  
  set A₄ : Subgroup G := Subgroup.closure ({a, z} : Set G) with hA₄
  have hE : IsElemAbelian2 A₄ 2 :=
    T7A.isElemAbelian2_closure_pair h.ha2 hz2 h.ha1 hz1 h.haz haz'
  have hA2 : IsPGroup 2 A₄ := IsPGroup.of_card (n := 2) hE.1
  have haA₄ : a ∈ A₄ := Subgroup.subset_closure (by simp)
  have hzA₄ : z ∈ A₄ := Subgroup.subset_closure (by simp)
  have hAC : A₄ ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
    rw [hA₄, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hta.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr htz.symm
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA2 hAC
  have haV : a ∈ V := hAV haA₄
  have hzV : z ∈ V := hAV hzA₄
  have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hst.mem
  have htJ : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
  have hP : PartIHyp Ω := ⟨hΩ, hst.cls, hst.aEmpty⟩
  have hΓ : gamma1 A₄ (V ⊓ ⨆ L ∈ twinSet Ω (conjSub g K), L) ≤
      Subgroup.centralizer ({a} : Set G) := by
    unfold gamma1
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    intro y hy
    obtain ⟨⟨hyV, -⟩, hyw⟩ := (Subgroup.mem_inf.mp hy) |>.imp Subgroup.mem_inf.mp id
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyw' : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp hyw
    rcases C25Y.mem_closure_pair h.ha2 hz2 haz' hw with h1 | h1 | h1 | h1
    · exact absurd h1 hw1
    · rw [h1] at hyw'
      exact hyw'
    · rw [h1] at hyw'
      exact comm_of_mem_sylow h hbad hgood hV.2.1 haV hzV y hyV (Or.inl hyw')
    · rw [h1] at hyw'
      exact comm_of_mem_sylow h hbad hgood hV.2.1 haV hzV y hyV (Or.inr hyw')
  
  obtain ⟨x, hxJ, hx4, hxa⟩ := Q3CL.l9_3 hP (conjSub g K) hJ (g * z * g⁻¹) htJ V
    hV A₄ hAV hE a haA₄ h.ha1 hΓ
  have hxx : x * x = g * z * g⁻¹ := C25X.sq_eq_of_orderOf_four htJ hxJ hx4
  have hx4' : x * x * x * x = 1 := by
    have h1 : x ^ 4 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx4] at this
    calc x * x * x * x = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := h1
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxa
  obtain ⟨h', hh'C, hh'⟩ := sq_mem_zConj hnc4 hM6 h5 (hyp := hyp) h.ha2 h.ha1 h.haR h.haR' hbad hgC
    hxC hxx hx4'
  exact hgn h' hh'C hh'
end NoMixed
end C25W
end Asc77

end

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
section Ext
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem twisted_false {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a y : G}
    (ha2 : a * a = 1)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hy2 : InFour a z (y * y))
    (hyc : ∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹))
    (hyaz : y * a * y⁻¹ = a * z) : False := by
  have haS : a ∈ (S : Subgroup G) := haA.1
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have haz' : a * z = z * a := hyp.hzS a haS
  have hyS : y ∈ (S : Subgroup G) := hyA.1
  have hyz : y * z = z * y := hyp.hzS y hyS
  have hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := by
    intro s hs
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  have hya : y * a = a * z * y := by
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * z * y := by rw [hyaz]
  have hcomm_false : y * a = a * y → False := by
    intro hc
    have h1 : y * a * y⁻¹ = a := by rw [hc]; group
    rw [hyaz] at h1
    exact hz1 (mul_left_cancel (a := a) (b := z) (c := 1) (by rw [mul_one]; exact h1))
  have hy2' : y * y = 1 ∨ y * y = z := by
    rcases hy2 with h | h | h | h
    · exact Or.inl h
    · exfalso
      apply hcomm_false
      calc y * a = y * (y * y) := by rw [h]
        _ = (y * y) * y := by group
        _ = a * y := by rw [h]
    · exact Or.inr h
    · exfalso
      apply hcomm_false
      have h1 : y * (a * z) = (a * z) * y := by
        calc y * (a * z) = y * (y * y) := by rw [h]
          _ = (y * y) * y := by group
          _ = (a * z) * y := by rw [h]
      have h2 : (y * a) * z = (a * y) * z := by
        calc (y * a) * z = y * (a * z) := by group
          _ = (a * z) * y := h1
          _ = a * (z * y) := by group
          _ = a * (y * z) := by rw [hyz]
          _ = (a * y) * z := by group
      exact mul_right_cancel h2
  have hFc := conj_mem_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  have hFyc : ∀ s ∈ (S : Subgroup G),
      s * y * s⁻¹ * y⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := fun s hs =>
    (inFour_iff_mem_closure ha2 hz2 haz').mp (hyc s hs)
  obtain ⟨y', hy'A, hy'sq, hy'a, hy'c⟩ : ∃ y' : G,
      y' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      y' * y' = z ∧ y' * a = a * z * y' ∧
      ∀ s ∈ (S : Subgroup G), s * y' * s⁻¹ * y'⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
    rcases hy2' with h | h
    ·
      refine ⟨y * a, Subgroup.mul_mem _ hyA haA, ?_, ?_, ?_⟩
      · calc y * a * (y * a) = (y * a * y⁻¹) * (y * y) * a := by group
          _ = a * z * 1 * a := by rw [hyaz, h]
          _ = a * (z * a) := by rw [mul_one]; group
          _ = a * (a * z) := by rw [haz']
          _ = (a * a) * z := by group
          _ = z := by rw [ha2, one_mul]
      · calc y * a * a = y := by rw [mul_assoc, ha2, mul_one]
          _ = a * z * (a * z * y) := by
            calc y = (a * z * a * z) * y := by
                  have : a * z * a * z = 1 := by
                    calc a * z * a * z = a * (z * a) * z := by group
                      _ = a * (a * z) * z := by rw [haz']
                      _ = (a * a) * (z * z) := by group
                      _ = 1 := by rw [ha2, hz2, one_mul]
                  rw [this, one_mul]
              _ = a * z * (a * z * y) := by group
          _ = a * z * (y * a) := by rw [hya]
      · intro s hs
        have hsa : s * a * s⁻¹ * a⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
          have := hFc s hs a (Subgroup.subset_closure (by simp))
          exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        have h3 := Subgroup.mul_mem _ (hFyc s hs) (hFc y hyS _ hsa)
        convert h3 using 1
        group
    · exact ⟨y, hyA, h, hya, hFyc⟩
  have hy'S : y' ∈ (S : Subgroup G) := hy'A.1
  have hy'z : y' * z = z * y' := hyp.hzS y' hy'S
  have hy'az : y' * (a * z) = a * y' := by
    calc y' * (a * z) = (y' * a) * z := by group
      _ = (a * z * y') * z := by rw [hy'a]
      _ = a * z * (y' * z) := by group
      _ = a * z * (z * y') := by rw [hy'z]
      _ = a * (z * z) * y' := by group
      _ = a * y' := by rw [hz2, mul_one]
  have haz4 : a * z * a * z = 1 := by
    calc a * z * a * z = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [haz']
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2, one_mul]
  have hy'zp : z ∈ Subgroup.zpowers y' := ⟨2, by show y' ^ (2 : ℤ) = z; rw [zpow_two, hy'sq]⟩
  have hBc : ∀ s ∈ (S : Subgroup G), s * y' * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs
    set w := s * y' * s⁻¹ with hw
    have hww : w * w = z := by
      calc w * w = s * (y' * y') * s⁻¹ := by rw [hw]; group
        _ = z := by rw [hy'sq, hzS s hs]
    have hwf : w = (w * y'⁻¹) * y' := by group
    have hf := hy'c s hs
    rcases C25Y.mem_closure_pair ha2 hz2 haz' hf with h | h | h | h
    · have : w = y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = y'; rw [h, one_mul]
      rw [this]
      exact Subgroup.mem_zpowers y'
    · exfalso
      have hw' : w = a * y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = a * y'; rw [h]
      have h1 : (a * y') * (a * y') = 1 := by
        calc (a * y') * (a * y') = a * (y' * a) * y' := by group
          _ = a * (a * z * y') * y' := by rw [hy'a]
          _ = (a * a) * z * (y' * y') := by group
          _ = 1 := by rw [ha2, hy'sq, one_mul, hz2]
      rw [hw', h1] at hww
      exact hz1 hww.symm
    · have : w = z * y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = z * y'; rw [h]
      rw [this]
      exact Subgroup.mul_mem _ hy'zp (Subgroup.mem_zpowers y')
    · exfalso
      have hw' : w = a * z * y' := by
        rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = a * z * y'; rw [h]
      have h1 : (a * z * y') * (a * z * y') = 1 := by
        calc (a * z * y') * (a * z * y') = a * z * (y' * (a * z)) * y' := by group
          _ = a * z * (a * y') * y' := by rw [hy'az]
          _ = (a * z * a) * (y' * y') := by group
          _ = (a * z * a) * z := by rw [hy'sq]
          _ = 1 := haz4
      rw [hw', h1] at hww
      exact hz1 hww.symm
  have hBc' : ∀ s ∈ (S : Subgroup G), ∀ b ∈ Subgroup.zpowers y',
      s * b * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hBc s hs) k
  have hBn : ∀ s ∈ (S : Subgroup G), conjSub s (Subgroup.zpowers y') = Subgroup.zpowers y' := by
    intro s hs
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have := hBc' s hs _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hBc' s⁻¹ ((S : Subgroup G).inv_mem hs) _ hx
      simpa [mul_assoc] using this
  have hBS : Subgroup.zpowers y' ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hy'S
  have hall : ∀ b ∈ Subgroup.zpowers y', b ≠ 1 →
      z ∈ zStarOf (Subgroup.centralizer ({b} : Set G)) := fun b hb hb1 =>
    good_of_mem_zpowers (z_mem_zpowers_of_sq hy'sq hz2 hb hb1)
  have hE := T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp
    (Subgroup.zpowers y') hy'zp hBS hBn hall
  have hy'z' : y' ∈ Subgroup.zpowers z := hE ▸ Subgroup.mem_zpowers y'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'z'
  have h1 : y' * y' = 1 := by
    rcases C25Y.zpow_eq_one_or_self hz2 k with h | h
    · rw [← hk, h]; simp
    · rw [← hk, h]; exact hz2
  rw [hy'sq] at h1
  exact hz1 h1
end Ext
section Residual
section Def

@[expose] def CentExt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            y * a = a * y → InFour a z (y * y) →
            (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) → InFour a z y
end Def
section Reduction
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem fourExhausts_of_centExt (hExt : CentExt)
    {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))) :
    ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      InFour a z b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbA, hbF⟩ := hcon
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have haS : a ∈ (S : Subgroup G) := haA.1
  have haz' : a * z = z * a := hyp.hzS a haS
  have hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := by
    intro s hs
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hA
  set F : Subgroup G := Subgroup.closure ({a, z} : Set G) with hF
  have hFA : F ≤ A := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact haA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hzA
  have hFne : F ≠ A := by
    intro hFA'
    apply hbF
    exact (inFour_iff_mem_closure ha2 hz2 haz').mpr (by rw [← hF, hFA']; exact hbA)
  have hAn : ∀ s ∈ (S : Subgroup G), conjSub s A = A := fun s hs =>
    T7T.conjSub_centralizer_of_hyp hyp hs
  have hFn := Asc77.C25W.conjSub_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  have hFc := conj_mem_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  obtain ⟨y, hyA, hyF, hy2, hyc⟩ := exists_sq_mem_mod S.isPGroup' inf_le_left hAn hFA hFn hFne
  have hyS : y ∈ (S : Subgroup G) := hyA.1
  have hyaF : y * a * y⁻¹ ∈ F := hFc y hyS a (Subgroup.subset_closure (by simp))
  rcases C25Y.mem_closure_pair ha2 hz2 haz' hyaF with h | h | h | h
  · exfalso
    apply ha1
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · apply hyF
    have hcomm : y * a = a * y := by
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = a * y := by rw [h]
    exact (inFour_iff_mem_closure ha2 hz2 haz').mp
      (hExt G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hcomm
        ((inFour_iff_mem_closure ha2 hz2 haz').mpr hy2)
        fun s hs => (inFour_iff_mem_closure ha2 hz2 haz').mpr (hyc s hs))
  · exfalso
    apply haz
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [h]
      _ = z := by
        have := hyp.hzS y hyS
        calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
          _ = y⁻¹ * (y * z) := by rw [this]
          _ = z := by group
  · exact twisted_false (hyp := hyp) ha2 haA hconj hyA
      ((inFour_iff_mem_closure ha2 hz2 haz').mpr hy2)
      (fun s hs => (inFour_iff_mem_closure ha2 hz2 haz').mpr (hyc s hs)) h
end Reduction
end Residual
end C25W
end Asc77

end

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
section Assembly

theorem c25_9_of_residuals (hnc4 : C25X.NC4Fact) (hM6 : C25Y.Layer6Cen4 3 1) (h5 : Layer5Sq) (hExt
    : CentExt) :
    C25_9 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  by_cases hA : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z
  · have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have hcard : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 2 := by
      rw [hA, Nat.card_zpowers, hz2']
    exact ⟨by omega, fun h4 => by omega⟩
  · obtain ⟨a, haA, ha2, ha1, haz, hconj, hbad⟩ := T7U.exists_normal_four_bad hyp hA
    have hA0 := fourExhausts_of_centExt hExt (hyp := hyp) haA ha2 ha1 haz hconj hbad
    have haz' : a * z = z * a := hyp.hzS a haA.1
    have hFD : FourData hyp a := ⟨ha2, ha1, haz, haA, hconj, hA0⟩
    have hAeq : Subgroup.closure ({a, z} : Set G) =
        (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      refine le_antisymm ?_ fun b hb =>
        (inFour_iff_mem_closure ha2 hz2 haz').mp (hA0 b hb)
      rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact haA
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hzA
    have hE := T7A.isElemAbelian2_closure_pair ha2 hz2 ha1 hz1 haz haz'
    have hcard : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 := by
      rw [← hAeq, hE.1]
      norm_num
    refine ⟨hcard.le, fun _ => ⟨a, hAeq, hbad, fun hgood => ?_⟩⟩
    exact no_mixed hnc4 hM6 h5 hFD hbad hgood
end Assembly
end C25W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
namespace C25W
open CFSG.ClassicalInvolution.Asc77.C25W

theorem c25_9_of_centExt (hnc4 : C25X.NC4Fact) (hM6 : C25Y.Layer6Cen4 3 1) (h5 : Layer5Sq)
    (hExt : CentExt) : C25_9 :=
  c25_9_of_residuals hnc4 hM6 h5 hExt
end C25W
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
