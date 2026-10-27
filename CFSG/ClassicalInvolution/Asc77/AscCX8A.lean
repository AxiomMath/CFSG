module

public import CFSG.ClassicalInvolution.Asc77.AscC25W3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem exists_layer_conj_of_member (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (hzY : z ∈ exactLayer Ω a) (hK : K ∈ tqMembers Ω a)
    (D : LieSystemData p f (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
      (oddQuotientFamily (exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {M : Subgroup G} (hM : M ∈ tqMembers Ω a) {b : G} (hb : IsUniqueInvolution M b) :
    ∃ h ∈ exactLayer Ω a, h * z * h⁻¹ = b := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
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
  have hxC : (x : G) ∈ Subgroup.centralizer ({a} : Set G) := exactLayer_le_centralizer Ω a x.2
  have hK₁ : conjSub (x : G) K ∈ tqMembers Ω a :=
    conjSub_mem_tqMembers hΩ.conjInvariant hxC hK
  have hb₁ : IsUniqueInvolution (conjSub (x : G) K) ((x : G) * z * (x : G)⁻¹) := hz.conj _
  have hb₁Y : (x : G) * z * (x : G)⁻¹ ∈ exactLayer Ω a :=
    (exactLayer Ω a).mul_mem ((exactLayer Ω a).mul_mem x.2 hzY) ((exactLayer Ω a).inv_mem x.2)
  have hbY : b ∈ exactLayer Ω a :=
    exactCore_le_exactLayer hM (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hM hb).mem
  have hbarM := T7H.exactImg_isUnique hp hΩ hcpg hM hb hbY
  have hbar₁ := T7H.exactImg_isUnique hp hΩ hcpg hK₁ hb₁ hb₁Y
  have hEq : T7H.exactImg Ω a (conjSub (x : G) K) = T7H.exactImg Ω a M := by
    rw [C25Y.exactImg_conjSub_layer, hMK, hx]
  rw [hEq] at hbar₁
  have hbb : T7H.toBar Ω a b hbY = T7H.toBar Ω a ((x : G) * z * (x : G)⁻¹) hb₁Y :=
    hbarM.eq hbar₁
  set u : ↥(exactLayer Ω a) := ⟨(x : G) * z * (x : G)⁻¹, hb₁Y⟩ with hu
  set v : ↥(exactLayer Ω a) := ⟨b, hbY⟩ with hv
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    show ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = 1
    calc ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = (x : G) * (z * z) * (x : G)⁻¹ := by
          group
      _ = 1 := by rw [hz.sq]; group
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    exact hb.sq
  have huv : u * v ∈ classicalInvolutionOddCore ↥(exactLayer Ω a) := by
    have h1 : u⁻¹ * v ∈ classicalInvolutionOddCore ↥(exactLayer Ω a) :=
      QuotientGroup.eq.mp hbb.symm
    rwa [inv_eq_of_mul_eq_one_right hu2] at h1
  obtain ⟨n, hn, hnv⟩ := C25Y.exists_conj_of_involutions_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥(exactLayer Ω a)) hu2 hv2 huv
  refine ⟨(n : G) * (x : G), (exactLayer Ω a).mul_mem n.2 x.2, ?_⟩
  have h1 : b = (n : G) * ((x : G) * z * (x : G)⁻¹) * (n : G)⁻¹ := congrArg Subtype.val hnv
  rw [h1]
  group

theorem c25_8_one_layer (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (hzY : z ∈ exactLayer Ω a) (hK : K ∈ tqMembers Ω a)
    (D : LieSystemData p f (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
      (oddQuotientFamily (exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    {J : Subgroup (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))}
    (hJ : J ∈ oddQuotientFamily (exactPair Ω a))
    {y : ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a)}
    (hyJ : y ∈ J) (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1)
    (hfix : C25Y.layerAut (exactLayer Ω a)
      (conjSub_exactLayer hyp.std.setting.stand.hyp.conjInvariant hbC) y = y) :
    ∃ h ∈ exactLayer Ω a, h * z * h⁻¹ = c * z * c⁻¹ := by
  obtain ⟨M, hM, hMb⟩ := C25Y.nc4_lift hyp ha2 hbC hJ hyJ hy4 hy2 hfix
  exact exists_layer_conj_of_member hyp ha2 hzY hK D hD1 hD4 hM hMb

theorem sq_mem_zConj_layer (hM6 : C25Y.Layer6Cen4 p f) (h5 : C25W.Layer5Sq p f)
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    {g x : G} (hgC : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    (hxC : x ∈ Subgroup.centralizer ({a} : Set G)) (hxx : x * x = g * z * g⁻¹)
    (hx4' : x * x * x * x = 1) :
    ∃ h ∈ exactLayer Ω a, h * z * h⁻¹ = g * z * g⁻¹ := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  obtain ⟨hzY, _hu₁Y, _hu₂Y, hK₂, _hK₂', _hgen, _hlt, htw⟩ :=
    C25X.layer_a_frame hyp ha2 ha1 haR haR'
  have hxY : conjSub x (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hxC
  have htY : conjSub (g * z * g⁻¹) (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hgC
  have hΦ : ∀ J ∈ oddQuotientFamily (exactPair Ω a), ∀ y : ↥(exactLayer Ω a) ⧸
      classicalInvolutionOddCore ↥(exactLayer Ω a),
      conjSub y J ∈ oddQuotientFamily (exactPair Ω a) := by
    intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← C25Y.exactImg_conjSub_layer x']
    exact T7H.exactImg_mem (conjSub_mem_tqMembers hΩ.conjInvariant
      (exactLayer_le_centralizer Ω a x'.2) hMtq)
  have htt : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  rcases C25X.layer_a_typed_proved hyp ha2 ha1 haR haR' with h1 | h1 | h1
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
    obtain ⟨J', hJ', y, hyJ', hy4, hy2, hβy⟩ := h5 hp hq _ _ D _ _ _ _ _ hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (C25Y.layerAut (exactLayer Ω a) hxY)
      (C25W.layerAut_four _ hxY hx4')
    have hfix : C25Y.layerAut (exactLayer Ω a)
        (conjSub_exactLayer hΩ.conjInvariant hgC) y = y := by
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
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (C25Y.layerAut (exactLayer Ω a) htY)
      (C25Y.layerAut_involutive _ htY htt)
    exact c25_8_one_layer hyp ha2 hzY hK₂ D hD1 hD4 hgC hJ' hyJ' hy4 hy2 hβy

end CFSG.ClassicalInvolution.Asc77.CX
