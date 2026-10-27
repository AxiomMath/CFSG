module

public import CFSG.ClassicalInvolution.Asc77.AscC25W2
public import CFSG.ClassicalInvolution.Asc77.AscC25X12
public import CFSG.ClassicalInvolution.Asc77.AscC25Y4
public import CFSG.ClassicalInvolution.Asc77.AscC25Y5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25W

section ModelFact

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Layer5Sq : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ → (∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) →
    ∀ β : Y ≃* Y, (∀ x : Y, β (β (β (β x))) = x) →
      ∃ J ∈ Φ, ∃ y ∈ J, y * y * y * y = 1 ∧ y * y ≠ 1 ∧ β (β y) = y

end ModelFact

section LayerAutLemmas

variable {G : Type} [Group G]

theorem layerAut_four (Y : Subgroup G) {x : G} (hx : conjSub x Y = Y) (hx4 : x * x * x * x = 1)
    (y : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    C25Y.layerAut Y hx (C25Y.layerAut Y hx (C25Y.layerAut Y hx (C25Y.layerAut Y hx y))) = y := by
  refine QuotientGroup.induction_on y fun y₀ => ?_
  simp only [C25Y.layerAut_mk]
  congr 1
  apply Subtype.ext
  simp only [C25Y.coe_conjOnSub]
  calc x * (x * (x * (x * (y₀ : G) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹
      = (x * x * x * x) * (y₀ : G) * (x * x * x * x)⁻¹ := by group
    _ = y₀ := by rw [hx4]; group

theorem layerAut_sq (Y : Subgroup G) {x b : G} (hx : conjSub x Y = Y) (hb : conjSub b Y = Y)
    (hxb : x * x = b) (y : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    C25Y.layerAut Y hx (C25Y.layerAut Y hx y) = C25Y.layerAut Y hb y := by
  refine QuotientGroup.induction_on y fun y₀ => ?_
  simp only [C25Y.layerAut_mk]
  congr 1
  apply Subtype.ext
  simp only [C25Y.coe_conjOnSub]
  rw [← hxb]
  group

end LayerAutLemmas

section NoMixed

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}



theorem sq_mem_zConj (hM6 : C25Y.Layer6Cen4 p f) (h5 : Layer5Sq p f)
    {hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂} {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    {g x : G} (hgC : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    (hxC : x ∈ Subgroup.centralizer ({a} : Set G)) (hxx : x * x = g * z * g⁻¹)
    (hx4' : x * x * x * x = 1) :
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hgen, hlt, htw⟩ := C25X.layer_a_frame hyp ha2 ha1 haR haR'
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
      (layerAut_four _ hxY hx4')
    have hfix : C25Y.layerAut (exactLayer Ω a)
        (conjSub_exactLayer hΩ.conjInvariant hgC) y = y := by
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
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (C25Y.layerAut (exactLayer Ω a) htY)
      (C25Y.layerAut_involutive _ htY htt)
    exact C25Y.c25_8_one hyp ha2 hzY hK₂ D hD1 hD4 hgC hJ' hyJ' hy4 hy2 hβy

theorem no_mixed (hM6 : C25Y.Layer6Cen4 p f) (h5 : Layer5Sq p f)
    {hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂} {a : G} (h : FourData hyp a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G))) : False := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
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
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, hst.aEmpty⟩
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
  obtain ⟨x, hxJ, hx4, hxa⟩ := l9_3 (p := p) (f := f) G Ω hP (conjSub g K) hJ (g * z * g⁻¹) htJ V
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
  obtain ⟨h', hh'C, hh'⟩ := sq_mem_zConj hM6 h5 (hyp := hyp) h.ha2 h.ha1 h.haR h.haR' hbad hgC
    hxC hxx hx4'
  exact hgn h' hh'C hh'

end NoMixed

end C25W

end CFSG.ClassicalInvolution.Asc77
