module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf4Tw
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf4Orth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfIdent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Dim

@[expose] def P23E4Dim (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R e →
      ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) e)), ∀ h : D.card = 1,
        ∀ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool),
          IsOrthTag d ε tag k → CompIs 3 1 (D.kind ⟨0, by omega⟩) tag k →
            d = 6 ∧ ε = piSign 3 1

end Dim

section Lemmas

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem involution_mem_sylow {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {J T : Subgroup Y} {w : Y}
    (hJ : J ∈ Ω) (hw : IsUniqueInvolution J w) (hT : IsSylow2In T J) : w ∈ T := by
  obtain ⟨x, hx, ox⟩ := CFSG.ClassicalInvolution.Q8P.P25.exists_orderOf_eq_four_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hJ hT)
  have : x * x = w := TwinPerp.sq_eq_of_orderOf_four hw (hT.1 hx) ox
  exact this ▸ T.mul_mem hx hx

theorem exists_std_t (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ A A' : Subgroup Y, IsSylow2In A (tightCore R) ∧ IsSylow2In A' K' ∧
      A ≤ Subgroup.centralizer ({e} : Set Y) ∧ A' ≤ Subgroup.centralizer ({e} : Set Y) ∧
      IsPGroup 2 ↥(A ⊔ A') ∧ t ∈ A ∧ t ∈ A' := by
  obtain ⟨A, A', hA, hA', hAe, hA'e, h2, -⟩ := exists_std hc
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  exact ⟨A, A', hA, hA', hAe, hA'e, h2,
    involution_mem_sylow hC.hyp (CoreAssembly.mem_conjClass_self _) hz hA,
    involution_mem_sylow hC.hyp hc.std.hK'.1 hzK' hA'⟩

theorem layer_orthTag (hP : TL4.TightBelowRPlus 3 n) (h : PerpHypS n Y R S t) {c : Y}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hno : SecNoExit R c)
    (hne : (TwinDisc.secFam (Om R) c).Nonempty)
    (htr : ∀ K ∈ TwinDisc.secFam (Om R) c, ∀ L ∈ TwinDisc.secFam (Om R) c,
      ∃ x : SecQ R c, conjSub x K = L)
    {J₁ J₂ : Subgroup Y} (hJ₁ : J₁ ∈ Om R) (hJ₂ : J₂ ∈ Om R) (hne' : J₂ ≠ J₁) {w : Y}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ T₂ : Subgroup Y}
    (hT₁ : IsSylow2In T₁ J₁) (hT₂ : IsSylow2In T₂ J₂)
    (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set Y)) (hT₂c : T₂ ≤ Subgroup.centralizer ({c} : Set Y))
    (hwT₁ : w ∈ T₁) (hwT₂ : w ∈ T₂)
    (D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) c))) (hcard : D.card = 1) :
    ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool), 5 ≤ d ∧
      IsOrthTag d ε tag k ∧ CompIs 3 1 (D.kind ⟨0, by omega⟩) tag k := by
  have hC := CoreData.of_S h.core
  obtain ⟨L₁, L₂, hm₁, hm₂, hLne, wb, hw₁', hw₂'⟩ := twin_lifts_in_section hP h hc2 hc1 hno hJ₁ hJ₂
    hne' hw₁ hw₂ hT₁ hT₂ hT₁c hT₂c hwT₁ hwT₂
  have hS := p23_q8Section h hc2
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam (TwinDisc.secFam (Om R) c)) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  obtain ⟨-, hl, -, -⟩ := lieDecomp_of_noExit hC.below hP (secQ_card_lt h hc1) hS hne hno
  have hgen : omegaGen (liftFam (TwinDisc.secFam (Om R) c)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u', hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  exact orthTag_of_oneComp D hΛ hgen (liftFam_transitive h hc2 hc1 hP hne hno htr)
    ⟨L₁, hm₁, L₂, ⟨hm₂, wb, hw₁', hw₂'⟩, hLne.symm⟩ hcard ⟨0, by omega⟩

theorem e_orthTag (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e) (hmem : P23Members n)
    (htr : ∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
      ∃ x : SecQ R e, conjSub x K = L)
    (D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) e))) (hcard : D.card = 1) :
    ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool), 5 ≤ d ∧
      IsOrthTag d ε tag k ∧ CompIs 3 1 (D.kind ⟨0, by omega⟩) tag k := by
  have hC := CoreData.of_S hc.std.perp.core
  have hzK : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hc.std.hK'
  obtain ⟨A, A', hA, hA', hAe, hA'e, -, htA, htA'⟩ := exists_std_t hc
  exact layer_orthTag hP hc.std.perp hc.data.he2 hc.data.he1 hno
    (hmem Y R S t K' W u e g hc).1 htr (CoreAssembly.mem_conjClass_self _) hc.std.hK'.1
    hc.std.hne hzK hzK' hA hA' hAe hA'e htA htA' D hcard

theorem u_orthTag (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R u) (hmem : P23Members n)
    (htr : ∀ K ∈ TwinDisc.secFam (Om R) u, ∀ L ∈ TwinDisc.secFam (Om R) u,
      ∃ x : SecQ R u, conjSub x K = L)
    (D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) u))) (hcard : D.card = 1) :
    ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool), 5 ≤ d ∧
      IsOrthTag d ε tag k ∧ CompIs 3 1 (D.kind ⟨0, by omega⟩) tag k := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hzK : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hc.std.hK'
  obtain ⟨A, A', hA, hA', hAe, hA'e, -, htA, htA'⟩ := exists_std_t hc
  have hd := hc.data
  have hNe := normalizer_le_centralizer_e hd
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := by
    have : (⨆ X ∈ DSet (Om R) W, X) ≤ Subgroup.normalizer (W : Set Y) :=
      iSup₂_le fun X hX => hX.2
    exact this hd.hg
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := hNe hgN
  have hu : u = (g * t * g⁻¹) * e := by
    rw [hd.hgt, mul_assoc, hd.he2, mul_one]
  have hconj : ∀ {T : Subgroup Y}, T ≤ Subgroup.centralizer ({e} : Set Y) →
      T ≤ tightCore R ⊔ K' → (∀ x ∈ T, x * t = t * x) →
      conjSub g T ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro T hTe _ hTt
    rintro _ ⟨x, hx, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [e1, Subgroup.mem_centralizer_singleton_iff]
    have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hTe hx)
    have hge : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hye : (g * x * g⁻¹) * e = e * (g * x * g⁻¹) := by
      have hge' : g⁻¹ * e = e * g⁻¹ := by
        calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * e) * g⁻¹ := by rw [hge]
          _ = e * g⁻¹ := by group
      calc (g * x * g⁻¹) * e = g * x * (g⁻¹ * e) := by group
        _ = g * x * (e * g⁻¹) := by rw [hge']
        _ = g * (x * e) * g⁻¹ := by group
        _ = g * (e * x) * g⁻¹ := by rw [hxe]
        _ = (g * e) * x * g⁻¹ := by group
        _ = (e * g) * x * g⁻¹ := by rw [hge]
        _ = e * (g * x * g⁻¹) := by group
    have hxt := hTt x hx
    have hyt : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hxt]
        _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
    have key : (g * x * g⁻¹) * u = u * (g * x * g⁻¹) := by
      rw [hu]
      calc (g * x * g⁻¹) * ((g * t * g⁻¹) * e)
          = ((g * x * g⁻¹) * (g * t * g⁻¹)) * e := by group
        _ = ((g * t * g⁻¹) * (g * x * g⁻¹)) * e := by rw [hyt]
        _ = (g * t * g⁻¹) * ((g * x * g⁻¹) * e) := by group
        _ = (g * t * g⁻¹) * (e * (g * x * g⁻¹)) := by rw [hye]
        _ = ((g * t * g⁻¹) * e) * (g * x * g⁻¹) := by group
    exact key
  have hAt : ∀ x ∈ A, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hzK (hA.1 hx))
  have hA't : ∀ x ∈ A', x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hzK' (hA'.1 hx))
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hzK.conj g
  have hw' : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hzK'.conj g
  have hne' : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  exact layer_orthTag hP hc.std.perp hd.hu2 hd.hu1 hno (hmem Y R S t K' W u e g hc).2 htr
    (hΩ.conjInvariant g _ hK) (hΩ.conjInvariant g _ hc.std.hK'.1) hne' hw hw'
    (hA.conj g) (hA'.conj g) (hconj hAe (le_sup_of_le_left hA.1) hAt)
    (hconj hA'e (le_sup_of_le_right hA'.1) hA't)
    (by rw [← hd.hgt]; exact conj_mem_conjSub htA) (by rw [← hd.hgt]; exact conj_mem_conjSub htA')
    D hcard

end Lemmas

section TypeSteps

theorem p23E4Type_of_dim {n : ℕ} (hd : P23E4Dim n) (htr : P23E4Trans n) : P23E4Type n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno D hcard
  have htr' := htr hcit hP Y R S t K' W u e g hc hno
  obtain ⟨tag, k, d, ε, -, hort, hcis⟩ := e_orthTag hP hc hno (p23Members n) htr' D hcard
  obtain ⟨hd6, hε⟩ := hd hcit hP Y R S t K' W u e g hc hno D hcard tag k d ε hort hcis
  subst hd6 hε
  exact ⟨tag, k, hort, hcis⟩

end TypeSteps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
