module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace E4M



variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem e_frame_sec (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ (A A' B : Subgroup (SecQ R e)) (z u₁ u₂ τ ε₀ : SecQ R e),
      TwinFrame (TwinDisc.secFam (Om R) e) A A' B z u₁ u₂ τ ε₀ ∧
        (∀ M ∈ TwinDisc.secFam (Om R) e, M ∈ omegaNbr (TwinDisc.secFam (Om R) e) A → M = A') ∧
        (∀ M ∈ TwinDisc.secFam (Om R) e, M ∈ omegaNbr (TwinDisc.secFam (Om R) e) A' → M = A) := by
  classical
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁e⟩⟩
  have hK'tq : K' ∈ tqMembers3 (Om R) e :=
    ⟨hc.std.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hc.std.hK'.1 ⟨R₁', hR₁', hR₁'e⟩⟩
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := by
    have : (⨆ X ∈ DSet (Om R) W, X) ≤ Subgroup.normalizer (W : Set Y) :=
      iSup₂_le fun X hX => hX.2
    exact this hd.hg
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := hNe hgN
  have hJ₃ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃e : conjSub g R₁ ≤ Subgroup.centralizer ({e} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC (hR₁e hx)) (Subgroup.inv_mem _ hgC)
  have hJ₃tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) e :=
    ⟨hJ₃, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₃ ⟨conjSub g R₁, hR₃, hR₃e⟩⟩
  have hτ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hS := p23_q8Section hc.std.perp hd.he2
  have hlt := secQ_card_lt hc.std.perp hd.he1
  have hztR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  have hcoreT : t ∈ TwinADescent.coreAt e (tightCore R) :=
    le_tightCore_of_isPGroup (le_inf hR₁.1 hR₁e) hR₁.2.1 hztR
  have hcoreB : b₁ ∈ TwinADescent.coreAt e (tightCore R) :=
    le_tightCore_of_isPGroup (le_inf hR₁.1 hR₁e) hR₁.2.1 hb₁R
  have hcoreB' : b' ∈ TwinADescent.coreAt e K' :=
    le_tightCore_of_isPGroup (le_inf hR₁'.1 hR₁'e) hR₁'.2.1 hb'R'
  have hcoreτ : u * e ∈ TwinADescent.coreAt e (conjSub g (tightCore R)) := by
    have := le_tightCore_of_isPGroup (le_inf hR₃.1 hR₃e) hR₃.2.1
      (conj_mem_conjSub hztR : g * t * g⁻¹ ∈ conjSub g R₁)
    rwa [hd.hgt] at this
  obtain ⟨wH, hwHv, hwHm⟩ := exists_hull_elt hKtq hcoreT
  obtain ⟨b₁H, hb₁Hv, hb₁Hm⟩ := exists_hull_elt hKtq hcoreB
  obtain ⟨b'H, hb'Hv, hb'Hm⟩ := exists_hull_elt hK'tq hcoreB'
  obtain ⟨τH, hτHv, hτHm⟩ := exists_hull_elt hJ₃tq hcoreτ
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) e) with hN
  have hv : ∀ x y : ↥(coreHull (Om R) e),
      (((x * y : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) *
          ((y : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) := fun _ _ => rfl
  have hext : ∀ x y : ↥(coreHull (Om R) e),
      ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        ((y : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  obtain ⟨eH, heH⟩ : ∃ eH : ↥(coreHull (Om R) e), eH = (b₁H * b'H)⁻¹ * τH := ⟨_, rfl⟩
  have heHv : ((eH : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = e := by
    have h1 : (((b₁H * b'H : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        b₁ * b' := by rw [hv, hb₁Hv, hb'Hv]
    have h2 : ((((b₁H * b'H)⁻¹ : ↥(coreHull (Om R) e)) :
        ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = (b₁ * b')⁻¹ := by rw [← h1]; rfl
    rw [heH]
    show ((((b₁H * b'H)⁻¹ : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) *
      ((τH : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = e
    rw [h2, hτHv, hub]
    group
  have hrelH : τH = b₁H * b'H * eH := by
    rw [heH]; group
  have hecen : QuotientGroup.mk' N eH ∈ Subgroup.center (↥(coreHull (Om R) e) ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_mul, ← map_mul]
    congr 1
    apply hext
    rw [hv, hv, heHv]
    exact Subgroup.mem_centralizer_singleton_iff.mp y.1.2
  have he2' : eH * eH = 1 := by
    apply hext
    rw [hv, heHv]
    exact hd.he2
  have he1' : QuotientGroup.mk' N eH ≠ 1 := by
    intro h1
    have hmem : eH ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have := CFSG.ClassicalInvolution.Asc77.T7H.eq_one_of_mem_odd_of_sq
      (CFSG.ComponentClassification.OddCore.odd_card _) hmem he2'
    apply hd.he1
    have := congrArg (fun x : ↥(coreHull (Om R) e) => ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y))
      this
    simpa [heHv] using this
  obtain ⟨htC, htY, hzA⟩ := isUniqueInvolution_secImg hΩ hc2' hKtq hz
  obtain ⟨htC', htY', hzA'⟩ := isUniqueInvolution_secImg hΩ hc2' hK'tq hz'
  obtain ⟨hτC, hτY, hτA⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₃tq hτ
  have hwHeq : wH = ⟨⟨t, htC⟩, htY⟩ := hext _ _ hwHv
  have hτHeq : τH = ⟨⟨u * e, hτC⟩, hτY⟩ := hext _ _ hτHv
  rw [hwHeq] at hwHm
  have hzA₁ : IsUniqueInvolution (secImg (Om R) e (tightCore R)) (QuotientGroup.mk' N wH) := by
    rw [hwHeq]; exact hzA
  have hzA₂ : IsUniqueInvolution (secImg (Om R) e K') (QuotientGroup.mk' N wH) := by
    rw [hwHeq]; exact hzA'
  have hτA' : IsUniqueInvolution (secImg (Om R) e (conjSub g (tightCore R)))
      (QuotientGroup.mk' N τH) := by
    rw [hτHeq]; exact hτA

  have hne_img := secImg_ne_of_twins hΩ hc2' hKtq hK'tq hc.std.hne hz hz'
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  have hnb : ∀ M ∈ TwinDisc.secFam (Om R) e,
      M ∈ omegaNbr (TwinDisc.secFam (Om R) e) (secImg (Om R) e (tightCore R)) →
        M = secImg (Om R) e K' := by
    intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hKtq hJ₀
      (fun J₀' hJ₀' hp => hp₁ J₀' hJ₀'.1 hp) hMn
  have hnb' : ∀ M ∈ TwinDisc.secFam (Om R) e,
      M ∈ omegaNbr (TwinDisc.secFam (Om R) e) (secImg (Om R) e K') →
        M = secImg (Om R) e (tightCore R) := by
    intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hK'tq hJ₀
      (fun J₀' hJ₀' hp => hp₂ J₀' hJ₀'.1 hp) hMn
  refine ⟨secImg (Om R) e (tightCore R), secImg (Om R) e K',
    secImg (Om R) e (conjSub g (tightCore R)), QuotientGroup.mk' N wH, QuotientGroup.mk' N b₁H,
    QuotientGroup.mk' N b'H, QuotientGroup.mk' N τH, QuotientGroup.mk' N eH,
    ⟨secImg_mem_secFam hKtq, secImg_mem_secFam hK'tq, secImg_mem_secFam hJ₃tq, hne_img, hzA₁, hzA₂,
      hb₁Hm, hb'Hm, ?_, ?_, hτA', hecen, ?_, he1', ?_⟩, hnb, hnb'⟩
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, hb₁Hv, hwHv]
    exact ob₁
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, hb'Hv, hwHv]
    exact ob'
  · rw [← map_mul, he2', map_one]
  · rw [← map_mul, ← map_mul, ← hrelH]

end E4M

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
