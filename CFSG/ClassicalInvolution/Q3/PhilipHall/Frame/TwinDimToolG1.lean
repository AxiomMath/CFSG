module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1c
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY2b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



section U1

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem nbr_liftFam_eq {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hΩ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hl : HasLifts Φ) (hex : ExactSylow Φ) {A₀ A₀' : Subgroup X}
    (hA₀ : A₀ ∈ Φ) (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A₀ → M = A₀') {MA MA' : Subgroup X}
    (hMA : MA ∈ liftFam Φ) (hMA' : MA' ∈ liftFam Φ) (hle : A₀ ≤ MA) (hle' : A₀' ≤ MA') :
    ∀ M ∈ liftFam Φ, M ∈ omegaNbr (liftFam Φ) MA → M = MA' := by
  intro M hM hMn
  obtain ⟨J, hJΦ, hJN⟩ := exists_core_of_mem_liftFam hM
  have hJ := (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hMA hA₀ hle hM hJΦ hJN).mp hMn
  have hJeq := hnb J hJΦ hJ
  subst hJeq
  exact liftFam_eq_of_le hΩ hM hMA' hJΦ hJN hle'

theorem u_frame_full (hc : P23Cfg n Y R S t K' W u e g) (hP : TL4.TightBelowRPlus 3 n)
    (hno : SecNoExit R u) :
    ∃ (τH vH : ↥(coreHull (Om R) u)) (v' : Y) (A A' : Subgroup (SecQ R u)) (a₀ b₀ : SecQ R u),
      ((τH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = u * e ∧
      ((vH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = v' ∧
      (v' = g * u * g⁻¹ ∨ v' = g * u * g⁻¹ * (u * e)) ∧ (t = v' ∨ t = u * v') ∧
      TwinSect (liftFam (TwinDisc.secFam (Om R) u)) A A'
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) τH) a₀ b₀
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) vH) ∧
      ∃ J₁ ∈ tqMembers3 (Om R) u, IsUniqueInvolution J₁ (u * e) ∧
        IsUniqueInvolution (secImg (Om R) u J₁)
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) τH) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hR₃u := conj_cent_u hc hR₁e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz (hR₁.1 hx)))
  have hR₃'u := conj_cent_u hc hR₁'e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz' (hR₁'.1 hx)))
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hc.std.hK'.1
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hJ₁tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hR₃u⟩⟩
  have hJ₂tq : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hS := p23_q8Section hc.std.perp hd.hu2
  have hlt := secQ_card_lt hc.std.perp hd.hu1
  obtain ⟨h2X, hl, hex⟩ := lifts_of_noExit hP hlt hS hno
  have hztR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  set a₂ := g * b₁ * g⁻¹ with ha₂
  set b₂ := g * b' * g⁻¹ with hb₂
  have ha₂sq : a₂ * a₂ = u * e := by
    calc a₂ * a₂ = g * (b₁ * b₁) * g⁻¹ := by rw [ha₂]; group
      _ = u * e := by rw [ob₁, hd.hgt]
  have hb₂sq : b₂ * b₂ = u * e := by
    calc b₂ * b₂ = g * (b' * b') * g⁻¹ := by rw [hb₂]; group
      _ = u * e := by rw [ob', hd.hgt]
  have hcorea : a₂ ∈ TwinADescent.coreAt u (conjSub g (tightCore R)) :=
    le_tightCore_of_isPGroup (le_inf hR₃.1 hR₃u) hR₃.2.1 (conj_mem_conjSub hb₁R)
  have hcoreb : b₂ ∈ TwinADescent.coreAt u (conjSub g K') :=
    le_tightCore_of_isPGroup (le_inf hR₃'.1 hR₃'u) hR₃'.2.1 (conj_mem_conjSub hb'R')
  have hcoreτ : u * e ∈ TwinADescent.coreAt u (conjSub g (tightCore R)) := by
    have := le_tightCore_of_isPGroup (le_inf hR₃.1 hR₃u) hR₃.2.1
      (conj_mem_conjSub hztR : g * t * g⁻¹ ∈ conjSub g R₁)
    rwa [hd.hgt] at this
  obtain ⟨a₂H, ha₂Hv, ha₂Hm⟩ := exists_hull_elt hJ₁tq hcorea
  obtain ⟨b₂H, hb₂Hv, hb₂Hm⟩ := exists_hull_elt hJ₂tq hcoreb
  obtain ⟨τH, hτHv, hτHm⟩ := exists_hull_elt hJ₁tq hcoreτ
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hv : ∀ x y : ↥(coreHull (Om R) u),
      (((x * y : ↥(coreHull (Om R) u)) : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) =
        ((x : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) *
          ((y : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) := fun _ _ => rfl
  have hext : ∀ x y : ↥(coreHull (Om R) u),
      ((x : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) =
        ((y : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  obtain ⟨hτC, hτY, hτA⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₁tq hτ₁
  obtain ⟨hτC', hτY', hτA'⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₂tq hτ₂
  have hτHeq : τH = ⟨⟨u * e, hτC⟩, hτY⟩ := hext _ _ hτHv
  have hzA₁ : IsUniqueInvolution (secImg (Om R) u (conjSub g (tightCore R)))
      (QuotientGroup.mk' N τH) := by
    rw [hτHeq]; exact hτA
  have hzA₂ : IsUniqueInvolution (secImg (Om R) u (conjSub g K')) (QuotientGroup.mk' N τH) := by
    rw [hτHeq]; exact hτA'
  obtain ⟨v', hv'form, hzv⟩ := z_cases hc
  have ha₂b₂ : g * u * g⁻¹ = a₂ * b₂ := by rw [ha₂, hb₂, hub]; group
  have hτcomm : (u * e) * b₂ = b₂ * (u * e) :=
    (hτ₂.commute_of_mem (hR₃'.1 (conj_mem_conjSub hb'R')))
  obtain ⟨vH, hvHv, hwform⟩ : ∃ vH : ↥(coreHull (Om R) u),
      ((vH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = v' ∧
        (QuotientGroup.mk' N vH = QuotientGroup.mk' N a₂H * QuotientGroup.mk' N b₂H ∨
          QuotientGroup.mk' N vH = (QuotientGroup.mk' N a₂H)⁻¹ * QuotientGroup.mk' N b₂H) := by
    rcases hv'form with h | h
    · refine ⟨a₂H * b₂H, by rw [hv, ha₂Hv, hb₂Hv, h, ha₂b₂], Or.inl (map_mul _ _ _)⟩
    · refine ⟨a₂H * b₂H * τH, by rw [hv, hv, ha₂Hv, hb₂Hv, hτHv, h, ha₂b₂], Or.inr ?_⟩
      have : a₂H * b₂H * τH = a₂H⁻¹ * b₂H := by
        apply hext
        rw [hv, hv, hv, ha₂Hv, hb₂Hv, hτHv]
        have hinv : ((a₂H⁻¹ : ↥(coreHull (Om R) u)) : ↥(Subgroup.centralizer ({u} : Set Y))).1 =
            a₂⁻¹ := by
          show ((a₂H : ↥(Subgroup.centralizer ({u} : Set Y))).1)⁻¹ = a₂⁻¹
          rw [ha₂Hv]
        rw [hinv]
        have h1 : a₂⁻¹ = a₂ * (u * e) := by
          have h4 : a₂ * (a₂ * (u * e)) = 1 := by
            have e1 : a₂ * (a₂ * (u * e)) = (a₂ * a₂) * (u * e) := by group
            rw [e1, ha₂sq]
            exact hτ₁.sq
          exact inv_eq_of_mul_eq_one_right h4
        rw [h1, mul_assoc, ← hτcomm]
        group
      rw [this, map_mul, map_inv]
  obtain ⟨LA, uA, hLA⟩ := hl _ (secImg_mem_secFam hJ₁tq)
  obtain ⟨LA', uA', hLA'⟩ := hl _ (secImg_mem_secFam hJ₂tq)
  have hMA := satU_mem_liftFam (secImg_mem_secFam hJ₁tq) hLA
  have hMA' := satU_mem_liftFam (secImg_mem_secFam hJ₂tq) hLA'
  have hne_img := secImg_ne_of_twins hΩ hc2' hJ₁tq hJ₂tq hne₂ hτ₁ hτ₂
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  have hnb : ∀ M ∈ TwinDisc.secFam (Om R) u,
      M ∈ omegaNbr (TwinDisc.secFam (Om R) u) (secImg (Om R) u (conjSub g (tightCore R))) →
        M = secImg (Om R) u (conjSub g K') := by
    intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hJ₁tq hJ₀
      (fun J₀' hJ₀' hp => perp_conj_pair hΩ hp₁ g J₀' hJ₀'.1 hp) hMn
  have hnb' : ∀ M ∈ TwinDisc.secFam (Om R) u,
      M ∈ omegaNbr (TwinDisc.secFam (Om R) u) (secImg (Om R) u (conjSub g K')) →
        M = secImg (Om R) u (conjSub g (tightCore R)) := by
    intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hJ₂tq hJ₀
      (fun J₀' hJ₀' hp => perp_conj_pair hΩ hp₂ g J₀' hJ₀'.1 hp) hMn
  refine ⟨τH, vH, v', satU (.sl2 3 1) LA uA, satU (.sl2 3 1) LA' uA', QuotientGroup.mk' N a₂H,
    QuotientGroup.mk' N b₂H, hτHv, hvHv, hv'form, hzv, ⟨hMA, hMA', ?_,
    isUniqueInvolution_liftFam_of_le hMA hzA₁ hLA.le_sat,
    isUniqueInvolution_liftFam_of_le hMA' hzA₂ hLA'.le_sat, hLA.le_sat ha₂Hm, hLA'.le_sat hb₂Hm,
    ?_, ?_, hwform, ?_, ?_, ?_⟩, ⟨_, hJ₁tq, hτ₁, hzA₁⟩⟩
  · intro h
    exact hne_img (hex.core_unique hS.hyp h2X hMA (secImg_mem_secFam hJ₁tq)
      (secImg_mem_secFam hJ₂tq) hLA.le_sat (by rw [h]; exact hLA'.le_sat))
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, ha₂Hv, hτHv]
    exact ha₂sq
  · rw [← map_mul]
    congr 1
    apply hext
    rw [hv, hb₂Hv, hτHv]
    exact hb₂sq
  · intro L hL
    obtain ⟨Jb, hJb, hJbL⟩ := exists_core_of_mem_liftFam hL
    obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hJb
    obtain ⟨m, hm, hmne⟩ := no_member_commutes_q8 hc hzv vH hvHv J hJ
    exact ⟨m, hJbL hm, hmne⟩
  · exact nbr_liftFam_eq hS.hyp h2X hl hex (secImg_mem_secFam hJ₁tq) hnb hMA hMA' hLA.le_sat
      hLA'.le_sat
  · exact nbr_liftFam_eq hS.hyp h2X hl hex (secImg_mem_secFam hJ₂tq) hnb' hMA' hMA hLA'.le_sat
      hLA.le_sat

end U1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
