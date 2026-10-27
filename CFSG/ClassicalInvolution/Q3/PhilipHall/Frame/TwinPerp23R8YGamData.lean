module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU29
public import CFSG.ClassicalInvolution.Asc77.AscT7K1
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected

section Hull

variable {Y : Type} [Group Y] [Finite Y]

@[expose] noncomputable def hcoeHom (Ω : Set (Subgroup Y)) (c : Y) : ↥(coreHull Ω c) →* Y :=
  (Subgroup.centralizer ({c} : Set Y)).subtype.comp (coreHull Ω c).subtype

theorem hcoeHom_injective (Ω : Set (Subgroup Y)) (c : Y) : Function.Injective (hcoeHom Ω c) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem hcoeHom_mem_centralizer (Ω : Set (Subgroup Y)) (c : Y) (x : ↥(coreHull Ω c)) :
    hcoeHom Ω c x ∈ Subgroup.centralizer ({c} : Set Y) :=
  (x : ↥(Subgroup.centralizer ({c} : Set Y))).2

end Hull

section Cert

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem e_decomp_W (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ (R₁ R₁' : Subgroup Y) (b₁ b' : Y), IsSylow2In R₁ (tightCore R) ∧ IsSylow2In R₁' K' ∧
      R₁ ∈ DSet (Om R) W ∧ R₁' ∈ DSet (Om R) W ∧ Commutes R₁ R₁' ∧ b₁ ∈ R₁ ∧ b' ∈ R₁' ∧
      b₁ ∈ W ∧ b' ∈ W ∧ b₁ * b₁ = t ∧ b' * b' = t ∧ u = b₁ * b' := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  have hd := hc.data
  obtain ⟨S₀, R₁, R₁', hWS, hR₁, hR₁', hRS, hR'S⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hc.std.hW hc.std.htW
  have hRD : R₁ ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK hR₁) hRS
  have hR'D : R₁' ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS
      (mem_RSet_of_isSylow2In hc.std.hK'.1 hR₁') hR'S
  have hcomm : Commutes R₁ R₁' :=
    hΩ.commutes_of_twin_of_isPGroup hK hc.std.hK'.1 hc.std.hne.symm hz hz' hR₁.1 hR₁'.1
      (S₀.isPGroup'.to_le (sup_le hRS hR'S))
  obtain ⟨b, hbRW, hb4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hc.std.hW hRD
  obtain ⟨b', hb'RW, hb'4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hc.std.hW hR'D
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hc.std.hW
  have hu := CFSG.ClassicalInvolution.Q8P.Asc77.T7E.involution_cases hs hR₁ hR₁' hRS hR'S hbRW.1
    hb'RW.1 hb4 hb'4 hd.hu (hWS hd.huW) hd.hu2 hd.hu1 hd.huz (hWab _ hd.huW _ hbRW.2)
    (hWab _ hd.huW _ hb'RW.2)
  have hbK : b ∈ tightCore R := hR₁.1 hbRW.1
  have hb'K' : b' ∈ K' := hR₁'.1 hb'RW.1
  have hbb : b * b = t := TwinPerp.sq_eq_of_orderOf_four hz hbK hb4
  have hb'b' : b' * b' = t := TwinPerp.sq_eq_of_orderOf_four hz' hb'K' hb'4
  have hztR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  have hzc : ∀ x ∈ tightCore R, t * x = x * t := fun x hx => hz.commute_of_mem hx
  obtain ⟨b₁, hb₁R, hb₁W, ob₁, hub₁⟩ : ∃ b₁ ∈ R₁, b₁ ∈ W ∧ b₁ * b₁ = t ∧ u = b₁ * b' := by
    rcases hu with hu | hu
    · exact ⟨b, hbRW.1, hbRW.2, hbb, hu⟩
    · refine ⟨t * b, R₁.mul_mem hztR hbRW.1, W.mul_mem hd.hzW hbRW.2, ?_, by rw [hu]; group⟩
      have hzb : t * b = b * t := hzc b hbK
      calc t * b * (t * b) = t * (b * t) * b := by group
        _ = t * (t * b) * b := by rw [← hzb]
        _ = (t * t) * (b * b) := by group
        _ = t := by rw [hz.sq, hbb, one_mul]
  exact ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'RW.1, hb₁W, hb'RW.2, ob₁, hb'b',
    hub₁⟩

theorem frame_at_u (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ (J₁ J₂ : Subgroup Y) (x κ₁ κ₂ vH : ↥(coreHull (Om R) u)) (v' : Y),
      J₁ ∈ tqMembers3 (Om R) u ∧ J₂ ∈ tqMembers3 (Om R) u ∧ J₂ ≠ J₁ ∧
      IsUniqueInvolution J₁ (u * e) ∧ IsUniqueInvolution J₂ (u * e) ∧
      hcoeHom (Om R) u x = u * e ∧ x * x = 1 ∧
      hcoeHom (Om R) u κ₁ ∈ W ∧ hcoeHom (Om R) u κ₂ ∈ W ∧
      κ₁ * κ₁ = x ∧ κ₂ * κ₂ = x ∧ κ₁ * κ₂ = κ₂ * κ₁ ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) κ₁ ∈ secImg (Om R) u J₁ ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) κ₂ ∈ secImg (Om R) u J₂ ∧
      IsUniqueInvolution (secImg (Om R) u J₁)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) x) ∧
      IsUniqueInvolution (secImg (Om R) u J₂)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) x) ∧
      hcoeHom (Om R) u vH = v' ∧ (t = v' ∨ t = u * v') ∧ (vH = κ₁ * κ₂ ∨ vH = κ₁⁻¹ * κ₂) ∧
      vH * vH = 1 ∧ vH * x = x * vH ∧ vH ≠ 1 ∧ vH ≠ x := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, -, hb₁R, hb'R', hb₁W, hb'W, ob₁, ob', hub⟩ :=
    e_decomp_W hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hne_ue⟩ := e_decomp hc
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
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hJ₁tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hR₃u⟩⟩
  have hJ₂tq : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩
  obtain ⟨hxC, hxY, hU₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁tq hτ₁
  obtain ⟨hxC₂, hxY₂, hU₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂tq hτ₂
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hztR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  have hk₁W : g * b₁ * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgN b₁).mp hb₁W
  have hk₂W : g * b' * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgN b').mp hb'W
  have hk₁sq : (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = u * e := by
    calc (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = g * (b₁ * b₁) * g⁻¹ := by group
      _ = u * e := by rw [ob₁, hd.hgt]
  have hk₂sq : (g * b' * g⁻¹) * (g * b' * g⁻¹) = u * e := by
    calc (g * b' * g⁻¹) * (g * b' * g⁻¹) = g * (b' * b') * g⁻¹ := by group
      _ = u * e := by rw [ob', hd.hgt]
  have hk₁₂ : (g * b₁ * g⁻¹) * (g * b' * g⁻¹) = (g * b' * g⁻¹) * (g * b₁ * g⁻¹) :=
    hWab _ hk₁W _ hk₂W
  have hcore₁ : g * b₁ * g⁻¹ ∈ TwinADescent.coreAt u (conjSub g (tightCore R)) :=
    le_tightCore_of_isPGroup (le_inf hR₃.1 hR₃u) hR₃.2.1 (conj_mem_conjSub hb₁R)
  have hcore₂ : g * b' * g⁻¹ ∈ TwinADescent.coreAt u (conjSub g K') :=
    le_tightCore_of_isPGroup (le_inf hR₃'.1 hR₃'u) hR₃'.2.1 (conj_mem_conjSub hb'R')
  obtain ⟨κ₁, hκ₁v, hκ₁m⟩ := exists_hull_elt hJ₁tq hcore₁
  obtain ⟨κ₂, hκ₂v, hκ₂m⟩ := exists_hull_elt hJ₂tq hcore₂
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hv₁ : hcoeHom (Om R) u κ₁ = g * b₁ * g⁻¹ := hκ₁v
  have hv₂ : hcoeHom (Om R) u κ₂ = g * b' * g⁻¹ := hκ₂v
  set x : ↥(coreHull (Om R) u) := ⟨⟨u * e, hxC⟩, hxY⟩ with hxdef
  have hvx : hcoeHom (Om R) u x = u * e := rfl
  have hinj := hcoeHom_injective (Om R) u
  have hue2 : (u * e) * (u * e) = 1 := ue_sq hc
  have hxx : x * x = 1 := hinj (by rw [map_mul, hvx, hue2, map_one])
  have hκ₁sq : κ₁ * κ₁ = x := hinj (by rw [map_mul, hv₁, hvx, hk₁sq])
  have hκ₂sq : κ₂ * κ₂ = x := hinj (by rw [map_mul, hv₂, hvx, hk₂sq])
  have hκ₁₂ : κ₁ * κ₂ = κ₂ * κ₁ := hinj (by rw [map_mul, map_mul, hv₁, hv₂, hk₁₂])
  have hk₁4 : (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) * ((g * b₁ * g⁻¹) * (g * b₁ * g⁻¹)) = 1 := by
    rw [hk₁sq]; exact hue2
  obtain ⟨v', hv'form, hzv⟩ := z_cases hc
  have hgug : g * u * g⁻¹ = (g * b₁ * g⁻¹) * (g * b' * g⁻¹) := by rw [hub]; group
  have hvcases : ∃ vH : ↥(coreHull (Om R) u), hcoeHom (Om R) u vH = v' ∧
      (vH = κ₁ * κ₂ ∨ vH = κ₁⁻¹ * κ₂) := by
    rcases hv'form with h | h
    · exact ⟨κ₁ * κ₂, by rw [map_mul, hv₁, hv₂, h, hgug], Or.inl rfl⟩
    · refine ⟨κ₁⁻¹ * κ₂, ?_, Or.inr rfl⟩
      rw [map_mul, map_inv, hv₁, hv₂, h, hgug, ← hk₁sq]
      set k₁ := g * b₁ * g⁻¹
      set k₂ := g * b' * g⁻¹
      have e1 : k₁⁻¹ = k₁ * k₁ * k₁ := by
        have : k₁ * (k₁ * k₁ * k₁) = 1 := by
          calc k₁ * (k₁ * k₁ * k₁) = k₁ * k₁ * (k₁ * k₁) := by group
            _ = 1 := hk₁4
        exact inv_eq_of_mul_eq_one_right this
      rw [e1]
      calc k₁ * k₁ * k₁ * k₂ = k₁ * k₁ * (k₁ * k₂) := by group
        _ = k₁ * k₁ * (k₂ * k₁) := by rw [hk₁₂]
        _ = k₁ * (k₁ * k₂) * k₁ := by group
        _ = k₁ * (k₂ * k₁) * k₁ := by rw [hk₁₂]
        _ = k₁ * k₂ * (k₁ * k₁) := by group
  obtain ⟨vH, hvH, hvHform⟩ := hvcases
  have hut : u * t = t * u := comm_ut hc
  have hu2 := hd.hu2
  have ht2 : t * t = 1 := hz.sq
  have hWt : t ∈ W := hd.hzW
  have hWu : u ∈ W := hd.huW
  have hWe : e ∈ W := (T7K.e_mem_inf hd).1
  have hWue : u * e ∈ W := W.mul_mem hWu hWe
  have hv'cases : v' = t ∨ v' = u * t := by
    rcases hzv with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      calc v' = u * (u * v') := by rw [← mul_assoc, hu2, one_mul]
        _ = u * t := by rw [← h]
  have hv'W : v' ∈ W := by
    rcases hv'cases with h | h
    · rw [h]; exact hWt
    · rw [h]; exact W.mul_mem hWu hWt
  have hv'2 : v' * v' = 1 := by
    rcases hv'cases with h | h
    · rw [h]; exact ht2
    · rw [h]
      calc u * t * (u * t) = u * (t * u) * t := by group
        _ = u * (u * t) * t := by rw [← hut]
        _ = (u * u) * (t * t) := by group
        _ = 1 := by rw [hu2, ht2, one_mul]
  have hv'x : v' * (u * e) = (u * e) * v' := hWab _ hv'W _ hWue
  have hv'1 : v' ≠ 1 := by
    rcases hv'cases with h | h
    · rw [h]; exact hz.ne_one
    · rw [h]
      intro h1
      apply hd.huz
      calc u = u * t * t := by rw [mul_assoc, ht2, mul_one]
        _ = 1 * t := by rw [h1]
        _ = t := one_mul t
  have hv'x1 : v' ≠ u * e := by
    rcases hv'cases with h | h
    · rw [h]; exact fun h' => hne_ue h'.symm
    · rw [h]
      intro h1
      apply e_not_mem_sup hc
      have : t = e := mul_left_cancel h1
      rw [← this]
      exact Subgroup.mem_sup_left hz.mem
  refine ⟨conjSub g (tightCore R), conjSub g K', x, κ₁, κ₂, vH, v', hJ₁tq, hJ₂tq, hne₂, hτ₁, hτ₂,
    hvx, hxx, by rw [hv₁]; exact hk₁W, by rw [hv₂]; exact hk₂W, hκ₁sq, hκ₂sq, hκ₁₂, hκ₁m, hκ₂m, hU₁,
    hU₂, hvH, hzv, hvHform, ?_, ?_, ?_, ?_⟩
  · exact hinj (by rw [map_mul, hvH, hv'2, map_one])
  · exact hinj (by rw [map_mul, map_mul, hvH, hvx, hv'x])
  · exact fun h => hv'1 (by rw [← hvH, h, map_one])
  · exact fun h => hv'x1 (by rw [← hvH, h, hvx])

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
