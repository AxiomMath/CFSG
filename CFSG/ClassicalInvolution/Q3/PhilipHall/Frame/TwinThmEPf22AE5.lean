module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf19Sect

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Ae5Branch


theorem e189AE5Q8_proved : E189AE5Q8 := by
  intro G _ _ Ω K S R W H c _h6 h7 _h4 z t k hz htk _hkH hzt htz hne Y Λ hdata hI
  obtain ⟨I⟩ := hI
  obtain ⟨hYH, hKY, hJY, hΛsub, hΛc, hKΛ, hJΛ, hgen, -, hE⟩ := hdata
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
  have hΦ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hΛ : HypOmegaGen Λ := hypOmegaGen_of_sub hΦ hΛsub hΛc
  have hΛq8 := fun L (hL : L ∈ Λ) => q8_restrict c.stand.q8 Y L (hΛsub hL)
  have hΛ2 := fun L (hL : L ∈ Λ) => two_restrict c.stand.two Y L (hΛsub hL)
  have hΛA : ∀ L ∈ Λ, AEmpty Λ L :=
    aEmpty_of_sub hΦ hΛsub fun L hL => by
      obtain ⟨L₀, hL₀, hL₀Y, rfl⟩ := hL
      exact AEmpty.restrict hΩ hL₀Y (hAΩ L₀ hL₀)
  have hzY : z ∈ Y := hKY hz.mem
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  have hzJ : IsUniqueInvolution (conjSub k K) t := by
    have := hz.conj k
    rwa [← htk] at this
  have htY : t ∈ Y := hJY hzJ.mem
  have ht' := isUniqueInvolution_subgroupOf hzJ hJY
  have ht2 : t * t = 1 := hzJ.sq
  have ha2 : (z * t) * (z * t) = 1 := mul_involution_of_commute hz.sq ht2 hzt
  have ha1 : z * t ≠ 1 := by
    intro h1
    apply htz
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  obtain ⟨K'', hK''tw, hK''ne⟩ := hE
  obtain ⟨z', hz'K, hz'K''⟩ := hK''tw.2
  have hzz : z' = (⟨z, hzY⟩ : ↥Y) := hz'K.eq hz'
  subst hzz
  have hKstw : K''.map Y.subtype ∈ twinSet Ω K :=
    map_mem_twinSet_restrict hKY (⟨hΛsub hK''tw.1, hK''tw.2⟩ :
      K'' ∈ twinSet (restrictFamily Ω Y) (K.subgroupOf Y))
  have hKsΩ : K''.map Y.subtype ∈ Ω := hKstw.1
  obtain ⟨z₂, hz₂K, hz₂Ks⟩ := hKstw.2
  have hz₂z : z₂ = z := hz₂K.eq hz
  have hz₂Ks' : IsUniqueInvolution (K''.map Y.subtype) z := hz₂z ▸ hz₂Ks
  obtain ⟨hRΩ, hRK, -⟩ := c.stand.hR
  obtain ⟨M₀, -, hRM₀⟩ := exists_isSylow2In_of_mem_RSet hRΩ
  have hRY : R ≤ Y := hRK.trans hKY
  have hRY2 : IsPGroup 2 ↥(R.subgroupOf Y) :=
    hRM₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  obtain ⟨PY, hPY⟩ := hRY2.exists_le_sylow
  have hPY2 : IsPGroup 2 ↥(PY.map Y.subtype) := PY.isPGroup'.map Y.subtype
  obtain ⟨S₂, hS₂⟩ := hPY2.exists_le_sylow
  have hPYS₂ : ∀ y ∈ (PY : Subgroup ↥Y), (y : G) ∈ (S₂ : Subgroup G) := fun y hy =>
    hS₂ ⟨y, hy, rfl⟩
  have hRS₂ : R ≤ (S₂ : Subgroup G) := fun x hx =>
    hPYS₂ ⟨x, hRY hx⟩ (hPY (Subgroup.mem_subgroupOf.mpr hx))
  obtain ⟨x, -, -, hW₂, hW₂S, hW₂n, hCW₂⟩ :=
    exists_W_of_sylow hΩ hK c.hyp.trans hz hzH c.stand.hR.1 c.stand.hR.2.1 c.stand.hR.2.2
      c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hRΩ hRK hRS₂
  have hW₂abel : ∀ a ∈ conjSub x W, ∀ b ∈ conjSub x W, a * b = b * a := by
    obtain ⟨η, hη, hWη⟩ := hW₂
    obtain ⟨S₁, hS₁, hinv⟩ := hη
    have := etaAbelian_of_gen hΩ S₁ η hS₁ hinv
    rwa [← hWη] at this
  obtain ⟨x₀, hx₀, hx₀4, hx₀R⟩ := exists_order_four_inf_W hΩ hW₂ hW₂S hK hRΩ hRK hRS₂
  have hx₀sq : x₀ * x₀ = z := by
    have h4' : (x₀ * x₀) * (x₀ * x₀) = 1 := by
      have : x₀ ^ 4 = 1 := by rw [← hx₀4]; exact pow_orderOf_eq_one x₀
      calc (x₀ * x₀) * (x₀ * x₀) = x₀ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    rcases hz.unique (x₀ * x₀) (K.mul_mem hx₀.1 hx₀.1) h4' with h | h
    · exfalso
      have : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx₀4] at this
      omega
    · exact h
  have hzt' : (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hztc' : (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  obtain ⟨s, hsP, hsK, hs⟩ := Ae5Q8.ae5_sect_main hΛ hΛ2 hΛq8 hΛA hgen I hKΛ hK''tw.1 hK''ne hz'
    hz'K'' hJΛ ht' hzt' hztc' PY
  have hx₀' : (⟨x₀, hKY hx₀.1⟩ : ↥Y) ∈ K.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx₀.1
  obtain ⟨g, n, hnc, hnodd, hgn⟩ := hs ⟨x₀, hKY hx₀.1⟩ hx₀' (Subtype.ext hx₀sq)
  set y₀ : G := (s : G) * x₀ * (s : G)⁻¹ with hy₀
  have hy₀K : y₀ ∈ K''.map Y.subtype := by
    have h1 : s * ⟨x₀, hKY hx₀.1⟩ * s⁻¹ ∈ K'' := hsK ▸ conj_mem_conjSub hx₀'
    exact ⟨_, h1, rfl⟩
  have hsS₂ : (s : G) ∈ (S₂ : Subgroup G) := hPYS₂ s hsP
  have hy₀W : y₀ ∈ conjSub x W := by
    have := conj_mem_conjSub (n := (s : G)) hx₀.2
    rwa [hW₂n _ hsS₂] at this
  have hy₀sq : y₀ * y₀ = z := by
    have h1 : y₀ * y₀ = (s : G) * z * (s : G)⁻¹ := by
      calc y₀ * y₀ = (s : G) * (x₀ * x₀) * (s : G)⁻¹ := by rw [hy₀]; group
        _ = (s : G) * z * (s : G)⁻¹ := by rw [hx₀sq]
    have h2 : (y₀ * y₀) * (y₀ * y₀) = 1 := by
      rw [h1]
      calc (s : G) * z * (s : G)⁻¹ * ((s : G) * z * (s : G)⁻¹) = (s : G) * (z * z) * (s : G)⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    rcases hz₂Ks'.unique (y₀ * y₀) ((K''.map Y.subtype).mul_mem hy₀K hy₀K) h2 with h | h
    · exfalso
      apply hz.ne_one
      have h3 : (s : G) * z * (s : G)⁻¹ = 1 := by rw [← h1]; exact h
      have : z = (s : G)⁻¹ * ((s : G) * z * (s : G)⁻¹) * (s : G) := by group
      rw [this, h3]
      group
    · exact h
  have hxy : x₀ * y₀ = y₀ * x₀ := hW₂abel x₀ hx₀.2 y₀ hy₀W
  have hv2 : (x₀ * y₀) * (x₀ * y₀) = 1 := by
    calc (x₀ * y₀) * (x₀ * y₀) = x₀ * (y₀ * x₀) * y₀ := by group
      _ = x₀ * (x₀ * y₀) * y₀ := by rw [hxy]
      _ = (x₀ * x₀) * (y₀ * y₀) := by group
      _ = 1 := by rw [hx₀sq, hy₀sq, hz.sq]
  have hgn' : (g : G) * (z * t) * (g : G)⁻¹ = x₀ * y₀ := by
    set vY : ↥Y := (⟨x₀, hKY hx₀.1⟩ : ↥Y) * (s * ⟨x₀, hKY hx₀.1⟩ * s⁻¹) with hvY
    have hv2Y : vY * vY = 1 := Subtype.ext hv2
    have hu2Y : (g * ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) * g⁻¹) *
        (g * ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) * g⁻¹) = 1 := by
      calc (g * ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) * g⁻¹) * (g * ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) * g⁻¹)
          = g * (((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) * ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩)) * g⁻¹ := by group
        _ = 1 := by
          rw [show ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) * ((⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩) = 1 from
            Subtype.ext ha2]
          group
    have hnn : n * n = 1 := by
      rw [hgn] at hu2Y
      have hcn : n * vY = vY * n := (Subgroup.mem_center_iff.mp hnc vY).symm
      have h3 : (vY * n) * (vY * n) = (vY * vY) * (n * n) := by
        calc (vY * n) * (vY * n) = vY * (n * vY) * n := by group
          _ = vY * (vY * n) * n := by rw [hcn]
          _ = (vY * vY) * (n * n) := by group
      rw [h3, hv2Y, one_mul] at hu2Y
      exact hu2Y
    have hn1 : n = 1 := Ae5Q8.eq_one_of_odd_orderOf hnn hnodd
    rw [hn1, mul_one] at hgn
    exact congrArg Subtype.val hgn
  have hgH : (g : G) ∈ H := hYH g.2
  have ha1' : x₀ * y₀ ≠ 1 := by
    intro h
    apply ha1
    have : z * t = (g : G)⁻¹ * (x₀ * y₀) * (g : G) := by rw [← hgn']; group
    rw [this, h]
    group
  have hKW₂ : K ⊓ conjSub x W ∈ USet Ω := inf_W_mem_USet' hΩ hW₂ hW₂S hK hRΩ hRK hRS₂
  have hKperp : K''.map Y.subtype ∈ KPerp Ω K := mem_kPerp_of_twin_gen' hΩ hKsΩ hK hz₂Ks' hz
  have hR₂Ω : conjSub (s : G) R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ (s : G)
  have hR₂S₂ : conjSub (s : G) R ≤ (S₂ : Subgroup G) := by
    intro v hv
    have h1 : (s : G)⁻¹ * v * (s : G) ∈ R := mem_conjSub_iff.mp hv
    have h2 : (s : G) * ((s : G)⁻¹ * v * (s : G)) * (s : G)⁻¹ ∈ (S₂ : Subgroup G) :=
      S₂.mul_mem (S₂.mul_mem hsS₂ (hRS₂ h1)) (S₂.inv_mem hsS₂)
    simpa [mul_assoc] using h2
  have hR₂K : conjSub (s : G) R ≤ K''.map Y.subtype := by
    intro v hv
    have h1 : (s : G)⁻¹ * v * (s : G) ∈ R := mem_conjSub_iff.mp hv
    have h2 : (⟨(s : G)⁻¹ * v * (s : G), hKY (hRK h1)⟩ : ↥Y) ∈ K.subgroupOf Y :=
      Subgroup.mem_subgroupOf.mpr (hRK h1)
    have h3 : s * ⟨(s : G)⁻¹ * v * (s : G), hKY (hRK h1)⟩ * s⁻¹ ∈ K'' := hsK ▸ conj_mem_conjSub h2
    refine ⟨_, h3, ?_⟩
    show (s : G) * ((s : G)⁻¹ * v * (s : G)) * (s : G)⁻¹ = v
    group
  have hC : Subgroup.centralizer ({x₀ * y₀} : Set G) ≤ H :=
    hCW₂ K hK hKW₂ _ hKperp R (conjSub (s : G) R) hRΩ hRK hRS₂ hR₂Ω hR₂K hR₂S₂
      (commutes_or_eq_of_le_sylow hΩ hRΩ hR₂Ω hRS₂ hR₂S₂) (x₀ * y₀)
      (Subgroup.mul_mem_sup hx₀R (conj_mem_conjSub (n := (s : G)) hx₀R))
      ((conjSub x W).mul_mem hx₀.2 hy₀W) ha1' hv2
  have hCa : Subgroup.centralizer ({z * t} : Set G) ≤ H := by
    intro c' hc'
    rw [Subgroup.mem_centralizer_singleton_iff] at hc'
    have hc'' : (g : G) * c' * (g : G)⁻¹ ∈ Subgroup.centralizer ({x₀ * y₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hgn']
      calc (g : G) * c' * (g : G)⁻¹ * ((g : G) * (z * t) * (g : G)⁻¹)
          = (g : G) * (c' * (z * t)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((z * t) * c') * (g : G)⁻¹ := by rw [hc']
        _ = (g : G) * (z * t) * (g : G)⁻¹ * ((g : G) * c' * (g : G)⁻¹) := by group
    have h2 : (g : G)⁻¹ * ((g : G) * c' * (g : G)⁻¹) * (g : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hgH) (hC hc'')) hgH
    simpa [mul_assoc] using h2
  exact fixesUniqueCoset_of_centralizer_le hCa (h7 G Ω K S R W H c (z * t) ha1 ha2 hCa)

end Ae5Branch

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
