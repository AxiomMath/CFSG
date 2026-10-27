module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf22AE5Quot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf24RedApply

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

theorem e189_exists_conj_of_involutions_mod_odd {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) {u v : Y} (hu : u * u = 1) (hv : v * v = 1)
    (h : QuotientGroup.mk' N u = QuotientGroup.mk' N v) : ∃ m ∈ N, u = m * v * m⁻¹ := by
  have hw : u * v ∈ N := by
    have : QuotientGroup.mk' N (u * v) = 1 := by
      rw [map_mul, h]
      have : QuotientGroup.mk' N v * QuotientGroup.mk' N v = 1 := by rw [← map_mul, hv, map_one]
      exact this
    exact (QuotientGroup.eq_one_iff _).mp this
  set w := u * v with hwdef
  have hr : Odd (orderOf w) := hN.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N hw)
  obtain ⟨j, hj⟩ := hr
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hwv : w * v = u := by rw [hwdef, mul_assoc, hv, mul_one]
  have hvwv : v * w * v⁻¹ = w⁻¹ := by
    have : w⁻¹ = v * u := by rw [hwdef, mul_inv_rev, huinv, hvinv]
    rw [this, hwdef, hvinv]
    calc v * (u * v) * v = v * u * (v * v) := by group
      _ = v * u := by rw [hv, mul_one]
  have hvwk : ∀ k : ℕ, v * w ^ k * v⁻¹ = (w⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc v * w ^ (k + 1) * v⁻¹ = (v * w ^ k * v⁻¹) * (v * w * v⁻¹) := by group
        _ = (w⁻¹) ^ k * w⁻¹ := by rw [ih, hvwv]
        _ = (w⁻¹) ^ (k + 1) := by rw [pow_succ]
  set a := w ^ (j + 1) with ha
  refine ⟨a, N.pow_mem hw _, ?_⟩
  have hva : v * a⁻¹ = a * v := by
    have h2 : v * a⁻¹ * v⁻¹ = a := by
      calc v * a⁻¹ * v⁻¹ = (v * a * v⁻¹)⁻¹ := by group
        _ = ((w⁻¹) ^ (j + 1))⁻¹ := by rw [ha, hvwk]
        _ = a := by rw [inv_pow, inv_inv]
    rwa [mul_inv_eq_iff_eq_mul] at h2
  have h2j : w ^ (2 * (j + 1)) = w := by
    have : 2 * (j + 1) = orderOf w + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  calc u = w * v := hwv.symm
    _ = w ^ (2 * (j + 1)) * v := by rw [h2j]
    _ = a * (a * v) := by rw [ha, two_mul, pow_add, mul_assoc]
    _ = a * (v * a⁻¹) := by rw [hva]
    _ = a * v * a⁻¹ := by rw [mul_assoc]

namespace Ae5Q8

section QuotMain


variable {Yt : Type} [Group Yt] [Finite Yt] {Λ : Set (Subgroup Yt)}

theorem ae5_sect_quot (hΛ : HypOmegaGen Λ)
    (hS : TwinDisc.Q8Section (Yt ⧸ classicalInvolutionOddCore Yt)
      (quotFamily Λ (classicalInvolutionOddCore Yt)))
    (I : AEIdent (quotFamily Λ (classicalInvolutionOddCore Yt)) 5)
    {K K' : Subgroup Yt} (hK : K ∈ Λ) (hK' : K' ∈ Λ) (hne : K' ≠ K) {z : Yt}
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z)
    {J : Subgroup Yt} (hJ : J ∈ Λ) {t : Yt} (htJ : IsUniqueInvolution J t)
    (hzt : z * t ≠ 1) (hztc : z * t = t * z) (P : Sylow 2 Yt) :
    ∃ s ∈ (P : Subgroup Yt),
      (conjSub s K).map (QuotientGroup.mk' (classicalInvolutionOddCore Yt)) =
        K'.map (QuotientGroup.mk' (classicalInvolutionOddCore Yt)) ∧
      ∀ x₀ ∈ K, x₀ * x₀ = z → ∃ g : Yt,
        QuotientGroup.mk' (classicalInvolutionOddCore Yt) (g * (z * t) * g⁻¹) =
          QuotientGroup.mk' (classicalInvolutionOddCore Yt) (x₀ * (s * x₀ * s⁻¹)) := by
  classical
  set N : Subgroup Yt := classicalInvolutionOddCore Yt with hNdef
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Yt
  have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd K) hzK
  have hz'' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd K') hzK'
  have ht' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd J) htJ
  have hne' : K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
    TwinThmE.map_ne_of_twin hΛ hNodd hK ⟨hK', z, hzK, hzK'⟩ hne
  have hzt' : QuotientGroup.mk' N z * QuotientGroup.mk' N t ≠ 1 := by
    intro h
    rw [← map_mul] at h
    have hmem : z * t ∈ N := (QuotientGroup.eq_one_iff _).mp h
    have hsq : (z * t) * (z * t) = 1 := by
      calc (z * t) * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← hztc]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hzK.sq, htJ.sq, one_mul]
    have h3 : orderOf (z * t) ∣ Nat.card N := by
      simpa using Subgroup.orderOf_dvd_natCard N hmem
    exact hzt (eq_one_of_odd_orderOf hsq (hNodd.of_dvd_nat h3))
  obtain ⟨ŝ, hŝP, hŝK, hŝ⟩ := ae5_core hS I (map_mem_quotFamily hK) (map_mem_quotFamily hK') hne'
    hz' hz'' (map_mem_quotFamily hJ) ht' hzt' (Sylow.mapSurjective (QuotientGroup.mk'_surjective N) P)
  rw [Sylow.coe_mapSurjective] at hŝP
  obtain ⟨s, hsP, rfl⟩ := hŝP
  refine ⟨s, hsP, ?_, ?_⟩
  · rw [AscQuot.map_conjSub]
    exact hŝK
  · intro x₀ hx₀K hx₀sq
    obtain ⟨g', hg'⟩ := hŝ (QuotientGroup.mk' N x₀) (Subgroup.mem_map_of_mem _ hx₀K)
      (by rw [← map_mul, hx₀sq])
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g'
    refine ⟨g, ?_⟩
    simp only [map_mul, map_inv]
    exact hg'

end QuotMain

end Ae5Q8

section Fix


theorem e189_eq_one_of_isPGroup_of_odd {G : Type} [Group G] [Finite G] {x : G}
    (hx : IsPGroup 2 (Subgroup.zpowers x)) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hx.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  have h1 : orderOf x = 1 := by rw [hk, hk0, pow_zero]
  exact orderOf_eq_one_iff.mp h1

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem e189_ae5_quot_fixes (h7 : E18_7Q8) (c : MinCexQ8 Ω K S R W H) {z t k : G}
    (hz : IsUniqueInvolution K z) (htk : t = k * z * k⁻¹) (hzt : z * t = t * z) (htz : t ≠ z)
    (hne : conjSub t K ≠ K)
    (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)) (hYH : Y ≤ H) (hKY : K ≤ Y) (hJY : conjSub k K ≤ Y)
    (hΛsub : Λ ⊆ restrictFamily Ω Y) (hΛc : ConjInvariant Λ) (hKΛ : K.subgroupOf Y ∈ Λ)
    (hJΛ : (conjSub k K).subgroupOf Y ∈ Λ) (hgen : (⨆ L ∈ Λ, L) = ⊤)
    (hT : ∀ L ∈ Λ, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = L)
    (hE : ∃ K' ∈ twinSet Λ (K.subgroupOf Y), K' ≠ K.subgroupOf Y)
    (hI : Nonempty (TC.Thin.AEIdent (quotFamily Λ (classicalInvolutionOddCore ↥Y)) 5)) :
    FixesUniqueCoset (z * t) H := by
  classical
  obtain ⟨I⟩ := hI
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
  have hΦ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hΛ : HypOmegaGen Λ := hypOmegaGen_of_sub hΦ hΛsub hΛc
  have hΛcls : Q3CL.ClassicalClause Λ :=
    ⟨fun L hL => (classicalClause_restrict c.stand.cls Y).subnormal L (hΛsub hL),
      fun J hJ => (classicalClause_restrict c.stand.cls Y).commOdd J (hΛsub hJ)⟩
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
  have hzt' : (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  have hne' : conjSub (⟨t, htY⟩ : Y) (K.subgroupOf Y) ≠ K.subgroupOf Y := by
    intro h
    apply hne
    rw [conjSub_subgroupOf] at h
    have hle : conjSub t K ≤ Y := by
      have := conjSub_mono (n := t) hKY
      rwa [conjSub_eq_self_of_mem htY] at this
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this
  have hqd := e189_quotData (n := Nat.card ↥Y + 1) (Nat.lt_succ_self _) hΛ hΛcls hΛq8 hΛ2 hΛA hgen
    hKΛ hJΛ hz' ht' hzt' hne' hT hE
  obtain ⟨K'', hK''tw, hK''ne⟩ := hE
  obtain ⟨zz, hzzK, hzzK''⟩ := hK''tw.2
  have hzz : zz = (⟨z, hzY⟩ : ↥Y) := hzzK.eq hz'
  subst hzz
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
  have hzt'' : (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  obtain ⟨s, hsP, hsK, hs⟩ := Ae5Q8.ae5_sect_quot hΛ hqd.hS I hKΛ hK''tw.1 hK''ne hz' hzzK'' hJΛ
    ht' hzt'' hzt' PY
  have hx₀' : (⟨x₀, hKY hx₀.1⟩ : ↥Y) ∈ K.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx₀.1
  obtain ⟨g, hg⟩ := hs ⟨x₀, hKY hx₀.1⟩ hx₀' (Subtype.ext hx₀sq)
  set y₀ : G := (s : G) * x₀ * (s : G)⁻¹ with hy₀
  have hsS₂ : (s : G) ∈ (S₂ : Subgroup G) := hPYS₂ s hsP
  have hy₀K : y₀ ∈ conjSub (s : G) K := conj_mem_conjSub hx₀.1
  have hzW₂ : z ∈ conjSub x W := by
    rw [← hx₀sq]
    exact (conjSub x W).mul_mem hx₀.2 hx₀.2
  have hy₀W : y₀ ∈ conjSub x W := by
    have := conj_mem_conjSub (n := (s : G)) hx₀.2
    rwa [hW₂n _ hsS₂] at this
  have hz₂W : (s : G) * z * (s : G)⁻¹ ∈ conjSub x W := by
    have := conj_mem_conjSub (n := (s : G)) hzW₂
    rwa [hW₂n _ hsS₂] at this
  have hz₂ : (s : G) * z * (s : G)⁻¹ = z := by
    set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
    have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
    set mk := QuotientGroup.mk' N₀ with hmk
    have hz''b : IsUniqueInvolution (K''.map mk) (mk ⟨z, hzY⟩) :=
      isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd K'') hzzK''
    have hconj := hqd.hz.conj (mk s)
    rw [← AscQuot.map_conjSub, hsK] at hconj
    have heq : mk s * mk ⟨z, hzY⟩ * (mk s)⁻¹ = mk ⟨z, hzY⟩ := hconj.eq hz''b
    set eY : ↥Y := (⟨z, hzY⟩ : ↥Y)⁻¹ * (s * ⟨z, hzY⟩ * s⁻¹) with heY
    have hnN : eY ∈ N₀ := by
      rw [← QuotientGroup.eq_one_iff]
      show mk eY = 1
      rw [heY]
      simp only [map_mul, map_inv]
      rw [heq]
      group
    have heG : (eY : G) = z⁻¹ * ((s : G) * z * (s : G)⁻¹) := rfl
    have heW : (eY : G) ∈ conjSub x W := by
      rw [heG]
      exact (conjSub x W).mul_mem ((conjSub x W).inv_mem hzW₂) hz₂W
    have hodd : Odd (orderOf (eY : G)) := by
      rw [Subgroup.orderOf_coe]
      exact hN₀odd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N₀ hnN)
    have h1 : (eY : G) = 1 :=
      e189_eq_one_of_isPGroup_of_odd
        (S₂.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hW₂S heW))) hodd
    rw [heG] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hy₀sq : y₀ * y₀ = z := by
    calc y₀ * y₀ = (s : G) * (x₀ * x₀) * (s : G)⁻¹ := by rw [hy₀]; group
      _ = (s : G) * z * (s : G)⁻¹ := by rw [hx₀sq]
      _ = z := hz₂
  have hsKΩ : conjSub (s : G) K ∈ Ω := hΩ.conjInvariant (s : G) K hK
  have hzK₂ : IsUniqueInvolution (conjSub (s : G) K) z := by
    have := hz.conj (s : G)
    rwa [hz₂] at this
  have hKperp : conjSub (s : G) K ∈ KPerp Ω K := mem_kPerp_of_twin_gen' hΩ hsKΩ hK hzK₂ hz
  have hxy : x₀ * y₀ = y₀ * x₀ := hW₂abel x₀ hx₀.2 y₀ hy₀W
  have hv2 : (x₀ * y₀) * (x₀ * y₀) = 1 := by
    calc (x₀ * y₀) * (x₀ * y₀) = x₀ * (y₀ * x₀) * y₀ := by group
      _ = x₀ * (x₀ * y₀) * y₀ := by rw [hxy]
      _ = (x₀ * x₀) * (y₀ * y₀) := by group
      _ = 1 := by rw [hx₀sq, hy₀sq, hz.sq]
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  set aY : ↥Y := (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ with haY
  set vY : ↥Y := (⟨x₀, hKY hx₀.1⟩ : ↥Y) * (s * ⟨x₀, hKY hx₀.1⟩ * s⁻¹) with hvY
  have haY2 : aY * aY = 1 := Subtype.ext ha2
  have hvY2 : vY * vY = 1 := Subtype.ext hv2
  have huY2 : (g * aY * g⁻¹) * (g * aY * g⁻¹) = 1 := by
    calc (g * aY * g⁻¹) * (g * aY * g⁻¹) = g * (aY * aY) * g⁻¹ := by group
      _ = 1 := by rw [haY2]; group
  obtain ⟨m, hmN, hum⟩ := e189_exists_conj_of_involutions_mod_odd hN₀odd huY2 hvY2 hg
  set c' : ↥Y := m⁻¹ * g with hc'
  have hvc : c' * aY * c'⁻¹ = vY := by
    calc c' * aY * c'⁻¹ = m⁻¹ * (g * aY * g⁻¹) * m := by rw [hc']; group
      _ = m⁻¹ * (m * vY * m⁻¹) * m := by rw [hum]
      _ = vY := by group
  have hvcG : (c' : G) * (z * t) * (c' : G)⁻¹ = x₀ * y₀ := by
    have := congrArg Subtype.val hvc
    simpa [haY, hvY, hy₀] using this
  have hc'H : (c' : G) ∈ H := hYH c'.2
  have hv1 : x₀ * y₀ ≠ 1 := by
    intro h
    apply ha1
    have : z * t = (c' : G)⁻¹ * (x₀ * y₀) * (c' : G) := by rw [← hvcG]; group
    rw [this, h]
    group
  have hKW₂ : K ⊓ conjSub x W ∈ USet Ω := inf_W_mem_USet' hΩ hW₂ hW₂S hK hRΩ hRK hRS₂
  have hR₂Ω : conjSub (s : G) R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRΩ (s : G)
  have hR₂S₂ : conjSub (s : G) R ≤ (S₂ : Subgroup G) := by
    intro v hv
    have h1 : (s : G)⁻¹ * v * (s : G) ∈ R := mem_conjSub_iff.mp hv
    have h2 : (s : G) * ((s : G)⁻¹ * v * (s : G)) * (s : G)⁻¹ ∈ (S₂ : Subgroup G) :=
      S₂.mul_mem (S₂.mul_mem hsS₂ (hRS₂ h1)) (S₂.inv_mem hsS₂)
    simpa [mul_assoc] using h2
  have hC : Subgroup.centralizer ({x₀ * y₀} : Set G) ≤ H :=
    hCW₂ K hK hKW₂ _ hKperp R (conjSub (s : G) R) hRΩ hRK hRS₂ hR₂Ω (conjSub_mono hRK) hR₂S₂
      (commutes_or_eq_of_le_sylow hΩ hRΩ hR₂Ω hRS₂ hR₂S₂) (x₀ * y₀)
      (Subgroup.mul_mem_sup hx₀R (conj_mem_conjSub (n := (s : G)) hx₀R))
      ((conjSub x W).mul_mem hx₀.2 hy₀W) hv1 hv2
  have hCa : Subgroup.centralizer ({z * t} : Set G) ≤ H := by
    intro c'' hc''
    rw [Subgroup.mem_centralizer_singleton_iff] at hc''
    have hc3 : (c' : G) * c'' * (c' : G)⁻¹ ∈ Subgroup.centralizer ({x₀ * y₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hvcG]
      calc (c' : G) * c'' * (c' : G)⁻¹ * ((c' : G) * (z * t) * (c' : G)⁻¹)
          = (c' : G) * (c'' * (z * t)) * (c' : G)⁻¹ := by group
        _ = (c' : G) * ((z * t) * c'') * (c' : G)⁻¹ := by rw [hc'']
        _ = (c' : G) * (z * t) * (c' : G)⁻¹ * ((c' : G) * c'' * (c' : G)⁻¹) := by group
    have h2 : (c' : G)⁻¹ * ((c' : G) * c'' * (c' : G)⁻¹) * (c' : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hc'H) (hC hc3)) hc'H
    simpa [mul_assoc] using h2
  exact fixesUniqueCoset_of_centralizer_le hCa (h7 G Ω K S R W H c (z * t) ha1 ha2 hCa)

end Fix

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
