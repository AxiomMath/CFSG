module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf19Sect
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18NoExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18OddCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.Ih8
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Red



theorem e189_comm_mod_odd_of_not_conj {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {n : ℕ}
    (hT4 : Thm4RTwinBelow 3 n) (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hA : ∀ L ∈ Ω, AEmpty Ω L)
    {Y₁ : Subgroup G} (hY₁ : Nat.card Y₁ < n) {Λ₀ : Set (Subgroup G)} (hΛ₀Ω : Λ₀ ⊆ Ω)
    (hΛ₀Y : ∀ J ∈ Λ₀, J ≤ Y₁) (hinv : ∀ y ∈ Y₁, ∀ J ∈ Λ₀, conjSub y J ∈ Λ₀)
    {J L : Subgroup G} (hJ : J ∈ Λ₀) (hL : L ∈ Λ₀) (hnot : ¬ ∃ y ∈ Y₁, conjSub y J = L) :
    ∀ a ∈ J, ∀ b ∈ L, ∃ m ∈ classicalInvolutionOddCore ↥Y₁, (m : G) = a * b * a⁻¹ * b⁻¹ := by
  classical
  set N₁ : Subgroup ↥Y₁ := classicalInvolutionOddCore ↥Y₁ with hN₁
  have hN₁odd : Odd (Nat.card N₁) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₁
  set mk := QuotientGroup.mk' N₁ with hmk
  set Λ₁ : Set (Subgroup ↥Y₁) := (fun M => M.subgroupOf Y₁) '' Λ₀ with hΛ₁def
  have hsub : Λ₁ ⊆ restrictFamily Ω Y₁ := by
    rintro _ ⟨M, hM, rfl⟩
    exact subgroupOf_mem_restrictFamily (hΛ₀Ω hM) (hΛ₀Y M hM)
  have hinvΛ : ConjInvariant Λ₁ := by
    intro g L hL
    obtain ⟨M, hM, rfl⟩ := hL
    rw [conjSub_subgroupOf]
    exact ⟨conjSub (g : G) M, hinv g g.2 M hM, rfl⟩
  have hΦ : HypOmegaGen (restrictFamily Ω Y₁) := hypOmegaGen_restrict hΩ Y₁
  have hΛ₁ : HypOmegaGen Λ₁ := hypOmegaGen_of_sub hΦ hsub hinvΛ
  have hΛ₁q8 := fun L (hL : L ∈ Λ₁) => q8_restrict hq8 Y₁ L (hsub hL)
  have hΛ₁2 := fun L (hL : L ∈ Λ₁) => two_restrict h2 Y₁ L (hsub hL)
  have hΛ₁A : ∀ L ∈ Λ₁, AEmpty Λ₁ L :=
    aEmpty_of_sub hΦ hsub fun L hL => by
      obtain ⟨L₀, hL₀, hL₀Y, rfl⟩ := hL
      exact AEmpty.restrict hΩ hL₀Y (hA L₀ hL₀)
  have hΔ : HypOmegaGen (quotFamily Λ₁ N₁) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ₁ hN₁odd
  have hΔ2 := two_quot_odd hΛ₁2 hN₁odd
  have hΔq8 : ∀ M ∈ quotFamily Λ₁ N₁, ∀ P : Subgroup (↥Y₁ ⧸ N₁), IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := fun M hM =>
    TwinDisc.forall_sylow_iso_of_exists (q8_quot_odd hN₁odd hΛ₁q8 M hM)
  have hΔA := aEmpty_quot_odd hΛ₁ hN₁odd hΛ₁A
  have hOq : classicalInvolutionOddCore (↥Y₁ ⧸ N₁) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y₁
  have hlt : Nat.card (↥Y₁ ⧸ N₁) < n := by
    have h1 : Nat.card (↥Y₁ ⧸ N₁) ≤ Nat.card ↥Y₁ :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₁)
    omega
  have hJ₁ : J.subgroupOf Y₁ ∈ Λ₁ := ⟨J, hJ, rfl⟩
  have hL₁ : L.subgroupOf Y₁ ∈ Λ₁ := ⟨L, hL, rfl⟩
  have hnot' : ¬ ∃ g : ↥Y₁ ⧸ N₁, conjSub g ((J.subgroupOf Y₁).map mk) = (L.subgroupOf Y₁).map mk := by
    rintro ⟨gb, hgb⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective N₁ gb
    have h1 : (conjSub g' (J.subgroupOf Y₁)).map mk = (L.subgroupOf Y₁).map mk := by
      rw [AscQuot.map_conjSub]
      exact hgb
    have hJ' : conjSub g' (J.subgroupOf Y₁) ∈ Λ₁ := hΛ₁.conjInvariant g' _ hJ₁
    obtain ⟨n', hn'N, hn'⟩ := Q3T6.exists_conj_of_map_eq_gen hΛ₁ hN₁odd hJ' hL₁ h1
    apply hnot
    refine ⟨((n' * g' : ↥Y₁) : G), (n' * g').2, ?_⟩
    have h3 : conjSub (n' * g') (J.subgroupOf Y₁) = L.subgroupOf Y₁ := by
      rw [conjSub_mul]
      exact hn'.symm
    rw [conjSub_subgroupOf] at h3
    have hle : conjSub ((n' * g' : ↥Y₁) : G) J ≤ Y₁ := by
      have := conjSub_mono (n := ((n' * g' : ↥Y₁) : G)) (hΛ₀Y J hJ)
      rwa [conjSub_eq_self_of_mem (n' * g').2] at this
    have := Subgroup.subgroupOf_inj.mp h3
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr (hΛ₀Y L hL)] at this
  have hcomm := hT4 (↥Y₁ ⧸ N₁) hlt (quotFamily Λ₁ N₁) hΔ hΔ2 hΔq8 hΔA hOq
    ((J.subgroupOf Y₁).map mk) (map_mem_quotFamily hJ₁) ((L.subgroupOf Y₁).map mk)
    (map_mem_quotFamily hL₁) hnot'
  intro a ha b hb
  set aY : ↥Y₁ := ⟨a, hΛ₀Y J hJ ha⟩ with haY
  set bY : ↥Y₁ := ⟨b, hΛ₀Y L hL hb⟩ with hbY
  have hcab : mk aY * mk bY = mk bY * mk aY :=
    hcomm (mk aY) ⟨aY, Subgroup.mem_subgroupOf.mpr ha, rfl⟩ (mk bY)
      ⟨bY, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hmem : aY * bY * aY⁻¹ * bY⁻¹ ∈ N₁ := by
    apply (QuotientGroup.eq_one_iff _).mp
    show mk (aY * bY * aY⁻¹ * bY⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hcab]
    group
  exact ⟨_, hmem, rfl⟩

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem e189_exists_minimal (hT : T4Supply) (c : MinCexQ8 Ω K S R W H) {z t k : G} (hz : IsUniqueInvolution K z)
    (htk : t = k * z * k⁻¹) (hkH : k ∈ H) (htS : t ∈ (S : Subgroup G)) (hne : conjSub t K ≠ K) :
    ∃ Y : Subgroup G, Y ≤ H ∧ K ≤ Y ∧ (∃ y ∈ Y, conjSub y K = conjSub k K) ∧
      (⨆ y : Y, conjSub (y : G) K) = Y := by
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have hKH : K ≤ H := fun w hw =>
    hzH (Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem hz hw).symm)
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
  have hT4 : Thm4RTwinBelow 3 (Nat.card G) := hT _ c.stand.ih.1 c.stand.ih.2
  have hHn : Nat.card H < Nat.card G := natCard_lt_of_ne_top c.proper
  let 𝒞 : Set (Subgroup G) := {Y' | Y' ≤ H ∧ K ≤ Y' ∧ ∃ y ∈ Y', conjSub y K = conjSub k K}
  have h𝒞 : H ∈ 𝒞 := ⟨le_rfl, hKH, k, hkH, rfl⟩
  obtain ⟨Y, hY𝒞, hYmin⟩ :=
    Set.exists_min_image 𝒞 (fun Y' : Subgroup G => Nat.card Y') (Set.toFinite 𝒞) ⟨H, h𝒞⟩
  obtain ⟨hYH, hKY, y₀, hy₀Y, hy₀⟩ := hY𝒞
  set Y₁ : Subgroup G := ⨆ y : Y, conjSub (y : G) K
  have hconjY : ∀ y : Y, conjSub (y : G) K ≤ Y := fun y => by
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  have hY₁Y : Y₁ ≤ Y := iSup_le hconjY
  have hKY₁ : K ≤ Y₁ := by
    have := le_iSup (fun y : Y => conjSub (y : G) K) 1
    simp only [Subgroup.coe_one, conjSub_one] at this
    exact this
  have hclaim : ∃ y₁ ∈ Y₁, conjSub y₁ K = conjSub k K := by
    by_contra hno
    push Not at hno
    set Λ₀ : Set (Subgroup G) := Set.range (fun y : Y => conjSub (y : G) K)
    have hΛ₀Ω : Λ₀ ⊆ Ω := by
      rintro _ ⟨y, rfl⟩
      exact hΩ.conjInvariant _ K hK
    have hΛ₀Y : ∀ J ∈ Λ₀, J ≤ Y₁ := by
      rintro _ ⟨y, rfl⟩
      exact le_iSup (fun y : Y => conjSub (y : G) K) y
    have hinv : ∀ y ∈ Y₁, ∀ J ∈ Λ₀, conjSub y J ∈ Λ₀ := by
      rintro y hy _ ⟨y', rfl⟩
      refine ⟨⟨y, hY₁Y hy⟩ * y', ?_⟩
      show conjSub (y * (y' : G)) K = conjSub y (conjSub (y' : G) K)
      exact conjSub_mul _ _ _
    have hY₁lt : Nat.card Y₁ < Nat.card G :=
      lt_of_le_of_lt (Subgroup.card_le_of_le (hY₁Y.trans hYH)) hHn
    have hKΛ : K ∈ Λ₀ := ⟨1, by simp⟩
    have hkΛ : conjSub k K ∈ Λ₀ := ⟨⟨y₀, hy₀Y⟩, hy₀⟩
    have hcomm := e189_comm_mod_odd_of_not_conj hT4 hΩ c.stand.q8 c.stand.two hAΩ hY₁lt hΛ₀Ω
      hΛ₀Y hinv hKΛ hkΛ (fun ⟨y, hy, h⟩ => hno y hy h)
    obtain ⟨hRΩ, hRK, hRS⟩ := c.stand.hR
    set N₁ : Subgroup ↥Y₁ := classicalInvolutionOddCore ↥Y₁ with hN₁
    have hN₁odd : Odd (Nat.card N₁) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₁
    have htK : t ∈ conjSub k K := by
      rw [htk]
      exact conj_mem_conjSub hz.mem
    have hcR : ∀ x ∈ R, t * x * t⁻¹ = x := by
      intro x hxR
      obtain ⟨m, hmN, hm⟩ := hcomm x (hRK hxR) t htK
      have hcS : x * t * x⁻¹ * t⁻¹ ∈ (S : Subgroup G) :=
        S.mul_mem (S.mul_mem (S.mul_mem (hRS hxR) htS) (S.inv_mem (hRS hxR))) (S.inv_mem htS)
      have hodd : Odd (orderOf (m : G)) := by
        rw [Subgroup.orderOf_coe]
        exact hN₁odd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N₁ hmN)
      have h1 : (m : G) = 1 :=
        e189_eq_one_of_isPGroup_of_odd
          (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hm ▸ hcS))) hodd
      rw [hm] at h1
      have hxt : x * t = t * x := by
        calc x * t = (x * t * x⁻¹ * t⁻¹) * (t * x) := by group
          _ = t * x := by rw [h1, one_mul]
      rw [← hxt]
      group
    have hRt : R ≤ conjSub t K := fun x hx => by
      have := conj_mem_conjSub (n := t) (hRK hx)
      rwa [hcR x hx] at this
    have hKt : conjSub t K ∈ Ω := hΩ.conjInvariant t K hK
    have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
    have h8 := hΩ.eight_le_of_mem_RSet hRΩ
    obtain ⟨m', hm'⟩ := hRsyl.2.1.exists_card_eq
    have hm3 : 3 ≤ m' := by
      have h8' : 2 ^ 3 ≤ 2 ^ m' := by rw [← hm']; exact h8
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h8'
    have hdvd : 8 ∣ Nat.card ↥(K ⊓ conjSub t K) := by
      have h1 : Nat.card R ∣ Nat.card ↥(K ⊓ conjSub t K) :=
        Subgroup.card_dvd_of_le (le_inf hRK hRt)
      have h2 : 8 ∣ Nat.card R := by
        rw [hm']
        exact (pow_dvd_pow 2 hm3 : 2 ^ 3 ∣ 2 ^ m')
      exact h2.trans h1
    have h3 : 3 ≤ padicValNat 2 (Nat.card ↥(K ⊓ conjSub t K)) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (by simpa using hdvd)
    have h4 := (hΩ.omega4 K hK (conjSub t K) hKt (Ne.symm hne)).1
    omega
  have hY₁𝒞 : Y₁ ∈ 𝒞 := ⟨hY₁Y.trans hYH, hKY₁, hclaim⟩
  have hcard : Nat.card Y ≤ Nat.card Y₁ := hYmin Y₁ hY₁𝒞
  have hY₁eq : Y₁ = Y := Subgroup.eq_of_le_of_card_ge hY₁Y hcard
  exact ⟨Y, hYH, hKY, ⟨y₀, hy₀Y, hy₀⟩, hY₁eq⟩

theorem e189_redData (hT : T4Supply) (c : MinCexQ8 Ω K S R W H) {z t k : G}
    (hz : IsUniqueInvolution K z) (htk : t = k * z * k⁻¹) (hkH : k ∈ H) (hzt : z * t = t * z)
    (htS : t ∈ (S : Subgroup G)) (hne : conjSub t K ≠ K) :
    ∃ (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)), E189RedData Ω K k H Y Λ := by
  classical
  obtain ⟨Y, hYH, hKY, ⟨y₀, hy₀Y, hy₀⟩, hgenY⟩ := e189_exists_minimal hT c hz htk hkH htS hne
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hconjY : ∀ y : Y, conjSub (y : G) K ≤ Y := fun y => by
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  have hJY : conjSub k K ≤ Y := by
    rw [← hy₀]
    exact hconjY ⟨y₀, hy₀Y⟩
  have hmap : ∀ y : ↥Y, (conjSub y (K.subgroupOf Y)).map Y.subtype = conjSub (y : G) K := by
    intro y
    rw [conjSub_subgroupOf Y y K, Subgroup.map_subgroupOf_eq_of_le (hconjY y)]
  set Λ : Set (Subgroup ↥Y) := Set.range (fun y : ↥Y => conjSub y (K.subgroupOf Y)) with hΛ
  have hzY : z ∈ Y := hKY hz.mem
  have hzJ : IsUniqueInvolution (conjSub k K) t := by
    have := hz.conj k
    rwa [← htk] at this
  have htY : t ∈ Y := hJY hzJ.mem
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  refine ⟨Y, Λ, ⟨hYH, hKY, hJY, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro L hL
    obtain ⟨y, rfl⟩ := hL
    show conjSub y (K.subgroupOf Y) ∈ restrictFamily Ω Y
    rw [conjSub_subgroupOf]
    exact subgroupOf_mem_restrictFamily (hΩ.conjInvariant (y : G) K hK) (hconjY y)
  · intro g L hL
    obtain ⟨y, rfl⟩ := hL
    exact ⟨g * y, conjSub_mul _ _ _⟩
  · exact ⟨1, conjSub_one _⟩
  · refine ⟨⟨y₀, hy₀Y⟩, ?_⟩
    show conjSub (⟨y₀, hy₀Y⟩ : ↥Y) (K.subgroupOf Y) = (conjSub k K).subgroupOf Y
    rw [conjSub_subgroupOf]
    show (conjSub y₀ K).subgroupOf Y = _
    rw [hy₀]
  · have hmapΛ : (⨆ L ∈ Λ, L).map Y.subtype = ⨆ L ∈ Λ, L.map Y.subtype := by
      rw [Subgroup.map_iSup]
      congr 1
      funext L
      rw [Subgroup.map_iSup]
    apply Subgroup.map_injective Y.subtype_injective
    rw [hmapΛ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply le_antisymm
    · refine iSup₂_le fun L hL => ?_
      obtain ⟨y, rfl⟩ := hL
      rw [hmap y]
      exact hconjY y
    · exact hgenY.symm.le.trans (iSup_le fun y => le_iSup₂_of_le (conjSub y (K.subgroupOf Y))
        ⟨y, rfl⟩ (le_of_eq (hmap y).symm))
  · rintro L ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · have hzt' : (⟨z, hzY⟩ : ↥Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
    have hzK' : IsUniqueInvolution (conjSub (⟨t, htY⟩ : ↥Y) (K.subgroupOf Y)) ⟨z, hzY⟩ := by
      have := hz'.conj (⟨t, htY⟩ : ↥Y)
      rwa [show (⟨t, htY⟩ : ↥Y) * ⟨z, hzY⟩ * (⟨t, htY⟩ : ↥Y)⁻¹ = ⟨z, hzY⟩ by
        rw [← hzt']; group] at this
    refine ⟨conjSub (⟨t, htY⟩ : ↥Y) (K.subgroupOf Y), ⟨⟨⟨t, htY⟩, rfl⟩, ⟨z, hzY⟩, hz', hzK'⟩, ?_⟩
    intro h
    apply hne
    rw [conjSub_subgroupOf] at h
    have hle : conjSub t K ≤ Y := by
      have := conjSub_mono (n := t) hKY
      rwa [conjSub_eq_self_of_mem htY] at this
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this

theorem e189ReduceQ8'_of_model (hT : T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar) :
    E189ReduceQ8' := by
  classical
  intro G _ _ Ω K S R W H c _h6 _h7 _h4 z t k hz htk hkH hzt _htz htS hne
  obtain ⟨Y, Λ, hdata⟩ := e189_redData hT c hz htk hkH hzt htS hne
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
  have hHn : Nat.card H < Nat.card G := natCard_lt_of_ne_top c.proper
  have hzY : z ∈ Y := hdata.kY hz.mem
  have hzJ : IsUniqueInvolution (conjSub k K) t := by
    have := hz.conj k
    rwa [← htk] at this
  have htY : t ∈ Y := hdata.jY hzJ.mem
  by_cases hconn : ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
      L ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore ↥Y))
        ((K.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)))
  · exact Or.inr ⟨Y, Λ, hdata, Or.inl hconn⟩
  · have hqd := e189_quotData_G (n := Nat.card G) hΩ c.stand.cls c.stand.q8 c.stand.two hAΩ hHn hK
      hz htk Y Λ hdata.yH hdata.kY hdata.jY hdata.sub hdata.inv hdata.kΛ hdata.jΛ hdata.gen
      hdata.trans hdata.twin hzt hne ⟨z, hzY⟩ ⟨t, htY⟩ rfl rfl
    have hih := c.stand.ih
    have htrans := trans_of_trans_at hqd.trans
    have hedge : ∃ M ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
        ∃ N : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y),
          N ∈ omegaNbr (quotFamily Λ (classicalInvolutionOddCore ↥Y)) M := by
      obtain ⟨K'', ⟨hK''Φ, w, hwK, hwK''⟩, hne''⟩ := hqd.twin
      exact ⟨_, hqd.hK, K'', Q3CL.T3.twin_mem_omegaNbr hqd.hS.hyp hqd.hK hK''Φ hne'' hwK hwK''⟩
    have hoddAll : ∀ M ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y), ∀ u : ↥Y ⧸ classicalInvolutionOddCore ↥Y,
        IsUniqueInvolution M u →
          oddCoreImg (Subgroup.centralizer ({u} : Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))) = ⊥ :=
      fun M hM u hu => TwinDisc.oddCentEdge_proved (Nat.card G) hih.1 hih.2 _ hqd.card _ hqd.hS
        htrans hedge M hM u hu
    have hdisc : ¬ T3.DStarConnected (quotFamily Λ (classicalInvolutionOddCore ↥Y)) :=
      fun hD => hconn fun L hL => hD _ hqd.hK L hL
    rcases TwinDisc.ExitU.noExit_or_ae5 hmodel hih.2.thmD.d2 hqd.card hqd.hS htrans hedge hoddAll
      hdisc with hNo | ⟨-, hI⟩
    · left
      exact e189_apply_gen hΩ c.stand.cls c.stand.q8 c.stand.two hAΩ hHn hK hz htk Y Λ hdata.yH
        hdata.kY hdata.jY hdata.sub hdata.inv hdata.kΛ hdata.jΛ hdata.gen hdata.trans hdata.twin
        hzt hne fun zY tY _ _ hqd' =>
          e189ConclF_noExit (Q3T8.Asc77.e189Sect_of_model Q3T8.Asc77.e189Model3_proved) hih.1
            (InductionBridge.ih8T_of_cit3Below hih.1) hih.2 hqd'.card hqd'.hS hNo hqd'.hK hqd'.hJ
            hqd'.hz hqd'.ht hqd'.hzt hqd'.hne
    · exact Or.inr ⟨Y, Λ, hdata, Or.inr hI⟩

end Red

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
