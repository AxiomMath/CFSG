module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf13BarB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

@[expose] def E189ConclG {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K H : Subgroup G) (z t : G) : Prop :=
  (∃ K'' ∈ twinSet Ω K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ K ∧ R₂ ∈ RSet Ω ∧
        R₂ ≤ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : G, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧
          x * u * x⁻¹ = z * t ∧
          ((∃ e ∈ H, e * u * e⁻¹ = z) ∨ ∀ a ∈ R₁, ∀ b ∈ R₂, orderOf a = 4 → orderOf b = 4 →
            ∃ e ∈ H, e * u * e⁻¹ = a * b)) ∨
    (∃ x ∈ H, ∃ M' ∈ twinSet Ω (conjSub x K), M' ≠ conjSub x K ∧
        ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ conjSub x K ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ M' ∧
          Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w)

structure E189QuotData {Y : Type} [Group Y] [Finite Y] (n : ℕ) (Λ : Set (Subgroup Y))
    (K J : Subgroup Y) (z t : Y) : Prop where
  hS : TwinDisc.Q8Section (Y ⧸ classicalInvolutionOddCore Y) (quotFamily Λ (classicalInvolutionOddCore Y))
  cls : Q3CL.ClassicalClause (quotFamily Λ (classicalInvolutionOddCore Y))
  card : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < n
  hK : K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) ∈
    quotFamily Λ (classicalInvolutionOddCore Y)
  hJ : J.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) ∈
    quotFamily Λ (classicalInvolutionOddCore Y)
  hz : IsUniqueInvolution (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
    (QuotientGroup.mk' (classicalInvolutionOddCore Y) z)
  ht : IsUniqueInvolution (J.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
    (QuotientGroup.mk' (classicalInvolutionOddCore Y) t)
  hzt : QuotientGroup.mk' (classicalInvolutionOddCore Y) z * QuotientGroup.mk' (classicalInvolutionOddCore Y) t =
    QuotientGroup.mk' (classicalInvolutionOddCore Y) t * QuotientGroup.mk' (classicalInvolutionOddCore Y) z
  hne : conjSub (QuotientGroup.mk' (classicalInvolutionOddCore Y) t)
    (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))) ≠
      K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))
  trans : ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore Y),
    ∃ y : Y ⧸ classicalInvolutionOddCore Y,
      conjSub y (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))) = L
  twin : ∃ K'' ∈ twinSet (quotFamily Λ (classicalInvolutionOddCore Y))
      (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))),
    K'' ≠ K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))

section Apply

theorem e189_quotData {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    (hcard : Nat.card Y < n) (hΛ : HypOmegaGen Λ) (hΛcls : Q3CL.ClassicalClause Λ)
    (hΛq8 : ∀ L ∈ Λ, ∃ P : Subgroup Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hΛ2 : ∀ L ∈ Λ, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hΛA : ∀ L ∈ Λ, AEmpty Λ L) (hgen : (⨆ L ∈ Λ, L) = ⊤)
    {K J : Subgroup Y} (hKΛ : K ∈ Λ) (hJΛ : J ∈ Λ) {z t : Y}
    (hz' : IsUniqueInvolution K z) (ht' : IsUniqueInvolution J t) (hzt' : z * t = t * z)
    (hne' : conjSub t K ≠ K) (hT : ∀ L ∈ Λ, ∃ y : Y, conjSub y K = L)
    (hE : ∃ K' ∈ twinSet Λ K, K' ≠ K) : E189QuotData n Λ K J z t := by
  classical
  set N₀ : Subgroup Y := classicalInvolutionOddCore Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card Y
  set mk := QuotientGroup.mk' N₀ with hmk
  have hΛ' : HypOmegaGen (quotFamily Λ N₀) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ hN₀odd
  have hcls' := classicalClause_quot_odd hΛ hΛcls hN₀odd
  have hq8' : ∀ J ∈ quotFamily Λ N₀, ∀ P : Subgroup (Y ⧸ N₀), IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup 2) := fun J hJ =>
    TwinDisc.forall_sylow_iso_of_exists (q8_quot_odd hN₀odd hΛq8 J hJ)
  have h2' := two_quot_odd hΛ2 hN₀odd
  have hA' := aEmpty_quot_odd hΛ hN₀odd hΛA
  have hOq : classicalInvolutionOddCore (Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hcard' : Nat.card (Y ⧸ N₀) < n := by
    have h1 : Nat.card (Y ⧸ N₀) ≤ Nat.card Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hgen' : (⨆ L ∈ quotFamily Λ N₀, L) = ⊤ := by
    have h1 : (⨆ L ∈ Λ, L).map mk = ⨆ L ∈ Λ, L.map mk := by
      rw [Subgroup.map_iSup]
      congr 1
      funext L
      rw [Subgroup.map_iSup]
    have h2 : (⊤ : Subgroup Y).map mk = ⊤ :=
      Subgroup.map_top_of_surjective mk (QuotientGroup.mk'_surjective N₀)
    apply top_le_iff.mp
    rw [← h2, ← hgen, h1]
    exact iSup₂_le fun L hL => le_iSup₂ (f := fun L' (_ : L' ∈ quotFamily Λ N₀) => L')
      (L.map mk) (map_mem_quotFamily hL)
  have hS : TwinDisc.Q8Section (Y ⧸ N₀) (quotFamily Λ N₀) :=
    ⟨hΛ', h2', hq8', hOq, hA', hgen'⟩
  have hzb : IsUniqueInvolution (K.map mk) (mk z) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd K) hz'
  have htb : IsUniqueInvolution (J.map mk) (mk t) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd J) ht'
  have hzt'' : mk z * mk t = mk t * mk z := by rw [← map_mul, ← map_mul, hzt']
  have hne'' : conjSub (mk t) (K.map mk) ≠ K.map mk := by
    intro h
    have hzK' : IsUniqueInvolution (conjSub t K) z := by
      have := hz'.conj t
      rwa [show t * z * t⁻¹ = z by rw [← hzt']; group] at this
    have hK' : conjSub t K ∈ twinSet Λ K :=
      ⟨hΛ.conjInvariant t K hKΛ, z, hz', hzK'⟩
    exact map_ne_of_twin hΛ hN₀odd hKΛ hK' hne' (by rw [AscQuot.map_conjSub]; exact h)
  have hTb : ∀ L ∈ quotFamily Λ N₀, ∃ y : Y ⧸ N₀, conjSub y (K.map mk) = L := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨y, hy⟩ := hT L hL
    exact ⟨mk y, by
      show conjSub (mk y) (K.map mk) = L.map mk
      rw [← hy, AscQuot.map_conjSub]⟩
  have hEb : ∃ K'' ∈ twinSet (quotFamily Λ N₀) (K.map mk), K'' ≠ K.map mk := by
    obtain ⟨K', hK'tw, hK'ne⟩ := hE
    obtain ⟨hK'Λ, z', hz'K, hz'K'⟩ := hK'tw
    exact ⟨K'.map mk, ⟨map_mem_quotFamily hK'Λ, mk z',
      isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd K) hz'K,
      isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd K') hz'K'⟩,
      map_ne_of_twin hΛ hN₀odd hKΛ ⟨hK'Λ, z', hz'K, hz'K'⟩ hK'ne⟩
  exact ⟨hS, hcls', hcard', map_mem_quotFamily hKΛ, map_mem_quotFamily hJΛ, hzb, htb, hzt'', hne'',
    hTb, hEb⟩

theorem e189_lift_conclF {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    (hΛ : HypOmegaGen Λ) {K J : Subgroup Y} (hKΛ : K ∈ Λ) {z t : Y}
    (hz' : IsUniqueInvolution K z) (ht' : IsUniqueInvolution J t) (hzt' : z * t = t * z)
    (hne' : conjSub t K ≠ K)
    (hbar : E189ConclF (quotFamily Λ (classicalInvolutionOddCore Y))
      (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) z)
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) t)) : E189ConclF Λ K z t := by
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  rcases hbar with
    ⟨K'', hK''tw, hK''ne, Rb₁, Rb₂, hRb₁, hRb₂, hRbc, ub, xb, hu, hu1, hu2, hux, hFb⟩ |
      ⟨xb, Mb, hM, hMne, Rb₁, Rb₂, hRb₁, hRb₂, hRbc, hcomm⟩
  · left
    exact e189_lift_a_F hΛ hN₀odd hKΛ hz' ht'.sq hzt' hK''tw hK''ne hRb₁ hRb₂ hRbc hu hu1 hu2
      hux hFb
  · right
    exact e189_lift_b_syl_gen hΛ hN₀odd hKΛ ht'.sq hz' hzt' (e189_mul_ne_one hz' hne') hM hMne
      hRb₁ hRb₂ hRbc hcomm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem e189_conclG_of_conclF (hΩ : HypOmegaGen Ω) {H K : Subgroup G} (hK : K ∈ Ω)
    {z t : G} (hz : IsUniqueInvolution K z)
    (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)) (hYH : Y ≤ H) (hKY : K ≤ Y)
    (hΛsub : Λ ⊆ restrictFamily Ω Y) (hzY : z ∈ Y) (htY : t ∈ Y)
    (hconcl : E189ConclF Λ (K.subgroupOf Y) ⟨z, hzY⟩ ⟨t, htY⟩) : E189ConclG Ω K H z t := by
  have htwin : ∀ {J₁ J₂ : Subgroup ↥Y}, J₂ ∈ twinSet Λ J₁ → J₂ ∈ twinSet (restrictFamily Ω Y) J₁ :=
    fun h => ⟨hΛsub h.1, h.2⟩
  rcases hconcl with
    ⟨K'', hK''tw, hK''ne, R₁, R₂, hR₁, hR₂, hRc, u, x, hu, hu1, hu2, hux, hF⟩ |
      ⟨x, M', hM'tw, hM'ne, R₁, R₂, hR₁, hR₂, hRc, hcomm⟩
  · left
    have hK''tw' := htwin hK''tw
    have hKΛ' := subgroupOf_mem_restrictFamily hK hKY
    have hRK : R₁.map Y.subtype ≤ K := by
      have := Subgroup.map_mono (f := Y.subtype) hR₁.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
    refine ⟨K''.map Y.subtype, map_mem_twinSet_restrict hKY hK''tw',
      map_ne_of_ne_subgroupOf hK''ne, R₁.map Y.subtype, R₂.map Y.subtype,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hKΛ' hR₁), hRK,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hK''tw'.1 hR₂), Subgroup.map_mono hR₂.1, ?_,
      (u : G), (x : G), ?_, fun h => hu1 (Subtype.ext h), congrArg Subtype.val hu2,
      by simpa using congrArg Subtype.val hux, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hRc a ha b hb)
    · have := Subgroup.mem_map_of_mem Y.subtype hu
      rwa [Subgroup.map_sup] at this
    · rcases hF with ⟨e, he⟩ | hF
      · exact Or.inl ⟨(e : G), hYH e.2, by simpa using congrArg Subtype.val he⟩
      · refine Or.inr ?_
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ha4 hb4
        obtain ⟨e, he⟩ := hF a ha b hb (by rwa [← Subgroup.orderOf_coe]) (by rwa [← Subgroup.orderOf_coe])
        exact ⟨(e : G), hYH e.2, by simpa using congrArg Subtype.val he⟩
  · right
    have hMY : conjSub (x : G) K ≤ Y := by
      have := conjSub_mono (n := (x : G)) hKY
      rwa [conjSub_eq_self_of_mem x.2] at this
    have hxK : (conjSub (x : G) K).subgroupOf Y ∈ restrictFamily Ω Y :=
      subgroupOf_mem_restrictFamily (hΩ.conjInvariant (x : G) K hK) hMY
    have hM'tw' := htwin hM'tw
    rw [conjSub_subgroupOf] at hM'tw' hM'ne hR₁
    have hM₂Y : M'.map Y.subtype ≤ Y := Subgroup.map_subtype_le M'
    refine ⟨(x : G), hYH x.2, M'.map Y.subtype, map_mem_twinSet_restrict hMY hM'tw',
      map_ne_of_ne_subgroupOf hM'ne, R₁.map Y.subtype, R₂.map Y.subtype,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hxK hR₁), ?_,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hM'tw'.1 hR₂), Subgroup.map_mono hR₂.1, ?_,
      fun w hw => ?_⟩
    · have := Subgroup.map_mono (f := Y.subtype) hR₁.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hMY] at this
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hRc a ha b hb)
    · rw [← Subgroup.map_sup] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      simpa using congrArg Subtype.val (hcomm w' hw')

theorem e189_quotData_G {n : ℕ}
    (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hAΩ : ∀ L ∈ Ω, AEmpty Ω L) {H K : Subgroup G} (hHn : Nat.card H < n) (hK : K ∈ Ω)
    {z t k : G} (hz : IsUniqueInvolution K z) (htk : t = k * z * k⁻¹)
    (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)) (hYH : Y ≤ H) (hKY : K ≤ Y) (hJY : conjSub k K ≤ Y)
    (hΛsub : Λ ⊆ restrictFamily Ω Y) (hΛc : ConjInvariant Λ) (hKΛ : K.subgroupOf Y ∈ Λ)
    (hJΛ : (conjSub k K).subgroupOf Y ∈ Λ) (hgen : (⨆ L ∈ Λ, L) = ⊤)
    (hT : ∀ L ∈ Λ, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = L)
    (hE : ∃ K' ∈ twinSet Λ (K.subgroupOf Y), K' ≠ K.subgroupOf Y)
    (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∀ (zY tY : ↥Y), (zY : G) = z → (tY : G) = t →
      E189QuotData n Λ (K.subgroupOf Y) ((conjSub k K).subgroupOf Y) zY tY := by
  classical
  intro zY tY hzY' htY'
  have hΦ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hΛ : HypOmegaGen Λ := hypOmegaGen_of_sub hΦ hΛsub hΛc
  have hΛcls : Q3CL.ClassicalClause Λ :=
    ⟨fun L hL => (classicalClause_restrict hcls Y).subnormal L (hΛsub hL),
      fun J hJ => (classicalClause_restrict hcls Y).commOdd J (hΛsub hJ)⟩
  have hΛq8 := fun L (hL : L ∈ Λ) => q8_restrict hq8 Y L (hΛsub hL)
  have hΛ2 := fun L (hL : L ∈ Λ) => two_restrict h2 Y L (hΛsub hL)
  have hΛA : ∀ L ∈ Λ, AEmpty Λ L :=
    aEmpty_of_sub hΦ hΛsub fun L hL => by
      obtain ⟨L₀, hL₀, hL₀Y, rfl⟩ := hL
      exact AEmpty.restrict hΩ hL₀Y (hAΩ L₀ hL₀)
  have hcard : Nat.card ↥Y < n := lt_of_le_of_lt (Subgroup.card_le_of_le hYH) hHn
  have hzY : z ∈ Y := hKY hz.mem
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  have hzJ : IsUniqueInvolution (conjSub k K) t := by
    have := hz.conj k
    rwa [← htk] at this
  have htY : t ∈ Y := hJY hzJ.mem
  have ht' := isUniqueInvolution_subgroupOf hzJ hJY
  have hzYe : zY = ⟨z, hzY⟩ := Subtype.ext hzY'
  have htYe : tY = ⟨t, htY⟩ := Subtype.ext htY'
  subst hzYe htYe
  have hzt' : (⟨z, hzY⟩ : Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  have hne' : conjSub (⟨t, htY⟩ : Y) (K.subgroupOf Y) ≠ K.subgroupOf Y := by
    intro h
    apply hne
    rw [conjSub_subgroupOf] at h
    have hle : conjSub t K ≤ Y := by
      have := conjSub_mono (n := t) hKY
      rwa [conjSub_eq_self_of_mem htY] at this
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this
  exact e189_quotData hcard hΛ hΛcls hΛq8 hΛ2 hΛA hgen hKΛ hJΛ hz' ht' hzt' hne' hT hE

theorem e189_apply_gen {n : ℕ}
    (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hAΩ : ∀ L ∈ Ω, AEmpty Ω L) {H K : Subgroup G} (hHn : Nat.card H < n) (hK : K ∈ Ω)
    {z t k : G} (hz : IsUniqueInvolution K z) (htk : t = k * z * k⁻¹)
    (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)) (hYH : Y ≤ H) (hKY : K ≤ Y) (hJY : conjSub k K ≤ Y)
    (hΛsub : Λ ⊆ restrictFamily Ω Y) (hΛc : ConjInvariant Λ) (hKΛ : K.subgroupOf Y ∈ Λ)
    (hJΛ : (conjSub k K).subgroupOf Y ∈ Λ) (hgen : (⨆ L ∈ Λ, L) = ⊤)
    (hT : ∀ L ∈ Λ, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = L)
    (hE : ∃ K' ∈ twinSet Λ (K.subgroupOf Y), K' ≠ K.subgroupOf Y)
    (hzt : z * t = t * z) (hne : conjSub t K ≠ K)
    (hcl : ∀ (zY tY : ↥Y), (zY : G) = z → (tY : G) = t →
      E189QuotData n Λ (K.subgroupOf Y) ((conjSub k K).subgroupOf Y) zY tY →
      E189ConclF (quotFamily Λ (classicalInvolutionOddCore ↥Y))
        ((K.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)))
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) zY)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) tY)) :
    E189ConclG Ω K H z t := by
  classical
  have hΦ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hΛ : HypOmegaGen Λ := hypOmegaGen_of_sub hΦ hΛsub hΛc
  have hzY : z ∈ Y := hKY hz.mem
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  have hzJ : IsUniqueInvolution (conjSub k K) t := by
    have := hz.conj k
    rwa [← htk] at this
  have htY : t ∈ Y := hJY hzJ.mem
  have ht' := isUniqueInvolution_subgroupOf hzJ hJY
  have hzt' : (⟨z, hzY⟩ : Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  have hne' : conjSub (⟨t, htY⟩ : Y) (K.subgroupOf Y) ≠ K.subgroupOf Y := by
    intro h
    apply hne
    rw [conjSub_subgroupOf] at h
    have hle : conjSub t K ≤ Y := by
      have := conjSub_mono (n := t) hKY
      rwa [conjSub_eq_self_of_mem htY] at this
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this
  have hqd := e189_quotData_G hΩ hcls hq8 h2 hAΩ hHn hK hz htk Y Λ hYH hKY hJY hΛsub hΛc hKΛ hJΛ
    hgen hT hE hzt hne ⟨z, hzY⟩ ⟨t, htY⟩ rfl rfl
  have hbar := hcl ⟨z, hzY⟩ ⟨t, htY⟩ rfl rfl hqd
  have hconcl : E189ConclF Λ (K.subgroupOf Y) ⟨z, hzY⟩ ⟨t, htY⟩ :=
    e189_lift_conclF hΛ hKΛ hz' ht' hzt' hne' hbar
  exact e189_conclG_of_conclF hΩ hK hz Y Λ hYH hKY hΛsub hzY htY hconcl

theorem e189_apply_q (hleaf : E189LeafQ8) (hodd : E189OddCoreQ8) {n : ℕ} (hih : EIH n)
    (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hAΩ : ∀ L ∈ Ω, AEmpty Ω L) {H K : Subgroup G} (hHn : Nat.card H < n) (hK : K ∈ Ω)
    {z t k : G} (hz : IsUniqueInvolution K z) (htk : t = k * z * k⁻¹)
    (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)) (hYH : Y ≤ H) (hKY : K ≤ Y) (hJY : conjSub k K ≤ Y)
    (hΛsub : Λ ⊆ restrictFamily Ω Y) (hΛc : ConjInvariant Λ) (hKΛ : K.subgroupOf Y ∈ Λ)
    (hJΛ : (conjSub k K).subgroupOf Y ∈ Λ) (hgen : (⨆ L ∈ Λ, L) = ⊤)
    (hT : ∀ L ∈ Λ, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = L)
    (hCb : ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
      L ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore ↥Y))
        ((K.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))))
    (hE : ∃ K' ∈ twinSet Λ (K.subgroupOf Y), K' ≠ K.subgroupOf Y)
    (hzt : z * t = t * z) (hne : conjSub t K ≠ K) : E189ConclG Ω K H z t := by
  refine e189_apply_gen hΩ hcls hq8 h2 hAΩ hHn hK hz htk Y Λ hYH hKY hJY hΛsub hΛc hKΛ hJΛ
    hgen hT hE hzt hne ?_
  intro zY tY hzY htY hqd
  by_cases hX : oddCoreImg (Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) zY} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))) = ⊥
  · exact hleaf n hih (↥Y ⧸ classicalInvolutionOddCore ↥Y) hqd.card _ hqd.hS hqd.cls _ hqd.hK
      hqd.trans hCb hqd.twin _ hqd.hz hX _ hqd.hJ _ hqd.ht hqd.hzt hqd.hne
  · exact hodd n hih (↥Y ⧸ classicalInvolutionOddCore ↥Y) hqd.card _ hqd.hS hqd.cls _ hqd.hK
      hqd.trans hCb hqd.twin _ hqd.hz hX _ hqd.hJ _ hqd.ht hqd.hzt hqd.hne

end Apply

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
