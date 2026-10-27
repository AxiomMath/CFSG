module

public import CFSG.ClassicalInvolution.SmallCases.G2STypeA
public import CFSG.ClassicalInvolution.SmallCases.G2SMem
public import CFSG.ClassicalInvolution.SmallCases.G2SRank3
public import CFSG.ClassicalInvolution.SmallCases.NDBH4R1
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem typeB_of_pair [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G}
    {z : G} (C : Ctx p f (𝒞 K) K z) (hconn : RouteD.DeltaConnected (𝒞 K)) {M M' : Subgroup G}
    (hM : M ∈ nbhd (𝒞 K) K) (hM' : M' ∈ nbhd (𝒞 K) K) (hne : M ≠ M') {t s : G}
    (ht : IsClassicalMember p f M t) (hs : IsClassicalMember p f M' s) (hts : t * s = s * t) :
    ∀ x ∈ layer (𝒞 K) M, (s * z) * x = x * (s * z) := by
  have Ct := C.at_member hM.1 ht
  have hKM : K ∈ nbhd (𝒞 K) M := nbhd_symm C.mem hM
  have hs2 : s * s = 1 := by
    have h2 : s ^ 2 = 1 := by rw [← hs.orderOf_eq_two]; exact pow_orderOf_eq_one s
    simpa [pow_two] using h2
  rcases Ct.lemmaA hKM C.cls hs2 hts.symm (fun x hx => (hM'.2.2 x hx s hs.mem).symm) with
    hA | hB
  · exact (C.typeA_false hnab hconn hM hM' hne ht hs hts hA).elim
  · exact hB

theorem not_central_of_mem_layer (C : Ctx p f Ω L w) {x : G} (hx : x ∈ layer Ω L)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : ¬ ∀ y ∈ layer Ω L, x * y = y * x := by
  classical
  intro hcen
  obtain ⟨D, i₁, hcard, htag, hrest⟩ := C.exists_data
  have he : 1 ≤ D.exp i₁ := (D.admissible i₁).2.1
  have hψ : Function.Injective (D.hom i₁) :=
    injective_of_ker_le_center C.odd htag (D.rank i₁) he (D.hom i₁) (D.ker_le_center i₁)
  have hxY : x ∈ locLayer Ω w := C.layer_le_locLayer hx
  obtain ⟨g, hg⟩ := C.mk_mem_range_of_mem_layer D i₁ hcard htag hrest hx hxY
  have hgc : ∀ e' : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K,
      g * e' = e' * g := by
    intro e'
    obtain ⟨y, hyL, hy⟩ := C.range_le_map_layer D i₁ hcard htag hrest ⟨e', rfl⟩
    apply hψ
    have hg' : D.hom i₁ g = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
        ⟨x, hxY⟩ := hg
    rw [map_mul, map_mul, hg', ← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcen y hyL)
  have hg1 : g = 1 := by
    have hbot := center_modelUniv_g2d4_eq_bot C.odd htag (D.rank i₁) he
    have : g ∈ Subgroup.center (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K :=
      Subgroup.mem_center_iff.mpr fun e' => (hgc e').symm
    rw [hbot] at this
    exact this
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨x, hxY⟩ = 1 := by
    rw [← hg, hg1, map_one]
  have hO : (⟨x, hxY⟩ : ↥(locLayer Ω w)) ∈ classicalInvolutionOddCore ↥(locLayer Ω w) :=
    (QuotientGroup.eq_one_iff _).mp h1
  have := eq_one_of_mem_oddCore_of_sq hO (Subtype.ext hx2)
  exact hx1 (congrArg Subtype.val this)

theorem false_of_three [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G}
    {z : G} (C : Ctx p f (𝒞 K) K z) (hconn : RouteD.DeltaConnected (𝒞 K))
    {N₀ N₁ N₂ N₃ : Subgroup G} {t₀ t₁ t₂ t₃ : G} (hN₀ : N₀ ∈ nbhd (𝒞 K) K)
    (hN₁ : N₁ ∈ nbhd (𝒞 K) K) (hN₂ : N₂ ∈ nbhd (𝒞 K) K) (hN₃ : N₃ ∈ nbhd (𝒞 K) K)
    (h₀ : IsClassicalMember p f N₀ t₀) (h₁ : IsClassicalMember p f N₁ t₁)
    (h₂ : IsClassicalMember p f N₂ t₂) (h₃ : IsClassicalMember p f N₃ t₃)
    (hne₁ : N₀ ≠ N₁) (hne₂ : N₀ ≠ N₂) (hne₃ : N₀ ≠ N₃) (hc₁ : t₀ * t₁ = t₁ * t₀)
    (hc₂ : t₀ * t₂ = t₂ * t₀) (hc₃ : t₀ * t₃ = t₃ * t₀) (hprod : t₁ * t₂ * t₃ = 1) : False := by
  have hz2 : z * z = 1 := by
    have h2 : z ^ 2 = 1 := by rw [← C.cls.orderOf_eq_two]; exact pow_orderOf_eq_one z
    simpa [pow_two] using h2
  have hz1 : z ≠ 1 := by
    intro h
    have := C.cls.orderOf_eq_two
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzc : ∀ {N : Subgroup G} {t : G}, N ∈ nbhd (𝒞 K) K → IsClassicalMember p f N t →
      z * t = t * z := fun {_ t} hN ht => (hN.2.2 z C.cls.mem t ht.mem)
  have B₁ := C.typeB_of_pair hnab hconn hN₀ hN₁ hne₁ h₀ h₁ hc₁
  have B₂ := C.typeB_of_pair hnab hconn hN₀ hN₂ hne₂ h₀ h₂ hc₂
  have B₃ := C.typeB_of_pair hnab hconn hN₀ hN₃ hne₃ h₀ h₃ hc₃
  have hz₂ := hzc hN₂ h₂
  have hz₃ := hzc hN₃ h₃
  have hg : (t₁ * z) * (t₂ * z) * (t₃ * z) = z := by
    calc (t₁ * z) * (t₂ * z) * (t₃ * z) = t₁ * (z * t₂) * z * (t₃ * z) := by group
      _ = t₁ * (t₂ * z) * z * (t₃ * z) := by rw [hz₂]
      _ = t₁ * t₂ * (z * z) * (t₃ * z) := by group
      _ = t₁ * t₂ * t₃ * z := by rw [hz2]; group
      _ = z := by rw [hprod, one_mul]
  have hzcen : ∀ y ∈ layer (𝒞 K) N₀, z * y = y * z := by
    intro y hy
    have e1 := B₁ y hy
    have e2 := B₂ y hy
    have e3 := B₃ y hy
    calc z * y = (t₁ * z) * (t₂ * z) * (t₃ * z) * y := by rw [hg]
      _ = (t₁ * z) * (t₂ * z) * ((t₃ * z) * y) := by group
      _ = (t₁ * z) * (t₂ * z) * (y * (t₃ * z)) := by rw [e3]
      _ = (t₁ * z) * ((t₂ * z) * y) * (t₃ * z) := by group
      _ = (t₁ * z) * (y * (t₂ * z)) * (t₃ * z) := by rw [e2]
      _ = ((t₁ * z) * y) * (t₂ * z) * (t₃ * z) := by group
      _ = (y * (t₁ * z)) * (t₂ * z) * (t₃ * z) := by rw [e1]
      _ = y * ((t₁ * z) * (t₂ * z) * (t₃ * z)) := by group
      _ = y * z := by rw [hg]
  have C₀ := C.at_member hN₀.1 h₀
  have hzL : z ∈ layer (𝒞 K) N₀ := le_layer (nbhd_symm C.mem hN₀) C.cls.mem
  exact C₀.not_central_of_mem_layer hzL hz2 hz1 hzcen

end Ctx

theorem g2d4SingleNoTwin_proved : G2D4SingleNoTwin p f := by
  intro G _ _ _ hnab K z S hnt tY nY htY hsh
  have C := ctx_of_setup S (Gaps.fundNoncentral p) (g2d4SharedInvolution p)
    (Balance.Bootstrap.twoClassInvolutionsConj p) hnt htY hsh
  obtain ⟨D, i₁, hcard, htag, hrest⟩ := C.exists_data
  obtain ⟨N₀, hN₀⟩ := C.nbhd_nonempty D i₁ htag
  obtain ⟨t₀, ht₀⟩ := C.inClass.classical N₀ hN₀.1
  obtain ⟨R, hR, -, r, hrR, hr2, hr1, hrc, hr⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hN₀ ht₀
  obtain ⟨x, x', hx2, hx'2, hx1, hx'1, hxx', hrx, hrx', hxcomm, hxr, hx'r, hxx'r⟩ :=
    exists_rank_three_model C.odd (D.admissible i₁) htag hR hrR hrc hr2 hr1
  have hxx'2 : (x * x') * (x * x') = 1 := by
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [← hxcomm]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  have hxx'1 : x * x' ≠ 1 := by
    intro h
    exact hxx' (by
      calc x = x * (x' * x'⁻¹) := by group
        _ = (x * x') * x'⁻¹ := by group
        _ = x'⁻¹ := by rw [h, one_mul]
        _ = x' := inv_eq_of_mul_eq_one_right hx'2)
  obtain ⟨N₁, t₁, ht₁Y, hN₁, h₁, hmk₁⟩ :=
    C.exists_member_of_involution D i₁ hcard htag hrest hx2 hx1
  obtain ⟨N₂, t₂, ht₂Y, hN₂, h₂, hmk₂⟩ :=
    C.exists_member_of_involution D i₁ hcard htag hrest hx'2 hx'1
  obtain ⟨N₃, t₃, ht₃Y, hN₃, h₃, hmk₃⟩ :=
    C.exists_member_of_involution D i₁ hcard htag hrest hxx'2 hxx'1
  have he : 1 ≤ D.exp i₁ := (D.admissible i₁).2.1
  have hψ : Function.Injective (D.hom i₁) :=
    injective_of_ker_le_center C.odd htag (D.rank i₁) he (D.hom i₁) (D.ker_le_center i₁)
  have hsq : ∀ {N : Subgroup G} {u : G}, IsClassicalMember p f N u → u * u = 1 := by
    intro N u hu
    have h2 : u ^ 2 = 1 := by rw [← hu.orderOf_eq_two]; exact pow_orderOf_eq_one u
    simpa [pow_two] using h2
  have ht₀Y : t₀ ∈ locLayer (𝒞 K) z :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hN₀) ht₀.mem
  have hcomm : ∀ {t : G} {y : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K}
      (htY : t ∈ locLayer (𝒞 K) z), t * t = 1 →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (𝒞 K) z)) ⟨t, htY⟩ = D.hom i₁ y →
      r * y = y * r → t₀ * t = t * t₀ := by
    intro t y htY ht2 hmk hry
    refine commute_of_mk_commute C.p1 ht₀Y htY (hsq ht₀) ht2 ?_
    rw [hmk, ← hr, ← map_mul, ← map_mul, hry]
  have hdist : ∀ {N : Subgroup G} {t : G} {y : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁)
      Fact.out).K} (htY : t ∈ locLayer (𝒞 K) z), IsClassicalMember p f N t →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (𝒞 K) z)) ⟨t, htY⟩ =
        D.hom i₁ y → y ≠ r → N₀ ≠ N := by
    intro N t y htY hcl hmk hyr h
    have h' : IsClassicalMember p f N₀ t := h ▸ hcl
    have heq : t₀ = t :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.odd C.five ht₀).eq
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.odd C.five h')
    apply hyr
    apply hψ
    have e : (⟨t₀, ht₀Y⟩ : ↥(locLayer (𝒞 K) z)) = ⟨t, htY⟩ := Subtype.ext heq
    rw [← hmk, hr, e]
  have ht₁₂ : t₁ * t₂ = t₂ * t₁ := by
    refine commute_of_mk_commute C.p1 ht₁Y ht₂Y (hsq h₁) (hsq h₂) ?_
    rw [hmk₁, hmk₂, ← map_mul, ← map_mul, hxcomm]
  have ht₁₂Y : t₁ * t₂ ∈ locLayer (𝒞 K) z := Subgroup.mul_mem _ ht₁Y ht₂Y
  have hprod : t₁ * t₂ * t₃ = 1 := by
    have h12 : t₁ * t₂ = t₃ := by
      refine eq_of_mk_eq_of_involutions C.p1 ht₁₂Y ht₃Y ?_ (hsq h₃) ?_
      · calc t₁ * t₂ * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by group
          _ = t₁ * (t₁ * t₂) * t₂ := by rw [← ht₁₂]
          _ = (t₁ * t₁) * (t₂ * t₂) := by group
          _ = 1 := by rw [hsq h₁, hsq h₂, one_mul]
      · have e : (⟨t₁ * t₂, ht₁₂Y⟩ : ↥(locLayer (𝒞 K) z)) = ⟨t₁, ht₁Y⟩ * ⟨t₂, ht₂Y⟩ :=
          Subtype.ext rfl
        rw [e, map_mul, hmk₁, hmk₂, ← map_mul, hmk₃]
    rw [h12]
    exact hsq h₃
  exact C.false_of_three hnab S.conn hN₀ hN₁ hN₂ hN₃ ht₀ h₁ h₂ h₃ (hdist ht₁Y h₁ hmk₁ hxr)
    (hdist ht₂Y h₂ hmk₂ hx'r) (hdist ht₃Y h₃ hmk₃ hxx'r) (hcomm ht₁Y (hsq h₁) hmk₁ hrx)
    (hcomm ht₂Y (hsq h₂) hmk₂ hrx') (hcomm ht₃Y (hsq h₃) hmk₃ (by
      rw [← mul_assoc, hrx, mul_assoc, hrx', mul_assoc]))
    hprod

end CFSG.ClassicalInvolution.NDB.G2S
