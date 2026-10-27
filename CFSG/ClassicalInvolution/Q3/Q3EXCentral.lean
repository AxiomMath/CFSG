module

public import CFSG.ClassicalInvolution.Q3.Q3EXGlue
public import CFSG.ClassicalInvolution.Q3.Q3EXD4Model
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGeom
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleClique
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Central

variable {X Y : Type} [Group X] [Finite X] [Group Y]

structure Central3 (π : X →* Y) (𝓕 : Set (Subgroup X)) (𝓖 : Set (Subgroup Y)) : Prop where
  ker_le : π.ker ≤ Subgroup.center X
  k3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1
  gen : ∀ R ∈ 𝓕, ModelFacts.Gen3 R
  inj : ∀ R ∈ 𝓕, ∀ r ∈ R, π r = 1 → r = 1
  map_mem : ∀ R ∈ 𝓕, R.map π ∈ 𝓖
  surj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L

variable {π : X →* Y} {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)}

theorem Central3.map_inj (h : Central3 π 𝓕 𝓖) {R R' : Subgroup X} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (e : R.map π = R'.map π) : R = R' :=
  eq_of_map_eq_gen3 π h.ker_le h.k3 (h.gen R hR) (h.gen R' hR') e

theorem Central3.commutes_iff (h : Central3 π 𝓕 𝓖) {R R' : Subgroup X} (hR : R ∈ 𝓕) :
    Commutes (R.map π) (R'.map π) ↔ Commutes R R' :=
  commutes_map_iff_gen3 π h.ker_le h.k3 (h.gen R hR)

theorem Central3.invOf (h : Central3 π 𝓕 𝓖) {R : Subgroup X} (hR : R ∈ 𝓕) {r : X}
    (hr : r ∈ R) (h2 : orderOf r = 2) : π r ∈ R.map π ∧ orderOf (π r) = 2 := by
  refine ⟨⟨r, hr, rfl⟩, ?_⟩
  have h1 : π r ≠ 1 := fun h1 => by
    have h2' := h.inj R hR r hr h1
    rw [h2', orderOf_one] at h2
    omega
  have h2' : π r ^ 2 = 1 := by
    rw [← map_pow, ← h2, pow_orderOf_eq_one, map_one]
  exact orderOf_eq_prime h2' h1

theorem IsFundTwin.of_map3 (h : Central3 π 𝓕 𝓖) {R R' : Subgroup X} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (htw : IsFundTwin 𝓖 (R.map π) (R'.map π)) : IsFundTwin 𝓕 R R' := by
  refine ⟨fun e => htw.1 (by rw [e]), (h.commutes_iff hR).mp htw.2.1, fun S hS => ?_⟩
  have key := htw.2.2 (S.map π) (h.map_mem S hS)
  rw [(⟨h.map_inj hS hR, fun e => by rw [e]⟩ : S.map π = R.map π ↔ S = R),
    (⟨h.map_inj hS hR', fun e => by rw [e]⟩ : S.map π = R'.map π ↔ S = R'),
    h.commutes_iff hS, h.commutes_iff hS] at key
  exact key

theorem IsFundTwin.to_map3 (h : Central3 π 𝓕 𝓖) {R R' : Subgroup X} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (htw : IsFundTwin 𝓕 R R') : IsFundTwin 𝓖 (R.map π) (R'.map π) := by
  refine ⟨fun e => htw.1 (h.map_inj hR hR' e), (h.commutes_iff hR).mpr htw.2.1, fun S' hS' => ?_⟩
  obtain ⟨S, hS, rfl⟩ := h.surj S' hS'
  have key := htw.2.2 S hS
  rw [(⟨h.map_inj hS hR, fun e => by rw [e]⟩ : S.map π = R.map π ↔ S = R),
    (⟨h.map_inj hS hR', fun e => by rw [e]⟩ : S.map π = R'.map π ↔ S = R'),
    h.commutes_iff hS, h.commutes_iff hS]
  exact key

theorem FundTwinsExist.of_central3 (h : Central3 π 𝓕 𝓖)
    (h' : ∀ L ∈ 𝓖, ∃ L' ∈ 𝓖, IsFundTwin 𝓖 L L') : FundTwinsExist 𝓕 := by
  intro R hR
  obtain ⟨L', hL', htw⟩ := h' _ (h.map_mem R hR)
  obtain ⟨R', hR', rfl⟩ := h.surj L' hL'
  exact ⟨R', hR', IsFundTwin.of_map3 h hR hR' htw⟩

theorem FundHubUnique.of_central3 (h : Central3 π 𝓕 𝓖) (h' : FundHubUnique 𝓖) :
    FundHubUnique 𝓕 := by
  intro R hR S₁ hS₁ S₂ hS₂ h₁ h₂
  have hub : ∀ S ∈ 𝓕, IsHub 𝓕 R S → IsHub 𝓖 (R.map π) (S.map π) := by
    rintro S hS ⟨hne, hc, hall⟩
    refine ⟨fun e => hne (h.map_inj hS hR e), (h.commutes_iff hS).mpr hc,
      fun S'' hS'' hc'' hne'' => ?_⟩
    obtain ⟨S', hS', rfl⟩ := h.surj S'' hS''
    have hcS' : Commutes S' R := (h.commutes_iff hS').mp hc''
    have hneS : S' ≠ S := fun e => hne'' (by rw [e])
    exact (h.commutes_iff hS').mpr (hall S' hS' hcS' hneS)
  exact h.map_inj hS₁ hS₂
    (h' _ (h.map_mem R hR) _ (h.map_mem S₁ hS₁) _ (h.map_mem S₂ hS₂) (hub S₁ hS₁ h₁)
      (hub S₂ hS₂ h₂))

theorem TwinWithinCentralizer.of_central3 (h : Central3 π 𝓕 𝓖) (h' : TwinWithinCentralizer 𝓖) :
    TwinWithinCentralizer 𝓕 := by
  intro R hR A hA B hB hAB hcAB hAR hBR hnb
  have hinj : ∀ {S T : Subgroup X}, S ∈ 𝓕 → T ∈ 𝓕 → (S.map π = T.map π ↔ S = T) :=
    fun hS hT => ⟨h.map_inj hS hT, fun e => by rw [e]⟩
  refine IsFundTwin.of_map3 h hA hB
    (h' (R.map π) (h.map_mem R hR) (A.map π) (h.map_mem A hA) (B.map π) (h.map_mem B hB)
      (fun e => hAB ((hinj hA hB).mp e)) ((h.commutes_iff hA).mpr hcAB)
      ((h.commutes_iff hA).mpr hAR) ((h.commutes_iff hB).mpr hBR) fun T' hT' hT'R => ?_)
  obtain ⟨T, hT, rfl⟩ := h.surj T' hT'
  have hc := (h.commutes_iff hT).mp hT'R
  rw [hinj hT hA, hinj hT hB, h.commutes_iff hT, h.commutes_iff hT]
  exact hnb T hT hc

theorem FundHasOrthogonal.of_central3 (h : Central3 π 𝓕 𝓖) (h' : FundHasOrthogonal 𝓖) :
    FundHasOrthogonal 𝓕 := by
  intro R hR
  obtain ⟨S', hS', hne, hc, hnt⟩ := h' _ (h.map_mem R hR)
  obtain ⟨S, hS, rfl⟩ := h.surj S' hS'
  exact ⟨S, hS, fun e => hne (by rw [e]), (h.commutes_iff hS).mp hc,
    fun htw => hnt (IsFundTwin.to_map3 h hR hS htw)⟩

theorem FundHasClique.of_central3 (h : Central3 π 𝓕 𝓖) (h' : FundHasClique 𝓖) :
    FundHasClique 𝓕 := by
  intro R hR
  obtain ⟨S₂, hS₂, S₃, hS₃, S₄, hS₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24,
    c34⟩ := h' _ (h.map_mem R hR)
  obtain ⟨R₂, hR₂, rfl⟩ := h.surj S₂ hS₂
  obtain ⟨R₃, hR₃, rfl⟩ := h.surj S₃ hS₃
  obtain ⟨R₄, hR₄, rfl⟩ := h.surj S₄ hS₄
  exact ⟨R₂, hR₂, R₃, hR₃, R₄, hR₄, fun e => n12 (by rw [e]), fun e => n13 (by rw [e]),
    fun e => n14 (by rw [e]), fun e => n23 (by rw [e]), fun e => n24 (by rw [e]),
    fun e => n34 (by rw [e]), (h.commutes_iff hR).mp c12, (h.commutes_iff hR).mp c13,
    (h.commutes_iff hR).mp c14, (h.commutes_iff hR₂).mp c23, (h.commutes_iff hR₂).mp c24,
    (h.commutes_iff hR₃).mp c34⟩

end Central

section Quotient

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {KY : Type} [Group KY] [Finite KY] {π : KY →* (V ≃ₗ[K] V)}
  {𝓕 : Set (Subgroup KY)}

theorem TwinInvolutionKernel.of_central3 (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank K V)
    (h : Central3 π 𝓕 (fundSet Q)) (hker : ∃ ε ∈ π.ker, ∀ k ∈ π.ker, k = 1 ∨ k = ε) :
    TwinInvolutionKernel 𝓕 := by
  obtain ⟨ε, hεker, hker'⟩ := hker
  refine ⟨ε, fun R hR R' hR' hRR' r hr r' hr' hr2 hr'2 => ?_⟩
  have htw := IsFundTwin.to_map3 h hR hR' hRR'
  obtain ⟨i, hi⟩ := h.map_mem R hR
  obtain ⟨i', hi'⟩ := h.map_mem R' hR'
  have hπr : π r = i := Gaps.invOf_eq hodd hi (h.invOf hR hr hr2)
  have hπr' : π r' = i' := Gaps.invOf_eq hodd hi' (h.invOf hR' hr' hr'2)
  have hii : i' = i := fundSet_twin_involution hodd hQ hdim hi hi' htw
  have hr'sq : r' * r' = 1 := by
    have := pow_orderOf_eq_one r'
    rwa [hr'2, pow_two] at this
  by_cases hrr : r = r'
  · exact Or.inl hrr
  · exact Or.inr (mul_eq_of_map_eq π h.ker_le hεker hker' hr'sq (by rw [hπr, hπr', hii]) hrr)

theorem FundCliqueProd.of_central3 (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V < 12)
    (h : Central3 π 𝓕 (fundSet Q)) (hker : ∃ ε ∈ π.ker, ∀ k ∈ π.ker, k = 1 ∨ k = ε) :
    FundCliqueProd 𝓕 := by
  obtain ⟨ε, hεker, hker'⟩ := hker
  intro R₁ hR₁ R₂ hR₂ R₃ hR₃ R₄ hR₄ n12 n13 n14 n23 n24 n34 c12 c13 c14 c23 c24 c34 r₁ hr₁ r₂
    hr₂ r₃ hr₃ r₄ hr₄ o₁ o₂ o₃ o₄ d12 d13 d14 d23 d24 d34
  obtain ⟨i₁, hi₁⟩ := h.map_mem R₁ hR₁
  obtain ⟨i₂, hi₂⟩ := h.map_mem R₂ hR₂
  obtain ⟨i₃, hi₃⟩ := h.map_mem R₃ hR₃
  obtain ⟨i₄, hi₄⟩ := h.map_mem R₄ hR₄
  have hπ₁ : π r₁ = i₁ := Gaps.invOf_eq hodd hi₁ (h.invOf hR₁ hr₁ o₁)
  have hπ₂ : π r₂ = i₂ := Gaps.invOf_eq hodd hi₂ (h.invOf hR₂ hr₂ o₂)
  have hπ₃ : π r₃ = i₃ := Gaps.invOf_eq hodd hi₃ (h.invOf hR₃ hr₃ o₃)
  have hπ₄ : π r₄ = i₄ := Gaps.invOf_eq hodd hi₄ (h.invOf hR₄ hr₄ o₄)
  have hsq : ∀ {x : KY}, orderOf x = 2 → x * x = 1 := by
    intro x hx
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have k12 : r₁ * r₂ = r₂ * r₁ := c12 r₁ hr₁ r₂ hr₂
  have k13 : r₁ * r₃ = r₃ * r₁ := c13 r₁ hr₁ r₃ hr₃
  have k14 : r₁ * r₄ = r₄ * r₁ := c14 r₁ hr₁ r₄ hr₄
  have k23 : r₂ * r₃ = r₃ * r₂ := c23 r₂ hr₂ r₃ hr₃
  have k24 : r₂ * r₄ = r₄ * r₂ := c24 r₂ hr₂ r₄ hr₄
  have k34 : r₃ * r₄ = r₄ * r₃ := c34 r₃ hr₃ r₄ hr₄
  have hεc : ∀ x : KY, ε * x = x * ε := fun x =>
    (Subgroup.mem_center_iff.mp (h.ker_le hεker) x).symm
  have pairing := fundSet_four_pairing hodd hdim hi₁ hi₂ hi₃ hi₄
    (fun e => n12 (h.map_inj hR₁ hR₂ e)) (fun e => n13 (h.map_inj hR₁ hR₃ e))
    (fun e => n14 (h.map_inj hR₁ hR₄ e)) (fun e => n23 (h.map_inj hR₂ hR₃ e))
    (fun e => n24 (h.map_inj hR₂ hR₄ e)) (fun e => n34 (h.map_inj hR₃ hR₄ e))
    ((h.commutes_iff hR₁).mpr c12) ((h.commutes_iff hR₁).mpr c13) ((h.commutes_iff hR₁).mpr c14)
    ((h.commutes_iff hR₂).mpr c23) ((h.commutes_iff hR₂).mpr c24) ((h.commutes_iff hR₃).mpr c34)
  rcases pairing with ⟨e₂, e₄⟩ | ⟨e₃, e₄⟩ | ⟨e₄, e₃⟩
  · have a := mul_eq_of_map_eq π h.ker_le hεker hker' (hsq o₂) (by rw [hπ₁, hπ₂, e₂]) d12
    have b := mul_eq_of_map_eq π h.ker_le hεker hker' (hsq o₄) (by rw [hπ₃, hπ₄, e₄]) d34
    have hεε : ε * ε = 1 := by rw [← a]; exact mul_self_of_commute (hsq o₁) (hsq o₂) k12
    calc r₁ * r₂ * r₃ * r₄ = (r₁ * r₂) * (r₃ * r₄) := by group
      _ = 1 := by rw [a, b, hεε]
  · have a := mul_eq_of_map_eq π h.ker_le hεker hker' (hsq o₃) (by rw [hπ₁, hπ₃, e₃]) d13
    have b := mul_eq_of_map_eq π h.ker_le hεker hker' (hsq o₄) (by rw [hπ₂, hπ₄, e₄]) d24
    have hεε : ε * ε = 1 := by rw [← a]; exact mul_self_of_commute (hsq o₁) (hsq o₃) k13
    calc r₁ * r₂ * r₃ * r₄ = r₁ * (r₂ * r₃) * r₄ := by group
      _ = r₁ * (r₃ * r₂) * r₄ := by rw [k23]
      _ = (r₁ * r₃) * (r₂ * r₄) := by group
      _ = 1 := by rw [a, b, hεε]
  · have a := mul_eq_of_map_eq π h.ker_le hεker hker' (hsq o₄) (by rw [hπ₁, hπ₄, e₄]) d14
    have b := mul_eq_of_map_eq π h.ker_le hεker hker' (hsq o₃) (by rw [hπ₂, hπ₃, e₃]) d23
    have hεε : ε * ε = 1 := by rw [← a]; exact mul_self_of_commute (hsq o₁) (hsq o₄) k14
    calc r₁ * r₂ * r₃ * r₄ = r₁ * (r₂ * r₃) * r₄ := by group
      _ = r₁ * ε * r₄ := by rw [b]
      _ = ε * r₁ * r₄ := by rw [← hεc r₁]
      _ = ε * (r₁ * r₄) := by group
      _ = 1 := by rw [a, hεε]

end Quotient

section Ctx

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)} {𝓕 : Set (Subgroup (spinGroup Q))}

theorem central3_of_ctx3 [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (hconj : ∀ R ∈ 𝓕, ∀ g : spinGroup Q, conjSub g R ∈ 𝓕)
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : spinGroup Q, R' = conjSub g R) (hne : 𝓕.Nonempty) :
    Central3 (spinAction Q) 𝓕 (fundSet Q) := by
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨fr₀, himg⟩ := c.hframe _ hR₀
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have h1 := ModelFacts.finrank_perp_add_four fr₀
    have h2 := c.hdim
    omega
  have hpos : 0 < Module.finrank 𝔽₃ (ι → 𝔽₃) := by
    have := c.hdim
    omega
  have : Nontrivial (ι → 𝔽₃) := Module.finrank_pos_iff.mp hpos
  have hcorr := spin_fund_correspondence odd_natCard_galoisField_three c.hQ hR₀ hconj
    (fun R hR => hsingle _ hR₀ R hR) fr₀ himg hperp
  refine ⟨ker_spinAction_le_center Q, ?_, c.hG3, ?_, hcorr.1, hcorr.2⟩
  · intro x hx h3
    have h2 : x * x = 1 := c.hker2 x hx
    have h : x ^ 3 = x ^ 2 * x := pow_succ x 2
    rw [h, pow_two, h2, one_mul] at h3
    exact h3
  · intro R hR r hr h1
    obtain ⟨fr, hfr⟩ := c.hframe R hR
    obtain ⟨e⟩ := c.hsl2 R hR
    have hcard : Nat.card R = Nat.card (R.map (spinAction Q)) := by
      rw [hfr, Nat.card_congr e.toEquiv]
      exact (Nat.card_congr (MonoidHom.ofInjective fr.La_injective).toEquiv)
    exact injOn_of_natCard_map3 (spinAction Q) hcard r hr 1 R.one_mem
      (h1.trans (map_one _).symm)

end Ctx

end CFSG.ClassicalInvolution.Q3.Q3W.EX
