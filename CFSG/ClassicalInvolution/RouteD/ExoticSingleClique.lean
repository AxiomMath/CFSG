module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFacts
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet orth_or_twin)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem no_three_same (hodd : Odd (Nat.card K)) {L₁ L₂ L₃ : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h₁ : IsFundamental Q L₁ i) (h₂ : IsFundamental Q L₂ i)
    (h₃ : IsFundamental Q L₃ i) (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₂₃ : L₂ ≠ L₃) : False := by
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd h₁
  have e₂ := (huniq L₂ h₂).resolve_left fun e => n₁₂ e.symm
  have e₃ := (huniq L₃ h₃).resolve_left fun e => n₁₃ e.symm
  exact n₂₃ (e₂.trans e₃.symm)

theorem two_involutions_eq (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V < 12)
    {L₁ L₂ L₃ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ i₃ : V ≃ₗ[K] V} (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃) (c₁₂ : Commutes L₁ L₂)
    (c₁₃ : Commutes L₁ L₃) (c₂₃ : Commutes L₂ L₃) : i₂ = i₁ ∨ i₃ = i₁ ∨ i₃ = i₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n₁₂, n₁₃, n₂₃⟩ := hcon
  have o12 := (orth_or_twin hodd h₁ h₂ c₁₂).resolve_right n₁₂
  have o13 := (orth_or_twin hodd h₁ h₃ c₁₃).resolve_right n₁₃
  have o23 := (orth_or_twin hodd h₂ h₃ c₂₃).resolve_right n₂₃
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  obtain ⟨F₃, rfl, rfl⟩ := h₃
  have := three_orth_dim (span_le_perp_of_negSpace hodd o12) (span_le_perp_of_negSpace hodd o13)
    (span_le_perp_of_negSpace hodd o23)
  omega

theorem fundSet_four_pairing (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V < 12)
    {L₁ L₂ L₃ L₄ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ i₃ i₄ : V ≃ₗ[K] V}
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃)
    (h₄ : IsFundamental Q L₄ i₄) (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₁₄ : L₁ ≠ L₄)
    (n₂₃ : L₂ ≠ L₃) (n₂₄ : L₂ ≠ L₄) (n₃₄ : L₃ ≠ L₄) (c₁₂ : Commutes L₁ L₂)
    (c₁₃ : Commutes L₁ L₃) (c₁₄ : Commutes L₁ L₄) (c₂₃ : Commutes L₂ L₃)
    (c₂₄ : Commutes L₂ L₄) (c₃₄ : Commutes L₃ L₄) :
    (i₂ = i₁ ∧ i₄ = i₃) ∨ (i₃ = i₁ ∧ i₄ = i₂) ∨ (i₄ = i₁ ∧ i₃ = i₂) := by
  have t123 := two_involutions_eq hodd hdim h₁ h₂ h₃ c₁₂ c₁₃ c₂₃
  have t124 := two_involutions_eq hodd hdim h₁ h₂ h₄ c₁₂ c₁₄ c₂₄
  have t134 := two_involutions_eq hodd hdim h₁ h₃ h₄ c₁₃ c₁₄ c₃₄
  by_cases e12 : i₂ = i₁
  · by_cases e34 : i₄ = i₃
    · exact Or.inl ⟨e12, e34⟩
    · exfalso
      rcases t134 with e | e | e
      · exact no_three_same hodd h₁ (e12 ▸ h₂) (e ▸ h₃) n₁₂ n₁₃ n₂₃
      · exact no_three_same hodd h₁ (e12 ▸ h₂) (e ▸ h₄) n₁₂ n₁₄ n₂₄
      · exact e34 e
  · rcases t123 with e | e | e
    · exact absurd e e12
    · rcases t124 with f | f | f
      · exact absurd f e12
      · exact (no_three_same hodd h₁ (e ▸ h₃) (f ▸ h₄) n₁₃ n₁₄ n₃₄).elim
      · exact Or.inr (Or.inl ⟨e, f⟩)
    · rcases t124 with f | f | f
      · exact absurd f e12
      · exact Or.inr (Or.inr ⟨f, e⟩)
      · exact (no_three_same hodd h₂ (e ▸ h₃) (f ▸ h₄) n₂₃ n₂₄ n₃₄).elim

omit [FiniteDimensional K V] in
theorem ne_of_involution_ne (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h' : IsFundamental Q L' i') (hne : i ≠ i') :
    L ≠ L' := fun e => hne (IsFundamental.involution_unique hodd h (e ▸ h'))

omit [Finite K] [FiniteDimensional K V] in
theorem La_range_commutes_perp (F₁ G : OFrame Q) (hG : G.span ≤ F₁.perp) :
    Commutes F₁.La.range G.La.range :=
  (commutes_La_range_of_span_le_perp F₁ G hG).symm

variable [Invertible (2 : K)]

theorem fundSet_hasClique_of_family (hodd : Odd (Nat.card K)) {m : ℕ} (hm : 4 ≤ m)
    (w : Fin m → Bool → V) (hw : IsHypFam Q w) : FundHasClique (fundSet Q) := by
  intro R hR
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨i, F₁, rfl, rfl⟩ := hR
  have hF₁ : IsFundamental Q F₁.La.range (F₁.La (-1)) := IsFundamental.of_frame F₁
  obtain ⟨L₂, hL₂, hne2, hc2, -⟩ := IsFundamental.exists_twin hodd hF₁
  obtain ⟨G, hG⟩ := exists_frame_in_perp_of_isHypFam hm w hw F₁
  have hGi : IsFundamental Q G.La.range (G.La (-1)) := IsFundamental.of_frame G
  have hij : G.La (-1) ≠ F₁.La (-1) := La_neg_one_ne_of_span_le_perp h2 hG
  obtain ⟨L₄, hL₄, hne4, hc4, -⟩ := IsFundamental.exists_twin hodd hGi
  have htw₂ : IsFundTwin (fundSet Q) F₁.La.range L₂ :=
    isFundTwin_aux hodd hF₁ hL₂ hne2.symm hc2
  have htw₄ : IsFundTwin (fundSet Q) G.La.range L₄ :=
    isFundTwin_aux hodd hGi hL₄ hne4.symm hc4
  have hc13 : Commutes F₁.La.range G.La.range := La_range_commutes_perp F₁ G hG
  have n13 : F₁.La.range ≠ G.La.range := ne_of_involution_ne hodd hF₁ hGi hij.symm
  have n12 : F₁.La.range ≠ L₂ := hne2.symm
  have n14 : F₁.La.range ≠ L₄ := ne_of_involution_ne hodd hF₁ hL₄ hij.symm
  have n23 : L₂ ≠ G.La.range := ne_of_involution_ne hodd hL₂ hGi hij.symm
  have n24 : L₂ ≠ L₄ := ne_of_involution_ne hodd hL₂ hL₄ hij.symm
  have n34 : G.La.range ≠ L₄ := hne4.symm
  have hF₁mem : F₁.La.range ∈ fundSet Q := ⟨_, hF₁⟩
  have hGmem : G.La.range ∈ fundSet Q := ⟨_, hGi⟩
  have hL₂mem : L₂ ∈ fundSet Q := ⟨_, hL₂⟩
  have hL₄mem : L₄ ∈ fundSet Q := ⟨_, hL₄⟩
  have c14 : Commutes F₁.La.range L₄ := by
    rcases (htw₄.2.2 F₁.La.range hF₁mem).mp (Or.inr hc13) with e | e
    · exact absurd e n14
    · exact e
  have c23 : Commutes L₂ G.La.range := by
    rcases (htw₂.2.2 G.La.range hGmem).mp (Or.inr hc13.symm) with e | e
    · exact absurd e n23.symm
    · exact e.symm
  have c24 : Commutes L₂ L₄ := by
    rcases (htw₄.2.2 L₂ hL₂mem).mp (Or.inr c23) with e | e
    · exact absurd e n24
    · exact e
  exact ⟨L₂, hL₂mem, G.La.range, hGmem, L₄, hL₄mem, n12, n13, n14, n23, n24, n34, hc2, hc13, c14,
    c23, c24, hc4⟩

end Geometry

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem FundHasClique.of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L)
    (h : FundHasClique 𝓖) : FundHasClique 𝓕 := by
  intro R hR
  obtain ⟨S₂, hS₂, S₃, hS₃, S₄, hS₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24,
    c34⟩ := h _ (hmap R hR)
  obtain ⟨R₂, hR₂, rfl⟩ := hsurj S₂ hS₂
  obtain ⟨R₃, hR₃, rfl⟩ := hsurj S₃ hS₃
  obtain ⟨R₄, hR₄, rfl⟩ := hsurj S₄ hS₄
  exact ⟨R₂, hR₂, R₃, hR₃, R₄, hR₄, fun e => n12 (by rw [e]), fun e => n13 (by rw [e]),
    fun e => n14 (by rw [e]), fun e => n23 (by rw [e]), fun e => n24 (by rw [e]),
    fun e => n34 (by rw [e]), (Gaps.commutes_map_iff hker (hperf R hR)).mp c12,
    (Gaps.commutes_map_iff hker (hperf R hR)).mp c13,
    (Gaps.commutes_map_iff hker (hperf R hR)).mp c14,
    (Gaps.commutes_map_iff hker (hperf R₂ hR₂)).mp c23,
    (Gaps.commutes_map_iff hker (hperf R₂ hR₂)).mp c24,
    (Gaps.commutes_map_iff hker (hperf R₃ hR₃)).mp c34⟩

end Transport

section Quotient

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {KY : Type} [Group KY] {π : KY →* (V ≃ₗ[K] V)} {𝓕 : Set (Subgroup KY)}

theorem FundCliqueProd.of_centralQuot (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V < 12)
    (h : Gaps.CentralQuot π 𝓕 (fundSet Q) (scalars K V))
    (hker : ∃ ε ∈ π.ker, ∀ k ∈ π.ker, k = 1 ∨ k = ε) : FundCliqueProd 𝓕 := by
  obtain ⟨ε, hεker, hker'⟩ := hker
  intro R₁ hR₁ R₂ hR₂ R₃ hR₃ R₄ hR₄ n12 n13 n14 n23 n24 n34 c12 c13 c14 c23 c24 c34 r₁ hr₁ r₂
    hr₂ r₃ hr₃ r₄ hr₄ o₁ o₂ o₃ o₄ d12 d13 d14 d23 d24 d34
  obtain ⟨i₁, hi₁⟩ := h.map_mem R₁ hR₁
  obtain ⟨i₂, hi₂⟩ := h.map_mem R₂ hR₂
  obtain ⟨i₃, hi₃⟩ := h.map_mem R₃ hR₃
  obtain ⟨i₄, hi₄⟩ := h.map_mem R₄ hR₄
  have hπ₁ : π r₁ = i₁ := Gaps.invOf_eq hodd hi₁ (h.invOf hR₁ ⟨hr₁, o₁⟩)
  have hπ₂ : π r₂ = i₂ := Gaps.invOf_eq hodd hi₂ (h.invOf hR₂ ⟨hr₂, o₂⟩)
  have hπ₃ : π r₃ = i₃ := Gaps.invOf_eq hodd hi₃ (h.invOf hR₃ ⟨hr₃, o₃⟩)
  have hπ₄ : π r₄ = i₄ := Gaps.invOf_eq hodd hi₄ (h.invOf hR₄ ⟨hr₄, o₄⟩)
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

variable {p f : ℕ} [Fact p.Prime]

theorem cliqueFacts_plus_of_datum {n : ℕ} (hn3 : 3 ≤ n)
    (h : CliqueFactsOn (fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3))) :
    CliqueFacts p f .POmegaPlus n := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  show CliqueFactsOn (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D)
  rw [e]
  exact h

theorem plusFourCliqueFacts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : CliqueFacts p f .POmegaPlus 4 := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hdim := Gaps.finrank_plus p f 4
  have hodd := odd_card_galoisField hp2 hq
  have : Invertible (2 : GaloisField p f) :=
    invertibleOfNonzero (ModelFacts.two_ne_zero_galoisField f hp2)
  have hfam := isHypFam_of_pairs (fun i : Fin 4 => plusPair (GaloisField p f) i)
    (fun i j hij => plusPair_orth hij)
  have hQuot := Gaps.centralQuot_plus hp2 (le_refl 4) hn3 hq
  have hker : ∃ ε ∈ (spinAction (quadPlus 4 (GaloisField p f))).ker,
      ∀ k ∈ (spinAction (quadPlus 4 (GaloisField p f))).ker, k = 1 ∨ k = ε := by
    have h := coe_ker_spinMatrix_quadPlus (n := 4) (K := GaloisField p f)
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  exact cliqueFacts_plus_of_datum hn3
    ⟨⟨_, rankOne_mem_fundamentalSubgroups_plusDatum hn3 (⟨0, by omega⟩ : Fin 4)⟩,
      FundHasClique.of_central _ hQuot.ker_le hQuot.perf hQuot.map_mem hQuot.surj
        (fundSet_hasClique_of_family hodd (le_refl 4) _ hfam),
      FundCliqueProd.of_centralQuot hodd (by omega) hQuot hker⟩

theorem rowSinglePlusSmall : RowPiece p f ShapeSinglePlusSmall := by
  intro a t n hs
  obtain ⟨rfl, rfl, rfl⟩ := hs
  exact shapePiece_of_cliqueFacts (by decide) fun hp2 hq hadm =>
    ⟨RouteD.yData_plus hadm.2.2 hadm (by omega), plusFourCliqueFacts hp2 hq⟩

end CFSG.ClassicalInvolution.RouteD.Exotic
