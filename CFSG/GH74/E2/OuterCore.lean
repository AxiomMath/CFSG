module

public import CFSG.GH74.E2.CaseIInner
public import CFSG.GH74.E2.OuterAlpha
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.GH74.E2

open Subgroup

theorem two_le_pRank_of_comm_involutions {H : Type} [Group H] [Finite H] {x y : H}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hcomm : x * y = y * x) (hne : x ≠ y) :
    2 ≤ CFSG.pRank 2 H := by
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hx hy hcomm hne
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two V hV (by rw [hVcard]; norm_num)

theorem unique_involution_of_pRank {G : Type} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    {K : Subgroup G} (hKC : K ≤ Cen t)
    (hrk : CFSG.pRank 2 ↥(Subgroup.centralizer (K : Set G)) = 1) :
    ∀ u ∈ Cen t, (∀ k ∈ K, u * k = k * u) → u ^ 2 = 1 → u = 1 ∨ u = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu hcomm hu2
  by_contra hcon
  push Not at hcon
  obtain ⟨hu1, hut⟩ := hcon
  have htD : t ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (mem_Cen.1 (hKC hk)).symm
  have huD : u ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (hcomm k hk).symm
  have h := two_le_pRank_of_comm_involutions
    (H := ↥(Subgroup.centralizer (K : Set G))) (x := ⟨t, htD⟩) (y := ⟨u, huD⟩)
    (by rw [Subgroup.orderOf_mk]; exact ht)
    (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime hu2 hu1)
    (Subtype.ext (mem_Cen.1 hu)) (fun h => hut (congrArg Subtype.val h).symm)
  rw [hrk] at h
  exact absurd h (by norm_num)

theorem exists_sylow_haut_of_noQ8C2 {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (huniq : ∀ K' : Subgroup G, IsCompCen t K' → K' = K)
    (hQ8 : Nonempty (↥(Qt t) ≃* QuaternionGroup 2))
    (hT : ∀ u ∈ Cen t, (∀ k ∈ K, u * k = k * u) → u ^ 2 = 1 → u = 1 ∨ u = t)
    (hNo : NoQ8C2 (MulAut ↥K)) {R : Subgroup G} (hRK : R ≤ K) (hR2 : IsPGroup 2 R) {f g : G}
    (hfR : f ∈ R) (hgR : g ∈ R) (hf2 : f ^ 2 = 1) (hfg : f * g ≠ g * f) :
    ∃ S₁ : Subgroup G, S₁ ≤ Cen t ∧ IsPGroup 2 S₁ ∧ R ≤ S₁ ∧
      (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Cen t → S₁ ≤ P → P = S₁) ∧
      ∃ htS : t ∈ S₁, ∀ ψ : MulAut ↥S₁, ψ ⟨t, htS⟩ ∈ Subgroup.center ↥S₁ →
        ψ ⟨t, htS⟩ = ⟨t, htS⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huniq' : ∀ K₁ K₂ : Subgroup G, IsCompCen t K₁ → IsCompCen t K₂ → K₁ = K₂ :=
    fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm
  have hL := localK_of_component hH ht huniq' hK
  have hKC : K ≤ Cen t := hK.1
  have hRC : R ≤ Cen t := hRK.trans hKC
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hR' : IsPGroup 2 (R.subgroupOf (Cen t)) := hR2.comap_subtype
  obtain ⟨P, hRP⟩ := hR'.exists_le_sylow
  set S₁ : Subgroup G := (P : Subgroup ↥(Cen t)).map (Cen t).subtype with hS₁
  have hS₁C : S₁ ≤ Cen t := sylow_map_le (Cen t) P
  have hS₁2 : IsPGroup 2 S₁ := sylow_map_isPGroup (Cen t) P
  have hmax : ∀ P' : Subgroup G, IsPGroup 2 P' → P' ≤ Cen t → S₁ ≤ P' → P' = S₁ :=
    fun P' hP' hP'C hle => sylow_map_max (Cen t) P P' hP' hP'C hle
  have hRS : R ≤ S₁ := fun x hx => ⟨⟨x, hRC hx⟩, hRP (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hQS : Qt t ≤ S₁ := by
    have hQn : (CFSG.pCore 2 ↥(Cen t)).Normal := CFSG.pCore_normal (p := 2) (G := ↥(Cen t))
    have hQ2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥(Cen t)) :=
      CFSG.pCore_isPGroup (p := 2) (G := ↥(Cen t))
    have hle := hQ2.le_sylow_of_normal P
    intro q hq
    obtain ⟨hqC, hq'⟩ := mem_Qt.1 hq
    exact ⟨⟨q, hqC⟩, hle hq', rfl⟩
  have htS : t ∈ S₁ := hQS (t_mem_Qt ht)
  refine ⟨S₁, hS₁C, hS₁2, hRS, hmax, htS, ?_⟩
  have hKn : ∀ x ∈ Cen t, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    have h1 := hL.K_normal.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 h1
  have hnorm : S₁ ≤ Subgroup.normalizer (K : Set G) := by
    intro s hs
    have hsC : s ∈ Cen t := hS₁C hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hKn s hsC x hx
    · intro hx
      have h1 := hKn s⁻¹ (inv_mem hsC) _ hx
      simpa [mul_assoc] using h1
  let θ : ↥S₁ →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hθ : ∀ (u : ↥S₁) (k : ↥K),
      ((θ u k : ↥K) : G) = (u : G) * (k : G) * (u : G)⁻¹ := fun _ _ => rfl
  obtain ⟨eQ⟩ := hQ8
  have hq1 : ∀ x : QuaternionGroup 2, x * x = 1 → x = 1 ∨ x = (QuaternionGroup.a 1) ^ 2 := by
    decide
  have hq4 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 := by decide
  have hq2 : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = (QuaternionGroup.a 1) ^ 2 := by
    decide
  have hq3 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ := by decide
  let t0 : ↥(Qt t) := ⟨t, t_mem_Qt ht⟩
  have ht0 : t0 = (eQ.symm (QuaternionGroup.a 1)) ^ 2 := by
    have h1 : eQ t0 * eQ t0 = 1 := by
      rw [← map_mul]
      have : t0 * t0 = 1 := Subtype.ext (by rw [← sq]; exact ht2)
      rw [this, map_one]
    rcases hq1 _ h1 with h | h
    · exfalso
      have h2 : t0 = 1 := eQ.injective (h.trans (map_one eQ).symm)
      have h3 : t = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · rw [← map_pow, ← h]
      exact (eQ.symm_apply_apply t0).symm
  let ι : ↥(Qt t) →* ↥S₁ := Subgroup.inclusion hQS
  let iS : ↥S₁ := ι (eQ.symm (QuaternionGroup.a 1))
  let jS : ↥S₁ := ι (eQ.symm (QuaternionGroup.xa 0))
  let tS : ↥S₁ := ⟨t, htS⟩
  have hιt : ι t0 = tS := rfl
  have hi : iS ^ 2 = tS := by
    rw [← hιt, ht0, map_pow]
  have hi4 : iS ^ 4 = 1 := by
    show ι (eQ.symm (QuaternionGroup.a 1)) ^ 4 = 1
    rw [← map_pow, ← map_pow, hq4, map_one, map_one]
  have hj : jS ^ 2 = tS := by
    show ι (eQ.symm (QuaternionGroup.xa 0)) ^ 2 = tS
    rw [← map_pow, ← map_pow, hq2, map_pow, map_pow, ← hιt, ht0, map_pow]
  have hji : jS * iS * jS⁻¹ = iS⁻¹ := by
    let Φ : QuaternionGroup 2 →* ↥S₁ := ι.comp eQ.symm.toMonoidHom
    have hΦi : iS = Φ (QuaternionGroup.a 1) := rfl
    have hΦj : jS = Φ (QuaternionGroup.xa 0) := rfl
    rw [hΦi, hΦj, ← map_inv, ← map_mul, ← map_mul, hq3, map_inv]
  have hts2 : tS ^ 2 = 1 := Subtype.ext (by simpa using ht2)
  have hts : tS ∈ Subgroup.center ↥S₁ :=
    Subgroup.mem_center_iff.2 fun s => Subtype.ext (mem_Cen'.1 (hS₁C s.2))
  let fS : ↥S₁ := ⟨f, hRS hfR⟩
  let gS : ↥S₁ := ⟨g, hRS hgR⟩
  have hfS2 : fS ^ 2 = 1 := Subtype.ext (by simpa using hf2)
  have hfS : fS ∉ Subgroup.center ↥S₁ := by
    intro h
    have h1 := Subgroup.mem_center_iff.1 h gS
    exact hfg (congrArg Subtype.val h1).symm
  have hcomm : ∀ q ∈ Qt t, q * f = f * q := fun q hq =>
    Qt_commute_comp hH ht hK huniq q hq f (hRK hfR)
  have hfi : fS * iS = iS * fS :=
    Subtype.ext (hcomm _ (eQ.symm (QuaternionGroup.a 1)).2).symm
  have hfj : fS * jS = jS * fS :=
    Subtype.ext (hcomm _ (eQ.symm (QuaternionGroup.xa 0)).2).symm
  have hu : ∀ u : ↥S₁, θ u = 1 → u ^ 2 = 1 → u = 1 ∨ u = tS := by
    intro u hu hu2
    have hc : ∀ k ∈ K, (u : G) * k = k * (u : G) := by
      intro k hk
      have h1 := hθ u ⟨k, hk⟩
      rw [hu] at h1
      have h2 : (k : G) = (u : G) * k * (u : G)⁻¹ := h1
      calc (u : G) * k = (u : G) * k * (u : G)⁻¹ * u := by group
        _ = k * u := by rw [← h2]
    have hu2' : (u : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hu2
    rcases hT u (hS₁C u.2) hc hu2' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  exact no_alpha_of_noQ8C2 hNo θ hi hi4 hj hji hts2 hts hfS2 hfS hfi hfj hu

theorem false_of_haut_of_noncentral {G : Type} [Group G] [Finite G] {t : G}
    (hnc : ∀ S : Sylow 2 G, ¬ ((S : Subgroup G) ≤ Cen t)) {S₁ : Subgroup G} (hS₁C : S₁ ≤ Cen t)
    (hS₁2 : IsPGroup 2 S₁) (htS : t ∈ S₁)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Cen t → S₁ ≤ P → P = S₁)
    (haut : ∀ ψ : MulAut ↥S₁, ψ ⟨t, htS⟩ ∈ Subgroup.center ↥S₁ → ψ ⟨t, htS⟩ = ⟨t, htS⟩) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hP : ∃ P : Subgroup G, IsPGroup 2 P ∧ S₁ ≤ P ∧ P ≠ S₁
  · obtain ⟨n, hn, hne, hmem, hcent⟩ := exists_normalizer_moving hS₁C hmax htS hP
    exact hne (hfix_of_aut htS haut n hn _ hmem hcent rfl)
  · push Not at hP
    obtain ⟨S, hS⟩ := hS₁2.exists_le_sylow
    have hSeq : (S : Subgroup G) = S₁ := hP _ S.isPGroup' hS
    exact hnc S (hSeq ▸ hS₁C)

end CFSG.GH74.E2
