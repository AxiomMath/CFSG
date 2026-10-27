module

public import CFSG.GH74.Uniqueness.Section5Prop52

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem IsMaxFixingThree.map_conjugate {p : ℕ} {P : Subgroup X} (hP : IsMaxFixingThree M p P)
    (g : X) : IsMaxFixingThree M p (conjugate P g) := by
  refine ⟨⟨isPGroup_conjugate hP.1.1 g, by rw [ncard_omegaFix_conjugate]; exact hP.1.2⟩,
    fun Q hQ hle => ?_⟩
  have hQ' : IsPGroup p (conjugate Q g⁻¹) ∧
      3 ≤ (omegaFix M ((conjugate Q g⁻¹ : Subgroup X) : Set X)).ncard :=
    ⟨isPGroup_conjugate hQ.1 g⁻¹, by rw [ncard_omegaFix_conjugate]; exact hQ.2⟩
  have hle' : P ≤ conjugate Q g⁻¹ := by
    have := conjugate_mono hle g⁻¹
    rwa [conjugate_conjugate_inv] at this
  have := conjugate_mono (hP.2 hQ' hle') g
  rwa [conjugate_inv_conjugate] at this

theorem IsProductDisconnected.lemma55_maxFixingThree (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsMaxFixingThree M p P) {β δ : Subgroup X}
    (hβ : β ∈ omegaFix M (P : Set X)) (hδ : δ ∈ omegaFix M (P : Set X)) (hβδ : β ≠ δ)
    (hno : ∀ s ∈ Z, s ∈ normalizer (P : Set X) → conjugate β s ≠ δ) {R : Subgroup X}
    (hR : ABGLocalTools.IsSylowOf p R (β ⊓ δ)) (hPR : P ≤ R) :
    omegaFix M (R : Set X) = {β, δ} ∧ P < R := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hβΩ, -⟩ := h.mem_omegaFix_iff.mp hβ
  obtain ⟨hδΩ, -⟩ := h.mem_omegaFix_iff.mp hδ
  have hβR : β ∈ omegaFix M (R : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hβΩ, hR.le.trans inf_le_left⟩
  have hδR : δ ∈ omegaFix M (R : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hδΩ, hR.le.trans inf_le_right⟩
  obtain ⟨s, hs, hsR, hs1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 hβΩ hδΩ hβδ hR
  have hΩR : omegaFix M (R : Set X) = {β, δ} := by
    by_contra hne
    have h3 : 3 ≤ (omegaFix M (R : Set X)).ncard := by
      by_contra hlt
      apply hne
      symm
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · rintro x (rfl | rfl)
        · exact hβR
        · exact hδR
      · rw [Set.ncard_pair hβδ]
        omega
    have hRP : R = P := le_antisymm (hP.2 ⟨hR.isPGroup, h3⟩ hPR) hPR
    rw [hRP] at hsR
    exact hno s hs hsR hs1
  refine ⟨hΩR, lt_of_le_of_ne hPR fun heq => ?_⟩
  have h3 := hP.1.2
  rw [heq, hΩR, Set.ncard_pair hβδ] at h3
  omega

theorem IsProductDisconnected.prop53_key (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsMaxFixingThree M p P) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    (hzN : z ∈ normalizer (P : Set X)) : P ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hPM
  have hPp := hP.1.1
  have hPodd := odd_card_of_isPGroup hp hp2 hPp
  set N := normalizer (P : Set X) with hN
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hrank : Open.pRank 2 (zHull Z N) ≤ 1 := by
    by_contra hge
    push Not at hge
    exact hPM (h.le_of_odd_normalizer hZ hPodd hge hz hzM hzN)
  have hiso : ∀ y ∈ Z, y ∈ N → y * z = z * y → y = z := fun y hy hyN hyz =>
    eq_of_commute_of_pRank_zHull_le_one hZ hrank hy hyN hz hzN hyz
  have hZstar : IsZStarIn (N ⊔ zpowers z) z := by
    rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hzN)]
    exact isZStarIn_of_isolated hZ hz hzN hiso
  obtain ⟨β, hβ, δ, hδ, hβδ, hno⟩ := h.lemma54 hZ hP.1.2 hz hzM hzN hPM hrank
  have hPβδ : P ≤ β ⊓ δ :=
    le_inf (h.mem_omegaFix_iff.mp hβ).2 (h.mem_omegaFix_iff.mp hδ).2
  obtain ⟨Q, hQ⟩ := (hPp.comap_subtype (K := β ⊓ δ)).exists_le_sylow
  set R : Subgroup X := (Q : Subgroup ↥(β ⊓ δ)).map (β ⊓ δ).subtype with hR
  have hRsyl : ABGLocalTools.IsSylowOf p R (β ⊓ δ) := ⟨Q, rfl⟩
  have hPR : P ≤ R := fun x hx =>
    ⟨⟨x, hPβδ hx⟩, hQ (show (⟨x, hPβδ hx⟩ : ↥(β ⊓ δ)) ∈ P.subgroupOf (β ⊓ δ) from hx), rfl⟩
  obtain ⟨hΩR, hPRlt⟩ := h.lemma55_maxFixingThree hZ hp hp2 hP hβ hδ hβδ hno hRsyl hPR
  have hRp := hRsyl.isPGroup
  have hmodΩ : (omega M).ncard ≡ 2 [MOD p] := by
    have := ncard_omega_modEq_ncard_omegaFix (M := M) hp hRp
    rwa [hΩR, Set.ncard_pair hβδ] at this
  obtain ⟨A, hAp, hPA, hAR, hAN⟩ :=
    CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hRp hPRlt
  obtain ⟨Q', hQ'⟩ := (hAp.comap_subtype (K := N)).exists_le_sylow
  set B : Subgroup X := (Q' : Subgroup ↥N).map N.subtype with hB
  have hBsyl : ABGLocalTools.IsSylowOf p B N := ⟨Q', rfl⟩
  have hAB : A ≤ B := fun x hx =>
    ⟨⟨x, hAN hx⟩, hQ' (show (⟨x, hAN hx⟩ : ↥N) ∈ A.subgroupOf N from hx), rfl⟩
  have hBp := hBsyl.isPGroup
  have hbot : z ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨Q₀, hQ₀, -, hzQ₀⟩ := exists_invariant_sylow hp hp2 (hZ.1 z hz)
    (Subgroup.le_normalizer hzN) hZstar bot_le IsPGroup.of_bot hbot
  obtain ⟨w, hwN, hwB⟩ := exists_conj_of_isSylowOf hQ₀ hBsyl
  set v := w⁻¹ * z * w with hv
  have hvZ : v ∈ Z := hZ.2 z hz w
  have hvN : v ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hwN) hzN) hwN
  have hv2 : v * v = 1 := hZ.mul_self_eq_one hvZ
  have hvB : v ∈ normalizer (B : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer, ← hwB, conjugate_conjugate]
    have e : w * v = z * w := by rw [hv]; group
    rw [e, ← conjugate_conjugate, conjugate_eq_iff_mem_normalizer.mpr hzQ₀]
  have hmodB : (omega M).ncard ≡ (omegaFix M (B : Set X)).ncard [MOD p] :=
    ncard_omega_modEq_ncard_omegaFix hp hBp
  have hB2 : 2 ≤ (omegaFix M (B : Set X)).ncard :=
    two_le_of_modEq_two hp hp2 (hmodΩ.symm.trans hmodB)
  obtain ⟨l₁, l₂, hl₁, hl₂, hl12⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mp (by omega : 1 < (omegaFix M (B : Set X)).ncard)
  have hex : ∃ l ∈ omegaFix M (B : Set X), conjugate l v ≠ l := by
    by_contra hall
    push Not at hall
    obtain ⟨γ, -, huniq⟩ := h.existsUnique_fixed_point hZ hvZ
    exact hl12 ((huniq l₁ ⟨hl₁.1, hall l₁ hl₁⟩).trans (huniq l₂ ⟨hl₂.1, hall l₂ hl₂⟩).symm)
  obtain ⟨l, hl, hlv⟩ := hex
  have hμ : conjugate l v ∈ omegaFix M (B : Set X) :=
    conjugate_mem_omegaFix_of_mem_normalizer hvB hl
  have hA3 : 3 ≤ (omegaFix M (A : Set X)).ncard := by
    by_contra hlt
    have hRA : omegaFix M (R : Set X) ⊆ omegaFix M (A : Set X) :=
      omegaFix_anti (fun x hx => hAR hx)
    have hBA : omegaFix M (B : Set X) ⊆ omegaFix M (A : Set X) :=
      omegaFix_anti (fun x hx => hAB hx)
    have hAcard : (omegaFix M (A : Set X)).ncard = 2 := by
      have h1 := Set.ncard_le_ncard hRA (Set.toFinite _)
      rw [hΩR, Set.ncard_pair hβδ] at h1
      omega
    have hAeq : omegaFix M (A : Set X) = {β, δ} := by
      rw [← hΩR]
      exact (Set.eq_of_subset_of_ncard_le hRA (by rw [hΩR, Set.ncard_pair hβδ]; omega)
        (Set.toFinite _)).symm
    have hBeq : omegaFix M (B : Set X) = {β, δ} := by
      rw [← hAeq]
      exact Set.eq_of_subset_of_ncard_le hBA (by omega) (Set.toFinite _)
    rw [hBeq] at hl hμ
    rcases hl with rfl | rfl <;> rcases hμ with hμ | hμ
    · exact hlv hμ
    · exact hno v hvZ hvN hμ
    · have : conjugate β v = l := by
        rw [← hμ, conjugate_conjugate, hv2, conjugate_one]
      exact hno v hvZ hvN this
    · exact hlv hμ
  exact absurd hPA (not_lt_of_ge (hP.2 ⟨hAp, hA3⟩ hPA.le))

theorem IsProductDisconnected.exists_mem_normalizer_of_isMaxFixingThree
    (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M)
    (hall : ∀ x : X, orderOf x = 2 → x ∈ Z) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup X} (hP : IsMaxFixingThree M p P) : ∃ s ∈ Z, s ∈ normalizer (P : Set X) := by
  obtain ⟨⟨n, hn, β, hβ, hβn⟩, hb⟩ := h.lemma51 hZ hp hp2 hP
  have hγ : conjugate β n ∈ omegaFix M (P : Set X) :=
    conjugate_mem_omegaFix_of_mem_normalizer hn hβ
  obtain ⟨s, hsN, hseven, -, -⟩ := hb β hβ _ hγ (fun heq => hβn heq.symm) ⟨n, hn, rfl⟩
  have h2 : 2 ∣ orderOf s := even_iff_two_dvd.mp hseven
  have ho : orderOf s ≠ 0 := (orderOf_pos s).ne'
  refine ⟨s ^ (orderOf s / 2), hall _ (orderOf_pow_orderOf_div ho h2), ?_⟩
  exact (normalizer (P : Set X)).pow_mem hsN _

theorem IsProductDisconnected.prop53a (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hall : ∀ x : X, orderOf x = 2 → x ∈ Z) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsMaxFixingThree M p P) :
    (∃ s ∈ Z, s ∈ normalizer (P : Set X)) ∧
      ∀ s ∈ Z, s ∈ normalizer (P : Set X) → ∀ β ∈ omega M, conjugate β s = β → P ≤ β := by
  refine ⟨h.exists_mem_normalizer_of_isMaxFixingThree hZ hall hp hp2 hP, ?_⟩
  intro s hs hsN β hβ hβs
  obtain ⟨g, hg⟩ := exists_conjugate_eq_base hβ
  have hmax' := hP.map_conjugate g
  have hsβ : s ∈ β := (h.conjugate_eq_iff_mem hβ).mp hβs
  have hzM : g⁻¹ * s * g ∈ M := by
    have : g⁻¹ * s * g ∈ conjugate β g := by
      rw [mem_conjugate_iff]
      have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
      rw [e]
      exact hsβ
    rwa [hg] at this
  have hzN : g⁻¹ * s * g ∈ normalizer (conjugate P g : Set X) := by
    rw [normalizer_conjugate, mem_conjugate_iff]
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rw [e]
    exact hsN
  have hle := h.prop53_key hZ hp hp2 hmax' (hZ.2 s hs g) hzM hzN
  intro x hx
  have hx' : g⁻¹ * x * g ∈ conjugate P g := by
    rw [mem_conjugate_iff]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  have hβeq : β = conjugate M g⁻¹ := by
    rw [← hg, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  rw [hβeq, mem_conjugate_iff]
  have e : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by rw [inv_inv]
  rw [e]
  exact hle hx'

omit [Finite X] in
theorem card_fixedPointsOfSubgroup_omega (U : Subgroup X) :
    Nat.card {ω : omega M // ω ∈ CFSG.BenderSuzuki.PFchapter1section1.fixedPointsOfSubgroup X (omega M) U} =
      (omegaFix M (U : Set X)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun ω => ⟨ω.1.1, ω.1.2, fun g hg => by
        have := congrArg (fun γ : omega M => (γ : Subgroup X)) (ω.2 g⁻¹ (U.inv_mem hg))
        simpa [omegaMulAction_smul_coe] using this⟩
      invFun := fun β => ⟨⟨β.1, β.2.1⟩, fun x hx => Subtype.ext (by
        show conjugate β.1 x⁻¹ = β.1
        exact β.2.2 _ (U.inv_mem hx))⟩
      left_inv := fun ω => rfl
      right_inv := fun β => rfl }

theorem normalizer_transitive_of_isMaxFixingThree
    (hD : DoublyTransitive M) {p : ℕ} (hp : p.Prime) {P : Subgroup X}
    (hP : IsMaxFixingThree M p P) :
    ∀ γ₁ ∈ omegaFix M (P : Set X), ∀ γ₂ ∈ omegaFix M (P : Set X),
      ∃ n ∈ normalizer (P : Set X), conjugate γ₁ n = γ₂ := by
  have : Finite (omega M) := Set.toFinite _
  have htwo : MulAction.IsMultiplyPretransitive X (omega M) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := hD a a.2 b b.2 (fun h => hab (Subtype.ext h)) c c.2 d d.2
      (fun h => hcd (Subtype.ext h))
    refine ⟨g⁻¹, Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [omegaMulAction_smul_coe, inv_inv]
      exact hg1
    · rw [omegaMulAction_smul_coe, inv_inv]
      exact hg2
  have hmax : Maximal (fun U : Subgroup X => IsPGroup p U ∧
      2 < Nat.card {ω : omega M // ω ∈ CFSG.BenderSuzuki.PFchapter1section1.fixedPointsOfSubgroup X (omega M) U}) P := by
    refine ⟨⟨hP.1.1, ?_⟩, fun Q hQ hle => hP.2 ⟨hQ.1, ?_⟩ hle⟩
    · rw [card_fixedPointsOfSubgroup_omega]
      exact hP.1.2
    · have := hQ.2
      rw [card_fixedPointsOfSubgroup_omega] at this
      exact this
  have h2 := CFSG.BenderSuzuki.chapter1_bender_normalizer_two_pretransitive hp htwo P hmax
  have hmem : ∀ γ (hγ : γ ∈ omegaFix M (P : Set X)),
      (⟨γ, hγ.1⟩ : omega M) ∈ CFSG.BenderSuzuki.PFchapter1section1.fixedPointsOfSubgroup X (omega M) P := by
    intro γ hγ x hx
    apply Subtype.ext
    show conjugate γ x⁻¹ = γ
    exact hγ.2 _ (P.inv_mem hx)
  have hex : ∀ γ ∈ omegaFix M (P : Set X), ∃ δ ∈ omegaFix M (P : Set X), δ ≠ γ := by
    intro γ hγ
    by_contra hall
    push Not at hall
    have hsub : omegaFix M (P : Set X) ⊆ {γ} := fun x hx => hall x hx
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp only [Set.ncard_singleton] at this
    have h3 := hP.1.2
    omega
  intro γ₁ hγ₁ γ₂ hγ₂
  by_cases h12 : γ₁ = γ₂
  · exact ⟨1, (normalizer (P : Set X)).one_mem, by rw [h12, conjugate_one]⟩
  · obtain ⟨δ₁, hδ₁, hδ₁γ⟩ := hex γ₁ hγ₁
    obtain ⟨δ₂, hδ₂, hδ₂γ⟩ := hex γ₂ hγ₂
    obtain ⟨f, hf1, -⟩ := h2 (hmem γ₁ hγ₁) (hmem δ₁ hδ₁) (hmem γ₂ hγ₂) (hmem δ₂ hδ₂)
      (fun h => hδ₁γ (congrArg Subtype.val h).symm)
      (fun h => hδ₂γ (congrArg Subtype.val h).symm)
    refine ⟨(f : X)⁻¹, (normalizer (P : Set X)).inv_mem f.2, ?_⟩
    have := congrArg (fun γ : omega M => (γ : Subgroup X)) hf1
    simpa [omegaMulAction_smul_coe] using this

theorem ZDSetup.prop53 (S : ZDSetup X Z M) :
    (∀ x : X, orderOf x = 2 → x ∈ Z) → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup X,
      IsMaxFixingThree M p P →
      ((∃ s ∈ Z, s ∈ normalizer (P : Set X)) ∧
        ∀ s ∈ Z, s ∈ normalizer (P : Set X) → ∀ β ∈ omega M, conjugate β s = β → P ≤ β) ∧
      (DoublyTransitive M → ∀ γ ∈ omegaFix M (P : Set X),
        ∃ s ∈ Z, s ∈ normalizer (P : Set X) ∧ conjugate γ s = γ) := by
  intro hall p hp hp2 P hP
  have hZ := S.invariant
  have h := S.prodDisc
  have ha := h.prop53a hZ hall hp hp2 hP
  refine ⟨ha, fun hD γ hγ => ?_⟩
  obtain ⟨s, hs, hsN⟩ := ha.1
  obtain ⟨γ₀, ⟨hγ₀Ω, hsγ₀⟩, -⟩ := h.existsUnique_fixed_point hZ hs
  have hγ₀ : γ₀ ∈ omegaFix M (P : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hγ₀Ω, ha.2 s hs hsN γ₀ hγ₀Ω hsγ₀⟩
  obtain ⟨n, hnN, hn⟩ := normalizer_transitive_of_isMaxFixingThree hD hp hP γ₀ hγ₀ γ hγ
  refine ⟨n⁻¹ * s * n, hZ.2 s hs n, ?_, ?_⟩
  · exact (normalizer (P : Set X)).mul_mem
      ((normalizer (P : Set X)).mul_mem ((normalizer (P : Set X)).inv_mem hnN) hsN) hnN
  · have e : conjugate γ (n⁻¹ * s * n) = conjugate (conjugate (conjugate γ n⁻¹) s) n := by
      rw [conjugate_conjugate, conjugate_conjugate, mul_assoc]
    have h1 : conjugate γ n⁻¹ = γ₀ := by
      rw [← hn, conjugate_conjugate, mul_inv_cancel, conjugate_one]
    rw [e, h1, hsγ₀, hn]

end CFSG.GH74.Uniqueness
