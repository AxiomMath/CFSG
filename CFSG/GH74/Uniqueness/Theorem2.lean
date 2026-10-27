module

public import CFSG.GH74.Uniqueness.Section5Cor57
public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem card_conjugate (A : Subgroup X) (g : X) : Nat.card ↥(conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

omit [Finite X] in
theorem card_eq_of_mem_omega {β : Subgroup X} (hβ : β ∈ omega M) : Nat.card β = Nat.card M := by
  obtain ⟨g, rfl⟩ := hβ
  exact card_conjugate M g

omit [Finite X] in
theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K P : Subgroup X} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ R : Subgroup X, ABGLocalTools.IsSylowOf p R K ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup ↥K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (show (⟨x, hPK hx⟩ : ↥K) ∈ P.subgroupOf K from hx), rfl⟩

theorem ZDSetup.theorem2b (S : ZDSetup X Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hno : ¬ ∃ P : Subgroup X, IsPGroup p P ∧ (omegaFix M (P : Set X)).ncard = 2) :
    ∀ β ∈ omega M, ∀ P : Subgroup X, IsPGroup p P → P ≤ β →
      3 ≤ (omegaFix M (P : Set X)).ncard →
      (∀ Q : Subgroup X, IsPGroup p Q → Q ≤ β → 3 ≤ (omegaFix M (Q : Set X)).ncard →
        P ≤ Q → Q = P) →
      (∀ γ ∈ omegaFix M (P : Set X), ∀ δ ∈ omegaFix M (P : Set X),
        ∃ n ∈ normalizer (P : Set X), conjugate γ n = δ) ∧
      ∀ γ ∈ omegaFix M (P : Set X), ∃ s ∈ Z, s ∈ normalizer (P : Set X) ∧ conjugate γ s = γ := by
  intro β hβ P hPp hPβ hP3 hPmax
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact p.Prime := ⟨hp⟩
  have hβP : β ∈ omegaFix M (P : Set X) := h.mem_omegaFix_iff.mpr ⟨hβ, hPβ⟩
  have h23 : ∀ R : Subgroup X, IsPGroup p R → 2 ≤ (omegaFix M (R : Set X)).ncard →
      3 ≤ (omegaFix M (R : Set X)).ncard := by
    intro R hR h2
    by_contra hlt
    exact hno ⟨R, hR, by omega⟩
  have hSyl : ∀ γ ∈ omegaFix M (P : Set X), γ ≠ β → ABGLocalTools.IsSylowOf p P (β ⊓ γ) := by
    intro γ hγ hγβ
    have hPle : P ≤ β ⊓ γ := le_inf hPβ (h.mem_omegaFix_iff.mp hγ).2
    obtain ⟨R₀, hR₀syl, hPR₀⟩ := exists_isSylowOf_ge (p := p) hPle hPp
    have hβR : β ∈ omegaFix M (R₀ : Set X) :=
      h.mem_omegaFix_iff.mpr ⟨hβ, hR₀syl.le.trans inf_le_left⟩
    have hγR : γ ∈ omegaFix M (R₀ : Set X) :=
      h.mem_omegaFix_iff.mpr ⟨hγ.1, hR₀syl.le.trans inf_le_right⟩
    have h2 : 2 ≤ (omegaFix M (R₀ : Set X)).ncard := by
      have := Set.ncard_le_ncard (show ({β, γ} : Set (Subgroup X)) ⊆ omegaFix M (R₀ : Set X) from by
        rintro x (rfl | rfl)
        · exact hβR
        · exact hγR) (Set.toFinite _)
      rwa [Set.ncard_pair (Ne.symm hγβ)] at this
    have hR₀P : R₀ = P :=
      hPmax R₀ hR₀syl.isPGroup (hR₀syl.le.trans inf_le_left) (h23 R₀ hR₀syl.isPGroup h2) hPR₀
    exact hR₀P ▸ hR₀syl
  have htrans0 : ∀ γ ∈ omegaFix M (P : Set X), ∃ s ∈ normalizer (P : Set X), conjugate β s = γ := by
    intro γ hγ
    by_cases hγβ : γ = β
    · exact ⟨1, one_mem _, by rw [hγβ, conjugate_one]⟩
    · obtain ⟨s, -, hsN, hs1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 hβ hγ.1 (Ne.symm hγβ)
        (hSyl γ hγ hγβ)
      exact ⟨s, hsN, hs1⟩
  have htrans : ∀ γ ∈ omegaFix M (P : Set X), ∀ δ ∈ omegaFix M (P : Set X),
      ∃ n ∈ normalizer (P : Set X), conjugate γ n = δ := by
    intro γ hγ δ hδ
    obtain ⟨s₁, hs₁N, hs₁⟩ := htrans0 γ hγ
    obtain ⟨s₂, hs₂N, hs₂⟩ := htrans0 δ hδ
    refine ⟨s₁⁻¹ * s₂, (normalizer (P : Set X)).mul_mem ((normalizer (P : Set X)).inv_mem hs₁N) hs₂N, ?_⟩
    rw [← hs₁, conjugate_conjugate, mul_inv_cancel_left, hs₂]
  refine ⟨htrans, ?_⟩
  obtain ⟨γ₁, hγ₁, hγ₁β⟩ : ∃ γ ∈ omegaFix M (P : Set X), γ ≠ β := by
    by_contra hall
    push Not at hall
    have hsub : omegaFix M (P : Set X) ⊆ {β} := fun x hx => hall x hx
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp only [Set.ncard_singleton] at this
    omega
  obtain ⟨s₀, hs₀, hs₀N, hs₀1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 hβ hγ₁.1
    (Ne.symm hγ₁β) (hSyl γ₁ hγ₁ hγ₁β)
  have hs₀cnt : zCosetNum Z P s₀ = zNumShare Z M p :=
    h.lemma39_card hZ hβ (Ne.symm hγ₁β) hp hp2 hs₀ hs₀1 (hSyl γ₁ hγ₁ hγ₁β) hs₀N
  have hcond : Prop52Cond Z M p P := ⟨hPp, hP3, s₀, hs₀, hs₀N, hs₀cnt⟩
  have hmax52 : Maximal (Prop52Cond Z M p) P := by
    refine ⟨hcond, fun R hR hPR => ?_⟩
    have hR3 := hR.three_le
    obtain ⟨δ, hδ⟩ : (omegaFix M (R : Set X)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    have hδP : δ ∈ omegaFix M (P : Set X) := omegaFix_anti (fun x hx => hPR hx) hδ
    obtain ⟨n, hnN, hn⟩ := htrans δ hδP β hβP
    have hR'β : conjugate R n ≤ β := by
      have hRδ : R ≤ δ := (h.mem_omegaFix_iff.mp hδ).2
      have := conjugate_mono hRδ n
      rwa [hn] at this
    have hPR' : P ≤ conjugate R n := by
      have := conjugate_mono hPR n
      rwa [conjugate_eq_iff_mem_normalizer.mpr hnN] at this
    have hR'3 : 3 ≤ (omegaFix M ((conjugate R n : Subgroup X) : Set X)).ncard := by
      rw [ncard_omegaFix_conjugate]
      exact hR3
    have hR'P : conjugate R n = P :=
      hPmax _ (isPGroup_conjugate hR.pgroup n) hR'β hR'3 hPR'
    have : R = P := by
      have h1 : conjugate (conjugate R n) n⁻¹ = R := conjugate_conjugate_inv R n
      rw [← h1, hR'P]
      exact conjugate_eq_iff_mem_normalizer.mpr ((normalizer (P : Set X)).inv_mem hnN)
    exact this.le
  have h52 := S.prop52 p hp hp2 P hmax52
  intro γ hγ
  obtain ⟨u, hu, huN, -⟩ := hcond.exists_u
  obtain ⟨δ₀, ⟨hδ₀Ω, hδ₀u⟩, -⟩ := h.existsUnique_fixed_point hZ hu
  have hδ₀P : δ₀ ∈ omegaFix M (P : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hδ₀Ω, h52.1.2 u hu huN δ₀ hδ₀Ω hδ₀u⟩
  obtain ⟨n, hnN, hn⟩ := htrans δ₀ hδ₀P γ hγ
  refine ⟨n⁻¹ * u * n, hZ.2 u hu n, ?_, ?_⟩
  · exact (normalizer (P : Set X)).mul_mem
      ((normalizer (P : Set X)).mul_mem ((normalizer (P : Set X)).inv_mem hnN) huN) hnN
  · rw [← hn, conjugate_conjugate]
    have e : n * (n⁻¹ * u * n) = u * n := by group
    rw [e, ← conjugate_conjugate, hδ₀u]

theorem ZDSetup.theorem2a (S : ZDSetup X Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hex : ∃ P : Subgroup X, IsPGroup p P ∧ (omegaFix M (P : Set X)).ncard = 2) :
    DoublyTransitive M := by
  by_contra hnot
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀, hP₀p, hP₀2⟩ := hex
  obtain ⟨β₀, γ₀, hβγ, hΩ₀⟩ := Set.ncard_eq_two.mp hP₀2
  have hβ₀ : β₀ ∈ omegaFix M (P₀ : Set X) := by rw [hΩ₀]; exact Or.inl rfl
  have hγ₀ : γ₀ ∈ omegaFix M (P₀ : Set X) := by rw [hΩ₀]; exact Or.inr rfl
  have hP₀β : P₀ ≤ β₀ := (h.mem_omegaFix_iff.mp hβ₀).2
  let F : Subgroup X → Prop := fun Q =>
    IsPGroup p Q ∧ Q ≤ β₀ ∧ 2 ≤ (omegaFix M (Q : Set X)).ncard
  have hF₀ : F P₀ := ⟨hP₀p, hP₀β, by omega⟩
  obtain ⟨P, hP₀P, hPmax⟩ := Finite.exists_le_maximal hF₀
  have hPF := hPmax.1
  have hΩP : omegaFix M (P : Set X) = {β₀, γ₀} := by
    have hsub : omegaFix M (P : Set X) ⊆ {β₀, γ₀} := by
      have := omegaFix_anti (M := M) (show (P₀ : Set X) ⊆ (P : Set X) from fun x hx => hP₀P hx)
      rw [hΩ₀] at this
      exact this
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hβγ]; exact hPF.2.2)
      (Set.toFinite _)
  have hγP : γ₀ ∈ omegaFix M (P : Set X) := by rw [hΩP]; exact Or.inr rfl
  have hPle : P ≤ β₀ ⊓ γ₀ := le_inf hPF.2.1 (h.mem_omegaFix_iff.mp hγP).2
  obtain ⟨R₀, hR₀syl, hPR₀⟩ := exists_isSylowOf_ge (p := p) hPle hPF.1
  have hR₀F : F R₀ := by
    refine ⟨hR₀syl.isPGroup, hR₀syl.le.trans inf_le_left, ?_⟩
    have hsub : ({β₀, γ₀} : Set (Subgroup X)) ⊆ omegaFix M (R₀ : Set X) := by
      rintro x (rfl | rfl)
      · exact h.mem_omegaFix_iff.mpr ⟨hβ₀.1, hR₀syl.le.trans inf_le_left⟩
      · exact h.mem_omegaFix_iff.mpr ⟨hγ₀.1, hR₀syl.le.trans inf_le_right⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair hβγ] at this
  have hR₀P : R₀ ≤ P := hPmax.2 hR₀F hPR₀
  have hPsyl : ABGLocalTools.IsSylowOf p P (β₀ ⊓ γ₀) := by
    have : R₀ = P := le_antisymm hR₀P hPR₀
    rwa [← this]
  have hPtop : ABGLocalTools.IsSylowOf p P ⊤ := h.isSylowOf_omegaFix_pair' hp hp2 hβγ hPsyl hΩP
  obtain ⟨s, hs, Q, hQp, -, hsQ, hQcnt, hQfix⟩ := (S.cor57 hnot p hp hp2).1
  obtain ⟨lam, ⟨hlamΩ, hslam⟩, hlamuniq⟩ := h.existsUnique_fixed_point hZ hs
  have hQlam : Q ≤ lam := hQfix lam hlamΩ hslam
  obtain ⟨R, hRsyl, hQR⟩ := exists_isSylowOf_ge (p := p) hQlam hQp
  have hPβ₀ : ABGLocalTools.IsSylowOf p P β₀ := hPtop.of_le hPF.2.1 le_top
  have hRtop : ABGLocalTools.IsSylowOf p R ⊤ := by
    refine ABGLocalTools.isSylowOf_of_card le_top ?_
    calc Nat.card R = p ^ (Nat.card lam).factorization p := hRsyl.card_eq
      _ = p ^ (Nat.card β₀).factorization p := by
        rw [card_eq_of_mem_omega hlamΩ, card_eq_of_mem_omega hβ₀.1]
      _ = Nat.card P := hPβ₀.card_eq.symm
      _ = p ^ (Nat.card (⊤ : Subgroup X)).factorization p := hPtop.card_eq
  obtain ⟨w, -, hw⟩ := exists_conj_of_isSylowOf hPtop hRtop
  have hRcard : (omegaFix M (R : Set X)).ncard = 2 := by
    rw [← hw, ncard_omegaFix_conjugate, hΩP, Set.ncard_pair hβγ]
  have hlamR : lam ∈ omegaFix M (R : Set X) := h.mem_omegaFix_iff.mpr ⟨hlamΩ, hRsyl.le⟩
  obtain ⟨x, y, hxy, hxyR⟩ := Set.ncard_eq_two.mp hRcard
  obtain ⟨δ, hδlam, hΩRδ⟩ : ∃ δ, δ ≠ lam ∧ omegaFix M (R : Set X) = {lam, δ} := by
    have hmem : lam ∈ ({x, y} : Set (Subgroup X)) := by rw [← hxyR]; exact hlamR
    rcases hmem with h1 | h1
    · exact ⟨y, by rw [h1]; exact fun h' => hxy h'.symm, by rw [hxyR, h1]⟩
    · exact ⟨x, by rw [h1]; exact hxy, by rw [hxyR, h1, Set.pair_comm]⟩
  have hδR : δ ∈ omegaFix M (R : Set X) := by rw [hΩRδ]; exact Or.inr rfl
  have hRδ : R ≤ δ := (h.mem_omegaFix_iff.mp hδR).2
  have hδΩ : δ ∈ omega M := hδR.1
  have hQle : Q ≤ lam ⊓ δ := le_inf hQlam (hQR.trans hRδ)
  have hQE : Q ≤ lam ⊓ δ ⊓ conjugate δ s := prop38a hQle hsQ
  have hsδ : conjugate δ s ≠ δ := fun hfix => hδlam (hlamuniq δ ⟨hδΩ, hfix⟩)
  have hs2 : s * s = 1 := hZ.mul_self_eq_one hs
  have hslamN : s ∈ normalizer (lam : Set X) :=
    Subgroup.le_normalizer ((h.conjugate_eq_iff_mem hlamΩ).mp hslam)
  have hsE : s ∈ normalizer ((lam ⊓ δ ⊓ conjugate δ s : Subgroup X) : Set X) := by
    rw [inf_assoc]
    exact mem_normalizer_inf hslamN (mem_normalizer_inf_conjugate (M := δ) hs2)
  have hEF : lam ⊓ δ ⊓ conjugate δ s ≤ δ ⊓ conjugate δ s := fun x hx =>
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2, (Subgroup.mem_inf.mp hx).2⟩
  obtain ⟨V, hVsyl, hQV, hsV⟩ :=
    h.prop37a_omega hZ hs hδΩ hsδ hp hp2 hEF hsE hQE hQp hsQ
  have hVodd := odd_card_of_isPGroup hp hp2 hVsyl.isPGroup
  have hVD : V ≤ lam ⊓ δ := hVsyl.le.trans inf_le_left
  have hIV := h.prop38b_omega hZ hs hlamΩ hslam hδΩ hδlam hp hp2 hVD hVsyl.isPGroup hsV
  have hcntV : zCosetNum Z V s = zNumShare Z M p := by
    have h2 := zCosetNum_mono (Z := Z) hQV s
    have h3 : zCosetNum Z V s ≤ zNumShare Z M p := by
      rw [zCosetNum_eq_card_invertedSet hZ hs hVodd hsV]
      exact hIV.1
    omega
  have hIVeq : Nat.card (CFSG.OddInversion.invertedSet V s) = zNumShare Z M p := by
    rw [← zCosetNum_eq_card_invertedSet hZ hs hVodd hsV]
    exact hcntV
  obtain ⟨Q', hQ'syl, hQ'E, -⟩ := h.prop38c_omega hZ hs hlamΩ hslam hδΩ hδlam hp hp2 hVD
    hVsyl.isPGroup hsV hIVeq
  have hQ'E' : ABGLocalTools.IsSylowOf p Q' (lam ⊓ δ ⊓ conjugate δ s) :=
    hQ'syl.of_le hQ'E inf_le_left
  have hVsylD : ABGLocalTools.IsSylowOf p V (lam ⊓ δ) :=
    ABGLocalTools.isSylowOf_of_card hVD (by
      rw [hVsyl.card_eq, ← hQ'E'.card_eq, hQ'syl.card_eq])
  have hRD : ABGLocalTools.IsSylowOf p R (lam ⊓ δ) :=
    hRtop.of_le (le_inf hRsyl.le hRδ) le_top
  obtain ⟨u', hu', hu'V⟩ := exists_conj_of_isSylowOf hRD hVsylD
  have hΩV : omegaFix M (V : Set X) = {lam, δ} := by
    have := omegaFix_conjugate (M := M) R u'
    rw [hu'V, hΩRδ] at this
    rw [this, Set.image_pair]
    have h1 : conjugate lam u' = lam := (h.conjugate_eq_iff_mem hlamΩ).mpr (Subgroup.mem_inf.mp hu').1
    have h2 : conjugate δ u' = δ := (h.conjugate_eq_iff_mem hδΩ).mpr (Subgroup.mem_inf.mp hu').2
    rw [h1, h2]
  have hδV : δ ∈ omegaFix M (V : Set X) := by rw [hΩV]; exact Or.inr rfl
  have hδsV := conjugate_mem_omegaFix_of_mem_normalizer hsV hδV
  rw [hΩV] at hδsV
  rcases hδsV with h1 | h1
  · apply hδlam
    have h2 : conjugate (conjugate δ s) s = δ := by rw [conjugate_conjugate, hs2, conjugate_one]
    rw [h1, hslam] at h2
    exact h2.symm
  · exact hsδ h1

theorem ZDSetup.theorem2 (S : ZDSetup X Z M) : Theorem2Stmt Z M := fun _ hp hp2 =>
  ⟨fun hex => S.theorem2a hp hp2 hex, fun hno => S.theorem2b hp hp2 hno⟩

end CFSG.GH74.Uniqueness
