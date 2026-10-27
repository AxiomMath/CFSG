module

public import CFSG.GH74.Uniqueness.Section7Stage2
public import CFSG.GH74.Uniqueness.Section5ZStar

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Generic

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem card_le_card_of_isPGroup_le_isSylowOf {p : ℕ} (hp : p.Prime) {P K Q : Subgroup X}
    (hPK : P ≤ K) (hP : IsPGroup p P) (hQ : ABGLocalTools.IsSylowOf p Q K) :
    Nat.card P ≤ Nat.card Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR, hPR⟩ := stage2_exists_isSylowOf_ge hPK hP
  calc Nat.card P ≤ Nat.card R := Subgroup.card_le_of_le hPR
    _ = p ^ (Nat.card K).factorization p := hR.card_eq
    _ = Nat.card Q := hQ.card_eq.symm

omit [Finite X] in
theorem TransitiveOnS.card_inf_inf_conjugate_eq (hT : TransitiveOnS Z M)
    {γ δ γ' δ' : Subgroup X} {s s' : X} (h₁ : STriple Z M γ δ s) (h₂ : STriple Z M γ' δ' s') :
    Nat.card ↥(γ ⊓ δ ⊓ conjugate δ s) = Nat.card ↥(γ' ⊓ δ' ⊓ conjugate δ' s') := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := hT γ δ s γ' δ' s' h₁ h₂
  have e : g * (g⁻¹ * s * g) = s * g := by group
  have hc : conjugate (γ ⊓ δ ⊓ conjugate δ s) g =
      conjugate γ g ⊓ conjugate δ g ⊓ conjugate (conjugate δ g) (g⁻¹ * s * g) := by
    rw [conjugate_inf, conjugate_inf, conjugate_conjugate, conjugate_conjugate, e]
  subst hg₁ hg₂ hg₃
  rw [← hc]
  exact (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm

theorem TransitiveOnS.card_le_of_le_inf_inf_conjugate (hT : TransitiveOnS Z M) {p : ℕ}
    (hp : p.Prime) {γ δ β : Subgroup X} {s z : X} (h₁ : STriple Z M γ δ s)
    (h₂ : STriple Z M M β z) {P₁ P : Subgroup X}
    (hP₁ : ABGLocalTools.IsSylowOf p P₁ (M ⊓ β ⊓ conjugate β z)) (hP : IsPGroup p P)
    (hPle : P ≤ γ ⊓ δ ⊓ conjugate δ s) : Nat.card P ≤ Nat.card P₁ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR, hPR⟩ := stage2_exists_isSylowOf_ge hPle hP
  calc Nat.card P ≤ Nat.card R := Subgroup.card_le_of_le hPR
    _ = p ^ (Nat.card ↥(γ ⊓ δ ⊓ conjugate δ s)).factorization p := hR.card_eq
    _ = p ^ (Nat.card ↥(M ⊓ β ⊓ conjugate β z)).factorization p := by
        rw [hT.card_inf_inf_conjugate_eq h₁ h₂]
    _ = Nat.card P₁ := hP₁.card_eq.symm

theorem IsProductDisconnected.isSylowOf_of_omegaFix_eq_singleton (h : IsProductDisconnected Z M)
    {p : ℕ} (hp : p.Prime) {K P : Subgroup X} (hP : ABGLocalTools.IsSylowOf p P (K ⊓ M))
    (hΩ : omegaFix M (P : Set X) = {M}) : ABGLocalTools.IsSylowOf p P K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀, hPS₀⟩ := stage2_exists_isSylowOf_ge (hP.le.trans inf_le_left) hP.isPGroup
  have hmod₁ := ncard_omega_modEq_ncard_omegaFix (M := M) hp hS₀.isPGroup
  have hmod₂ := ncard_omega_modEq_ncard_omegaFix (M := M) hp hP.isPGroup
  rw [hΩ, Set.ncard_singleton] at hmod₂
  have hne : (omegaFix M (S₀ : Set X)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Set.ncard_empty] at hmod₁
    have hmod : 0 ≡ 1 [MOD p] := hmod₁.symm.trans hmod₂
    have h01 : 0 % p = 1 % p := hmod
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt] at h01
    exact absurd h01 (by norm_num)
  obtain ⟨δ, hδ⟩ := hne
  have hδP : δ ∈ omegaFix M (P : Set X) := omegaFix_anti (fun x hx => hPS₀ hx) hδ
  rw [hΩ, Set.mem_singleton_iff] at hδP
  have hS₀M : S₀ ≤ M := by
    have := (h.mem_omegaFix_iff.mp hδ).2
    rwa [hδP] at this
  have hS₀eq : S₀ = P := hP.eq_of_le hPS₀ (le_inf hS₀.le hS₀M) hS₀.isPGroup
  rw [← hS₀eq]
  exact hS₀

theorem exists_omegaFix_eq_singleton_of_isSylowOf {p : ℕ} (hp : p.Prime) {K P S' γ : Subgroup X}
    (hP : ABGLocalTools.IsSylowOf p P K) (hΩ : omegaFix M (P : Set X) = {γ})
    (hS' : ABGLocalTools.IsSylowOf p S' K) : ∃ γ' : Subgroup X, omegaFix M (S' : Set X) = {γ'} := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hn⟩ := exists_conj_of_isSylowOf hP hS'
  exact ⟨conjugate γ n, by rw [← hn, omegaFix_conjugate, hΩ, Set.image_singleton]⟩

end Generic

section Lemma710

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma710_false_of_zStar (S : ZDSetup X Z M) {z : X} {p : ℕ}
    {W β Q : Subgroup X} {t : X} {R P₁ : Subgroup X}
    (d : Stage2Data Z M z p W β Q t R P₁)
    (hall : ∀ y ∈ Z, y ∈ normalizer (Q : Set X) → IsZStarIn (normalizer (Q : Set X)) y) :
    False := by
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := d.tmax.cand
  have hp := hcand.prime
  have hp2 := hcand.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup X := normalizer (Q : Set X) with hN
  have hzZ : z ∈ Z := hcand.mem_Z
  have hzM : z ∈ M := hcand.mem_M
  have hzN : z ∈ N := d.adm.z_norm
  have hz2 : orderOf z = 2 := hZ.1 z hzZ
  have htZ : t ∈ Z := d.t_mem
  have htN : t ∈ N := d.t_norm_Q
  have ht2 : orderOf t = 2 := hZ.1 t htZ
  have hβΩ : β ∈ omega M := d.beta_mem.1
  have hMz : conjugate M z = M := (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM
  have hSMβ : STriple Z M M β z := ⟨self_mem_omega M, hβΩ, hzZ, hMz, d.beta_ne.symm⟩
  have hbound : ∀ (γ δ : Subgroup X) (s : X), STriple Z M γ δ s → ∀ P : Subgroup X,
      IsPGroup p P → P ≤ γ ⊓ δ ⊓ conjugate δ s → Nat.card P ≤ Nat.card P₁ :=
    fun γ δ s hs P hP hle =>
      d.transS.card_le_of_le_inf_inf_conjugate hp hs hSMβ d.P₁_syl hP hle
  have hRM : R ≤ M := (d.R_syl.le.trans inf_le_left).trans inf_le_left
  have hRβ : R ≤ β := (d.R_syl.le.trans inf_le_left).trans inf_le_right
  have hRN : R ≤ N := d.R_syl.le.trans inf_le_right
  have hzNM : z ∈ normalizer ((N ⊓ M : Subgroup X) : Set X) :=
    Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨hzN, hzM⟩)
  have hZstarz : IsZStarIn ((N ⊓ M) ⊔ zpowers z) z :=
    IsZStarIn.restrict (hZ.mul_self_eq_one hzZ) (hall z hzZ hzN) inf_le_left hzNM
  have hzbot : z ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨Pstar, hPstar, -, hzPstar⟩ :=
    exists_invariant_sylow hp hp2 hz2 hzNM hZstarz bot_le IsPGroup.of_bot hzbot
  have hPstarM : Pstar ≤ M := hPstar.le.trans inf_le_right
  have hPstar_gt : Nat.card P₁ < Nat.card Pstar :=
    lt_of_lt_of_le d.card_P₁_lt
      (card_le_card_of_isPGroup_le_isSylowOf hp (le_inf hRN hRM) d.R_syl.isPGroup hPstar)
  have hΩPstar : omegaFix M (Pstar : Set X) = {M} := by
    ext δ
    rw [Set.mem_singleton_iff]
    constructor
    · intro hδ
      by_contra hδM
      obtain ⟨hδΩ, hPδ⟩ := h.mem_omegaFix_iff.mp hδ
      have hPle : Pstar ≤ M ⊓ δ ⊓ conjugate δ z := prop38a (le_inf hPstarM hPδ) hzPstar
      have hTr : STriple Z M M δ z := ⟨self_mem_omega M, hδΩ, hzZ, hMz, Ne.symm hδM⟩
      exact absurd (hbound M δ z hTr Pstar hPstar.isPGroup hPle) (not_le.mpr hPstar_gt)
    · intro hδ
      rw [hδ]
      exact h.self_mem_omegaFix_iff.mpr hPstarM
  have hPstarN_syl : ABGLocalTools.IsSylowOf p Pstar N :=
    h.isSylowOf_of_omegaFix_eq_singleton hp hPstar hΩPstar
  have hΩsyl : ∀ S' : Subgroup X, ABGLocalTools.IsSylowOf p S' N →
      ∃ γ : Subgroup X, omegaFix M (S' : Set X) = {γ} := fun S' hS' =>
    exists_omegaFix_eq_singleton_of_isSylowOf hp hPstarN_syl hΩPstar hS'
  have htNN : t ∈ normalizer (N : Set X) := Subgroup.le_normalizer htN
  have hZstart : IsZStarIn (N ⊔ zpowers t) t := by
    rw [sup_eq_left.mpr ((Subgroup.zpowers_le).mpr htN)]
    exact hall t htZ htN
  obtain ⟨Rstar, hRstar, hRRstar, htRstar⟩ :=
    exists_invariant_sylow hp hp2 ht2 htNN hZstart hRN d.R_syl.isPGroup d.t_norm_R
  obtain ⟨γ, hγ⟩ := hΩsyl Rstar hRstar
  have hγmem : γ ∈ omegaFix M (Rstar : Set X) := by
    rw [hγ]
    exact Set.mem_singleton γ
  have hγt : conjugate γ t = γ := by
    have := conjugate_mem_omegaFix_of_mem_normalizer htRstar hγmem
    rwa [hγ, Set.mem_singleton_iff] at this
  obtain ⟨hγΩ, hRstarγ⟩ := h.mem_omegaFix_iff.mp hγmem
  have hγM : γ ≠ M := by
    intro hγM'
    rw [hγM'] at hγt
    exact d.beta_ne (d.t_swap.symm.trans hγt)
  have hTr' : STriple Z M γ M t := ⟨hγΩ, self_mem_omega M, htZ, hγt, hγM⟩
  have hRle : R ≤ γ ⊓ M ⊓ conjugate M t :=
    le_inf (le_inf (hRRstar.trans hRstarγ) hRM) (by rw [d.t_swap]; exact hRβ)
  exact absurd (hbound γ M t hTr' R d.R_syl.isPGroup hRle) (not_le.mpr d.card_P₁_lt)

theorem ZDSetup.lemma710 (S : ZDSetup X Z M) : Lemma710Stmt Z M := by
  intro z p W β Q t R P₁ d
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := d.tmax.cand
  have hzZ : z ∈ Z := hcand.mem_Z
  have hzM : z ∈ M := hcand.mem_M
  have hzN : z ∈ normalizer (Q : Set X) := d.adm.z_norm
  have htZ : t ∈ Z := d.t_mem
  have htN : t ∈ normalizer (Q : Set X) := d.t_norm_Q
  have hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer (Q : Set X))) := by
    by_contra hlt
    exact S.lemma710_false_of_zStar d fun y hy hyN =>
      isZStarIn_of_pRank_zHull_le_one hZ (by omega) hy hyN
  refine ⟨hrank, ?_⟩
  set L : Subgroup X := zHull Z (normalizer (Q : Set X)) with hL
  set O₁ : Subgroup X := pPrimeCoreIn L with hO₁
  have hLnorm : L ≤ normalizer (O₁ : Set X) := pPrimeCoreIn_normalizes L
  have hzL : z ∈ L := Subgroup.subset_closure ⟨hzZ, hzN⟩
  have htL : t ∈ L := Subgroup.subset_closure ⟨htZ, htN⟩
  have hrank' : 2 ≤ Open.pRank 2 (zHull Z (normalizer (O₁ : Set X))) :=
    hrank.trans (CFSG.SectionRank.pRank_mono Nat.one_lt_two
      ((Subgroup.closure_le _).mpr fun y hy =>
        Subgroup.subset_closure ⟨hy.1, hLnorm (Subgroup.subset_closure hy)⟩))
  have hMz : conjugate M z = M := (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM
  have hO₁M : O₁ ≤ M :=
    S.lemma313 (odd_card_pPrimeCoreIn L) hrank' hzZ (hLnorm hzL) (self_mem_omega M) hMz
  have hO₁β : O₁ ≤ β := by
    intro x hx
    rw [← d.t_swap, mem_conjugate_iff]
    exact hO₁M ((Subgroup.mem_normalizer_iff.mp (hLnorm htL) x).mp hx)
  exact prop38a (le_inf hO₁M hO₁β) (hLnorm hzL)

end Lemma710

end CFSG.GH74.Uniqueness
