module

public import CFSG.GH74.Uniqueness.Section6Lemma61
public import CFSG.GH74.Uniqueness.Section6Lemma62
public import CFSG.GH74.Uniqueness.Section5Lemma51
public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Lemma73

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
private theorem conjugate_le_conjugate_of_le' {A B : Subgroup X} (h : A ≤ B) (g : X) :
    conjugate A g ≤ conjugate B g := by
  intro x hx
  rw [mem_conjugate_iff] at hx ⊢
  exact h hx

omit [Finite X] in
private theorem card_conjugate_eq' {A : Subgroup X} (g : X) :
    Nat.card (conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

omit [Finite X] in
private theorem exists_isSylowOf_ge' {p : ℕ} [Fact p.Prime] {P K : Subgroup X} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ R : Subgroup X, ABGLocalTools.IsSylowOf p R K ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (show (⟨x, hPK hx⟩ : K) ∈ P.subgroupOf K from hx), rfl⟩

theorem IsProductDisconnected.exists_invariant_sylow_inf_conjugate
    (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z)
    (hzM : z ∈ M) {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Q : Subgroup X} (hQp : IsPGroup p Q) (hQE : Q ≤ M ⊓ β ⊓ conjugate β z)
    (hzQ : z ∈ normalizer (Q : Set X)) :
    ∃ P : Subgroup X, ABGLocalTools.IsSylowOf p P (M ⊓ β ⊓ conjugate β z) ∧ Q ≤ P ∧
      z ∈ normalizer (P : Set X) := by
  have hβz := h.conjugate_ne_of_ne_self hZ hz hzM hβ hβM
  have hEF : M ⊓ β ⊓ conjugate β z ≤ β ⊓ conjugate β z := fun x hx =>
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2, (Subgroup.mem_inf.mp hx).2⟩
  have hF : z ∈ normalizer ((β ⊓ conjugate β z : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate (M := β) (hZ.mul_self_eq_one hz)
  have hzE : z ∈ normalizer ((M ⊓ β ⊓ conjugate β z : Subgroup X) : Set X) := by
    rw [inf_assoc]
    exact mem_normalizer_inf (Subgroup.le_normalizer hzM) hF
  exact h.prop37a_omega hZ hz hβ hβz hp hp2 hEF hzE hQE hQp hzQ

theorem exists_swap_of_isSylowOf_inf_conjugate (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} {β : Subgroup X} (hβ : β ∈ omega M) {p : ℕ}
    (hp : p.Prime) {P₀ P : Subgroup X}
    (hP₀ : ABGLocalTools.IsSylowOf p P₀ (M ⊓ β ⊓ conjugate β z))
    (hP : ABGLocalTools.IsSylowOf p P (M ⊓ β ⊓ conjugate β z))
    (h₀ : ∃ t ∈ Z, t ∈ normalizer (P₀ : Set X) ∧ conjugate M t = β) :
    ∃ t ∈ Z, t ∈ normalizer (P : Set X) ∧ conjugate M t = β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t₀, ht₀, ht₀P, ht₀β⟩ := h₀
  obtain ⟨w, hw, hwP⟩ := exists_conj_of_isSylowOf hP₀ hP
  have hwM : w ∈ M := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).1).1
  have hwβ : w ∈ β := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).1).2
  refine ⟨w⁻¹ * t₀ * w, hZ.2 t₀ ht₀ w, ?_, ?_⟩
  · rw [← conjugate_eq_iff_mem_normalizer, ← hwP, conjugate_conjugate,
      show w * (w⁻¹ * t₀ * w) = t₀ * w by group, ← conjugate_conjugate,
      conjugate_eq_iff_mem_normalizer.mpr ht₀P]
  · rw [conjugate_mul_mul, (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr (M.inv_mem hwM), ht₀β,
      (h.conjugate_eq_iff_mem hβ).mpr hwβ]

theorem IsProductDisconnected.exists_swap_of_normalized_sylow (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQ : ABGLocalTools.IsSylowOf p Q (M ⊓ β)) (hzQ : z ∈ normalizer (Q : Set X)) :
    ∃ P : Subgroup X, ABGLocalTools.IsSylowOf p P (M ⊓ β ⊓ conjugate β z) ∧
      ∃ t ∈ Z, t ∈ normalizer (P : Set X) ∧ conjugate M t = β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, htQ, htβ, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 (self_mem_omega M) hβ
    hβM.symm hQ
  exact ⟨Q, hQ.of_le (prop38a hQ.le hzQ) inf_le_left, t, ht, htQ, htβ⟩

theorem ZDSetup.exists_sylow_swap_of_not_normalized
    (S : ZDSetup X Z M) (hD : DoublyTransitive M)
    {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hno : ¬ ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (M ⊓ β) ∧ z ∈ normalizer (Q : Set X)) :
    ∃ P : Subgroup X, ABGLocalTools.IsSylowOf p P (M ⊓ β ⊓ conjugate β z) ∧
      z ∈ normalizer (P : Set X) ∧ ∃ t ∈ Z, t ∈ normalizer (P : Set X) ∧ conjugate M t = β := by
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact p.Prime := ⟨hp⟩
  have hEM : M ⊓ β ⊓ conjugate β z ≤ M := inf_le_left.trans inf_le_left
  have hEβ : M ⊓ β ⊓ conjugate β z ≤ β := inf_le_left.trans inf_le_right
  have hEF : M ⊓ β ⊓ conjugate β z ≤ β ⊓ conjugate β z := le_inf hEβ inf_le_right
  have hEMβ : M ⊓ β ⊓ conjugate β z ≤ M ⊓ β := inf_le_left
  have hβz := h.conjugate_ne_of_ne_self hZ hz hzM hβ hβM
  have hzbot : z ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨P, hP, -, hzP⟩ := h.exists_invariant_sylow_inf_conjugate hZ hz hzM hβ hβM hp hp2
    (Q := ⊥) IsPGroup.of_bot bot_le hzbot
  have hPF : ¬ ABGLocalTools.IsSylowOf p P (β ⊓ conjugate β z) := by
    intro hPF
    have hcard := h.prop37d_omega hZ hz hβ hβz hp hp2 hPF hzP
    have h31 := (h.prop38c hZ hz hzM hβ hβM hp hp2).out 3 1
    exact hno (h31.mp ⟨P, hP.le.trans hEMβ, hP.isPGroup, hzP, hcard⟩)
  have hNM : ¬ normalizer (P : Set X) ≤ M := by
    intro hNM
    obtain ⟨P', hP', hPP'⟩ := exists_isSylowOf_ge' (hP.le.trans hEF) hP.isPGroup
    have hlt : P < P' := lt_of_le_of_ne hPP' (fun heq => hPF (heq ▸ hP'))
    obtain ⟨R₁, hR₁p, hPR₁, hR₁P', hR₁N⟩ :=
      CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hP'.isPGroup hlt
    have hR₁F : R₁ ≤ β ⊓ conjugate β z := hR₁P'.trans hP'.le
    have hR₁E : R₁ ≤ M ⊓ β ⊓ conjugate β z :=
      le_inf (le_inf (hR₁N.trans hNM) (hR₁F.trans inf_le_left)) (hR₁F.trans inf_le_right)
    exact absurd (hP.eq_of_le hPR₁.le hR₁E hR₁p) (ne_of_gt hPR₁)
  have hex : ∃ s ∈ Z, s ∈ normalizer (P : Set X) ∧ s ∉ M := by
    by_cases hH : normalizer (P : Set X) = ⊤
    · obtain ⟨s, hs, hsM⟩ := S.exists_mem_not_mem
      exact ⟨s, hs, by rw [hH]; exact Subgroup.mem_top s, hsM⟩
    · have hne : (Z ∩ ((normalizer (P : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
        ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzP, hzM⟩⟩
      have hSE := S.theorem1_unconditional.2.1.2.2.2.2 (normalizer (P : Set X)) hH hne hNM
      have hnot : ¬ zHull Z (normalizer (P : Set X)) ≤ M := by
        intro hle
        apply hSE.1
        rw [Subgroup.subgroupOf_eq_top]
        exact le_inf hle le_rfl
      by_contra hall
      apply hnot
      rw [zHull, Subgroup.closure_le]
      rintro s ⟨hsZ, hsH⟩
      by_contra hsM
      exact hall ⟨s, hsZ, hsH, hsM⟩
  obtain ⟨s, hsZ, hsP, hsM⟩ := hex
  obtain ⟨u, huZ, hucl, hu1⟩ := h.exists_conj_mem_closure hZ hsZ hsM hz (Or.inl hzM)
  have huP : u ∈ normalizer (P : Set X) := by
    have : Subgroup.closure ({z, s} : Set X) ≤ normalizer (P : Set X) := by
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | rfl
      · exact hzP
      · exact hsP
    exact this hucl
  have hu2 : u * u = 1 := hZ.mul_self_eq_one huZ
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hus : u * s = z * u := by
    rw [hui] at hu1
    calc u * s = (u * s * u) * u := by rw [mul_assoc (u * s) u u, hu2, mul_one]
      _ = z * u := by rw [hu1]
  have hMz : conjugate M z = M := (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM
  have hγs : conjugate (conjugate M u) s = conjugate M u := by
    rw [conjugate_conjugate, hus, ← conjugate_conjugate, hMz]
  have hγM : conjugate M u ≠ M := by
    intro heq
    apply hsM
    have := hγs
    rw [heq] at this
    exact (h.conjugate_eq_iff_mem (self_mem_omega M)).mp this
  have hST₁ : STriple Z M (conjugate M u) M s :=
    ⟨conjugate_mem_omega (self_mem_omega M) u, self_mem_omega M, hsZ, hγs, hγM⟩
  have hST₂ : STriple Z M M β z := ⟨self_mem_omega M, hβ, hz, hMz, hβM.symm⟩
  obtain ⟨g, hg1, hg2, hg3⟩ :=
    h.transitiveOnS_of_doublyTransitive hZ hD _ _ _ _ _ _ hST₁ hST₂
  have hsg : s * g = g * z := by rw [← hg3]; group
  have hPM : P ≤ M := hP.le.trans hEM
  have hPγ : P ≤ conjugate M u := by
    have := conjugate_le_conjugate_of_le' hPM u
    rwa [conjugate_eq_iff_mem_normalizer.mpr huP] at this
  have hPMs : P ≤ conjugate M s := by
    have := conjugate_le_conjugate_of_le' hPM s
    rwa [conjugate_eq_iff_mem_normalizer.mpr hsP] at this
  have hP'E : conjugate P g ≤ M ⊓ β ⊓ conjugate β z := by
    have h1 := conjugate_le_conjugate_of_le' (le_inf (le_inf hPγ hPM) hPMs) g
    rw [conjugate_inf, conjugate_inf, hg1, hg2, conjugate_conjugate, hsg, ← conjugate_conjugate,
      hg2] at h1
    exact h1
  have hP'syl : ABGLocalTools.IsSylowOf p (conjugate P g) (M ⊓ β ⊓ conjugate β z) :=
    ABGLocalTools.isSylowOf_of_card hP'E (by rw [card_conjugate_eq']; exact hP.card_eq)
  have hzP' : z ∈ normalizer (conjugate P g : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer, conjugate_conjugate, ← hsg, ← conjugate_conjugate,
      conjugate_eq_iff_mem_normalizer.mpr hsP]
  have htP' : g⁻¹ * u * g ∈ normalizer (conjugate P g : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer, conjugate_conjugate,
      show g * (g⁻¹ * u * g) = u * g by group, ← conjugate_conjugate,
      conjugate_eq_iff_mem_normalizer.mpr huP]
  have hMg : conjugate M g⁻¹ = conjugate M u :=
    calc conjugate M g⁻¹ = conjugate (conjugate (conjugate M u) g) g⁻¹ := by rw [hg1]
      _ = conjugate M u := by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
  have htM : conjugate M (g⁻¹ * u * g) = β := by
    rw [conjugate_mul_mul, hMg, conjugate_conjugate M u u, hu2, conjugate_one, hg2]
  exact ⟨conjugate P g, hP'syl, hzP', g⁻¹ * u * g, hZ.2 u huZ g, htP', htM⟩

theorem ZDSetup.lemma73
    (S : ZDSetup X Z M) (hC57 : Cor57Stmt Z M) : Lemma73Stmt Z M := by
  intro z p W hW β hβ hβM
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := hW.cand
  have hβΩ : β ∈ omega M := (h.mem_omegaFix_iff.mp hβ).1
  have hp := hcand.prime
  have hp2 := hcand.ne_two
  refine ⟨fun Q hQp hQE hzQ => h.exists_invariant_sylow_inf_conjugate hZ hcand.mem_Z hcand.mem_M
    hβΩ hβM hp hp2 hQp hQE hzQ, fun P hP _ => ?_⟩
  suffices H : ∃ P₀ : Subgroup X,
      ABGLocalTools.IsSylowOf p P₀ (M ⊓ β ⊓ conjugate β z) ∧
        ∃ t ∈ Z, t ∈ normalizer (P₀ : Set X) ∧ conjugate M t = β by
    obtain ⟨P₀, hP₀, h₀⟩ := H
    exact exists_swap_of_isSylowOf_inf_conjugate hZ h hβΩ hp hP₀ hP h₀
  by_cases hcase : ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (M ⊓ β) ∧
      z ∈ normalizer (Q : Set X)
  · obtain ⟨Q, hQ, hzQ⟩ := hcase
    exact h.exists_swap_of_normalized_sylow hZ hβΩ hβM hp hp2 hQ hzQ
  · have hD : DoublyTransitive M := by
      by_contra hnot
      exact hcase ((S.lemma62 z p W hW β hβ hβM).mpr
        (T4Max.card_eq_zNumShare_of_not_doublyTransitive S hC57 hW hnot))
    obtain ⟨P₀, hP₀, -, h₀⟩ := S.exists_sylow_swap_of_not_normalized hD hcand.mem_Z hcand.mem_M hβΩ
      hβM hp hp2 hcase
    exact ⟨P₀, hP₀, h₀⟩

end Lemma73

end CFSG.GH74.Uniqueness
