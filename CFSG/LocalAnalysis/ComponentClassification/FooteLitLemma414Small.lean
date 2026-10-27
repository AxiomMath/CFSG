module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Bender
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Trans

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conj_eq_of_footeInCC_of_mem_footeK
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {s : G}
    (hs : FooteInCC M s) (hsK : s ∈ footeK L s) {T A : Subgroup G}
    (hT : IsSylowOf 2 T (coreActionKernel M ⊓ centralizer ({s} : Set G)))
    (hA : IsOmegaOneOf A T) {y : G} (hy2 : y ^ 2 = 1) (hys : y ∈ centralizer ({s} : Set G))
    (hyT : y ∈ normalizer (T : Set G)) : ∀ x ∈ A, y * x * y⁻¹ = x := by
  have hs' := hs
  obtain ⟨hs2, hsC, hCs⟩ := hs'
  obtain ⟨hBN, -, -, -⟩ := foote_lemma_4_9_core h h47 hST hM hs2 hsC hCs
  obtain ⟨-, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM hs2 hsC hCs
  obtain ⟨A', hA', -, -, -, hS', -⟩ := exists_omega_of_footeInCC h h47 hST hAsc h2An hM hs hT
  have hcov : IsCoverOverTwo (footeK L s ⧸ pPrimeCore 2 (footeK L s)) (Open.Sz 1) := by
    rcases htype with ⟨-, hsK'⟩ | ⟨hcov, -⟩
    · exact absurd hsK hsK'
    · exact hcov
  have hAK := hS' hsK
  have hRK := isSylowOf_inf_footeK h h47 hST hAsc h2An hM hs hT
  have hyK : y ∈ normalizer (footeK L s : Set G) := mem_normalizer_footeK (hBN hys)
  have hyR : y ∈ normalizer ((T ⊓ footeK L s : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem hyT hyK
  intro x hx
  rw [hA.eq hA'] at hx
  exact conj_eq_of_isCoverOverTwo_sz hRK hcov hyK hyR hy2 (mem_inf.mpr ⟨hA'.1 hx, hAK hx⟩)
    (hA'.2.1 x hx)

theorem eight_le_card_inf_centralizer
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M)
    {T A : Subgroup G} (hT : IsSylowOf 2 T (coreActionKernel M)) (hA : IsOmegaOneOf A T)
    (hACC : ∀ a ∈ A, a ≠ 1 → FooteInCC M a) {t y : G} (htA : t ∈ A) (ht1 : t ≠ 1)
    (hTt : T ≤ centralizer ({t} : Set G)) (hy2 : y ^ 2 = 1) (hyN : y ∈ normalizer (M : Set G))
    (hyt : y * t = t * y) (hyT : y ∈ normalizer (T : Set G)) :
    8 ≤ Nat.card ↥(A ⊓ centralizer ({y} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hC
  have ht := hACC t htA ht1
  have ht' := ht
  obtain ⟨ht2, htC, hCt⟩ := ht'
  have hTt' : IsSylowOf 2 T (C ⊓ centralizer ({t} : Set G)) :=
    hT.of_le (le_inf hT.le hTt) inf_le_left
  have hyA : y ∈ normalizer (A : Set G) := hA.mem_normalizer hyT
  have hys : y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hyt
  obtain ⟨A', hA', -, hA8, hB, -, -⟩ := exists_omega_of_footeInCC h h47 hST hAsc h2An hM ht hTt'
  have hAA' : A' = A := hA'.eq hA
  rw [hAA'] at hA8 hB
  by_contra hU8
  push Not at hU8
  suffices hcent : ∀ x ∈ A, y * x * y⁻¹ = x by
    have hle : A ≤ A ⊓ centralizer ({y} : Set G) := fun x hx => mem_inf.mpr ⟨hx,
      mem_centralizer_singleton_iff.mpr (by
        calc x * y = y * x * y⁻¹ * y := by rw [hcent x hx]
          _ = y * x := by group)⟩
    have := card_le_of_le hle
    omega
  have hBN := (foote_lemma_4_9_core h h47 hST hM ht2 htC hCt).1
  by_cases htK : t ∈ footeK L t
  · exact conj_eq_of_footeInCC_of_mem_footeK h h47 hST hAsc h2An hM ht htK hTt' hA hy2 hys hyT
  obtain ⟨hdec, h4⟩ := hB htK
  have hyK : y ∈ normalizer (footeK L t : Set G) := mem_normalizer_footeK (hBN hys)
  have hUp : IsPGroup 2 ↥(A ⊓ centralizer ({y} : Set G)) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hA.2.1 x (mem_inf.mp x.2).1)⟩
  have hfix : Nat.card ↥(A ⊓ footeK L t ⊓ centralizer ({y} : Set G)) ≤ 2 :=
    card_le_two_of_lt_eight hUp (inf_le_inf_right _ inf_le_left) hU8
      (mem_inf.mpr ⟨htA, mem_centralizer_singleton_iff.mpr hyt.symm⟩)
      fun h1 => htK (mem_inf.mp (mem_inf.mp h1).1).2
  obtain ⟨f, hfF, hf1, hyf, hc⟩ :=
    exists_commutator_mem_pair hA.2.1 hy2 hyA hyK htA hyt hdec h4 hfix
  have hfA : f ∈ A := (mem_inf.mp hfF).1
  have hf := hACC f hfA hf1
  have hf' := hf
  obtain ⟨hf2, hfC, hCf⟩ := hf'
  have hyf' : y ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.mpr hyf
  have hAC : A ≤ C := hA.1.trans hT.le
  have hAD : A ≤ C ⊓ centralizer ({f} : Set G) := fun x hx =>
    mem_inf.mpr ⟨hAC hx, mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one hA.2.1 hx hfA)⟩
  have hAp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hA.2.1 x x.2)⟩
  have hyD : y ∈ normalizer ((C ⊓ centralizer ({f} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem (normalizer_le_normalizer_coreActionKernel M hyN)
      (le_normalizer hyf')
  obtain ⟨Tf, hTf, hATf, hyTf⟩ := exists_isSylowOf_ge_mem_normalizer hAD hAp hy2 hyD hyA
  obtain ⟨A₂, hA₂, -, -, hB₂, -, -⟩ := exists_omega_of_footeInCC h h47 hST hAsc h2An hM hf hTf
  have hA₂A : A₂ = A := omega_eq_of_le hT hA (fun x hx => hA₂.2.2 x (hATf hx) (hA.2.1 x hx))
    (hA₂.1.trans (hTf.le.trans inf_le_left)) hA₂.2.1
  rw [hA₂A] at hA₂ hB₂
  by_cases hfK : f ∈ footeK L f
  · exact conj_eq_of_footeInCC_of_mem_footeK h h47 hST hAsc h2An hM hf hfK hTf hA₂ hy2 hyf' hyTf
  obtain ⟨hdec₂, -⟩ := hB₂ hfK
  have hBNf := (foote_lemma_4_9_core h h47 hST hM hf2 hfC hCf).1
  exact conj_eq_of_commutator_mem_pair hA.2.1 (mem_normalizer_footeK (hBNf hyf')) hfA hfK hyf
    hdec₂ hc

end CFSG.ComponentClassification.FooteLit
