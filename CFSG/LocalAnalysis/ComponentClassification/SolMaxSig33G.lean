module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33F
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33D
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem IsPermAction.eq_one_of_mem_coreActionKernel {M : Subgroup X} {r : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θ ρ) (hr : 4 ≤ r)
    {g : X} (hg : g ∈ UnbalancedLayer.coreActionKernel M) : ρ ⟨g, hg.1⟩ = 1 := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup r hr
  rw [map_one]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := θ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ρ _ * _ * (ρ _)⁻¹ = (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r))
  rw [← hρ]
  have h1 := coreImage_conj_of_cak θ hg x.2
    (by
      have := (mem_normalizer_iff.mp hg.1 x).mp x.2
      exact this)
  have h2 : (M.normalizerMonoidHom ⟨g, hg.1⟩ x : ↥M) =
      ⟨g * x * g⁻¹, (mem_normalizer_iff.mp hg.1 x).mp x.2⟩ := rfl
  rw [h2]
  exact h1

theorem exists_involution_centralizer_disjoint [Finite X] {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {E : Subgroup X}
    (hEJ : E ≤ J) {D : Finset (Fin n)} (hD : D.card = 4)
    (hsE : ∀ (x : X) (hx : x ∈ J), x ∈ E → (coreImage θ hx).support ⊆ D) {y : X}
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hB2 : IsPGroup 2 ↥(E ⊔ zpowers y)) :
    ∃ (f : X) (hf : f ∈ J), f ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X) ∧
      orderOf f = 2 ∧ (coreImage θ hf).support.card ≤ 4 ∧
      Disjoint (coreImage θ hf).support D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (J : Set X) with hNdef
  set B := E ⊔ zpowers y with hBdef
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥N →* Perm (Fin n), IsPermAction θ ρ :=
    exists_isPermAction (M := J) (by omega) (by omega) θ
  have hcard : 3 < (Dᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :
      ∃ a b c d, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧ d ∈ Dᶜ ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
        c ≠ d := by
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      Finset.three_lt_card_iff.mp hcard
    exact ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
  set σ : Perm (Fin n) := swap a b * swap c d with hσdef
  have hσA : σ ∈ alternatingGroup (Fin n) := by
    rw [Perm.mem_alternatingGroup, hσdef, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    rfl
  have hσsupp : σ.support ⊆ ({a, b, c, d} : Finset (Fin n)) := by
    intro v hv
    have hv' := Perm.mem_support.mp hv
    by_contra hvn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvn
    apply hv'
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne hvn.2.2.1 hvn.2.2.2,
      swap_apply_of_ne_of_ne hvn.1 hvn.2.1]
  have hσD : Disjoint σ.support D := by
    refine Finset.disjoint_left.mpr fun v hv hvD => ?_
    have h1 := hσsupp hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with rfl | rfl | rfl | rfl
    · exact (Finset.mem_compl.mp ha) hvD
    · exact (Finset.mem_compl.mp hb) hvD
    · exact (Finset.mem_compl.mp hc) hvD
    · exact (Finset.mem_compl.mp hd) hvD
  have hσ1 : σ ≠ 1 := by
    intro h
    have h1 : σ a = a := by rw [h]; rfl
    rw [hσdef, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left] at h1
    exact hab h1.symm
  have hσ2 : σ * σ = 1 := by
    have hcomm : swap a b * swap c d = swap c d * swap a b := by
      have hdisj : (swap a b).Disjoint (swap c d) := by
        rw [Perm.disjoint_iff_disjoint_support, Perm.support_swap hab, Perm.support_swap hcd,
          Finset.disjoint_left]
        intro v hv hv'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
        rcases hv with rfl | rfl <;> rcases hv' with h | h
        · exact hac h
        · exact had h
        · exact hbc h
        · exact hbd h
      exact hdisj.commute.eq
    rw [hσdef]
    calc swap a b * swap c d * (swap a b * swap c d) =
        swap a b * (swap c d * swap a b) * swap c d := by group
      _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hcomm]
      _ = 1 := by simp [← mul_assoc]
  have hBN : B ≤ N := sup_le (fun x hx => le_normalizer (hEJ hx)) (zpowers_le.mpr hyK.1)
  set Z : Subgroup ↥N := (centralizer ({σ} : Set (Perm (Fin n)))).comap ρ with hZdef
  have hTZ : B.subgroupOf N ≤ Z := by
    have hEZ : E.subgroupOf N ≤ Z := by
      intro x hx
      rw [mem_subgroupOf] at hx
      rw [hZdef, mem_comap, mem_centralizer_singleton_iff]
      have h1 := hρ.apply_of_mem (by omega) ⟨x, hEJ hx⟩
      have h2 : (⟨(x : X), le_normalizer (hEJ hx)⟩ : ↥N) = x := Subtype.ext rfl
      rw [h2] at h1
      rw [h1]
      have hxs := hsE x (hEJ hx) hx
      have hdisj : (coreImage θ (hEJ hx)).Disjoint σ := by
        rw [Perm.disjoint_iff_disjoint_support]
        exact Finset.disjoint_of_subset_left hxs hσD.symm
      exact hdisj.commute.eq
    have hyZ : (zpowers y).subgroupOf N ≤ Z := by
      intro x hx
      rw [mem_subgroupOf] at hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
      rw [hZdef, mem_comap, mem_centralizer_singleton_iff]
      have h1 : x = (⟨y, hyK.1⟩ : ↥N) ^ k := Subtype.ext (by
        rw [Subgroup.coe_zpow]
        exact hk.symm)
      rw [h1, map_zpow, hρ.eq_one_of_mem_coreActionKernel (by omega) hyK, one_zpow, one_mul,
        mul_one]
    intro x hx
    rw [mem_subgroupOf] at hx
    have h1 : B.subgroupOf N = E.subgroupOf N ⊔ (zpowers y).subgroupOf N := by
      rw [hBdef, subgroupOf_sup (le_sup_left.trans hBN) (le_sup_right.trans hBN)]
    have hx' : x ∈ B.subgroupOf N := hx
    rw [h1] at hx'
    exact (sup_le hEZ hyZ) hx'
  set O : Subgroup ↥N := ((pPrimeCore 2 ↥J).map J.subtype).subgroupOf N with hOdef
  have hOn : O.Normal := by
    constructor
    intro o ho g
    rw [hOdef, mem_subgroupOf] at ho ⊢
    have h1 := Sol78.le_normalizer_map_subtype (H := J) (pPrimeCore 2 ↥J)
    have h2 : (g : X) ∈ normalizer (((pPrimeCore 2 ↥J).map J.subtype : Subgroup X) : Set X) :=
      le_normalizer_pPrimeCore g.2
    exact (mem_normalizer_iff.mp h2 o).mp ho
  have hOodd : ¬ 2 ∣ Nat.card (QuotientGroup.mk' O).ker := by
    rw [QuotientGroup.ker_mk']
    have h1 : Nat.card O = Nat.card ((pPrimeCore 2 ↥J).map J.subtype) := by
      rw [hOdef]
      exact Nat.card_congr (subgroupOfEquivOfLe (fun x hx =>
        le_normalizer (map_subtype_le _ hx))).toEquiv
    rw [h1, card_map_of_injective J.subtype_injective]
    exact fun h => (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr h)
  obtain ⟨q, hq⟩ := θ.surjective ⟨σ, hσA⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  set sN : ↥N := ⟨s, le_normalizer s.2⟩ with hsNdef
  have hgs : ∀ g ∈ B.subgroupOf N, g * sN * g⁻¹ * sN⁻¹ ∈ O := by
    intro g hg
    have hgZ := hTZ hg
    rw [hZdef, mem_comap, mem_centralizer_singleton_iff] at hgZ
    rw [hOdef, mem_subgroupOf]
    have hgsJ : (g : X) * s * (g : X)⁻¹ ∈ J := (mem_normalizer_iff.mp g.2 s).mp s.2
    have h1 := hρ g s
    have h2 : (J.normalizerMonoidHom g s : ↥J) = ⟨(g : X) * s * (g : X)⁻¹, hgsJ⟩ := rfl
    rw [h2, hq] at h1
    change _ = ρ g * σ * (ρ g)⁻¹ at h1
    rw [hgZ, show σ * ρ g * (ρ g)⁻¹ = σ by group] at h1
    have h3 : ((⟨(g : X) * s * (g : X)⁻¹, hgsJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) =
        (s : ↥J ⧸ pPrimeCore 2 ↥J) := θ.injective (by rw [hq]; exact Subtype.ext h1)
    have h4 : s⁻¹ * (⟨(g : X) * s * (g : X)⁻¹, hgsJ⟩ : ↥J) ∈ pPrimeCore 2 ↥J :=
      QuotientGroup.eq.mp h3.symm
    have h5 : s * (s⁻¹ * (⟨(g : X) * s * (g : X)⁻¹, hgsJ⟩ : ↥J)) * s⁻¹ ∈ pPrimeCore 2 ↥J :=
      (inferInstance : (pPrimeCore 2 ↥J).Normal).conj_mem _ h4 s
    refine ⟨_, h5, ?_⟩
    change (s : X) * ((s : X)⁻¹ * ((g : X) * s * (g : X)⁻¹)) * (s : X)⁻¹ =
      (g : X) * s * (g : X)⁻¹ * (s : X)⁻¹
    group
  have hsT : QuotientGroup.mk' O sN ∈
      centralizer (((B.subgroupOf N).map (QuotientGroup.mk' O) : Subgroup _) : Set _) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    have h1 : QuotientGroup.mk' O (g * sN * g⁻¹ * sN⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hgs g hg)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc QuotientGroup.mk' O g * QuotientGroup.mk' O sN =
        (QuotientGroup.mk' O g * QuotientGroup.mk' O sN * (QuotientGroup.mk' O g)⁻¹ *
          (QuotientGroup.mk' O sN)⁻¹) * QuotientGroup.mk' O sN * QuotientGroup.mk' O g := by
          group
      _ = QuotientGroup.mk' O sN * QuotientGroup.mk' O g := by rw [h1, one_mul]
  have hT2 : IsPGroup 2 ↥(B.subgroupOf N) := hB2.of_equiv (subgroupOfEquivOfLe hBN).symm
  have hlift := GrSLit.map_centralizer_eq_of_odd_ker (QuotientGroup.mk' O)
    (QuotientGroup.mk'_surjective O) hOodd hT2
  rw [← hlift] at hsT
  obtain ⟨w, hwC, hwq⟩ := hsT
  have hwo : sN⁻¹ * w ∈ O := QuotientGroup.eq.mp hwq.symm
  rw [hOdef, mem_subgroupOf] at hwo
  obtain ⟨o, ho, hoeq⟩ := hwo
  have hoeq' : (o : X) = (s : X)⁻¹ * w := hoeq
  have hwJ : (w : X) ∈ J := by
    have h1 : (w : X) = s * (o : X) := by
      rw [hoeq']
      group
    rw [h1]
    exact mul_mem s.2 o.2
  set wJ : ↥J := ⟨w, hwJ⟩ with hwJdef
  have hwJs : (wJ : ↥J ⧸ pPrimeCore 2 ↥J) = (s : ↥J ⧸ pPrimeCore 2 ↥J) := by
    symm
    rw [QuotientGroup.eq]
    have h1 : s⁻¹ * wJ = o := Subtype.ext (by
      rw [hoeq']
      rfl)
    rw [h1]
    exact ho
  have hwθ : θ (wJ : ↥J ⧸ pPrimeCore 2 ↥J) = ⟨σ, hσA⟩ := by rw [hwJs, hq]
  have hw2 : (wJ : ↥J ⧸ pPrimeCore 2 ↥J) ^ 2 = 1 := by
    apply θ.injective
    rw [map_pow, hwθ, map_one, sq]
    exact Subtype.ext hσ2
  have hw1 : (wJ : ↥J ⧸ pPrimeCore 2 ↥J) ≠ 1 := by
    intro h
    apply hσ1
    have h1 := hwθ
    rw [h, map_one] at h1
    exact (congrArg Subtype.val h1).symm
  obtain ⟨k, hk2, hkimg⟩ := exists_involution_of_mk
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hw2 hw1
  have hfJ : ((wJ ^ k : ↥J) : X) ∈ J := (wJ ^ k).2
  refine ⟨((wJ ^ k : ↥J) : X), hfJ, ?_, ?_, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro b hb
    have hbw : (⟨b, hBN hb⟩ : ↥N) * w = w * ⟨b, hBN hb⟩ :=
      mem_centralizer_iff.mp hwC ⟨b, hBN hb⟩ (show (⟨b, hBN hb⟩ : ↥N) ∈ B.subgroupOf N from
        hb)
    have hbw' : b * (w : X) = (w : X) * b := congrArg Subtype.val hbw
    have h1 : ((wJ ^ k : ↥J) : X) = (w : X) ^ k := by rw [Subgroup.coe_pow]
    rw [h1]
    exact (Commute.pow_right hbw' k).eq
  · rw [Subgroup.orderOf_coe]
    exact hk2
  · have h1 : coreImage θ hfJ = σ := by
      unfold coreImage
      have h2 : (⟨((wJ ^ k : ↥J) : X), hfJ⟩ : ↥J) = wJ ^ k := rfl
      rw [h2, hkimg, hwθ]
    rw [h1]
    exact (Finset.card_le_card hσsupp).trans Finset.card_le_four
  · have h1 : coreImage θ hfJ = σ := by
      unfold coreImage
      have h2 : (⟨((wJ ^ k : ↥J) : X), hfJ⟩ : ↥J) = wJ ^ k := rfl
      rw [h2, hkimg, hwθ]
    rw [h1]
    exact hσD

end CFSG.ComponentClassification.SolMax
