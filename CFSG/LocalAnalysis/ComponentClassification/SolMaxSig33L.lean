module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33K

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem support_conj_subset_compl {m : ℕ} {τ g k : Perm (Fin m)} (hg : g * τ = τ * g)
    (hk : k.support ⊆ τ.supportᶜ) : (g * k * g⁻¹).support ⊆ τ.supportᶜ := by
  classical
  rw [Perm.support_conj]
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
  have h1 := hk hw
  rw [Finset.mem_compl, Perm.notMem_support] at h1 ⊢
  change τ (g w) = g w
  rw [← Perm.mul_apply, ← hg, Perm.mul_apply, h1]

namespace Sol33

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem exists_acts_like {c e₀ : X} (hc : c ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X))
    (he₀ : e₀ ∈ J) {Jc : Subgroup X} (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hτc : ∀ (e : X) (he : e ∈ E), coreImage θ (S.le he) * coreImage θ he₀ =
      coreImage θ he₀ * coreImage θ (S.le he))
    (hdich : (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).support) ∨
      (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).supportᶜ))
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) = coreImage θ hx)
    {a : X} (ha : a ∈ E ⊔ zpowers y) :
    ∃ (j : X) (hjJ : j ∈ Jc), a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc ∧
      ((χ ((⟨j, hjJ⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))).support.card ≤ 4 := by
  classical
  set τ := coreImage θ he₀ with hτdef
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hcB : ∀ b ∈ E ⊔ zpowers y, b * c = c * b := fun b hb =>
    (mem_centralizer_iff.mp hc b hb)
  have hNe : ∀ e ∈ E, e ∈ normalizer (Jc : Set X) := by
    intro e he
    refine mem_normalizer_of_fixed_component θ hJcC hres hinv hsubP (le_normalizer (S.le he))
      (hcB e (mem_sup_left he)) fun x hx hxs => ?_
    have hgx := (mem_normalizer_iff.mp (le_normalizer (S.le he)) x).mp hx
    rw [coreImage_conj_of_mem θ (S.le he) hx hgx]
    exact support_conj_subset_compl (hτc e he) hxs
  have hNy : y ∈ normalizer (Jc : Set X) := by
    refine mem_normalizer_of_fixed_component θ hJcC hres hinv hsubP S.hyK.1
      (hcB y (mem_sup_right (mem_zpowers y))) fun x hx hxs => ?_
    rw [coreImage_conj_of_cak θ S.hyK hx]
    exact hxs
  have hKy : y ∈ UnbalancedLayer.coreActionKernel Jc :=
    mem_coreActionKernel_of_le hJcJ' S.hyK hNy
  obtain ⟨e, he, hae | hae⟩ := S.mem_cases ha
  all_goals rcases hdich with hA | hB
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [inv_one, mul_one, hae]
      refine mem_coreActionKernel_of_commute θ hJcJ' (S.le he) (hNe e he) fun x hx hxJc => ?_
      obtain ⟨hx', hxs⟩ := hsubP x hxJc
      have hd : (coreImage θ (S.le he)).Disjoint (coreImage θ hx) := by
        rw [Perm.disjoint_iff_disjoint_support]
        exact Finset.disjoint_of_subset_left (hA e he)
          (Finset.disjoint_of_subset_right hxs disjoint_compl_right)
      exact hd.commute.eq
    · have h1 : ((⟨1, one_mem Jc⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = 1 :=
        QuotientGroup.mk_one _
      rw [h1, map_one]
      simp
  · have heJc : e ∈ Jc := hinv e (S.le he) (hcB e (mem_sup_left he))
      ⟨1, by rw [pow_one, sq]; exact S.mul_self_of_mem_E he⟩ (hB e he)
    refine ⟨e, heJc, ?_, ?_⟩
    · rw [hae, mul_inv_cancel]
      exact one_mem _
    · have h1 := hχ ⟨e, heJc⟩ (S.le he)
      rw [← card_support_ofSubtype, h1]
      exact (Finset.card_le_card (S.supp e (S.le he) he)).trans S.card.le
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [inv_one, mul_one, hae]
      refine mul_mem ?_ hKy
      refine mem_coreActionKernel_of_commute θ hJcJ' (S.le he) (hNe e he) fun x hx hxJc => ?_
      obtain ⟨hx', hxs⟩ := hsubP x hxJc
      have hd : (coreImage θ (S.le he)).Disjoint (coreImage θ hx) := by
        rw [Perm.disjoint_iff_disjoint_support]
        exact Finset.disjoint_of_subset_left (hA e he)
          (Finset.disjoint_of_subset_right hxs disjoint_compl_right)
      exact hd.commute.eq
    · have h1 : ((⟨1, one_mem Jc⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = 1 :=
        QuotientGroup.mk_one _
      rw [h1, map_one]
      simp
  · have heJc : e ∈ Jc := hinv e (S.le he) (hcB e (mem_sup_left he))
      ⟨1, by rw [pow_one, sq]; exact S.mul_self_of_mem_E he⟩ (hB e he)
    refine ⟨e, heJc, ?_, ?_⟩
    · rw [hae]
      exact conj_mem_coreActionKernel (hNe e he) hKy
    · have h1 := hχ ⟨e, heJc⟩ (S.le he)
      rw [← card_support_ofSubtype, h1]
      exact (Finset.card_le_card (S.supp e (S.le he) he)).trans S.card.le

end Sol33

end CFSG.ComponentClassification.SolMax
