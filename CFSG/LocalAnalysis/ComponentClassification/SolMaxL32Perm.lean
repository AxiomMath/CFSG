module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33F

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_coreActionKernel_of_support_subset [Finite X] {J Jc : Subgroup X} {n : ℕ}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} (hρJ : IsPermAction θ ρJ)
    {c e₀ : X} (he₀ : e₀ ∈ J) (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) = coreImage θ hx)
    {w : X} (hwN : w ∈ normalizer (J : Set X)) (hwc : w * c = c * w)
    (hwD : (ρJ ⟨w, hwN⟩).support ⊆ (coreImage θ he₀).support) :
    w ∈ normalizer (Jc : Set X) ∧ w ∈ UnbalancedLayer.coreActionKernel Jc := by
  classical
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hconj : ∀ (x : X) (hx : x ∈ J), (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ →
      coreImage θ ((mem_normalizer_iff.mp hwN x).mp hx) = coreImage θ hx := by
    intro x hx hxs
    have h1 := hρJ ⟨w, hwN⟩ ⟨x, hx⟩
    have h2 : (J.normalizerMonoidHom ⟨w, hwN⟩ ⟨x, hx⟩ : ↥J) =
        ⟨w * x * w⁻¹, (mem_normalizer_iff.mp hwN x).mp hx⟩ := rfl
    rw [h2] at h1
    change coreImage θ _ = ρJ ⟨w, hwN⟩ * coreImage θ hx * (ρJ ⟨w, hwN⟩)⁻¹ at h1
    rw [h1]
    have hd : (ρJ ⟨w, hwN⟩).Disjoint (coreImage θ hx) := by
      rw [Perm.disjoint_iff_disjoint_support]
      exact Finset.disjoint_of_subset_left hwD
        (Finset.disjoint_of_subset_right hxs disjoint_compl_right)
    rw [hd.commute.eq]
    group
  have hwJc : w ∈ normalizer (Jc : Set X) :=
    mem_normalizer_of_fixed_component θ hJcC hres hinv hsubP hwN hwc fun x hx hxs => by
      rw [hconj x hx hxs]
      exact hxs
  refine ⟨hwJc, hwJc, fun l hl => ?_⟩
  have hlJ := hJcJ' hl
  obtain ⟨hlJ', hls'⟩ := hsubP l hl
  have hls : (coreImage θ hlJ).support ⊆ (coreImage θ he₀).supportᶜ := hls'
  have hwinv : w⁻¹ ∈ normalizer (J : Set X) := inv_mem hwN
  have hwl : w⁻¹ * l * w⁻¹⁻¹ ∈ J := (mem_normalizer_iff.mp hwinv l).mp hlJ
  have h1 := hρJ ⟨w⁻¹, hwinv⟩ ⟨l, hlJ⟩
  have h2 : (J.normalizerMonoidHom ⟨w⁻¹, hwinv⟩ ⟨l, hlJ⟩ : ↥J) = ⟨w⁻¹ * l * w⁻¹⁻¹, hwl⟩ := rfl
  rw [h2] at h1
  change coreImage θ hwl = ρJ ⟨w⁻¹, hwinv⟩ * coreImage θ hlJ * (ρJ ⟨w⁻¹, hwinv⟩)⁻¹ at h1
  have hd : (ρJ ⟨w⁻¹, hwinv⟩).Disjoint (coreImage θ hlJ) := by
    rw [Perm.disjoint_iff_disjoint_support]
    have h9 : ρJ ⟨w⁻¹, hwinv⟩ = (ρJ ⟨w, hwN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h9, Perm.support_inv]
    exact Finset.disjoint_of_subset_left hwD
      (Finset.disjoint_of_subset_right hls disjoint_compl_right)
  have h3 : coreImage θ hwl = coreImage θ hlJ := by
    rw [h1, hd.commute.eq, mul_inv_cancel_right]
  have hwlJc : w⁻¹ * l * w⁻¹⁻¹ ∈ Jc := (mem_normalizer_iff.mp (inv_mem hwJc) l).mp hl
  have hz : l⁻¹ * w⁻¹ * l * w ∈ Jc := by
    have h4 : l⁻¹ * w⁻¹ * l * w = l⁻¹ * (w⁻¹ * l * w⁻¹⁻¹) := by group
    rw [h4]
    exact mul_mem (inv_mem hl) hwlJc
  have h5 : coreImage θ (hJcJ' hz) = 1 := by
    have h6 : (⟨l⁻¹ * w⁻¹ * l * w, hJcJ' hz⟩ : ↥J) =
        (⟨l, hlJ⟩ : ↥J)⁻¹ * ⟨w⁻¹ * l * w⁻¹⁻¹, hwl⟩ :=
      Subtype.ext (by simp only [coe_mul, coe_inv]; group)
    have h7 : coreImage θ (hJcJ' hz) = (coreImage θ hlJ)⁻¹ * coreImage θ hwl := by
      unfold coreImage
      rw [h6, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      rfl
    rw [h7, h3, inv_mul_cancel]
  have h8 : ((χ ((⟨_, hz⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) :
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) = 1 := by
    apply Perm.ofSubtype_injective
    rw [hχ ⟨_, hz⟩ (hJcJ' hz), h5, map_one]
  have h9 : χ ((⟨_, hz⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = 1 := Subtype.ext h8
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h9
  exact ⟨⟨_, hz⟩, h9, rfl⟩

theorem commute_altFour : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    a * b = b * a := by
  decide

theorem commute_of_four {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4) {u v : Perm (Fin n)}
    (huA : Perm.sign u = 1) (hvA : Perm.sign v = 1) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (huD : ∀ ω ∉ D, u ω = ω) (hvD : ∀ ω ∉ D, v ω = ω) : u * v = v * u := by
  classical
  have hcardD : Fintype.card ↥D = 4 := by rw [Fintype.card_coe, hD]
  set e : ↥D ≃ Fin 4 := Fintype.equivFinOfCardEq hcardD with hedef
  have hmem : ∀ σ : Perm (Fin n), (∀ ω ∉ D, σ ω = ω) →
      σ ∈ (Perm.ofSubtype : Perm (Subtype (· ∈ D)) →* Perm (Fin n)).range := by
    intro σ hσD
    rw [Perm.mem_range_ofSubtype_iff]
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (hσD ω hωD)
  obtain ⟨u', rfl⟩ := hmem u huD
  obtain ⟨v', rfl⟩ := hmem v hvD
  rw [Perm.sign_ofSubtype] at huA hvA
  have hu2' : u' * u' = 1 := Perm.ofSubtype_injective (by rw [map_mul, hu2, map_one])
  have hv2' : v' * v' = 1 := Perm.ofSubtype_injective (by rw [map_mul, hv2, map_one])
  set a : alternatingGroup (Fin 4) := ⟨e.permCongr u', by
    rw [Perm.mem_alternatingGroup, Perm.sign_permCongr]; exact huA⟩ with hadef
  set b : alternatingGroup (Fin 4) := ⟨e.permCongr v', by
    rw [Perm.mem_alternatingGroup, Perm.sign_permCongr]; exact hvA⟩ with hbdef
  have ha2 : a * a = 1 := Subtype.ext (by
    change e.permCongr u' * e.permCongr u' = 1
    rw [← Equiv.permCongr_mul, hu2']
    ext x
    simp)
  have hb2 : b * b = 1 := Subtype.ext (by
    change e.permCongr v' * e.permCongr v' = 1
    rw [← Equiv.permCongr_mul, hv2']
    ext x
    simp)
  have hab := congrArg Subtype.val (commute_altFour a b ha2 hb2)
  change e.permCongr u' * e.permCongr v' = e.permCongr v' * e.permCongr u' at hab
  rw [← Equiv.permCongr_mul, ← Equiv.permCongr_mul] at hab
  have h1 : u' * v' = v' * u' := e.permCongr.injective hab
  rw [← map_mul, ← map_mul, h1]

theorem exists_not_commute_of_sign {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4)
    {σ : Perm (Fin n)} (hσD : ∀ ω ∉ D, σ ω = ω) (hσ : Perm.sign σ ≠ 1) :
    ∃ u : alternatingGroup (Fin n), u * u = 1 ∧ (∀ ω ∉ D, (u : Perm (Fin n)) ω = ω) ∧
      σ * u ≠ u * σ := by
  by_contra hne
  push Not at hne
  exact hσ (sign_eq_one_of_commute_klein hD hσD hne)

end CFSG.ComponentClassification.SolMax.L32
