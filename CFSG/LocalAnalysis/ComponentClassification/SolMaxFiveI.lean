module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveG

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem coreImage_congr {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {x x' : X} (h : x = x')
    (hx : x ∈ J) (hx' : x' ∈ J) : coreImage θ hx = coreImage θ hx' := by
  subst h
  rfl

theorem exists_fix_of_pump [Finite X] {M Jc : Subgroup X} {t : X} {r : ℕ}
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ) (hr5 : 5 ≤ r)
    (hr6 : r ≠ 6) (htM : t ∈ normalizer (M : Set X)) (ht2 : t * t = 1) (hJcM : Jc ≤ M)
    (hJcC : Jc ≤ centralizer ({t} : Set X))
    (hJcpc : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))))
    (eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5)) (hperf : ⁅Jc, Jc⁆ = Jc)
    (hJcK : ¬ Jc ≤ UnbalancedLayer.coreActionKernel M) :
    ∃ τ : Perm (Fin r), r - τ.support.card = 5 ∧
      (∀ (z : X) (hz : z ∈ Jc), ρ ⟨z, le_normalizer (hJcM hz)⟩ ∈
        (fixAlt τ).map (alternatingGroup (Fin r)).subtype) ∧
      (∀ b ∈ fixAlt τ, ∃ (z : X) (hz : z ∈ Jc),
        ρ ⟨z, le_normalizer (hJcM hz)⟩ = (b : Perm (Fin r))) ∧
      ∀ (z : X) (hz : z ∈ Jc), z ∈ coreNOf Jc → ρ ⟨z, le_normalizer (hJcM hz)⟩ = 1 := by
  classical
  obtain ⟨τ, hτimg, hτ5⟩ :=
    exists_perm_of_fixed_component htM ht2 hJcM hJcC hJcpc le_rfl hr5 hr6 eJc θM
  have hJcN : Jc ≤ normalizer (M : Set X) := fun z hz => le_normalizer (hJcM hz)
  have hmem : ∀ (z : X) (hz : z ∈ Jc),
      ρ ⟨z, hJcN hz⟩ ∈ (fixAlt τ).map (alternatingGroup (Fin r)).subtype := by
    intro z hz
    have h1 : ρ ⟨z, hJcN hz⟩ = (θM ((⟨z, hJcM hz⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) :=
      hρ.apply_of_mem (by omega) ⟨z, hJcM hz⟩
    rw [h1]
    exact ⟨_, hτimg ⟨⟨z, hJcM hz⟩, hz, rfl⟩, rfl⟩
  have hQ : Nat.card ((fixAlt τ).map (alternatingGroup (Fin r)).subtype) ≤
      Nat.factorial 5 / 2 := by
    rw [card_map_of_injective (alternatingGroup (Fin r)).subtype_injective,
      card_fixAlt (by omega), hτ5]
  obtain ⟨hsurj, hO⟩ := hρ.image_eq_of_le hJcN le_rfl eJc hperf hJcK hQ hmem
  exact ⟨τ, hτ5, hmem, fun b hb => hsurj b ⟨b, hb, rfl⟩, hO⟩

theorem mul_inv_mem_cak_of_four [Finite X] {J Jc : Subgroup X}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)) {e₀ : X} (he₀ : e₀ ∈ J)
    (hs4 : (coreImage θ he₀).support.card = 4) (hJcJ : Jc ≤ J)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    {a j j₀ : X} (hjJc : j ∈ Jc) (hj2 : j * j = 1) (hθj : coreImage θ (hJcJ hjJc) ≠ 1)
    (hajK : a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc) (hj₀ : j₀ ∈ J)
    (haj₀ : a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hj₀4 : (coreImage θ hj₀).support.card ≤ 4) :
    a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjJ : j ∈ J := hJcJ hjJc
  set θj := coreImage θ hjJ with hθjdef
  set π : Perm (Fin 9) := θj⁻¹ * coreImage θ hj₀ with hπdef
  have haJN : a ∈ normalizer (J : Set X) := by
    have h1 : a = a * j₀⁻¹ * j₀ := by group
    rw [h1]
    exact mul_mem haj₀.1 (le_normalizer hj₀)
  have haJcN : a ∈ normalizer (Jc : Set X) := by
    have h1 : a = a * j⁻¹ * j := by group
    rw [h1]
    exact mul_mem hajK.1 (le_normalizer hjJc)
  have hcoreJc : ∀ x x' : ↥Jc, (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) = (x' : ↥Jc ⧸ pPrimeCore 2 ↥Jc) →
      coreImage θ (hJcJ x.2) = coreImage θ (hJcJ x'.2) := by
    intro x x' hxx
    rw [← hχ x (hJcJ x.2), ← hχ x' (hJcJ x'.2), hxx]
  have hcomm : ∀ (l : X) (hl : l ∈ Jc),
      π * coreImage θ (hJcJ hl) = coreImage θ (hJcJ hl) * π := by
    intro l hl
    have hal : a * l * a⁻¹ ∈ J := (mem_normalizer_iff.mp haJN l).mp (hJcJ hl)
    have h1 := coreImage_conj_of_acts θ hj₀ haj₀ (hJcJ hl) hal
    have hjl : j * l * j⁻¹ ∈ Jc := mul_mem (mul_mem hjJc hl) (inv_mem hjJc)
    have hgx : a * j⁻¹ * (j * l * j⁻¹) * (a * j⁻¹)⁻¹ ∈ Jc := by
      have h2 : a * j⁻¹ * (j * l * j⁻¹) * (a * j⁻¹)⁻¹ = a * l * a⁻¹ := by group
      rw [h2]
      exact (mem_normalizer_iff.mp haJcN l).mp hl
    have h2 := mk_conj_eq_of_mem_cak hajK ⟨j * l * j⁻¹, hjl⟩ hgx
    have h3 := hcoreJc _ _ h2
    have h4 : coreImage θ hal = coreImage θ (hJcJ hgx) :=
      coreImage_congr θ (by group) hal (hJcJ hgx)
    have h5 := coreImage_conj_of_mem θ hjJ (hJcJ hl) (hJcJ hjl)
    have h6 : coreImage θ hj₀ * coreImage θ (hJcJ hl) * (coreImage θ hj₀)⁻¹ =
        θj * coreImage θ (hJcJ hl) * θj⁻¹ := by
      rw [← h1]
      exact h4.trans (h3.trans h5)
    rw [hπdef]
    calc θj⁻¹ * coreImage θ hj₀ * coreImage θ (hJcJ hl) =
        θj⁻¹ * (coreImage θ hj₀ * coreImage θ (hJcJ hl) * (coreImage θ hj₀)⁻¹) *
          coreImage θ hj₀ := by group
      _ = θj⁻¹ * (θj * coreImage θ (hJcJ hl) * θj⁻¹) * coreImage θ hj₀ := by rw [h6]
      _ = coreImage θ (hJcJ hl) * (θj⁻¹ * coreImage θ hj₀) := by group
  have hπfix : ∀ v, v ∉ (coreImage θ he₀).support → π v = v := by
    intro v hv
    refine apply_eq_of_commute_fixAlt (by omega) (fun b hb => ?_) hv
    obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv (coreImage θ he₀)
    obtain ⟨q, hq⟩ := χ.surjective (φ.symm ⟨b, hb⟩)
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (b : Perm (Fin 9)) = coreImage θ (hJcJ l.2) := by
      rw [← hχ l (hJcJ l.2), hq]
      have h2 := hφ (φ.symm ⟨b, hb⟩)
      rw [MulEquiv.apply_symm_apply] at h2
      exact h2
    rw [h1]
    exact hcomm l l.2
  have hθjsupp : θj.support ⊆ (coreImage θ he₀).supportᶜ := by
    intro v hv
    rw [Finset.mem_compl]
    intro hvτ
    have h1 := hχ ⟨j, hjJc⟩ hjJ
    rw [← hθjdef] at h1
    rw [Perm.mem_support, ← h1] at hv
    apply hv
    refine Perm.ofSubtype_apply_of_not_mem _ ?_
    intro hvF
    exact (Finset.mem_compl.mp hvF) hvτ
  have hπsupp : π.support ⊆ (coreImage θ he₀).support := by
    intro v hv
    by_contra hvτ
    exact (Perm.mem_support.mp hv) (hπfix v hvτ)
  have hdisj : θj.Disjoint π := by
    rw [Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left hθjsupp
      (Finset.disjoint_of_subset_right hπsupp disjoint_compl_left)
  have hmul : coreImage θ hj₀ = θj * π := by
    rw [hπdef]
    group
  have hcard := hdisj.card_support_mul
  rw [← hmul] at hcard
  have hθj2 : θj * θj = 1 := by
    have h1 : (⟨j, hjJ⟩ : ↥J) * ⟨j, hjJ⟩ = 1 := Subtype.ext hj2
    have h2 : θ ((⟨j, hjJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨j, hjJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  have h4 : 4 ≤ θj.support.card :=
    four_le_card_support_of_mem_alternatingGroup (coreImage_mem θ hjJ) hθj2 hθj
  have hπ1 : π = 1 := by
    have h0 : π.support.card = 0 := by omega
    exact Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0)
  have hj₀j : coreImage θ hj₀ = θj := by rw [hmul, hπ1, mul_one]
  have h1 : θ ((⟨j₀, hj₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) =
      θ ((⟨j, hjJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := Subtype.ext hj₀j
  have h2 := QuotientGroup.eq.mp (θ.injective h1)
  have h3 : j₀⁻¹ * j ∈ coreNOf J := ⟨_, h2, rfl⟩
  have h4 : j₀ * j⁻¹ ∈ coreNOf J := by
    have h5 := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hj₀))
      _).mp (inv_mem h3)
    have h6 : j₀ * (j₀⁻¹ * j)⁻¹ * j₀⁻¹ = j₀ * j⁻¹ := by group
    rwa [h6] at h5
  have h5 : a * j⁻¹ = (a * j₀⁻¹) * (j₀ * j⁻¹) := by group
  rw [h5]
  exact mul_mem haj₀ (coreNOf_le_coreActionKernel J h4)

end CFSG.ComponentClassification.SolMax
