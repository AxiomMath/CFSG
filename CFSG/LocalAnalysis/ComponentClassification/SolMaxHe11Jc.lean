module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33F
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
public import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPlaneCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.ComponentClassification.SolMax.He11

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem eq_of_isPComponent_of_card [Finite X] {H J Jc Jc' : Subgroup X} {n : ℕ}
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {e₀ : X} (he₀ : e₀ ∈ J)
    (hs4 : (coreImage θ he₀).support.card = 4) (hn : 9 ≤ n) (hJcJ : Jc ≤ J) (hJc'J : Jc' ≤ J)
    (hJcH : Jc ≤ H) (hJc'H : Jc' ≤ H) (hpc : IsPComponent 2 (Jc.subgroupOf H))
    (hpc' : IsPComponent 2 (Jc'.subgroupOf H))
    (χ' : ↥Jc' ⧸ pPrimeCore 2 ↥Jc' ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)))
    (hχ' : ∀ (x : ↥Jc') (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ' (x : ↥Jc' ⧸ pPrimeCore 2 ↥Jc') : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) = coreImage θ hx)
    (hcard : 24 < Nat.card (↥Jc ⧸ pPrimeCore 2 ↥Jc)) : Jc = Jc' := by
  by_contra hne
  have hK : Jc ≤ UnbalancedLayer.coreActionKernel Jc' :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJc'H hJcH hpc' hpc (Ne.symm hne)
  have hF5 : 5 ≤ ((coreImage θ he₀).supportᶜ : Finset (Fin n)).card := by
    rw [Finset.card_compl, Fintype.card_fin, hs4]
    omega
  have hfill : ∀ b ∈ RankThree.GroupTheory.alternatingOn (coreImage θ he₀).supportᶜ,
      ∃ (y : X) (hy : y ∈ Jc'), coreImage θ (hJc'J hy) = b := by
    rintro _ ⟨b', hb', rfl⟩
    obtain ⟨q, hq⟩ := χ'.surjective ⟨b', hb'⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨y, y.2, ?_⟩
    rw [← hχ' y (hJc'J y.2), hq]
  have hfix : ∀ (x : X) (hx : x ∈ Jc), ∀ v ∈ ((coreImage θ he₀).supportᶜ : Finset (Fin n)),
      coreImage θ (hJcJ hx) v = v := by
    intro x hx v hv
    refine RankThree.GroupTheory.apply_eq_self_of_commute_alternatingOn hF5 (fun b hb => ?_) hv
    obtain ⟨y, hy, rfl⟩ := hfill b hb
    have hxy : x * y * x⁻¹ ∈ J := mul_mem (mul_mem (hJcJ hx) (hJc'J hy)) (inv_mem (hJcJ hx))
    have h1 := coreImage_conj_eq_of_cak hJc'J χ' hχ' (hK hx) hy hxy
    rw [coreImage_conj_of_mem θ (hJcJ hx) (hJc'J hy) hxy] at h1
    have h2 : coreImage θ (hJcJ hx) * coreImage θ (hJc'J hy) =
        coreImage θ (hJc'J hy) * coreImage θ (hJcJ hx) := by
      calc coreImage θ (hJcJ hx) * coreImage θ (hJc'J hy) =
          coreImage θ (hJcJ hx) * coreImage θ (hJc'J hy) * (coreImage θ (hJcJ hx))⁻¹ *
            coreImage θ (hJcJ hx) := by group
        _ = coreImage θ (hJc'J hy) * coreImage θ (hJcJ hx) := by rw [h1]
    exact h2
  let φ : ↥Jc →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp
    (θ.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp (inclusion hJcJ)))
  have hrange : φ.range ≤ (Perm.ofSubtype :
      Perm ↥((coreImage θ he₀).support : Finset (Fin n)) →* Perm (Fin n)).range := by
    rintro _ ⟨x, rfl⟩
    rw [Perm.mem_range_ofSubtype_iff]
    intro v hv
    by_contra hvD
    exact (Perm.mem_support.mp hv) (hfix x x.2 v (Finset.mem_compl.mpr hvD))
  have hr24 : Nat.card φ.range ≤ 24 := by
    calc Nat.card φ.range ≤ Nat.card (Perm.ofSubtype :
          Perm ↥((coreImage θ he₀).support : Finset (Fin n)) →* Perm (Fin n)).range :=
          card_le_of_le hrange
      _ ≤ Nat.card (Perm ↥((coreImage θ he₀).support : Finset (Fin n))) :=
          Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
      _ = 24 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe, hs4]
          rfl
  have hle : φ.ker.map (inclusion hJcJ) ≤ pPrimeCore 2 ↥J := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : φ x = 1 := hx
    have h2 : θ ((inclusion hJcJ x : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext hx'
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
    exact h2
  have hker : φ.ker ≤ pPrimeCore 2 ↥Jc := by
    refine le_sSup ⟨φ.normal_ker, ?_⟩
    have h1 : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥J) := by
      rw [← card_map_of_injective (inclusion_injective hJcJ)]
      exact card_dvd_of_le hle
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hidx : (pPrimeCore 2 ↥Jc).index ≤ φ.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite)) (index_dvd_of_le hker)
  have hcard' : (pPrimeCore 2 ↥Jc).index = Nat.card (↥Jc ⧸ pPrimeCore 2 ↥Jc) := rfl
  rw [index_ker] at hidx
  omega

end CFSG.ComponentClassification.SolMax.He11
