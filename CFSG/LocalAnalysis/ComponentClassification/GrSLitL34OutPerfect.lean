module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.ComponentClassification.GrSLit.L34Out

open CFSG Subgroup CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
open scoped commutatorElement

theorem le_sup_centralizer_of_perfect {X : Type} [Group X]
    [Finite X] {K H : Subgroup X} (hK : Group.IsPerfect ↥K) (hKt : IsL34Type (↥K ⧸ center ↥K))
    (hH : ⁅H, H⁆ = H) (hHK : H ≤ normalizer (K : Set X)) :
    H ≤ K ⊔ centralizer (K : Set X) := by
  classical
  obtain ⟨ψ⟩ := nonempty_equiv_psl34_of_lieModel hKt
  obtain ⟨eR, -, hinn⟩ := PSL3Four.full_automorphism_action
  let f : MulAut ↥K →* PSL3Four.R :=
    eR.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp inducedHom)
  let N : Subgroup PSL3Four.R := PSL3Four.S.subgroupOf PSL3Four.R
  have : N.Normal := PSL3Four.S_normal
  have hN : Nat.card N = 20160 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe PSL3Four.S_le_R).toEquiv, PSL3Four.card_S]
  have hQ : Nat.card (PSL3Four.R ⧸ N) = 12 := by
    have h := card_eq_card_quotient_mul_card_subgroup N
    rw [PSL3Four.card_R, hN] at h
    omega
  let q : PSL3Four.R →* PSL3Four.R ⧸ N := QuotientGroup.mk' N
  let F : ↥(normalizer (K : Set X)) →* PSL3Four.R ⧸ N :=
    q.comp (f.comp (normalizerMonoidHom K))
  have hH' : Group.IsPerfect ↥(H.subgroupOf (normalizer (K : Set X))) := by
    have : Group.IsPerfect ↥H := isPerfect_iff.mpr hH
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hHK).symm.toMonoidHom)
      (subgroupOfEquivOfLe hHK).symm.surjective
  have himg : (H.subgroupOf (normalizer (K : Set X))).map F = ⊥ := by
    have : Group.IsPerfect ↥((H.subgroupOf (normalizer (K : Set X))).map F) :=
      Group.IsPerfect.map F
    have hcard : Nat.card ↥((H.subgroupOf (normalizer (K : Set X))).map F) ∣ 12 :=
      hQ ▸ card_subgroup_dvd_card _
    have hsol : Group.IsSolvable ↥((H.subgroupOf (normalizer (K : Set X))).map F) := by
      refine LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      have h1 : (Nat.card ↥((H.subgroupOf (normalizer (K : Set X))).map F)).primeFactors ⊆
          (12 : ℕ).primeFactors := Nat.primeFactors_mono hcard (by norm_num)
      have h2 : (12 : ℕ).primeFactors.card = 2 := by
        rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors Nat.prime_two,
          Nat.Prime.primeFactors Nat.prime_three]
        rfl
      exact (Finset.card_le_card h1).trans h2.le
    by_contra hne
    have : Nontrivial ↥((H.subgroupOf (normalizer (K : Set X))).map F) :=
      (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hsol
  intro h hh
  have hhN : h ∈ normalizer (K : Set X) := hHK hh
  have hF1 : F ⟨h, hhN⟩ = 1 := by
    have : F ⟨h, hhN⟩ ∈ (H.subgroupOf (normalizer (K : Set X))).map F :=
      mem_map_of_mem _ (mem_subgroupOf.mpr hh)
    rwa [himg, mem_bot] at this
  have hmemN : f (normalizerMonoidHom K ⟨h, hhN⟩) ∈ N := (QuotientGroup.eq_one_iff _).mp hF1
  have hinner : eR (f (normalizerMonoidHom K ⟨h, hhN⟩)) ∈
      (MulAut.conj : PSL3Four.S →* MulAut PSL3Four.S).range := by
    rw [← hinn]
    exact mem_map_of_mem _ hmemN
  have hf : eR (f (normalizerMonoidHom K ⟨h, hhN⟩)) =
      MulAut.congr ψ (inducedHom (normalizerMonoidHom K ⟨h, hhN⟩)) := by
    simp [f]
  rw [hf] at hinner
  obtain ⟨s, hs⟩ := hinner
  obtain ⟨k, hk⟩ := mem_range_conj_of_inducedHom hK (normalizerMonoidHom K ⟨h, hhN⟩)
    ⟨ψ.symm s, by
      apply (MulAut.congr ψ).injective
      rw [← hs]
      ext x
      simp [MulAut.congr_apply]⟩
  have hc : (k : X)⁻¹ * h ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : X)) hk
    simp only [MulAut.conj_apply, coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe] at h1
    calc x * ((k : X)⁻¹ * h) = (k : X)⁻¹ * ((k : X) * x * (k : X)⁻¹) * h := by group
      _ = (k : X)⁻¹ * (h * x * h⁻¹) * h := by rw [h1]
      _ = (k : X)⁻¹ * h * x := by group
  rw [show h = (k : X) * ((k : X)⁻¹ * h) by group]
  exact mul_mem (mem_sup_left k.2) (mem_sup_right hc)

end CFSG.ComponentClassification.GrSLit.L34Out
