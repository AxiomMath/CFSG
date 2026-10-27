module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420RedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowCount
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem isPGroup_center_pQuot {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (K : Subgroup Q) : IsPGroup p (Subgroup.center (PQuot p K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup hp
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p)

theorem card_center_pQuot_chevTransfer_dvd_mul {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {K I₀ : Subgroup Q} (hIK : I₀ ≤ K)
    (hA : CFSG.Open.IsQuasisimple (PQuot p I₀))
    (hB : Nontrivial (PQuot p (chevTransfer p K I₀))) :
    Nat.card (Subgroup.center (PQuot p I₀)) ∣
      Nat.card (Subgroup.center (PQuot p (chevTransfer p K I₀))) *
        Nat.card (Subgroup.center (PQuot p K)) := by
  set Φ : ↥I₀ →* PQuot p K := (pQuotHom p K).comp (Subgroup.inclusion hIK) with hΦ
  set f0 : ↥I₀ →* PSimple p K := (chevQuotHom p K).comp (Subgroup.inclusion hIK) with hf0
  have hr : chevTransfer p K I₀ = f0.range := chevTransfer_eq_range p hIK
  let f : ↥I₀ →* ↥(chevTransfer p K I₀) :=
    f0.codRestrict _ (fun x => by rw [hr]; exact ⟨x, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : PSimple p K) ∈ f0.range := by rw [← hr]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hker : ∀ x, f x = 1 → Φ x ∈ Subgroup.center (PQuot p K) := by
    intro x hx
    have h1 : f0 x = 1 := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hcop : Nat.Coprime p (Nat.card Φ.ker) := by
    have hle : Φ.ker.map (Subgroup.inclusion hIK) ≤ I₀.subgroupOf K ⊓ (pQuotHom p K).ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    have hmap : Nat.card (Φ.ker.map (Subgroup.inclusion hIK)) = Nat.card Φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIK)
    rw [← hmap]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (coprime_card_inf_ker_pQuotHom hp K _)
  exact card_center_pQuot_dvd_mul hp Φ hcop (isPGroup_center_pQuot hp K) f hf hker hA
    (isPGroup_center_pQuot hp I₀) hB

private theorem modelA_parts {p : ℕ} {Q : Type} [Group Q] [Finite Q] {K I₀ D : Subgroup Q}
    (hM : I1420ModelA p K I₀ D) :
    IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ D ≤ Subgroup.normalizer (K : Set Q) ∧
      CFSG.Open.IsQuasisimple (PQuot p K) ∧ IsCatalogGroup (PSimple p K) ∧
      GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set Q)) I₀ ∧
      ¬ K ≤ I₀ ⊔ GLAPPrimeCoreOf p K ∧
      ∃ a ∈ D, a ≠ 1 ∧ K ≤ Subgroup.centralizer ({a} : Set Q) := by
  obtain ⟨⟨hD, hcard, hN, hq, hc, hI, hnot, -⟩, a, haD, ha1, hKa⟩ := hM
  exact ⟨hD, hcard, hN, hq, hc, hI, hnot, a, haD, ha1, hKa⟩

theorem exists_coreP_of_modelA {p z : ℕ} {P : TauCeti.CFSGIndex → Prop} (hp : p.Prime)
    {Q : Type} [Group Q] [Finite Q] {K I₀ D : Subgroup Q} (hM : I1420ModelA p K I₀ D)
    (hT : S8.IsTypeWithCenter p I₀ P z) :
    CFSG.Open.IsQuasisimple (PQuot p K) ∧ IsCatalogGroup (PSimple p K) ∧
      ∃ (β : MulAut (PSimple p K)) (J : Subgroup (PSimple p K)), I1420CoreP p P z β J ∧
        z ∣ Nat.card (Subgroup.center (PQuot p J)) * Nat.card (Subgroup.center (PQuot p K)) := by
  obtain ⟨hD, hcard, hN, hq, hcat, hI, hnot, a, haD, ha1, hKa⟩ := modelA_parts hM
  obtain ⟨y, hyD, hya⟩ := S8.L89.exists_not_mem_zpowers hp hD hcard haD
  have hDle := S8.L89.le_sup_zpowers hp hD hcard haD ha1 hyD hya
  have hI' : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Q)) I₀ := by
    rw [← inf_centralizer_eq_of_le_sup hyD hKa hDle]; exact hI
  have hy : y ∈ Subgroup.normalizer (K : Set Q) := hN hyD
  have hyp : y ^ p = 1 := hD.2 y hyD
  have hap : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hJne : chevTransfer p K I₀ ≠ ⊤ := chevTransfer_ne_top p hq.1 hnot
  have hJc := glaPComponent_chevTransfer hp hy hap hI'
  haveI : IsSimpleGroup (PSimple p K) := hq.2
  refine ⟨hq, hcat, chevAut p K ⟨y, hy⟩, chevTransfer p K I₀, ?_, ?_⟩
  · unfold I1420CoreP
    refine ⟨hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq,
      chevAut_pow_eq_one p K hy hyp, fun h => ?_, hJne, hJc, ?_, ?_⟩
    · rw [h] at hJc
      exact false_of_glaPComponent_fixSubgroup_one hp hJc hJne
    · obtain ⟨i, hi, ⟨e⟩⟩ := hT.1
      obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hy hap hI'
      exact ⟨i, hi, ⟨g.symm.trans e⟩⟩
    · haveI : Nontrivial (PSimple p (chevTransfer p K I₀)) :=
        (isQuasisimple_pQuot_of_glaPComponent hp hJc).2.toNontrivial
      have hB : Nontrivial (PQuot p (chevTransfer p K I₀)) :=
        (QuotientGroup.mk'_surjective
          (Subgroup.center (PQuot p (chevTransfer p K I₀)))).nontrivial
      have h := card_center_pQuot_chevTransfer_dvd hp (hI.1.trans inf_le_left)
        (isQuasisimple_pQuot_of_glaPComponent hp hI) hB
      rwa [hT.2] at h
  · haveI : Nontrivial (PSimple p (chevTransfer p K I₀)) :=
      (isQuasisimple_pQuot_of_glaPComponent hp hJc).2.toNontrivial
    have hB : Nontrivial (PQuot p (chevTransfer p K I₀)) :=
      (QuotientGroup.mk'_surjective
        (Subgroup.center (PQuot p (chevTransfer p K I₀)))).nontrivial
    have h := card_center_pQuot_chevTransfer_dvd_mul hp (hI.1.trans inf_le_left)
      (isQuasisimple_pQuot_of_glaPComponent hp hI) hB
    rwa [hT.2] at h

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
