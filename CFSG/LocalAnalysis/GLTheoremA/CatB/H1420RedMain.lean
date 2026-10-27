module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420RedCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420RedKL
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma88

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem inf_centralizer_eq_of_le_sup {Q : Type} [Group Q] {K D : Subgroup Q} {a y : Q}
    (hy : y ∈ D) (hKa : K ≤ Subgroup.centralizer ({a} : Set Q))
    (hD : D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers y) :
    K ⊓ Subgroup.centralizer (D : Set Q) = K ⊓ Subgroup.centralizer ({y} : Set Q) := by
  refine le_antisymm
    (inf_le_inf_left K (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hy))) ?_
  rintro k ⟨hk, hky⟩
  refine ⟨hk, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
  have hka := Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  have hky' := Subgroup.mem_centralizer_singleton_iff.1 hky
  have h1 : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({k} : Set Q) :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hka.symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hky'.symm))
  exact Subgroup.mem_centralizer_singleton_iff.1 (h1 (hD hd))

theorem chevTransfer_eq_range {Q : Type} [Group Q] [Finite Q] (p : ℕ) {K I₀ : Subgroup Q}
    (hIK : I₀ ≤ K) :
    chevTransfer p K I₀ = ((chevQuotHom p K).comp (Subgroup.inclusion hIK)).range := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem exists_surjective_chevTransfer {Q : Type} [Group Q] [Finite Q] (p : ℕ)
    {K I₀ : Subgroup Q} (hIK : I₀ ≤ K) :
    ∃ f : ↥I₀ →* ↥(chevTransfer p K I₀), Function.Surjective f := by
  have hr := chevTransfer_eq_range p hIK
  set φ := (chevQuotHom p K).comp (Subgroup.inclusion hIK) with hφ
  refine ⟨φ.codRestrict _ fun x => by rw [hr]; exact ⟨x, rfl⟩, fun y => ?_⟩
  have hy : (y : PSimple p K) ∈ φ.range := by rw [← hr]; exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem card_center_pQuot_chevTransfer_dvd {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {K I₀ : Subgroup Q} (hIK : I₀ ≤ K) (hA : CFSG.Open.IsQuasisimple (PQuot p I₀))
    (hB : Nontrivial (PQuot p (chevTransfer p K I₀))) :
    Nat.card (Subgroup.center (PQuot p (chevTransfer p K I₀))) ∣
      Nat.card (Subgroup.center (PQuot p I₀)) := by
  obtain ⟨f, hf⟩ := exists_surjective_chevTransfer p hIK
  exact card_center_pQuot_dvd hp f hf hA hB

theorem exists_core_of_modelA {p z : ℕ} {s : TauCeti.SporadicName} (hp : p.Prime) {Q : Type}
    [Group Q] [Finite Q] {K I₀ D : Subgroup Q} (hM : I1420ModelA p K I₀ D)
    (hT : S8.IsTypeWithCenter p I₀ (S8.sporIs s) z) :
    ∃ (β : MulAut (PSimple p K)) (J : Subgroup (PSimple p K)), I1420Core p z s β J := by
  obtain ⟨⟨hD, hcard, hN, hq, -, hI, hnot, -⟩, a, haD, ha1, hKa⟩ := hM
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
  refine ⟨chevAut p K ⟨y, hy⟩, chevTransfer p K I₀, ?_⟩
  unfold I1420Core
  refine ⟨hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq,
    chevAut_pow_eq_one p K hy hyp, fun h => ?_, hJne, hJc, ?_, ?_⟩
  · rw [h] at hJc
    exact false_of_glaPComponent_fixSubgroup_one hp hJc hJne
  · obtain ⟨i, hi, ⟨e⟩⟩ := hT.1
    obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hy hap hI'
    obtain rfl : i = .sporadic s := hi
    exact ⟨g.symm.trans e⟩
  · haveI : Nontrivial (PSimple p (chevTransfer p K I₀)) :=
      (isQuasisimple_pQuot_of_glaPComponent hp hJc).2.toNontrivial
    have hB : Nontrivial (PQuot p (chevTransfer p K I₀)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p (chevTransfer p K I₀)))).nontrivial
    have h := card_center_pQuot_chevTransfer_dvd hp (hI.1.trans inf_le_left)
      (isQuasisimple_pQuot_of_glaPComponent hp hI) hB
    rwa [hT.2] at h

theorem i1420Red_holds : I1420Red := by
  intro p z s ht Q _ _ K I₀ D hM hT
  have hp : p.Prime := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  exact exists_core_of_modelA hp hM hT

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
