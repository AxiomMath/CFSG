module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartOne.KA5L.Chain

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L

section Algebra

@[expose] def cartan5 (i l : Fin 5) : ℤ := Tag.E7.cartan (a5chain i) (a5chain l)

@[expose] def adj5 (i k : Fin 5) : ℤ :=
  ((min i.val k.val : ℕ) + 1 : ℤ) * (5 - (max i.val k.val : ℕ))

theorem adj5_cartan5 : ∀ k l : Fin 5, ∑ i : Fin 5, adj5 i k * cartan5 i l = if k = l then 6 else 0 := by
  decide +kernel

theorem cartan5_adj5 : ∀ i k : Fin 5, ∑ l : Fin 5, cartan5 i l * adj5 k l = if i = k then 6 else 0 := by
  decide +kernel

variable {G : Type*} [CommGroup G]

theorem prod_adj_cartan (x : Fin 5 → G) (l : Fin 5) :
    ∏ i, (∏ k, x k ^ adj5 i k) ^ cartan5 i l = x l ^ 6 := by
  classical
  have h1 : ∀ i, (∏ k, x k ^ adj5 i k) ^ cartan5 i l = ∏ k, x k ^ (adj5 i k * cartan5 i l) := by
    intro i
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun k _ => by rw [← _root_.zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  have h2 : ∀ k, ∏ i, x k ^ (adj5 i k * cartan5 i l) = x k ^ (if k = l then (6 : ℤ) else 0) := by
    intro k
    rw [← zpow_finsetSum, adj5_cartan5]
  simp only [h2]
  rw [Finset.prod_eq_single l]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem prod_cartan_adj (y : Fin 5 → G) (k : Fin 5) :
    ∏ l, (∏ i, y i ^ cartan5 i l) ^ adj5 k l = y k ^ 6 := by
  classical
  have h1 : ∀ l, (∏ i, y i ^ cartan5 i l) ^ adj5 k l = ∏ i, y i ^ (cartan5 i l * adj5 k l) := by
    intro l
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun i _ => by rw [← _root_.zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  have h2 : ∀ i, ∏ l, y i ^ (cartan5 i l * adj5 k l) = y i ^ (if i = k then (6 : ℤ) else 0) := by
    intro i
    rw [← zpow_finsetSum, cartan5_adj5]
  simp only [h2]
  rw [Finset.prod_eq_single k]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ k) h

end Algebra

section Chain

variable {L : Type} [Field L]

@[expose] def chainTuple (a : Fin 5 → Lˣ) : Fin Tag.E7.rank → Lˣ :=
  fun m => ∏ i, a i ^ Tag.E7.cartan (a5chain i) m

@[expose] def chainTorus (L : Type) [Field L] : (Fin 5 → Lˣ) →* ModGL Tag.E7 L where
  toFun a := rootDiagUnit Tag.E7 (chainTuple a)
  map_one' := by
    have : chainTuple (1 : Fin 5 → Lˣ) = 1 := by
      funext m
      simp [chainTuple]
    rw [this]
    exact rootDiagUnit_one
  map_mul' a b := by
    have : chainTuple (a * b) = chainTuple a * chainTuple b := by
      funext m
      simp only [chainTuple, Pi.mul_apply, mul_zpow]
      exact Finset.prod_mul_distrib
    rw [this]
    exact rootDiagUnit_mul _ _

theorem chainTorus_apply (a : Fin 5 → Lˣ) :
    chainTorus L a = rootDiagUnit Tag.E7 (chainTuple a) := rfl

theorem chainTorus_mulSingle (i : Fin 5) (u : Lˣ) :
    chainTorus L (Pi.mulSingle i u) = torusElt Tag.E7 L (a5chain i) u := by
  classical
  rw [chainTorus_apply, torusElt_eq_rootDiagUnit]
  congr 1
  funext m
  simp only [chainTuple]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem mem_chainTorus_iff {g : ModGL Tag.E7 L} :
    g ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ↔
      ∃ a : Fin 5 → Lˣ, chainTorus L a = g := by
  classical
  have hJ : subsystemGroup Tag.E7 L (a5Nodes Tag.E7) ⊓ torusGroup Tag.E7 L =
      supportedTorus Tag.E7 L (a5Nodes Tag.E7) :=
    subsystemGroup_inf_torusGroup_eq_supportedTorus _
  rw [subsystemGroup_eq_rootSpan] at hJ
  have h : torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) =
      supportedTorus Tag.E7 L (a5Nodes Tag.E7) := by rw [inf_comm]; exact hJ
  rw [h, supportedTorus_eq_subsystemTorus]
  constructor
  · intro hg
    have hle : subsystemTorus Tag.E7 L (a5Nodes Tag.E7) ≤ (chainTorus L).range := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, hj, u, rfl⟩
      obtain ⟨i, rfl⟩ := exists_a5chain_of_mem hj
      exact ⟨Pi.mulSingle i u, chainTorus_mulSingle i u⟩
    exact hle hg
  · rintro ⟨a, rfl⟩
    have hmem : ∀ i, chainTorus L (Pi.mulSingle i (a i)) ∈
        subsystemTorus Tag.E7 L (a5Nodes Tag.E7) := fun i => by
      rw [chainTorus_mulSingle]
      exact torusElt_mem_subsystemTorus (a5chain_mem i) _
    have := Finset.prod_induction (fun i => (Pi.mulSingle i (a i) : Fin 5 → Lˣ))
      (fun x : Fin 5 → Lˣ => chainTorus L x ∈ subsystemTorus Tag.E7 L (a5Nodes Tag.E7))
      (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
      (by rw [map_one]; exact one_mem _) (fun i _ => hmem i) (s := Finset.univ)
    rw [Finset.univ_prod_mulSingle] at this
    exact this

theorem rootChar_single_one (b : Fin Tag.E7.rank → Lˣ) (m : Fin Tag.E7.rank) :
    rootChar b (Pi.single m 1) = b m := by
  classical
  simp [rootChar, Pi.single_apply]

theorem rootChar_eq_one_of_support (b : Fin Tag.E7.rank → Lˣ)
    (hb : ∀ l : Fin 5, b (a5chain l) = 1) {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : rootChar b α = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : i ∈ a5Nodes Tag.E7
  · obtain ⟨l, rfl⟩ := exists_a5chain_of_mem hi
    rw [hb l, _root_.one_zpow]
  · rw [hα.2 i hi, zpow_zero]

theorem centralizes_of_chain_eq_one (c : Fin Tag.E7.rank → Lˣ)
    (hc : ∀ l : Fin 5, c (a5chain l) = 1) {q : ModGL Tag.E7 L}
    (hq : q ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))) :
    rootDiagUnit Tag.E7 c * q = q * rootDiagUnit Tag.E7 c := by
  have hle := rootSpan_le_centralizer (K := L) c (S := parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (fun α hα => ⟨hα.1, rootChar_eq_one_of_support c hc hα⟩)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hq)).symm

theorem exists_pow_six_eq_mul [IsAlgClosed L] {t : ModGL Tag.E7 L} (ht : t ∈ torusGroup Tag.E7 L) :
    ∃ z ∈ torusGroup Tag.E7 L,
      (∀ q ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)), z * q = q * z) ∧
      ∃ s ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
        t ^ 6 = z * s := by
  classical
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set x : Fin 5 → Lˣ := fun i => b (a5chain i) with hx
  set a : Fin 5 → Lˣ := fun i => ∏ k, x k ^ adj5 i k with ha
  have hchain : ∀ l : Fin 5, chainTuple a (a5chain l) = b (a5chain l) ^ 6 := by
    intro l
    have := prod_adj_cartan x l
    simpa [chainTuple, ha, cartan5] using this
  set c : Fin Tag.E7.rank → Lˣ := fun m => b m ^ 6 * (chainTuple a m)⁻¹ with hc
  have hc1 : ∀ l : Fin 5, c (a5chain l) = 1 := fun l => by
    simp only [hc, hchain l, mul_inv_cancel]
  refine ⟨rootDiagUnit Tag.E7 c, rootDiagUnit_mem_torusGroup c,
    fun q hq => centralizes_of_chain_eq_one c hc1 hq, chainTorus L a,
    (mem_chainTorus_iff).2 ⟨a, rfl⟩, ?_⟩
  rw [chainTorus_apply, ← rootDiagUnit_mul]
  have : b ^ 6 = c * chainTuple a := by
    funext m
    simp [hc]
  rw [← this]
  exact (map_pow (rootDiagUnitHom Tag.E7 L) b 6).symm

theorem pow_six_eq_one_of_centralizes {f : ModGL Tag.E7 L}
    (hf : f ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)))
    (hc : ∀ q ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)), f * q = q * f) :
    f ^ 6 = 1 := by
  classical
  obtain ⟨a, rfl⟩ := (mem_chainTorus_iff).1 hf
  have hchain : ∀ l : Fin 5, chainTuple a (a5chain l) = 1 := by
    intro l
    set m := a5chain l with hm
    have hroot : Pi.single m (1 : ℤ) ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
      have : m ∈ a5Nodes Tag.E7 := a5chain_mem l
      exact single_mem_parabolicRoots this
    have hX : pinnedX Tag.E7 L (Pi.single m 1) 1 ∈
        rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :=
      pinnedX_mem_rootSpan hroot 1
    have h1 := hc _ hX
    rw [chainTorus_apply] at h1
    have h2 := rootDiagUnit_conj_pinnedX (K := L) (chainTuple a) hroot.1 1
    have h3 : rootDiagUnit Tag.E7 (chainTuple a) * pinnedX Tag.E7 L (Pi.single m 1) 1 *
        (rootDiagUnit Tag.E7 (chainTuple a))⁻¹ = pinnedX Tag.E7 L (Pi.single m 1) 1 := by
      rw [h1]; group
    rw [h3] at h2
    have h4 := pinnedX_injective Tag.E7 L (Pi.single m 1) h2
    rw [rootChar_single_one] at h4
    exact Units.ext (by simpa using h4.symm)
  have hpow : ∀ k : Fin 5, a k ^ 6 = 1 := by
    intro k
    have := prod_cartan_adj a k
    have h1 : ∀ l, (∏ i, a i ^ cartan5 i l) = 1 := fun l => by
      simpa [chainTuple, cartan5] using hchain l
    simp only [h1, _root_.one_zpow, Finset.prod_const_one] at this
    exact this.symm
  have : a ^ 6 = 1 := funext fun k => hpow k
  rw [← map_pow, this, map_one]

end Chain

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
