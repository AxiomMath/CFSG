module

public import CFSG.LieType.SeitzGeneration.RootPairSpBlock
public import CFSG.LieType.SeitzGeneration.RootPairSpConj

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)
open CFSG.ClassicalInvolution.Models.SymplecticPairs renaming gram → symGram

namespace RootPair

section Basis

variable {r : ℕ} {K : Type} [Field K]

theorem spForm_ll (i j : Fin r) :
    spForm r K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) = 0 := by
  simp [spForm_apply, symGram, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.fromBlocks]

theorem spForm_lr (i j : Fin r) :
    spForm r K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) = if i = j then 1 else 0 := by
  simp [spForm_apply, symGram, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.fromBlocks,
    Matrix.one_apply]

theorem spForm_rl (i j : Fin r) :
    spForm r K (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inl j) 1) = if i = j then -1 else 0 := by
  simp [spForm_apply, symGram, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.fromBlocks,
    Matrix.one_apply]
  split_ifs <;> simp

theorem spForm_rr (i j : Fin r) :
    spForm r K (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1) = 0 := by
  simp [spForm_apply, symGram, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.fromBlocks]

@[expose] def dualVec : Fin r ⊕ Fin r → (Fin r ⊕ Fin r → K)
  | Sum.inl a => -Pi.single (Sum.inr a) 1
  | Sum.inr a => Pi.single (Sum.inl a) 1

theorem spForm_dualVec (i : Fin r ⊕ Fin r) (y : Fin r ⊕ Fin r → K) :
    spForm r K (dualVec i) y = y i := by
  cases i with
  | inl a =>
    simp [dualVec, spForm_apply, symGram, Matrix.mulVec, dotProduct, Pi.single_apply,
      Matrix.fromBlocks, Matrix.one_apply]
  | inr a =>
    simp [dualVec, spForm_apply, symGram, Matrix.mulVec, dotProduct, Pi.single_apply,
      Matrix.fromBlocks, Matrix.one_apply]

theorem dualVec_ne_zero (i : Fin r ⊕ Fin r) : (dualVec i : Fin r ⊕ Fin r → K) ≠ 0 := by
  intro h
  have := spForm_dualVec (r := r) (K := K) i (Pi.single i 1)
  rw [h] at this
  simp at this

theorem dualVec_rat {k : Subfield K} (i : Fin r ⊕ Fin r) :
    (dualVec i : Fin r ⊕ Fin r → K) = fun a => ((dualVec i : Fin r ⊕ Fin r → k) a : K) := by
  funext a
  cases i <;> simp [dualVec, Pi.single_apply] <;> split_ifs <;> simp

end Basis

section Closure

variable {r : ℕ} {K : Type} [Field K]

@[expose] def plane (K : Type) [Field K] (i : Fin r) : Submodule K (Fin r ⊕ Fin r → K) :=
  Submodule.span K {Pi.single (Sum.inl i) 1, Pi.single (Sum.inr i) 1}

theorem mem_plane {i : Fin r} {c : Fin r ⊕ Fin r → K} :
    c ∈ plane K i ↔ ∃ x y : K, x • Pi.single (Sum.inl i) 1 + y • Pi.single (Sum.inr i) 1 = c :=
  Submodule.mem_span_pair

theorem inl_mem_plane (i : Fin r) : (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin r → K) ∈ plane K i :=
  Submodule.subset_span (by simp)

theorem inr_mem_plane (i : Fin r) : (Pi.single (Sum.inr i) 1 : Fin r ⊕ Fin r → K) ∈ plane K i :=
  Submodule.subset_span (by simp)

theorem plane_orth {i j : Fin r} (hij : i ≠ j) {u v : Fin r ⊕ Fin r → K} (hu : u ∈ plane K i)
    (hv : v ∈ plane K j) : spForm r K u v = 0 := by
  obtain ⟨x, y, rfl⟩ := mem_plane.mp hu
  obtain ⟨x', y', rfl⟩ := mem_plane.mp hv
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    spForm_ll, spForm_lr, spForm_rl, spForm_rr, hij, ↓reduceIte]
  ring

theorem plane_nondeg (i : Fin r) : ((spForm r K).restrict (plane K i)).Nondegenerate := by
  constructor
  · intro u hu
    obtain ⟨x, y, hxy⟩ := mem_plane.mp u.2
    have h1 := hu ⟨Pi.single (Sum.inr i) 1, inr_mem_plane i⟩
    have h2 := hu ⟨Pi.single (Sum.inl i) 1, inl_mem_plane i⟩
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h1 h2
    rw [← hxy] at h1 h2
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_ll, spForm_lr, spForm_rl, spForm_rr, ↓reduceIte] at h1 h2
    have hx : x = 0 := by linear_combination h1
    have hy : y = 0 := by linear_combination -h2
    apply Subtype.ext
    rw [← hxy, hx, hy]
    simp
  · intro u hu
    obtain ⟨x, y, hxy⟩ := mem_plane.mp u.2
    have h1 := hu ⟨Pi.single (Sum.inr i) 1, inr_mem_plane i⟩
    have h2 := hu ⟨Pi.single (Sum.inl i) 1, inl_mem_plane i⟩
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h1 h2
    rw [← hxy] at h1 h2
    simp only [map_add, map_smul, smul_eq_mul,
      spForm_ll, spForm_lr, spForm_rl, spForm_rr, ↓reduceIte] at h1 h2
    have hx : x = 0 := by linear_combination -h1
    have hy : y = 0 := by linear_combination h2
    apply Subtype.ext
    rw [← hxy, hx, hy]
    simp

theorem iSup_plane : ⨆ i : Fin r, plane K i = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ i : Fin r, (y (Sum.inl i) • Pi.single (Sum.inl i) 1 +
      y (Sum.inr i) • Pi.single (Sum.inr i) 1) := by
    funext a
    cases a <;> simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (inl_mem_plane i))
      (Submodule.smul_mem _ _ (inr_mem_plane i)))

end Closure

section Centers

variable {r : ℕ} {K : Type} [Field K]

@[expose] def ratVec {k : Subfield K} (v₀ : Fin r ⊕ Fin r → k) : Fin r ⊕ Fin r → K :=
  fun a => (v₀ a : K)

theorem transCenter_rat {k : Subfield K} {H : Subgroup (StatedSp r K)} (hsp : spSub r k ≤ H)
    {e₀ : Fin r ⊕ Fin r → k} (he₀ : e₀ ≠ 0) (he : TransCenter H (ratVec e₀))
    {v₀ : Fin r ⊕ Fin r → k} (hv₀ : v₀ ≠ 0) : TransCenter H (ratVec v₀) := by
  obtain ⟨s, hs⟩ := exists_spEnd_eq' he₀ hv₀
  have hmem : subfieldSpHom r k s ∈ H := hsp ⟨s, rfl⟩
  have h1 := he.map hmem
  have h2 : spEnd (subfieldSpHom r k s) (ratVec e₀) = ratVec v₀ := by
    unfold ratVec
    rw [spEnd_subfieldSpHom', hs]
  rwa [h2] at h1

theorem single_one_rat (k : Subfield K) (a : Fin r ⊕ Fin r) :
    (Pi.single a 1 : Fin r ⊕ Fin r → K) = ratVec (Pi.single a 1 : Fin r ⊕ Fin r → k) :=
  (coe_single_one k a).symm

theorem transCenter_plane {k : Subfield K} {H : Subgroup (StatedSp r K)}
    (hrat : ∀ v₀ : Fin r ⊕ Fin r → k, v₀ ≠ 0 → TransCenter H (ratVec v₀)) (i : Fin r)
    {c : Fin r ⊕ Fin r → K} (hc : c ∈ plane K i) : TransCenter H c := by
  obtain ⟨x, y, rfl⟩ := mem_plane.mp hc
  have hl : TransCenter H (Pi.single (Sum.inl i) 1) := by
    rw [single_one_rat k]
    exact hrat _ (by
      intro h
      have := congrFun h (Sum.inl i)
      simp at this)
  have hr : TransCenter H (Pi.single (Sum.inr i) 1) := by
    rw [single_one_rat k]
    exact hrat _ (by
      intro h
      have := congrFun h (Sum.inr i)
      simp at this)
  by_cases hx : x = 0
  · rw [hx, zero_smul, zero_add]
    exact hr.smul y
  by_cases hy : y = 0
  · rw [hy, zero_smul, add_zero]
    exact hl.smul x
  refine (hl.smul x).add (hr.smul y) ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, spForm_lr, ↓reduceIte, mul_one]
  first | exact mul_ne_zero hx hy | exact mul_ne_zero hy hx

theorem transCenter_pair' {k : Subfield K} {H : Subgroup (StatedSp r K)}
    (hrat : ∀ v₀ : Fin r ⊕ Fin r → k, v₀ ≠ 0 → TransCenter H (ratVec v₀)) {i j : Fin r}
    (hij : i ≠ j) {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ plane K i) (hy' : y' ∈ plane K j)
    (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) : TransCenter H (y + y') := by
  have hbl : ∀ l : Fin r, (Pi.single (Sum.inl l) 1 : Fin r ⊕ Fin r → K) ≠ 0 := fun l h => by
    have := congrFun h (Sum.inl l)
    simp at this
  obtain ⟨g₁, hg₁, hg₁y, hg₁z⟩ := exists_mem_fixing_eq (plane_nondeg i)
    (fun c hc => transCenter_plane hrat i hc) (inl_mem_plane i) hy (hbl i) hy0
  obtain ⟨g₂, hg₂, hg₂y, hg₂z⟩ := exists_mem_fixing_eq (plane_nondeg j)
    (fun c hc => transCenter_plane hrat j hc) (inl_mem_plane j) hy' (hbl j) hy'0
  have hv : TransCenter H (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1) := by
    have hne : (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1 : Fin r ⊕ Fin r → k) ≠ 0 :=
      fun h => by
        have := congrFun h (Sum.inl i)
        simp [hij] at this
    have hrv : ratVec (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1 :
        Fin r ⊕ Fin r → k) = (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1 :
          Fin r ⊕ Fin r → K) := by
      funext a
      simp [ratVec, Pi.single_apply]
      split_ifs <;> simp
    rw [← hrv]
    exact hrat _ hne
  have h2 := (hv.map hg₂)
  rw [map_add, hg₂y, hg₂z _ (fun c hc => plane_orth hij (inl_mem_plane i) hc)] at h2
  have h1 := h2.map hg₁
  rw [map_add, hg₁y, hg₁z _ (fun c hc => plane_orth hij.symm hy' hc)] at h1
  exact h1

theorem eq_top_of_rat_centers {k : Subfield K} {H : Subgroup (StatedSp r K)}
    (hrat : ∀ v₀ : Fin r ⊕ Fin r → k, v₀ ≠ 0 → TransCenter H (ratVec v₀)) : H = ⊤ :=
  eq_top_of_transCenter (transCenter_of_pairs (Vs := plane K) iSup_plane
    (fun _ _ hij _ hu _ hv => plane_orth hij hu hv) plane_nondeg
    (fun i _ hc => transCenter_plane hrat i hc)
    (fun _ _ hij _ hy _ hy' hy0 hy'0 => transCenter_pair' hrat hij hy hy' hy0 hy'0))

end Centers

section Main

variable {r : ℕ} {K : Type} [Field K] [Finite K] [NeZero r]

theorem transCenter_dual {k : Subfield K} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k) (A : gsp r K)
    {H : Subgroup (StatedSp r K)} (hsp : spSub r k ≤ H)
    (hmap : (spSub r k).map (conjSp r K A).toMonoidHom ≤ H) {i j : Fin r ⊕ Fin r}
    (hij : (((multiplier r K A)⁻¹ : Kˣ) : K) *
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j) ^ 2 ∉ k) :
    TransCenter H (dualVec i) := by
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := ((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set μi : K := (((multiplier r K A)⁻¹ : Kˣ) : K) with hμi
  set β : K := Am i j with hβdef
  set e : Fin r ⊕ Fin r → K := dualVec i with hedef
  set w' : Fin r ⊕ Fin r → K := Am *ᵥ Pi.single j 1 with hw'
  have hβ : spForm r K e w' = β := by
    rw [hedef, spForm_dualVec, hw', hβdef, Matrix.mulVec_single_one]
    rfl
  have hβ0 : β ≠ 0 := fun h => hij (by rw [h]; simp)
  set f : Fin r ⊕ Fin r → K := β⁻¹ • w' with hfdef
  have hef : spForm r K e f = 1 := by
    rw [hfdef, map_smul, hβ, smul_eq_mul, inv_mul_cancel₀ hβ0]
  have he_rat : e = ratVec (dualVec i : Fin r ⊕ Fin r → k) := dualVec_rat i
  have hj_rat : (Pi.single j 1 : Fin r ⊕ Fin r → K) =
      ratVec (Pi.single j 1 : Fin r ⊕ Fin r → k) := single_one_rat k j
  have hu : ∀ t ∈ k, u2 (t * (-1)) ∈ (H.comap (spSL2Hom hef)) := by
    intro t ht
    show spSL2Hom hef (u2 (t * (-1))) ∈ H
    rw [spSL2Hom_u2]
    have h1 : -(t * -1) = t := by ring
    rw [h1, he_rat]
    have h2 := subfieldSpHom_spTransvection k (dualVec i : Fin r ⊕ Fin r → k) ⟨t, ht⟩
    exact hsp ⟨_, h2⟩
  have hl : ∀ s ∈ k, l2 (s * (μi * β ^ 2)) ∈ (H.comap (spSL2Hom hef)) := by
    intro s hs
    show spSL2Hom hef (l2 (s * (μi * β ^ 2))) ∈ H
    rw [spSL2Hom_l2, hfdef, spTransvection_smul]
    have h1 : β⁻¹ * β⁻¹ * (s * (μi * β ^ 2)) = μi * s := by
      field_simp
    rw [h1]
    have h2 : conjSp r K A (spTransvection (Pi.single j 1) s) = spTransvection w' (μi * s) := by
      rw [conjSp_spTransvection]
    rw [← h2, hj_rat]
    have h3 := subfieldSpHom_spTransvection k (Pi.single j 1 : Fin r ⊕ Fin r → k) ⟨s, hs⟩
    exact hmap ⟨_, ⟨_, h3⟩, rfl⟩
  have hαβ : (-1 : K) * (μi * β ^ 2) ∉ k := by
    intro h
    apply hij
    have := k.neg_mem h
    simpa using this
  have hM := sl2_eq_top_of_root_pair hp hp2 hK hk3 hαβ hu hl
  intro t
  have h1 : u2 (-t) ∈ (H.comap (spSL2Hom hef)) := by rw [hM]; trivial
  have h2 : spSL2Hom hef (u2 (-t)) ∈ H := h1
  rw [spSL2Hom_u2, neg_neg] at h2
  exact h2

end Main

end RootPair

theorem subfieldPairSp_of_three_le {K : Type} [Field K] [Finite K]
    (k : Subfield K) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k) {r : ℕ} (hr : 2 ≤ r)
    (A : gsp r K) (hne : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k) :
    Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
      ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤ := by
  have : NeZero r := ⟨by omega⟩
  set H : Subgroup (StatedSp r K) := Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
      ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) with hH
  have hsp : spSub r k ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hmap : (spSub r k).map (conjSp r K A).toMonoidHom ≤ H :=
    fun x hx => Subgroup.subset_closure (Or.inr hx)
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin r ⊕ Fin r, (((multiplier r K A)⁻¹ : Kˣ) : K) *
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j) ^ 2 ∉ k := by
    by_contra hall
    push Not at hall
    have hle := RootPair.conj_spSub_le hp hp2 hK A hall
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (conjSp r K A).injective]
  have hd := RootPair.transCenter_dual hp hp2 hK hk3 A hsp hmap hij
  have hd0 : (RootPair.dualVec i : Fin r ⊕ Fin r → k) ≠ 0 := RootPair.dualVec_ne_zero i
  have hrat : ∀ v₀ : Fin r ⊕ Fin r → k, v₀ ≠ 0 → TransCenter H (RootPair.ratVec v₀) := by
    intro v₀ hv₀
    refine RootPair.transCenter_rat hsp hd0 ?_ hv₀
    have h1 : RootPair.ratVec (RootPair.dualVec i : Fin r ⊕ Fin r → k) = RootPair.dualVec i :=
      (RootPair.dualVec_rat i).symm
    rw [h1]
    exact hd
  exact RootPair.eq_top_of_rat_centers hrat

end CFSG.LieType.SeitzGeneration
