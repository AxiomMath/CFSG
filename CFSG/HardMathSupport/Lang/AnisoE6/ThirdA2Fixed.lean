module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
public import CFSG.RankThree.E6.NativeTwoA2

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

set_option linter.unusedSectionVars false


section Words

variable (K : Type) [Field K]

theorem nElt_append {τ : Tag} (ω₁ ω₂ : List (Fin τ.rank)) :
    nElt τ K (ω₁ ++ ω₂) = nElt τ K ω₁ * nElt τ K ω₂ := by
  simp [nElt]

theorem nElt_flatten (ωf : List (Fin TwistTag.E6.foldedTag.rank)) :
    nElt TwistTag.E6.tag K (ωf.map TwistTag.E6.orbitWord).flatten =
      (ωf.map fun a => canonicalRep (coxeterSystem TwistTag.E6.tag) K
        (TwistTag.E6.orbitReflection a)).prod := by
  induction ωf with
  | nil => simp [nElt]
  | cons a l ih =>
    rw [List.map_cons, List.flatten_cons, nElt_append, ih, List.map_cons, List.prod_cons,
      canonicalRep_orbitReflection]
    rfl

theorem nElt_omegaWord_mem :
    nElt Tag.E6 K ωWord ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  change nElt TwistTag.E6.tag K (ωFold.map TwistTag.E6.orbitWord).flatten ∈ _
  rw [nElt_flatten]
  refine list_prod_mem fun g hg => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
  exact graphFixedRootGroup_le _ _ _
    (canonicalRep_orbitReflection_mem_graphFixedRootGroup (t := TwistTag.E6) (σ := RingHom.id K) a)

theorem xyUnit_mem_fixed_of_orbitWord_eq (j : Fin Tag.F4.rank) (i : Fin Tag.E6.rank)
    (h : TwistTag.E6.orbitWord (f4FoldedIndex j) = [i]) (c : K) :
    xUnit Tag.E6 K i c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ∧
    yUnit Tag.E6 K i c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  have hx := f4OrbitXUnit_mem (K := K) j c
  have hy := f4OrbitYUnit_mem (K := K) j c
  simp only [f4OrbitXUnit, f4OrbitYUnit, h, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hx hy
  exact ⟨hx, hy⟩

theorem orbitWord_f4_zero : TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) =
    [e6Index 1] := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) =
      [(⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank)] := by decide +kernel
  exact h

theorem orbitWord_f4_one : TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) =
    [e6Index 3] := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) =
      [(⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank)] := by decide +kernel
  exact h

theorem subsystemGroup_fixedNodes_le :
    subsystemGroup Tag.E6 K {e6Index 1, e6Index 3} ≤
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rcases hi with rfl | rfl
    · exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨0, by decide⟩ _ orbitWord_f4_zero c).1
    · exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨1, by decide⟩ _ orbitWord_f4_one c).1
  · rcases hi with rfl | rfl
    · exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨0, by decide⟩ _ orbitWord_f4_zero c).2
    · exact (xyUnit_mem_fixed_of_orbitWord_eq K ⟨1, by decide⟩ _ orbitWord_f4_one c).2

theorem uWord_smul_e0 :
    (coxeterSystem Tag.E6).wordProd uWord • (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Index 1) 1 := by
  simp only [uWord, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul]
  decide +kernel

theorem uWord_smul_e2 :
    (coxeterSystem Tag.E6).wordProd uWord • (Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Index 3) 1 := by
  simp only [uWord, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul]
  decide +kernel

theorem conj_uWord_mem {b : ModGL Tag.E6 K} (hb : b ∈ subsystemGroup Tag.E6 K support13) :
    nElt Tag.E6 K uWord * b * (nElt Tag.E6 K uWord)⁻¹ ∈
      subsystemGroup Tag.E6 K {e6Index 1, e6Index 3} := by
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hy
    · obtain ⟨ε, -, hx⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K uWord
        (isRoot_single Tag.E6 j)
      have ex : nElt Tag.E6 K uWord * xUnit Tag.E6 K j c * (nElt Tag.E6 K uWord)⁻¹ =
          pinnedX Tag.E6 K ((coxeterSystem Tag.E6).wordProd uWord • Pi.single j 1) (ε * c) := by
        rw [← pinnedX_single]
        exact hx c
      rcases (show j = e6Index 0 ∨ j = e6Index 2 from hj) with rfl | rfl
      · rw [ex, uWord_smul_e0, pinnedX_single]
        exact Subgroup.subset_closure ⟨_, Or.inl rfl, _, Or.inl rfl⟩
      · rw [ex, uWord_smul_e2, pinnedX_single]
        exact Subgroup.subset_closure ⟨_, Or.inr rfl, _, Or.inl rfl⟩
    · obtain ⟨ε, -, hy⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K uWord
        (isRoot_neg_single Tag.E6 j)
      have ey : nElt Tag.E6 K uWord * yUnit Tag.E6 K j c * (nElt Tag.E6 K uWord)⁻¹ =
          pinnedX Tag.E6 K (-((coxeterSystem Tag.E6).wordProd uWord • Pi.single j 1)) (ε * c) := by
        rw [← pinnedX_neg_single, ← smul_neg]
        exact hy c
      rcases (show j = e6Index 0 ∨ j = e6Index 2 from hj) with rfl | rfl
      · rw [ey, uWord_smul_e0, pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨_, Or.inl rfl, _, Or.inr rfl⟩
      · rw [ey, uWord_smul_e2, pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨_, Or.inr rfl, _, Or.inr rfl⟩
  | one => simpa using one_mem _
  | mul x y _ _ hx hy =>
    have e : nElt Tag.E6 K uWord * (x * y) * (nElt Tag.E6 K uWord)⁻¹ =
        (nElt Tag.E6 K uWord * x * (nElt Tag.E6 K uWord)⁻¹) *
          (nElt Tag.E6 K uWord * y * (nElt Tag.E6 K uWord)⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : nElt Tag.E6 K uWord * x⁻¹ * (nElt Tag.E6 K uWord)⁻¹ =
        (nElt Tag.E6 K uWord * x * (nElt Tag.E6 K uWord)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem conj_wWord_mem_fixed {b : ModGL Tag.E6 K} (hb : b ∈ subsystemGroup Tag.E6 K support13) :
    nElt Tag.E6 K wWord * b * (nElt Tag.E6 K wWord)⁻¹ ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  have hω := nElt_omegaWord_mem K
  have hu := subsystemGroup_fixedNodes_le K (conj_uWord_mem K hb)
  have e : nElt Tag.E6 K wWord * b * (nElt Tag.E6 K wWord)⁻¹ =
      nElt Tag.E6 K ωWord * (nElt Tag.E6 K uWord * b * (nElt Tag.E6 K uWord)⁻¹) *
        (nElt Tag.E6 K ωWord)⁻¹ := by
    rw [wWord, nElt_append]
    group
  rw [e]
  exact mul_mem (mul_mem hω hu) (inv_mem hω)

end Words

section Base

variable {k K : Type} [Field k] [Field K] (ι : k →+* K)

theorem baseChangeGL_nElt (τ : Tag) (ω : List (Fin τ.rank)) :
    baseChangeGL ι (nElt τ k ω) = nElt τ K ω := by
  induction ω with
  | nil => simp [nElt]
  | cons i l ih =>
    simp only [nElt, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [baseChangeGL_weylElt_one, ih]

theorem baseChangeGL_mem_subsystemGroup {τ : Tag} {J : Set (Fin τ.rank)} {b : ModGL τ k}
    (hb : b ∈ subsystemGroup τ k J) : baseChangeGL ι b ∈ subsystemGroup τ K J := by
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hy
    · rw [baseChangeGL_xUnit]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
    · rw [baseChangeGL_yUnit]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
  | one => simpa using one_mem _
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

theorem natCard_SL3_dvd {p : ℕ} (q : ℕ) (hq : 1 ≤ q) (hp : p ∣ q ^ 2 + q + 1) :
    p ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h3 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    zify [Nat.one_le_pow 3 (m + 1) (by omega)]
    ring
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (h3 ▸ Dvd.dvd.mul_left hp _) _) _

theorem exists_e1 [Finite k] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card k ^ 2 + Nat.card k + 1) :
    ∃ e : ModGL Tag.E6 K,
      e ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) ∧
      orderOf e = p ∧
      ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
        ∀ d : K, Commute e (xUnit Tag.E6 K i d) ∧ Commute e (yUnit Tag.E6 K i d) := by
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  have hcard : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
    have := natCard_SL3_dvd (p := p) (Nat.card k) hq hp
    simpa [Finset.prod_Icc_succ_top, Nat.mul_assoc] using this
  obtain ⟨A₀, hA₀⟩ := exists_prime_orderOf_dvd_card' p hcard
  set b₁ : ModGL Tag.E6 k := (((a2Equiv₁ k).symm A₀ : subsystemGroup Tag.E6 k support13) :
    ModGL Tag.E6 k) with hb₁
  have hb₁mem : b₁ ∈ subsystemGroup Tag.E6 k support13 := ((a2Equiv₁ k).symm A₀).2
  have hord₁ : orderOf b₁ = p := by
    rw [hb₁, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hA₀]
  refine ⟨baseChangeGL ι (nElt Tag.E6 k wWord * b₁ * (nElt Tag.E6 k wWord)⁻¹),
    ⟨_, conj_wWord_mem_fixed k hb₁mem, rfl⟩, ?_, ?_⟩
  · rw [orderOf_injective (baseChangeGL ι) (baseChangeGL_injective ι),
      ← orderOf_injective (MulAut.conj (nElt Tag.E6 k wWord)).toMonoidHom
        (MulAut.conj (nElt Tag.E6 k wWord)).injective b₁] at *
    · exact hord₁
  · intro i hi d
    rw [map_mul, map_mul, map_inv, baseChangeGL_nElt]
    exact commute_conj_support13 K (baseChangeGL_mem_subsystemGroup ι hb₁mem) i hi d

end Base


end CFSG.HardMathSupport.Lang.AnisoE6
