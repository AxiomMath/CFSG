module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three3
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open CFSG.LieType.SeitzGeneration.ExcHighThree
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open CFSG.RankThree.PartOne.KE6
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix Pointwise

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {Fr : Ω →+* Ω}

noncomputable def torusDiag : ↥(torusGroup Tag.E6 Ω) →* (Fin Tag.E6.rank → Ωˣ) where
  toFun t := Classical.choose (exists_rootDiagUnit_of_mem_torusGroup t.2)
  map_one' := by
    apply rootDiagUnit_injective
    rw [Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup
      (one_mem (torusGroup Tag.E6 Ω))), rootDiagUnit_one]
  map_mul' x y := by
    apply rootDiagUnit_injective
    have hx := Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup x.2)
    have hy := Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup y.2)
    have hxy := Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup (mul_mem x.2 y.2))
    rw [rootDiagUnit_mul, hxy, hx, hy]

theorem torusDiag_rootDiagUnit (b : Fin Tag.E6.rank → Ωˣ) :
    torusDiag (⟨rootDiagUnit Tag.E6 b, rootDiagUnit_mem_torusGroup b⟩) = b := by
  apply rootDiagUnit_injective
  exact Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup
    (rootDiagUnit_mem_torusGroup b))

noncomputable def torusRootChar (α : Fin Tag.E6.rank → ℤ) :
    ↥(torusGroup Tag.E6 Ω) →* Ωˣ :=
  (rootCharHom (L := Ω) α).comp torusDiag

theorem e6T3W_smul_ne_root {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    e6T3W • α ≠ α ∧ e6T3W • α ≠ -α := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W_eq]
  exact e6T3Matrix_mulVec_ne α (mem_rootFinset.2 hα)

theorem e6T3W_cube : e6T3W ^ 3 = 1 := CFSG.RankThree.Lattice.e6T3_cube

theorem eq_pm_orbit_of_e6T3W_stable {S : Set (Fin Tag.E6.rank → ℤ)}
    (hSroots : ∀ β ∈ S, IsRoot Tag.E6 β)
    (hSneg : ∀ β ∈ S, -β ∈ S)
    (hSu : ∀ β ∈ S, e6T3W • β ∈ S)
    (hScard : S.ncard = 6) {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ S) :
    S = {β | β = α ∨ β = -α ∨ β = e6T3W • α ∨ β = -(e6T3W • α) ∨
      β = e6T3W • (e6T3W • α) ∨ β = -(e6T3W • (e6T3W • α))} := by
  classical
  have hu3 : e6T3W ^ 3 = 1 := e6T3W_cube
  have hαroot : IsRoot Tag.E6 α := hSroots α hα
  have huαroot : IsRoot Tag.E6 (e6T3W • α) := IsRoot.smul hαroot e6T3W
  have h1 : e6T3W • α ≠ α := (e6T3W_smul_ne_root hαroot).1
  have h2 : e6T3W • α ≠ -α := (e6T3W_smul_ne_root hαroot).2
  have h3 : e6T3W • (e6T3W • α) ≠ e6T3W • α := (e6T3W_smul_ne_root huαroot).1
  have h4 : e6T3W • (e6T3W • α) ≠ -(e6T3W • α) := (e6T3W_smul_ne_root huαroot).2
  have hzero : ∀ v : Fin Tag.E6.rank → ℤ, v = -v → v = 0 := by
    intro v hv
    have h2v : (2 : ℤ) • v = 0 := by
      have hv2 : v + v = 0 := by
        nth_rewrite 1 [hv]
        exact neg_add_cancel v
      rwa [two_smul]
    exact (smul_eq_zero.mp h2v).resolve_left (by norm_num)
  have h5 : α ≠ -α := fun h => IsRoot.ne_zero hαroot (hzero α h)
  have hαu : α ≠ e6T3W • α := h1.symm
  have h6 : e6T3W • (e6T3W • α) ≠ α := by
    intro h
    apply h1
    have h' : e6T3W • (e6T3W • (e6T3W • α)) = e6T3W • α := congrArg (fun x => e6T3W • x) h
    have h3' : (e6T3W * e6T3W * e6T3W) • α = α := by
      have hpow : e6T3W * e6T3W * e6T3W = e6T3W ^ 3 := (pow_three' e6T3W).symm
      rw [hpow, hu3, one_smul]
    have h3n : e6T3W • (e6T3W • (e6T3W • α)) = α := by
      simpa only [mul_smul] using h3'
    rw [h3n] at h'
    exact h'.symm
  have h7 : e6T3W • (e6T3W • α) ≠ -α := by
    intro h
    apply h2
    have h' : e6T3W • (e6T3W • (e6T3W • α)) = e6T3W • (-α) := congrArg (fun x => e6T3W • x) h
    have h3' : (e6T3W * e6T3W * e6T3W) • α = α := by
      have hpow : e6T3W * e6T3W * e6T3W = e6T3W ^ 3 := (pow_three' e6T3W).symm
      rw [hpow, hu3, one_smul]
    have h3n : e6T3W • (e6T3W • (e6T3W • α)) = α := by
      simpa only [mul_smul] using h3'
    rw [h3n, smul_neg] at h'
    exact (by simpa using (congrArg Neg.neg h').symm)
  let O : Finset (Fin Tag.E6.rank → ℤ) := {α, e6T3W • α, e6T3W • (e6T3W • α)}
  let N : Finset (Fin Tag.E6.rank → ℤ) :=
    {-α, -(e6T3W • α), -(e6T3W • (e6T3W • α))}
  have hOcard : O.card = 3 := by
    rw [Finset.card_triple_eq_three_iff]
    exact ⟨hαu, h6.symm, h3.symm⟩
  have hNcard : N.card = 3 := by
    rw [Finset.card_triple_eq_three_iff]
    exact ⟨fun h => hαu (neg_injective h),
      fun h => h6 (neg_injective h).symm,
      fun h => h3 (neg_injective h).symm⟩
  have hdisj : Disjoint O N := by
    rw [Finset.disjoint_left]
    intro y hyO hyN
    simp only [O, N, Finset.mem_insert, Finset.mem_singleton] at hyO hyN
    rcases hyO with rfl | rfl | rfl <;> rcases hyN with hy | hy | hy
    · exact h5 hy
    · exact h2 (by simpa using (congrArg Neg.neg hy).symm)
    · exact h7 (by simpa using (congrArg Neg.neg hy).symm)
    · exact h2 hy
    · exact IsRoot.ne_zero huαroot (hzero _ hy)
    · exact h4 (by simpa using (congrArg Neg.neg hy).symm)
    · exact h7 hy
    · exact h4 hy
    · exact IsRoot.ne_zero (IsRoot.smul huαroot e6T3W) (hzero _ hy)
  have hTcard : ((O ∪ N : Finset (Fin Tag.E6.rank → ℤ)) :
      Set (Fin Tag.E6.rank → ℤ)).ncard = 6 := by
    rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj, hOcard, hNcard]
  have hTsub : ((O ∪ N : Finset (Fin Tag.E6.rank → ℤ)) :
      Set (Fin Tag.E6.rank → ℤ)) ⊆ S := by
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, O, N, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact hα
    · exact hSu α hα
    · exact hSu _ (hSu α hα)
    · exact hSneg α hα
    · exact hSneg _ (hSu α hα)
    · exact hSneg _ (hSu _ (hSu α hα))
  have hSfin : S.Finite := Set.finite_of_ncard_ne_zero (by rw [hScard]; norm_num)
  have hle : S.ncard ≤ ((O ∪ N : Finset (Fin Tag.E6.rank → ℤ)) :
      Set (Fin Tag.E6.rank → ℤ)).ncard := by rw [hScard, hTcard]
  have heq : ((O ∪ N : Finset (Fin Tag.E6.rank → ℤ)) :
      Set (Fin Tag.E6.rank → ℤ)) = S :=
    Set.eq_of_subset_of_ncard_le hTsub hle hSfin
  rw [← heq]
  ext β
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, O, N, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ((rfl | rfl | rfl) | (rfl | rfl | rfl))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem stable_subset_rootCharKernel_iff {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {b : Fin Tag.E6.rank → Ωˣ}
    (hbT : rootDiagUnit Tag.E6 b ∈ twistedTorus (phi3N Ω) Fr)
    {S : Set (Fin Tag.E6.rank → ℤ)}
    (hSroots : ∀ β ∈ S, IsRoot Tag.E6 β)
    (hSneg : ∀ β ∈ S, -β ∈ S)
    (hSu : ∀ β ∈ S, e6T3W • β ∈ S)
    (hScard : S.ncard = 6) :
    ∀ (rootv : Fin Tag.E6.rank → ℤ), rootv ∈ S →
      (S ⊆ rootCharKernel b ↔ rootChar b rootv = 1) := by
  intro rootv hrootv
  constructor
  · intro hS
    exact (hS hrootv).2
  · intro hval
    have horbit := eq_pm_orbit_of_e6T3W_stable hSroots hSneg hSu hScard hrootv
    have hpow : ∀ μ : Fin Tag.E6.rank → ℤ,
        rootChar b (e6T3W • μ) = (rootChar b μ) ^ q :=
      fun μ => rootChar_e6T3W_eq_pow hFr hbT rfl μ
    have hneg : ∀ μ : Fin Tag.E6.rank → ℤ,
        rootChar b (-μ) = (rootChar b μ)⁻¹ := fun μ => rootChar_neg' b μ
    intro β hβ
    rw [horbit] at hβ
    rcases hβ with h | h | h | h | h | h
    · rw [h]
      exact ⟨hSroots rootv hrootv, hval⟩
    · rw [h]
      exact ⟨IsRoot.neg (hSroots rootv hrootv), by rw [hneg, hval, inv_one]⟩
    · rw [h]
      exact ⟨IsRoot.smul (hSroots rootv hrootv) e6T3W, by rw [hpow rootv, hval, one_pow]⟩
    · rw [h]
      refine ⟨IsRoot.neg (IsRoot.smul (hSroots rootv hrootv) e6T3W), ?_⟩
      rw [hneg, hpow rootv, hval, one_pow, inv_one]
    · rw [h]
      refine ⟨IsRoot.smul (IsRoot.smul (hSroots rootv hrootv) e6T3W) e6T3W, ?_⟩
      rw [hpow (e6T3W • rootv), hpow rootv, hval, one_pow, one_pow]
    · rw [h]
      refine ⟨IsRoot.neg (IsRoot.smul (IsRoot.smul (hSroots rootv hrootv) e6T3W) e6T3W), ?_⟩
      rw [hneg, hpow (e6T3W • rootv), hpow rootv, hval, one_pow, one_pow, inv_one]

theorem torusRootKernel_eq_rootCharKernel {z : ModGL Tag.E6 Ω}
    (hzT : z ∈ twistedTorus (phi3N Ω) Fr) :
    torusRootKernel z = rootCharKernel (torusDiag ⟨z, (mem_twistedTorus.1 hzT).1⟩) := by
  have hz' : rootDiagUnit Tag.E6 (torusDiag ⟨z, (mem_twistedTorus.1 hzT).1⟩) = z :=
    Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup
      (mem_twistedTorus.1 hzT).1)
  have h1 : torusRootKernel z =
      torusRootKernel (rootDiagUnit Tag.E6 (torusDiag ⟨z, (mem_twistedTorus.1 hzT).1⟩)) := by
    rw [hz']
  rw [h1, torusRootKernel_rootDiagUnit]

theorem stable_subset_torusRootKernel_iff {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {z : ModGL Tag.E6 Ω} (hzT : z ∈ twistedTorus (phi3N Ω) Fr)
    {S : Set (Fin Tag.E6.rank → ℤ)} (α : Fin Tag.E6.rank → ℤ) (hα : α ∈ S)
    (hSroots : ∀ β ∈ S, IsRoot Tag.E6 β)
    (hSneg : ∀ β ∈ S, -β ∈ S)
    (hSu : ∀ β ∈ S, e6T3W • β ∈ S)
    (hScard : S.ncard = 6) :
    S ⊆ torusRootKernel z ↔
      rootChar (torusDiag ⟨z, (mem_twistedTorus.1 hzT).1⟩) α = 1 := by
  rw [torusRootKernel_eq_rootCharKernel hzT]
  refine stable_subset_rootCharKernel_iff hFr ?_ hSroots hSneg hSu hScard α hα
  have hz' : rootDiagUnit Tag.E6 (torusDiag ⟨z, (mem_twistedTorus.1 hzT).1⟩) = z :=
    Classical.choose_spec (exists_rootDiagUnit_of_mem_torusGroup
      (mem_twistedTorus.1 hzT).1)
  rw [hz']
  exact hzT

theorem exists_second_point_of_stable [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hFr : ∀ c, Fr c = c ^ q)
    {A : Subgroup (ModGL Tag.E6 Ω)} (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hAT : A ≤ twistedTorus (phi3N Ω) Fr)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ A) (hx1 : x ≠ 1)
    {S : Set (Fin Tag.E6.rank → ℤ)}
    (hSroots : ∀ β ∈ S, IsRoot Tag.E6 β)
    (hSneg : ∀ β ∈ S, -β ∈ S)
    (hSu : ∀ β ∈ S, e6T3W • β ∈ S)
    (hScard : S.ncard = 6) {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ S) :
    ∃ z ∈ A, z ∉ Subgroup.zpowers x ∧ S ⊆ torusRootKernel z := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  classical
  have hAle : A ≤ torusGroup Tag.E6 Ω := hAT.trans inf_le_left
  let χ : ↥A →* Ωˣ := (torusRootChar α).comp (Subgroup.inclusion hAle)
  have hχval : ∀ z : ↥A, χ z = rootChar (torusDiag ⟨z.1, hAle z.2⟩) α := by
    intro z
    have hz : (Subgroup.inclusion hAle) z = ⟨z.1, hAle z.2⟩ := Subtype.ext rfl
    simp only [χ, MonoidHom.comp_apply, hz, torusRootChar, torusDiag_rootDiagUnit]
    rfl
  have hker : ∀ z : ↥A, χ z = 1 ↔ S ⊆ torusRootKernel z.1 := by
    intro z
    rw [hχval]
    exact (stable_subset_torusRootKernel_iff hFr (hAT z.2) α hα hSroots hSneg hSu hScard).symm
  have hrange : χ.range ≤ rootsOfUnity p Ω := by
    rintro _ ⟨z, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow]
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hA.2 z.1 z.2
    rw [hzp, map_one]
  have hcard_range : Nat.card χ.range ≤ p :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity (R := Ω) (k := p))
  have hcard_ker : p ^ 2 ≤ Nat.card χ.ker := by
    have hmul := Subgroup.card_ker_mul_card_range χ
    have hle : Nat.card χ.ker * Nat.card χ.range ≤ Nat.card χ.ker * p :=
      Nat.mul_le_mul_left _ hcard_range
    rw [hmul, hAcard] at hle
    have hp3 : p ^ 3 = p ^ 2 * p := by ring
    rw [hp3] at hle
    exact Nat.le_of_mul_le_mul_right hle (by positivity)
  have hx' : (⟨x, hx⟩ : ↥A) ≠ 1 := by simpa using hx1
  have horder : orderOf (⟨x, hx⟩ : ↥A) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA.2 x hx) hx1
  have hcard_zp : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : ↥A)) = p := by
    rw [Nat.card_zpowers, horder]
  have hex : ∃ z : ↥A, z ∈ χ.ker ∧ z ∉ Subgroup.zpowers (⟨x, hx⟩ : ↥A) := by
    by_contra h
    push Not at h
    have hle : χ.ker ≤ Subgroup.zpowers (⟨x, hx⟩ : ↥A) := fun z hz => h z hz
    haveI : Finite ↥(Subgroup.zpowers (⟨x, hx⟩ : ↥A)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard_zp]; positivity)
    have hcardle := Subgroup.card_le_of_le hle
    rw [hcard_zp] at hcardle
    have hple : p ^ 2 ≤ p := hcard_ker.trans hcardle
    nlinarith [(Fact.out : p.Prime).two_le]
  obtain ⟨z, hzker, hznot⟩ := hex
  refine ⟨z.1, z.2, ?_, (hker z).1 hzker⟩
  intro hzmem
  apply hznot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
