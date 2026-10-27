module

public import CFSG.LieType.Chevalley.WeylSpace
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.Blueprint.ChevalleyRootGroups

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType

private theorem reflect_add
    {τ : Tag} (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    reflect τ i (x + y) = reflect τ i x + reflect τ i y := by
  rw [← reflection_cartan, ← reflection_cartan, ← reflection_cartan, map_add]

theorem exists_weyl_smul_single_of_cartan
    {τ : Tag} {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    ∃ w : WeylGroup τ, w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  have hj : simple τ j • (Pi.single i 1 : Fin τ.rank → ℤ) =
      Pi.single i 1 + Pi.single j 1 := by
    rw [simple_smul, reflect_single, hji, neg_one_smul, sub_neg_eq_add]
  refine ⟨simple τ i * simple τ j, ?_⟩
  calc (simple τ i * simple τ j) • (Pi.single i 1 : Fin τ.rank → ℤ)
      = simple τ i • (simple τ j • (Pi.single i 1 : Fin τ.rank → ℤ)) := mul_smul _ _ _
    _ = simple τ i • (Pi.single i 1 + Pi.single j 1) := by rw [hj]
    _ = reflect τ i (Pi.single i 1 + Pi.single j 1) := by rw [simple_smul]
    _ = reflect τ i (Pi.single i 1) + reflect τ i (Pi.single j 1) := reflect_add i _ _
    _ = Pi.single j 1 := by
      rw [reflect_single, reflect_single, Tag.cartan_self, hij]
      module

private theorem simpleConj_E6
    (i : Fin Tag.E6.rank) :
    ∃ w : WeylGroup Tag.E6, w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (⟨3, by decide⟩ : Fin Tag.E6.rank) 1 := by
  fin_cases i
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨0, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨2, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨2, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w2 * w1, by rw [mul_smul, hw1, hw2]⟩
  · exact exists_weyl_smul_single_of_cartan (i := (⟨1, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · exact exists_weyl_smul_single_of_cartan (i := (⟨2, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · exact ⟨1, one_smul _ _⟩
  · exact exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨5, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨4, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E6.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w2 * w1, by rw [mul_smul, hw1, hw2]⟩

private theorem simpleConj_E7
    (i : Fin Tag.E7.rank) :
    ∃ w : WeylGroup Tag.E7, w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) =
      Pi.single (⟨3, by decide⟩ : Fin Tag.E7.rank) 1 := by
  fin_cases i
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨0, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨2, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨2, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w2 * w1, by rw [mul_smul, hw1, hw2]⟩
  · exact exists_weyl_smul_single_of_cartan (i := (⟨1, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · exact exists_weyl_smul_single_of_cartan (i := (⟨2, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · exact ⟨1, one_smul _ _⟩
  · exact exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨5, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨4, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w2 * w1, by rw [mul_smul, hw1, hw2]⟩
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨6, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨5, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨5, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨4, by decide⟩) (by decide) (by decide)
    obtain ⟨w3, hw3⟩ := exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E7.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w3 * (w2 * w1), by rw [mul_smul, mul_smul, hw1, hw2, hw3]⟩

private theorem simpleConj_E8
    (i : Fin Tag.E8.rank) :
    ∃ w : WeylGroup Tag.E8, w • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) =
      Pi.single (⟨3, by decide⟩ : Fin Tag.E8.rank) 1 := by
  fin_cases i
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨0, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨2, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨2, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w2 * w1, by rw [mul_smul, hw1, hw2]⟩
  · exact exists_weyl_smul_single_of_cartan (i := (⟨1, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · exact exists_weyl_smul_single_of_cartan (i := (⟨2, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · exact ⟨1, one_smul _ _⟩
  · exact exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨5, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨4, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w2 * w1, by rw [mul_smul, hw1, hw2]⟩
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨6, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨5, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨5, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨4, by decide⟩) (by decide) (by decide)
    obtain ⟨w3, hw3⟩ := exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w3 * (w2 * w1), by rw [mul_smul, mul_smul, hw1, hw2, hw3]⟩
  · obtain ⟨w1, hw1⟩ := exists_weyl_smul_single_of_cartan (i := (⟨7, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨6, by decide⟩) (by decide) (by decide)
    obtain ⟨w2, hw2⟩ := exists_weyl_smul_single_of_cartan (i := (⟨6, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨5, by decide⟩) (by decide) (by decide)
    obtain ⟨w3, hw3⟩ := exists_weyl_smul_single_of_cartan (i := (⟨5, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨4, by decide⟩) (by decide) (by decide)
    obtain ⟨w4, hw4⟩ := exists_weyl_smul_single_of_cartan (i := (⟨4, by decide⟩ : Fin Tag.E8.rank))
      (j := ⟨3, by decide⟩) (by decide) (by decide)
    exact ⟨w4 * (w3 * (w2 * w1)),
      by rw [mul_smul, mul_smul, mul_smul, hw1, hw2, hw3, hw4]⟩

private theorem simpleConj_of_conj_to
    {τ : Tag} {t : Fin τ.rank}
    (hconj : ∀ i : Fin τ.rank, ∃ w : WeylGroup τ,
      w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single t 1) :
    ∀ i j : Fin τ.rank, ∃ w : WeylGroup τ,
      w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  intro i j
  obtain ⟨w1, hw1⟩ := hconj i
  obtain ⟨w2, hw2⟩ := hconj j
  exact ⟨w2⁻¹ * w1, by rw [mul_smul, hw1, ← hw2, inv_smul_smul]⟩

private theorem exists_weyl_smul_eq_of_simpleConj
    {τ : Tag}
    (hconj : ∀ i j : Fin τ.rank, ∃ w : WeylGroup τ,
      w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) :
    ∃ w : WeylGroup τ, w • α = β := by
  obtain ⟨wα, i, hα⟩ := isRoot_iff_exists_smul_single.1 hα
  obtain ⟨wβ, j, hβ⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨w, hw⟩ := hconj i j
  refine ⟨wβ * w * wα⁻¹, ?_⟩
  rw [mul_smul, mul_smul, ← hα, inv_smul_smul, hw, hβ]

theorem exists_weyl_smul_eq_of_isRoot {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) :
    ∃ w : WeylGroup τ, w • α = β := by
  rcases hτ with rfl | rfl | rfl
  · exact exists_weyl_smul_eq_of_simpleConj (simpleConj_of_conj_to simpleConj_E6) hα hβ
  · exact exists_weyl_smul_eq_of_simpleConj (simpleConj_of_conj_to simpleConj_E7) hα hβ
  · exact exists_weyl_smul_eq_of_simpleConj (simpleConj_of_conj_to simpleConj_E8) hα hβ

theorem canonicalRep_mem_normalizer_torusPow {τ : Tag}
    (F : Type) [Field F] (p : ℕ)
    (w : WeylGroup τ) :
    (⟨canonicalRep (coxeterSystem τ) F w,
        canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) F w⟩ : ↥(adjointGroup τ F)) ∈
      Subgroup.normalizer
        ((TableBExc.torusPow τ F p : Subgroup ↥(adjointGroup τ F)) :
          Set ↥(adjointGroup τ F)) := by
  set g : ↥(adjointGroup τ F) :=
    ⟨canonicalRep (coxeterSystem τ) F w,
      canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) F w⟩
  have hgN := (canonical_weyl_root_transport τ F).2.2 w
  have hconjpow : ∀ x : ↥(adjointGroup τ F), (g * x * g⁻¹) ^ p = g * x ^ p * g⁻¹ := by
    intro x
    rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hH, hp⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hgN x.1).1 hH, ?_⟩
    rw [hconjpow x, hp, mul_one, mul_inv_cancel]
  · rintro ⟨hH, hp⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hgN x.1).2 hH, ?_⟩
    have hp' : (g * x * g⁻¹) ^ p = 1 := hp
    rw [hconjpow x] at hp'
    have := congrArg (fun y : ↥(adjointGroup τ F) => g⁻¹ * y * g) hp'
    calc x ^ p = g⁻¹ * (g * x ^ p * g⁻¹) * g := by group
      _ = 1 := by simpa using this

theorem rootSubgroup_subgroupOf_le_of_weyl_smul {τ : Tag}
    (F : Type) [Field F] (p : ℕ)
    {X : Subgroup ↥(adjointGroup τ F)}
    (hN : Subgroup.normalizer
        ((TableBExc.torusPow τ F p : Subgroup ↥(adjointGroup τ F)) :
          Set ↥(adjointGroup τ F)) ≤
      Subgroup.normalizer (X : Set ↥(adjointGroup τ F)))
    {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hαX : (rootSubgroup τ F α).subgroupOf (adjointGroup τ F) ≤ X)
    (w : WeylGroup τ) (hw : w • α = γ) :
    (rootSubgroup τ F γ).subgroupOf (adjointGroup τ F) ≤ X := by
  let g : ↥(adjointGroup τ F) :=
    ⟨canonicalRep (coxeterSystem τ) F w,
      canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) F w⟩
  have hgV : g ∈ Subgroup.normalizer
      ((TableBExc.torusPow τ F p : Subgroup ↥(adjointGroup τ F)) :
        Set ↥(adjointGroup τ F)) := canonicalRep_mem_normalizer_torusPow F p w
  have hgX : g ∈ Subgroup.normalizer (X : Set ↥(adjointGroup τ F)) := hN hgV
  have hγmap : rootSubgroup τ F γ =
      (rootSubgroup τ F α).map (MulAut.conj (g : ModGL τ F)).toMonoidHom := by
    rw [← hw, ← (canonical_weyl_root_transport τ F).2.1 w α hα]
  intro y hy
  rw [hγmap] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hxA : x ∈ adjointGroup τ F := rootSubgroup_le_adjointGroup α hx
  let xA : ↥(adjointGroup τ F) := ⟨x, hxA⟩
  have hxX : xA ∈ X := hαX hx
  have hy_eq : g * xA * g⁻¹ = y := Subtype.ext (by simpa [MulAut.conj_apply] using hxy)
  rw [← hy_eq]
  exact (Subgroup.mem_normalizer_iff.mp hgX xA).mp hxX

theorem eq_top_of_rootSubgroup_le {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (F : Type) [Field F]
    (p : ℕ)
    {X : Subgroup ↥(adjointGroup τ F)}
    (hN : Subgroup.normalizer
        ((TableBExc.torusPow τ F p : Subgroup ↥(adjointGroup τ F)) :
          Set ↥(adjointGroup τ F)) ≤
      Subgroup.normalizer (X : Set ↥(adjointGroup τ F)))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hαX : (rootSubgroup τ F α).subgroupOf (adjointGroup τ F) ≤ X) : X = ⊤ := by
  have hroot : ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
      (rootSubgroup τ F β).subgroupOf (adjointGroup τ F) ≤ X := by
    intro β hβ
    obtain ⟨w, hw⟩ := exists_weyl_smul_eq_of_isRoot hτ hα hβ
    exact rootSubgroup_subgroupOf_le_of_weyl_smul F p hN hα hαX w hw
  set S : Set (ModGL τ F) := {g | ∃ (i : Fin τ.rank) (c : F),
    (g : Module.End F (RootModule τ F)) = xOp τ F i c ∨
      (g : Module.End F (RootModule τ F)) = yOp τ F i c}
  have hgen : Subgroup.closure (((↑) : ↥(adjointGroup τ F) → ModGL τ F) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage (k := S)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have hgx : g = ⟨xUnit τ F i c, xUnit_mem_adjointGroup i c⟩ := by
      apply Subtype.ext
      exact Units.ext hg
    rw [hgx]
    exact hroot _ (IsRoot.basis i) (Subgroup.mem_subgroupOf.2 (by
      change xUnit τ F i c ∈ rootSubgroup τ F (Pi.single i 1)
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩))
  · have hgy : g = ⟨yUnit τ F i c, yUnit_mem_adjointGroup i c⟩ := by
      apply Subtype.ext
      exact Units.ext hg
    rw [hgy]
    exact hroot (-Pi.single i 1) (IsRoot.neg (IsRoot.basis i)) (Subgroup.mem_subgroupOf.2 (by
      change yUnit τ F i c ∈ rootSubgroup τ F (-Pi.single i 1)
      rw [← pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩))

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
