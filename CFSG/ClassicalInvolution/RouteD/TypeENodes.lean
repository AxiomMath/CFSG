module

public import CFSG.ClassicalInvolution.RouteD.TypeELocal
public import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Standard
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.RouteD.TypeEModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem oddCoverSL3_of_five_le (hq : 5 ≤ p ^ f) : OddCoverSL3 (GaloisField p f) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf)
    hq

section YData

theorem central_of_stdPair {t : StatedLieTag} {Y : LieUniversal}
    (hsc : FundamentalSingleClass t Y.D) {R₀ R₀' W : Subgroup Y.K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t Y.D)
    (hW : LinearBlockStandardPair (GaloisField p f) W R₀ R₀') :
    ∀ R ∈ fundamentalSubgroups t Y.D, ∀ r ∈ R, r ∈ Subgroup.center Y.K → r = 1 := by
  intro R hR r hr hrc
  obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
  exact (eq_one_of_mem_center_of_stdPair
    (ModelFacts.linearBlockStandardPair_map_conj hW g)).1 r hr hrc

theorem std_of_stdPair {t : StatedLieTag} {Y : LieUniversal}
    (hsc : FundamentalSingleClass t Y.D) {R₀ R₀' W : Subgroup Y.K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t Y.D) (hR₀' : R₀' ∈ fundamentalSubgroups t Y.D)
    (hW : LinearBlockStandardPair (GaloisField p f) W R₀ R₀') :
    ∀ R ∈ fundamentalSubgroups t Y.D, ∃ R' ∈ fundamentalSubgroups t Y.D, ∃ W' : Subgroup Y.K,
      LinearBlockStandardPair (GaloisField p f) W' R R' := by
  intro R hR
  obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
  exact ⟨conjSub g R₀', conjSub_mem_fundamentalSubgroups hR₀' g, _,
    ModelFacts.linearBlockStandardPair_map_conj hW g⟩

theorem perfectK_of_admissible {t : StatedLieTag} {n : ℕ} (hp : p.Prime)
    (hfund : ModelFacts.IsFundTag t) (hadm : StatedLieAdmissible t n p f) :
    Group.IsPerfect (modelUniv t n p f Fact.out).K :=
  ⟨(ModelFacts.modelClauseZero t n p f hp hfund hadm).1.1⟩

theorem yData_D6 (hadm : StatedLieAdmissible .POmegaPlus 6 p f) (hq : 4 ≤ p ^ f) :
    YData p f .POmegaPlus 6 := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hadmT : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  obtain ⟨M⟩ := nonempty_extModel_E7 hadmT hq
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField p f)
    (by norm_num : 3 ≤ 6) (by norm_num : 4 ≤ 6)
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .POmegaPlus) (modelUniv .POmegaPlus 6 p f Fact.out).D
    (k := ⟨0, by show 0 < 6; decide⟩) (hl ⟨0, by show 0 < 6; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .POmegaPlus) (modelUniv .POmegaPlus 6 p f Fact.out).D
    (k := ⟨1, by show 1 < 6; decide⟩) (hl ⟨1, by show 1 < 6; decide⟩ trivial)
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm, M.perf_Y,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁⟩

theorem yData_E7 (hadm : StatedLieAdmissible .E7 0 p f) (hq : 4 ≤ p ^ f) : YData p f .E7 0 := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hadmT : StatedLieAdmissible .E8 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  obtain ⟨M⟩ := nonempty_extModel_E8 hadmT hq
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e7Datum (F := GaloisField p f)
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .E7) (modelUniv .E7 0 p f Fact.out).D
    (k := ⟨0, by show 0 < 7; decide⟩) (hl ⟨0, by show 0 < 7; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .E7) (modelUniv .E7 0 p f Fact.out).D
    (k := ⟨2, by show 2 < 7; decide⟩) (hl ⟨2, by show 2 < 7; decide⟩ trivial)
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm, M.perf_Y,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁⟩

theorem yData_A5 (hadm : StatedLieAdmissible .PSL 6 p f) (hq : 4 ≤ p ^ f) : YData p f .PSL 6 := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hadmT : StatedLieAdmissible .E6 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  obtain ⟨M⟩ := nonempty_extModel_E6 hadmT hq
  have hsc : FundamentalSingleClass .PSL (modelUniv .PSL 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .PSL 6 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨W₁, hW₁⟩ := ModelFacts.standardPair_specialLinear (GaloisField p f) 5 (by norm_num)
  have hl := ModelFacts.isLongestRoot_single .PSL 6 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .PSL) (modelUniv .PSL 6 p f Fact.out).D
    (k := ⟨0, by show 0 < 5; decide⟩) (hl ⟨0, by show 0 < 5; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .PSL) (modelUniv .PSL 6 p f Fact.out).D
    (k := ⟨1, by show 1 < 5; decide⟩) (hl ⟨1, by show 1 < 5; decide⟩ trivial)
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm, M.perf_Y,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁⟩

end YData


section NodeSystems

variable {G : Type} [Group G]

structure NodeSystem (p f : ℕ) [Fact p.Prime] {r : ℕ} (adj : Fin r → Fin r → Prop)
    (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) (j : Fin r → Subgroup G) : Prop where
  mem : ∀ a, j a ∈ centralizingMembers Ω {z}
  ne_K : ∀ a, j a ≠ K
  commK : ∀ a, Commutes K (j a)
  comm : ∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (j a) (j b)
  pair : ∀ a b, adj a b →
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} [Finite G]

theorem ETCtx.exists_nodeSystem_D6 (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hadm : StatedLieAdmissible .POmegaPlus 6 p f) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadm
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 6)
    (fun a => rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeD 6)
    (fun a b hab h1 h2 => commutes_rankOne_plusDatum (n := 6) (K := GaloisField p f)
      (by norm_num) (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1)
    (fun a b h => standardPair_plusDatum_edge (F := GaloisField p f) (by norm_num) h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩⟩

theorem ETCtx.exists_nodeSystem_E7 (c : ETCtx p f .E7 0 Ω K z)
    (hadm : StatedLieAdmissible .E7 0 p f) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadm
  have hdiv : (modelUniv .E7 0 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E7 0 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 7; decide⟩
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 7)
    (fun a => rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeE 7)
    (fun a b hab h1 h2 => commutes_rankOne_of_cartan_eq_zero _ hext hℓ
      ((WeakCT.edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))).2.2.1 a b hab h1 h2).1)
    (fun a b h => stdPair_edge_E7 h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩⟩

theorem stdPair_specialLinear_edge (F : Type) [Field F] (m : ℕ) {i j : Fin m}
    (h : j.val = i.val + 1) :
    ∃ W, LinearBlockStandardPair F W (rankOne (SpecialLinear.rootGroup m F) i)
      (rankOne (SpecialLinear.rootGroup m F) j) := by
  rw [WeakCT.rankOne_eq_range, WeakCT.rankOne_eq_range]
  exact ⟨_, (WeakCT.weakCTSystem_standard (K := F) m).pair i j h⟩

theorem ETCtx.exists_nodeSystem_A5 (c : ETCtx p f .PSL 6 Ω K z)
    (hadm : StatedLieAdmissible .PSL 6 p f) :
    ∃ j : Fin 5 → Subgroup G, NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z j := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .PSL 6 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .PSL 6 p f hp trivial hadm
  have hdiv : (modelUniv .PSL 6 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .PSL 6 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 5; decide⟩
  have hA : ∀ a b : Fin 5, a ≠ b → ¬ b.val = a.val + 1 → ¬ a.val = b.val + 1 →
      CartanMatrix.A 5 a b = 0 := by
    intro a b hab h1 h2
    simp only [CartanMatrix.A, Matrix.of_apply]
    split_ifs
    all_goals first | rfl | omega
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 5)
    (fun a => rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (fun a b : Fin 5 => b.val = a.val + 1)
    (fun a b hab h1 h2 => commutes_rankOne_of_cartan_eq_zero _ hext hℓ (hA a b hab h1 h2))
    (fun a b h => stdPair_specialLinear_edge (GaloisField p f) 5 h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩⟩

end NodeSystems

end CFSG.ClassicalInvolution.RouteD
