module

public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups
open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Universal.Spin CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups
  FundamentalSingleClass IsLongestRoot modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair exists_ctFamily_of_pairs
  exists_recognition torusHom torusHom_injective rankOne_eq_range)

theorem weakCT_recognition_nodes (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hq : 4 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : SL(n + 1, K) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧
      ∀ i, (rankOne (SpecialLinear.rootGroup n K) i).map ψ = U i := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs hK4 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.WeakCT.exists_unit_ne_one (by omega : 3 ≤ Nat.card K)
    refine ⟨⟨0, by omega⟩, torusHom K s, fun h => hs ?_⟩
    apply torusHom_injective
    rw [map_one]
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, hψ, hsurj, hker, -, -, -⟩ := exists_recognition hn hp hf hK F hgen' hnt
  refine ⟨ψ, hsurj, hker, fun i => ?_⟩
  rw [rankOne_eq_range, MonoidHom.range_eq_map, Subgroup.map_map, ← (hF i).1,
    MonoidHom.range_eq_map]
  congr 1
  exact MonoidHom.ext (hψ i)

@[expose] def nodeA3 : Fin 3 → Fin 5 := ![3, 2, 4]

theorem exists_theta_sl4_plusDatum {p f : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ p ^ f) :
    ∃ Θ : SL(4, F) →* spinGroup (quadPlus 5 F),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin 3, (rankOne (SpecialLinear.rootGroup 3 F) k).map Θ =
        rankOne (plusDatum 5 F (by omega)).rootGroup (nodeA3 k)) ∧
      Θ.range = ⨆ k : Fin 3, rankOne (plusDatum 5 F (by omega)).rootGroup (nodeA3 k) := by
  have hn3 : 3 ≤ 5 := by omega
  set L : Fin 3 → Subgroup (spinGroup (quadPlus 5 F)) := fun k =>
    rankOne (plusDatum 5 F hn3).rootGroup (nodeA3 k) with hL
  set X : Subgroup (spinGroup (quadPlus 5 F)) := ⨆ k, L k with hX
  have hLle : ∀ k, L k ≤ X := fun k => le_iSup L k
  have h34 : cartanD 5 (3 : Fin 5) 4 = 0 := by
    refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1 <;> decide
  obtain ⟨Ψ, hsurj, hker, hnodes⟩ := weakCT_recognition_nodes F p f hp hF hq (n := 3) (by omega)
    (X := ↥X) (U := fun k => (L k).subgroupOf X)
    (fun i j hij x hx y hy => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exact Subtype.ext (commutes_rankOne_plusDatum hn3 h34 x.1 (Subgroup.mem_subgroupOf.mp hx)
        y.1 (Subgroup.mem_subgroupOf.mp hy)))
    (fun i j hij => by
      have hpair : ∃ W, LinearBlockStandardPair F W (L i) (L j) := by
        fin_cases i <;> fin_cases j <;> simp at hij
        · have hedge : edgeD 5 (2 : Fin 5) 3 := by unfold edgeD; decide
          obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 hedge
          exact ⟨W, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW⟩
        · have hedge : edgeD 5 (2 : Fin 5) 4 := by unfold edgeD; decide
          exact standardPair_plusDatum_edge (F := F) hn3 hedge
      obtain ⟨W, hW⟩ := hpair
      have hWle : W ≤ X := (linearBlockStandardPair_le_sup hW).trans (sup_le (hLle i) (hLle j))
      exact ⟨W.subgroupOf X,
        CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf hWle hW⟩)
    (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self L)
  refine ⟨X.subtype.comp Ψ, ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · intro k
    rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hLle k)]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

theorem nonempty_extModelU_D5 {p f : ℕ} [hp : Fact p.Prime]
    (hscT : FundamentalSingleClass .POmegaPlus (plusDatum 5 (GaloisField p f) (by omega)))
    (hscY : FundamentalSingleClass .PSL (SpecialLinear.rootDatum 3 (GaloisField p f)))
    (hlong : ∀ k : Fin 3,
      IsLongestRoot (SpecialLinear.rootDatum 3 (GaloisField p f)) (Pi.single k 1))
    (hq : 4 ≤ p ^ f) :
    Nonempty (ExtModelU .POmegaPlus .PSL
      ⟨spinGroup (quadPlus 5 (GaloisField p f)), plusDatum 5 (GaloisField p f) (by omega)⟩
      ⟨SL(4, GaloisField p f), SpecialLinear.rootDatum 3 (GaloisField p f)⟩ 2) := by
  have hn3 : 3 ≤ 5 := by omega
  set F := GaloisField p f with hFdef
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hF : Nat.card F = p ^ f := GaloisField.card p f hf
  have hq' : 4 ≤ Nat.card F := hF ▸ hq
  obtain ⟨Θ, hker, hnode, hrange⟩ :=
    exists_theta_sl4_plusDatum (p := p) (f := f) (F := F) hp.out hF hq
  set DT := plusDatum 5 F hn3 with hDT
  set DY := SpecialLinear.rootDatum 3 F with hDY
  set X : Subgroup (spinGroup (quadPlus 5 F)) :=
    ⨆ k : Fin 3, rankOne DT.rootGroup (nodeA3 k) with hX
  have hcommX0 : ∀ k : Fin 3,
      Commutes (rankOne DT.rootGroup (0 : Fin 5)) (rankOne DT.rootGroup (nodeA3 k)) := by
    intro k
    refine commutes_rankOne_plusDatum hn3 ?_
    refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1
    · fin_cases k <;> decide
    · fin_cases k <;> decide
    · fin_cases k <;> decide
  have hcommXθ : Commutes X (rootθD 5 F hn3) := by
    refine commutes_iSup_left.mpr fun k => ?_
    exact (commutes_rootθD_rankOne hn3 (by omega) (k := nodeA3 k)
      (by fin_cases k <;> decide)).symm
  have hcommX0' : Commutes X (rankOne DT.rootGroup (0 : Fin 5)) :=
    commutes_iSup_left.mpr fun k => (hcommX0 k).symm
  have himg : ∀ R ∈ fundamentalSubgroups .PSL DY, ∃ g : SL(4, F),
      R.map Θ = conjSub (Θ g) (rankOne DT.rootGroup (nodeA3 0)) := by
    intro R hR
    obtain ⟨g, hg⟩ := hscY (rankOne DY.rootGroup (0 : Fin 3))
      (rankOne_mem_fundamental DY (hlong 0)) R hR
    refine ⟨g, ?_⟩
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map]
    exact congrArg _ (hnode 0)
  have hperfY : ∀ R ∈ fundamentalSubgroups .PSL DY, R ≤ ⁅R, R⁆ := by
    obtain ⟨W₁, hW₁⟩ := CFSG.ClassicalInvolution.ModelFacts.standardPair_specialLinear F 3
      (by norm_num)
    exact perfect_of_mem_fundamental hscY (rankOne_mem_fundamental DY (hlong 0))
      (linearBlockStandardPair_perfect hq' hW₁).1
  refine ⟨{
    Rθ := rootθD 5 F hn3
    twin := fun _ => rankOne DT.rootGroup (0 : Fin 5)
    Θ := Θ
    Rθ_mem := rootθD_mem_fundamentalSubgroups hn3 (by omega)
    twin_mem := fun _ => rankOne_mem_fundamentalSubgroups_plusDatum hn3 _
    Θ_ker := hker
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := ?_
    twin_comm_Θ := ?_
    twin_inj := fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)
    perf_T := ?_
    perf_Y := hperfY }⟩
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    exact conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 : conjSub (Θ g) (rootθD 5 F hn3) = rootθD 5 F hn3 :=
      CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommXθ
    have h2 : Commutes (rankOne DT.rootGroup (nodeA3 0)) (rootθD 5 F hn3) :=
      (commutes_rootθD_rankOne hn3 (by omega) (k := nodeA3 0) (by decide)).symm
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · intro i
    exact (commutes_rootθD_rankOne hn3 (by omega) (k := (0 : Fin 5)) (by decide)).symm
  · intro i R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2 := hcommX0 0
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · have h01 : edgeD 5 (0 : Fin 5) (1 : Fin 5) := by unfold edgeD; decide
    obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 h01
    exact perfect_of_mem_fundamental hscT
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (0 : Fin 5))
      (linearBlockStandardPair_perfect hq' hW).1

variable {p f : ℕ} [hp : Fact p.Prime]

theorem modelUniv_PSL_eq {m : ℕ} :
    modelUniv .PSL (m + 1) p f hp.out =
      ⟨SL(m + 1, GaloisField p f), SpecialLinear.rootDatum m (GaloisField p f)⟩ := by
  simp only [modelUniv, lieUniversal]

theorem nonempty_extModel_D5 (hq : 4 ≤ p ^ f) : Nonempty (ExtModel p f .POmegaPlus 5 .PSL 4 2) := by
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf
  have hn3 : 3 ≤ 5 := by omega
  have hadmT : StatedLieAdmissible .POmegaPlus 5 p f := ⟨hp.out, hf1, by show 4 ≤ 5; omega⟩
  have hadmY : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, hf1, by show 2 ≤ 4; omega, fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have e1 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have e2 : modelUniv .PSL 4 p f hp.out =
      ⟨SL(4, GaloisField p f), SpecialLinear.rootDatum 3 (GaloisField p f)⟩ :=
    modelUniv_PSL_eq (m := 3)
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 5 p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus 5 p f hp.out trivial
      hadmT (by decide) (by decide)
  have hscY : FundamentalSingleClass .PSL (modelUniv .PSL 4 p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSL 4 p f hp.out trivial hadmY
      (by decide) (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 5 (GaloisField p f) hn3) := by
    revert hscT; rw [e1]; exact id
  have hscY' : FundamentalSingleClass .PSL (SpecialLinear.rootDatum 3 (GaloisField p f)) := by
    revert hscY; rw [e2]; exact id
  have hlong : ∀ k : Fin 3,
      IsLongestRoot (SpecialLinear.rootDatum 3 (GaloisField p f)) (Pi.single k 1) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .PSL 4 p f hp.out trivial
      hadmY
    exact fun k => h k trivial
  show Nonempty (ExtModelU .POmegaPlus .PSL (modelUniv .POmegaPlus 5 p f hp.out)
    (modelUniv .PSL 4 p f hp.out) 2)
  rw [e1, e2]
  exact nonempty_extModelU_D5 hscT' hscY' hlong hq

theorem yData_A3 (hq : 4 ≤ p ^ f) : YData p f .PSL 4 := by
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, hf1, by show 2 ≤ 4; omega, fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  obtain ⟨M⟩ := nonempty_extModel_D5 (p := p) (f := f) hq
  have hsc : FundamentalSingleClass .PSL (modelUniv .PSL 4 p f Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSL 4 p f hp.out trivial hadm
      (by decide) (by decide)
  obtain ⟨W₁, hW₁⟩ := CFSG.ClassicalInvolution.ModelFacts.standardPair_specialLinear
    (GaloisField p f) 3 (by norm_num)
  have hl := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .PSL 4 p f hp.out trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .PSL) (modelUniv .PSL 4 p f Fact.out).D
    (k := ⟨0, by show 0 < 3; decide⟩) (hl ⟨0, by show 0 < 3; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .PSL) (modelUniv .PSL 4 p f Fact.out).D
    (k := ⟨1, by show 1 < 3; decide⟩) (hl ⟨1, by show 1 < 3; decide⟩ trivial)
  exact ⟨by decide, hsc, perfectK_of_admissible hp.out trivial hadm, M.perf_Y,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁⟩

end CFSG.ClassicalInvolution.RouteD
