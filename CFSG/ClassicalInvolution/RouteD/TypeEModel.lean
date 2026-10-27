module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.RouteD.TypeERecog
public import CFSG.ClassicalInvolution.RouteD.Perp
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Blueprint.Chevalley (Tag)

section Edges

theorem edge_data_E {τ : Tag} (h : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : Fin τ.rank}
    (hij : edgeE τ.rank i j) :
    i ≠ j ∧ τ.cartan i j = -1 ∧ τ.cartan j i = -1 ∧
      ∃ k : Fin τ.rank, ¬ (3 : ℤ) ∣ τ.cartan i k + 2 * τ.cartan j k := by
  obtain ⟨h1, h2, h3, h4⟩ := WeakCT.edgeE_orientation h
  obtain ⟨c1, c2⟩ := h2 i j hij
  have hne : i ≠ j := by
    intro e
    subst e
    exact h1 i i hij hij
  obtain ⟨k, hki, hkj, hk⟩ := h4 i j hij
  refine ⟨hne, c1, c2, k, ?_⟩
  rcases hk with ⟨hjk, hik, hki'⟩ | ⟨hik, hjk, hkj'⟩
  · have e1 : τ.cartan i k = 0 := (h3 i k (Ne.symm hki) hik hki').1
    have e2 : τ.cartan j k = -1 := by
      rcases hjk with h' | h'
      · exact (h2 j k h').1
      · exact (h2 k j h').2
    rw [e1, e2]
    norm_num
  · have e1 : τ.cartan j k = 0 := (h3 j k (Ne.symm hkj) hjk hkj').1
    have e2 : τ.cartan i k = -1 := by
      rcases hik with h' | h'
      · exact (h2 i k h').1
      · exact (h2 k i h').2
    rw [e1, e2]
    norm_num

theorem stdPair_edge_E6 {F : Type} [Field F] [Finite F] {i j : Fin 6} (h : edgeE 6 i j) :
    ∃ W, LinearBlockStandardPair F W (rankOne (Steinberg.Minuscule.e6Datum F).rootGroup i)
      (rankOne (Steinberg.Minuscule.e6Datum F).rootGroup j) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Minuscule.e6Datum F).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum F).divisible) rfl
  have hE := Steinberg.Minuscule.e6_chevalleyExtras F O _
    (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC F
      Steinberg.Minuscule.posDef_cartan_E6 _
      (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O)
  have hdiv : (Steinberg.Minuscule.e6Datum F).divisible = ∅ := rfl
  obtain ⟨hne, c1, c2, k, hk⟩ := edge_data_E (τ := .E6) (Or.inl rfl) h
  exact (ModelFacts.standardPair_of_chevalleyExtras hE hdiv (k := k) hne c1 c2 hk).2

theorem stdPair_edge_E7 {F : Type} [Field F] [Finite F] {i j : Fin 7} (h : edgeE 7 i j) :
    ∃ W, LinearBlockStandardPair F W (rankOne (Steinberg.Minuscule.e7Datum F).rootGroup i)
      (rankOne (Steinberg.Minuscule.e7Datum F).rootGroup j) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Minuscule.e7Datum F).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum F).divisible) rfl
  have hE := Steinberg.Minuscule.e7_chevalleyExtras F O _
    (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC F
      Steinberg.Minuscule.posDef_cartan_E7 _
      (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O)
  have hdiv : (Steinberg.Minuscule.e7Datum F).divisible = ∅ := rfl
  obtain ⟨hne, c1, c2, k, hk⟩ := edge_data_E (τ := .E7) (Or.inr (Or.inl rfl)) h
  exact (ModelFacts.standardPair_of_chevalleyExtras hE hdiv (k := k) hne c1 c2 hk).2

theorem stdPair_edge_E8 {F : Type} [Field F] [Finite F] {i j : Fin 8} (h : edgeE 8 i j) :
    ∃ W, LinearBlockStandardPair F W (rankOne (Steinberg.Adjoint.e8Datum F).rootGroup i)
      (rankOne (Steinberg.Adjoint.e8Datum F).rootGroup j) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Adjoint.e8Datum F).isFiniteType
    (Dv := (Steinberg.Adjoint.e8Datum F).divisible) rfl
  have hE := Steinberg.Adjoint.e8_chevalleyExtras F O _
    (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
      Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ F) O)
  have hdiv : (Steinberg.Adjoint.e8Datum F).divisible = ∅ := rfl
  obtain ⟨hne, c1, c2, k, hk⟩ := edge_data_E (τ := .E8) (Or.inr (Or.inr rfl)) h
  exact (ModelFacts.standardPair_of_chevalleyExtras hE hdiv (k := k) hne c1 c2 hk).2

end Edges


section Theta

@[expose] def cartE6 : Matrix (Fin 6) (Fin 6) ℤ := Tag.cartan .E6

@[expose] def cartE7 : Matrix (Fin 7) (Fin 7) ℤ := Tag.cartan .E7

@[expose] def cartE8 : Matrix (Fin 8) (Fin 8) ℤ := Tag.cartan .E8

@[expose] def theta6 : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def theta7 : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]

@[expose] def theta8 : Fin 8 → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem rroot_theta6 : RRoot cartE6 theta6 := by
  have := rroot_chainVec cartE6 0 [2, 3, 1, 4, 3, 2, 5, 4, 3, 1]
  rwa [show chainVec cartE6 0 [2, 3, 1, 4, 3, 2, 5, 4, 3, 1] = theta6 by decide +kernel] at this

theorem rroot_theta7 : RRoot cartE7 theta7 := by
  have := rroot_chainVec cartE7 0 [2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0]
  rwa [show chainVec cartE7 0 [2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0] = theta7 by
    decide +kernel] at this

theorem rroot_theta8 : RRoot cartE8 theta8 := by
  have := rroot_chainVec cartE8 0 [2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1,
    2, 3, 4, 5, 6, 7]
  rwa [show chainVec cartE8 0 [2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1,
    2, 3, 4, 5, 6, 7] = theta8 by decide +kernel] at this

theorem coroot_theta6 : ∀ k : Fin 6, k ≠ 1 → ∑ j, cartE6 k j * theta6 j = 0 := by
  decide +kernel

theorem coroot_theta7 : ∀ k : Fin 7, k ≠ 0 → ∑ j, cartE7 k j * theta7 j = 0 := by
  decide +kernel

theorem coroot_theta8 : ∀ k : Fin 8, k ≠ 7 → ∑ j, cartE8 k j * theta8 j = 0 := by
  decide +kernel

end Theta


section Assemble

variable {t tY : StatedLieTag} {T Y : LieUniversal}

theorem nonempty_extModelU_one (hscT : FundamentalSingleClass t T.D)
    (hscY : FundamentalSingleClass tY Y.D) {R₀T : Subgroup T.K}
    (hR₀T : R₀T ∈ fundamentalSubgroups t T.D) (hpT : R₀T ≤ ⁅R₀T, R₀T⁆) {R₀Y : Subgroup Y.K}
    (hR₀Y : R₀Y ∈ fundamentalSubgroups tY Y.D) (hpY : R₀Y ≤ ⁅R₀Y, R₀Y⁆) {Rθ : Subgroup T.K}
    (hRθ : Rθ ∈ fundamentalSubgroups t T.D) (Θ : Y.K →* T.K) (hker : Θ.ker ≤ Subgroup.center Y.K)
    (hΘ₀ : R₀Y.map Θ ∈ fundamentalSubgroups t T.D) (hcomm : Commutes Θ.range Rθ) :
    Nonempty (ExtModelU t tY T Y 1) := by
  refine ⟨{
    Rθ := Rθ
    twin := fun i => Fin.elim0 i
    Θ := Θ
    Rθ_mem := hRθ
    twin_mem := fun i => Fin.elim0 i
    Θ_ker := hker
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := fun i => Fin.elim0 i
    twin_comm_Θ := fun i => Fin.elim0 i
    twin_inj := fun i => Fin.elim0 i
    perf_T := perfect_of_mem_fundamental hscT hR₀T hpT
    perf_Y := perfect_of_mem_fundamental hscY hR₀Y hpY }⟩
  · intro R hR
    obtain ⟨g, rfl⟩ := hscY R₀Y hR₀Y R hR
    rw [← CFSG.ClassicalInvolution.Generic.conjSub_map]
    exact conjSub_mem_fundamentalSubgroups hΘ₀ (Θ g)
  · intro R hR a ha b hb
    exact hcomm a (Subgroup.map_le_range Θ R ha) b hb

end Assemble


section Simply

variable {K : Type} [Group K] (D : UniversalRootDatum K)

theorem isLongestRoot_of_lenSq {ℓ : ℚ} (hℓ : ∀ γ ∈ D.roots, ModelFacts.lenSq D.isFiniteType γ = ℓ)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    CFSG.ClassicalInvolution.Generic.IsLongestRoot D γ :=
  ⟨hγ, fun δ hδ => by
    have h1 : form D.isFiniteType (toRat δ) (toRat δ) = ℓ := hℓ δ hδ
    have h2 : form D.isFiniteType (toRat γ) (toRat γ) = ℓ := hℓ γ hγ
    rw [h1, h2]⟩

theorem rankOne_mem_fundamental {t : StatedLieTag} {k : Fin D.rank}
    (hk : CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1)) :
    rankOne D.rootGroup k ∈ fundamentalSubgroups t D :=
  ⟨1, Pi.single k 1, Or.inl hk, (CFSG.ClassicalInvolution.Generic.conjSub_one _).symm⟩

theorem fund_of_longest {t : StatedLieTag} {γ : Fin D.rank → ℤ}
    (hγ : CFSG.ClassicalInvolution.Generic.IsLongestRoot D γ) :
    D.rootGroup γ ⊔ D.rootGroup (-γ) ∈ fundamentalSubgroups t D :=
  ⟨1, γ, Or.inl hγ, (CFSG.ClassicalInvolution.Generic.conjSub_one _).symm⟩

theorem commutes_rankOne_theta {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : Steinberg.SteinbergExtras D n H) {ℓ : ℚ} (hℓ : ∀ γ ∈ D.roots, ModelFacts.lenSq D.isFiniteType γ = ℓ)
    {θ : Fin D.rank → ℤ} (hθ : θ ∈ D.roots) {k : Fin D.rank} (hk : coroot D.cartan k θ = 0) :
    Commutes (rankOne D.rootGroup k) (D.rootGroup θ ⊔ D.rootGroup (-θ)) := by
  refine commutes_fund_of_orthogonal D hext hℓ (single_mem_roots D k) hθ ?_
  rw [form_comm]
  exact form_toRat_single_eq_zero D k θ hk

end Simply


section E6

variable {p f : ℕ} [Fact p.Prime]

@[expose] def path6 : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]

theorem path6_comm : ∀ i j : Fin 5, i.val + 1 < j.val → cartE6 (path6 i) (path6 j) = 0 := by
  decide +kernel

theorem path6_edge : ∀ i j : Fin 5, j.val = i.val + 1 → edgeE 6 (path6 i) (path6 j) := by
  decide

theorem path6_ne : ∀ i : Fin 5, path6 i ≠ 1 := by decide

theorem nonempty_extModel_E6 (hadm : StatedLieAdmissible .E6 0 p f) (hq : 4 ≤ p ^ f) :
    Nonempty (ExtModel p f .E6 0 .PSL 6 1) := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hadmY : StatedLieAdmissible .PSL 6 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num,
    by simp, by simp⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E6 0 p f hp trivial hadm
  set D := (modelUniv .E6 0 p f Fact.out).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E6 0 p f hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 6; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta6 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta6
  have hRθ := fund_of_longest (t := .E6) D (isLongestRoot_of_lenSq D hℓ hθ)
  have hlong : ∀ k, CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1) :=
    fun k => isLongestRoot_of_lenSq D hℓ (single_mem_roots D k)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := hK ▸ hq
  obtain ⟨ψ, hψker, hψrange, hψblk⟩ := exists_psi_of_chain (p := p) (f := f) hq (m := 3)
    (by norm_num) (G := (modelUniv .E6 0 p f Fact.out).K)
    (U := fun i => rankOne D.rootGroup (path6 i))
    (fun i j hij => commutes_rankOne_of_cartan_eq_zero D hext hℓ (path6_comm i j hij))
    (fun i j hij => stdPair_edge_E6 (path6_edge i j hij))
  let y0 : Fin (modelUniv .PSL 6 p f Fact.out).D.rank := ⟨0, by show 0 < 5; decide⟩
  obtain ⟨W₀, hW₀⟩ := stdPair_edge_E6 (F := GaloisField p f) (i := 0) (j := 2) (by decide)
  let Θ : (modelUniv .PSL 6 p f Fact.out).K →* (modelUniv .E6 0 p f Fact.out).K := ψ
  have hΘker : Θ.ker ≤ Subgroup.center (modelUniv .PSL 6 p f Fact.out).K := hψker
  have hΘrange : Θ.range = ⨆ i, rankOne D.rootGroup (path6 i) := hψrange
  have hRY : rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup y0 =
      (WeakCT.blockSL2 (GaloisField p f) 5 0).range :=
    WeakCT.rankOne_eq_range (K := GaloisField p f) (n := 5) 0
  have hΘ₀ : (rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup y0).map Θ =
      rankOne D.rootGroup (path6 0) := by
    rw [hRY]
    exact hψblk 0
  refine nonempty_extModelU_one
    (ModelFacts.fundamentalSingleClass .E6 0 p f hp trivial hadm (by decide) (by decide))
    (ModelFacts.fundamentalSingleClass .PSL 6 p f hp trivial hadmY (by decide) (by decide))
    (rankOne_mem_fundamental D (hlong z0))
    (linearBlockStandardPair_perfect h4 hW₀).1
    (R₀Y := rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup y0)
    (rankOne_mem_fundamental _ (ModelFacts.isLongestRoot_single .PSL 6 p f hp trivial hadmY y0 trivial))
    ?_ hRθ Θ hΘker ?_ ?_
  · rw [hRY]
    exact range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4) _
  · rw [hΘ₀]
    exact rankOne_mem_fundamental D (hlong (path6 0))
  · rw [hΘrange]
    refine commutes_iSup_left.mpr fun i => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := path6 i)
      ((coroot_apply D.cartan (path6 i) theta6).trans (coroot_theta6 _ (path6_ne i)))

end E6


section E7

variable {p f : ℕ} [Fact p.Prime]

@[expose] def iota7 : Fin 6 → Fin 7 := ![6, 5, 4, 3, 2, 1]

theorem iota7_comm : ∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i →
    cartE7 (iota7 i) (iota7 j) = 0 := by
  decide +kernel

theorem iota7_edge : ∀ i j : Fin 6, edgeD 6 i j →
    edgeE 7 (iota7 i) (iota7 j) ∨ edgeE 7 (iota7 j) (iota7 i) := by
  decide

theorem iota7_ne : ∀ i : Fin 6, iota7 i ≠ 0 := by decide

theorem stdPair_adj_E7 {F : Type} [Field F] [Finite F] {i j : Fin 7}
    (h : edgeE 7 i j ∨ edgeE 7 j i) :
    ∃ W, LinearBlockStandardPair F W (rankOne (Steinberg.Minuscule.e7Datum F).rootGroup i)
      (rankOne (Steinberg.Minuscule.e7Datum F).rootGroup j) := by
  rcases h with h | h
  · exact stdPair_edge_E7 h
  · obtain ⟨W, hW⟩ := stdPair_edge_E7 (F := F) h
    exact ⟨W, hW.symm⟩

theorem nonempty_extModel_E7 (hadm : StatedLieAdmissible .E7 0 p f) (hq : 4 ≤ p ^ f) :
    Nonempty (ExtModel p f .E7 0 .POmegaPlus 6 1) := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadm
  set D := (modelUniv .E7 0 p f Fact.out).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 7; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta7 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta7
  have hRθ := fund_of_longest (t := .E7) D (isLongestRoot_of_lenSq D hℓ hθ)
  have hlong : ∀ k, CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1) :=
    fun k => isLongestRoot_of_lenSq D hℓ (single_mem_roots D k)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := hK ▸ hq
  obtain ⟨ψ, hψker, hψrange, hψrk⟩ := exists_psi_D6 (p := p) (f := f) hadmY hq
    (X := (modelUniv .E7 0 p f Fact.out).K) (fun i => rankOne D.rootGroup (iota7 i))
    (fun i j hij h1 h2 => commutes_rankOne_of_cartan_eq_zero D hext hℓ (iota7_comm i j hij h1 h2))
    (fun i j h => stdPair_adj_E7 (iota7_edge i j h))
  let y0 : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank := ⟨0, by show 0 < 6; decide⟩
  obtain ⟨W₀, hW₀⟩ := stdPair_edge_E7 (F := GaloisField p f) (i := 0) (j := 2) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField p f)
    (by norm_num : 3 ≤ 6) (by norm_num : 4 ≤ 6)
  let Θ : (modelUniv .POmegaPlus 6 p f Fact.out).K →* (modelUniv .E7 0 p f Fact.out).K := ψ
  have hΘker : Θ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K := hψker
  have hΘrange : Θ.range = ⨆ i, rankOne D.rootGroup (iota7 i) := hψrange
  have hΘ₀ : (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup y0).map Θ =
      rankOne D.rootGroup (iota7 0) := hψrk 0
  refine nonempty_extModelU_one
    (ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadm (by decide) (by decide))
    (ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadmY (by decide) (by decide))
    (rankOne_mem_fundamental D (hlong z0))
    (linearBlockStandardPair_perfect h4 hW₀).1
    (R₀Y := rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup y0)
    (rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadmY y0 trivial))
    (linearBlockStandardPair_perfect h4 hW₁).1 hRθ Θ hΘker ?_ ?_
  · rw [hΘ₀]
    exact rankOne_mem_fundamental D (hlong (iota7 0))
  · rw [hΘrange]
    refine commutes_iSup_left.mpr fun i => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := iota7 i)
      ((coroot_apply D.cartan (iota7 i) theta7).trans (coroot_theta7 _ (iota7_ne i)))

end E7


section E8

variable {p f : ℕ} [Fact p.Prime]

theorem castSucc_comm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
    cartE8 i.castSucc j.castSucc = 0 := by
  decide +kernel

theorem castSucc_edge : ∀ i j : Fin 7, edgeE 7 i j → edgeE 8 i.castSucc j.castSucc := by
  decide

theorem castSucc_ne : ∀ i : Fin 7, i.castSucc ≠ 7 := by decide

theorem nonempty_extModel_E8 (hadm : StatedLieAdmissible .E8 0 p f) (hq : 4 ≤ p ^ f) :
    Nonempty (ExtModel p f .E8 0 .E7 0 1) := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hadmY : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E8 0 p f hp trivial hadm
  set D := (modelUniv .E8 0 p f Fact.out).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E8 0 p f hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 8; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta8 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta8
  have hRθ := fund_of_longest (t := .E8) D (isLongestRoot_of_lenSq D hℓ hθ)
  have hlong : ∀ k, CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1) :=
    fun k => isLongestRoot_of_lenSq D hℓ (single_mem_roots D k)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := hK ▸ hq
  obtain ⟨ψ, hψker, hψrange, hψrk⟩ := exists_psi_E7 (p := p) (f := f) hadmY hq
    (X := (modelUniv .E8 0 p f Fact.out).K) (fun i : Fin 7 => rankOne D.rootGroup i.castSucc)
    (fun i j hij h1 h2 => commutes_rankOne_of_cartan_eq_zero D hext hℓ (castSucc_comm i j hij h1 h2))
    (fun i j h => stdPair_edge_E8 (castSucc_edge i j h))
  let y0 : Fin (modelUniv .E7 0 p f Fact.out).D.rank := ⟨0, by show 0 < 7; decide⟩
  obtain ⟨W₀, hW₀⟩ := stdPair_edge_E8 (F := GaloisField p f) (i := 0) (j := 2) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e7Datum (F := GaloisField p f)
  let Θ : (modelUniv .E7 0 p f Fact.out).K →* (modelUniv .E8 0 p f Fact.out).K := ψ
  have hΘker : Θ.ker ≤ Subgroup.center (modelUniv .E7 0 p f Fact.out).K := hψker
  have hΘrange : Θ.range = ⨆ i : Fin 7, rankOne D.rootGroup i.castSucc := hψrange
  have hΘ₀ : (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup y0).map Θ =
      rankOne D.rootGroup (0 : Fin 7).castSucc := hψrk y0
  refine nonempty_extModelU_one
    (ModelFacts.fundamentalSingleClass .E8 0 p f hp trivial hadm (by decide) (by decide))
    (ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadmY (by decide) (by decide))
    (rankOne_mem_fundamental D (hlong z0))
    (linearBlockStandardPair_perfect h4 hW₀).1
    (R₀Y := rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup y0)
    (rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadmY y0 trivial))
    (linearBlockStandardPair_perfect h4 hW₁).1 hRθ Θ hΘker ?_ ?_
  · rw [hΘ₀]
    exact rankOne_mem_fundamental D (hlong _)
  · rw [hΘrange]
    refine commutes_iSup_left.mpr fun i : Fin 7 => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := i.castSucc)
      ((coroot_apply D.cartan i.castSucc theta8).trans (coroot_theta8 _ (castSucc_ne i)))

end E8

end CFSG.ClassicalInvolution.RouteD
