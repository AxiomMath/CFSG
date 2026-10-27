module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117
public import CFSG.LocalAnalysis.GLTheoremA.S11.LabelFacts
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.CentTransfer
public import CFSG.Goldschmidt.Steps.G55Basic
public import CFSG.Goldschmidt.Steps.AxB
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Inputs114 (G : Type) [Group G] [Finite G] : Prop extends Inputs111 G where
  i166 : I166At G
  labUniq : LabelUniqAt G
  eTable : ETableAt G
  i61 : I61At G
  i1441 : I1441At G
  i14neg : I14NegAt G
  i1416 : I1416Chev2At G
  i142 : I142At G
  sch : CFSG.AGLEmbedding.KFactCatalogSchreier
  i25 : Input2_5
  rank3 : RankThreeLabelAt G
  ys08 : YS08
  u64types : U64TypesAt G
  u5rank : U5RankAt
  u5out : U5OutAt G
  u6struct : U6StructAt G
  u5case : U5CaseAt G
  u6case : U6CaseAt G
  centq : CentQuasiAt G

structure Succ11 (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (p' : ℕ)
    (B' : Subgroup G) (x' : G) (L' J : Subgroup G) : Prop where
  R : RQuad G m p B x L
  R' : RQuad G m p' B' x' L'
  cfg : Cfg116 G m p L p' B' x' J
  c117 : Concl117 G p p' B' x' x J L'
  field : ∀ lab' labJ : GLALabel, LabelOf L' lab' → LabelOf J labJ → FieldRel p (canonLabel lab') (canonLabel labJ)

section Lemma119Inn

open CFSG.Assembly

private theorem lemma119_innSet_gen {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι K)) (S : Set (GL ι K)) (hS : ∀ h ∈ H, h ∈ S) :
    LargeEvenInnSet (LargeEvenProj H) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S := by
  rintro _ ⟨r, rfl⟩
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective r
  refine ⟨(h₀ : GL ι K), hS _ h₀.2, fun h h' hh' => ?_⟩
  show (h₀ : LargeEvenProj H) * (h : LargeEvenProj H) * (h₀ : LargeEvenProj H)⁻¹ =
    (h' : LargeEvenProj H)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (by rw [hh']; rfl)

private theorem lemma119_innSet_sl {K : Type} [Field K] {d : ℕ} :
    LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ :=
  lemma119_innSet_gen _ _ (fun _ _ => Set.mem_univ _)

private theorem lemma119_sp_form {K : Type} [Field K] {m : ℕ} {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ LargeEvenSpGroup K m) :
    Matrix.transpose (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * LargeEvenSpForm K m *
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = LargeEvenSpForm K m := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    calc Matrix.transpose ((x * y : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
          ((x * y : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)
        = Matrix.transpose (y : Matrix _ _ K) *
            (Matrix.transpose (x : Matrix _ _ K) * LargeEvenSpForm K m * (x : Matrix _ _ K)) *
              (y : Matrix _ _ K) := by
          rw [Units.val_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Matrix.transpose ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
          ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)
        = Matrix.transpose ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *
            (Matrix.transpose (x : Matrix _ _ K) * LargeEvenSpForm K m * (x : Matrix _ _ K)) *
              ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) := by rw [hx]
      _ = Matrix.transpose ((x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)) *
            LargeEvenSpForm K m *
              ((x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

private theorem lemma119_innSet_sp {K : Type} [Field K] {m : ℕ} (H : Subgroup (GL (Fin m ⊕ Fin m) K))
    (hH : H ≤ LargeEvenSpGroup K m) :
    LargeEvenInnSet (LargeEvenProj H) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGSpSet K m) :=
  lemma119_innSet_gen H _ (fun h hh => ⟨1, one_ne_zero, by
    rw [one_smul]; exact lemma119_sp_form (hH hh)⟩)

private theorem lemma119_su_mem_gu {K : Type} [Field K] [CharP K 2] {d n : ℕ} {g : GL (Fin d) K}
    (hg : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) : g ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  have hmap : ∀ M : Matrix (Fin d) (Fin d) K,
      M.map (fun x => x ^ 2 ^ n) = M.map (iterateFrobenius K 2 n) := fun M => rfl
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, hid⟩ := hx
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    rw [one_smul]
    exact hid
  | one =>
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    simp
  | mul x y _ _ hx hy =>
    obtain ⟨μx, hμx0, hμx1, hμx⟩ := hx
    obtain ⟨μy, hμy0, hμy1, hμy⟩ := hy
    refine ⟨μx * μy, mul_ne_zero hμx0 hμy0, by rw [mul_pow, hμx1, hμy1], ?_⟩
    rw [hmap] at hμx hμy ⊢
    simp only [Units.val_mul]
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          (Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((x : Matrix (Fin d) (Fin d) K) * (y : Matrix (Fin d) (Fin d) K))
        = (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
            (x : Matrix (Fin d) (Fin d) K)) * (y : Matrix (Fin d) (Fin d) K) := by
          simp only [Matrix.mul_assoc]
      _ = (μx * μy) • (1 : Matrix (Fin d) (Fin d) K) := by
          rw [hμx, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hμy, smul_smul]
  | inv x _ hx =>
    obtain ⟨μ, hμ0, hμ1, hX⟩ := hx
    rw [hmap] at hX
    have hXZ : (x : Matrix (Fin d) (Fin d) K) * ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hXfZf : Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n) *
        Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n) = 1 := by
      rw [← Matrix.map_mul, hXZ, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = 1 := by
      rw [← Matrix.transpose_mul, hXfZf, Matrix.transpose_one]
    have h2 : μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = (x : Matrix (Fin d) (Fin d) K) := by
      calc μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose
          = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (μ • (1 : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * ((Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (x : Matrix (Fin d) (Fin d) K)) := by rw [hX]
        _ = ((Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose) * (x : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc]
        _ = (x : Matrix (Fin d) (Fin d) K) := by rw [h1, Matrix.one_mul]
    have h3 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = μ⁻¹ • (x : Matrix (Fin d) (Fin d) K) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμ1], ?_⟩
    rw [hmap]
    rw [h3, Matrix.smul_mul, hXZ]

private theorem lemma119_su_mem_gu_closure {K : Type} [Field K] [CharP K 2] {d n : ℕ} :
    ∀ g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n), g ∈ LargeEvenGUSet (Fin d) K (2 ^ n) :=
  fun _ hg => lemma119_su_mem_gu hg

private theorem lemma119_innSet_su {K : Type} [Field K] [CharP K 2] {d n : ℕ} (H : Subgroup (GL (Fin d) K))
    (hH : H ≤ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    LargeEvenInnSet (LargeEvenProj H) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin d) K (2 ^ n)) :=
  lemma119_innSet_gen H _ (fun h hh => lemma119_su_mem_gu (hH hh))

private theorem lemma119_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = (2 ^ n) ^ 2) :
    CharP K 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hc⟩ := CharP.exists K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have hcard : Fintype.card K = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, h, ← pow_mul, mul_comm]
  have hdvd : p ∣ 2 ^ (2 * n) := by
    rw [← hcard, hk]
    exact dvd_pow_self p (PNat.ne_zero k)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc

private theorem lemma119_recipeLinear_inn {d N : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_gen _ _ (fun _ _ => Set.mem_univ _)⟩⟩

private theorem lemma119_recipeUnitary_inn {d n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  have hc : CharP K 2 := lemma119_charP_two hK
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_su _ le_rfl⟩⟩

private theorem lemma119_recipeSymplectic_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m q false Q) :
    LargeEvenRecipeSymplectic m q false fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_sp _ le_rfl⟩⟩

private theorem lemma119_recipeSymplecticDer_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m q true Q) :
    LargeEvenRecipeSymplectic m q true fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  have hder : ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ ≤ LargeEvenSpGroup K m :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (LargeEvenSpGroup K m).mul_mem ((LargeEvenSpGroup K m).mul_mem
        ((LargeEvenSpGroup K m).mul_mem ha hb) ((LargeEvenSpGroup K m).inv_mem ha))
        ((LargeEvenSpGroup K m).inv_mem hb)
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_sp _ hder⟩⟩

private theorem lemma119_chevID_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
    (H : Subgroup (LargeEvenChevGL A K)) :
    LargeEvenInnSet (LargeEvenCenterQuot H) ⊆ LargeEvenChevIDImage A K H :=
  fun _ hφ => Subgroup.subset_closure (Set.mem_union_left _ hφ)

private theorem lemma119_parentID_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
    (P H : Subgroup (LargeEvenChevGL A K)) :
    LargeEvenInnSet (LargeEvenCenterQuot H) ⊆ LargeEvenChevParentIDImage A K P H :=
  fun φ hφ => Subgroup.subset_closure (Set.mem_union_left _ (lemma119_chevID_inn H hφ))

private theorem lemma119_recipeOmegaPlus_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, subset_rfl⟩⟩

private theorem lemma119_recipeOmegaMinus_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, b, c, hbc, ⟨hQ, subset_rfl⟩⟩

private theorem lemma119_recipeChevalley_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ}
    {derived : Bool} {Q : LargeEvenRawCont} (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_chevID_inn _⟩⟩

private theorem lemma119_recipeTwisted_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {ρ : Equiv.Perm (Fin r)} {m n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_chevID_inn _⟩⟩

private theorem lemma119_recipeSuzuki_inn {a : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, subset_rfl⟩⟩

private theorem lemma119_recipeTwF4_inn {a : ℕ} {Q : LargeEvenRawCont} (h : LargeEvenRecipeTwF4 a Q) :
    LargeEvenRecipeTwF4 a fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_chevID_inn _⟩⟩

private theorem lemma119_recipeTwF4Inh_inn {a : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeTwF4Inherited a Q) :
    LargeEvenRecipeTwF4Inherited a fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  refine ⟨K, hF, hfin, hK, ⟨hQ, ?_⟩⟩
  split_ifs
  · exact lemma119_parentID_inn _ _
  · exact lemma119_chevID_inn _

private theorem lemma119_recipeG2Der_inn {Q : LargeEvenRawCont} (h : LargeEvenRecipeG2Derived Q) :
    LargeEvenRecipeG2Derived fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_parentID_inn _ _⟩⟩

private theorem lemma119_rawDatum_inn (lab : LargeEvenLabel) (Q : LargeEvenRawCont)
    (h : LargeEvenRawDatum lab Q) :
    LargeEvenRawDatum lab (fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I) := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  · exact lemma119_recipeLinear_inn h
  · exact lemma119_recipeUnitary_inn h
  · exact lemma119_recipeSymplectic_inn h
  · exact lemma119_recipeSymplectic_inn h
  · split_ifs at h ⊢
    · exact lemma119_recipeLinear_inn h
    · exact lemma119_recipeOmegaPlus_inn h
  · split_ifs at h ⊢
    · exact lemma119_recipeLinear_inn h
    · exact lemma119_recipeUnitary_inn h
    · exact lemma119_recipeOmegaMinus_inn h
  · exact lemma119_recipeChevalley_inn h
  · exact lemma119_recipeChevalley_inn h
  · exact lemma119_recipeChevalley_inn h
  · exact lemma119_recipeChevalley_inn h
  · exact lemma119_recipeTwisted_inn h
  · exact lemma119_recipeTwisted_inn h
  · exact lemma119_recipeChevalley_inn h
  · exact lemma119_recipeSuzuki_inn h
  · exact lemma119_recipeTwF4Inh_inn h
  · exact lemma119_recipeSymplecticDer_inn h
  · exact lemma119_recipeG2Der_inn h
  · exact lemma119_recipeTwF4Inh_inn h


end Lemma119Inn

namespace S11

variable {G : Type} [Group G] [Finite G] {m p p' : ℕ} {B B' : Subgroup G} {x x' : G} {L L' J : Subgroup G}

theorem le_normalizer_of_innerDiag {B L : Subgroup G} (h : InnerDiagMarking B L) : B ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, -, R, _, I, F, θ, -, -, hBN, -⟩ := CFSG.StandardType.Canonical.largeEvenMarking_exists h
  exact hBN

theorem bstar_norm (hc : Cfg116 G m p L p' B' x' J) {L'' : Subgroup G}
    (hL' : GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) L'') (hJL : J ≤ L'')
    (huniq : ∀ Y : Subgroup G, GLAPComponent p' (Subgroup.centralizer ({x'} : Set G)) Y → J ≤ Y → Y = L'') :
    B' ≤ Subgroup.normalizer (L'' : Set G) := by
  intro b hb
  refine x_mem_normalizer ?_ (le_normalizer_of_innerDiag hc.cfg.idiag hb) hL' hJL huniq
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact isElemAbelian_commute hc.cfg.elem hb hc.cfg.mem

theorem exists_label_of_isChev2 {K : Subgroup G} (h : IsChev2 K) : ∃ lab : GLALabel, LabelOf K lab := by
  obtain ⟨hK, lab, hlab, hraw⟩ := h
  refine ⟨lab, hK, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, -⟩
  exact ⟨hs, hna, θ, rfl⟩

theorem p'_ne_p (hH : Hyp111 G m p B x L) (hns : NoSplit16 p L) (hc : Cfg116 G m p L p' B' x' J) : p ≠ p' := by
  obtain ⟨lab, hlab⟩ := exists_label_of_isChev2 hH.isChev2
  intro h
  exact hns lab hlab (h ▸ hc.splits lab hlab)

theorem chev_of_cfg (hctx : ThmACtx G m) (hsf : StageFacts G m) (h1416 : I1416Chev2At G) (hR : RQuad G m p B x L)
    (hns : NoSplit16 p L) (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L') :
    IsChevSimple 2 (PSimple p' L') := by
  have hH := rquad_hyp hsf hR
  have hp : p.Prime := hH.prime
  have hp' : p'.Prime := hc.cfg.prime
  obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf p' hc.mu
  have hc6 : S6Ctx G p' := S6Ctx.of_ctx hctx hc.mu h3 h4o h4 h5
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) := kGroup_centralizer hc6 hc.cfg.ne_one
  have h6 : 6 ≤ twoRank ↥J := by
    have := hc.cfg.m2
    have := hctx.1.four_le
    have := hc.e_eq
    omega
  exact h1416 p p' (Subgroup.centralizer ({x'} : Set G)) L' J x hp hH.ne_two hp' hc.cfg.odd (p'_ne_p hH hns hc) hKX
    hc117.comp' hc117.comp_p hc117.x_norm (hH.elem.2 x hH.mem) hc117.J_layer.2 hc.cfg.chev2 hc.cfg.comp.1.2.2
    hc.cfg.odd_center h6

theorem lemma118 (hctx : ThmACtx G m) (hsf : StageFacts G m) (h1416 : I1416Chev2At G) (h142 : I142At G) (hR : RQuad G m p B x L)
    (hns : NoSplit16 p L) (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L') : IsGB p' B' L' := by
  have hp' : p'.Prime := hc.cfg.prime
  have hnorm : B' ≤ Subgroup.normalizer (L' : Set G) := bstar_norm hc hc117.comp' hc117.J_le hc117.uniq
  obtain ⟨E, hEB, hEel, hEcard, hx'E, hlay⟩ := hc.cfg.e3
  obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf p' hc.mu
  have hc6 : S6Ctx G p' := S6Ctx.of_ctx hctx hc.mu h3 h4o h4 h5
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) := kGroup_centralizer hc6 hc.cfg.ne_one
  have hchev := chev_of_cfg hctx hsf h1416 hR hns hc hc117
  refine ⟨E, hEB, hEel, hEcard, hEB.trans hnorm, ?_⟩
  exact h142 p' (Subgroup.centralizer ({x'} : Set G)) L' E (J ⊓ Subgroup.centralizer (E : Set G)) hp' hc.cfg.odd hKX
    hc117.comp' hchev hEel (hEB.trans hnorm) (inf_le_inf_right _ hc117.J_le) hlay

theorem isGStar_of_isGB {p : ℕ} {B L : Subgroup G} (hG : IsGB p B L) (hn : B ≤ Subgroup.normalizer (L : Set G)) :
    IsGStar p B L := by
  obtain ⟨E, hEB, hE, hEc, -, hlay⟩ := hG
  refine ⟨E, hEB, hE, hEc, ?_⟩
  rw [closureIn_eq_self hn]
  exact hlay

private theorem lemma119_mem_sup {G : Type} [Group G] {J : Subgroup G} {x : G}
    (hx : ∀ j ∈ J, j * x = x * j) {a : G} (ha : a ∈ J ⊔ Subgroup.zpowers x) :
    ∃ j ∈ J, ∃ k : ℤ, a = j * x ^ k := by
  let T : Subgroup G :=
    { carrier := {a | ∃ j ∈ J, ∃ k : ℤ, a = j * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨j1, hj1, k1, rfl⟩ ⟨j2, hj2, k2, rfl⟩
        have hc : x ^ k1 * j2 = j2 * x ^ k1 :=
          ((show Commute j2 x from hx j2 hj2).zpow_right k1).eq.symm
        refine ⟨j1 * j2, J.mul_mem hj1 hj2, k1 + k2, ?_⟩
        calc j1 * x ^ k1 * (j2 * x ^ k2) = j1 * (x ^ k1 * j2) * x ^ k2 := by group
          _ = j1 * (j2 * x ^ k1) * x ^ k2 := by rw [hc]
          _ = j1 * j2 * x ^ (k1 + k2) := by rw [zpow_add]; group
      one_mem' := ⟨1, J.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨j, hj, k, rfl⟩
        refine ⟨j⁻¹, J.inv_mem hj, -k, ?_⟩
        have hc0 : Commute (x ^ k) j⁻¹ :=
          ((((show Commute j x from hx j hj).inv_left).zpow_right k)).symm
        rw [mul_inv_rev, zpow_neg, hc0.inv_left.eq] }
  have hxT : x ∈ T := ⟨1, J.one_mem, 1, by simp⟩
  have hle : J ⊔ Subgroup.zpowers x ≤ T :=
    sup_le (fun j hj => ⟨j, hj, 0, by simp⟩) (Subgroup.zpowers_le.2 hxT)
  obtain ⟨j, hj, k, hk⟩ := hle ha
  exact ⟨j, hj, k, hk⟩

private theorem lemma119_normal_subgroupOf {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    (H.subgroupOf K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 := (Subgroup.mem_normalizer_iff.1 (hK g.2) n).1 hn
  simpa using h1

private theorem lemma119_rl_conj_sup {Y Z W : Subgroup G} {g : G}
    (hY : ∀ y ∈ Y, g * y * g⁻¹ ∈ W) (hZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ W) :
    ∀ w ∈ Y ⊔ Z, g * w * g⁻¹ ∈ W := by
  have hle : Y ⊔ Z ≤ Subgroup.comap (MulAut.conj g).toMonoidHom W :=
    sup_le (fun y hy => Subgroup.mem_comap.2 (by simpa using hY y hy))
      (fun z hz => Subgroup.mem_comap.2 (by simpa using hZ z hz))
  intro w hw
  simpa using Subgroup.mem_comap.1 (hle hw)

private theorem lemma119_rl_le_normalizer {A Y : Subgroup G}
    (h : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) : A ≤ Subgroup.normalizer (Y : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h a ha y hy, fun hy => ?_⟩
  have h2 := h a⁻¹ (A.inv_mem ha) _ hy
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rw [e] at h2
  exact h2

private theorem lemma119_rl_comm_mem {O : Subgroup G} {g o : G}
    (hg : g ∈ Subgroup.normalizer (O : Set G)) (ho : o ∈ O) : ⁅o, g⁆ ∈ O := by
  have e : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.1 hg o⁻¹).1 (O.inv_mem ho))

private theorem lemma119_rl_comm_closure {O A E : Subgroup G}
    (hM : A ⊔ (E ⊔ O) ≤ Subgroup.normalizer (O : Set G)) {r : G}
    (hA : ∀ a ∈ A, ⁅a, r⁆ ∈ O) (hE : ∀ e ∈ E, ⁅e, r⁆ ∈ O) (hO : ∀ o ∈ O, ⁅o, r⁆ ∈ O) :
    ∀ x ∈ A ⊔ (E ⊔ O), ⁅x, r⁆ ∈ O := by
  let D : Subgroup G :=
    { carrier := {x | x ∈ A ⊔ (E ⊔ O) ∧ ⁅x, r⁆ ∈ O}
      one_mem' := ⟨Subgroup.one_mem _, by rw [commutatorElement_one_left]; exact O.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, haO⟩ ⟨hb, hbO⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have e : ⁅a * b, r⁆ = (a * ⁅b, r⁆ * a⁻¹) * ⁅a, r⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hM ha) _).1 hbO) haO
      inv_mem' := by
        rintro a ⟨ha, haO⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : ⁅a⁻¹, r⁆ = a⁻¹ * ⁅a, r⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hM (Subgroup.inv_mem _ ha)) _).1 (O.inv_mem haO) }
  have hAD : A ≤ D := fun a ha => ⟨Subgroup.mem_sup_left ha, hA a ha⟩
  have hED : E ≤ D := fun e he => ⟨Subgroup.mem_sup_right (Subgroup.mem_sup_left he), hE e he⟩
  have hOD : O ≤ D := fun o ho => ⟨Subgroup.mem_sup_right (Subgroup.mem_sup_right ho), hO o ho⟩
  have hall : A ⊔ (E ⊔ O) ≤ D := sup_le hAD (sup_le hED hOD)
  intro x hx
  exact (hall hx).2

private theorem lemma119_rl_pow_mul {O M : Subgroup G} (hM : M ≤ Subgroup.normalizer (O : Set G))
    (hcomm : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ O) {n : ℕ} {x z : G} (hx : x ∈ M) (hz : z ∈ M)
    (hxn : x ^ n ∈ O) (hzn : z ^ n ∈ O) : (x * z) ^ n ∈ O := by
  haveI : (O.subgroupOf M).Normal := lemma119_normal_subgroupOf hM
  let a : ↥M := ⟨x, hx⟩
  let b : ↥M := ⟨z, hz⟩
  have hab : (QuotientGroup.mk a : ↥M ⧸ O.subgroupOf M) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((a * b)⁻¹ * (b * a) : ↥M) : G) = ⁅z⁻¹, x⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, a, b, commutatorElement_def]; group
    rw [e]
    exact hcomm _ (M.inv_mem hz) _ (M.inv_mem hx)
  have hpow : ∀ c : ↥M, (QuotientGroup.mk c : ↥M ⧸ O.subgroupOf M) ^ n =
      QuotientGroup.mk (c ^ n) := fun c => (map_pow (QuotientGroup.mk' (O.subgroupOf M)) c n).symm
  have ha1 : (QuotientGroup.mk a : ↥M ⧸ O.subgroupOf M) ^ n = 1 := by
    rw [hpow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [a] using hxn
  have hb1 : (QuotientGroup.mk b : ↥M ⧸ O.subgroupOf M) ^ n = 1 := by
    rw [hpow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [b] using hzn
  have hprod : (QuotientGroup.mk (a * b) : ↥M ⧸ O.subgroupOf M) ^ n = 1 := by
    rw [QuotientGroup.mk_mul, (show Commute (QuotientGroup.mk a : ↥M ⧸ O.subgroupOf M)
      (QuotientGroup.mk b) from hab).mul_pow, ha1, hb1, one_mul]
  have h4 : (QuotientGroup.mk ((a * b) ^ n) : ↥M ⧸ O.subgroupOf M) = 1 := by
    rw [← hpow]; exact hprod
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h4
  simpa using h4

theorem rank_lift {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {O A E S : Subgroup G}
    (hO : ¬ q ∣ Nat.card ↥O) (hAO : A ≤ Subgroup.normalizer (O : Set G))
    (hEO : E ≤ Subgroup.normalizer (O : Set G)) (hSO : S ≤ Subgroup.normalizer (O : Set G))
    (hA : IsElemAbelian q A) (hE : IsElemAbelian q E) (hAE : ∀ a ∈ A, ∀ e ∈ E, ⁅a, e⁆ ∈ O)
    (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hES : ∀ e ∈ E, ∀ s ∈ S, ⁅s, e⁆ ∈ O) :
    Nat.card ↥A * Nat.card ↥E ≤ Nat.card ↥(A ⊓ (E ⊔ O)) * q ^ GLATwoLocalRank q G := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOM : O ≤ A ⊔ (E ⊔ O) := (le_sup_right : O ≤ E ⊔ O).trans le_sup_right
  have hEM : E ≤ A ⊔ (E ⊔ O) := (le_sup_left : E ≤ E ⊔ O).trans le_sup_right
  have hAM : A ≤ A ⊔ (E ⊔ O) := le_sup_left
  have hMO : A ⊔ (E ⊔ O) ≤ Subgroup.normalizer (O : Set G) :=
    sup_le hAO (sup_le hEO Subgroup.le_normalizer)
  have hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' =>
    isElemAbelian_commute hE he he'
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    isElemAbelian_commute hA ha ha'
  have hcomm_inv : ∀ a b : G, ⁅a, b⁆⁻¹ = ⁅b, a⁆ := fun a b => by
    simp only [commutatorElement_def]; group
  have hUa : ∀ a ∈ A, ∀ x ∈ A ⊔ (E ⊔ O), ⁅x, a⁆ ∈ O := by
    intro a ha
    refine lemma119_rl_comm_closure hMO (r := a) ?_ ?_ ?_
    · intro a' ha'
      have h1 : ⁅a', a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hAcomm a' ha' a ha)
      rw [h1]; exact O.one_mem
    · intro e he
      rw [← hcomm_inv]
      exact O.inv_mem (hAE a ha e he)
    · intro o ho
      exact lemma119_rl_comm_mem (hAO ha) ho
  have hUe : ∀ e ∈ E, ∀ x ∈ A ⊔ (E ⊔ O), ⁅x, e⁆ ∈ O := by
    intro e he
    refine lemma119_rl_comm_closure hMO (r := e) ?_ ?_ ?_
    · intro a ha
      exact hAE a ha e he
    · intro e' he'
      have h1 : ⁅e', e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hEcomm e' he' e he)
      rw [h1]; exact O.one_mem
    · intro o ho
      exact lemma119_rl_comm_mem (hEO he) ho
  have hcomm : ∀ y ∈ A ⊔ (E ⊔ O), ∀ x ∈ A ⊔ (E ⊔ O), ⁅x, y⁆ ∈ O := by
    intro y hy
    refine lemma119_rl_comm_closure hMO (r := y) ?_ ?_ ?_
    · intro a ha
      rw [← hcomm_inv]
      exact O.inv_mem (hUa a ha y hy)
    · intro e he
      rw [← hcomm_inv]
      exact O.inv_mem (hUe e he y hy)
    · intro o ho
      exact lemma119_rl_comm_mem (hMO hy) ho
  have hpowO : ∀ x ∈ A ⊔ (E ⊔ O), x ^ q ∈ O := by
    let K : Subgroup G :=
      { carrier := {x | x ∈ A ⊔ (E ⊔ O) ∧ x ^ q ∈ O}
        one_mem' := ⟨Subgroup.one_mem _, by rw [one_pow]; exact O.one_mem⟩
        mul_mem' := fun {x z} hx hz =>
          ⟨Subgroup.mul_mem _ hx.1 hz.1,
            lemma119_rl_pow_mul hMO (fun a ha b hb => hcomm b hb a ha) hx.1 hz.1 hx.2 hz.2⟩
        inv_mem' := fun {x} hx =>
          ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow]; exact O.inv_mem hx.2⟩ }
    have hAK : A ≤ K := fun a ha => ⟨hAM ha, by rw [hA.2 a ha]; exact O.one_mem⟩
    have hEK : E ≤ K := fun e he => ⟨hEM he, by rw [hE.2 e he]; exact O.one_mem⟩
    have hOK : O ≤ K := fun o ho => ⟨hOM ho, O.pow_mem ho q⟩
    have hall : A ⊔ (E ⊔ O) ≤ K := sup_le hAK (sup_le hEK hOK)
    intro x hx
    exact (hall hx).2
  obtain ⟨a₀, ha₀⟩ := exists_card_eq_pow_of_isElemAbelian hq hA
  obtain ⟨b₀, hb₀⟩ := exists_card_eq_pow_of_isElemAbelian hq hE
  have hOE_inf : Nat.card ↥(O ⊓ E) = 1 := by
    have h1 : Nat.card ↥(O ⊓ E) ∣ q ^ b₀ := by
      have := Subgroup.card_dvd_of_le (inf_le_right : O ⊓ E ≤ E)
      rwa [hb₀] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1 h1
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [hj, h0, pow_zero]
    · exfalso
      have hq1 : q ∣ Nat.card ↥(O ⊓ E) := by rw [hj]; exact dvd_pow_self q hpos.ne'
      exact hO (hq1.trans (Subgroup.card_dvd_of_le (inf_le_left : O ⊓ E ≤ O)))
  have hOE : Nat.card ↥(O ⊔ E) = Nat.card ↥O * Nat.card ↥E := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := E) hEO
    rw [hOE_inf, mul_one] at h
    exact h
  have hEO' : Nat.card ↥(E ⊔ O) = Nat.card ↥O * Nat.card ↥E := by
    rw [sup_comm]; exact hOE
  have hAEO : A ≤ Subgroup.normalizer ((E ⊔ O : Subgroup G) : Set G) := by
    refine lemma119_rl_le_normalizer (fun a ha => ?_)
    refine lemma119_rl_conj_sup (Y := E) (Z := O) (W := E ⊔ O) (g := a)
      (fun e he => ?_) (fun o ho => ?_)
    · have e' : a * e * a⁻¹ = ⁅a, e⁆ * e := by rw [commutatorElement_def]; group
      rw [e']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hAE a ha e he)) (Subgroup.mem_sup_left he)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hAO ha) o).1 ho)
  have hMcard : Nat.card ↥(A ⊔ (E ⊔ O)) * Nat.card ↥(A ⊓ (E ⊔ O)) =
      Nat.card ↥(E ⊔ O) * Nat.card ↥A := by
    rw [sup_comm A (E ⊔ O), inf_comm A (E ⊔ O)]
    exact card_sup_mul_card_inf_of_le_normalizer hAEO
  have hNcard : Nat.card ↥(O.subgroupOf (A ⊔ (E ⊔ O))) = Nat.card ↥O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOM).toEquiv
  have hMQ : Nat.card ↥(A ⊔ (E ⊔ O)) =
      Nat.card (↥(A ⊔ (E ⊔ O)) ⧸ O.subgroupOf (A ⊔ (E ⊔ O))) * Nat.card ↥O := by
    rw [← hNcard]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hOpos : 0 < Nat.card ↥O := Nat.card_pos
  set Qc := Nat.card (↥(A ⊔ (E ⊔ O)) ⧸ O.subgroupOf (A ⊔ (E ⊔ O))) with hQc_def
  set c := Nat.card ↥(A ⊓ (E ⊔ O)) with hc_def
  have hQc : Qc * c = Nat.card ↥E * Nat.card ↥A := by
    have hkey : Nat.card ↥O * (Qc * c) = Nat.card ↥O * (Nat.card ↥E * Nat.card ↥A) := by
      have h3 := hMcard
      rw [hEO', hMQ] at h3
      calc Nat.card ↥O * (Qc * c) = Qc * Nat.card ↥O * c := by ring
        _ = Nat.card ↥O * Nat.card ↥E * Nat.card ↥A := h3
        _ = Nat.card ↥O * (Nat.card ↥E * Nat.card ↥A) := by ring
    exact Nat.eq_of_mul_eq_mul_left hOpos hkey
  have hQpow : Qc ∣ q ^ (a₀ + b₀) := by
    refine Dvd.intro c ?_
    rw [pow_add, ← ha₀, ← hb₀, hQc, mul_comm]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1 hQpow
  have hcopQO : Nat.Coprime (Nat.card ↥O) Qc := by
    rw [hj]
    exact Nat.Coprime.pow_right j (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hO))
  haveI hNn : (O.subgroupOf (A ⊔ (E ⊔ O))).Normal := lemma119_normal_subgroupOf hMO
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := O.subgroupOf (A ⊔ (E ⊔ O))) (by rw [hNcard]; exact hcopQO)
  have hNH : O.subgroupOf (A ⊔ (E ⊔ O)) ⊓ H = ⊥ := disjoint_iff.1 hH.disjoint
  have hHcard : Nat.card ↥H = Qc := by
    have h1 : Nat.card ↥(O.subgroupOf (A ⊔ (E ⊔ O))) * Nat.card ↥H =
        Nat.card ↥(A ⊔ (E ⊔ O)) := Subgroup.IsComplement.card_mul_card hH
    rw [hNcard, hMQ] at h1
    exact Nat.eq_of_mul_eq_mul_left hOpos (h1.trans (mul_comm _ _))
  have hTcomm : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ * h₂ = h₂ * h₁ := by
    intro h₁ hh₁ h₂ hh₂
    have hu : (⁅h₁, h₂⁆ : ↥(A ⊔ (E ⊔ O))) = 1 := by
      have hmem : (⁅h₁, h₂⁆ : ↥(A ⊔ (E ⊔ O))) ∈ O.subgroupOf (A ⊔ (E ⊔ O)) ⊓ H := by
        refine ⟨Subgroup.mem_subgroupOf.2 ?_, ?_⟩
        · have e : ((⁅h₁, h₂⁆ : ↥(A ⊔ (E ⊔ O))) : G) = ⁅(h₁ : G), (h₂ : G)⁆ := by
            simp [commutatorElement_def]
          rw [e]
          exact hcomm _ h₂.2 _ h₁.2
        · rw [commutatorElement_def]
          exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
      rw [hNH, Subgroup.mem_bot] at hmem
      exact hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 hu
  have hTexp : ∀ h ∈ H, h ^ q = 1 := by
    intro h hh
    have hmem : h ^ q ∈ O.subgroupOf (A ⊔ (E ⊔ O)) ⊓ H := by
      refine ⟨Subgroup.mem_subgroupOf.2 ?_, H.pow_mem hh q⟩
      simpa using hpowO (h : G) h.2
    rw [hNH, Subgroup.mem_bot] at hmem
    exact hmem
  set T₀ : Subgroup G := H.map (A ⊔ (E ⊔ O)).subtype with hT₀def
  have hT₀card : Nat.card ↥T₀ = Qc := by
    rw [hT₀def, Subgroup.card_map_of_injective Subtype.val_injective, hHcard]
  have hT₀M : T₀ ≤ A ⊔ (E ⊔ O) := Subgroup.map_subtype_le H
  have hGcomm : ∀ x ∈ T₀, ∀ y ∈ T₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨h₁, hh₁, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨h₂, hh₂, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul, hTcomm h₁ hh₁ h₂ hh₂]
  have hGexp : ∀ x ∈ T₀, x ^ q = 1 := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hTexp h hh, map_one]
  have hT₀el : IsElemAbelian q T₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (hGcomm a a.2 b b.2)⟩⟩, fun x hx => hGexp x hx⟩
  have hAP : A ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := by
    refine lemma119_rl_le_normalizer (fun a ha => ?_)
    refine lemma119_rl_conj_sup (Y := S) (Z := O) (W := S ⊔ O) (g := a)
      (fun s hs => ?_) (fun o ho => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hAS ha) s).1 hs)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hAO ha) o).1 ho)
  have hEP : E ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := by
    refine lemma119_rl_le_normalizer (fun e he => ?_)
    refine lemma119_rl_conj_sup (Y := S) (Z := O) (W := S ⊔ O) (g := e)
      (fun s hs => ?_) (fun o ho => ?_)
    · have e' : e * s * e⁻¹ = ⁅s, e⁆⁻¹ * s := by rw [commutatorElement_def]; group
      rw [e']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (O.inv_mem (hES e he s hs)))
        (Subgroup.mem_sup_left hs)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hEO he) o).1 ho)
  have hOP : O ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) :=
    fun o ho => (Subgroup.le_normalizer (H := S ⊔ O)) (Subgroup.mem_sup_right ho)
  have hT₀P : T₀ ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) :=
    hT₀M.trans (sup_le hAP (sup_le hEP hOP))
  have hPcard : Nat.card ↥(S ⊔ O) * Nat.card ↥(S ⊓ O) = Nat.card ↥O * Nat.card ↥S := by
    rw [sup_comm S O, inf_comm S O]
    exact card_sup_mul_card_inf_of_le_normalizer hSO
  have hPnd : ¬ q ∣ Nat.card ↥(S ⊔ O) := by
    intro hdvd
    have h1 : q ∣ Nat.card ↥O * Nat.card ↥S := by
      rw [← hPcard]; exact Dvd.dvd.mul_right hdvd _
    rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
    · exact hO h
    · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
      have hq2' : q ∣ 2 ^ k := hk ▸ h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hq2'))
  have hPeven : Even (Nat.card ↥(S ⊔ O)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hSne
      apply Subgroup.eq_bot_of_card_eq
      simpa using hk
    have h2S : 2 ∣ Nat.card ↥S := by rw [hk]; exact dvd_pow_self 2 hk0
    exact even_iff_two_dvd.2 (h2S.trans (Subgroup.card_dvd_of_le le_sup_left))
  obtain ⟨R, hRne, -, hR2, hTR⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_twoGroup_normalized_of_coprime_even hq hq2
      (isPGroup_of_isElemAbelian hT₀el) hT₀P hPnd hPeven
  have hbound : Nat.card ↥T₀ ≤ q ^ GLATwoLocalRank q G :=
    card_le_pow_glaTwoLocalRank hq hT₀el hRne hR2 hTR
  rw [hT₀card] at hbound
  calc Nat.card ↥A * Nat.card ↥E = Nat.card ↥E * Nat.card ↥A := mul_comm _ _
    _ = c * Qc := by rw [← hQc, mul_comm]
    _ ≤ c * q ^ GLATwoLocalRank q G := Nat.mul_le_mul_left _ hbound

theorem centMod_eq_zpowers_of_cfg (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') : CentModEqZpowers p' B' L' x' := by
  have hp' : p'.Prime := hc.cfg.prime
  have hxc : ∀ l ∈ L', l * x' = x' * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl)
  have hJq : CFSG.Open.IsQuasisimple ↥J := hc.cfg.comp.1.2.2
  have hJL : J ≤ L' := hc117.J_le
  intro b hb
  constructor
  · intro hcm
    obtain ⟨S, hSJ, hS2, hBS, hCS⟩ := hc.cfg.eight
    have hb' := mem_centModSubgroup.1 (centMod_iff.1 hcm)
    have hcent : b ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsL : s ∈ L' := hJL (hSJ hs)
      have hcS : ⁅s, b⁆ ∈ S := by
        have hbs : b * s⁻¹ * b⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.1 (hBS hb) s⁻¹).1 (S.inv_mem hs)
        have hdecomp : ⁅s, b⁆ = s * (b * s⁻¹ * b⁻¹) := by
          rw [commutatorElement_def]; group
        rw [hdecomp]
        exact S.mul_mem hs hbs
      have hcO : ⁅s, b⁆ ∈ GLAPPrimeCoreOf p' L' := hb'.2 s hsL
      have hcJ : ⁅s, b⁆ ∈ J := hSJ hcS
      have hnormal : ((GLAPPrimeCoreOf p' L').subgroupOf J).Normal :=
        lemma119_normal_subgroupOf (H := GLAPPrimeCoreOf p' L') (K := J)
          (hJL.trans (le_normalizer_glaPPrimeCoreOf p' L'))
      have hne : (GLAPPrimeCoreOf p' L').subgroupOf J ≠ ⊤ := by
        intro htop
        have hJO : J ≤ GLAPPrimeCoreOf p' L' := by
          intro j hj
          have hmem : (⟨j, hj⟩ : ↥J) ∈ (GLAPPrimeCoreOf p' L').subgroupOf J := by
            rw [htop]; exact Subgroup.mem_top _
          exact Subgroup.mem_subgroupOf.1 hmem
        have h2 : p' ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
          (dvd_mul_left p' p).trans hc.cfg.dvd
        have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
        have h1 : p' ∣ Nat.card ↥J := by
          rw [h3]; exact Dvd.dvd.mul_right h2 _
        exact not_dvd_card_glaPPrimeCoreOf hp' L' (h1.trans (Subgroup.card_dvd_of_le hJO))
      have hz : (⟨⁅s, b⁆, hcJ⟩ : ↥J) ∈ Subgroup.center ↥J :=
        le_center_of_normal_of_isQuasisimple hJq hnormal hne (Subgroup.mem_subgroupOf.2 hcO)
      have hu : ⁅s, b⁆ = 1 := by
        obtain ⟨n, hn⟩ := hS2 ⟨⁅s, b⁆, hcS⟩
        have h2n : ⁅s, b⁆ ^ 2 ^ n = 1 := by
          have := congrArg Subtype.val hn
          simpa using this
        have hord2 : orderOf ⁅s, b⁆ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2n
        have hZ := orderOf_dvd_natCard (⟨⟨⁅s, b⁆, hcJ⟩, hz⟩ : Subgroup.center ↥J)
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hZ
        have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥(Subgroup.center ↥J)) :=
          Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hc.cfg.odd_center)
        have hone : orderOf ⁅s, b⁆ = 1 := by
          have := Nat.dvd_gcd hord2 hZ
          rw [hcop.gcd_eq_one] at this
          exact Nat.dvd_one.1 this
        exact orderOf_eq_one_iff.1 hone
      exact commutatorElement_eq_one_iff_mul_comm.1 hu
    have hbz : b ∈ B' ⊓ Subgroup.centralizer (S : Set G) := ⟨hb, hcent⟩
    rw [hCS] at hbz
    exact hbz
  · intro hbz
    apply centMod_of_mem_centralizer
    have hx : x' ∈ Subgroup.centralizer (L' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact hxc l hl
    exact (Subgroup.zpowers_le.2 hx) hbz

private theorem lemma119_O_le_centMod (p : ℕ) (L : Subgroup G) :
    GLAPPrimeCoreOf p L ≤ centModSubgroup p L := by
  intro o ho
  have hOL : GLAPPrimeCoreOf p L ≤ L := Subgroup.map_subtype_le _
  refine mem_centModSubgroup.2 ⟨Subgroup.le_normalizer (H := L) (hOL ho), fun l hl => ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L hl) o).1 ho
  have e : ⁅l, o⁆ = (l * o * l⁻¹) * o⁻¹ := by rw [commutatorElement_def]
  rw [e]
  exact (GLAPPrimeCoreOf p L).mul_mem h1 ((GLAPPrimeCoreOf p L).inv_mem ho)

theorem ab_case1_cent (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hB : B' ≤ J ⊔ Subgroup.zpowers x') :
    ∀ S : Subgroup G, S ≤ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) → IsPGroup p' S → IsCyclic S := by
  intro S hS hSp
  by_contra hnc
  have hq : p'.Prime := hc.cfg.prime
  haveI : Fact p'.Prime := ⟨hq⟩
  have hq2 : p' ≠ 2 := hc.cfg.odd
  obtain ⟨E, hES', hE, hEcard⟩ := CFSG.Goldschmidt.G55.exists_isElemAbelian_card_sq hq hq2 hSp hnc
  have hEc : ∀ e ∈ E, e ∈ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) :=
    fun e he => hS (hES' he)
  have hJL : J ≤ L' := hc117.J_le
  have hxc : ∀ l ∈ L', l * x' = x' * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl)
  have hxJ : ∀ j ∈ J, j * x' = x' * j := fun j hj => hxc j (hJL hj)
  obtain ⟨Ss, hSsJ, hSs2, hBSs, hCSs⟩ := hc.cfg.eight
  have hSsne : Ss ≠ ⊥ := by
    intro hbot
    have hBle : B' ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
      intro b _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
    have hBeq : B' = Subgroup.zpowers x' := by
      rw [← hCSs, hbot, inf_eq_left.2 hBle]
    have hord : orderOf x' = p' := orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one
    have hcard : Nat.card ↥B' = p' := by
      rw [hBeq, Nat.card_zpowers, hord]
    have hm : p' ^ m = p' := by
      rw [← hc.e_eq, ← hc.cfg.rank_B, hcard]
    have hm1 : m = 1 := Nat.pow_right_injective hq.two_le (show p' ^ m = p' ^ 1 by rw [hm, pow_one])
    have h4 := hctx.1.four_le
    omega
  have hO : ¬ p' ∣ Nat.card ↥(GLAPPrimeCoreOf p' L') := not_dvd_card_glaPPrimeCoreOf hq L'
  have hBN : B' ≤ Subgroup.normalizer (GLAPPrimeCoreOf p' L' : Set G) :=
    (bstar_norm hc hc117.comp' hc117.J_le hc117.uniq).trans
      (normalizer_le_normalizer_glaPPrimeCoreOf p' L')
  have hEN : E ≤ Subgroup.normalizer (GLAPPrimeCoreOf p' L' : Set G) := fun e he =>
    normalizer_le_normalizer_glaPPrimeCoreOf p' L' ((mem_centModSubgroup.1 (hEc e he).1).1)
  have hSsN : Ss ≤ Subgroup.normalizer (GLAPPrimeCoreOf p' L' : Set G) :=
    hSsJ.trans (hJL.trans (le_normalizer_glaPPrimeCoreOf p' L'))
  have hAE : ∀ a ∈ B', ∀ e ∈ E, ⁅a, e⁆ ∈ GLAPPrimeCoreOf p' L' := by
    intro a ha e he
    obtain ⟨j, hj, k, rfl⟩ := lemma119_mem_sup hxJ (hB ha)
    have hex : e * x' = x' * e := Subgroup.mem_centralizer_singleton_iff.1 (hEc e he).2
    have hcz : Commute (x' ^ k) e := ((show Commute x' e from hex.symm).zpow_left k)
    have hce : x' ^ k * e * (x' ^ k)⁻¹ = e := by rw [hcz.eq]; group
    have e1 : ⁅j * x' ^ k, e⁆ = j * (x' ^ k * e * (x' ^ k)⁻¹) * j⁻¹ * e⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1, hce]
    have e2 : j * e * j⁻¹ * e⁻¹ = ⁅j, e⁆ := by
      simp only [commutatorElement_def]
    rw [e2]
    exact (mem_centModSubgroup.1 (hEc e he).1).2 j (hJL hj)
  have hES : ∀ e ∈ E, ∀ s ∈ Ss, ⁅s, e⁆ ∈ GLAPPrimeCoreOf p' L' := fun e he s hs =>
    (mem_centModSubgroup.1 (hEc e he).1).2 s (hJL (hSsJ hs))
  have hrank := rank_lift hq hq2 hO hBN hEN hSsN hc.cfg.elem hE hAE hSs2 hSsne hBSs hES
  have hcle : Nat.card ↥(B' ⊓ (E ⊔ GLAPPrimeCoreOf p' L')) ≤ p' := by
    have hsub : B' ⊓ (E ⊔ GLAPPrimeCoreOf p' L') ≤ Subgroup.zpowers x' := by
      intro b hb
      have hsup : E ⊔ GLAPPrimeCoreOf p' L' ≤ centModSubgroup p' L' :=
        sup_le (fun e he => (hEc e he).1) (lemma119_O_le_centMod p' L')
      exact (centMod_eq_zpowers_of_cfg hc hc117 b hb.1).1 (centMod_iff.2 (hsup hb.2))
    calc Nat.card ↥(B' ⊓ (E ⊔ GLAPPrimeCoreOf p' L')) ≤ Nat.card ↥(Subgroup.zpowers x') :=
          Subgroup.card_le_of_le hsub
      _ = p' := by rw [Nat.card_zpowers, orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one]
  have hm : Nat.card ↥B' = p' ^ m := by rw [hc.cfg.rank_B, hc.e_eq]
  have hrk : GLATwoLocalRank p' G = m := hc.mu.2.1
  rw [hm, hEcard, hrk] at hrank
  have h2 : p' ^ m * p' ^ 2 ≤ p' * p' ^ m := le_trans hrank (Nat.mul_le_mul_right _ hcle)
  rw [mul_comm p' (p' ^ m)] at h2
  have hpos : 0 < p' ^ m := pow_pos hq.pos m
  have h3 : p' ^ 2 ≤ p' := Nat.le_of_mul_le_mul_left h2 hpos
  have h4 := hq.two_le
  nlinarith

theorem ab_case1_cyc (hctx : ThmACtx G m) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hB : B' ≤ J ⊔ Subgroup.zpowers x') : CycModSylow p' L' := by
  have hp' : p'.Prime := hc.cfg.prime
  haveI : Fact p'.Prime := ⟨hp'⟩
  have hxc : ∀ l ∈ L', l * x' = x' * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl)
  have hx' : x' ∈ centModSubgroup p' L' := by
    refine mem_centModSubgroup.2 ⟨Subgroup.centralizer_le_normalizer (L' : Set G) ?_, fun l hl => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact hxc l hl
    · have h1 : ⁅l, x'⁆ = 1 := by
        rw [commutatorElement_def, hxc l hl]
        group
      rw [h1]
      exact Subgroup.one_mem _
  exact cycModSylow_of_cent_cyclic hp' hx' (orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one)
    (ab_case1_cent hctx hc hc117 hB)

private theorem lemma119_induces_inner {G : Type} [Group G] {p : ℕ} {L' J : Subgroup G} {x : G}
    (hJ : J ≤ L') (hL : L' ≤ Subgroup.centralizer ({x} : Set G)) {j : G} (hj : j ∈ J) (k : ℤ)
    {R : Type} [Group R] (θ : (PQuot p L') ⧸ Subgroup.center (PQuot p L') ≃* R) :
    GLAInduces θ (indRel p L' (j * x ^ k))
      (MulAut.conj ((θ (QuotientGroup.mk (QuotientGroup.mk ⟨j, hJ hj⟩ : PQuot p L')))⁻¹)) := by
  rintro q q' ⟨l, l', rfl, rfl, hll⟩
  have hjL' : j ∈ L' := hJ hj
  have hu_mem : j⁻¹ * (l : G) * j ∈ L' := L'.mul_mem (L'.mul_mem (L'.inv_mem hjL') l.2) hjL'
  have hu_cent : j⁻¹ * (l : G) * j * x = x * (j⁻¹ * (l : G) * j) :=
    Subgroup.mem_centralizer_singleton_iff.1 (hL hu_mem)
  have hcomm_k : Commute (j⁻¹ * (l : G) * j) (x ^ k) :=
    (show Commute (j⁻¹ * (l : G) * j) x from hu_cent).zpow_right k
  have key : (x ^ k)⁻¹ * (j⁻¹ * (l : G) * j) * x ^ k = j⁻¹ * (l : G) * j := by
    rw [mul_assoc ((x ^ k)⁻¹) (j⁻¹ * (l : G) * j) (x ^ k), hcomm_k.eq, inv_mul_cancel_left]
  have hl'eq : l' = (⟨j, hjL'⟩ : L')⁻¹ * l * ⟨j, hjL'⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hll]
    calc (j * x ^ k)⁻¹ * (l : G) * (j * x ^ k) = (x ^ k)⁻¹ * (j⁻¹ * (l : G) * j) * x ^ k := by
          group
      _ = j⁻¹ * (l : G) * j := key
  rw [hl'eq, MulAut.conj_apply]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, inv_inv]

theorem ab_case1_idiag (h08 : YS08) (hsf : StageFacts G m) (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L')
    (hB : B' ≤ J ⊔ Subgroup.zpowers x') (hchev : IsChevSimple 2 (PSimple p' L')) : InnDiagOn p' B' L' := by
  have hp' : p'.Prime := hc.cfg.prime
  have hnorm : B' ≤ Subgroup.normalizer (L' : Set G) :=
    bstar_norm hc hc117.comp' hc117.J_le hc117.uniq
  have hq : CFSG.Open.IsQuasisimple (PQuot p' L') :=
    isQuasisimple_pQuot_of_glaPComponent hp' hc117.comp'
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h08 (PQuot p' L') hq hchev
  refine ⟨hnorm, hcomm, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (lemma119_rawDatum_inn lab _ hraw)
  rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hInn⟩
  refine ⟨hs, hna, θ, fun a ha => ?_⟩
  have hx : ∀ j ∈ J, j * x' = x' * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 (hc117.J_le hj))
  obtain ⟨j, hj, k, rfl⟩ := lemma119_mem_sup hx (hB ha)
  exact ⟨MulAut.conj ((θ (QuotientGroup.mk (QuotientGroup.mk ⟨j, hc117.J_le hj⟩ : PQuot p' L')))⁻¹),
    hInn ⟨_, rfl⟩, lemma119_induces_inner hc117.J_le hc117.comp'.1 hj k θ⟩

theorem ab_case1 (h08 : YS08) (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hB : B' ≤ J ⊔ Subgroup.zpowers x') (hchev : IsChevSimple 2 (PSimple p' L')) :
    CycModSylow p' L' ∧ InnDiagOn p' B' L' :=
  ⟨ab_case1_cyc hctx hc hc117 hB, ab_case1_idiag h08 hsf hc hc117 hB hchev⟩

theorem u64_labelJ (h6 : U6StructAt G) (hc : Cfg116 G m p L p' B' x' J) (hU : LabelOf L ⟨.twA, 5, 2⟩) :
    LabelOf J ⟨.twA, 4, 2⟩ := by
  obtain ⟨labJ, hlabJ, hshape⟩ := hc.cfg.shape ⟨.twA, 5, 2⟩ hU
  have hZ : Subgroup.center ↥L = ⊥ := h6.center L hU
  have hz3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
    rw [hZ]
    simp
  obtain ⟨t, r, n⟩ := labJ
  simp [JShape, hz3] at hshape
  obtain ⟨h1, h2, h3⟩ := hshape
  subst h1 h2 h3
  exact hlabJ

theorem u64_x_mem_J (h6 : U6StructAt G) (hc : Cfg116 G m p L p' B' x' J) (hU : LabelOf L ⟨.twA, 5, 2⟩)
    (hp5 : p' = 5) : x' ∈ J := by
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact h6.mem L J x' hU (hc.cfg.le hc.cfg.mem)
    (orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one) hc.cfg.comp.2 (u64_labelJ h6 hc hU)

theorem centMod_le_centralizer_of_mem {q : ℕ} (hq : q.Prime) {K : Subgroup G} {y : G} (hyK : y ∈ K)
    (hyc : ∀ l ∈ K, l * y = y * l) (hyq : orderOf y = q) :
    centModSubgroup q K ≤ Subgroup.centralizer ({y} : Set G) := by
  intro g hg
  obtain ⟨hgN, hgc⟩ := mem_centModSubgroup.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hy' : g * y * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgN y).1 hyK
  have hz : ⁅y, g⁆ ∈ GLAPPrimeCoreOf q K := hgc y hyK
  have hy'c : ∀ l ∈ K, l * (g * y * g⁻¹) = (g * y * g⁻¹) * l := by
    intro l hl
    have hl' : g⁻¹ * l * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgN) l).1 hl
      simpa using this
    have h := hyc _ hl'
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
      _ = (g * y * g⁻¹) * l := by group
  have hzeq : ⁅y, g⁆ = y * (g * y * g⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  have hcomm : Commute y (g * y * g⁻¹) := (hyc _ hy').symm
  have hyp : y ^ q = 1 := by rw [← hyq]; exact pow_orderOf_eq_one y
  have hy'p : (g * y * g⁻¹) ^ q = 1 := by
    rw [conj_pow, hyp]
    simp
  have hzp : (⁅y, g⁆) ^ q = 1 := by
    rw [hzeq, hcomm.inv_right.mul_pow, hyp, inv_pow, hy'p]
    simp
  have hO : ¬ q ∣ Nat.card ↥(GLAPPrimeCoreOf q K) := not_dvd_card_glaPPrimeCoreOf hq K
  have hz1 : ⁅y, g⁆ = 1 := by
    by_contra hne
    have h1 : orderOf (⁅y, g⁆) ∣ q := orderOf_dvd_of_pow_eq_one hzp
    have hq' : orderOf (⁅y, g⁆) = q := by
      rcases (Nat.dvd_prime hq).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hne
      · exact h
    have hord : orderOf (⟨⁅y, g⁆, hz⟩ : ↥(GLAPPrimeCoreOf q K)) = q := by
      rw [Subgroup.orderOf_mk]
      exact hq'
    have hdvd := orderOf_dvd_natCard (⟨⁅y, g⁆, hz⟩ : ↥(GLAPPrimeCoreOf q K))
    rw [hord] at hdvd
    exact hO hdvd
  have : y = g * y * g⁻¹ := by
    have := hz1
    rw [hzeq, mul_inv_eq_one] at this
    exact this
  calc g * y = (g * y * g⁻¹) * g := by group
    _ = y * g := by rw [← this]

private theorem lemma119_u64_types_of_m4 (hm4 : m = 4) (h08 : YS08) (h64 : U64TypesAt G) (h5r : U5RankAt)
    (h6 : U6StructAt G) (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L)
    (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L') (hU : LabelOf L ⟨.twA, 5, 2⟩)
    (hp3 : p = 3) (hp5 : p' = 5) (hchev : IsChevSimple 2 (PSimple p' L')) :
    GLAMarking (PQuot p' L') (fun lab _ _ _ _ _ => lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩) := by
  subst hp5
  have hq : Nat.Prime 5 := hc.cfg.prime
  haveI : Fact (Nat.Prime 5) := ⟨hq⟩
  have hqs : CFSG.Open.IsQuasisimple (PQuot 5 L') := isQuasisimple_pQuot_of_glaPComponent hq hc117.comp'
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h08 (PQuot 5 L') hqs hchev
  have hmark : GLAMarking (PQuot 5 L') (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (by rintro R _ I F ⟨hs, hna, θ, -⟩; exact ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hxJ : x' ∈ J := u64_x_mem_J h6 hc hU rfl
  have hxL : x' ∈ L' := hc117.J_le hxJ
  have hx5 : x' ^ 5 = 1 := hc.cfg.elem.2 x' hc.cfg.mem
  have hord : orderOf x' = 5 := orderOf_eq_prime hx5 hc.cfg.ne_one
  have hzc5 : 5 ∣ Nat.card (Subgroup.center (PQuot 5 L')) := by
    set z : PQuot 5 L' := QuotientGroup.mk (⟨x', hxL⟩ : ↥L') with hz_def
    have hzc : z ∈ Subgroup.center (PQuot 5 L') := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
      rw [hz_def, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 h.2))
    have hz1 : z ≠ 1 := by
      intro h1
      have hmem : x' ∈ GLAPPrimeCoreOf 5 L' :=
        Subgroup.mem_map.2 ⟨⟨x', hxL⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
      have hdvd := orderOf_dvd_natCard (⟨x', hmem⟩ : ↥(GLAPPrimeCoreOf 5 L'))
      rw [Subgroup.orderOf_mk, hord] at hdvd
      exact not_dvd_card_glaPPrimeCoreOf hq L' hdvd
    have hzp : z ^ 5 = 1 := by
      have h := map_pow (QuotientGroup.mk' (GLAPPrimeCore 5 ↥L')) (⟨x', hxL⟩ : ↥L') 5
      have hx5' : (⟨x', hxL⟩ : ↥L') ^ 5 = 1 := Subtype.ext (by simpa using hx5)
      rw [hx5', map_one] at h
      exact h.symm
    have hzord : orderOf z = 5 := orderOf_eq_prime hzp hz1
    have hcard : Nat.card (Subgroup.zpowers z) = 5 := by rw [Nat.card_zpowers, hzord]
    have hle : Subgroup.zpowers z ≤ Subgroup.center (PQuot 5 L') := Subgroup.zpowers_le.2 hzc
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [hcard] at hdvd
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) := by
    obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf 5 hc.mu
    have hc6 : S6Ctx G 5 := S6Ctx.of_ctx hctx hc.mu h3 h4o h4 h5
    exact kGroup_centralizer hc6 hc.cfg.ne_one
  have hxp : x ^ 3 = 1 := by
    have hH := rquad_hyp hsf hR
    have h := hH.elem.2 x hH.mem
    rw [hp3] at h
    exact h
  have hJ3 : GLAPComponent 3 (L' ⊓ Subgroup.centralizer ({x} : Set G)) J := by
    subst hp3
    exact hc117.J_layer.2
  have hK3 : GLAPComponent 3 (Subgroup.centralizer ({x'} : Set G)) L' := by
    subst hp3
    exact hc117.comp_p
  have hcases := h64 (Subgroup.centralizer ({x'} : Set G)) L' J x lab hKX hc117.comp' hK3 hmark hzc5
    hc117.x_norm hxp hJ3 (u64_labelJ h6 hc hU)
  rcases hcases with h1 | h1 | ⟨r, hr, h1⟩
  · exact ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (by rintro R _ I F ⟨hs, hna, θ, -⟩; exact ⟨hs, hna, θ, Or.inl h1⟩) hraw⟩
  · exact ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (by rintro R _ I F ⟨hs, hna, θ, -⟩; exact ⟨hs, hna, θ, Or.inr h1⟩) hraw⟩
  · exfalso
    have hmark' : GLAMarking (PQuot 5 L') (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5 * r - 1, 2⟩) :=
      ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (by rintro R _ I F ⟨hs, hna, θ, -⟩; exact ⟨hs, hna, θ, h1⟩) hraw⟩
    have h5 := h5r (PQuot 5 L') r hr hmark'
    have hG : GLATwoLocalRank 5 G = m := hc.mu.2.1
    have hle : GLATwoLocalRank 5 (PQuot 5 L') ≤ GLATwoLocalRank 5 G :=
      (twoLocalRank_quot_le hq (by norm_num) L').trans (twoLocalRank_le_top hq L')
    omega

theorem u64_types (h08 : YS08) (h64 : U64TypesAt G) (h5r : U5RankAt) (h6 : U6StructAt G)
    (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hU : LabelOf L ⟨.twA, 5, 2⟩) (hp3 : p = 3) (hp5 : p' = 5)
    (hchev : IsChevSimple 2 (PSimple p' L')) (hm4 : m = 4) :
    GLAMarking (PQuot p' L') (fun lab _ _ _ _ _ => lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩) :=
  lemma119_u64_types_of_m4 hm4 h08 h64 h5r h6 hctx hsf hR hc hc117 hU hp3 hp5 hchev

theorem u64_idiag (h5o : U5OutAt G) (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L')
    (hty : GLAMarking (PQuot p' L') (fun lab _ _ _ _ _ => lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩))
    (hp5 : p' = 5) : InnDiagOn p' B' L' := by
  subst hp5
  exact h5o (Subgroup.centralizer ({x'} : Set G)) L' B' hc117.comp' hc.cfg.elem
    (bstar_norm hc hc117.comp' hc117.J_le hc117.uniq) hty

private theorem y10x_two_dvd_of_perfect {K : Type} [Group K] [Finite K] [Nontrivial K]
    (hK : commutator K = ⊤) : 2 ∣ Nat.card K := by
  by_contra h
  have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hodd
  have : Group.IsPerfect K := ⟨hK⟩
  exact Group.IsPerfect.not_isSolvable K ‹_›

private theorem y10x_inf_eq_bot {L A : Subgroup G} (hZ : Subgroup.center ↥L = ⊥)
    (hA : A ≤ Subgroup.centralizer (L : Set G)) : A ⊓ L = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.1 hy
  have hz : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L :=
    Subgroup.mem_center_iff.2 fun k => Subtype.ext (Subgroup.mem_centralizer_iff.1 (hA hyA) k k.2)
  rw [hZ, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)

private theorem y10x_le_normalizer_of_comm {T E : Subgroup G} (h : ∀ e ∈ E, ∀ t ∈ T, e * t = t * e) :
    E ≤ Subgroup.normalizer (T : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h1 : e * t * e⁻¹ = t := by
      rw [h e he t ht, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact ht
  · intro hs
    have hc : e * (e * t * e⁻¹) = (e * t * e⁻¹) * e := h e he _ hs
    have h3 : e * (e * t * e⁻¹) = e * t := by
      rw [hc]; group
    have hst : e * t * e⁻¹ = t := mul_left_cancel h3
    rw [hst] at hs
    exact hs

private theorem y10x_attain {q : ℕ} (hq : q.Prime) {L : Subgroup G} [Nontrivial ↥L] (hcomm : commutator ↥L = ⊤) :
    ∃ T E : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ L ∧ E ≤ L ∧ IsElemAbelian q E ∧
      Nat.card E = q ^ GLATwoLocalRank q ↥L ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  have h2 : 2 ∣ Nat.card ↥L := y10x_two_dvd_of_perfect hcomm
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact absurd hg (by norm_num)
  obtain ⟨T₀, hT₀, hT₀2, E₀, hE₀N, hE₀a, hE₀c⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_twoLocal_attaining_GLATwoLocalRank hq
      ⟨Subgroup.zpowers g, fun h => hg1 (Subgroup.zpowers_eq_bot.1 h),
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])⟩
  refine ⟨T₀.map L.subtype, E₀.map L.subtype, ?_, hT₀2.map L.subtype, Subgroup.map_subtype_le T₀,
    Subgroup.map_subtype_le E₀, ?_, ?_, ?_⟩
  · intro h
    apply hT₀
    exact Subgroup.map_injective L.subtype_injective (h.trans (Subgroup.map_bot _).symm)
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b₀, hb₀, hb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hE₀a ha₀ hb₀]
    · obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 ha
      rw [← ha, ← map_pow, hE₀a.2 a₀ ha₀, map_one]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE₀c]
  · have fwd : ∀ e ∈ E₀, ∀ s ∈ T₀.map L.subtype, (e : G) * s * (e : G)⁻¹ ∈ T₀.map L.subtype := by
      rintro e he _ ⟨t, ht, rfl⟩
      exact ⟨e * t * e⁻¹, (Subgroup.mem_normalizer_iff.1 (hE₀N he) t).1 ht, by simp⟩
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fwd e he h
    · intro hh
      have := fwd e⁻¹ (E₀.inv_mem he) _ hh
      simpa [mul_assoc] using this

theorem u64_cent_rank (h6 : U6StructAt G) (hctx : ThmACtx G m) (hR : RQuad G m p B x L) (hind : Cor112Indep G m p B x L)
    (hc : Cfg116 G m p L p' B' x' J) (hU : LabelOf L ⟨.twA, 5, 2⟩) (hm4 : m = 4) (hp3 : p = 3) (hp5 : p' = 5) :
    CFSG.Open.pRank p (Subgroup.centralizer (L : Set G)) ≤ 1 ∧ ¬ p' ∣ Nat.card ↥(Subgroup.centralizer (L : Set G)) ∧
      Odd (Nat.card ↥(Subgroup.centralizer (L : Set G))) := by
  subst hp3 hp5
  have hcomm : commutator ↥L = ⊤ := (show commutator ↥L = ⊤ ∧ _ from hU).1
  obtain ⟨F, hFL, hFa, hFc⟩ := h6.rank L hU
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFc
    norm_num at hFc
  have hLne : L ≠ ⊥ := fun h => hFne (eq_bot_iff.2 fun f hf => by
    have := hFL hf
    rw [h] at this
    exact this)
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hLne
  have hm1 : GLATwoLocalRank 3 ↥L = 3 := by rw [hind.rank, hm4]
  have hG3 : GLATwoLocalRank 3 G = 4 := by
    have h := hR.1
    simp only [Mu, Set.mem_setOf_eq] at h
    rw [h.2.1, hm4]
  have hG5 : GLATwoLocalRank 5 G = 4 := by
    have h := hc.mu
    simp only [Mu, Set.mem_setOf_eq] at h
    rw [h.2.1, hm4]
  have hL5 : GLATwoLocalRank 5 ↥L = 4 := by rw [hc.cfg.rank_K, hc.e_eq, hm4]
  have hZ : Subgroup.center ↥L = ⊥ := h6.center L hU
  have h3 : CFSG.Open.pRank 3 (Subgroup.centralizer (L : Set G)) ≤ 1 := by
    obtain ⟨T, E₁, hT, hT2, hTL, hE₁L, hE₁a, hE₁c, hE₁N⟩ := y10x_attain (q := 3) Nat.prime_three hcomm
    rw [hm1] at hE₁c
    by_contra hk
    push_neg at hk
    obtain ⟨E, hEC, hEa, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (Subgroup.centralizer (L : Set G))
    have hEL : E ⊓ L = ⊥ := y10x_inf_eq_bot hZ hEC
    have hdisj : E₁ ⊓ E = ⊥ := by
      rw [inf_comm]
      exact eq_bot_mono (inf_le_inf_left E hE₁L) hEL
    have hE_N : E ≤ Subgroup.normalizer (E₁ : Set G) := y10x_le_normalizer_of_comm fun e he t ht =>
      (Subgroup.mem_centralizer_iff.1 (hEC he) t (hE₁L ht)).symm
    have hcard := card_sup_mul_card_inf_of_le_normalizer (A := E₁) (B := E) hE_N
    rw [hdisj, Subgroup.card_bot, mul_one, hE₁c, hEc, ← pow_add] at hcard
    have hQa : IsElemAbelian 3 (E₁ ⊔ E) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hE₁a hEa fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 (hEC hb) a (hE₁L ha)
    have hQN : E₁ ⊔ E ≤ Subgroup.normalizer (T : Set G) :=
      sup_le hE₁N (y10x_le_normalizer_of_comm fun e he t ht =>
        (Subgroup.mem_centralizer_iff.1 (hEC he) t (hTL ht)).symm)
    have hup := CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes (p := 3) Nat.prime_three hT hT2 hQN
    rw [hG3] at hup
    have hlow := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_refl (E₁ ⊔ E)) hQa hcard
    omega
  have h5 : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G)) := by
    intro h5
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (L : Set G))) 5 h5
    have hc0 : (c : G) ∈ Subgroup.centralizer (L : Set G) := c.2
    have hzC5 : Subgroup.zpowers (c : G) ≤ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.2 hc0
    have hord : orderOf (c : G) = 5 := by rw [Subgroup.orderOf_coe, hc5]
    have hZ5 : IsElemAbelian 5 (Subgroup.zpowers (c : G)) :=
      CFSG.Open.isElemAbelian_zpowers (by rw [← hord, pow_orderOf_eq_one])
    obtain ⟨T, E₅, hT, hT2, hTL, hE₅L, hE₅a, hE₅c, hE₅N⟩ := y10x_attain (q := 5) (by norm_num) hcomm
    rw [hL5] at hE₅c
    have hdisj : E₅ ⊓ Subgroup.zpowers (c : G) = ⊥ := by
      rw [inf_comm]
      exact eq_bot_mono (inf_le_inf_left _ hE₅L) (y10x_inf_eq_bot hZ hzC5)
    have hN1 : Subgroup.zpowers (c : G) ≤ Subgroup.normalizer (E₅ : Set G) :=
      y10x_le_normalizer_of_comm fun e he t ht =>
        (Subgroup.mem_centralizer_iff.1 (hzC5 he) t (hE₅L ht)).symm
    have hcard := card_sup_mul_card_inf_of_le_normalizer (A := E₅) (B := Subgroup.zpowers (c : G)) hN1
    rw [hdisj, Subgroup.card_bot, mul_one, hE₅c, Nat.card_zpowers, hord, ← pow_succ] at hcard
    have hQa : IsElemAbelian 5 (E₅ ⊔ Subgroup.zpowers (c : G)) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hE₅a hZ5 fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 (hzC5 hb) a (hE₅L ha)
    have hQN : E₅ ⊔ Subgroup.zpowers (c : G) ≤ Subgroup.normalizer (T : Set G) :=
      sup_le hE₅N (y10x_le_normalizer_of_comm fun e he t ht =>
        (Subgroup.mem_centralizer_iff.1 (hzC5 he) t (hTL ht)).symm)
    have hup := CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes (p := 5) (by norm_num) hT hT2 hQN
    rw [hG5] at hup
    have hlow := CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) (le_refl (E₅ ⊔ Subgroup.zpowers (c : G))) hQa hcard
    omega
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer (L : Set G))) := by
    apply Nat.odd_iff.2
    have h2 : ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G)) := by
      intro h2
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (L : Set G))) 2 h2
      have ht0 : (t : G) ∈ Subgroup.centralizer (L : Set G) := t.2
      have hord : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
      have hT : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
      have hTne : Subgroup.zpowers (t : G) ≠ ⊥ := fun h => by
        have h1 := Subgroup.zpowers_eq_bot.1 h
        rw [h1, orderOf_one] at hord
        norm_num at hord
      have hFN : F ≤ Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) :=
        y10x_le_normalizer_of_comm fun e he s hs => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
          exact ((show Commute e (t : G) from Subgroup.mem_centralizer_iff.1 ht0 e (hFL he)).zpow_right k).eq
      have hup := CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes (p := 5) (by norm_num) hTne hT hFN
      rw [hG5] at hup
      have hlow := CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) (le_refl F) hFa hFc
      omega
    omega
  exact ⟨h3, h5, hodd⟩

private theorem y10x_conj_mem_centralizer {g x : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    {h : G} (hh : h ∈ Subgroup.centralizer ({x} : Set G)) :
    g * h * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
  have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  rw [inv_inv] at hk
  have hxg : x * g = g * x ^ k := by rw [hk]; group
  have hc : h * x ^ k = x ^ k * h := ((show Commute h x from hh).zpow_right k).eq
  calc g * h * g⁻¹ * x = g * h * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * h * x ^ k * g⁻¹ := by rw [hk]
    _ = g * (h * x ^ k) * g⁻¹ := by group
    _ = g * (x ^ k * h) * g⁻¹ := by rw [hc]
    _ = (g * x ^ k) * h * g⁻¹ := by group
    _ = x * g * h * g⁻¹ := by rw [hxg]
    _ = x * (g * h * g⁻¹) := by group

private theorem y10x_normalizer_centralizer {g x : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact y10x_conj_mem_centralizer hg hh
  · intro hh
    have h2 := y10x_conj_mem_centralizer (inv_mem hg) hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e] at h2
    exact h2

private theorem y10x_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hA h) (hB h)

private theorem y10x_comm_central {H : Type} [Group H] {A B u v : H}
    (hu_A : Commute u A) (hu_B : Commute u B) (hv_A : Commute v A) (hv_B : Commute v B) (huv : Commute u v) :
    ⁅u * A, v * B⁆ = ⁅A, B⁆ := by
  have hCu : Commute u ⁅A, B⁆ := by
    rw [commutatorElement_def]
    exact ((hu_A.mul_right hu_B).mul_right hu_A.inv_right).mul_right hu_B.inv_right
  have hCv : Commute v ⁅A, B⁆ := by
    rw [commutatorElement_def]
    exact ((hv_A.mul_right hv_B).mul_right hv_A.inv_right).mul_right hv_B.inv_right
  have h1 : ⁅u * A, v⁆ = 1 := commutatorElement_eq_one_iff_commute.2 (huv.mul_left hv_A.symm)
  have h2 : ⁅u * A, B⁆ = u * ⁅A, B⁆ * u⁻¹ := by
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_eq_one_iff_commute.2 hu_B, mul_one]
  rw [commutatorElement_mul_right_eq_mul_conj, h1, h2, one_mul, hCu.eq, mul_inv_cancel_right,
    hCv.eq, mul_inv_cancel_right]

private theorem y10x_cent_of_central_comm {K : Subgroup G} (hKq : commutator ↥K = ⊤) {g : G}
    (hz : ∀ j ∈ K, ⁅j, g⁆ ∈ K ∧ ∀ k ∈ K, ⁅j, g⁆ * k = k * ⁅j, g⁆) : ∀ j ∈ K, j * g = g * j := by
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ * g = g * ⁅a, b⁆ := by
    intro a ha b hb
    obtain ⟨hza, hzaK⟩ := hz a ha
    obtain ⟨hzb, hzbK⟩ := hz b hb
    have hga : g * a * g⁻¹ = ⁅a, g⁆⁻¹ * a := by
      rw [commutatorElement_def]; group
    have hgb : g * b * g⁻¹ = ⁅b, g⁆⁻¹ * b := by
      rw [commutatorElement_def]; group
    have hconj : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have hcA : Commute ⁅a, g⁆ a := hzaK a ha
    have hcB : Commute ⁅a, g⁆ b := hzaK b hb
    have hcA' : Commute ⁅b, g⁆ a := hzbK a ha
    have hcB' : Commute ⁅b, g⁆ b := hzbK b hb
    have hcAB : Commute ⁅a, g⁆ ⁅b, g⁆ := hzaK _ hzb
    have key : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
      rw [hconj, hga, hgb]
      exact y10x_comm_central hcA.inv_left hcB.inv_left hcA'.inv_left hcB'.inv_left hcAB.inv_left.inv_right
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  let S : Subgroup ↥K := (Subgroup.centralizer ({g} : Set G)).comap K.subtype
  have hS : commutator ↥K ≤ S := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    show ((⁅a, b⁆ : ↥K) : G) ∈ Subgroup.centralizer ({g} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : ((⁅a, b⁆ : ↥K) : G) = ⁅(a : G), (b : G)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc]
    exact hcomm a a.2 b b.2
  rw [hKq] at hS
  intro j hj
  exact Subgroup.mem_centralizer_singleton_iff.1 (hS (Subgroup.mem_top (⟨j, hj⟩ : ↥K)))

private theorem y10x_central_comm {K L' : Subgroup G} {p' : ℕ} (hp' : p'.Prime)
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hKL : K ≤ L') (hpK : p' ∣ Nat.card ↥K) {g : G}
    (hgcore : ∀ l ∈ L', ⁅l, g⁆ ∈ GLAPPrimeCoreOf p' L') (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    ∀ j ∈ K, ⁅j, g⁆ ∈ K ∧ ∀ k ∈ K, ⁅j, g⁆ * k = k * ⁅j, g⁆ := by
  have hOn : ∀ k ∈ L', ∀ n ∈ GLAPPrimeCoreOf p' L', k * n * k⁻¹ ∈ GLAPPrimeCoreOf p' L' := fun k hk n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p' L' hk) n).1 hn
  have hMn : ((K ⊓ GLAPPrimeCoreOf p' L').subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨K.mul_mem (K.mul_mem k.2 hn.1) (K.inv_mem k.2), hOn k (hKL k.2) _ hn.2⟩⟩
  have hMtop : (K ⊓ GLAPPrimeCoreOf p' L').subgroupOf K ≠ ⊤ := by
    intro htop
    apply not_dvd_card_glaPPrimeCoreOf hp' L'
    refine hpK.trans (Subgroup.card_dvd_of_le ?_)
    intro j hj
    have hmem : (⟨j, hj⟩ : ↥K) ∈ (K ⊓ GLAPPrimeCoreOf p' L').subgroupOf K := by
      rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).2
  have hcen := le_center_of_normal_of_isQuasisimple hKq hMn hMtop
  intro j hj
  have hzK : ⁅j, g⁆ ∈ K := by
    have h1 : g * j⁻¹ * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgK j⁻¹).1 (K.inv_mem hj)
    have h2 : ⁅j, g⁆ = j * (g * j⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]; exact K.mul_mem hj h1
  have hzO : ⁅j, g⁆ ∈ GLAPPrimeCoreOf p' L' := hgcore j (hKL hj)
  refine ⟨hzK, fun k hk => ?_⟩
  have hzM : (⟨⁅j, g⁆, hzK⟩ : ↥K) ∈ (K ⊓ GLAPPrimeCoreOf p' L').subgroupOf K :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hzK, hzO⟩)
  have hc := Subgroup.mem_center_iff.1 (hcen hzM) ⟨k, hk⟩
  exact (congrArg Subtype.val hc).symm

theorem u64_normN_le (h6 : U6StructAt G) (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L)
    (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L') (hU : LabelOf L ⟨.twA, 5, 2⟩)
    (hp3 : p = 3) (hp5 : p' = 5) :
    ∀ g ∈ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G),
      g ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G) := by
  subst hp5
  intro g hg
  obtain ⟨hgAB, hgZ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgcm, -⟩ := Subgroup.mem_inf.1 hgAB
  have hgN : g ∈ Subgroup.normalizer (L' : Set G) := (mem_centModSubgroup.1 hgcm).1
  have hgcore : ∀ l ∈ L', ⁅l, g⁆ ∈ GLAPPrimeCoreOf 5 L' := (mem_centModSubgroup.1 hgcm).2
  have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
    y10x_normalizer_centralizer hgZ
  obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf p hR.1
  have hc6 : S6Ctx G p := S6Ctx.of_ctx hctx hR.1 h3 h4o h4 h5
  have hLlay : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := sstarMax_layer_eq hc6 hR.2.1
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := by
    have h := mem_normalizer_glaPLayer (p := p) hgC
    rwa [hLlay] at h
  have hgLC : g ∈ Subgroup.normalizer ((L' ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    y10x_normalizer_inf hgN hgC
  have hgJn : g ∈ Subgroup.normalizer (GLAPLayer p (L' ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) :=
    mem_normalizer_glaPLayer (p := p) hgLC
  rw [hc117.J_layer.1] at hgJn
  have hJL : J ≤ L' := hc117.J_le
  obtain ⟨-, -, hJq⟩ := hc.cfg.comp.1
  have hp5' : (5 : ℕ).Prime := by norm_num
  have hpJ : 5 ∣ Nat.card ↥J :=
    ((dvd_mul_left 5 p).trans hc.cfg.dvd).trans (Subgroup.card_quotient_dvd_card _)
  have hcent : ∀ j ∈ J, j * g = g * j :=
    y10x_cent_of_central_comm hJq.1 (y10x_central_comm hp5' hJq hJL hpJ hgcore hgJn)
  have hgCJ : g ∈ Subgroup.centralizer (J : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => hcent h hh)
  have hx'L : x' ∈ L := hc.cfg.le hc.cfg.mem
  haveI : Fact (Nat.Prime 5) := ⟨hp5'⟩
  have hord : orderOf x' = 5 := orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one
  obtain ⟨a, ha, hcon⟩ := h6.cent L J x' g hU hx'L hord hc.cfg.comp.2 (u64_labelJ h6 hc hU) hgL hgCJ
  have hgc : g * a⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hcon l hl
    calc l * (g * a⁻¹) = g * (g⁻¹ * l * g) * a⁻¹ := by group
      _ = g * (a⁻¹ * l * a) * a⁻¹ := by rw [h]
      _ = g * a⁻¹ * l := by group
  have hfin := Subgroup.mul_mem _ (Subgroup.mem_sup_right hgc) (Subgroup.mem_sup_left ha)
  rwa [inv_mul_cancel_right] at hfin

private theorem y10x_cent_zpowers {c x : G} (h : c * x = x * c) :
    c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact ((show Commute c x from h).zpow_right k).eq.symm

private theorem y10x_conj_mem_centralizer_set {S : Set G} {a h : G}
    (ha : a ∈ Subgroup.centralizer S) (hh : h ∈ Subgroup.centralizer S) :
    a * h * a⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at ha hh ⊢
  intro s hs
  have e1 : s * a = a * s := ha s hs
  have e2 : s * h = h * s := hh s hs
  have e3 : s * a⁻¹ = a⁻¹ * s := (show Commute s a from e1).inv_right.eq
  calc s * (a * h * a⁻¹) = (s * a) * h * a⁻¹ := by group
    _ = (a * s) * h * a⁻¹ := by rw [e1]
    _ = a * (s * h) * a⁻¹ := by group
    _ = a * (h * s) * a⁻¹ := by rw [e2]
    _ = a * h * (s * a⁻¹) := by group
    _ = a * h * (a⁻¹ * s) := by rw [e3]
    _ = (a * h * a⁻¹) * s := by group

private theorem y10x_normalizer_centralizer_set {S : Set G} {a : G} (ha : a ∈ Subgroup.centralizer S) :
    a ∈ Subgroup.normalizer (Subgroup.centralizer S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact y10x_conj_mem_centralizer_set ha hh
  · intro hh
    have h2 := y10x_conj_mem_centralizer_set (inv_mem ha) hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h2

private theorem y10x_core_le_centMod (q : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf q X ≤ centModSubgroup q X := by
  intro o ho
  have hoX : o ∈ X := by
    unfold GLAPPrimeCoreOf at ho
    exact Subgroup.map_subtype_le _ ho
  refine mem_centModSubgroup.2 ⟨Subgroup.le_normalizer hoX, fun l hl => ?_⟩
  have h1 : l * o * l⁻¹ ∈ GLAPPrimeCoreOf q X :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf q X hl) o).1 ho
  have e : ⁅l, o⁆ = (l * o * l⁻¹) * o⁻¹ := by rw [commutatorElement_def]
  rw [e]
  exact (GLAPPrimeCoreOf q X).mul_mem h1 ((GLAPPrimeCoreOf q X).inv_mem ho)

open scoped Pointwise in
private theorem y10x_exists_conj_sylow {q : ℕ} (hq : q.Prime) {Y : Subgroup G} (Q : Sylow q Y)
    {S : Subgroup G} (hSY : S ≤ Y) (hS : IsPGroup q S) :
    ∃ g : Y, ∀ s ∈ S, ∃ t ∈ (Q : Subgroup Y), (t : G) = (g : G) * s * (g : G)⁻¹ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hS' : IsPGroup q (S.subgroupOf Y) := hS.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hS'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q₀ Q
  have hconj : MulAut.conj g • (Q₀ : Subgroup Y) = (Q : Subgroup Y) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  refine ⟨g, fun s hs => ?_⟩
  have hsQ₀ : (⟨s, hSY hs⟩ : Y) ∈ Q₀ := hQ₀ (Subgroup.mem_subgroupOf.2 hs)
  have hmem := Subgroup.smul_mem_pointwise_smul (⟨s, hSY hs⟩ : Y) (MulAut.conj g) _ hsQ₀
  rw [hconj] at hmem
  exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩

private theorem y10x_cyc_of_max {Y P : Subgroup G} (hPY : P ≤ Y) (hP5 : IsPGroup 5 P) (hPc : IsCyclic ↥P)
    (hPmax : ∀ Q : Subgroup G, Q ≤ Y → IsPGroup 5 Q → P ≤ Q → Q = P)
    {S : Subgroup G} (hSY : S ≤ Y) (hS5 : IsPGroup 5 S) : IsCyclic ↥S := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP' : IsPGroup 5 (P.subgroupOf Y) := hP5.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hP'.exists_le_sylow
  have hQ₀P : (Q₀ : Subgroup Y).map Y.subtype = P := by
    apply hPmax
    · exact Subgroup.map_subtype_le _
    · exact Q₀.isPGroup'.map Y.subtype
    · intro p hp
      exact ⟨⟨p, hPY hp⟩, hQ₀ (Subgroup.mem_subgroupOf.2 hp), rfl⟩
  obtain ⟨g, hg⟩ := y10x_exists_conj_sylow Nat.prime_five Q₀ hSY hS5
  let φ : S →* ((Q₀ : Subgroup Y).map Y.subtype) :=
    MonoidHom.codRestrict ((MulAut.conj (g : G)).toMonoidHom.comp S.subtype)
      ((Q₀ : Subgroup Y).map Y.subtype) fun s => by
        obtain ⟨t, htQ, ht⟩ := hg s s.2
        exact ⟨t, htQ, by simpa [MulAut.conj_apply] using ht⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg (fun x : (Q₀ : Subgroup Y).map Y.subtype => (x : G)) hab
    simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype] at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  have hcyc : IsCyclic ↥((Q₀ : Subgroup Y).map Y.subtype) := by
    rw [hQ₀P]; exact hPc
  exact isCyclic_of_injective φ hφ

private theorem y10x_exists_E25 {C : Subgroup G} (hC : IsPGroup 5 C) (hnc : ¬ IsCyclic ↥C) :
    ∃ E : Subgroup G, E ≤ C ∧ IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (IsPGroup 5 ↥C) := ⟨hC⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 5) (by norm_num) hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian 5 (S.map C.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine ⟨S.map C.subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 _).mp hSm
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hScard]

private theorem y10x_five_dvd_cube_sub {j : ℕ} {u : ℤ} (h : (5 : ℤ) ^ j ∣ u * u * u - 1) :
    (5 : ℤ) ^ j ∣ u - 1 := by
  have hfac : u * u * u - 1 = (u - 1) * (u ^ 2 + u + 1) := by ring
  have hs : ¬ (5 : ℤ) ∣ u ^ 2 + u + 1 := by
    intro h5
    have key : ∀ z : ZMod 5, z ^ 2 + z + 1 ≠ 0 := by decide
    apply key (u : ZMod 5)
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u ^ 2 + u + 1) 5).2 (by exact_mod_cast h5)
    push_cast at this
    exact this
  have hprime : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.2 (by norm_num)
  have hcop : IsCoprime (5 : ℤ) (u ^ 2 + u + 1) := (hprime.irreducible.coprime_iff_not_dvd).2 hs
  rw [hfac] at h
  exact (hcop.pow_left).dvd_of_dvd_mul_right h

private theorem y10x_cyc_cent {x : G} (hx3 : x ^ 3 = 1) {C : Subgroup G} (hC5 : IsPGroup 5 C)
    (hCc : IsCyclic ↥C) (hxN : x ∈ Subgroup.normalizer (C : Set G)) :
    C ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hgen : ∀ y ∈ C, y ∈ Subgroup.zpowers (g : G) := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  set c : G := (g : G) with hcdef
  have hcC : c ∈ C := g.2
  obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.1
    (hgen _ ((Subgroup.mem_normalizer_iff.1 hxN c).1 hcC))
  have h2 : x * (c ^ u) * x⁻¹ = c ^ (u * u) := by
    rw [← conj_zpow, ← hu, ← zpow_mul]
  have h3 : x * (c ^ (u * u)) * x⁻¹ = c ^ (u * u * u) := by
    rw [← conj_zpow, ← hu, ← zpow_mul]
    congr 1
    ring
  have hxxx : x * x * x = 1 := by
    have : x ^ 3 = x * x * x := by simp [pow_three, mul_assoc]
    rw [← this, hx3]
  have h4 : x * (x * (x * c * x⁻¹) * x⁻¹) * x⁻¹ = c := by
    have e : x * (x * (x * c * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * c * (x * x * x)⁻¹ := by group
    rw [e, hxxx]; group
  rw [← hu, h2, h3] at h4
  have hpow : c ^ (u * u * u - 1) = 1 := by
    rw [zpow_sub, h4, zpow_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hC5 ⟨c, hcC⟩
  have hck : c ^ (5 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hck)
  have hdvd : (5 : ℤ) ^ j ∣ u * u * u - 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := u * u * u - 1)).2 hpow
    rw [hj] at this
    exact_mod_cast this
  have hdvd' := y10x_five_dvd_cube_sub hdvd
  have hcu : c ^ (u - 1) = 1 := by
    have : (orderOf c : ℤ) ∣ u - 1 := by rw [hj]; exact_mod_cast hdvd'
    exact orderOf_dvd_iff_zpow_eq_one.1 this
  have hcx : c ^ u = c := by
    have : c ^ u = c ^ (u - 1) * c := by rw [← zpow_add_one]; congr 1; ring
    rw [this, hcu, one_mul]
  have hxc : x * c * x⁻¹ = c := by rw [← hu, hcx]
  have hcx' : c * x = x * c := by
    calc c * x = (x * c * x⁻¹) * x := by rw [hxc]
      _ = x * c := by group
  intro y hy
  obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen y hy)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((show Commute c x from hcx').zpow_left k').eq

theorem u64_cyc_of_P (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hp3 : p = 3) (hp5 : p' = 5) (hxL : x' ∈ L') {P : Subgroup G}
    (hP : P ≤ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G)) (hP5 : IsPGroup p' P)
    (hPmax : ∀ Q : Subgroup G, Q ≤ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) → IsPGroup p' Q → P ≤ Q → Q = P)
    (hPB : B' ≤ Subgroup.normalizer (P : Set G)) (hPx : x ∈ Subgroup.normalizer (P : Set G))
    (hPc : P ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x') : CycModSylow p' L' := by
  subst hp3 hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH := rquad_hyp hsf hR
  have hx3 : x ^ 3 = 1 := hH.elem.2 x hH.mem
  have hxne : x ≠ 1 := hH.ne_one
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.comp.1
  have hB'L : B' ≤ L := hc.cfg.le
  have hB5 : IsPGroup 5 B' := isPGroup_of_isElemAbelian hc.cfg.elem
  have hxB' : x ∈ Subgroup.centralizer (B' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLx (hB'L hb))
  have hord3 : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) 5 := by
    rw [Nat.card_zpowers, hord3]; norm_num
  have hcommB : ⁅Subgroup.zpowers x, B'⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.zpowers_le.2 hxB')
  have hx'ord : orderOf x' = 5 := orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one
  have hx'card : Nat.card (Subgroup.zpowers x') = 5 := by rw [Nat.card_zpowers, hx'ord]
  have hcentle : centModSubgroup 5 L' ≤ Subgroup.centralizer ({x'} : Set G) :=
    centMod_le_centralizer_of_mem Nat.prime_five hxL
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl)) hx'ord
  have hG5 : GLATwoLocalRank 5 G = m := by
    have h := hc.mu
    simp only [Mu, Set.mem_setOf_eq] at h
    exact h.2.1
  have hm4 : 4 ≤ m := hctx.1.four_le
  have hcardB : Nat.card B' = 5 ^ m := by rw [hc.cfg.rank_B, hc.e_eq]
  have hPcyc : IsCyclic ↥P := by
    by_contra hPnc
    have hPnotx : ¬ P ≤ Subgroup.centralizer ({x} : Set G) := by
      intro hle
      apply hPnc
      have hPeq : P = Subgroup.zpowers x' := by rw [← hPc, inf_eq_left.2 hle]
      rw [hPeq]
      infer_instance
    have hCnot : ¬ (P ⊓ Subgroup.centralizer (B' : Set G) ≤ Subgroup.centralizer ({x} : Set G)) := by
      intro hCle
      have hfix : P ⊓ Subgroup.centralizer (B' : Set G) ≤
          Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
        fun c hc' => y10x_cent_zpowers (Subgroup.mem_centralizer_singleton_iff.1 (hCle hc'))
      have hPle := CFSG.Goldschmidt.N10 G P (Subgroup.zpowers x) B' hP5 hcop hB5
        (Subgroup.zpowers_le.2 hPx) hPB hcommB hfix
      apply hPnotx
      intro p0 hp0
      have := Subgroup.mem_centralizer_iff.1 (hPle hp0) x (Subgroup.mem_zpowers x)
      exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
    have hCnc : ¬ IsCyclic ↥(P ⊓ Subgroup.centralizer (B' : Set G)) := by
      intro hCc
      apply hCnot
      have hxN : x ∈ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B' : Set G) : Subgroup G) : Set G) :=
        y10x_normalizer_inf hPx (y10x_normalizer_centralizer_set hxB')
      exact y10x_cyc_cent hx3 (hP5.to_le inf_le_left) hCc hxN
    obtain ⟨E, hEC, hEa, hEc⟩ := y10x_exists_E25 (hP5.to_le inf_le_left) hCnc
    have hEP : E ≤ P := hEC.trans inf_le_left
    have hEB : ∀ e ∈ E, ∀ b ∈ B', b * e = e * b := fun e he b hb =>
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hEC he)).2 b hb
    obtain ⟨S, hSJ, hS2, hBS, hBSc⟩ := hc.cfg.eight
    have hSne : S ≠ ⊥ := by
      rintro rfl
      have hB'le : B' ≤ Subgroup.zpowers x' := by
        rw [← hBSc]
        refine le_inf le_rfl fun b _ => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain rfl := Subgroup.mem_bot.1 (show h ∈ (⊥ : Subgroup G) from hh)
        simp
      have h1 := Subgroup.card_le_of_le hB'le
      rw [hx'card, hcardB] at h1
      have h625 : 5 ^ 4 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
      norm_num at h625
      omega
    have hBL'N : B' ≤ Subgroup.normalizer (L' : Set G) :=
      bstar_norm hc hc117.comp' hc117.J_le hc117.uniq
    have hAO : B' ≤ Subgroup.normalizer (GLAPPrimeCoreOf 5 L' : Set G) := fun b hb =>
      CFSG.HardMathSupport.Solomon.LocalBalance.normalizer_le_normalizer_glaPPrimeCoreOf 5 L' (hBL'N hb)
    have hEO : E ≤ Subgroup.normalizer (GLAPPrimeCoreOf 5 L' : Set G) := fun e he =>
      CFSG.HardMathSupport.Solomon.LocalBalance.normalizer_le_normalizer_glaPPrimeCoreOf 5 L'
        (mem_centModSubgroup.1 (hP (hEP he)).1).1
    have hSO : S ≤ Subgroup.normalizer (GLAPPrimeCoreOf 5 L' : Set G) := fun s hs =>
      CFSG.HardMathSupport.Solomon.LocalBalance.normalizer_le_normalizer_glaPPrimeCoreOf 5 L'
        (Subgroup.le_normalizer (hc117.J_le (hSJ hs)))
    have hO : ¬ 5 ∣ Nat.card ↥(GLAPPrimeCoreOf 5 L') := not_dvd_card_glaPPrimeCoreOf Nat.prime_five L'
    have hAE : ∀ a ∈ B', ∀ e ∈ E, ⁅a, e⁆ ∈ GLAPPrimeCoreOf 5 L' := fun a ha e he => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (hEB e he a ha)]
      exact (GLAPPrimeCoreOf 5 L').one_mem
    have hES : ∀ e ∈ E, ∀ s ∈ S, ⁅s, e⁆ ∈ GLAPPrimeCoreOf 5 L' := fun e he s hs =>
      (mem_centModSubgroup.1 (hP (hEP he)).1).2 s (hc117.J_le (hSJ hs))
    have hrank := rank_lift (q := 5) (by norm_num) (by norm_num) hO hAO hEO hSO hc.cfg.elem hEa hAE hS2 hSne
      hBS hES
    have hEcm : E ≤ centModSubgroup 5 L' := fun e he => (Subgroup.mem_inf.1 (hP (hEP he))).1
    have hEOc : E ⊔ GLAPPrimeCoreOf 5 L' ≤ centModSubgroup 5 L' := sup_le hEcm (y10x_core_le_centMod 5 L')
    have hsub : B' ⊓ (E ⊔ GLAPPrimeCoreOf 5 L') ≤ Subgroup.zpowers x' := by
      intro b hb
      obtain ⟨hbB, hbE⟩ := Subgroup.mem_inf.1 hb
      exact (centMod_eq_zpowers_of_cfg hc hc117 b hbB).1 (centMod_iff.2 (hEOc hbE))
    have hk := Subgroup.card_le_of_le hsub
    rw [hx'card] at hk
    rw [hcardB, hEc, hG5] at hrank
    have hpos : 0 < 5 ^ m := by positivity
    have hk5 : Nat.card ↥(B' ⊓ (E ⊔ GLAPPrimeCoreOf 5 L')) * 5 ^ m ≤ 5 * 5 ^ m :=
      Nat.mul_le_mul_right _ hk
    have hfin := le_trans hrank hk5
    have h25 : (5 : ℕ) ^ m * 5 ^ 2 = 25 * 5 ^ m := by ring
    rw [h25] at hfin
    linarith
  have hPY : P ≤ centModSubgroup 5 L' := hP.trans inf_le_left
  have hcentle : centModSubgroup 5 L' ≤ Subgroup.centralizer ({x'} : Set G) :=
    centMod_le_centralizer_of_mem Nat.prime_five hxL
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl)) hx'ord
  have hPmax' : ∀ Q : Subgroup G, Q ≤ centModSubgroup 5 L' → IsPGroup 5 Q → P ≤ Q → Q = P :=
    fun Q hQ hQ5 hPQ => hPmax Q (le_inf hQ (hQ.trans hcentle)) hQ5 hPQ
  intro S' hS' hS'5
  exact y10x_cyc_of_max hPY hP5 hPcyc hPmax' (fun g hg => centMod_iff.1 (hS' g hg)) hS'5


private theorem y10x_mem_sup_of_normalizes {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) {g : G} (hg : g ∈ N ⊔ Subgroup.zpowers x) :
    ∃ n ∈ N, ∃ k : ℤ, g = n * x ^ k := by
  have hconj : ∀ k : ℤ, ∀ n ∈ N, x ^ k * n * (x ^ k)⁻¹ ∈ N := fun k n hn =>
    (Subgroup.mem_normalizer_iff.1 (zpow_mem hx k) n).1 hn
  let W : Subgroup G :=
    { carrier := {g | ∃ n ∈ N, ∃ k : ℤ, g = n * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨n1, hn1, k1, rfl⟩ ⟨n2, hn2, k2, rfl⟩
        refine ⟨n1 * (x ^ k1 * n2 * (x ^ k1)⁻¹), N.mul_mem hn1 (hconj k1 n2 hn2), k1 + k2, ?_⟩
        rw [zpow_add]
        group
      one_mem' := ⟨1, N.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, hn, k, rfl⟩
        refine ⟨x ^ (-k) * n⁻¹ * (x ^ (-k))⁻¹, hconj (-k) n⁻¹ (N.inv_mem hn), -k, ?_⟩
        group }
  have hle : N ⊔ Subgroup.zpowers x ≤ W :=
    sup_le (fun n hn => ⟨n, hn, 0, by simp⟩) (Subgroup.zpowers_le.2 ⟨1, N.one_mem, 1, by simp⟩)
  exact hle hg

private theorem y10x_cent_normalizes_zpowers {c x : G} (h : c * x = x * c) :
    c ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hcomm : ∀ k : ℤ, c * x ^ k = x ^ k * c := fun k => ((show Commute c x from h).zpow_right k).eq
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have e1 : c * x ^ k * c⁻¹ = x ^ k := by rw [hcomm k]; group
    rw [e1]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  · intro hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : c⁻¹ * x ^ k * c = x ^ k := by
      calc c⁻¹ * x ^ k * c = c⁻¹ * (x ^ k * c) := by group
        _ = c⁻¹ * (c * x ^ k) := by rw [hcomm k]
        _ = x ^ k := by group
    have h2 : w = c⁻¹ * (c * w * c⁻¹) * c := by group
    rw [h2, ← hk, h1]

private theorem y10x_normalizer_cent_of_mem {L : Subgroup G} {a : G} (ha : a ∈ L) :
    a ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  have key : ∀ b ∈ L, ∀ c ∈ Subgroup.centralizer (L : Set G), b * c * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro b hb c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro l hl
    have hm : b⁻¹ * l * b ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hb) hl) hb
    have hmc := hc _ hm
    calc l * (b * c * b⁻¹) = b * ((b⁻¹ * l * b) * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * l * b)) * b⁻¹ := by rw [hmc]
      _ = b * c * b⁻¹ * l := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact key a ha c hc
  · intro hc
    have := key a⁻¹ (L.inv_mem ha) _ hc
    have e : a⁻¹ * (a * c * a⁻¹) * a⁻¹⁻¹ = c := by group
    rwa [e] at this

private theorem y10x_zpow_five {x' : G} (hord : orderOf x' = 5) : x' ^ (5 : ℤ) = 1 := by
  rw [zpow_ofNat]
  have := pow_orderOf_eq_one x'
  rw [hord] at this
  exact this

private theorem y10x_zpowers_inf_cent_bot {L : Subgroup G} {x' : G}
    (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord : orderOf x' = 5) :
    Subgroup.zpowers x' ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun a ha => ?_
  obtain ⟨hax, haC⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hax
  rw [Subgroup.mem_bot]
  by_contra hne
  have h5 : (x' ^ k) ^ 5 = 1 := by
    have e1 : (x' ^ k) ^ 5 = (x' ^ (5 : ℤ)) ^ k := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e1, y10x_zpow_five hord, one_zpow]
  have hdvd : orderOf (x' ^ k) ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hord5 : orderOf (x' ^ k) = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hdvdC : orderOf (x' ^ k) ∣ Nat.card ↥(Subgroup.centralizer (L : Set G)) := by
    have := orderOf_dvd_natCard (⟨x' ^ k, haC⟩ : ↥(Subgroup.centralizer (L : Set G)))
    rwa [Subgroup.orderOf_mk] at this
  exact hZ (hord5 ▸ hdvdC)

private theorem y10x_card_K {L : Subgroup G} {x' : G} (hx'L : x' ∈ L)
    (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord : orderOf x' = 5) :
    Nat.card ↥(Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G)) =
      5 * Nat.card ↥(Subgroup.centralizer (L : Set G)) := by
  have hB : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers x' : Set G) := fun c hc =>
    y10x_cent_normalizes_zpowers (Subgroup.mem_centralizer_iff.1 hc x' hx'L).symm
  have hA := card_sup_mul_card_inf_of_le_normalizer (A := Subgroup.zpowers x')
    (B := Subgroup.centralizer (L : Set G)) hB
  rw [y10x_zpowers_inf_cent_bot hZ hord, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord] at hA
  exact hA

private theorem y10x_three_mem_cent {L : Subgroup G} {x' g : G} (hx'L : x' ∈ L)
    (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord : orderOf x' = 5)
    (hg : g ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G)) (j : ℕ) (hj : g ^ 3 ^ j = 1) :
    g ∈ Subgroup.centralizer (L : Set G) := by
  rw [sup_comm] at hg
  obtain ⟨c, hc, k, rfl⟩ := y10x_mem_sup_of_normalizes (y10x_normalizer_cent_of_mem hx'L) hg
  have hmem : x' ^ k ∈ L := zpow_mem hx'L k
  have hcom : Commute c (x' ^ k) := (Subgroup.mem_centralizer_iff.1 hc (x' ^ k) hmem).symm
  have hpow : c ^ 3 ^ j * (x' ^ k) ^ 3 ^ j = 1 := by
    rw [← hcom.mul_pow]; exact hj
  have ha_eq : (x' ^ k) ^ 3 ^ j = (c ^ 3 ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hpow
  have ha_bot : (x' ^ k) ^ 3 ^ j ∈ Subgroup.zpowers x' ⊓ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x') k) _, ?_⟩
    rw [ha_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc _)
  rw [y10x_zpowers_inf_cent_bot hZ hord, Subgroup.mem_bot] at ha_bot
  have hdvd : (5 : ℤ) ∣ k * (3 : ℤ) ^ j := by
    have h := ha_bot
    rw [← zpow_natCast, ← zpow_mul] at h
    have h2 := (orderOf_dvd_iff_zpow_eq_one (x := x') (i := k * ((3 ^ j : ℕ) : ℤ))).2 h
    rw [hord] at h2
    push_cast at h2
    exact h2
  have hcop5 : IsCoprime (5 : ℤ) ((3 : ℤ) ^ j) :=
    IsCoprime.pow_right (Int.isCoprime_iff_gcd_eq_one.2 (by norm_num))
  obtain ⟨t, rfl⟩ := hcop5.dvd_of_dvd_mul_right hdvd
  have hxk : x' ^ (5 * t) = 1 := by rw [zpow_mul, y10x_zpow_five hord, one_zpow]
  rw [hxk, mul_one]
  exact hc


private theorem y10x_exists_E_sq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {C : Subgroup G} (hC : IsPGroup p C)
    (hnc : ¬ IsCyclic ↥C) : ∃ E : Subgroup G, E ≤ C ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact (IsPGroup p ↥C) := ⟨hC⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := p) hp2 hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian p (S.map C.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine ⟨S.map C.subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hSm
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hScard]

private theorem y10x_cyclic_of_pRank {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {C : Subgroup G}
    (hrk : CFSG.Open.pRank p C ≤ 1) {S : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup p S) : IsCyclic ↥S := by
  by_contra hnc
  obtain ⟨E, hES, hEa, hEc⟩ := y10x_exists_E_sq hp2 hS hnc
  have h2 := CFSG.SectionRank.le_pRank hp.out.one_lt (hES.trans hSC) hEa hEc
  omega

private theorem y10x_sup_K {L M : Subgroup G} {x x' : G} (hxN : x ∈ Subgroup.normalizer (M : Set G))
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (h1 : ∀ n ∈ M, n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) → n ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))
    {g : G} (hg : g ∈ M ⊔ Subgroup.zpowers x) (hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    g ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨n, hn, k, rfl⟩ := y10x_mem_sup_of_normalizes hxN hg
  have hxk : x ^ k ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    zpow_mem (Subgroup.le_normalizer (Subgroup.mem_zpowers x)) k
  have hnN : n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have := (Subgroup.normalizer (Subgroup.zpowers x : Set G)).mul_mem hgN (inv_mem hxk)
    simpa using this
  have hxkC : x ^ k ∈ Subgroup.centralizer (L : Set G) := zpow_mem hxC k
  exact Subgroup.mul_mem _ (h1 n hn hnN) (Subgroup.mem_sup_right hxkC)

private theorem y10x_three_sub {L : Subgroup G} {x' : G} (hx'L : x' ∈ L)
    (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord : orderOf x' = 5) {S : Subgroup G}
    (hS : S ≤ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G)) (hS3 : IsPGroup 3 S) :
    S ≤ Subgroup.centralizer (L : Set G) := by
  intro g hg
  obtain ⟨j, hj⟩ := hS3 ⟨g, hg⟩
  have hj' : g ^ 3 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  exact y10x_three_mem_cent hx'L hZ hord (hS hg) j hj'

private theorem y10x_cyc_three_sub_centx {L M : Subgroup G} {x x' : G} (hx'L : x' ∈ L)
    (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord' : orderOf x' = 5) (hxN : x ∈ Subgroup.normalizer (M : Set G))
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (h1 : ∀ n ∈ M, n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) → n ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))
    (hrk : CFSG.Open.pRank 3 (Subgroup.centralizer (L : Set G)) ≤ 1)
    {S : Subgroup G} (hS : S ≤ (M ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G))
    (hS3 : IsPGroup 3 S) : IsCyclic ↥S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSK : S ≤ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G) := by
    intro g hg
    obtain ⟨hgM, hgC⟩ := Subgroup.mem_inf.1 (hS hg)
    exact y10x_sup_K hxN hxC h1 hgM (y10x_cent_normalizes_zpowers (Subgroup.mem_centralizer_singleton_iff.1 hgC))
  have hSC := y10x_three_sub hx'L hZ hord' hSK hS3
  exact y10x_cyclic_of_pRank (p := 3) (by norm_num) hrk hSC hS3

private theorem y10x_mem_zpowers_of_orderOf_eq {C : Subgroup G} [IsCyclic C] {y z : G} (hyC : y ∈ C)
    (hzC : z ∈ C) (hord : orderOf y = orderOf z) : z ∈ Subgroup.zpowers y := by
  have heq : Subgroup.zpowers (⟨y, hyC⟩ : C) = Subgroup.zpowers (⟨z, hzC⟩ : C) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk,
      Subgroup.orderOf_mk]
    exact hord
  have hz : (⟨z, hzC⟩ : C) ∈ Subgroup.zpowers (⟨y, hyC⟩ : C) := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩

private theorem y10x_transfer {q : ℕ} (hq : q.Prime) {Y : Subgroup G} {y : G} (hy : y ∈ Y)
    (hyq : orderOf y = q)
    (h : ∀ S : Subgroup G, S ≤ Y ⊓ Subgroup.centralizer ({y} : Set G) → IsPGroup q S → IsCyclic S) :
    ∀ S : Subgroup G, S ≤ Y → IsPGroup q S → IsCyclic S := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hzp : IsPGroup q (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyq, pow_one])
  obtain ⟨Q, hQ⟩ := (hzp.comap_subtype (K := Y)).exists_le_sylow
  have hQ'p : IsPGroup q ((Q : Subgroup Y).map Y.subtype) := Q.isPGroup'.map Y.subtype
  have hQ'Y : (Q : Subgroup Y).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
  have hyQ' : y ∈ (Q : Subgroup Y).map Y.subtype :=
    ⟨⟨y, hy⟩, hQ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers y)), rfl⟩
  have hQ'cyc : IsCyclic ((Q : Subgroup Y).map Y.subtype) := by
    set Q' : Subgroup G := (Q : Subgroup Y).map Y.subtype with hQ'
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hyq
      exact hq.one_lt.ne hyq
    haveI : Nontrivial Q' := ⟨⟨⟨y, hyQ'⟩, 1, fun h' => hy1 (congrArg Subtype.val h')⟩⟩
    haveI : Nontrivial (Subgroup.center Q') := hQ'p.center_nontrivial
    have hZp : IsPGroup q (Subgroup.center Q') := hQ'p.to_subgroup _
    have hdvd : q ∣ Nat.card (Subgroup.center Q') := by
      obtain ⟨n, hn0, hn⟩ := hZp.nontrivial_iff_card.1 inferInstance
      rw [hn]
      exact dvd_pow_self q hn0.ne'
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' q hdvd
    have hzQ' : ((ζ : Q') : G) ∈ Q' := (ζ : Q').2
    have hzord : orderOf ((ζ : Q') : G) = q := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hζ]
    have hzcomm : ∀ w ∈ Q', w * ((ζ : Q') : G) = ((ζ : Q') : G) * w := by
      intro w hw
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ζ.2 ⟨w, hw⟩)
    have hzcent : ((ζ : Q') : G) ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact hzcomm u hyQ'
    haveI hCcyc : IsCyclic ↥(Q' ⊓ Subgroup.centralizer ({y} : Set G)) :=
      h _ (inf_le_inf_right _ hQ'Y) (hQ'p.to_le inf_le_left)
    have hyC : y ∈ Q' ⊓ Subgroup.centralizer ({y} : Set G) :=
      ⟨hyQ', Subgroup.mem_centralizer_iff.2 fun u hu => by
        rw [Set.mem_singleton_iff] at hu
        rw [hu]⟩
    have hzC : ((ζ : Q') : G) ∈ Q' ⊓ Subgroup.centralizer ({y} : Set G) := ⟨hzQ', hzcent⟩
    have hy_mem : y ∈ Subgroup.zpowers ((ζ : Q') : G) :=
      y10x_mem_zpowers_of_orderOf_eq hzC hyC (hzord.trans hyq.symm)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy_mem
    have hQ'cent : Q' ≤ Subgroup.centralizer ({y} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      rw [← hn]
      exact (Commute.zpow_left (Commute.symm (hzcomm w hw)) n).eq
    exact h Q' (le_inf hQ'Y hQ'cent) hQ'p
  intro S hSY hSp
  obtain ⟨g, hg⟩ := y10x_exists_conj_sylow hq Q hSY hSp
  let φ : S →* ((Q : Subgroup Y).map Y.subtype) :=
    MonoidHom.codRestrict ((MulAut.conj (g : G)).toMonoidHom.comp S.subtype)
      ((Q : Subgroup Y).map Y.subtype) fun s => by
        obtain ⟨t, htQ, ht⟩ := hg s s.2
        exact ⟨t, htQ, by simpa [MulAut.conj_apply] using ht⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg (fun x : (Q : Subgroup Y).map Y.subtype => (x : G)) hab
    simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype] at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  exact isCyclic_of_injective φ hφ


private theorem y10x_orderOf_conj (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using h

private theorem y10x_three_pow_dvd_sub {a q : ℕ} {u : ℤ} (hq : Odd q) (h3 : ¬ 3 ∣ q)
    (h : (3 : ℤ) ^ a ∣ u ^ q - 1) : (3 : ℤ) ^ a ∣ u - 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  haveI : NeZero (3 ^ a) := ⟨by positivity⟩
  have hu : ((u : ZMod (3 ^ a))) ^ q = 1 := by
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (u ^ q - 1) (3 ^ a)).2 (by exact_mod_cast h)
    push_cast at h'
    exact sub_eq_zero.1 h'
  have hq0 : q ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hq)
  have hunit : IsUnit (u : ZMod (3 ^ a)) :=
    isUnit_iff_exists_inv.2 ⟨(u : ZMod (3 ^ a)) ^ (q - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hq0), hu]⟩
  set U := hunit.unit with hUdef
  have hUq : U ^ q = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hUdef, IsUnit.unit_spec, Units.val_one, hu]
  have hq1 : orderOf U ∣ q := orderOf_dvd_of_pow_eq_one hUq
  have hφ : orderOf U ∣ Nat.totient (3 ^ a) := orderOf_dvd_of_pow_eq_one (ZMod.pow_totient U)
  have hcop : Nat.Coprime q (Nat.totient (3 ^ a)) := by
    rw [Nat.totient_prime_pow Nat.prime_three ha]
    have h2 : ¬ 2 ∣ q := by have := Nat.odd_iff.1 hq; omega
    have c3 : Nat.Coprime q 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    have c2 : Nat.Coprime q 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ c3) (by simpa using c2)
  have hord1 : orderOf U = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hq1 hcop) hφ
  have hU1 : U = 1 := orderOf_eq_one_iff.1 hord1
  have hval : (u : ZMod (3 ^ a)) = 1 := by
    have := congrArg Units.val hU1
    rw [hUdef, IsUnit.unit_spec, Units.val_one] at this
    exact this
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (u - 1) (3 ^ a)).1 (by push_cast; rw [hval, sub_self])
  exact_mod_cast h0

private theorem y10x_three_elt_cent {Mx T : Subgroup G} (hT : IsCyclic ↥T) (hT3 : IsPGroup 3 T)
    (hTM : T ≤ Mx) (hTmax : ∀ Q : Subgroup G, Q ≤ Mx → IsPGroup 3 Q → T ≤ Q → Q = T)
    {g : G} (hgM : g ∈ Mx) (hgN : g ∈ Subgroup.normalizer (T : Set G)) (j : ℕ) (hj : g ^ 3 ^ j = 1) :
    g ∈ Subgroup.centralizer (T : Set G) := by
  obtain ⟨n0, hn0⟩ := isPGroup_iff_card_dvd_pow.1 hT3
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hn0
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hj)
  have hB : Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set G) := Subgroup.zpowers_le.2 hgN
  have hA := card_sup_mul_card_inf_of_le_normalizer (A := T) (B := Subgroup.zpowers g) hB
  rw [Nat.card_zpowers, he, ha] at hA
  have hWdvd : Nat.card ↥(T ⊔ Subgroup.zpowers g) ∣ 3 ^ (a + e) := by
    rw [pow_add, ← hA]
    exact Dvd.intro _ rfl
  have hW3 : IsPGroup 3 (T ⊔ Subgroup.zpowers g : Subgroup G) := IsPGroup.of_card_dvd_pow hWdvd
  have hWM : T ⊔ Subgroup.zpowers g ≤ Mx := sup_le hTM (Subgroup.zpowers_le.2 hgM)
  have hWeq := hTmax (T ⊔ Subgroup.zpowers g) hWM hW3 le_sup_left
  have hzg : Subgroup.zpowers g ≤ T := (le_sup_right : Subgroup.zpowers g ≤ T ⊔ Subgroup.zpowers g).trans hWeq.le
  have hgT : g ∈ T := hzg (Subgroup.mem_zpowers g)
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ht ⟨w, hw⟩)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 (ht ⟨g, hgT⟩)
  have hwk : (t : G) ^ k = w := congrArg Subtype.val hk
  have hgl : (t : G) ^ l = g := congrArg Subtype.val hl
  rw [← hwk, ← hgl]
  exact ((Commute.refl (t : G)).zpow_zpow k l).eq

private theorem y10x_coprime_cent {T : Subgroup G} (hT : IsCyclic ↥T) (hT3 : IsPGroup 3 T)
    {g : G} (hgN : g ∈ Subgroup.normalizer (T : Set G)) {q : ℕ} (hqodd : Odd q) (h3q : ¬ 3 ∣ q)
    (hq : g ^ q = 1) : g ∈ Subgroup.centralizer (T : Set G) := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  have htT : (t : G) ∈ T := t.2
  have hTt : ∀ w ∈ T, ∃ k : ℤ, (t : G) ^ k = w := fun w hw => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ht ⟨w, hw⟩)
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨n0, hn0⟩ := isPGroup_iff_card_dvd_pow.1 hT3
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hn0
  have hzT : Subgroup.zpowers (t : G) = T :=
    le_antisymm (Subgroup.zpowers_le.2 htT) (fun w hw => Subgroup.mem_zpowers_iff.2 (hTt w hw))
  have hord : orderOf (t : G) = 3 ^ a := by
    rw [← Nat.card_zpowers, hzT, ha]
  obtain ⟨u, hu⟩ := hTt _ ((Subgroup.mem_normalizer_iff.1 hgN t).1 htT)
  have hiter : ∀ m : ℕ, g ^ m * (t : G) * (g ^ m)⁻¹ = (t : G) ^ (u ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc g ^ (m + 1) * (t : G) * (g ^ (m + 1))⁻¹ = g * (g ^ m * (t : G) * (g ^ m)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (t : G) ^ (u ^ m) * g⁻¹ := by rw [ih]
        _ = (g * (t : G) * g⁻¹) ^ (u ^ m) := (conj_zpow).symm
        _ = ((t : G) ^ u) ^ (u ^ m) := by rw [← hu]
        _ = (t : G) ^ (u ^ (m + 1)) := by rw [← zpow_mul, pow_succ']
  have hq' : (t : G) = (t : G) ^ (u ^ q) := by
    have := hiter q
    rw [hq, one_mul, inv_one, mul_one] at this
    exact this
  have hdvd : (3 : ℤ) ^ a ∣ u ^ q - 1 := by
    have h1 : (t : G) ^ (u ^ q - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← hq', mul_inv_cancel]
    have h2 := (orderOf_dvd_iff_zpow_eq_one).2 h1
    rw [hord] at h2
    exact_mod_cast h2
  have hdvd1 : (3 : ℤ) ^ a ∣ u - 1 := y10x_three_pow_dvd_sub hqodd h3q hdvd
  have ht1 : (t : G) ^ (u - 1) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [hord]; exact_mod_cast hdvd1)
  have htu : (t : G) ^ u = (t : G) := by
    rw [show u = (u - 1) + 1 by ring, zpow_add_one, ht1, one_mul]
  have hgt : g * (t : G) * g⁻¹ = (t : G) := by rw [← hu, htu]
  have hcomm : Commute (t : G) g := by
    have h' : g * (t : G) = (t : G) * g := by
      calc g * (t : G) = (g * (t : G) * g⁻¹) * g := by group
        _ = (t : G) * g := by rw [hgt]
    exact h'.symm
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  obtain ⟨k, rfl⟩ := hTt w hw
  exact (hcomm.zpow_left k).eq

private theorem y10x_mem_normalizer_zpowers {g x : G} (h1 : g * x * g⁻¹ ∈ Subgroup.zpowers x)
    (h2 : g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have fwd : ∀ g' : G, g' * x * g'⁻¹ ∈ Subgroup.zpowers x →
      ∀ w ∈ Subgroup.zpowers x, g' * w * g'⁻¹ ∈ Subgroup.zpowers x := by
    intro g' hg' w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hg' k
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact fwd g h1 w
  · intro hw
    have := fwd g⁻¹ h2 _ hw
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rwa [e] at this


private theorem y10x_normalizer_cent_T {L M : Subgroup G} {x x' : G}
    (hx'L : x' ∈ L) (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord' : orderOf x' = 5)
    (hxN : x ∈ Subgroup.normalizer (M : Set G)) (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (h1 : ∀ n ∈ M, n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) →
      n ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))
    (hKodd : Odd (Nat.card ↥(Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))))
    {T : Subgroup G} (hT : IsCyclic ↥T) (hT3 : IsPGroup 3 T) (hxT : x ∈ T)
    (hTM : T ≤ M ⊔ Subgroup.zpowers x)
    (hTmax : ∀ Q : Subgroup G, Q ≤ M ⊔ Subgroup.zpowers x → IsPGroup 3 Q → T ≤ Q → Q = T)
    {g : G} (hg : g ∈ M ⊔ Subgroup.zpowers x) (hgT : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.centralizer (T : Set G) := by
  have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x :=
    y10x_mem_zpowers_of_orderOf_eq hxT ((Subgroup.mem_normalizer_iff.1 hgT x).1 hxT)
      (by rw [y10x_orderOf_conj])
  have hgx' : g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.zpowers x :=
    y10x_mem_zpowers_of_orderOf_eq hxT ((Subgroup.mem_normalizer_iff.1 (inv_mem hgT) x).1 hxT)
      (by rw [y10x_orderOf_conj])
  have hgZ : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := y10x_mem_normalizer_zpowers hgx hgx'
  have hgK : g ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G) :=
    y10x_sup_K hxN hxC h1 hg hgZ
  have hodd : Odd (orderOf g) := by
    have hdvd : orderOf g ∣ Nat.card ↥(Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G)) := by
      have := orderOf_dvd_natCard (⟨g, hgK⟩ : ↥(Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    exact hKodd.of_dvd_nat hdvd
  obtain ⟨j, q, h3q, hsq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hqodd : Odd q := (Nat.odd_mul.1 (hsq ▸ hodd)).2
  have hcop : IsCoprime (q : ℤ) ((3 : ℤ) ^ j) := by
    have h3 : Nat.Coprime q 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3q).symm
    have h' : Nat.Coprime q (3 ^ j) := Nat.Coprime.pow_right j h3
    have h'' := Nat.isCoprime_iff_coprime.2 h'
    push_cast at h''
    exact h''
  obtain ⟨α, β, hαβ⟩ := hcop
  have hgsplit : g ^ (α * q) * g ^ (β * 3 ^ j) = g := by
    rw [← zpow_add, hαβ, zpow_one]
  have hpow_ord : ∀ c : ℤ, g ^ (c * (orderOf g : ℤ)) = 1 := fun c => by
    rw [zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hg3j : (g ^ (α * q)) ^ 3 ^ j = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have e : α * (q : ℤ) * ((3 ^ j : ℕ) : ℤ) = α * (orderOf g : ℤ) := by
      rw [hsq]; push_cast; ring
    rw [e, hpow_ord]
  have hgq : (g ^ (β * 3 ^ j)) ^ q = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have e : β * (3 : ℤ) ^ j * (q : ℤ) = β * (orderOf g : ℤ) := by
      rw [hsq]; push_cast; ring
    rw [e, hpow_ord]
  have hg3c : g ^ (α * q) ∈ Subgroup.centralizer (T : Set G) :=
    y10x_three_elt_cent hT hT3 hTM hTmax (zpow_mem hg _) (zpow_mem hgT _) j hg3j
  have hg'c : g ^ (β * 3 ^ j) ∈ Subgroup.centralizer (T : Set G) :=
    y10x_coprime_cent hT hT3 (zpow_mem hgT _) hqodd h3q hgq
  rw [← hgsplit]
  exact Subgroup.mul_mem _ hg3c hg'c


private theorem y10x_K0_exists {L M : Subgroup G} {x x' : G} (hx'L : x' ∈ L)
    (hZ : ¬ 5 ∣ Nat.card ↥(Subgroup.centralizer (L : Set G))) (hord' : orderOf x' = 5) (hord3 : orderOf x = 3)
    (hxN : x ∈ Subgroup.normalizer (M : Set G)) (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (h1 : ∀ n ∈ M, n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) →
      n ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))
    (hKodd : Odd (Nat.card ↥(Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))))
    (hrk : CFSG.Open.pRank 3 (Subgroup.centralizer (L : Set G)) ≤ 1) :
    ∃ K0 : Subgroup G, ∀ g : G, g ∈ K0 ↔ (g ∈ M ⊔ Subgroup.zpowers x ∧ ¬ 3 ∣ orderOf g) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set NN : Subgroup G := M ⊔ Subgroup.zpowers x with hNN
  have hxNN : x ∈ NN := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hcyc : ∀ T : Subgroup G, T ≤ NN → IsPGroup 3 T → IsCyclic ↥T := fun T hT hT3 =>
    y10x_transfer Nat.prime_three hxNN hord3 (fun S hS hS3 =>
      y10x_cyc_three_sub_centx hx'L hZ hord' hxN hxC h1 hrk hS hS3) T hT hT3
  have hx3 : IsPGroup 3 (Subgroup.zpowers (⟨x, hxNN⟩ : ↥NN)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord3, pow_one])
  obtain ⟨Tt, hTt⟩ := hx3.exists_le_sylow
  set T : Subgroup G := (Tt : Subgroup ↥NN).map NN.subtype with hTdef
  have hTNN : T ≤ NN := Subgroup.map_subtype_le _
  have hT3 : IsPGroup 3 T := Tt.isPGroup'.map NN.subtype
  have hxT : x ∈ T := ⟨⟨x, hxNN⟩, hTt (Subgroup.mem_zpowers _), rfl⟩
  have hTcyc : IsCyclic ↥T := hcyc T hTNN hT3
  have hTmax : ∀ Q : Subgroup G, Q ≤ NN → IsPGroup 3 Q → T ≤ Q → Q = T := by
    intro Q hQN hQ3 hTQ
    have hQt3 : IsPGroup 3 (Q.subgroupOf NN) := hQ3.comap_subtype
    obtain ⟨S₀, hS₀⟩ := hQt3.exists_le_sylow
    have hTtQ : (Tt : Subgroup ↥NN) ≤ Q.subgroupOf NN := by
      intro tt htt
      exact Subgroup.mem_subgroupOf.2 (hTQ ⟨tt, htt, rfl⟩)
    have hTtS : (Tt : Subgroup ↥NN) ≤ (S₀ : Subgroup ↥NN) := hTtQ.trans hS₀
    have hcard : Nat.card (Tt : Subgroup ↥NN) = Nat.card (S₀ : Subgroup ↥NN) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hTS : (Tt : Subgroup ↥NN) = (S₀ : Subgroup ↥NN) :=
      Subgroup.eq_of_le_of_card_ge hTtS hcard.ge
    have hQTt : Q.subgroupOf NN ≤ (Tt : Subgroup ↥NN) := hTS ▸ hS₀
    have heq : Q.subgroupOf NN = (Tt : Subgroup ↥NN) := le_antisymm hQTt hTtQ
    rw [hTdef, ← Subgroup.map_subgroupOf_eq_of_le hQN, heq]
  have hNH : Subgroup.normalizer ((Tt : Subgroup ↥NN) : Set ↥NN) ≤
      Subgroup.centralizer ((Tt : Subgroup ↥NN) : Set ↥NN) := by
    intro gt hgt
    have fwd : ∀ g' ∈ Subgroup.normalizer ((Tt : Subgroup ↥NN) : Set ↥NN), ∀ s ∈ T,
        (g' : G) * s * (g' : G)⁻¹ ∈ T := by
      rintro g' hg' _ ⟨tt, htt, rfl⟩
      exact ⟨g' * tt * g'⁻¹, (Subgroup.mem_normalizer_iff.1 hg' tt).1 htt, by simp⟩
    have hgT : (gt : G) ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact fwd gt hgt h hh
      · intro hh
        have := fwd gt⁻¹ (inv_mem hgt) _ hh
        have e : ((gt⁻¹ : ↥NN) : G) * ((gt : G) * h * (gt : G)⁻¹) * ((gt⁻¹ : ↥NN) : G)⁻¹ = h := by
          rw [Subgroup.coe_inv]; group
        rwa [e] at this
    have hgC := y10x_normalizer_cent_T hx'L hZ hord' hxN hxC h1 hKodd hTcyc hT3 hxT hTNN hTmax gt.2 hgT
    refine Subgroup.mem_centralizer_iff.2 fun tt htt => Subtype.ext ?_
    show (tt : G) * (gt : G) = (gt : G) * (tt : G)
    exact Subgroup.mem_centralizer_iff.1 hgC (tt : G) ⟨tt, htt, rfl⟩
  have hcomp := MonoidHom.ker_transferSylow_isComplement' Tt hNH
  have hK3 := MonoidHom.not_dvd_card_ker_transferSylow Tt hNH
  have hKdisj := MonoidHom.ker_transferSylow_disjoint Tt hNH (Tt : Subgroup ↥NN) Tt.isPGroup'

  obtain ⟨Kt, hKt⟩ : ∃ Kt : Subgroup ↥NN, Kt = (MonoidHom.transferSylow Tt hNH).ker := ⟨_, rfl⟩
  rw [← hKt] at hK3 hKdisj
  haveI hKn : Kt.Normal := by rw [hKt]; exact MonoidHom.normal_ker _
  have hchar : ∀ gt : ↥NN, ¬ 3 ∣ orderOf gt → gt ∈ Kt := by
    intro gt hgt
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab, -⟩ :=
      (Subgroup.isComplement_iff_existsUnique.1 (Subgroup.isComplement'_def.1 hcomp)) gt
    have ha' : a ∈ Kt := by rw [hKt]; exact ha
    have hb' : b ∈ (Tt : Subgroup ↥NN) := hb
    have hab' : a * b = gt := hab
    have ha1 : (QuotientGroup.mk' Kt a : ↥NN ⧸ Kt) = 1 := (QuotientGroup.eq_one_iff a).2 ha'
    have hφg : (QuotientGroup.mk' Kt gt : ↥NN ⧸ Kt) = QuotientGroup.mk' Kt b := by
      rw [← hab', map_mul, ha1, one_mul]
    have hφ1 : orderOf (QuotientGroup.mk' Kt gt) ∣ orderOf gt := orderOf_map_dvd _ _
    obtain ⟨n, hn⟩ := Tt.isPGroup' ⟨b, hb'⟩
    have hbn : b ^ 3 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hφ2 : orderOf (QuotientGroup.mk' Kt gt) ∣ 3 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hφg, ← map_pow, hbn, map_one]
    have hcop : Nat.Coprime (orderOf gt) (3 ^ n) :=
      Nat.Coprime.pow_right n (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hgt))
    have hone : orderOf (QuotientGroup.mk' Kt gt) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hφ1 hcop) hφ2
    have hφ1' : QuotientGroup.mk' Kt b = 1 := by
      rw [← hφg]; exact orderOf_eq_one_iff.1 hone
    have hbK : b ∈ Kt := (QuotientGroup.eq_one_iff b).1 hφ1'
    have hb1 : b = 1 := by
      have hbot : Kt ⊓ (Tt : Subgroup ↥NN) = ⊥ := disjoint_iff.1 hKdisj
      have hmem : b ∈ Kt ⊓ (Tt : Subgroup ↥NN) := Subgroup.mem_inf.2 ⟨hbK, hb'⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rw [← hab', hb1, mul_one]
    exact ha'
  refine ⟨Kt.map NN.subtype, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    obtain ⟨gt, hgt, rfl⟩ := Subgroup.mem_map.1 hg
    refine ⟨gt.2, ?_⟩
    intro hdiv
    have hdvdK : orderOf (NN.subtype gt) ∣ Nat.card ↥Kt := by
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      have := orderOf_dvd_natCard (⟨gt, hgt⟩ : ↥Kt)
      rwa [Subgroup.orderOf_mk] at this
    exact hK3 (hdiv.trans hdvdK)
  · rintro ⟨hgNN, hg3⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hgNN⟩, hchar ⟨g, hgNN⟩ ?_, rfl⟩
    rwa [Subgroup.orderOf_mk]

private theorem y10x_five_elt_not_three {Q : Subgroup G} (hQ5 : IsPGroup 5 Q) {g : G} (hg : g ∈ Q) :
    ¬ 3 ∣ orderOf g := by
  obtain ⟨n, hn⟩ := hQ5 ⟨g, hg⟩
  have hn' : g ^ 5 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hn')
  rw [hi]
  intro h3
  have : (3 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

private theorem y10x_not_three_dvd_of_char {K0 : Subgroup G}
    (hK0 : ∀ g : G, g ∈ K0 → ¬ 3 ∣ orderOf g) : ¬ 3 ∣ Nat.card ↥K0 := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K0) 3 h
  exact hK0 k.1 k.2 (by rw [Subgroup.orderOf_coe, hk])

private theorem y10x_five_group_not_three {Q : Subgroup G} (hQ5 : IsPGroup 5 Q) : ¬ 3 ∣ Nat.card ↥Q := by
  intro h
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hQ5
  have h3 : 3 ∣ 5 ^ n := h.trans hn
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

private theorem y10x_mem_sup_normalizes_gen {N B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (N : Set G))
    {g : G} (hg : g ∈ N ⊔ B) : ∃ n ∈ N, ∃ b ∈ B, g = n * b := by
  let W : Subgroup G :=
    { carrier := {g | ∃ n ∈ N, ∃ b ∈ B, g = n * b}
      mul_mem' := by
        rintro _ _ ⟨n1, hn1, b1, hb1, rfl⟩ ⟨n2, hn2, b2, hb2, rfl⟩
        refine ⟨n1 * (b1 * n2 * b1⁻¹), N.mul_mem hn1 ((Subgroup.mem_normalizer_iff.1 (hBN hb1) n2).1 hn2),
          b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        group
      one_mem' := ⟨1, N.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, hn, b, hb, rfl⟩
        refine ⟨b⁻¹ * n⁻¹ * b⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (hBN (B.inv_mem hb)) n⁻¹).1 (N.inv_mem hn),
          b⁻¹, B.inv_mem hb, ?_⟩
        group }
  have hle : N ⊔ B ≤ W := sup_le (fun n hn => ⟨n, hn, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, N.one_mem, b, hb, by simp⟩)
  exact hle hg

private theorem y10x_mem_normalizer_sup {N B : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hxB : x ∈ Subgroup.normalizer (B : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) :
    x ∈ Subgroup.normalizer ((N ⊔ B : Subgroup G) : Set G) := by
  have fwd : ∀ y : G, y ∈ Subgroup.normalizer (N : Set G) → y ∈ Subgroup.normalizer (B : Set G) →
      ∀ g ∈ N ⊔ B, y * g * y⁻¹ ∈ N ⊔ B := by
    intro y hyN hyB g hg
    obtain ⟨n, hn, b, hb, rfl⟩ := y10x_mem_sup_normalizes_gen hBN hg
    rw [show y * (n * b) * y⁻¹ = (y * n * y⁻¹) * (y * b * y⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hyN n).1 hn))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hyB b).1 hb))
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fwd x hxN hxB g
  · intro hg
    have := fwd x⁻¹ (inv_mem hxN) (inv_mem hxB) _ hg
    have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
    rwa [e] at this

private theorem y10x_normalizer_of_centralizes {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hgh : ∀ a ∈ A, g * a * g⁻¹ = a := fun a ha => by
    have hcomm := Subgroup.mem_centralizer_iff.1 hg a ha
    calc g * a * g⁻¹ = (a * g) * g⁻¹ := by rw [hcomm.symm]
      _ = a := by group
  have hginv : ∀ a ∈ A, g⁻¹ * a * g⁻¹⁻¹ = a := fun a ha => by
    have hcomm := Subgroup.mem_centralizer_iff.1 hg a ha
    calc g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [hcomm]
      _ = a := by group
  constructor
  · intro ha
    rw [hgh h ha]
    exact ha
  · intro ha
    have e : h = g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ := by group
    rw [e, hginv _ ha]
    exact ha

private theorem y10x_conj_NN {M : Subgroup G} {x b : G} (hxM : x ∈ Subgroup.normalizer (M : Set G))
    (hbM : b ∈ Subgroup.normalizer (M : Set G)) (hbx : b * x * b⁻¹ = x) {g : G}
    (hg : g ∈ M ⊔ Subgroup.zpowers x) : b * g * b⁻¹ ∈ M ⊔ Subgroup.zpowers x := by
  obtain ⟨m, hm, k, rfl⟩ := y10x_mem_sup_of_normalizes hxM hg
  have hbxk : b * x ^ k * b⁻¹ = x ^ k := by rw [← conj_zpow, hbx]
  rw [show b * (m * x ^ k) * b⁻¹ = (b * m * b⁻¹) * (b * x ^ k * b⁻¹) by group, hbxk]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hbM m).1 hm))
    (Subgroup.mem_sup_right (zpow_mem (Subgroup.mem_zpowers x) k))

private theorem y10x_conj_K0 {M K0 : Subgroup G} {x b : G} (hK0 : ∀ g : G, g ∈ K0 ↔ (g ∈ M ⊔ Subgroup.zpowers x ∧ ¬ 3 ∣ orderOf g))
    (hxM : x ∈ Subgroup.normalizer (M : Set G))
    (hbM : b ∈ Subgroup.normalizer (M : Set G)) (hbx : b * x * b⁻¹ = x) :
    b ∈ Subgroup.normalizer (K0 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨hgNN, hg3⟩ := (hK0 g).1 hg
    refine (hK0 _).2 ⟨y10x_conj_NN hxM hbM hbx hgNN, ?_⟩
    rwa [y10x_orderOf_conj]
  · intro hg
    have hxb : x * b = b * x := by
      calc x * b = (b * x * b⁻¹) * b := by rw [hbx]
        _ = b * x := by group
    have hbinv : b⁻¹ * x * b⁻¹⁻¹ = x := by
      calc b⁻¹ * x * b⁻¹⁻¹ = b⁻¹ * (x * b) := by group
        _ = b⁻¹ * (b * x) := by rw [hxb]
        _ = x := by group
    obtain ⟨hgNN, hg3⟩ := (hK0 _).1 hg
    have hbinvM : b⁻¹ ∈ Subgroup.normalizer (M : Set G) := inv_mem hbM
    have := (hK0 _).2 ⟨y10x_conj_NN hxM hbinvM hbinv hgNN, by rwa [y10x_orderOf_conj]⟩
    rwa [show b⁻¹ * (b * g * b⁻¹) * b⁻¹⁻¹ = g by group] at this

private theorem y10x_conj_into_max {Y S Q : Subgroup G} (hSY : S ≤ Y) (hS5 : IsPGroup 5 S)
    (hSmax : ∀ Q' : Subgroup G, Q' ≤ Y → IsPGroup 5 Q' → S ≤ Q' → Q' = S)
    (hQY : Q ≤ Y) (hQ5 : IsPGroup 5 Q) : ∃ g ∈ Y, ∀ s ∈ Q, g * s * g⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS' : IsPGroup 5 (S.subgroupOf Y) := hS5.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hS'.exists_le_sylow
  have hQ₀S : (Q₀ : Subgroup Y).map Y.subtype = S := by
    apply hSmax
    · exact Subgroup.map_subtype_le _
    · exact Q₀.isPGroup'.map Y.subtype
    · intro s hs
      exact ⟨⟨s, hSY hs⟩, hQ₀ (Subgroup.mem_subgroupOf.2 hs), rfl⟩
  obtain ⟨g, hg⟩ := y10x_exists_conj_sylow Nat.prime_five Q₀ hQY hQ5
  refine ⟨g, g.2, fun s hs => ?_⟩
  obtain ⟨t, htQ₀, ht⟩ := hg s hs
  rw [← ht, ← hQ₀S]
  exact ⟨t, htQ₀, rfl⟩

theorem u64_exists_P (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hp3 : p = 3) (hp5 : p' = 5)
    (h1 : ∀ g ∈ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G),
      g ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))
    (h2 : CFSG.Open.pRank p (Subgroup.centralizer (L : Set G)) ≤ 1 ∧ ¬ p' ∣ Nat.card ↥(Subgroup.centralizer (L : Set G)) ∧
      Odd (Nat.card ↥(Subgroup.centralizer (L : Set G)))) :
    ∃ P : Subgroup G, P ≤ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) ∧ IsPGroup p' P ∧
      (∀ Q : Subgroup G, Q ≤ centModSubgroup p' L' ⊓ Subgroup.centralizer ({x'} : Set G) → IsPGroup p' Q → P ≤ Q → Q = P) ∧
      B' ≤ Subgroup.normalizer (P : Set G) ∧ x ∈ Subgroup.normalizer (P : Set G) ∧
      P ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x' := by
  subst hp3 hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hrk, h5nd, hodd⟩ := h2
  have hH := rquad_hyp hsf hR
  have hx3 : x ^ 3 = 1 := hH.elem.2 x hH.mem
  have hxne : x ≠ 1 := hH.ne_one
  have hord3 : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.comp.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hB'L : B' ≤ L := hc.cfg.le
  have hB5 : IsPGroup 5 B' := isPGroup_of_isElemAbelian hc.cfg.elem
  have hx'L : x' ∈ L := hB'L hc.cfg.mem
  have hord' : orderOf x' = 5 := orderOf_eq_prime (hc.cfg.elem.2 x' hc.cfg.mem) hc.cfg.ne_one
  have hB'C : ∀ b ∈ B', b * x = x * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLx (hB'L hb))
  have hbx : ∀ b ∈ B', b * x * b⁻¹ = x := fun b hb => by rw [hB'C b hb]; group
  have hxB' : x ∈ Subgroup.centralizer (B' : Set G) := Subgroup.mem_centralizer_iff.2 hB'C
  have hxB'N : x ∈ Subgroup.normalizer (B' : Set G) := y10x_normalizer_of_centralizes hxB'
  have hKodd : Odd (Nat.card ↥(Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G))) := by
    rw [y10x_card_K hx'L h5nd hord']
    exact Odd.mul ⟨2, rfl⟩ hodd
  set M : Subgroup G := centModSubgroup 5 L' ⊓ Subgroup.centralizer ({x'} : Set G) with hMdef
  have hBL'N : B' ≤ Subgroup.normalizer (L' : Set G) := bstar_norm hc hc117.comp' hc117.J_le hc117.uniq
  have hxL'N : x ∈ Subgroup.normalizer (L' : Set G) := hc117.x_norm
  have hx'C'L : x' ∈ Subgroup.centralizer (L' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl))
  have hx'M : x' ∈ M := Subgroup.mem_inf.2 ⟨mem_centModSubgroup.2 ⟨y10x_normalizer_of_centralizes hx'C'L,
    fun l hl => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hc117.comp'.1 hl))]
      exact Subgroup.one_mem _⟩, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hxC' : x ∈ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hB'C x' hc.cfg.mem).symm
  have hxM : x ∈ Subgroup.normalizer (M : Set G) :=
    y10x_normalizer_inf (normalizer_le_normalizer_centModSubgroup 5 L' hxL'N) (y10x_normalizer_centralizer_set hxC')
  have hBM : B' ≤ Subgroup.normalizer (M : Set G) := fun b hb =>
    y10x_normalizer_inf (normalizer_le_normalizer_centModSubgroup 5 L' (hBL'N hb))
      (y10x_normalizer_centralizer_set (Subgroup.mem_centralizer_singleton_iff.2
        (isElemAbelian_commute hc.cfg.elem hb hc.cfg.mem)))
  have h1' : ∀ n ∈ M, n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) →
      n ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G) := fun n hn hnN =>
    h1 n (Subgroup.mem_inf.2 ⟨hn, hnN⟩)
  obtain ⟨K0, hK0⟩ := y10x_K0_exists hx'L h5nd hord' hord3 hxM hxC h1' hKodd hrk
  have hxK0 : x ∈ Subgroup.normalizer (K0 : Set G) :=
    y10x_conj_K0 hK0 hxM hxM (by group)
  have hBK0 : ∀ b ∈ B', b ∈ Subgroup.normalizer (K0 : Set G) := fun b hb =>
    y10x_conj_K0 hK0 hxM (hBM hb) (hbx b hb)
  have hx'N₀ : x' ∈ M ⊓ K0 := Subgroup.mem_inf.2 ⟨hx'M,
    (hK0 x').2 ⟨(le_sup_left : M ≤ M ⊔ Subgroup.zpowers x) hx'M, by rw [hord']; norm_num⟩⟩
  set N₀ : Subgroup G := M ⊓ K0 with hN₀
  have hBN₀ : B' ≤ Subgroup.normalizer (N₀ : Set G) := fun b hb =>
    y10x_normalizer_inf (hBM hb) (hBK0 b hb)
  have hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set G) := y10x_normalizer_inf hxM hxK0
  have hΓN₀ : N₀ ⊔ B' ≤ Subgroup.normalizer (N₀ : Set G) :=
    sup_le (fun n hn => Subgroup.le_normalizer hn) hBN₀
  have hK0card : ¬ 3 ∣ Nat.card ↥K0 := y10x_not_three_dvd_of_char (fun g hg => ((hK0 g).1 hg).2)
  have hN₀card : ¬ 3 ∣ Nat.card ↥N₀ := fun h => hK0card (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hM3 : ¬ 3 ∣ Nat.card ↥(N₀ ⊔ B') := by
    intro h
    have hcard := card_sup_mul_card_inf_of_le_normalizer (A := N₀) (B := B') hBN₀
    have h3 : 3 ∣ Nat.card ↥N₀ * Nat.card ↥B' := by
      rw [← hcard]; exact Dvd.dvd.mul_right h _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h' | h'
    · exact hN₀card h'
    · exact y10x_five_group_not_three hB5 h'
  have hxΓ : Subgroup.zpowers x ≤ Subgroup.normalizer ((N₀ ⊔ B' : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (y10x_mem_normalizer_sup hxN₀ hxB'N hBN₀)
  have hA3 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord3, pow_one])
  obtain ⟨S, hSfus, hB'S, hzS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_five hA3 hM3 hxΓ le_sup_right hB5 (Subgroup.zpowers_le.2 hxB'N)
  obtain ⟨hSΓ, hS5, hSmax⟩ := hSfus
  have hPM : S ⊓ N₀ ≤ M := inf_le_right.trans inf_le_left
  refine ⟨S ⊓ N₀, hPM, hS5.to_le inf_le_left, ?_, ?_, ?_, ?_⟩
  ·
    intro Q hQM hQ5 hPQ
    have hQN₀ : Q ≤ N₀ := fun q hq => Subgroup.mem_inf.2 ⟨hQM hq, (hK0 q).2
      ⟨(le_sup_left : M ≤ M ⊔ Subgroup.zpowers x) (hQM hq), y10x_five_elt_not_three hQ5 hq⟩⟩
    have hQΓ : Q ≤ N₀ ⊔ B' := hQN₀.trans le_sup_left
    obtain ⟨g, hgΓ, hgQ⟩ := y10x_conj_into_max hSΓ hS5 hSmax hQΓ hQ5
    have hgN₀ : g ∈ Subgroup.normalizer (N₀ : Set G) := hΓN₀ hgΓ
    have hmapP : Q.map (MulAut.conj g).toMonoidHom ≤ S ⊓ N₀ := by
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_inf.2 ⟨hgQ q hq, (Subgroup.mem_normalizer_iff.1 hgN₀ q).1 (hQN₀ hq)⟩
    have hcardmap : Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Q :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hle : Nat.card ↥Q ≤ Nat.card ↥(S ⊓ N₀) := by
      rw [← hcardmap]; exact Subgroup.card_le_of_le hmapP
    exact (Subgroup.eq_of_le_of_card_ge hPQ hle).symm
  · exact fun b hb => y10x_normalizer_inf (Subgroup.le_normalizer (hB'S hb)) (hBN₀ hb)
  · exact y10x_normalizer_inf (hzS (Subgroup.mem_zpowers x)) hxN₀
  · apply le_antisymm
    · intro g hg
      obtain ⟨hgP, hgCx⟩ := Subgroup.mem_inf.1 hg
      have hgM : g ∈ M := hPM hgP
      have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
        y10x_cent_normalizes_zpowers (Subgroup.mem_centralizer_singleton_iff.1 hgCx)
      have hgCL : g ∈ Subgroup.zpowers x' ⊔ Subgroup.centralizer (L : Set G) :=
        h1' g hgM hgN
      rw [sup_comm] at hgCL
      obtain ⟨c, hc', k, rfl⟩ := y10x_mem_sup_of_normalizes (y10x_normalizer_cent_of_mem hx'L) hgCL
      obtain ⟨j, hj⟩ := (hS5.to_le inf_le_left) ⟨c * x' ^ k, hgP⟩
      have hj' : (c * x' ^ k) ^ 5 ^ j = 1 := by
        have := congrArg Subtype.val hj
        simpa using this
      have hcomm : Commute c (x' ^ k) :=
        (Subgroup.mem_centralizer_iff.1 hc' (x' ^ k) (zpow_mem hx'L k)).symm
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [pow_zero, pow_one] at hj'
        rw [hj']
        exact Subgroup.one_mem _
      · have ha5 : (x' ^ k) ^ 5 = 1 := by
          have e1 : (x' ^ k) ^ 5 = (x' ^ (5 : ℤ)) ^ k := by
            rw [← zpow_natCast, ← zpow_mul, ← zpow_mul]
            congr 1
            push_cast
            ring
          rw [e1, y10x_zpow_five hord', one_zpow]
        have ha : (x' ^ k) ^ 5 ^ j = 1 := by
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [pow_succ', pow_mul, ha5, one_pow]
        have hc5 : c ^ 5 ^ j = 1 := by
          rw [hcomm.mul_pow, ha, mul_one] at hj'
          exact hj'
        have hc1 : c = 1 := by
          by_contra hne
          have hdvd : orderOf c ∣ 5 ^ j := orderOf_dvd_of_pow_eq_one hc5
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
          have hi0 : i ≠ 0 := by
            rintro rfl
            exact hne (orderOf_eq_one_iff.1 (by simpa using hi))
          have h5i : 5 ∣ orderOf c := by
            rw [hi]; exact dvd_pow_self 5 hi0
          have hdvdC : orderOf c ∣ Nat.card ↥(Subgroup.centralizer (L : Set G)) := by
            have := orderOf_dvd_natCard (⟨c, hc'⟩ : ↥(Subgroup.centralizer (L : Set G)))
            rwa [Subgroup.orderOf_mk] at this
          exact h5nd (h5i.trans hdvdC)
        rw [hc1, one_mul]
        exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    · have hx'P : x' ∈ S ⊓ N₀ := Subgroup.mem_inf.2 ⟨hB'S hc.cfg.mem, hx'N₀⟩
      have hx'Cx : x' ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 (hB'C x' hc.cfg.mem)
      exact Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hx'P, hx'Cx⟩)

theorem u64_cyc (h6 : U6StructAt G) (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L)
    (hind : Cor112Indep G m p B x L) (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L')
    (hU : LabelOf L ⟨.twA, 5, 2⟩) (hm4 : m = 4) (hp3 : p = 3) (hp5 : p' = 5) : CycModSylow p' L' := by
  have hxL : x' ∈ L' := hc117.J_le (u64_x_mem_J h6 hc hU hp5)
  obtain ⟨P, hPN, hP5, hPmax, hPB, hPx, hPc⟩ := u64_exists_P hctx hsf hR hc hc117 hp3 hp5
    (u64_normN_le h6 hctx hsf hR hc hc117 hU hp3 hp5) (u64_cent_rank h6 hctx hR hind hc hU hm4 hp3 hp5)
  exact u64_cyc_of_P hctx hsf hR hc hc117 hp3 hp5 hxL hPN hP5 hPmax hPB hPx hPc

theorem ab_case2 (h08 : YS08) (h64 : U64TypesAt G) (h5r : U5RankAt) (h5o : U5OutAt G) (h6 : U6StructAt G)
    (heT : ETableAt G) (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L)
    (hind : Cor112Indep G m p B x L)
    (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L') (hU : LabelOf L ⟨.twA, 5, 2⟩)
    (hp3 : p = 3) (hp5 : p' = 5) (hchev : IsChevSimple 2 (PSimple p' L')) :
    CycModSylow p' L' ∧ InnDiagOn p' B' L' := by
  have hm4 : m = 4 := by
    obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := heT L ⟨.twA, 5, 2⟩ hU
    have := h9 ⟨rfl, rfl⟩ (by norm_num) (h6.center L hU)
    rw [hc.e_eq] at this
    exact this
  have hty := u64_types h08 h64 h5r h6 hctx hsf hR hc hc117 hU hp3 hp5 hchev hm4
  exact ⟨u64_cyc h6 hctx hsf hR hind hc hc117 hU hm4 hp3 hp5, u64_idiag h5o hc hc117 hty hp5⟩

theorem p'_eq_five (hc : Cfg116 G m p L p' B' x' J) (hU : LabelOf L ⟨.twA, 5, 2⟩) : p' = 5 := by
  have h := hc.splits ⟨.twA, 5, 2⟩ hU
  simp [GLASplit16, CFSG.Assembly.LargeEvenSplit16, CFSG.Assembly.LargeEvenUntwisted] at h
  have : p' ∣ 5 := by simpa using h
  exact (Nat.prime_dvd_prime_iff_eq hc.cfg.prime (by norm_num)).1 this

theorem ab_of_cfg (h08 : YS08) (h64 : U64TypesAt G) (h5r : U5RankAt) (h5o : U5OutAt G) (h6 : U6StructAt G)
    (heT : ETableAt G) (hctx : ThmACtx G m) (hsf : StageFacts G m) (hR : RQuad G m p B x L) (hind : Cor112Indep G m p B x L)
    (hp3 : LabelOf L ⟨.twA, 5, 2⟩ → p = 3) (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hchev : IsChevSimple 2 (PSimple p' L')) :
    CycModSylow p' L' ∧ InnDiagOn p' B' L' := by
  rcases hc.cfg.seven with h | h
  · exact ab_case1 h08 hctx hsf hR hc hc117 h hchev
  · exact ab_case2 h08 h64 h5r h5o h6 heT hctx hsf hR hind hc hc117 h (hp3 h) (p'_eq_five hc h) hchev

theorem lemma119_rquad (h08 : YS08) (h64 : U64TypesAt G) (h5r : U5RankAt) (h5o : U5OutAt G) (h6 : U6StructAt G)
    (heT : ETableAt G) (hctx : ThmACtx G m) (hsf : StageFacts G m) (h1416 : I1416Chev2At G) (h142 : I142At G)
    (hR : RQuad G m p B x L) (hns : NoSplit16 p L) (hind : Cor112Indep G m p B x L)
    (hp3 : LabelOf L ⟨.twA, 5, 2⟩ → p = 3) (hc : Cfg116 G m p L p' B' x' J) (hc117 : Concl117 G p p' B' x' x J L') :
    RQuad G m p' B' x' L' := by
  have hnorm : B' ≤ Subgroup.normalizer (L' : Set G) := bstar_norm hc hc117.comp' hc117.J_le hc117.uniq
  have hGB := lemma118 hctx hsf h1416 h142 hR hns hc hc117
  have hS0 : IsS0 p' B' x' L' := isS0_of_isGStar hc117.triple (isGStar_of_isGB hGB hnorm)
  obtain ⟨hcyc, hinn⟩ := ab_of_cfg h08 h64 h5r h5o h6 heT hctx hsf hR hind hp3 hc hc117 (chev_of_cfg hctx hsf h1416 hR hns hc hc117)
  obtain ⟨-, h4o, -, -, -, -, -, h9, -⟩ := hsf p' hc.mu
  have hS0M : IsS0Max p' B' x' L' := h4o.2.2.2.2.1 B' x' L' hS0 hcyc
  have hSS : IsSStarMax p' B' x' L' := ⟨hS0M, hcyc⟩
  have hqs : CFSG.Open.IsQuasisimple ↥L' := (h9.1 B' x' L' hSS).1
  exact ⟨hc.mu, hSS, S10.inner_of_innDiagOn hc117.comp' hqs hinn⟩

theorem lemma119_field (hin : I1441At G) (hR' : RQuad G m p' B' x' L') (hc : Cfg116 G m p L p' B' x' J)
    (hc117 : Concl117 G p p' B' x' x J L') (hxp : x ^ p = 1) (hpp : p.Prime) (hp2 : p ≠ 2) :
    ∀ lab' labJ : GLALabel, LabelOf L' lab' → LabelOf J labJ → FieldRel p (canonLabel lab') (canonLabel labJ) := by
  intro lab' labJ hlab' hlabJ
  exact hin p L' J x lab' labJ hpp hp2 (isChev2_of_innerDiag hR'.2.2) hc.cfg.chev2 hc117.x_norm hxp hc117.J_layer.2 hlab' hlabJ

theorem exists_succ (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs114 G) (hR : RQuad G m p B x L)
    (hns : NoSplit16 p L) :
    ∃ (p' : ℕ) (B' : Subgroup G) (x' : G) (L' J : Subgroup G), Succ11 G m p B x L p' B' x' L' J := by
  obtain ⟨p', B', x', J, hc⟩ := lemma116 hctx hsf hin.toInputs111 hin.i166 hin.labUniq hR hns
  obtain ⟨L', hc117⟩ := lemma117 hctx hsf hin.sch hin.i25 hin.u5case hin.u6case hin.centq hR hc
  have hH := rquad_hyp hsf hR
  have hcor := cor112_full hctx hsf hin.toInputs111 hR hns
  have hp3 : LabelOf L ⟨.twA, 5, 2⟩ → p = 3 := by
    intro hU
    obtain ⟨lab, hlab, hl110⟩ := hcor.half
    have hlabeq : lab = ⟨.twA, 5, 2⟩ := by
      rcases hin.labUniq L lab ⟨.twA, 5, 2⟩ (by rw [hcor.e_eq]; exact hctx.1.four_le) hlab hU with h | ⟨h1, h2, h3, h4⟩
      · exact h
      · simp at h2
    subst hlabeq
    rcases hl110.cases with hA | ⟨hb, hdiv⟩ | ⟨hc', -, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · simp [TypeA] at hA
    · have : p ∣ 3 := by simpa using hdiv
      exact (Nat.prime_dvd_prime_iff_eq hH.prime Nat.prime_three).1 this
    · simp at hc'
    · simp at h1
    · simp at h1
  have hR' := lemma119_rquad hin.ys08 hin.u64types hin.u5rank hin.u5out hin.u6struct hin.eTable hctx hsf hin.i1416 hin.i142 hR hns hcor.indep hp3 hc hc117
  exact ⟨p', B', x', L', J, hR, hR', hc, hc117,
    lemma119_field hin.i1441 hR' hc hc117 (hH.elem.2 x hH.mem) hH.prime hH.ne_two⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
