module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFact
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTablesSp6

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear
  blockSpecialLinear_mono)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)
open scoped MatrixGroups

section Siegel

variable {F : Type} [Field F] {n : ℕ}

theorem mem_siegelLeviGL_of_blocks_eq_zero {x : StatedSp n F}
    (hz : ∀ i j, mat n F x (Sum.inl i) (Sum.inr j) = 0 ∧ mat n F x (Sum.inr i) (Sum.inl j) = 0) :
    x ∈ siegelLeviGL F n := by
  set M := mat n F x with hM
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    exact (hz i j).1
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact (hz i j).2
  have hMb : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [h12, h21]
  have hsym := mat_transpose_mul_gram_mul x
  rw [← hM, hMb, ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply] at hsym
  have hAD : (M.toBlocks₁₁)ᵀ * M.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₁₂ hsym
    simpa using this
  have hDA : (M.toBlocks₂₂)ᵀ * M.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.transpose hAD
    simpa [Matrix.transpose_mul] using this
  refine ⟨⟨M.toBlocks₁₁, (M.toBlocks₂₂)ᵀ, mul_eq_one_comm.1 hDA, hDA⟩, mat_injective ?_⟩
  rw [mat_leviEmbedGL, ← hM]
  conv_rhs => rw [hMb]
  congr 1

variable (F) in
@[expose] noncomputable def siegelBlock (B : Finset (Fin n)) : Subgroup (StatedSp n F) :=
  (blockSpecialLinear (K := F) B).map (leviEmbedSL F n)

theorem mat_leviEmbedSL_inl_inl (C : SL(n, F)) (i j : Fin n) :
    mat n F (leviEmbedSL F n C) (Sum.inl i) (Sum.inl j) = (C : Matrix (Fin n) (Fin n) F) i j := by
  rw [mat_leviEmbedSL, fromBlocks_apply₁₁]

theorem siegelBlock_le_spBlock (B : Finset (Fin n)) : siegelBlock F B ≤ spBlock F B := by
  rintro _ ⟨C, hC, rfl⟩
  have hCi : C⁻¹ ∈ blockSpecialLinear (K := F) B := inv_mem hC
  intro a b hab
  rw [mat_leviEmbedSL]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁, hC i j (not_and_or.1 hab)]
    simp [Matrix.one_apply]
  · simp [fromBlocks_apply₁₂]
  · simp [fromBlocks_apply₂₁]
  · rw [fromBlocks_apply₂₂, transpose_apply, hCi j i (not_and_or.1 hab).symm]
    simp [Matrix.one_apply, eq_comm]

theorem siegelLevi_inf_spBlock_le (B : Finset (Fin n)) :
    siegelLevi F n ⊓ spBlock F B ≤ siegelBlock F B := by
  rintro x ⟨⟨C, rfl⟩, hx⟩
  refine ⟨C, fun i j hij => ?_, rfl⟩
  have h := hx (Sum.inl i) (Sum.inl j) (fun h => by
    rcases hij with hi | hj
    · exact hi h.1
    · exact hj h.2)
  rw [mat_leviEmbedSL_inl_inl] at h
  rw [h]
  simp [Matrix.one_apply]

theorem commute_siegelBlock_diagSp {B : Finset (Fin n)} {t : Fin n → Fˣ}
    (ht : ∀ i ∈ B, ∀ j ∈ B, t i = t j) {x : StatedSp n F} (hx : x ∈ siegelBlock F B) :
    Commute x (diagSp F n t) := by
  obtain ⟨C, hC, rfl⟩ := hx
  refine commute_diagSp_leviEmbedGL (A := Matrix.SpecialLinearGroup.toGL C) ?_
  refine Units.ext ?_
  change (C : Matrix (Fin n) (Fin n) F) * (TauCeti.diagGL t : Matrix (Fin n) (Fin n) F) =
    (TauCeti.diagGL t : Matrix (Fin n) (Fin n) F) * (C : Matrix (Fin n) (Fin n) F)
  rw [TauCeti.diagGL_coe]
  refine (matrix_mul_diagonal_comm_iff _ _).2 fun i j hij => ?_
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  rw [hC i j (not_and_or.1 fun h => hij (by rw [ht i h.1 j h.2])), Matrix.one_apply_ne hij']

theorem siegelBlock_le_centralizer_of_const {B : Finset (Fin n)} {D : Set (Fin n → Fˣ)}
    (hconst : ∀ s ∈ D, ∀ i ∈ B, ∀ j ∈ B, s i = s j) :
    siegelBlock F B ≤ centralizer (diagSp F n '' D) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  exact (commute_siegelBlock_diagSp (hconst s hs) hx).eq.symm

theorem commutator_siegelBlock_eq {B : Finset (Fin n)}
    (hperf : ⁅blockSpecialLinear (K := F) B, blockSpecialLinear (K := F) B⁆ =
      blockSpecialLinear B) :
    ⁅siegelBlock F B, siegelBlock F B⁆ = siegelBlock F B := by
  rw [siegelBlock, ← Subgroup.map_commutator, hperf]

@[expose] noncomputable def siegelBlockEquiv (B : Finset (Fin n)) :
    Matrix.SpecialLinearGroup (Fin B.card) F ≃* siegelBlock F B :=
  ((LinearPilot.reindexSpecialLinear B.equivFin).symm.trans
      ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := F) B)).trans
        (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed B)))).trans
    ((blockSpecialLinear (K := F) B).equivMapOfInjective (leviEmbedSL F n) leviEmbedSL_injective)

end Siegel

section LeviFact

variable {F : Type} [Field F] {n : ℕ}

@[expose] def SameLagBlock (B : Finset (Fin n)) : Fin n ⊕ Fin n → Fin n ⊕ Fin n → Prop
  | Sum.inl i, Sum.inl j => i ∈ B ∧ j ∈ B
  | Sum.inr i, Sum.inr j => i ∈ B ∧ j ∈ B
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False

theorem not_sameLagBlock_of_not_mem {B : Finset (Fin n)} {a : Fin n ⊕ Fin n}
    (ha : a ∉ planeCoords B) (b : Fin n ⊕ Fin n) : ¬SameLagBlock B a b ∧ ¬SameLagBlock B b a := by
  have hi : ∀ i : Fin n, planeOf a = i → i ∉ B := fun i h hi => ha (by
    rw [mem_planeCoords, h]
    exact hi)
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [SameLagBlock, not_false_eq_true, and_self, not_and]
  · exact ⟨fun h => absurd h (hi i rfl), fun _ h => absurd h (hi i rfl)⟩
  · exact ⟨fun h => absurd h (hi i rfl), fun _ h => absurd h (hi i rfl)⟩

theorem mat_eq_zero_of_mem_spBlock_inf_centralizer_of_not_sameLagBlock {N B : Finset (Fin n)}
    {D : Set (Fin n → Fˣ)}
    (hsep : ∀ a ∈ planeCoords N, ∀ b ∈ planeCoords N, a ≠ b → ¬SameLagBlock B a b →
      ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b)
    {x : StatedSp n F} (hx : x ∈ spBlock F N ⊓ centralizer (diagSp F n '' D))
    {a b : Fin n ⊕ Fin n} (hab : a ≠ b) (hB : ¬SameLagBlock B a b) : mat n F x a b = 0 := by
  obtain ⟨hxN, hxD⟩ := mem_inf.1 hx
  by_cases hN : a ∈ planeCoords N ∧ b ∈ planeCoords N
  · obtain ⟨s, hs, hne⟩ := hsep a hN.1 b hN.2 hab hB
    have hc : Commute x (diagSp F n s) :=
      ((mem_centralizer_iff.1 hxD) _ ⟨s, hs, rfl⟩).symm
    exact (commute_diagSp_iff x s).1 hc a b hne
  · rw [hxN a b hN, Matrix.one_apply_ne hab]

theorem perfectCore_spBlock_inf_centralizer_eq_siegelBlock [Finite F] {N B : Finset (Fin n)}
    (hBN : B ⊆ N) (D : Set (Fin n → Fˣ)) (hconst : ∀ s ∈ D, ∀ i ∈ B, ∀ j ∈ B, s i = s j)
    (hsep : ∀ a ∈ planeCoords N, ∀ b ∈ planeCoords N, a ≠ b → ¬SameLagBlock B a b →
      ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b)
    (hperf : ⁅blockSpecialLinear (K := F) B, blockSpecialLinear (K := F) B⁆ =
      blockSpecialLinear B) :
    perfectCore (spBlock F N ⊓ centralizer (diagSp F n '' D)) = siegelBlock F B := by
  set C := spBlock F N ⊓ centralizer (diagSp F n '' D)
  have hzero : ∀ x ∈ C, ∀ a b, a ≠ b → ¬SameLagBlock B a b → mat n F x a b = 0 :=
    fun x hx a b hab hB =>
      mat_eq_zero_of_mem_spBlock_inf_centralizer_of_not_sameLagBlock hsep hx hab hB
  have hsiegel : ∀ x ∈ C, x ∈ siegelLeviGL F n := fun x hx =>
    mem_siegelLeviGL_of_blocks_eq_zero fun i j =>
      ⟨hzero x hx _ _ Sum.inl_ne_inr id, hzero x hx _ _ Sum.inr_ne_inl id⟩
  have h1 : ⁅C, C⁆ ≤ siegelLevi F n := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    rw [commutatorElement_def]
    exact commutator_mem_siegelLevi (hsiegel g hg) (hsiegel g' hg')
  have h2 : ⁅C, C⁆ ≤ spBlock F B :=
    CFSG.SeitzReduction.F4Pilot.commutator_le_suppGroup fun x hx a ha b hba =>
      ⟨hzero x hx a b hba.symm (not_sameLagBlock_of_not_mem ha b).1,
        hzero x hx b a hba (not_sameLagBlock_of_not_mem ha b).2⟩
  refine le_antisymm ?_ (le_perfectCore_of_perfect (le_inf
    ((siegelBlock_le_spBlock B).trans (spBlock_mono hBN))
    (siegelBlock_le_centralizer_of_const hconst)) (commutator_siegelBlock_eq hperf))
  calc perfectCore C = ⁅perfectCore C, perfectCore C⁆ := (perfectCore_perfect C).symm
    _ ≤ ⁅C, C⁆ := commutator_mono (perfectCore_le C) (perfectCore_le C)
    _ ≤ siegelLevi F n ⊓ spBlock F B := le_inf h1 h2
    _ ≤ siegelBlock F B := siegelLevi_inf_spBlock_le B

end LeviFact

section String

variable (K : Type) [Field K] {n : ℕ}

@[expose] def stringTorusParam (B : Finset (Fin n)) : Subgroup (Fin n → Kˣ) where
  carrier := {t | ∀ i ∈ B, ∀ j ∈ B, t i = t j}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := fun {t s} ht hs i hi j hj => by
    simp only [Pi.mul_apply, ht i hi j hj, hs i hi j hj]
  inv_mem' := fun {t} ht i hi j hj => by
    simp only [Pi.inv_apply, ht i hi j hj]

@[expose] noncomputable def stringTorusSp (B : Finset (Fin n)) : Subgroup (StatedSp n K) :=
  diagTorusSp K (stringTorusParam K B)

variable {K}

theorem mem_stringTorusParam {B : Finset (Fin n)} {t : Fin n → Kˣ} :
    t ∈ stringTorusParam K B ↔ ∀ i ∈ B, ∀ j ∈ B, t i = t j :=
  Iff.rfl

theorem pairTorusParam_eq_stringTorusParam (a b : Fin n) :
    pairTorusParam K a b = stringTorusParam K {a, b} := by
  ext t
  rw [mem_pairTorusParam, mem_stringTorusParam]
  constructor
  · intro h i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    exacts [rfl, h, h.symm, rfl]
  · intro h
    exact h a (by simp) b (by simp)

theorem leviTorusParam_string_eq {a b : ℕ} (hb : b < n) :
    leviTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      stringTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b) := by
  ext t
  rw [mem_leviTorusParam, mem_stringTorusParam]
  constructor
  · intro ht i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have ha : a < n := by omega
    have key : ∀ d : ℕ, ∀ i : Fin n, i.val = a + d → i.val ≤ b → t i = t ⟨a, ha⟩ := by
      intro d
      induction d with
      | zero =>
        intro i hi _
        exact congrArg t (Fin.ext hi)
      | succ d ih =>
        intro i hi hib
        have h1 : a + d + 1 < n := by omega
        have hJ : (⟨a + d, by omega⟩ : Fin n) ∈
            Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        have h2 := (ht _ hJ).1 h1
        rw [← ih ⟨a + d, by omega⟩ rfl (by simp; omega), h2]
        exact congrArg t (Fin.ext (by simp; omega))
    rw [key (i.val - a) i (by omega) hi.2, key (j.val - a) j (by omega) hj.2]
  · intro ht j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨fun h => ht j (by simp; omega) ⟨j.val + 1, h⟩ (by simp; omega), fun h => ?_⟩
    omega

theorem rootTorusSp_le_stringTorusSp {k : Fin n} {B : Finset (Fin n)} (hk : k ∉ B) :
    rootTorusSp K k ≤ stringTorusSp K B := by
  rintro _ ⟨κ, rfl⟩
  refine ⟨Pi.mulSingle k κ, fun i hi j hj => ?_, rfl⟩
  have hik : i ≠ k := fun h => hk (h ▸ hi)
  have hjk : j ≠ k := fun h => hk (h ▸ hj)
  simp [hik, hjk]

theorem exists_mem_stringTorusParam_diagSpEntry_ne {κ : Kˣ} (hκ : κ * κ ≠ 1)
    {B : Finset (Fin n)} {a b : Fin n ⊕ Fin n} (hab : a ≠ b) (hB : ¬SameLagBlock B a b) :
    ∃ t ∈ stringTorusParam K B, diagSpEntry t a ≠ diagSpEntry t b := by
  have hmem : ∀ i : Fin n, i ∉ B → Pi.mulSingle i κ ∈ stringTorusParam K B :=
    fun i hi j hj j' hj' => by
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hj'i : j' ≠ i := fun h => hi (h ▸ hj')
      simp [hji, hj'i]
  by_cases ha : a ∈ planeCoords B
  · by_cases hb : b ∈ planeCoords B
    ·
      have h3 : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun e =>
        units_ne_inv_of_mul_self_ne_one hκ (Units.ext e)
      let t : Fin n → Kˣ := fun i => if i ∈ B then κ else 1
      have ht : t ∈ stringTorusParam K B := fun i hi j hj => by simp [t, hi, hj]
      refine ⟨t, ht, ?_⟩
      rw [mem_planeCoords] at ha hb
      rcases a with i | i <;> rcases b with j | j
      · exact absurd ⟨ha, hb⟩ hB
      · have ha' : i ∈ B := ha
        have hb' : j ∈ B := hb
        simpa [t, ha', hb'] using h3
      · have ha' : i ∈ B := ha
        have hb' : j ∈ B := hb
        simpa [t, ha', hb'] using h3.symm
      · exact absurd ⟨ha, hb⟩ hB
    · exact ⟨_, hmem _ hb, diagSpEntry_mulSingle_ne hκ hab (Or.inr (mem_coords_planeOf b))⟩
  · exact ⟨_, hmem _ ha, diagSpEntry_mulSingle_ne hκ hab (Or.inl (mem_coords_planeOf a))⟩

theorem perfectCore_spBlock_inf_centralizer_stringTorus {F : Type} [Field F] [Finite F]
    (ι : K →+* F) {κ : Kˣ} (hκ : κ * κ ≠ 1) {N B : Finset (Fin n)} (hBN : B ⊆ N)
    (hperf : ⁅blockSpecialLinear (K := F) B, blockSpecialLinear (K := F) B⁆ =
      blockSpecialLinear B) :
    perfectCore (spBlock F N ⊓
        centralizer (diagSp F n '' (liftParam ι '' (stringTorusParam K B : Set (Fin n → Kˣ))))) =
      siegelBlock F B := by
  refine perfectCore_spBlock_inf_centralizer_eq_siegelBlock hBN _ ?_ (fun a _ b _ hab hB => ?_)
    hperf
  · rintro _ ⟨t, ht, rfl⟩ i hi j hj
    simp only [liftParam, ht i hi j hj]
  · obtain ⟨t, ht, hne⟩ := exists_mem_stringTorusParam_diagSpEntry_ne hκ hab hB
    refine ⟨liftParam ι t, ⟨t, ht, rfl⟩, ?_⟩
    rw [diagSpEntry_liftParam, diagSpEntry_liftParam]
    exact fun h => hne (ι.injective h)

end String

section Cores

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

@[expose] noncomputable def stringCore (B : Finset (Fin n)) : Subgroup G :=
  torusCore e (stringTorusParam K B)

theorem stringCore_def (B : Finset (Fin n)) :
    stringCore e B = centralizerPerfectCore (modelToG e (stringTorusSp K B)) :=
  rfl

theorem pieceCore_string_eq {a b : ℕ} (hb : b < n) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      stringCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b) := by
  rw [pieceCore_eq_torusCore, leviTorusParam_string_eq hb, stringCore]

theorem pieceCore_singleton_eq_stringCore {j : Fin n} (h : j.val + 1 < n) :
    pieceCore e {j} = stringCore e {j, ⟨j.val + 1, h⟩} := by
  rw [pieceCore_eq_torusCore, leviTorusParam_singleton_of_lt h,
    pairTorusParam_eq_stringTorusParam, stringCore]

theorem modelToG_rootTorusSp_le_stringTorusSp {k : Fin n} {B : Finset (Fin n)} (hk : k ∉ B) :
    modelToG e (rootTorusSp K k) ≤ modelToG e (stringTorusSp K B) :=
  modelToG_mono e (rootTorusSp_le_stringTorusSp hk)

theorem stringCore_le_neighbourCore {k : Fin n} {B : Finset (Fin n)} (hk : k ∉ B) :
    stringCore e B ≤ neighbourCore e k :=
  CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_anti
    (modelToG_rootTorusSp_le_stringTorusSp e hk)

theorem modelToG_siegelBlock_le_stringCore {B : Finset (Fin n)}
    (hperf : ⁅blockSpecialLinear (K := K) B, blockSpecialLinear (K := K) B⁆ =
      blockSpecialLinear B) :
    modelToG e (siegelBlock K B) ≤ stringCore e B := by
  refine UnitaryPilot.modelToG_le_centralizerPerfectCore e ?_ (commutator_siegelBlock_eq hperf)
  have hset : ((stringTorusSp K B : Subgroup (StatedSp n K)) : Set (StatedSp n K)) =
      diagSp K n '' (stringTorusParam K B : Set (Fin n → Kˣ)) := Subgroup.coe_map _ _
  change siegelBlock K B ≤ centralizer ((stringTorusSp K B : Subgroup (StatedSp n K)) :
    Set (StatedSp n K))
  rw [hset]
  exact siegelBlock_le_centralizer_of_const fun s hs => hs

theorem stringCore_eq [Finite G] {k : Fin n} {B : Finset (Fin n)} (hk : k ∉ B) :
    stringCore e B = perfectCore (neighbourCore e k ⊓
      centralizer (modelToG e (stringTorusSp K B) : Set G)) :=
  UnitaryPilot.centralizerPerfectCore_modelToG_eq_perfectCore_inf e
    (modelToG_rootTorusSp_le_stringTorusSp e hk)

end Cores

section Piece

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

theorem stringCore_eq_map_of_conjDiagSp {κ : Kˣ} (hκ : κ * κ ≠ 1) {N B : Finset (Fin n)}
    (hBN : B ⊆ N)
    (hperf : ⁅blockSpecialLinear (K := F) B, blockSpecialLinear (K := F) B⁆ =
      blockSpecialLinear B)
    {X : Subgroup G} (hXB : X ≤ modelToG e (stringTorusSp K B))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : TorusEquivariant e ι N (stringTorusParam K B) Φ) :
    stringCore e B = ((siegelBlock F B).subgroupOf (spBlock F N)).map Φ :=
  torusCore_eq_map_of_conjDiagSp e ι ((siegelBlock_le_spBlock B).trans (spBlock_mono hBN))
    (perfectCore_spBlock_inf_centralizer_stringTorus ι hκ hBN hperf) hXB Φ hker hrange hΦ

theorem stringCore_eq_map_of_conjDiagSp_of_four_le (hK : 4 ≤ Nat.card K)
    {N B : Finset (Fin n)} (hBN : B ⊆ N) (hB : 2 ≤ B.card)
    {X : Subgroup G} (hXB : X ≤ modelToG e (stringTorusSp K B))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : TorusEquivariant e ι N (stringTorusParam K B) Φ) :
    stringCore e B = ((siegelBlock F B).subgroupOf (spBlock F N)).map Φ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact stringCore_eq_map_of_conjDiagSp e ι hκ hBN
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hB (le_card_of_ringHom ι hK))
    hXB Φ hker hrange hΦ

theorem pieceCore_string_eq_map_of_neighbourCore (hK : 4 ≤ Nat.card K) {a b : ℕ} (hab : a < b)
    (hb : b < n) {k : Fin n} (hk : k ∉ Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)
    (Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Φ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Φ.range = neighbourCore e k)
    (hΦ : TorusEquivariant e ι {k}ᶜ
      (stringTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)) Φ) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      ((siegelBlock F (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
        (spBlock F ({k}ᶜ : Finset (Fin n)))).map Φ := by
  have hB : 2 ≤ (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b).card := by
    refine Finset.one_lt_card.2 ⟨⟨a, by omega⟩, by simp; omega, ⟨b, hb⟩, by simp; omega, ?_⟩
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [pieceCore_string_eq e hb]
  exact stringCore_eq_map_of_conjDiagSp_of_four_le e ι hK (subset_compl_singleton_of_notMem hk) hB
    (modelToG_rootTorusSp_le_stringTorusSp e hk) Φ hker hrange hΦ

theorem nonempty_mulEquiv_stringCore_of_conjDiagSp [CharP F 2] (hK : 4 ≤ Nat.card K)
    {N B : Finset (Fin n)} (hBN : B ⊆ N) (hB : 2 ≤ B.card) {X : Subgroup G}
    (hXB : X ≤ modelToG e (stringTorusSp K B))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : TorusEquivariant e ι N (stringTorusParam K B) Φ) :
    Nonempty (Matrix.SpecialLinearGroup (Fin B.card) F ≃* stringCore e B) := by
  set H := (siegelBlock F B).subgroupOf (spBlock F N)
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_spBlock_eq_bot N).le
  have hrangeH : (Φ.comp H.subtype).range = stringCore e B := by
    rw [MonoidHom.range_comp, range_subtype,
      stringCore_eq_map_of_conjDiagSp_of_four_le e ι hK hBN hB hXB Φ hker hrange hΦ]
  have e₁ : H ≃* stringCore e B :=
    (MonoidHom.ofInjective (f := Φ.comp H.subtype) (hinj.comp H.subtype_injective)).trans
      (MulEquiv.subgroupCongr hrangeH)
  have e₂ : siegelBlock F B ≃* H :=
    (Subgroup.subgroupOfEquivOfLe ((siegelBlock_le_spBlock B).trans (spBlock_mono hBN))).symm
  exact ⟨(siegelBlockEquiv B).trans (e₂.trans e₁)⟩

end Piece

section Disjoint

theorem map_subgroupOf_le_centralizer_of_disjoint {G : Type*} [Group G] {F : Type} [Field F]
    {n : ℕ} {N I J : Finset (Fin n)} (hIJ : Disjoint I J) {H₁ H₂ : Subgroup (StatedSp n F)}
    (h₁ : H₁ ≤ spBlock F I) (h₂ : H₂ ≤ spBlock F J) (Φ : spBlock F N →* G) :
    (H₁.subgroupOf (spBlock F N)).map Φ ≤
      centralizer (((H₂.subgroupOf (spBlock F N)).map Φ : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h : y * x = x * y := Subtype.ext (commute_of_mem_spBlock_of_disjoint hIJ
    (h₁ (mem_subgroupOf.1 hx)) (h₂ (mem_subgroupOf.1 hy))).eq.symm
  rw [← map_mul, ← map_mul, h]

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

theorem stringCore_le_centralizer_planeCore_of_disjoint (hK : 4 ≤ Nat.card K)
    {N B I : Finset (Fin n)} (hBN : B ⊆ N) (hIN : I ⊆ N) (hBI : Disjoint B I) (hB : 2 ≤ B.card)
    {X : Subgroup G} (hXB : X ≤ modelToG e (stringTorusSp K B))
    (hXI : X ≤ modelToG e (planeTorusSp K I))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦB : TorusEquivariant e ι N (stringTorusParam K B) Φ)
    (hΦI : TorusEquivariant e ι N (planeTorusParam K I) Φ) :
    stringCore e B ≤ centralizer (planeCore e I : Set G) := by
  rw [stringCore_eq_map_of_conjDiagSp_of_four_le e ι hK hBN hB hXB Φ hker hrange hΦB,
    planeCore_eq_map_of_conjDiagSp_of_four_le e ι hK hIN hXI Φ hker hrange hΦI]
  exact map_subgroupOf_le_centralizer_of_disjoint hBI (siegelBlock_le_spBlock B) le_rfl Φ

theorem stringCore_le_centralizer_stringCore_of_disjoint (hK : 4 ≤ Nat.card K)
    {N B B' : Finset (Fin n)} (hBN : B ⊆ N) (hB'N : B' ⊆ N) (hBB' : Disjoint B B')
    (hB : 2 ≤ B.card) (hB' : 2 ≤ B'.card)
    {X : Subgroup G} (hXB : X ≤ modelToG e (stringTorusSp K B))
    (hXB' : X ≤ modelToG e (stringTorusSp K B'))
    (Φ : spBlock F N →* G) (hker : Φ.ker ≤ center (spBlock F N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦB : TorusEquivariant e ι N (stringTorusParam K B) Φ)
    (hΦB' : TorusEquivariant e ι N (stringTorusParam K B') Φ) :
    stringCore e B ≤ centralizer (stringCore e B' : Set G) := by
  rw [stringCore_eq_map_of_conjDiagSp_of_four_le e ι hK hBN hB hXB Φ hker hrange hΦB,
    stringCore_eq_map_of_conjDiagSp_of_four_le e ι hK hB'N hB' hXB' Φ hker hrange hΦB']
  exact map_subgroupOf_le_centralizer_of_disjoint hBB' (siegelBlock_le_spBlock B)
    (siegelBlock_le_spBlock B') Φ

end Disjoint

section Transport

theorem image_sumMap_planeCoords {n : ℕ} (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    Sum.map π π '' planeCoords I = planeCoords (I.map π.toEmbedding) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases x with i | i <;>
      exact Finset.mem_map_of_mem π.toEmbedding (show i ∈ I from hx)
  · intro ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_map.1 (show planeOf a ∈ I.map π.toEmbedding from ha)
    rcases a with j | j
    · exact ⟨Sum.inl i, hi, by
        simp only [Sum.map_inl, Equiv.coe_toEmbedding] at hia ⊢
        rw [hia, planeOf_inl]⟩
    · exact ⟨Sum.inr i, hi, by
        simp only [Sum.map_inr, Equiv.coe_toEmbedding] at hia ⊢
        rw [hia, planeOf_inr]⟩

theorem map_conj_permSp_spBlock {F : Type} [Field F] {n : ℕ} (π : Equiv.Perm (Fin n))
    (I : Finset (Fin n)) :
    (spBlock F I).map (MulAut.conj (permSp F π)).toMonoidHom = spBlock F (I.map π.toEmbedding) := by
  rw [spBlock, map_conj_permSp_suppGroup, image_sumMap_planeCoords, spBlock]

theorem map_permParam_stringTorusParam {K : Type} [Field K] {n : ℕ} (π : Equiv.Perm (Fin n))
    (B : Finset (Fin n)) :
    (stringTorusParam K B).map (permParam K π) = stringTorusParam K (B.map π.toEmbedding) := by
  ext t
  rw [mem_map, mem_stringTorusParam]
  constructor
  · rintro ⟨s, hs, rfl⟩ i hi j hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.1 hj
    simp only [coe_permParam, Function.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    exact hs i' hi' j' hj'
  · intro ht
    refine ⟨t ∘ π, fun i hi j hj => ht (π i) (Finset.mem_map_of_mem _ hi) (π j)
      (Finset.mem_map_of_mem _ hj), ?_⟩
    funext j
    simp [coe_permParam]

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

theorem modelToG_spBlock_map_eq (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    modelToG e (spBlock K (I.map π.toEmbedding)) =
      (modelToG e (spBlock K I)).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  rw [← map_conj_permSp_spBlock, UnitaryPilot.modelToG_map_conj]

theorem stringCore_map_eq [Finite G] (π : Equiv.Perm (Fin n)) (B : Finset (Fin n)) :
    stringCore e (B.map π.toEmbedding) =
      (stringCore e B).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  rw [stringCore, stringCore, ← map_permParam_stringTorusParam, torusCore_map_permParam]

end Transport

end CFSG.SeitzReduction.SymplecticPilot
