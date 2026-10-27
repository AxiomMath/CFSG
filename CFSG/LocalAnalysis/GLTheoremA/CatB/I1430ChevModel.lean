module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430AltTrans
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430ChevModel

open Matrix CFSG.Open

abbrev Blk2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

def chJ : Blk2 := !![0, 1; -1, 0]

def chA : Blk2 := !![0, 1; 1, 1]

def chA2 : Blk2 := !![1, 1; 1, 0]

def chT : Blk2 := !![1, 1; 0, 1]

def chRho (k : ZMod 3) : Blk2 := if k = 0 then 1 else if k = 1 then chA else chA2

theorem chRho_add : ∀ k l : ZMod 3, chRho (k + l) = chRho k * chRho l := by decide

theorem chRho_eq_one : ∀ k : ZMod 3, chRho k = 1 → k = 0 := by decide

theorem chRho_symp : ∀ k : ZMod 3, (chRho k)ᵀ * chJ * chRho k = chJ := by decide

theorem chT_symp : chTᵀ * chJ * chT = chJ := by decide

theorem chT_mul_self : chT * chT = 1 := by decide

theorem chT_ne_one : chT ≠ 1 := by decide

theorem chOne_symp : (1 : Blk2)ᵀ * chJ * 1 = chJ := by
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

def chBlk {ℓ : ℕ} (M : Fin ℓ → Blk2) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) (ZMod 2) :=
  fromBlocks (diagonal fun i => M i 0 0) (diagonal fun i => M i 0 1)
    (diagonal fun i => M i 1 0) (diagonal fun i => M i 1 1)

def chGram (ℓ : ℕ) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) (ZMod 2) :=
  fromBlocks 0 1 (-1) 0

theorem chBlk_mul {ℓ : ℕ} (M N : Fin ℓ → Blk2) :
    chBlk (fun i => M i * N i) = chBlk M * chBlk N := by
  unfold chBlk
  rw [fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, ← diagonal_add, mul_apply, Fin.sum_univ_two]

theorem chBlk_transpose {ℓ : ℕ} (M : Fin ℓ → Blk2) : (chBlk M)ᵀ = chBlk (fun i => (M i)ᵀ) := by
  unfold chBlk
  rw [fromBlocks_transpose]
  simp only [diagonal_transpose, transpose_apply]

theorem chBlk_one {ℓ : ℕ} : chBlk (fun _ : Fin ℓ => (1 : Blk2)) = 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [chBlk, Matrix.one_apply, Matrix.diagonal_apply]

theorem chBlk_gram {ℓ : ℕ} : chBlk (fun _ : Fin ℓ => chJ) = chGram ℓ := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> by_cases h : a = b <;>
    simp [chBlk, chGram, chJ, Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply, h] <;> decide

theorem chBlk_symp {ℓ : ℕ} {M : Fin ℓ → Blk2} (hM : ∀ i, (M i)ᵀ * chJ * M i = chJ) :
    (chBlk M)ᵀ * chGram ℓ * chBlk M = chGram ℓ := by
  rw [← chBlk_gram, chBlk_transpose, ← chBlk_mul, ← chBlk_mul]
  congr 1
  funext i
  exact hM i

theorem chBlk_injective {ℓ : ℕ} :
    Function.Injective (chBlk : (Fin ℓ → Blk2) → Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) (ZMod 2)) := by
  intro M N h
  funext i
  ext a b
  have e1 := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have e2 := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  have e3 := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
  have e4 := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
  simp only [chBlk, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.diagonal_apply_eq] at e1 e2 e3 e4
  fin_cases a <;> fin_cases b <;> simp_all

def chChi {ℓ : ℕ} (x : ZMod 3 × ZMod 3 × ZMod 3) (i : Fin ℓ) : Blk2 :=
  if i.val = 0 then chRho x.1 else if i.val = 1 then chRho x.2.1
    else if i.val = 2 then chRho x.2.2 else 1

theorem chChi_add {ℓ : ℕ} (x y : ZMod 3 × ZMod 3 × ZMod 3) :
    chChi (ℓ := ℓ) (x + y) = fun i => chChi x i * chChi y i := by
  funext i
  unfold chChi
  split_ifs <;> simp [chRho_add]

theorem chChi_zero {ℓ : ℕ} : chChi (ℓ := ℓ) 0 = fun _ => 1 := by
  funext i
  unfold chChi
  split_ifs <;> simp [chRho]

theorem chChi_symp {ℓ : ℕ} (x : ZMod 3 × ZMod 3 × ZMod 3) (i : Fin ℓ) :
    (chChi x i)ᵀ * chJ * chChi x i = chJ := by
  unfold chChi
  split_ifs
  · exact chRho_symp _
  · exact chRho_symp _
  · exact chRho_symp _
  · exact chOne_symp

def chBlkC {ℓ : ℕ} (x : ZMod 3 × ZMod 3 × ZMod 3) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) (ZMod 2) :=
  chBlk (chChi x)

theorem chBlkC_mul {ℓ : ℕ} (x y : ZMod 3 × ZMod 3 × ZMod 3) :
    chBlkC (ℓ := ℓ) x * chBlkC y = chBlkC (x + y) := by
  unfold chBlkC
  rw [← chBlk_mul, chChi_add]

theorem chBlkC_zero {ℓ : ℕ} : chBlkC (ℓ := ℓ) 0 = 1 := by
  unfold chBlkC
  rw [chChi_zero, chBlk_one]

theorem chAddNeg : ∀ x : ZMod 3 × ZMod 3 × ZMod 3, x + -x = 0 := by decide

theorem chNegAdd : ∀ x : ZMod 3 × ZMod 3 × ZMod 3, -x + x = 0 := by decide

def chGL (ℓ : ℕ) (x : ZMod 3 × ZMod 3 × ZMod 3) :
    Matrix.GeneralLinearGroup (Fin ℓ ⊕ Fin ℓ) (ZMod 2) :=
  ⟨chBlkC x, chBlkC (-x), by rw [chBlkC_mul, chAddNeg, chBlkC_zero],
    by rw [chBlkC_mul, chNegAdd, chBlkC_zero]⟩

theorem chGL_mul {ℓ : ℕ} (x y : ZMod 3 × ZMod 3 × ZMod 3) :
    chGL ℓ x * chGL ℓ y = chGL ℓ (x + y) :=
  Units.ext (chBlkC_mul x y)

theorem chGL_mem {ℓ : ℕ} (x : ZMod 3 × ZMod 3 × ZMod 3) : chGL ℓ x ∈ StatedSp ℓ (ZMod 2) := by
  apply Subgroup.subset_closure
  show (chBlkC x)ᵀ * chGram ℓ * chBlkC x = chGram ℓ
  exact chBlk_symp (chChi_symp x)

def chTrip (ℓ : ℕ) : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* ↥(StatedSp ℓ (ZMod 2)) :=
  MonoidHom.mk' (fun x => ⟨chGL ℓ (Multiplicative.toAdd x), chGL_mem _⟩) fun x y =>
    Subtype.ext (chGL_mul (Multiplicative.toAdd x) (Multiplicative.toAdd y)).symm

theorem chTrip_injective {ℓ : ℕ} (hℓ : 3 ≤ ℓ) : Function.Injective (chTrip ℓ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : chGL ℓ (Multiplicative.toAdd x) = 1 := congrArg Subtype.val hx
  have h2 : chBlk (chChi (Multiplicative.toAdd x)) = chBlk (fun _ : Fin ℓ => (1 : Blk2)) := by
    rw [chBlk_one]
    exact congrArg Units.val h1
  have h3 : chChi (Multiplicative.toAdd x) = fun _ => 1 := chBlk_injective h2
  have h0 : chRho (Multiplicative.toAdd x).1 = 1 := by
    have := congrFun h3 ⟨0, by omega⟩
    simpa [chChi] using this
  have h1' : chRho (Multiplicative.toAdd x).2.1 = 1 := by
    have := congrFun h3 ⟨1, by omega⟩
    simpa [chChi] using this
  have h2' : chRho (Multiplicative.toAdd x).2.2 = 1 := by
    have := congrFun h3 ⟨2, by omega⟩
    simpa [chChi] using this
  have hx0 : Multiplicative.toAdd x = 0 :=
    Prod.ext (chRho_eq_one _ h0) (Prod.ext (chRho_eq_one _ h1') (chRho_eq_one _ h2'))
  exact Multiplicative.toAdd.injective (hx0.trans toAdd_one.symm)

def chTvec (ℓ : ℕ) : Fin ℓ → Blk2 := fun i => if i.val = 3 then chT else 1

theorem chTvec_sq (ℓ : ℕ) : (fun i => chTvec ℓ i * chTvec ℓ i) = fun _ => 1 := by
  funext i
  unfold chTvec
  split_ifs <;> simp [chT_mul_self]

theorem chTvec_symp (ℓ : ℕ) (i : Fin ℓ) : (chTvec ℓ i)ᵀ * chJ * chTvec ℓ i = chJ := by
  unfold chTvec
  split_ifs
  · exact chT_symp
  · exact chOne_symp

def chTGL (ℓ : ℕ) : Matrix.GeneralLinearGroup (Fin ℓ ⊕ Fin ℓ) (ZMod 2) :=
  ⟨chBlk (chTvec ℓ), chBlk (chTvec ℓ), by rw [← chBlk_mul, chTvec_sq, chBlk_one],
    by rw [← chBlk_mul, chTvec_sq, chBlk_one]⟩

theorem chTGL_mem (ℓ : ℕ) : chTGL ℓ ∈ StatedSp ℓ (ZMod 2) := by
  apply Subgroup.subset_closure
  show (chBlk (chTvec ℓ))ᵀ * chGram ℓ * chBlk (chTvec ℓ) = chGram ℓ
  exact chBlk_symp (chTvec_symp ℓ)

def chTU (ℓ : ℕ) : ↥(StatedSp ℓ (ZMod 2)) := ⟨chTGL ℓ, chTGL_mem ℓ⟩

theorem chTGL_commute {ℓ : ℕ} (x : ZMod 3 × ZMod 3 × ZMod 3) :
    chTGL ℓ * chGL ℓ x = chGL ℓ x * chTGL ℓ := by
  apply Units.ext
  show chBlk (chTvec ℓ) * chBlkC x = chBlkC x * chBlk (chTvec ℓ)
  unfold chBlkC
  rw [← chBlk_mul, ← chBlk_mul]
  congr 1
  funext i
  unfold chTvec chChi
  split_ifs <;> first | omega | simp

theorem chTU_comm {ℓ : ℕ} (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)) :
    chTU ℓ * chTrip ℓ x = chTrip ℓ x * chTU ℓ :=
  Subtype.ext (chTGL_commute (Multiplicative.toAdd x))

theorem chTU_sq (ℓ : ℕ) : chTU ℓ ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Units.ext
  show chBlk (chTvec ℓ) * chBlk (chTvec ℓ) = 1
  rw [← chBlk_mul, chTvec_sq, chBlk_one]

theorem chTU_ne_one {ℓ : ℕ} (hℓ : 4 ≤ ℓ) : chTU ℓ ≠ 1 := by
  intro h
  have h1 : chTGL ℓ = 1 := congrArg Subtype.val h
  have h2 : chBlk (chTvec ℓ) = chBlk (fun _ : Fin ℓ => (1 : Blk2)) := by
    rw [chBlk_one]
    exact congrArg Units.val h1
  have h3 : chTvec ℓ = fun _ => 1 := chBlk_injective h2
  have h4 := congrFun h3 ⟨3, by omega⟩
  simp [chTvec] at h4
  exact chT_ne_one h4

abbrev chE (ℓ : ℕ) : Subgroup ↥(StatedSp ℓ (ZMod 2)) := (chTrip ℓ).range

theorem chE_card {ℓ : ℕ} (hℓ : 3 ≤ ℓ) : Nat.card (chE ℓ) = 3 ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (chTrip_injective hℓ)).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem chTrip_cube : ∀ x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3), x ^ 3 = 1 := by decide

theorem chE_isElemAbelian {ℓ : ℕ} : IsElemAbelian 3 (chE ℓ) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    change a.1 * b.1 = b.1 * a.1
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, chTrip_cube, map_one]

theorem chU_ne_bot {ℓ : ℕ} (hℓ : 4 ≤ ℓ) : Subgroup.zpowers (chTU ℓ) ≠ ⊥ := by
  intro h
  apply chTU_ne_one hℓ
  have hmem : chTU ℓ ∈ Subgroup.zpowers (chTU ℓ) := Subgroup.mem_zpowers _
  rw [h] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem chU_pGroup {ℓ : ℕ} (hℓ : 4 ≤ ℓ) : IsPGroup 2 (Subgroup.zpowers (chTU ℓ)) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, orderOf_eq_prime (chTU_sq ℓ) (chTU_ne_one hℓ)]
  norm_num

theorem chE_le_normalizer {ℓ : ℕ} :
    chE ℓ ≤ Subgroup.normalizer ((Subgroup.zpowers (chTU ℓ) : Subgroup ↥(StatedSp ℓ (ZMod 2))) :
      Set ↥(StatedSp ℓ (ZMod 2))) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hc : Commute (chTU ℓ) (chTrip ℓ x) := chTU_comm x
  exact (hc.zpow_left k).eq

theorem i1430TwoLocal_statedSp (ℓ : ℕ) (hℓ : 4 ≤ ℓ) : I1430TwoLocal ↥(StatedSp ℓ (ZMod 2)) 3 :=
  ⟨Subgroup.zpowers (chTU ℓ), chE ℓ, chU_ne_bot hℓ, chU_pGroup hℓ, chE_le_normalizer,
    chE_isElemAbelian, chE_card (by omega)⟩

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430ChevModel
