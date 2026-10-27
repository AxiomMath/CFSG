module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

namespace L62Model

abbrev ι₂ : Type := Fin 2 ⊕ Fin 2

abbrev ι : Type := Fin 2 ⊕ ι₂

@[expose] def Y : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

@[expose] def Y' : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 1, 0]

theorem Y_mul_Y' : Y * Y' = 1 := by decide
theorem Y'_mul_Y : Y' * Y = 1 := by decide
@[expose] def levi (A A' : Matrix (Fin 2) (Fin 2) (ZMod 2)) (B B' : Matrix ι₂ ι₂ (ZMod 2))
    (hA : A * A' = 1) (hA' : A' * A = 1) (hB : B * B' = 1) (hB' : B' * B = 1) :
    (Matrix ι ι (ZMod 2))ˣ where
  val := fromBlocks A 0 0 B
  inv := fromBlocks A' 0 0 B'
  val_inv := by
    rw [fromBlocks_multiply]
    simp [hA, hB]
  inv_val := by
    rw [fromBlocks_multiply]
    simp [hA', hB']

theorem add_self_mat {m n : Type*} [Fintype m] [Fintype n] (φ : Matrix m n (ZMod 2)) :
    φ + φ = 0 := by
  ext i j
  have : ∀ x : ZMod 2, x + x = 0 := by decide
  simp [this]

@[expose] def Tm (φ : Matrix ι₂ (Fin 2) (ZMod 2)) : (Matrix ι ι (ZMod 2))ˣ where
  val := fromBlocks 1 0 φ 1
  inv := fromBlocks 1 0 φ 1
  val_inv := by
    rw [fromBlocks_multiply]
    simp [add_self_mat]
  inv_val := by
    rw [fromBlocks_multiply]
    simp [add_self_mat]

theorem Tm_mul (φ ψ : Matrix ι₂ (Fin 2) (ZMod 2)) : Tm φ * Tm ψ = Tm (φ + ψ) := by
  apply Units.ext
  show fromBlocks 1 0 φ 1 * fromBlocks 1 0 ψ 1 = fromBlocks 1 0 (φ + ψ) 1
  rw [fromBlocks_multiply]
  simp [add_comm]

theorem Tm_zero : Tm 0 = 1 := by
  apply Units.ext
  show fromBlocks 1 0 0 1 = 1
  exact fromBlocks_one

theorem Tm_inv (φ : Matrix ι₂ (Fin 2) (ZMod 2)) : (Tm φ)⁻¹ = Tm φ := rfl

@[expose] def Rsub : Subgroup (Matrix ι ι (ZMod 2))ˣ where
  carrier := {g | ∃ φ, g = Tm φ}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨φ + ψ, Tm_mul φ ψ⟩
  one_mem' := ⟨0, Tm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨φ, rfl⟩
    exact ⟨φ, Tm_inv φ⟩

theorem isElemAbelian_Rsub : IsElemAbelian 2 Rsub := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨φ, hφ⟩ := a.2
    obtain ⟨ψ, hψ⟩ := b.2
    apply Subtype.ext
    change (a : (Matrix ι ι (ZMod 2))ˣ) * b = b * a
    rw [hφ, hψ, Tm_mul, Tm_mul, add_comm]
  · obtain ⟨φ, rfl⟩ := hx
    rw [pow_two, Tm_mul, add_self_mat, Tm_zero]

theorem Rsub_ne_bot : Rsub ≠ ⊥ := by
  intro h
  have hmem : Tm (Matrix.single (Sum.inl 0) 0 1) ∈ Rsub := ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg (fun g : (Matrix ι ι (ZMod 2))ˣ => (g : Matrix ι ι (ZMod 2))) hmem
  revert this
  decide

theorem levi_conj (A A' : Matrix (Fin 2) (Fin 2) (ZMod 2)) (B B' : Matrix ι₂ ι₂ (ZMod 2))
    (hA : A * A' = 1) (hA' : A' * A = 1) (hB : B * B' = 1) (hB' : B' * B = 1)
    (φ : Matrix ι₂ (Fin 2) (ZMod 2)) :
    levi A A' B B' hA hA' hB hB' * Tm φ * (levi A A' B B' hA hA' hB hB')⁻¹ = Tm (B * φ * A') := by
  apply Units.ext
  show fromBlocks A 0 0 B * fromBlocks 1 0 φ 1 * fromBlocks A' 0 0 B' =
    fromBlocks 1 0 (B * φ * A') 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [hA, hB, mul_assoc]

theorem levi_mem_normalizer (A A' : Matrix (Fin 2) (Fin 2) (ZMod 2)) (B B' : Matrix ι₂ ι₂ (ZMod 2))
    (hA : A * A' = 1) (hA' : A' * A = 1) (hB : B * B' = 1) (hB' : B' * B = 1) :
    levi A A' B B' hA hA' hB hB' ∈ Subgroup.normalizer (Rsub : Set (Matrix ι ι (ZMod 2))ˣ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨_, levi_conj A A' B B' hA hA' hB hB' φ⟩
  · rintro ⟨ψ, hψ⟩
    have h1 := levi_conj A' A B' B hA' hA hB' hB ψ
    have h2 : (levi A A' B B' hA hA' hB hB')⁻¹ = levi A' A B' B hA' hA hB' hB := rfl
    refine ⟨B' * ψ * A, ?_⟩
    rw [← h1, ← h2, ← hψ]
    group

theorem fb_mul_Y : fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
    fromBlocks Y' 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by decide

theorem fb_mul_Y' : fromBlocks Y' 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
    fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by decide

theorem fb_mul_Z : fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y *
    fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y' = 1 := by decide

theorem fb_mul_Z' : fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y' *
    fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y = 1 := by decide

@[expose] def y1 : (Matrix ι ι (ZMod 2))ˣ :=
  levi Y Y' 1 1 Y_mul_Y' Y'_mul_Y (mul_one _) (mul_one _)

@[expose] def y2 : (Matrix ι ι (ZMod 2))ˣ :=
  levi 1 1 (fromBlocks Y 0 0 1) (fromBlocks Y' 0 0 1) (mul_one _) (mul_one _) fb_mul_Y fb_mul_Y'

@[expose] def y3 : (Matrix ι ι (ZMod 2))ˣ :=
  levi 1 1 (fromBlocks 1 0 0 Y) (fromBlocks 1 0 0 Y') (mul_one _) (mul_one _) fb_mul_Z fb_mul_Z'

theorem y1_cube : y1 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (fromBlocks Y 0 0 (1 : Matrix ι₂ ι₂ (ZMod 2))) ^ 3 = 1
  decide +kernel

theorem y2_cube : y2 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (fromBlocks 1 0 0 (fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)))) ^ 3 = 1
  decide +kernel

theorem y3_cube : y3 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (fromBlocks 1 0 0 (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y)) ^ 3 = 1
  decide +kernel

theorem y12_comm : y1 * y2 = y2 * y1 := by
  apply Units.ext
  change fromBlocks Y 0 0 (1 : Matrix ι₂ ι₂ (ZMod 2)) *
      fromBlocks 1 0 0 (fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))) =
    fromBlocks 1 0 0 (fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))) *
      fromBlocks Y 0 0 (1 : Matrix ι₂ ι₂ (ZMod 2))
  decide +kernel

theorem y13_comm : y1 * y3 = y3 * y1 := by
  apply Units.ext
  change fromBlocks Y 0 0 (1 : Matrix ι₂ ι₂ (ZMod 2)) *
      fromBlocks 1 0 0 (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y) =
    fromBlocks 1 0 0 (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y) *
      fromBlocks Y 0 0 (1 : Matrix ι₂ ι₂ (ZMod 2))
  decide +kernel

theorem y23_comm : y2 * y3 = y3 * y2 := by
  apply Units.ext
  change fromBlocks 1 0 0 (fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))) *
      fromBlocks 1 0 0 (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y) =
    fromBlocks 1 0 0 (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 Y) *
      fromBlocks 1 0 0 (fromBlocks Y 0 0 (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)))
  decide +kernel

theorem isElemAbelian_closure {G : Type*} [Group G] (p : ℕ) {k : Set G}
    (hcomm : k.Pairwise Commute) (hexp : ∀ x ∈ k, x ^ p = 1) :
    IsElemAbelian p (Subgroup.closure k) := by
  have hC := Subgroup.isMulCommutative_closure hcomm
  refine ⟨hC, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hexp x hx
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc : Commute a b :=
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure k) ⟨b, hb⟩)
    rw [hc.mul_pow, iha, ihb, mul_one]
  | inv a ha iha =>
    rw [inv_pow, iha, inv_one]

@[expose] def E0 : Subgroup (Matrix ι ι (ZMod 2))ˣ := Subgroup.closure {y1, y2, y3}

theorem pairwise_comm : ({y1, y2, y3} : Set (Matrix ι ι (ZMod 2))ˣ).Pairwise Commute := by
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact y12_comm
  · exact y13_comm
  · exact y12_comm.symm
  · exact absurd rfl hab
  · exact y23_comm
  · exact y13_comm.symm
  · exact y23_comm.symm
  · exact absurd rfl hab

theorem isElemAbelian_E0 : IsElemAbelian 3 E0 := by
  refine isElemAbelian_closure 3 pairwise_comm ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact y1_cube
  · exact y2_cube
  · exact y3_cube

theorem E0_le_normalizer : E0 ≤ Subgroup.normalizer (Rsub : Set (Matrix ι ι (ZMod 2))ˣ) := by
  rw [E0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact levi_mem_normalizer _ _ _ _ _ _ _ _
  · exact levi_mem_normalizer _ _ _ _ _ _ _ _
  · exact levi_mem_normalizer _ _ _ _ _ _ _ _

@[expose] def f27 (x : Fin 3 × Fin 3 × Fin 3) : (Matrix ι ι (ZMod 2))ˣ :=
  y1 ^ (x.1 : ℕ) * y2 ^ (x.2.1 : ℕ) * y3 ^ (x.2.2 : ℕ)

theorem f27_injective : Function.Injective f27 := by
  decide +kernel

theorem f27_mem (x : Fin 3 × Fin 3 × Fin 3) : f27 x ∈ E0 :=
  mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _))
    (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem card_E0 : Nat.card E0 = 27 := by
  apply le_antisymm
  · have hE := isElemAbelian_E0
    haveI := hE.1
    have h := Rank3.card_le_three_pow_of_injective' (ι := ι) (E := ↥E0) (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (by simpa using hE.2 e e.2)) E0.subtype E0.subtype_injective
    have hι : Fintype.card ι = 6 := by simp [ι, ι₂]
    rw [hι] at h
    simpa using h
  · have hinj : Function.Injective (fun x : Fin 3 × Fin 3 × Fin 3 => (⟨f27 x, f27_mem x⟩ : E0)) :=
      fun a b h => f27_injective (congrArg Subtype.val h)
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this

theorem exists_pair : ∃ E₀ U₀ : Subgroup (Matrix ι ι (ZMod 2))ˣ, IsElemAbelian 3 E₀ ∧
    Nat.card E₀ = 27 ∧ IsPGroup 2 U₀ ∧ U₀ ≠ ⊥ ∧ E₀ ≤ Subgroup.normalizer (U₀ : Set _) :=
  ⟨E0, Rsub, isElemAbelian_E0, card_E0, isPGroup_of_isElemAbelian isElemAbelian_Rsub,
    Rsub_ne_bot, E0_le_normalizer⟩

end L62Model

theorem statedSL_two_eq_top (n : ℕ) :
    CFSG.Open.StatedSL n (ZMod 2) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  refine Subgroup.subset_closure ?_
  have hu : IsUnit (Matrix.det (g : Matrix (Fin n) (Fin n) (ZMod 2))) :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (Matrix.det (g : Matrix (Fin n) (Fin n) (ZMod 2)))
    with h | h
  · rw [h] at hu
    exact absurd hu (by decide)
  · exact h

@[expose] def e6 : L62Model.ι ≃ Fin 6 :=
  ((Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by norm_num))

@[expose] noncomputable def glReindex6 :
    (Matrix (Fin 6) (Fin 6) (ZMod 2))ˣ ≃* (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e6.symm).toMulEquiv

theorem bridge_l62two {S : Type} [Group S]
    (h : catalogIs S (onLie fun d' => d' = TauCeti.LieTypeIndex.A 5 gfTwoPP)) :
    Nonempty (S ≃* (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ) := by
  obtain ⟨d, hv, hd, ⟨e⟩⟩ := exists_lieIndex h
  subst hd
  have hm := CFSG.Models.lieModel_A 5 gfTwoPP hv e
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two (K := K) (by rw [hK]; norm_num [gfTwoPP])
  have hSL := CFSG.Adapters.RankTwoModelTransports.glCongr_statedSL φ 6
  exact ⟨((e'.trans (statedProjEquivZMod2 φ hSL)).trans
    (MulEquiv.subgroupCongr (statedSL_two_eq_top 6))).trans
    (Subgroup.topEquiv.trans glReindex6)⟩

section I106

variable {G : Type} [Group G] [Finite G]

theorem normalizer_map_subtype {J : Subgroup G} {W P : Subgroup ↥J}
    (h : W ≤ Subgroup.normalizer (P : Set ↥J)) :
    W.map J.subtype ≤ Subgroup.normalizer ((P.map J.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have hw' := (Subgroup.mem_normalizer_iff.1 (h hw))
  have hwinv := (Subgroup.mem_normalizer_iff.1 (h (W.inv_mem hw)))
  intro x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨w * p * w⁻¹, (hw' p).1 hp, by simp⟩
  · rintro ⟨q, hq, hqx⟩
    refine ⟨w⁻¹ * q * w, ?_, ?_⟩
    · have := (hwinv q).1 hq
      simpa using this
    · have : (w : G) * x * (w : G)⁻¹ = q := hqx.symm
      calc ((w⁻¹ * q * w : ↥J) : G) = (w : G)⁻¹ * q * w := by simp
        _ = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * w := by rw [this]
        _ = x := by group

theorem i106L62At_holds : I106L62At G := by
  intro K ⟨hcat, hZ⟩
  obtain ⟨e⟩ := bridge_l62two hcat
  obtain ⟨π, hπs, hker⟩ := exists_hom_ker_eq_of_center_bot e hZ
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top_of_surjective π hπs
  refine ⟨fun E hEK hE => ?_, ?_⟩
  ·
    haveI := hE.1
    have hinj : Function.Injective (π.comp (Subgroup.inclusion hEK)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxk : Subgroup.inclusion hEK x ∈ π.ker := hx
      rw [hker] at hxk
      have hx3 : (Subgroup.inclusion hEK x) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hE.2 x x.2
      have := eq_one_of_mem_primeCore_of_pow_three hxk hx3
      exact Subgroup.inclusion_injective hEK (by rw [this]; rfl)
    have h := Rank3.card_le_three_pow_of_injective' (ι := L62Model.ι) (E := ↥E)
      (fun a b => mul_comm' a b) (fun x => Subtype.ext (by simpa using hE.2 x x.2))
      (π.comp (Subgroup.inclusion hEK)) hinj
    have hι : Fintype.card L62Model.ι = 6 := by simp [L62Model.ι, L62Model.ι₂]
    rw [hι] at h
    simpa using h
  · obtain ⟨E₀, U₀, hE₀, hc₀, hU₀, hne, hn⟩ := L62Model.exists_pair
    obtain ⟨W, P, hW3, hWmap, hWinj, hP2, hPmap, hWP⟩ := exists_lift_normalizing π hk3
      (isPGroup_of_isElemAbelian hE₀) hU₀ (by rw [hrange]; exact le_top)
      (by rw [hrange]; exact le_top) hn
    obtain ⟨hEel, hEcard⟩ := map_subtype_isElemAbelian_card π hWmap hWinj hE₀
    refine ⟨W.map K.subtype, P.map K.subtype, Subgroup.map_subtype_le _, hEel,
      by rw [hEcard, hc₀]; norm_num, Subgroup.map_subtype_le _, hP2.map K.subtype, ?_,
      normalizer_map_subtype hWP⟩
    intro hle
    apply hne
    rw [← hPmap]
    have hPle : P ≤ GLAPPrimeCore 3 ↥K := by
      have : P.map K.subtype ≤ (GLAPPrimeCore 3 ↥K).map K.subtype := hle
      exact (Subgroup.map_le_map_iff_of_injective K.subtype_injective).1 this
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ π.ker := by rw [hker]; exact hPle hx
    exact this

end I106

@[expose] def L62Core : Prop :=
  ∀ (D I J S : Subgroup (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ), Nat.card D = 3 → I ≤ J →
    (∀ x ∈ D, ∀ i ∈ I, x * i = i * x) → (∀ x ∈ D, ∀ j ∈ J, x * j = j * x) →
    Nonempty (↥I ≃* ↥(alternatingGroup (Fin 7))) →
    Nonempty (↥J ≃* ↥(alternatingGroup (Fin 8))) → S ≠ ⊥ → IsPGroup 2 S →
    D ≤ Subgroup.normalizer (S : Set (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ) →
    I ≤ Subgroup.normalizer (S : Set (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ) →
    J ≤ Subgroup.normalizer (S : Set (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ)

section I131

variable {G : Type} [Group G] [Finite G]

theorem normalizer_of_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (H : Subgroup A)
    {y : A} (hy : e y ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup B) : Set B)) :
    y ∈ Subgroup.normalizer (H : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro z
  have := hy (e z)
  have h1 : e z ∈ H.map e.toMonoidHom ↔ z ∈ H := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := e.injective hwz
      rwa [this] at hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have h2 : e y * e z * (e y)⁻¹ ∈ H.map e.toMonoidHom ↔ y * z * y⁻¹ ∈ H := by
    have : e y * e z * (e y)⁻¹ = e (y * z * y⁻¹) := by simp
    rw [this]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = y * z * y⁻¹ := e.injective hwz
      rwa [this] at hw
    · intro hz
      exact ⟨_, hz, rfl⟩
  rw [← h1, ← h2]
  exact this

theorem i131L62At_of_core (hc : L62Core) : I131L62At G := by
  intro X K Do J I S hX hKc hK hSK hS2 hSN hDoK hDo3 hIK hDoI hI7 hDoIN hJK hIJ hJlayer hJ8
  obtain ⟨hcat, hZ⟩ := hK
  have eZ : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨e'⟩ := bridge_l62two hcat
  let e : PQuot 3 K ≃* (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ := eZ.symm.trans e'
  set π := piOf K e with hπ
  have hker := piOf_ker K e
  have himg : ∀ T : Subgroup G, (imageMod 3 K T).map e.toMonoidHom = (T.subgroupOf K).map π := by
    intro T
    unfold imageMod
    rw [Subgroup.map_map]
    rfl
  have hJle : J ≤ K ⊓ Subgroup.centralizer (Do : Set G) := by
    rw [← hJlayer]
    exact sSup_le fun L hL => hL.1
  have hDoK' : ∀ x ∈ Do.subgroupOf K, x ^ 3 = 1 := by
    intro x hx
    have h1 : (⟨(x : G), hx⟩ : ↥Do) ^ Nat.card ↥Do = 1 := pow_card_eq_one'
    rw [hDo3] at h1
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have hinj : Function.Injective (π.comp (Do.subgroupOf K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : ↥K) ∈ π.ker := hx
    rw [hker] at hxk
    exact Subtype.ext (eq_one_of_mem_primeCore_of_pow_three hxk (hDoK' x x.2))
  have hD : Nat.card ((Do.subgroupOf K).map π) = 3 := by
    rw [← card_eq_of_injective_comp_subtype π hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDoK).toEquiv, hDo3]
  have hS2' : IsPGroup 2 (S.subgroupOf K) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hSne : (S.subgroupOf K).map π ≠ ⊥ := by
    intro hbot
    apply hSN
    intro t ht
    have htK : t ∈ K := hSK ht
    have hmem : (⟨t, htK⟩ : ↥K) ∈ S.subgroupOf K := ht
    have : π ⟨t, htK⟩ ∈ (S.subgroupOf K).map π := Subgroup.mem_map_of_mem π hmem
    rw [hbot, Subgroup.mem_bot] at this
    have hk : (⟨t, htK⟩ : ↥K) ∈ π.ker := this
    rw [hker] at hk
    exact (mem_primeCoreOf_iff ⟨t, htK⟩).2 hk
  have hcomm : ∀ (A : Subgroup G), (∀ x ∈ Do, ∀ a ∈ A, x * a = a * x) → A ≤ K →
      ∀ x ∈ (Do.subgroupOf K).map π, ∀ i ∈ (A.subgroupOf K).map π, x * i = i * x := by
    intro A hA hAK x hx i hi
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hi
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA a ha b hb)
  have hIJ' : (I.subgroupOf K).map π ≤ (J.subgroupOf K).map π :=
    Subgroup.map_mono (fun x hx => hIJ hx)
  have hI7' : Nonempty (↥((I.subgroupOf K).map π) ≃* ↥(alternatingGroup (Fin 7))) := by
    obtain ⟨f⟩ := hI7
    exact ⟨(MulEquiv.subgroupCongr (himg I)).symm.trans
      ((Subgroup.equivMapOfInjective (imageMod 3 K I) e.toMonoidHom e.injective).symm.trans f)⟩
  have hJ8' : Nonempty (↥((J.subgroupOf K).map π) ≃* ↥(alternatingGroup (Fin 8))) := by
    obtain ⟨f⟩ := hJ8
    exact ⟨(MulEquiv.subgroupCongr (himg J)).symm.trans
      ((Subgroup.equivMapOfInjective (imageMod 3 K J) e.toMonoidHom e.injective).symm.trans f)⟩
  have hmain := hc ((Do.subgroupOf K).map π) ((I.subgroupOf K).map π) ((J.subgroupOf K).map π)
    ((S.subgroupOf K).map π) hD hIJ' (hcomm I hDoI hIK)
    (hcomm J (fun x hx j hj => Subgroup.mem_centralizer_iff.1 (hJle hj).2 x hx) hJK)
    hI7' hJ8' hSne (hS2'.map π)
    (map_le_normalizer_map π (le_sup_left.trans hDoIN))
    (map_le_normalizer_map π (le_sup_right.trans hDoIN))
  intro y hy
  refine normalizer_of_map_equiv e (imageMod 3 K S) ?_
  have h1 : e y ∈ (imageMod 3 K J).map e.toMonoidHom := Subgroup.mem_map_of_mem _ hy
  rw [himg J] at h1
  have := hmain h1
  rwa [← himg S] at this

end I131

end CFSG.LocalAnalysis.GLTheoremA.CatB
