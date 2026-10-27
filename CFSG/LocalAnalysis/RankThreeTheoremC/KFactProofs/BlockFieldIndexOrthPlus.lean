module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTower
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusExt
import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexAbstract
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4 (plusZ plusA plus_relations isometry_plusZ
  isometry_plusA exists_isElemAbelian_of_witness)

section BaseChange

theorem orthPlus_sum_alt {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type*} [CommRing R]
    (D : κ → κ → R) (h0 : ∀ a, D a a = 0) (h1 : ∀ a b, D a b + D b a = 0) (w : κ → R) :
    ∑ a, ∑ b, D a b * (w a * w b) = 0 := by
  have key : ∀ s : Finset κ, ∑ a ∈ s, ∑ b ∈ s, D a b * (w a * w b) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert c s hc ih =>
      rw [Finset.sum_insert hc]
      simp only [Finset.sum_insert hc, Finset.sum_add_distrib]
      have e1 : ∑ b ∈ s, D c b * (w c * w b) + ∑ a ∈ s, D a c * (w a * w c) = 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun b _ => ?_
        have := h1 c b
        linear_combination (w c * w b) * this
      rw [h0 c, zero_mul, zero_add]
      linear_combination e1 + ih
  exact key Finset.univ

variable {m : ℕ}

def orthPlusCoef {R : Type*} [CommRing R] (N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R)
    (a b : Fin m ⊕ Fin m) : R :=
  ∑ i, N (Sum.inl i) a * N (Sum.inr i) b

theorem orthPlus_quad_mulVec {R : Type*} [CommRing R]
    (N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) (w : Fin m ⊕ Fin m → R) :
    ∑ i, (N *ᵥ w) (Sum.inl i) * (N *ᵥ w) (Sum.inr i) =
      ∑ a, ∑ b, orthPlusCoef N a b * (w a * w b) := by
  calc ∑ i, (N *ᵥ w) (Sum.inl i) * (N *ᵥ w) (Sum.inr i)
      = ∑ i, ∑ a, ∑ b, (N (Sum.inl i) a * w a) * (N (Sum.inr i) b * w b) := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
    _ = ∑ a, ∑ i, ∑ b, (N (Sum.inl i) a * w a) * (N (Sum.inr i) b * w b) := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, (N (Sum.inl i) a * w a) * (N (Sum.inr i) b * w b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, orthPlusCoef N a b * (w a * w b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [orthPlusCoef, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem orthPlusCoef_map {F K : Type*} [CommRing F] [CommRing K] (f : F →+* K)
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (a b : Fin m ⊕ Fin m) :
    orthPlusCoef (M.map f) a b = f (orthPlusCoef M a b) := by
  simp [orthPlusCoef, map_sum, map_mul]

theorem orthPlus_isometry_map {F K : Type*} [Field F] [Field K] (f : F →+* K)
    {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hM : ∀ v : Fin m ⊕ Fin m → F, ∑ i, (M *ᵥ v) (Sum.inl i) * (M *ᵥ v) (Sum.inr i) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i)) (w : Fin m ⊕ Fin m → K) :
    ∑ i, ((M.map f) *ᵥ w) (Sum.inl i) * ((M.map f) *ᵥ w) (Sum.inr i) =
      ∑ i, w (Sum.inl i) * w (Sum.inr i) := by
  set E : Fin m ⊕ Fin m → Fin m ⊕ Fin m → F :=
    fun a b => orthPlusCoef M a b - orthPlusCoef (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b
    with hEdef
  have hE : ∀ v : Fin m ⊕ Fin m → F, ∑ a, ∑ b, E a b * (v a * v b) = 0 := by
    intro v
    have h1 := orthPlus_quad_mulVec M v
    have h2 := orthPlus_quad_mulVec (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) v
    rw [Matrix.one_mulVec] at h2
    have h3 := hM v
    simp only [hEdef, sub_mul, Finset.sum_sub_distrib]
    rw [← h1, ← h2, h3, sub_self]
  have hE0 : ∀ a, E a a = 0 := by
    intro a
    have := hE (Pi.single a 1)
    simpa [Pi.single_apply] using this
  have hE1 : ∀ a b, E a b + E b a = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hE0, add_zero]
    · have := hE (Pi.single a 1 + Pi.single b 1)
      simp [Pi.single_apply, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib, hab,
        Ne.symm hab] at this
      rw [hE0, hE0] at this
      rw [add_comm]
      simpa [add_assoc] using this
  have hD := orthPlus_sum_alt (fun a b => f (E a b)) (fun a => by rw [hE0, map_zero])
    (fun a b => by rw [← map_add, hE1, map_zero]) w
  have h1 := orthPlus_quad_mulVec (M.map f) w
  have h2 := orthPlus_quad_mulVec (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) w
  rw [Matrix.one_mulVec] at h2
  rw [h1, h2]
  have hone : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F).map f :=
    (Matrix.map_one f (map_zero f) (map_one f)).symm
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have : ∀ a, ∑ b, orthPlusCoef (M.map f) a b * (w a * w b) -
      ∑ b, orthPlusCoef (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b * (w a * w b) =
      ∑ b, f (E a b) * (w a * w b) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_mul, hone, orthPlusCoef_map, orthPlusCoef_map, hEdef, map_sub]
  rw [Finset.sum_congr rfl fun a _ => this a]
  exact hD

end BaseChange

section Rank

variable {K : Type} [Field K] [CharP K 2]

noncomputable def orthPlusEmb (K : Type) [Field K] [CharP K 2] {r : ℕ} (hr : 4 ≤ r) :
    GL (Fin 4 ⊕ Fin 4) (ZMod 2) →* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (plusResExt K (show (r - 4) + 4 = r by omega)).comp
    ((OrthogonalSplit.matrixEquiv 4 K).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K)))

theorem orthPlus_plusResExt_injective {r t m : ℕ} (htm : t + m = r) :
    Function.Injective (plusResExt K htm) := by
  intro h₁ h₂ h
  apply OrthogonalSplit.autMat_injective
  have e1 := autMat_plusResExt htm h₁
  have e2 := autMat_plusResExt htm h₂
  rw [h] at e1
  have h3 := congrArg (fun M => M.submatrix (plusResIdx htm) (plusResIdx htm)) (e1.symm.trans e2)
  simpa [submatrix_extendMat] using h3

theorem orthPlusEmb_injective {r : ℕ} (hr : 4 ≤ r) : Function.Injective (orthPlusEmb K hr) := by
  intro a b hab
  have h2 := (OrthogonalSplit.matrixEquiv 4 K).injective (orthPlus_plusResExt_injective _ hab)
  apply Units.ext
  have h3 := congrArg
    (fun g : GL (Fin 4 ⊕ Fin 4) K => (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)) h2
  ext i j
  exact (ZMod.castHom (dvd_refl 2) K).injective (congrFun (congrFun h3 i) j)

theorem orthPlusEmb_mem_orthogonalGroup {r : ℕ} (hr : 4 ≤ r) {a : GL (Fin 4 ⊕ Fin 4) (ZMod 2)}
    (ha : ∀ v : Fin 4 ⊕ Fin 4 → ZMod 2,
      CFSG.PGLModel.plusQuadForm 4 ((a : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
        CFSG.PGLModel.plusQuadForm 4 v) :
    orthPlusEmb K hr a ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
  refine plusResExt_mem_orthogonalGroup _ ?_
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  rw [quadPlus_apply, quadPlus_apply]
  exact orthPlus_isometry_map (ZMod.castHom (dvd_refl 2) K) ha w

theorem exists_elemAbelian_orthElementary {r : ℕ} (hr : 4 ≤ r) :
    ∃ E : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      E ≤ orthElementaryGroup (quadPlus r K) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have hinj := orthPlusEmb_injective (K := K) hr
  obtain ⟨h3, h1, h2, hZA, hZZ, hcomm⟩ := plus_relations
  have hZO : ∀ i, orthPlusEmb K hr (plusZ i) ∈ orthElementaryGroup (quadPlus r K) := by
    intro i
    rw [← OrthogonalSplit.commutator_orthogonalGroup_quadPlus (by omega : 3 ≤ r)]
    rw [← hcomm i, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (orthPlusEmb_mem_orthogonalGroup hr (isometry_plusA i))
      (orthPlusEmb_mem_orthogonalGroup hr (isometry_plusZ i))
  obtain ⟨E, hE, hcard, hEle⟩ := exists_isElemAbelian_of_witness
    (MonoidHom.id ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) (by simp)
    (fun i => orthPlusEmb K hr (plusZ i)) (fun i => orthPlusEmb K hr (plusA i))
    (fun i => by rw [← map_pow, h3 i, map_one])
    (fun i hc => h1 i (hinj (by rw [map_mul, map_mul]; exact hc.eq)))
    (fun i hc => h2 i (hinj (by rw [map_mul, map_mul, map_pow]; exact hc.eq)))
    (fun i j hij => by
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul, hZA i j hij])
    (fun i j hij => by
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul, hZZ i j hij])
  refine ⟨E, hEle.trans ?_, hE, hcard⟩
  rw [Subgroup.map_id]
  exact (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hZO i)

theorem four_le_pRank_of_mulEquiv_orthElementary {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    {r : ℕ} (hr : 4 ≤ r) (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥L) :
    4 ≤ Open.pRank 3 L := by
  obtain ⟨E, hEO, hE, hcard⟩ := exists_elemAbelian_orthElementary (K := K) hr
  have hEc := hE.1
  let f : ↥E →* Y := L.subtype.comp (ρ.toMonoidHom.comp (Subgroup.inclusion hEO))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (ρ.injective.comp (Subgroup.inclusion_injective hEO))
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext ?_) hcard f hf ?_
  · rw [Subgroup.coe_pow, hE.2 _ a.2]
    rfl
  · rintro _ ⟨x, rfl⟩
    exact (ρ (Subgroup.inclusion hEO x)).2

end Rank

section Family

variable {Y : Type} [Group Y] [Finite Y]

theorem four_le_pRank_idxD (hZ : OddCenterRest) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hD : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L)) : 4 ≤ Open.pRank 3 L := by
  obtain ⟨r, K, _, _, _, hr, ⟨ρ⟩⟩ := exists_mulEquiv_plusElementary_of_idxD hZ hL hodd hD
  exact four_le_pRank_of_mulEquiv_orthElementary hr ρ.symm

theorem orthPlus_not_statedClassicalModel_four (hZ : OddCenterRest) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hD : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L)) (h3 : Open.pRank 3 L ≤ 3) (m : ℕ) :
    ¬ StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus 4 2 m := fun _ => by
  have := four_le_pRank_idxD hZ hL hodd hD
  omega

theorem leviInnOn_orthPlus (hGA : GriessAllModelsStatement) :
    LeviInnOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD hLn hrank h3 hrk
  have h4 := four_le_pRank_idxD (oddCenterRest_of_griess hGA) hCP.comp hCP.odd hD
  have h3' := hrank 3 Nat.prime_three (by norm_num)
  omega

theorem fieldIndexOn_orthPlus (hGA : GriessAllModelsStatement) :
    FieldIndexOn (IsLieOf IdxD) := by
  refine fieldIndexOn_of_outPNice (fun Y _ _ L P hCP hD hrank => ?_) (leviInnOn_orthPlus hGA)
  exact outPNice_three_of_idxD hD (orthPlus_not_statedClassicalModel_four
    (oddCenterRest_of_griess hGA) hCP.comp hCP.odd hD (hrank 3 Nat.prime_three (by norm_num)))

end Family

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
