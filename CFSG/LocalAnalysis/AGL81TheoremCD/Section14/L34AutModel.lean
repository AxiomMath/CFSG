module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3B
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.Quasithin.EmptyFaithful.S1421QA13aL34
import CFSG.Quasithin.Vol2.Ch10SecA312AA
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup Matrix
open CFSG.ComponentClassification.PSL3Four
open CFSG.PSL3Four.Native
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

variable {K : Type} [Group K] [Finite K]

private theorem card_eq_20160_of_isPSL (hK : CFSG.Quasithin.IsPSL 3 2 2 K) :
    Nat.card K = 20160 := by
  obtain ⟨-, K₀, hF₀, hFin₀, hK₀card, ⟨e₀⟩⟩ := hK
  letI : Field K₀ := hF₀
  letI : Finite K₀ := hFin₀
  have hK₀ : Nat.card K₀ = 4 := by rw [hK₀card]; norm_num
  rw [Nat.card_congr (e₀.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K₀).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K₀))).toEquiv,
    CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.card_projectiveSL_four hK₀]

private theorem card_eq_64_of_sylow_two {K : Type} [Group K] [Finite K]
    {U Y : Subgroup K} (hcardK : Nat.card K = 20160)
    (hUfac : Nat.card U = 2 ^ (Nat.card Y).factorization 2)
    (hYdvd : Nat.card Y ∣ Nat.card K) (h64 : 64 ∣ Nat.card Y) : Nat.card U = 64 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h64fac : 6 ≤ (Nat.card Y).factorization 2 := by
    refine (Nat.prime_two.pow_dvd_iff_le_factorization (n := Nat.card Y) (k := 6)
      (Nat.card_pos (α := Y)).ne').1 ?_
    simpa using h64
  have hfacK : (Nat.card K).factorization 2 = 6 := by
    rw [hcardK]
    norm_num [Nat.factorization]
  have hfacY : (Nat.card Y).factorization 2 ≤ 6 := by
    have h := Finsupp.le_def.mp
      ((Nat.factorization_le_iff_dvd (Nat.card_pos (α := Y)).ne'
        (Nat.card_pos (α := K)).ne').2 hYdvd) 2
    rwa [hfacK] at h
  rw [hUfac]
  have hle : 2 ^ (Nat.card Y).factorization 2 ≤ 2 ^ 6 :=
    Nat.pow_le_pow_right (by norm_num) hfacY
  have hge : 2 ^ 6 ≤ 2 ^ (Nat.card Y).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) h64fac
  rw [le_antisymm hle hge]
  norm_num

private theorem exists_sylow_two_card_64 (hK : CFSG.Quasithin.IsPSL 3 2 2 K)
    {Y : Subgroup K} (h64 : 64 ∣ Nat.card Y) :
    ∃ U : Subgroup K, U ≤ Y ∧ IsPGroup 2 U ∧ Nat.card U = 64 ∧
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardK : Nat.card K = 20160 := card_eq_20160_of_isPSL hK
  obtain ⟨P⟩ := (Sylow.nonempty (p := 2) (G := ↥Y))
  let U : Subgroup K := P.map Y.subtype
  have hUY : U ≤ Y := Subgroup.map_subtype_le _
  have hU2 : IsPGroup 2 U := P.isPGroup'.map Y.subtype
  have hYdvd : Nat.card Y ∣ Nat.card K := by
    simpa using Subgroup.card_dvd_of_le (le_top : Y ≤ ⊤)
  have hUfac : Nat.card U = 2 ^ (Nat.card Y).factorization 2 := by
    rw [show Nat.card U = Nat.card ↥(P : Subgroup ↥Y) from
      Subgroup.card_map_of_injective Y.subtype_injective,
      Sylow.card_eq_multiplicity P]
  have hUcard : Nat.card U = 64 := card_eq_64_of_sylow_two hcardK hUfac hYdvd h64
  have hUtop : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, hU2, ?_⟩
    have hidx : (U.subgroupOf ⊤).index = U.index := by
      have hsurj : Function.Surjective (⊤ : Subgroup K).subtype := fun x => ⟨⟨x, trivial⟩, rfl⟩
      have h := Subgroup.index_map_eq (H := U.subgroupOf ⊤)
        (f := (⊤ : Subgroup K).subtype) hsurj (by simp)
      rw [Subgroup.map_subgroupOf_eq_of_le (le_top : U ≤ ⊤)] at h
      exact h.symm
    have hidx' : U.index = 315 := by
      have h := Subgroup.card_mul_index U
      rw [hUcard, hcardK] at h
      omega
    rw [hidx, hidx']
    norm_num
  exact ⟨U, hUY, hU2, hUcard, hUtop⟩

theorem l34_eq_top_of_dvd_card (hK : CFSG.Quasithin.IsPSL 3 2 2 K)
    {Y : Subgroup K} (h64 : 64 ∣ Nat.card Y) (h9 : 9 ∣ Nat.card Y) : Y = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardK : Nat.card K = 20160 := card_eq_20160_of_isPSL hK
  have hsimp : IsSimpleGroup K :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity K 3 2 2 hK).2
  obtain ⟨U, hUY, hU2, hUcard, hUtop⟩ := exists_sylow_two_card_64 hK h64
  obtain ⟨K', hF', hFin', hChar', φ, hK'card, -, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hK hUtop
  letI : Field K' := hF'
  letI : Finite K' := hFin'
  letI : CharP K' 2 := hChar'
  have hK' : Nat.card K' = 4 := by rw [hK'card]; norm_num
  let Pj : Fin 2 → Subgroup K := fun j => (parab34 K' j).map φ.symm.toMonoidHom
  have hres' : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt K U Pj := hres
  by_contra hY
  obtain ⟨Z, hZmax, hYZ⟩ := (eq_top_or_exists_le_coatom Y).resolve_left hY
  have hUZ : U ≤ Z := hUY.trans hYZ
  obtain ⟨j, rfl⟩ := (hres'.2.2.1 Z hUZ).1 (IsCoatom.covBy_top hZmax)
  have hZtop : Pj j ≠ ⊤ := ((hres'.2.2.1 (Pj j) (hres'.2.1 j)).2 ⟨j, rfl⟩).lt.ne
  have hdInfcard : Nat.card ↥(CFSG.QuasithinUnique.Setup.X6.dInf (Pj j)) = 960 := by
    rw [show Pj j = (parab34 K' j).map φ.symm.toMonoidHom from rfl,
      CFSG.QuasithinUnique.Setup.X6.dInf_map_equiv,
      Subgroup.card_map_of_injective φ.symm.injective,
      (CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.parab34_structure hK' j).1]
  have hdP : CFSG.QuasithinUnique.Setup.X6.dInf (Pj j) = Pj j :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.eq_of_le_of_card_eq_960 hcardK
      (CFSG.QuasithinUnique.Setup.X6.dInf_le _) hZtop hdInfcard
  have hPcard : Nat.card ↥(Pj j) = 960 := by rw [← hdP, hdInfcard]
  have h9P : 9 ∣ Nat.card ↥(Pj j) := h9.trans (Subgroup.card_dvd_of_le hYZ)
  rw [hPcard] at h9P
  norm_num at h9P

private def Half (x : Equiv.Perm (Fin 42)) : Prop :=
  ∀ i : Fin 42, (x i).val < 21 ↔ i.val < 21

private def SwapHalf (x : Equiv.Perm (Fin 42)) : Prop :=
  ∀ i : Fin 42, (x i).val < 21 ↔ ¬ i.val < 21

private theorem half_one : Half (1 : Equiv.Perm (Fin 42)) := fun _ => Iff.rfl

private theorem half_mul {x y : Equiv.Perm (Fin 42)} (hx : Half x) (hy : Half y) :
    Half (x * y) := by
  intro i
  rw [Equiv.Perm.mul_apply, hx (y i), hy i]

private theorem half_inv {x : Equiv.Perm (Fin 42)} (hx : Half x) : Half x⁻¹ := by
  intro i
  simpa using (hx (x⁻¹ i)).symm

private theorem half_mul_swap {x y : Equiv.Perm (Fin 42)} (hx : Half x) (hy : SwapHalf y) :
    SwapHalf (x * y) := by
  intro i
  rw [Equiv.Perm.mul_apply, hx (y i), hy i]

private theorem swap_mul_half {x y : Equiv.Perm (Fin 42)} (hx : SwapHalf x) (hy : Half y) :
    SwapHalf (x * y) := by
  intro i
  rw [Equiv.Perm.mul_apply, hx (y i), hy i]

private theorem swap_mul_swap {x y : Equiv.Perm (Fin 42)} (hx : SwapHalf x) (hy : SwapHalf y) :
    Half (x * y) := by
  intro i
  rw [Equiv.Perm.mul_apply, hx (y i), hy i]
  simp

private theorem swap_inv {x : Equiv.Perm (Fin 42)} (hx : SwapHalf x) : SwapHalf x⁻¹ := by
  intro i
  have h := hx (x⁻¹ i)
  have hxinv : x (x⁻¹ i) = i := by
    rw [Equiv.Perm.inv_def]
    exact Equiv.apply_symm_apply x i
  rw [hxinv] at h
  omega

private theorem half_pow {x : Equiv.Perm (Fin 42)} (hx : Half x) (n : ℕ) : Half (x ^ n) := by
  induction n with
  | zero => simpa using half_one
  | succ n ih => rw [pow_succ']; exact half_mul hx ih

private theorem rho_half (A : GL (Fin 3) F4) : Half (rho A) := by
  intro i
  rw [rho_apply]
  unfold rhoFun
  by_cases hi : i.val < 21
  · rw [if_pos hi]
    simp only
    have := vIdx_lt ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf i)
    omega
  · rw [if_neg hi]
    simp only
    have := vIdx_lt ((Matrix.transpose
      (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4))) *ᵥ vecOf i)
    omega

private theorem g5_half : Half g₅ := by
  intro i
  show (g5Fun i).val < 21 ↔ i.val < 21
  unfold g5Fun
  simp only
  have := vIdx_lt (fun k => vecOf i k ^ 2)
  have hdiv : i.val / 21 = 0 ∨ i.val / 21 = 1 := by omega
  rcases hdiv with h | h <;> omega

private theorem g6_swap : SwapHalf g₆ := by
  intro i
  show (g6Fun i).val < 21 ↔ ¬ i.val < 21
  unfold g6Fun
  by_cases hi : i.val < 21
  · rw [dif_pos hi]
    simp only
    omega
  · rw [dif_neg hi]
    simp only
    omega

private theorem not_half_and_swap {x : Equiv.Perm (Fin 42)} (hx : Half x) (hx' : SwapHalf x) :
    False := by
  have h1 := hx 0
  have h2 := hx' 0
  simp at h1 h2
  omega

theorem mem_R_halves {x : Equiv.Perm (Fin 42)} (hx : x ∈ R) :
    (∀ i : Fin 42, ((x i).val < 21 ↔ i.val < 21)) ∨
      (∀ i : Fin 42, ((x i).val < 21 ↔ ¬ i.val < 21)) := by
  change Half x ∨ SwapHalf x
  have hgen : ∀ y ∈ ({g₁, g₂, g₃, g₄, g₅, g₆} : Set (Equiv.Perm (Fin 42))),
      Half y ∨ SwapHalf y := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (rho_half aGL)
    · exact Or.inl (rho_half bGL)
    · exact Or.inl (rho_half cGL)
    · exact Or.inl (rho_half dGL)
    · exact Or.inl g5_half
    · exact Or.inr g6_swap
  refine Subgroup.closure_induction hgen (Or.inl half_one) ?_ ?_ hx
  · rintro a b _ _ (ha | ha) (hb | hb)
    · exact Or.inl (half_mul ha hb)
    · exact Or.inr (half_mul_swap ha hb)
    · exact Or.inr (swap_mul_half ha hb)
    · exact Or.inl (swap_mul_swap ha hb)
  · rintro a _ (ha | ha)
    · exact Or.inl (half_inv ha)
    · exact Or.inr (swap_inv ha)

private theorem conj_swap {c x : Equiv.Perm (Fin 42)} (hc : c ∈ R) (hx : SwapHalf x) :
    SwapHalf (c * x * c⁻¹) := by
  intro i
  rcases mem_R_halves hc with hcH | hcS
  · have hci : (c⁻¹ i).val < 21 ↔ i.val < 21 := by
      have h2 : c (c⁻¹ i) = i := by
        rw [Equiv.Perm.inv_def]
        exact Equiv.apply_symm_apply c i
      simpa [h2] using (hcH (c⁻¹ i)).symm
    have hcx : (c (x (c⁻¹ i))).val < 21 ↔ (x (c⁻¹ i)).val < 21 := hcH (x (c⁻¹ i))
    have hx' := hx (c⁻¹ i)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    omega
  · have hci : (c⁻¹ i).val < 21 ↔ ¬ i.val < 21 := by
      have h2 : c (c⁻¹ i) = i := by
        rw [Equiv.Perm.inv_def]
        exact Equiv.apply_symm_apply c i
      have := hcS (c⁻¹ i)
      rw [h2] at this
      omega
    have hcx : (c (x (c⁻¹ i))).val < 21 ↔ ¬ (x (c⁻¹ i)).val < 21 := hcS (x (c⁻¹ i))
    have hx' := hx (c⁻¹ i)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    omega

theorem r₄_swaps (i : Fin 42) : ((r₄ i).val < 21 ↔ ¬ i.val < 21) := by
  have h := half_mul_swap g5_half g6_swap
  exact h i

private def tabW : CFSG.PSL3Four.Native.Tab :=
  CFSG.PSL3Four.Native.comp 42 (CFSG.PSL3Four.Native.comp 42 g₂T g₁T) g₂T

private def tabWInv : CFSG.PSL3Four.Native.Tab :=
  #[9, 6, 2, 19, 16, 0, 10, 12, 11, 5, 1, 17, 13, 7, 14, 3, 20, 8, 18, 15, 4, 22, 30, 26, 38, 34,
    31, 27, 39, 35, 21, 23, 25, 24, 32, 40, 36, 28, 33, 37, 29, 41]

private def tabX : CFSG.PSL3Four.Native.Tab :=
  CFSG.PSL3Four.Native.comp 42 r₄T
    (CFSG.PSL3Four.Native.conjTab 42 tabW tabWInv r₄T)

private def tabX2 : CFSG.PSL3Four.Native.Tab :=
  #[6, 5, 0, 8, 7, 2, 9, 19, 16, 10, 1, 14, 18, 20, 13, 4, 11, 15, 17, 12, 3, 23, 31, 26, 41, 36,
    22, 21, 25, 24, 27, 30, 37, 40, 35, 32, 38, 29, 39, 33, 28, 34]

private def tabX4 : CFSG.PSL3Four.Native.Tab :=
  #[9, 2, 6, 16, 19, 0, 10, 12, 11, 1, 5, 13, 17, 3, 20, 7, 14, 4, 15, 18, 8, 26, 30, 22, 34, 38,
    31, 23, 36, 41, 21, 27, 29, 28, 32, 37, 39, 24, 33, 40, 25, 35]

private def tabX8 : CFSG.PSL3Four.Native.Tab :=
  #[1, 6, 10, 14, 18, 9, 5, 17, 13, 2, 0, 3, 4, 16, 8, 12, 20, 19, 7, 15, 11, 31, 21, 30, 32, 33,
    27, 22, 39, 35, 26, 23, 41, 36, 29, 24, 40, 34, 28, 25, 38, 37]

private def tabX12 : CFSG.PSL3Four.Native.Tab :=
  #[2, 10, 5, 20, 15, 1, 0, 4, 3, 6, 9, 16, 19, 14, 11, 17, 8, 18, 12, 7, 13, 27, 26, 21, 29, 28,
    23, 30, 40, 37, 31, 22, 35, 39, 41, 34, 25, 32, 36, 38, 33, 24]

private def tabPow (n : ℕ) (t : CFSG.PSL3Four.Native.Tab) : ℕ → CFSG.PSL3Four.Native.Tab
  | 0 => CFSG.PSL3Four.Native.idTab n
  | k + 1 => CFSG.PSL3Four.Native.comp n t (tabPow n t k)

private theorem tabWInv_size : tabWInv.size = 42 := by decide

private theorem tabWInv_comp : CFSG.PSL3Four.Native.comp 42 tabWInv tabW =
    CFSG.PSL3Four.Native.idTab 42 := by decide

private theorem tabX4_eq : CFSG.PSL3Four.Native.comp 42 tabX2 tabX2 = tabX4 := by decide

private theorem tabX8_eq : CFSG.PSL3Four.Native.comp 42 tabX4 tabX4 = tabX8 := by decide

private theorem tabX12_eq : CFSG.PSL3Four.Native.comp 42 tabX8 tabX4 = tabX12 := by decide

private theorem tabX12_ne : tabX12 ≠ CFSG.PSL3Four.Native.idTab 42 := by decide

private theorem tabRep_pow {n : ℕ} {t : CFSG.PSL3Four.Native.Tab}
    {g : Equiv.Perm (Fin n)} (h : TabRep t g) (k : ℕ) : TabRep (tabPow n t k) (g ^ k) := by
  induction k with
  | zero => simpa [tabPow] using (TabRep.idTab (n := n))
  | succ k ih =>
    rw [tabPow, pow_succ']
    exact h.comp ih

private theorem tabX2_pow_eq : tabPow 42 tabX 2 = tabX2 := by decide

theorem exists_unitary_product_order_seven : ∃ g ∈ S,
    (r₄ * (g * r₄ * g⁻¹)) ^ 12 ≠ 1 := by
  classical
  have ht : TabRep tabW (g₂ * g₁ * g₂) := (tabRep_g₂.comp tabRep_g₁).comp tabRep_g₂
  have htinv : TabRep tabWInv (g₂ * g₁ * g₂)⁻¹ :=
    ht.inv tabWInv_size tabWInv_comp
  have hconj : TabRep
      (CFSG.PSL3Four.Native.conjTab 42 tabW tabWInv r₄T)
      ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹) :=
    ht.conjTab tabRep_r₄ htinv
  have hx : TabRep tabX (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) :=
    tabRep_r₄.comp hconj
  have hx2 : TabRep tabX2 ((r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 2) := by
    have h := tabRep_pow hx 2
    rwa [tabX2_pow_eq] at h
  have hx4 : TabRep tabX4 ((r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 4) := by
    have h := hx2.comp hx2
    rw [tabX4_eq] at h
    have hp : (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 4 =
        (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 2 *
          (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    rw [hp]
    exact h
  have hx8 : TabRep tabX8 ((r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 8) := by
    have h := hx4.comp hx4
    rw [tabX8_eq] at h
    have hp : (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 8 =
        (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 4 *
          (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 4 := by
      rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add]
    rw [hp]
    exact h
  have hx12 : TabRep tabX12 ((r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 12) := by
    have h := hx8.comp hx4
    rw [tabX12_eq] at h
    have hp : (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 12 =
        (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 8 *
          (r₄ * ((g₂ * g₁ * g₂) * r₄ * (g₂ * g₁ * g₂)⁻¹)) ^ 4 := by
      rw [show (12 : ℕ) = 8 + 4 by norm_num, pow_add]
    rw [hp]
    exact h
  have hne : tabX12 ≠ CFSG.PSL3Four.Native.idTab 42 := tabX12_ne
  refine ⟨g₂ * g₁ * g₂, ?_, ?_⟩
  · exact S.mul_mem (S.mul_mem g₂_mem_S g₁_mem_S) g₂_mem_S
  · intro h12
    exact hne ((hx12.eq_iff TabRep.idTab).2 h12)

private theorem l34_aut_exists_commuting_involution
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} (hB'R : B' ≤ R)
    (hB'2 : IsPGroup 2 ↥B') (hS₃'S : S₃' ≤ S)
    (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    (hgen : B' ⊓ S = ⨆ (member : ↥S₃') (_ : member ≠ 1),
      (B' ⊓ S) ⊓ Subgroup.centralizer ({(member : Equiv.Perm (Fin 42))} : Set _))
    (hDne : B' ⊓ S ≠ ⊥) :
    ∃ (e : ↥S₃') (d : Equiv.Perm (Fin 42)), e ≠ 1 ∧ d ≠ 1 ∧ d ∈ B' ∧ d ∈ S ∧
      d * d = 1 ∧ d * (e : Equiv.Perm (Fin 42)) = (e : Equiv.Perm (Fin 42)) * d := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup (Equiv.Perm (Fin 42)) := B' ⊓ S
  have hD2 : IsPGroup 2 ↥D := hB'2.to_le inf_le_left
  have hgen' : D = ⨆ (member : ↥S₃') (_ : member ≠ 1),
      D ⊓ Subgroup.centralizer ({(member : Equiv.Perm (Fin 42))} : Set _) := hgen
  change D ≠ ⊥ at hDne
  rw [hgen'] at hDne
  obtain ⟨e, hene, hEne⟩ : ∃ e : ↥S₃', e ≠ 1 ∧
      (D ⊓ Subgroup.centralizer ({(e : Equiv.Perm (Fin 42))} : Set _)) ≠ ⊥ := by
    by_contra h
    apply hDne
    rw [iSup_eq_bot]
    intro e
    rw [iSup_eq_bot]
    intro he
    by_contra hne
    exact h ⟨e, he, hne⟩
  let E : Subgroup (Equiv.Perm (Fin 42)) :=
    D ⊓ Subgroup.centralizer ({(e : Equiv.Perm (Fin 42))} : Set _)
  have hE2 : IsPGroup 2 ↥E := hD2.to_le inf_le_left
  obtain ⟨x₀, hx₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
  obtain ⟨n, hn1, hn2⟩ :=
    CFSG.Quasithin.Vol2.Ch10.A312A.exists_pow_involution hE2 (γ := x₀) (by simpa using hx₀)
  let d : Equiv.Perm (Fin 42) := (x₀ : Equiv.Perm (Fin 42)) ^ n
  have hdE : d ∈ E := E.pow_mem x₀.2 n
  have hd1 : d ≠ 1 := by
    intro h
    apply hn1
    apply Subtype.ext
    simpa [d, Subgroup.coe_pow] using h
  have hd2 : d * d = 1 := by
    have := congrArg (fun u : ↥E => (u : Equiv.Perm (Fin 42))) hn2
    simpa [d, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] using this
  refine ⟨e, d, hene, hd1, (hdE.1).1, (hdE.1).2, hd2, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp hdE.2

private theorem l34_aut_commuting_involution_false
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} (hB'R : B' ≤ R)
    (hS₃'S : S₃' ≤ S) (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    {e : ↥S₃'} (hene : e ≠ 1) {d : Equiv.Perm (Fin 42)}
    (hd1 : d ≠ 1) (hdB : d ∈ B') (hdS : d ∈ S) (hd2 : d * d = 1)
    (hdcomm : d * (e : Equiv.Perm (Fin 42)) = (e : Equiv.Perm (Fin 42)) * d) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdord : orderOf d = 2 := orderOf_eq_prime hd2 hd1
  let y : ↥R := ⟨d, hB'R hdB⟩
  have hyord : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe y]
    exact hdord
  have he3 : orderOf (e : Equiv.Perm (Fin 42)) = 3 := by
    apply orderOf_eq_prime (hS₃'e.2 (e : Equiv.Perm (Fin 42)) e.2)
    intro h1
    exact hene (Subtype.ext h1)
  let F : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.zpowers (e : Equiv.Perm (Fin 42))
  have hF : F ≤ S ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 42))) := by
    refine le_inf ?_ ?_
    · show Subgroup.zpowers (e : Equiv.Perm (Fin 42)) ≤ S
      rw [Subgroup.zpowers_le]
      exact hS₃'S e.2
    · show Subgroup.zpowers (e : Equiv.Perm (Fin 42)) ≤
          Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 42)))
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hdcomm.symm
  have hFcard : Nat.card ↥F = 3 := by
    show Nat.card ↥(Subgroup.zpowers (e : Equiv.Perm (Fin 42))) = 3
    rw [Nat.card_zpowers, he3]
  have h3dvd : ∀ {r : ↥R}, IsConj y r → 3 ∣
      Nat.card ↥(Subgroup.centralizer ({(r : Equiv.Perm (Fin 42))} : Set _) ⊓ S) := by
    intro r hr
    obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj hr
    obtain ⟨F', hF'le, hF'card, -, -⟩ :=
      CFSG.Quasithin.QA13a.conj_transport (n := d) (r := (r : Equiv.Perm (Fin 42))) hcR hc hF
    have hdvd := Subgroup.card_dvd_of_le hF'le
    rwa [hF'card, hFcard] at hdvd
  rcases (orderOf_eq_two_iff y).mp hyord with h1 | h2 | h3 | h4
  · have h3 := h3dvd h1
    have hC : Subgroup.centralizer ({(r₁R : Equiv.Perm (Fin 42))} : Set _) ⊓ S = C₁ := rfl
    rw [hC, card_C₁] at h3
    norm_num at h3
  · exact absurd hdS (not_mem_S_of_isConj h2 not_mem_S_r₂)
  · exact absurd hdS (not_mem_S_of_isConj h3 not_mem_S_r₃)
  · exact absurd hdS (not_mem_S_of_isConj h4 not_mem_S_r₄)

private theorem l34_aut_inf_S_eq_bot
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} (hB'R : B' ≤ R)
    (hB'2 : IsPGroup 2 ↥B') (hS₃'S : S₃' ≤ S) (hS₃'card : Nat.card ↥S₃' = 9)
    (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    (hnorm : ∀ s ∈ S₃', ∀ b ∈ B', s * b * s⁻¹ ∈ B') : B' ⊓ S = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup (Equiv.Perm (Fin 42)) := B' ⊓ S
  have hD2 : IsPGroup 2 ↥D := hB'2.to_le inf_le_left
  have hS₃'normB : S₃' ≤ Subgroup.normalizer (B' : Set (Equiv.Perm (Fin 42))) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact fun hb => hnorm s hs b hb
    · intro hb
      have h := hnorm s⁻¹ (S₃'.inv_mem hs) (s * b * s⁻¹) hb
      have e : s⁻¹ * (s * b * s⁻¹) * (s⁻¹)⁻¹ = b := by group
      rwa [e] at h
  have hDnorm : S₃' ≤ Subgroup.normalizer (D : Set (Equiv.Perm (Fin 42))) :=
    Subgroup.le_normalizer_inf hS₃'normB (hS₃'S.trans Subgroup.le_normalizer)
  have hD3 : ¬ 3 ∣ Nat.card ↥D := by
    obtain ⟨k, hk⟩ := hD2.exists_card_eq
    intro h3
    rw [hk] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
    omega
  have hpower : ∀ member : ↥S₃', member ^ 3 = 1 := fun e => by
    apply Subtype.ext
    simpa using hS₃'e.2 (e : Equiv.Perm (Fin 42)) e.2
  have hcard3 : Nat.card ↥S₃' = 3 ^ 2 := by rw [hS₃'card]; norm_num
  have hgen : B' ⊓ S = ⨆ (member : ↥S₃') (_ : member ≠ 1),
      (B' ⊓ S) ⊓ Subgroup.centralizer ({(member : Equiv.Perm (Fin 42))} : Set _) := by
    have h :=
      CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
        3 Nat.prime_three S₃' D hpower hcard3 hD3 hDnorm
    simpa [D] using h
  by_contra hDne
  obtain ⟨e, d, hene, hd1, hdB, hdS, hd2, hdcomm⟩ :=
    l34_aut_exists_commuting_involution hB'R hB'2 hS₃'S hS₃'e hgen hDne
  exact l34_aut_commuting_involution_false hB'R hS₃'S hS₃'e hene hd1 hdB hdS hd2 hdcomm

private theorem l34_aut_involution_conj_r4
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} (hB'R : B' ≤ R)
    (hB'2 : IsPGroup 2 ↥B') (hS₃'S : S₃' ≤ S) (hS₃'card : Nat.card ↥S₃' = 9)
    (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    (hnorm : ∀ s ∈ S₃', ∀ b ∈ B', s * b * s⁻¹ ∈ B')
    {y : Equiv.Perm (Fin 42)} (hyB : y ∈ B') (hy1 : y ≠ 1) (hy2 : y * y = 1) :
    IsConj (⟨y, hB'R hyB⟩ : ↥R) r₄R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDbot := l34_aut_inf_S_eq_bot hB'R hB'2 hS₃'S hS₃'card hS₃'e hnorm
  have hcomm : ∀ s ∈ S₃', ∀ b ∈ B', s * b = b * s := by
    intro s hs b hb
    have h1 : s * b * s⁻¹ * b⁻¹ ∈ B' :=
      B'.mul_mem (hnorm s hs b hb) (B'.inv_mem hb)
    have h2 : s * b * s⁻¹ * b⁻¹ ∈ S := by
      have h3 : b * s⁻¹ * b⁻¹ ∈ S := conj_mem_S (hB'R hb) (S.inv_mem (hS₃'S hs))
      have e : s * b * s⁻¹ * b⁻¹ = s * (b * s⁻¹ * b⁻¹) := by group
      rw [e]
      exact S.mul_mem (hS₃'S hs) h3
    have h3 : s * b * s⁻¹ * b⁻¹ ∈ B' ⊓ S := ⟨h1, h2⟩
    rw [hDbot] at h3
    have h4 : s * b * s⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp h3
    calc s * b = (s * b * s⁻¹ * b⁻¹) * (b * s) := by group
      _ = b * s := by rw [h4, one_mul]
  let yR : ↥R := ⟨y, hB'R hyB⟩
  have hyR2 : orderOf yR = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      rw [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
      exact hy2
    · intro h
      exact hy1 (congrArg Subtype.val h)
  have hS₃'C : S₃' ≤ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 42))) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm s hs y hyB
  have h9dvd : ∀ {r : ↥R}, IsConj yR r → 9 ∣
      Nat.card ↥(Subgroup.centralizer ({(r : Equiv.Perm (Fin 42))} : Set _) ⊓ S) := by
    intro r hr
    obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj hr
    have hF : S₃' ≤ S ⊓ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 42))) :=
      le_inf hS₃'S hS₃'C
    obtain ⟨F', hF'le, hF'card, -, -⟩ :=
      CFSG.Quasithin.QA13a.conj_transport (n := y) (r := (r : Equiv.Perm (Fin 42))) hcR hc hF
    have hdvd := Subgroup.card_dvd_of_le hF'le
    rwa [hF'card, hS₃'card] at hdvd
  rcases (orderOf_eq_two_iff yR).mp hyR2 with h1 | h2 | h3 | h4
  · have h9 := h9dvd h1
    have hC : Subgroup.centralizer ({(r₁R : Equiv.Perm (Fin 42))} : Set _) ⊓ S = C₁ := rfl
    rw [hC, card_C₁] at h9
    norm_num at h9
  · have h9 := h9dvd h2
    have hC : Subgroup.centralizer ({(r₂R : Equiv.Perm (Fin 42))} : Set _) ⊓ S = C₂ := rfl
    rw [hC, card_C₂] at h9
    norm_num at h9
  · have h9 := h9dvd h3
    have hC : Subgroup.centralizer ({(r₃R : Equiv.Perm (Fin 42))} : Set _) ⊓ S = C₃ := rfl
    rw [hC, card_C₃] at h9
    norm_num at h9
  · exact h4

private theorem l34_aut_involution_swaps
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} (hB'R : B' ≤ R)
    (hB'2 : IsPGroup 2 ↥B') (hS₃'S : S₃' ≤ S) (hS₃'card : Nat.card ↥S₃' = 9)
    (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    (hnorm : ∀ s ∈ S₃', ∀ b ∈ B', s * b * s⁻¹ ∈ B')
    {y : Equiv.Perm (Fin 42)} (hyB : y ∈ B') (hy1 : y ≠ 1) (hy2 : y * y = 1) :
    SwapHalf y := by
  have hconj := l34_aut_involution_conj_r4 hB'R hB'2 hS₃'S hS₃'card hS₃'e hnorm hyB hy1 hy2
  obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj hconj
  have hc' : y = c * r₄ * c⁻¹ := hc
  rw [hc']
  exact conj_swap hcR (show SwapHalf r₄ from r₄_swaps)

private theorem l34_aut_no_half {B' : Subgroup (Equiv.Perm (Fin 42))}
    (hB'2 : IsPGroup 2 ↥B')
    (hInv : ∀ y ∈ B', y ≠ 1 → y * y = 1 → SwapHalf y) :
    ∀ x ∈ B', x ≠ 1 → ¬ Half x := by
  intro x hxB hx1 hxH
  obtain ⟨n, hn1, hn2⟩ := CFSG.Quasithin.Vol2.Ch10.A312A.exists_pow_involution hB'2
    (γ := ⟨x, hxB⟩) (by simpa using hx1)
  let z : Equiv.Perm (Fin 42) := x ^ n
  have hzB : z ∈ B' := B'.pow_mem hxB n
  have hz1 : z ≠ 1 := by
    intro hz
    exact hn1 (Subtype.ext hz)
  have hz2 : z * z = 1 := by
    have := congrArg (fun u : ↥B' => (u : Equiv.Perm (Fin 42))) hn2
    simpa [z, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] using this
  have hzH : Half z := half_pow hxH n
  exact not_half_and_swap hzH (hInv z hzB hz1 hz2)

private theorem l34_aut_card_le_two_of_no_half {B' : Subgroup (Equiv.Perm (Fin 42))}
    (hB'R : B' ≤ R) (hnoHalf : ∀ x ∈ B', x ≠ 1 → ¬ Half x) : Nat.card ↥B' ≤ 2 := by
  classical
  by_contra hcard
  have h3 : 3 ≤ Nat.card ↥B' := by omega
  have hlt : 1 < (Finset.univ.erase (1 : ↥B')).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_erase] at ha hb
  have ha1 : a ≠ 1 := ha.1
  have hb1 : b ≠ 1 := hb.1
  have hxa : (a : Equiv.Perm (Fin 42)) ∈ B' := a.2
  have hxb : (b : Equiv.Perm (Fin 42)) ∈ B' := b.2
  have hswap : ∀ x : ↥B', x ≠ 1 → SwapHalf (x : Equiv.Perm (Fin 42)) := by
    intro x hx1
    rcases mem_R_halves (hB'R x.2) with h | h
    · exact absurd h (hnoHalf (x : Equiv.Perm (Fin 42)) x.2 (by
        intro hx; exact hx1 (Subtype.ext hx)))
    · exact h
  have ha2 : (a : Equiv.Perm (Fin 42)) * (a : Equiv.Perm (Fin 42)) = 1 := by
    have hh := swap_mul_swap (hswap a ha1) (hswap a ha1)
    by_contra hne
    exact hnoHalf ((a : Equiv.Perm (Fin 42)) * (a : Equiv.Perm (Fin 42)))
      (B'.mul_mem hxa hxa) hne hh
  have hb2 : (b : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42)) = 1 := by
    have hh := swap_mul_swap (hswap b hb1) (hswap b hb1)
    by_contra hne
    exact hnoHalf ((b : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42)))
      (B'.mul_mem hxb hxb) hne hh
  have hprod : Half ((a : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42))) :=
    swap_mul_swap (hswap a ha1) (hswap b hb1)
  by_cases hEq : (a : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42)) = 1
  · have hab' : (a : Equiv.Perm (Fin 42)) = (b : Equiv.Perm (Fin 42)) := by
      calc (a : Equiv.Perm (Fin 42)) =
          (a : Equiv.Perm (Fin 42)) *
            ((b : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42))) := by
            rw [hb2, mul_one]
        _ = ((a : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42))) *
            (b : Equiv.Perm (Fin 42)) := by
            group
        _ = (b : Equiv.Perm (Fin 42)) := by rw [hEq, one_mul]
    exact hab (Subtype.ext hab')
  · exact hnoHalf ((a : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42)))
      (B'.mul_mem hxa hxb) hEq hprod

private theorem l34_aut_card_le_two
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} (hB'R : B' ≤ R)
    (hB'2 : IsPGroup 2 ↥B') (hS₃'S : S₃' ≤ S) (hS₃'card : Nat.card ↥S₃' = 9)
    (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    (hnorm : ∀ s ∈ S₃', ∀ b ∈ B', s * b * s⁻¹ ∈ B') : Nat.card ↥B' ≤ 2 :=
  l34_aut_card_le_two_of_no_half hB'R (l34_aut_no_half hB'2 fun y hyB hy1 hy2 =>
    l34_aut_involution_swaps hB'R hB'2 hS₃'S hS₃'card hS₃'e hnorm hyB hy1 hy2)

private theorem l34_aut_mem_conj_r4
    {K : Type} [Group K] [Finite K] {B : Subgroup (MulAut K)}
    {B' S₃' : Subgroup (Equiv.Perm (Fin 42))} {Θ : MulAut K ≃* ↥R}
    (hB'R : B' ≤ R) (hB'2 : IsPGroup 2 ↥B')
    (hS₃'S : S₃' ≤ S) (hS₃'card : Nat.card ↥S₃' = 9)
    (hS₃'e : CFSG.Open.IsElemAbelian 3 S₃')
    (hnorm' : ∀ s ∈ S₃', ∀ b ∈ B', s * b * s⁻¹ ∈ B')
    (hBmap : B' = B.map (R.subtype.comp Θ.toMonoidHom))
    (hBcard : Nat.card B ≤ 2) {b : MulAut K} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ∃ c ∈ R, ((Θ b : ↥R) : Equiv.Perm (Fin 42)) = c * r₄ * c⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθb' : ((Θ b : ↥R) : Equiv.Perm (Fin 42)) ∈ B' := by
    rw [hBmap]
    exact Subgroup.mem_map_of_mem (R.subtype.comp Θ.toMonoidHom) hb
  have hbord : orderOf b = 2 := by
    have hdvd : orderOf b ∣ Nat.card ↥B := Subgroup.orderOf_dvd_natCard B hb
    have hne : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
    have hpos : 0 < orderOf b := orderOf_pos b
    have hle : orderOf b ≤ 2 := by
      have h1 := Nat.le_of_dvd (Nat.card_pos (α := B)) hdvd
      omega
    omega
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rw [hbord] at h
    simpa [pow_two] using h
  have hb'1 : ((Θ b : ↥R) : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h
    apply hb1
    apply Θ.injective
    apply Subtype.ext
    simpa using h
  have hb'2 : ((Θ b : ↥R) : Equiv.Perm (Fin 42)) *
      ((Θ b : ↥R) : Equiv.Perm (Fin 42)) = 1 := by
    have h : (Θ b : ↥R) * (Θ b : ↥R) = 1 := by
      rw [← map_mul, hb2, map_one]
    exact congrArg (fun u : ↥R => (u : Equiv.Perm (Fin 42))) h
  have hconj : IsConj (Θ b) r₄R :=
    l34_aut_involution_conj_r4 hB'R hB'2 hS₃'S hS₃'card hS₃'e hnorm' hθb' hb'1 hb'2
  exact eq_conj_of_isConj hconj

private theorem l34_aut_order_seven_witness
    {K : Type} [Group K] [Finite K] {b : MulAut K}
    {ψ : K ≃* ↥S} {Θ : MulAut K ≃* ↥R}
    (hΘconj : ∀ k : K, (Θ (MulAut.conj k) : Equiv.Perm (Fin 42)) =
      (ψ k : Equiv.Perm (Fin 42)))
    {c : Equiv.Perm (Fin 42)} (hcR : c ∈ R)
    (hθb : ((Θ b : ↥R) : Equiv.Perm (Fin 42)) = c * r₄ * c⁻¹) :
    ∃ g : K, (b * MulAut.conj g * b * (MulAut.conj g)⁻¹) ^ 12 ≠ 1 := by
  obtain ⟨g₀, hg₀S, hg₀⟩ := exists_unitary_product_order_seven
  have hg₁S : c * g₀ * c⁻¹ ∈ S := conj_mem_S hcR hg₀S
  let gK : K := ψ.symm ⟨c * g₀ * c⁻¹, hg₁S⟩
  refine ⟨gK, ?_⟩
  intro h12
  have hmap : (Θ b * Θ (MulAut.conj gK) * Θ b * (Θ (MulAut.conj gK))⁻¹) ^ 12 = 1 := by
    have h := congrArg Θ h12
    simpa only [map_pow, map_mul, map_inv, map_one] using h
  have hΘg : Θ (MulAut.conj gK) = ⟨c * g₀ * c⁻¹, S_le_R hg₁S⟩ := by
    apply Subtype.ext
    have hψg : ψ gK = ⟨c * g₀ * c⁻¹, hg₁S⟩ := by simp [gK]
    simpa [hψg] using hΘconj gK
  rw [hΘg] at hmap
  have hmapP : ((((Θ b : ↥R) : Equiv.Perm (Fin 42)) * (c * g₀ * c⁻¹) *
      ((Θ b : ↥R) : Equiv.Perm (Fin 42)) * (c * g₀ * c⁻¹)⁻¹) ^ 12) = 1 := by
    have := congrArg (fun u : ↥R => (u : Equiv.Perm (Fin 42))) hmap
    simpa using this
  rw [hθb] at hmapP
  have hconjEq : (c * r₄ * c⁻¹) * (c * g₀ * c⁻¹) * (c * r₄ * c⁻¹) * (c * g₀ * c⁻¹)⁻¹ =
      c * (r₄ * (g₀ * r₄ * g₀⁻¹)) * c⁻¹ := by group
  rw [hconjEq] at hmapP
  have hpowConj : (c * (r₄ * (g₀ * r₄ * g₀⁻¹)) * c⁻¹) ^ 12 =
      c * (r₄ * (g₀ * r₄ * g₀⁻¹)) ^ 12 * c⁻¹ := by
    have h := map_pow (MulAut.conj c) (r₄ * (g₀ * r₄ * g₀⁻¹)) 12
    rw [MulAut.conj_apply] at h
    rw [MulAut.conj_apply] at h
    exact h.symm
  have hfinal : (r₄ * (g₀ * r₄ * g₀⁻¹)) ^ 12 = 1 := by
    have h1 : c * (r₄ * (g₀ * r₄ * g₀⁻¹)) ^ 12 * c⁻¹ = 1 := by
      rwa [hpowConj] at hmapP
    have h2 := congrArg (fun y => c⁻¹ * y * c) h1
    have e : c⁻¹ * (c * (r₄ * (g₀ * r₄ * g₀⁻¹)) ^ 12 * c⁻¹) * c =
        (r₄ * (g₀ * r₄ * g₀⁻¹)) ^ 12 := by group
    rw [e] at h2
    simpa using h2
  exact hg₀ hfinal

theorem l34_aut_two_subgroup {K : Type} [Group K] [Finite K]
    (hK : CFSG.Quasithin.IsPSL 3 2 2 K) {B : Subgroup (MulAut K)} (hB : IsPGroup 2 B)
    {S₃ : Subgroup K} (hS₃ : Nat.card S₃ = 9) (hS₃e : CFSG.Open.IsElemAbelian 3 S₃)
    (hnorm : ∀ s ∈ S₃, ∀ b ∈ B, MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈ B) :
    Nat.card B ≤ 2 ∧ ∀ b ∈ B, b ≠ 1 →
      ∃ g : K, (b * MulAut.conj g * b * (MulAut.conj g)⁻¹) ^ 12 ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, Θ, -, hΘconj⟩ := CFSG.Quasithin.QA13a.exists_autIso hK
  let θ : MulAut K →* Equiv.Perm (Fin 42) := R.subtype.comp Θ.toMonoidHom
  let ψ' : K →* Equiv.Perm (Fin 42) := S.subtype.comp ψ.toMonoidHom
  let B' : Subgroup (Equiv.Perm (Fin 42)) := B.map θ
  let S₃' : Subgroup (Equiv.Perm (Fin 42)) := S₃.map ψ'
  have hθinj : Function.Injective θ := by
    intro a b h
    exact Θ.injective (Subtype.ext h)
  have hψ'inj : Function.Injective ψ' := by
    intro a b h
    exact ψ.injective (Subtype.ext h)
  have hB'R : B' ≤ R := by
    rintro _ ⟨b, -, rfl⟩
    exact (Θ b).2
  have hB'2 : IsPGroup 2 ↥B' := hB.map θ
  have hBmap : B' = B.map (R.subtype.comp Θ.toMonoidHom) := rfl
  have hS₃'S : S₃' ≤ S := by
    rintro _ ⟨s, -, rfl⟩
    exact (ψ s).2
  have hS₃'card : Nat.card ↥S₃' = 9 := by
    rw [Subgroup.card_map_of_injective hψ'inj, hS₃]
  have hS₃'e : CFSG.Open.IsElemAbelian 3 S₃' := IsElemAbelian.map hS₃e ψ'
  have hnorm' : ∀ s ∈ S₃', ∀ b ∈ B', s * b * s⁻¹ ∈ B' := by
    rintro _ ⟨s₀, hs₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
    refine ⟨MulAut.conj s₀ * b₀ * (MulAut.conj s₀)⁻¹, hnorm s₀ hs₀ b₀ hb₀, ?_⟩
    change ((Θ (MulAut.conj s₀ * b₀ * (MulAut.conj s₀)⁻¹) : ↥R) :
        Equiv.Perm (Fin 42)) =
      ((ψ s₀ : ↥S) : Equiv.Perm (Fin 42)) * ((Θ b₀ : ↥R) : Equiv.Perm (Fin 42)) *
        (((ψ s₀ : ↥S) : Equiv.Perm (Fin 42)))⁻¹
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hΘconj s₀]
  have hB'le : Nat.card ↥B' ≤ 2 :=
    l34_aut_card_le_two hB'R hB'2 hS₃'S hS₃'card hS₃'e hnorm'
  have hBcard : Nat.card B ≤ 2 := by
    have h : Nat.card ↥B' = Nat.card ↥B :=
      Subgroup.card_map_of_injective (K := B) hθinj
    omega
  refine ⟨hBcard, fun b hb hb1 => ?_⟩
  obtain ⟨c, hcR, hc⟩ :=
    l34_aut_mem_conj_r4 hB'R hB'2 hS₃'S hS₃'card hS₃'e hnorm' hBmap hBcard hb hb1
  exact l34_aut_order_seven_witness hΘconj hcR hc
end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
