module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen
open scoped commutatorElement

namespace L3InvUni

theorem map_layer_le_of_commutator_le {X : Type*} [Group X] (C J : Subgroup X)
    (h : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ J) : (CFSG.layer ↥C).map C.subtype ≤ J := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  have hperf : Group.IsPerfect ↥K := hK.1.1
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈ commutator ↥K := by
    rw [hperf.commutator_eq_top]; trivial
  have hle : commutator ↥K ≤ (J.comap C.subtype).comap K.subtype := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact h _ a.1.2 _ b.1.2
  exact hle hk'

section Entries

variable {p f : ℕ} {F : Type} [Field F]

theorem entries_row_of_commute_dgn {M : Matrix (Fin 3) (Fin 3) F} {c : Fin 3} (h2 : (2 : F) ≠ 0)
    (hcomm : M * dgn F c = dgn F c * M) {j : Fin 3} (hj : j ≠ c) : M c j = 0 := by
  have := congrFun (congrFun hcomm c) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  simp only [hj, ite_true, ite_false] at this
  have h3 : (2 : F) * M c j = 0 := by linear_combination -this
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem mat_commute_of_mem_centralizer (c : Fin 3) (t g : unitarySU p f F 3)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hg : g ∈ centralizer ({t} : Set (unitarySU p f F 3))) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * dgn F c =
      dgn F c * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have := congrArg (fun x : unitarySU p f F 3 => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hg
  simpa [Subgroup.coe_mul, Units.val_mul, ht] using this

theorem mem_centralizer_of_mat_commute (c : Fin 3) (t g : unitarySU p f F 3)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * dgn F c =
      dgn F c * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    g ∈ centralizer ({t} : Set (unitarySU p f F 3)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, ht]
  exact hg

theorem entry_mul_of_commute {M N : Matrix (Fin 3) (Fin 3) F} {c : Fin 3} (h2 : (2 : F) ≠ 0)
    (hM : M * dgn F c = dgn F c * M) : (M * N) c c = M c c * N c c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · intro k _ hk
    rw [entries_row_of_commute_dgn h2 hM hk, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

theorem commutator_mem_coordBlock (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (c : Fin 3)
    (t g g' : unitarySU p f F 3)
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hg : g ∈ centralizer ({t} : Set (unitarySU p f F 3)))
    (hg' : g' ∈ centralizer ({t} : Set (unitarySU p f F 3))) :
    ⁅g, g'⁆ ∈ coordBlock p f F c := by
  have h2 := two_ne_zero_of_data h hp2
  set N := centralizer ({t} : Set (unitarySU p f F 3)) with hN
  let mat : unitarySU p f F 3 → Matrix (Fin 3) (Fin 3) F :=
    fun x => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hmat_mul : ∀ x y : unitarySU p f F 3, mat (x * y) = mat x * mat y := fun x y => rfl
  have hcomm : ∀ x ∈ N, mat x * dgn F c = dgn F c * mat x :=
    fun x hx => mat_commute_of_mem_centralizer c t x ht hx
  have hent : ∀ x ∈ N, ∀ y : unitarySU p f F 3, mat (x * y) c c = mat x c c * mat y c c :=
    fun x hx y => by rw [hmat_mul]; exact entry_mul_of_commute h2 (hcomm x hx)
  have hone : mat 1 c c = 1 := by
    show ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) c c = 1
    simp
  have hinv : ∀ x ∈ N, mat x c c * mat x⁻¹ c c = 1 := fun x hx => by
    rw [← hent x hx, mul_inv_cancel, hone]
  have hmem : ⁅g, g'⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hg hg') (N.inv_mem hg)) (N.inv_mem hg')
  have hdiag : mat ⁅g, g'⁆ c c = 1 := by
    rw [commutatorElement_def]
    have e1 : mat (g * g' * g⁻¹ * g'⁻¹) c c =
        mat g c c * mat g' c c * mat g⁻¹ c c * mat g'⁻¹ c c := by
      rw [hent _ (N.mul_mem (N.mul_mem hg hg') (N.inv_mem hg)), hent _ (N.mul_mem hg hg'),
        hent _ hg]
    rw [e1]
    calc mat g c c * mat g' c c * mat g⁻¹ c c * mat g'⁻¹ c c
        = (mat g c c * mat g⁻¹ c c) * (mat g' c c * mat g'⁻¹ c c) := by ring
      _ = 1 := by rw [hinv g hg, hinv g' hg', one_mul]
  have hcol : ∀ i, mat ⁅g, g'⁆ i c = if i = c then 1 else 0 := fun i => by
    by_cases hi : i = c
    · subst hi; simpa using hdiag
    · simpa [hi] using entries_of_commute_dgn h2 (hcomm _ hmem) hi
  rw [mem_coordBlock, Matrix.mulVec_single_one]
  funext i
  rw [Pi.single_apply]
  exact hcol i

end Entries

section Block

variable {p f : ℕ} {F : Type} [Field F]

theorem injective_statedProjMk_comp_coordBlock (h : UnitaryFieldData p f F) (c : Fin 3) :
    Function.Injective ((statedProjMk (unitarySU p f F 3)).comp (coordBlock p f F c).subtype) := by
  set e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3) with he
  have hcomp : e.toMonoidHom.comp (unitaryProj h 3) = statedProjMk (unitarySU p f F 3) :=
    MonoidHom.ext fun g => unitaryPSUEquiv_unitaryProj h (by norm_num) g
  rw [← hcomp, MonoidHom.comp_assoc]
  exact e.injective.comp (injective_unitaryProj_comp_coordBlock h c)

theorem Ez_le_block (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (c : Fin 3)
    (t : unitarySU p f F 3) (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c) :
    Ez (statedProjMk (unitarySU p f F 3) t) ≤
      (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) := by
  unfold Ez
  apply map_layer_le_of_commutator_le
  intro x hx y hy
  obtain ⟨g, rfl⟩ := statedProjMk_surjective (unitarySU p f F 3) x
  obtain ⟨g', rfl⟩ := statedProjMk_surjective (unitarySU p f F 3) y
  have hgc : g ∈ centralizer ({t} : Set (unitarySU p f F 3)) :=
    mem_centralizer_of_mat_commute c t g ht (commute_of_mem_centralizer c t g ht hx)
  have hgc' : g' ∈ centralizer ({t} : Set (unitarySU p f F 3)) :=
    mem_centralizer_of_mat_commute c t g' ht (commute_of_mem_centralizer c t g' ht hy)
  exact ⟨⁅g, g'⁆, commutator_mem_coordBlock h hp2 c t g g' ht hgc hgc',
    map_commutatorElement _ _ _⟩

theorem Ez_eq_block (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (c : Fin 3)
    (t : unitarySU p f F 3) (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c)
    (hq : 4 ≤ p ^ f) :
    Ez (statedProjMk (unitarySU p f F 3) t) =
      (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) :=
  le_antisymm (Ez_le_block h hp2 c t ht) (block_le_Ez h hp2 c t ht hq)

end Block

section Torus

variable {p f : ℕ} {F : Type} [Field F]

@[expose] def torusGL (F : Type) [Field F] (l : Fˣ) : GL (Fin 3) F :=
  ⟨!![(l : F), 0, 0; 0, (l : F)⁻¹, 0; 0, 0, 1], !![(l : F)⁻¹, 0, 0; 0, (l : F), 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem torusGL_val (l : Fˣ) :
    ((torusGL F l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(l : F), 0, 0; 0, (l : F)⁻¹, 0; 0, 0, 1] := rfl

theorem torusGL_mem (h : UnitaryFieldData p f F) (l : Fˣ) (hl : l ^ (p ^ f + 1) = 1) :
    torusGL F l ∈ unitarySU p f F 3 := by
  rw [mem_unitarySU_iff h]
  have hl' : h.bar (l : F) * (l : F) = 1 := by
    have := congrArg Units.val hl
    rwa [Units.val_pow_eq_pow_val, pow_succ, Units.val_one, ← h.bar_apply] at this
  have hl'' : (h.bar (l : F))⁻¹ * (l : F)⁻¹ = 1 := by
    rw [← mul_inv, hl', inv_one]
  refine ⟨by simp [torusGL_val, Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusGL_val, Matrix.mul_apply, Fin.sum_univ_three, hl', hl'']

@[expose] def torusElt (h : UnitaryFieldData p f F) (l : ↥(rootsOfUnity (p ^ f + 1) F)) :
    unitarySU p f F 3 :=
  ⟨torusGL F l, torusGL_mem h l l.2⟩

theorem torusElt_mem_block (h : UnitaryFieldData p f F) (l : ↥(rootsOfUnity (p ^ f + 1) F)) :
    torusElt h l ∈ coordBlock p f F 2 := by
  rw [mem_coordBlock, Matrix.mulVec_single_one]
  funext i
  fin_cases i <;> simp [torusElt, torusGL_val]

theorem torusElt_commute (h : UnitaryFieldData p f F) (l : ↥(rootsOfUnity (p ^ f + 1) F)) :
    ((torusElt h l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * dgn F 1 =
      dgn F 1 * ((torusElt h l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  show ((torusGL F l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * dgn F 1 =
    dgn F 1 * ((torusGL F l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [torusGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, dgn, Matrix.diagonal_apply]

theorem card_rootsOfUnity_succ {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 2 ≤ q)
    (hF : Nat.card F = q ^ 2) : Nat.card ↥(rootsOfUnity (q + 1) F) = q + 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_units, hF]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
    rw [this]
    simp
  have hdvd : (q - 1) ∣ orderOf g := ⟨q + 1, by rw [hg, hcard]⟩
  have hord : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hg, hcard]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hprim : IsPrimitiveRoot (g ^ (q - 1)) (q + 1) := IsPrimitiveRoot.iff_orderOf.mpr hord
  have : NeZero (q + 1) := ⟨by omega⟩
  exact hprim.card_rootsOfUnity'

@[expose] def torusEquivFun (h : UnitaryFieldData p f F) (t₂ : unitarySU p f F 3)
    (ht₂ : ((t₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 1)
    (l : ↥(rootsOfUnity (p ^ f + 1) F)) :
    ↥(coordBlock p f F 2 ⊓ centralizer ({t₂} : Set (unitarySU p f F 3))) :=
  ⟨torusElt h l, Subgroup.mem_inf.mpr ⟨torusElt_mem_block h l,
    mem_centralizer_of_mat_commute 1 t₂ _ ht₂ (torusElt_commute h l)⟩⟩

theorem torusEquivFun_injective (h : UnitaryFieldData p f F) (t₂ : unitarySU p f F 3)
    (ht₂ : ((t₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 1) :
    Function.Injective (torusEquivFun h t₂ ht₂) := by
  intro l l' hll
  have := congrArg (fun x : ↥(coordBlock p f F 2 ⊓ centralizer ({t₂} : Set (unitarySU p f F 3))) =>
    ((x.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) hll
  simp [torusEquivFun, torusElt, torusGL_val] at this
  exact Subtype.ext (Units.ext this)

theorem torusEquivFun_surjective (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (t₂ : unitarySU p f F 3)
    (ht₂ : ((t₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 1) :
    Function.Surjective (torusEquivFun h t₂ ht₂) := by
  have h2 := two_ne_zero_of_data h hp2
  rintro ⟨b, hb⟩
  obtain ⟨hbB2, hbC2⟩ := Subgroup.mem_inf.mp hb
  set M : Matrix (Fin 3) (Fin 3) F := ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hM
  have hcol : ∀ i, M i 2 = if i = 2 then 1 else 0 := block_col (mem_coordBlock.mp hbB2)
  have hU : (M.map h.bar)ᵀ * M = 1 := ((mem_unitarySU_iff h).mp b.2).2
  have hrow : ∀ j, M 2 j = if 2 = j then 1 else 0 := block_row h.bar hU hcol
  have hc : M * dgn F 1 = dgn F 1 * M := mat_commute_of_mem_centralizer 1 t₂ b ht₂ hbC2
  have h01 : M 0 1 = 0 := entries_of_commute_dgn h2 hc (by decide)
  have h21 : M 2 1 = 0 := entries_of_commute_dgn h2 hc (by decide)
  have h10 : M 1 0 = 0 := entries_row_of_commute_dgn h2 hc (by decide)
  have h12 : M 1 2 = 0 := entries_row_of_commute_dgn h2 hc (by decide)
  have h02 : M 0 2 = 0 := by simpa using hcol 0
  have h20 : M 2 0 = 0 := by simpa using hrow 0
  have h22 : M 2 2 = 1 := by simpa using hcol 2
  have hdet : M.det = 1 := ((mem_unitarySU_iff h).mp b.2).1
  have hdet' : M 0 0 * M 1 1 = 1 := by
    rw [Matrix.det_fin_three] at hdet
    simpa [h01, h02, h10, h12, h20, h21, h22] using hdet
  have hunit : h.bar (M 0 0) * M 0 0 = 1 := by
    have := congrFun (congrFun hU 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h10, h20] using this
  have hinv : (M 0 0)⁻¹ = M 1 1 := inv_eq_of_mul_eq_one_right hdet'
  obtain ⟨l, hlv⟩ : ∃ l : Fˣ, (l : F) = M 0 0 :=
    ⟨⟨M 0 0, M 1 1, hdet', by rw [mul_comm]; exact hdet'⟩, rfl⟩
  have hl : l ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one, hlv, ← h.bar_apply]
    exact hunit
  refine ⟨⟨l, (mem_rootsOfUnity _ _).mpr hl⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show ((torusGL F l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M
  rw [torusGL_val, hlv, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, h22]

theorem card_block_inf_centralizer (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq2 : 2 ≤ p ^ f)
    (t₂ : unitarySU p f F 3)
    (ht₂ : ((t₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 1) :
    Nat.card ↥(coordBlock p f F 2 ⊓ centralizer ({t₂} : Set (unitarySU p f F 3))) = p ^ f + 1 := by
  have hfin := h.finite
  have hF : Nat.card F = (p ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨torusEquivFun_injective h t₂ ht₂,
    torusEquivFun_surjective h hp2 t₂ ht₂⟩)).symm.trans (card_rootsOfUnity_succ hq2 hF)

end Torus

section Std

variable {p f : ℕ} {F : Type} [Field F]

theorem map_block_inf_centralizer (c c' : Fin 3) (t' : unitarySU p f F 3)
    (ht' : ((t' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F c') :
    (coordBlock p f F c).map (statedProjMk (unitarySU p f F 3)) ⊓
        centralizer ({statedProjMk (unitarySU p f F 3) t'} : Set (StatedProj (unitarySU p f F 3))) =
      (coordBlock p f F c ⊓ centralizer ({t'} : Set (unitarySU p f F 3))).map
        (statedProjMk (unitarySU p f F 3)) := by
  ext x
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hx⟩
    exact ⟨b, Subgroup.mem_inf.mpr ⟨hb, mem_centralizer_of_mat_commute c' t' b ht'
      (commute_of_mem_centralizer c' t' b ht' hx)⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
    have hc : b * t' = t' * b := Subgroup.mem_centralizer_singleton_iff.mp hbC
    exact ⟨⟨b, hbB, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hc])⟩

theorem card_map_of_le_block (h : UnitaryFieldData p f F) (c : Fin 3)
    (T : Subgroup (unitarySU p f F 3)) (hT : T ≤ coordBlock p f F c) :
    Nat.card ↥(T.map (statedProjMk (unitarySU p f F 3))) = Nat.card ↥T := by
  have hinj : Set.InjOn (statedProjMk (unitarySU p f F 3)) (T : Set (unitarySU p f F 3)) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (injective_statedProjMk_comp_coordBlock h c
      (a₁ := ⟨x, hT hx⟩) (a₂ := ⟨y, hT hy⟩) hxy)
  exact Nat.card_image_of_injOn hinj

theorem card_std (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq4 : 4 ≤ p ^ f)
    (t₃ t₂ : unitarySU p f F 3)
    (ht₃ : ((t₃ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 2)
    (ht₂ : ((t₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 1) :
    Nat.card ↥(centralizer ({statedProjMk (unitarySU p f F 3) t₂} :
        Set (StatedProj (unitarySU p f F 3))) ⊓ Ez (statedProjMk (unitarySU p f F 3) t₃)) =
      p ^ f + 1 := by
  rw [Ez_eq_block h hp2 2 t₃ ht₃ hq4, inf_comm, map_block_inf_centralizer 2 1 t₂ ht₂,
    card_map_of_le_block h 2 _ inf_le_left]
  exact card_block_inf_centralizer h hp2 (by omega) t₂ ht₂

end Std

theorem l3InvTorus_std (F : Type) [Field F] [Finite F] {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (hF : Nat.card F = q ^ 2) :
    Nat.card ↥(centralizer ({uniU₀' F hq} : Set (StatedProj (StatedSU 3 q F))) ⊓
      Ez (uniU₀ F hq)) = q + 1 := by
  obtain ⟨p, f, h, rfl, hp2⟩ := Std44UniConj.exists_unitaryFieldData hq hF
  exact card_std h hp2 (by omega)
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
    ⟨oddDiag₂ F, Subgroup.subset_closure ⟨det_oddDiag₂ F, unitary_oddDiag₂ hq⟩⟩
    (dgn_oddDiag₃ F) (dgn_oddDiag₂ F)

section Transport

theorem map_centralizer_singleton {K X : Type*} [Group K] [Group X] (φ : K ≃* X) (b : K) :
    (centralizer ({b} : Set K)).map φ.toMonoidHom = centralizer ({φ b} : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    show φ y * φ b = φ b * φ y
    rw [← map_mul, ← map_mul, hy']
  · intro hx
    have hx' : x * φ b = φ b * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨φ.symm x, Subgroup.mem_centralizer_singleton_iff.mpr ?_, φ.apply_symm_apply x⟩
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact hx'

theorem card_inf_Ez_transport {J X : Type} [Group J] [Group X] (φ : J ≃* X) (a b : J) :
    Nat.card ↥(centralizer ({b} : Set J) ⊓ Ez a) =
      Nat.card ↥(centralizer ({φ b} : Set X) ⊓ Ez (φ a)) := by
  have h1 : (centralizer ({b} : Set J) ⊓ Ez a).map φ.toMonoidHom =
      centralizer ({φ b} : Set X) ⊓ Ez (φ a) := by
    rw [Subgroup.map_inf _ _ _ φ.injective, map_centralizer_singleton, Ez_map]
  rw [← h1]
  exact (Subgroup.card_map_of_injective φ.injective).symm

end Transport

end L3InvUni

theorem l3InvTorus_uni (J : Type) [Group J] [Finite J] (q : ℕ) (hq : Odd q) (hq5 : 5 ≤ q)
    (hJ : IsLnEps 3 J (-1) q) (a b : J) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a ≠ b) (hcomm : a * b = b * a) :
    (Nat.card ↥(Subgroup.centralizer ({b} : Set J) ⊓ Ez a) : ℤ) = (q : ℤ) - (-1) := by
  rcases hJ with ⟨h1, -⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩
  · exact absurd h1 (by norm_num)
  · have h1 : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
    have h2 : orderOf (e b) = 2 := by rw [MulEquiv.orderOf_eq]; exact hb
    have h3 : e a ≠ e b := fun h => hab (e.injective h)
    have h4 : e a * e b = e b * e a := by rw [← map_mul, ← map_mul, hcomm]
    obtain ⟨g, hg1, hg2⟩ := uniConj F hq hF _ _ h1 h2 h3 h4
    let φ : J ≃* StatedProj (StatedSU 3 q F) := e.trans (MulAut.conj g)
    have hφa : φ a = uniU₀ F hq := by simpa [φ, MulAut.conj_apply] using hg1
    have hφb : φ b = uniU₀' F hq := by simpa [φ, MulAut.conj_apply] using hg2
    rw [L3InvUni.card_inf_Ez_transport φ a b, hφa, hφb, L3InvUni.l3InvTorus_std F hq hq5 hF]
    push_cast
    ring

end CFSG.GH74.GLS.LU.Local
