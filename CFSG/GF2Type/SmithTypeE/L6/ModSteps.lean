module

public import CFSG.GF2Type.SmithTypeE.L6.Defs
public import CFSG.LargeExtraspecial.S14SMGPair
public import CFSG.LargeExtraspecial.S14SMGMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.LargeExtraspecial.S14.SMG
open CFSG.SmithL6 (wt adjW tvCols)
open CFSG.SmithE (applyCols)
open scoped MatrixGroups

structure ModelFacts : Prop where
  wt_ne_zero : ∀ {i : Nat}, i < 1395 → wt i ≠ 0
  exists_adj : ∀ {i : Nat}, i < 1395 → ∃ j < 1395, adjW i j = true ∧ wt j ≠ wt i
  wt_ne_xor : ∀ {i j : Nat}, i < 1395 → j < 1395 → adjW i j = false →
    ∀ k < 1395, wt k ≠ wt i ^^^ wt j
  tv_wt : ∀ {k i : Nat}, k < 1953 → i < 1395 →
    ∃ j < 1395, wt j = applyCols (tvCols k) (wt i) ∧ adjW i j = true
  pair_rel_sym : ∀ {k l : Nat}, k < 1953 → l < 1953 → k ≠ l →
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c)) ∨
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) ∨
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) c))) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c))))
  int_rel_sym : ∀ {k l : Nat}, k < 1953 → l < 1953 → k ≠ l → ∀ {c c' : Nat}, c < 2 ^ 20 →
    c' < 2 ^ 20 → applyCols (tvCols k) c ^^^ c = applyCols (tvCols l) c' ^^^ c' →
      applyCols (tvCols k) c ^^^ c = 0 ∨
        ((∀ e < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) e) =
          applyCols (tvCols l) (applyCols (tvCols k) e)) ∧
         ∃ j < 1395, wt j = applyCols (tvCols k) c ^^^ c)

theorem fourth_mem_of_dihedral {G : Type} [Group G] [Finite G] {S : Setting G}
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)} {x y : G} {A B : Nat → Nat} (hxM : x ∈ S.M)
    (hyM : y ∈ S.M) (hA : Acts S φ x A) (hB : Acts S φ y B)
    (hAA : ∀ c < 2 ^ 20, A (A c) = c) (hBB : ∀ c < 2 ^ 20, B (B c) = c)
    (hd8 : ∀ c < 2 ^ 20, A (B (A (B c))) = B (A (B (A c)))) : (x * y) ^ 4 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  have hxy2 := hxy.mul hm hxy
  have hxy3 := hxy.mul (S.M.mul_mem hm hm) hxy2
  have hxy4 := hxy.mul (S.M.mul_mem hm (S.M.mul_mem hm hm)) hxy3
  rw [show (x * y) ^ 4 = x * y * (x * y * (x * y * (x * y))) by
    rw [pow_succ, pow_succ, sq, mul_assoc, mul_assoc]]
  refine mem_QG_of_acts (S.M.mul_mem hm (S.M.mul_mem hm (S.M.mul_mem hm hm))) hxy4 fun c hc => ?_
  have hAc : A c < 2 ^ 20 := hA.lt hc
  have hBAc : B (A c) < 2 ^ 20 := hB.lt hAc
  have hABAc : A (B (A c)) < 2 ^ 20 := hA.lt hBAc
  have hD : A (B (A (B c))) = B (A (B (A c))) := hd8 c hc
  change A (B (A (B (A (B (A (B c))))))) = c
  rw [hD, hBB _ hABAc, hAA _ hBAc, hBB _ hAc]
  exact hAA c hc

theorem smithL6E34Q_of (hF : ModelFacts) (hM : SmithL6Module) : SmithL6E34Q := by
  intro G _ _ _ S hw hU h b haQ hb hbQ _ hbQa habz
  obtain ⟨φ, h2a, -, h3, -⟩ := hM G S hw hU
  by_cases haz : h * S.z * h⁻¹ = S.z
  · exact hbQa (by rw [SMG.Qa_eq_QG_of_eq S haz]; exact hbQ)
  have hzQa : S.z ∈ S.Qa h := S.z_mem_Qa_of_mem_QG rfl haQ haz
  have haQa : h * S.z * h⁻¹ ∈ S.Qa h := (S.conjBy h).z_mem_QG
  have hbz : b ≠ S.z := fun e => hbQa (e ▸ hzQa)
  obtain ⟨i, hi, hai⟩ := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) haQ haz
  obtain ⟨j, hj, hbj⟩ := h2a b hb hbQ hbz
  have hadj : adjW i j = false := by
    cases e : adjW i j
    · rfl
    · exact absurd ((h3 h b haQ haz hb hbQ hbz i j hi hj hai hbj).mpr e) hbQa
  have habne : h * S.z * h⁻¹ * b ≠ S.z := by
    intro e
    apply hbQa
    have hb' : b = (h * S.z * h⁻¹)⁻¹ * S.z := by
      calc b = (h * S.z * h⁻¹)⁻¹ * (h * S.z * h⁻¹ * b) := by group
        _ = (h * S.z * h⁻¹)⁻¹ * S.z := by rw [e]
    rw [hb']
    exact (S.Qa h).mul_mem ((S.Qa h).inv_mem haQa) hzQa
  obtain ⟨k, hk, habk⟩ := h2a _ habz (S.QG.mul_mem haQ hbQ) habne
  rw [S.cl_mul haQ hbQ, psi_add, hai, hbj] at habk
  exact hF.wt_ne_xor hi hj hadj k hk habk.symm

theorem smithL6E24Line_of (hF : ModelFacts) (hM : SmithL6Module) :
    SmithL6E24Line := by
  intro G _ _ _ S hw hU h hbQ hbz
  obtain ⟨φ, h2a, h2b, h3, -⟩ := hM G S hw hU
  obtain ⟨i, hi, hbi⟩ := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) hbQ hbz
  obtain ⟨j, hj, hadj, hne⟩ := hF.exists_adj hi
  obtain ⟨c, hc, hcQ, hcj⟩ := h2b j hj
  have hcz : c ≠ S.z := by
    rintro rfl
    rw [S.cl_z, psi_zero] at hcj
    exact hF.wt_ne_zero hj hcj.symm
  refine ⟨c, hc, hcQ, (h3 h c hbQ hbz hc hcQ hcz i j hi hj hbi hcj).mpr hadj, hcz, ?_, ?_⟩
  · rintro rfl
    exact hne (hcj.symm.trans hbi)
  · intro e
    apply hne
    rw [← hcj, ← hbi, e, S.cl_mul S.z_mem_QG hbQ, S.cl_z, zero_add]

theorem smithL6E24_of (hF : ModelFacts) (hM : SmithL6Module) : SmithL6E24 := by
  intro G _ _ _ S hw hU x h hx hxM hxQ hyQ
  obtain ⟨φ, h2a, -, h3, h4⟩ := hM G S hw hU
  by_cases hyz : h * S.z * h⁻¹ = S.z
  · rw [SMG.Qa_eq_QG_of_eq S hyz, hyz]
    have e : x * S.z * x⁻¹ = S.z := by
      rw [S.z_comm hxM]
      group
    rw [e]
    exact S.z_mem_QG
  obtain ⟨i, hi, hyi⟩ := h2a _ (isConj_iff.mpr ⟨h, rfl⟩) hyQ hyz
  obtain ⟨k, hk, hkx⟩ := h4 x hx hxM hxQ
  obtain ⟨j, hj, hji, hadj⟩ := hF.tv_wt hk hi
  have hc : IsConj S.z (x * (h * S.z * h⁻¹) * x⁻¹) := isConj_iff.mpr ⟨x * h, by group⟩
  have hcz : x * (h * S.z * h⁻¹) * x⁻¹ ≠ S.z := by
    intro e
    apply hyz
    calc h * S.z * h⁻¹ = x⁻¹ * (x * (h * S.z * h⁻¹) * x⁻¹) * x := by group
      _ = x⁻¹ * (S.z * x) := by rw [e, mul_assoc]
      _ = x⁻¹ * (x * S.z) := by rw [S.z_comm hxM]
      _ = S.z := by group
  have hcj : code (φ (S.cl (x * (h * S.z * h⁻¹) * x⁻¹))) = wt j := by
    rw [hkx _ hyQ, hyi, hji]
  exact (h3 h _ hyQ hyz hc (S.conj_mem_QG hxM hyQ) hcz i j hi hj hyi hcj).mpr hadj

theorem smithL6E23_of (hF : ModelFacts) (hM : SmithL6Module) : SmithL6E23 := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ hyQ
  obtain ⟨φ, -, -, -, h4⟩ := hM G S hw hU
  obtain ⟨k, hk, hA⟩ := h4 x hx hxM hxQ
  obtain ⟨l, hl, hB⟩ := h4 y hy hyM hyQ
  change Acts S φ x (applyCols (tvCols k)) at hA
  change Acts S φ y (applyCols (tvCols l)) at hB
  have hAA := hA.invol hx hxM
  have hBB := hB.invol hy hyM
  by_cases hkl : k = l
  · subst hkl
    exact Or.inl (mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun c hc => hAA c hc)
  rcases hF.pair_rel_sym hk hl hkl with hc | hbr | hd8
  · exact Or.inr (Or.inl (sq_mem_of_comm hxM hyM hA hB hAA hBB hc))
  · exact Or.inr (Or.inr (Or.inl (cube_mem_of_braid hxM hyM hA hB hAA hBB hbr)))
  · exact Or.inr (Or.inr (Or.inr (fourth_mem_of_dihedral hxM hyM hA hB hAA hBB hd8)))

theorem smithL6E25_of (hF : ModelFacts) (hM : SmithL6Module) : SmithL6E25 := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ hyQ hxyQ
  obtain ⟨φ, -, h2b, -, h4⟩ := hM G S hw hU
  obtain ⟨k, hk, hA⟩ := h4 x hx hxM hxQ
  obtain ⟨l, hl, hB⟩ := h4 y hy hyM hyQ
  change Acts S φ x (applyCols (tvCols k)) at hA
  change Acts S φ y (applyCols (tvCols l)) at hB
  have hAA := hA.invol hx hxM
  have hBB := hB.invol hy hyM
  have hkl : k ≠ l := by
    rintro rfl
    exact hxyQ (mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun c hc => hAA c hc)
  have hint : ∀ v ∈ S.commQt x ⊓ S.commQt y, code (φ v) = 0 ∨
      ((∀ e < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) e) =
        applyCols (tvCols l) (applyCols (tvCols k) e)) ∧ ∃ j < 1395, wt j = code (φ v)) := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := code_mem_commQt hxM hA hv.1
    obtain ⟨c', hc', hcv'⟩ := code_mem_commQt hyM hB hv.2
    rw [hcv]
    exact hF.int_rel_sym hk hl hkl hc hc' (hcv.symm.trans hcv')
  have hzero : ∀ {v : S.Qt}, code (φ v) = 0 → v = 0 := fun h => psi_inj S φ (by rw [h, psi_zero])
  refine ⟨fun _ v hv => ?_, fun hcu => ?_, fun hn2 _ => ?_⟩
  · rcases hint v hv with h0 | ⟨-, j, hj, hjv⟩
    · exact ⟨S.z, IsConj.refl _, S.z_mem_QG, by rw [hzero h0, S.cl_z]⟩
    · obtain ⟨c, hc, hcQ, hcj⟩ := h2b j hj
      exact ⟨c, hc, hcQ, psi_inj S φ (hcj.trans hjv)⟩
  · have hbr := braid_of_cube_mem hxM hyM hA hB hAA hBB hcu
    rw [eq_bot_iff]
    intro v hv
    rcases hint v hv with h0 | ⟨hc, -⟩
    · exact (Submodule.mem_bot _).mpr (hzero h0)
    · exfalso
      apply hxyQ
      refine mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun c hc' => ?_
      have e1 : applyCols (tvCols l) c = applyCols (tvCols k) c :=
        calc applyCols (tvCols l) c
            = applyCols (tvCols k) (applyCols (tvCols k) (applyCols (tvCols l) c)) :=
              (hAA _ (hB.lt hc')).symm
          _ = applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) := by
              rw [hc c hc']
          _ = applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c)) := hbr c hc'
          _ = applyCols (tvCols l) (applyCols (tvCols l) (applyCols (tvCols k) c)) := by
              rw [hc c hc']
          _ = applyCols (tvCols k) c := hBB _ (hA.lt hc')
      change applyCols (tvCols k) (applyCols (tvCols l) c) = c
      rw [e1, hAA c hc']
  · rw [eq_bot_iff]
    intro v hv
    rcases hint v hv with h0 | ⟨hc, -⟩
    · exact (Submodule.mem_bot _).mpr (hzero h0)
    · exact absurd (sq_mem_of_comm hxM hyM hA hB hAA hBB hc) hn2

end CFSG.GF2Type.SmithTypeE.L6
