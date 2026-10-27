module

public import CFSG.LargeExtraspecial.S14SMEDefs
public import CFSG.LargeExtraspecial.S14SMGAct
public import CFSG.LargeExtraspecial.S14SMGCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.SmithE SMG

namespace SMG

variable {G : Type} [Group G] [Finite G] {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)}
  {x y : G} {A B : Nat → Nat}

theorem sq_mem_of_comm (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A) (hB : Acts S φ y B)
    (hAA : ∀ c < 2 ^ 20, A (A c) = c) (hBB : ∀ c < 2 ^ 20, B (B c) = c)
    (hc : ∀ c < 2 ^ 20, A (B c) = B (A c)) : (x * y) ^ 2 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  rw [sq]
  refine mem_QG_of_acts (S.M.mul_mem hm hm) (hxy.mul hm hxy) fun c hc' => ?_
  rw [hc c hc', hBB _ (hA.lt hc'), hAA c hc']

theorem cube_mem_of_braid (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ c < 2 ^ 20, A (A c) = c) (hBB : ∀ c < 2 ^ 20, B (B c) = c)
    (hbr : ∀ c < 2 ^ 20, A (B (A c)) = B (A (B c))) : (x * y) ^ 3 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  rw [show (x * y) ^ 3 = x * y * (x * y * (x * y)) by rw [pow_succ, sq, mul_assoc]]
  refine mem_QG_of_acts (S.M.mul_mem hm (S.M.mul_mem hm hm))
    (hxy.mul (S.M.mul_mem hm hm) (hxy.mul hm hxy)) fun c hc' => ?_
  have h1 : B c < 2 ^ 20 := hB.lt hc'
  have h2 : A (B c) < 2 ^ 20 := hA.lt h1
  rw [hbr _ (hB.lt h2), hBB _ h2, hAA _ h1, hBB c hc']

omit [Finite G] in
theorem braid_of_cube_mem (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ c < 2 ^ 20, A (A c) = c) (hBB : ∀ c < 2 ^ 20, B (B c) = c)
    (hcu : (x * y) ^ 3 ∈ S.QG) : ∀ c < 2 ^ 20, A (B (A c)) = B (A (B c)) := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  rw [show (x * y) ^ 3 = x * y * (x * y * (x * y)) by rw [pow_succ, sq, mul_assoc]] at hcu
  have hF := acts_of_mem_QG hcu (hxy.mul (S.M.mul_mem hm hm) (hxy.mul hm hxy))
  intro c hc
  have h1 : B c < 2 ^ 20 := hB.lt hc
  have h2 : A (B c) < 2 ^ 20 := hA.lt h1
  have := hF (B (A (B c))) (hB.lt h2)
  change A (B (A (B (A (B (B (A (B c)))))))) = B (A (B c)) at this
  rwa [hBB _ h2, hAA _ h1, hBB c hc] at this

theorem code_mem_commQt {w : G} {T : Nat → Nat} (hwM : w ∈ S.M) (hT : Acts S φ w T)
    {v : S.Qt} (hv : v ∈ S.commQt w) : ∃ c < 2 ^ 20, code (φ v) = T c ^^^ c := by
  obtain ⟨u, hu, rfl⟩ := (S.mem_commQt_iff hwM).mp hv
  refine ⟨code (φ (S.cl u)), psi_lt S φ _, ?_⟩
  rw [S.cl_mul (S.conj_mem_QG hwM hu) (S.QG.inv_mem hu), S.cl_inv hu, psi_add, hT u hu]

end SMG

theorem smithE23_of (hM : SmithE22Module) : SmithE23 := by
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
  rcases pair_rel_sym hk hl hkl with hc | hbr
  · exact Or.inr (Or.inl (sq_mem_of_comm hxM hyM hA hB hAA hBB hc))
  · exact Or.inr (Or.inr (cube_mem_of_braid hxM hyM hA hB hAA hBB hbr))

theorem smithE25_of
    (hM : SmithE22Module) : SmithE25 := by
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
        applyCols (tvCols l) (applyCols (tvCols k) e)) ∧ ∃ j < 891, wt j = code (φ v)) := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := code_mem_commQt hxM hA hv.1
    obtain ⟨c', hc', hcv'⟩ := code_mem_commQt hyM hB hv.2
    rw [hcv]
    exact int_rel_sym hk hl hkl hc hc' (hcv.symm.trans hcv')
  have hzero : ∀ {v : S.Qt}, code (φ v) = 0 → v = 0 := fun h => psi_inj S φ (by rw [h, psi_zero])
  refine ⟨fun _ v hv => ?_, fun hcu => ?_⟩
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

end CFSG.LargeExtraspecial.S14
