module

public import CFSG.GF2Type.SmithTypeE.E7.ModDefs
public import CFSG.GF2Type.SmithTypeE.E7.ModFacts
public import CFSG.GF2Type.SmithTypeE.E7.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.LargeExtraspecial
open CFSG.SmithD6 (wt tvCols applyCols)
open CFSG.GF2Type.SmithTypeE.DMod (decode32 code32 code32_lt decode32_code32 code32_decode32
  decode32_xor decode32_zero)

theorem code32_add (u v : Fin 32 → ZMod 2) : code32 (u + v) = code32 u ^^^ code32 v := by
  have hx : code32 u ^^^ code32 v < 2 ^ 32 := Nat.xor_lt_two_pow (code32_lt u) (code32_lt v)
  have e : u + v = decode32 (code32 u ^^^ code32 v) := by
    rw [decode32_xor, decode32_code32, decode32_code32]
  rw [e, code32_decode32 hx]

theorem code32_zero : code32 0 = 0 := by
  have h := code32_decode32 (c := 0) (by norm_num)
  rwa [decode32_zero] at h

theorem code32_injective : Function.Injective code32 := by
  intro u v h
  have h' := congrArg decode32 h
  rwa [decode32_code32, decode32_code32] at h'

theorem exists_code32 {c : Nat} (hc : c < 2 ^ 32) : ∃ v : Fin 32 → ZMod 2, code32 v = c :=
  ⟨decode32 c, code32_decode32 hc⟩

section Action

variable {G : Type} [Group G] (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2))

theorem psi_add (u v : S.Qt) : code32 (φ (u + v)) = code32 (φ u) ^^^ code32 (φ v) := by
  rw [map_add, code32_add]

theorem psi_zero : code32 (φ 0) = 0 := by
  rw [map_zero, code32_zero]

theorem psi_lt (v : S.Qt) : code32 (φ v) < 2 ^ 32 := code32_lt _

theorem psi_inj {u v : S.Qt} (h : code32 (φ u) = code32 (φ v)) : u = v :=
  φ.injective (code32_injective h)

theorem exists_psi {c : Nat} (hc : c < 2 ^ 32) : ∃ u ∈ S.QG, code32 (φ (S.cl u)) = c := by
  obtain ⟨v, rfl⟩ := exists_code32 hc
  obtain ⟨u, hu, huv⟩ := S.exists_cl (φ.symm v)
  exact ⟨u, hu, by rw [huv, φ.apply_symm_apply]⟩

theorem mul_self_eq_one_of_isConj {x : G} (hx : IsConj S.z x) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  calc g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ := by group
    _ = 1 := by rw [S.z_mul_z]; group

@[expose] def Acts (g : G) (F : Nat → Nat) : Prop :=
  ∀ u ∈ S.QG, code32 (φ (S.cl (g * u * g⁻¹))) = F (code32 (φ (S.cl u)))

variable {S φ}

theorem Acts.mul {g h : G} {F H : Nat → Nat} (hh : h ∈ S.M) (hg : Acts S φ g F)
    (hH : Acts S φ h H) : Acts S φ (g * h) (fun c => F (H c)) := by
  intro u hu
  have e : g * h * u * (g * h)⁻¹ = g * (h * u * h⁻¹) * g⁻¹ := by group
  rw [e, hg _ (S.conj_mem_QG hh hu), hH u hu]

theorem Acts.lt {g : G} {F : Nat → Nat} (hg : Acts S φ g F) {c : Nat} (hc : c < 2 ^ 32) :
    F c < 2 ^ 32 := by
  obtain ⟨u, hu, rfl⟩ := exists_psi S φ hc
  rw [← hg u hu]
  exact psi_lt S φ _

theorem mem_QG_of_acts [Finite G] {g : G} {F : Nat → Nat} (hgM : g ∈ S.M) (hg : Acts S φ g F)
    (hF : ∀ c < 2 ^ 32, F c = c) : g ∈ S.QG :=
  S.mem_QG_of_cl_conj hgM fun u hu => psi_inj S φ (by rw [hg u hu, hF _ (psi_lt S φ _)])

theorem cl_conj_of_mem_QG {g u : G} (hg : g ∈ S.QG) (hu : u ∈ S.QG) :
    S.cl (g * u * g⁻¹) = S.cl u := by
  rcases S.commutator_eq_one_or_z hg hu with h | h
  · have e : g * u * g⁻¹ = u := by
      calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
        _ = u := by rw [h, one_mul]
    rw [e]
  · have e : g * u * g⁻¹ = S.z * u := by
      calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
        _ = S.z * u := by rw [h]
    rw [e, S.cl_mul S.z_mem_QG hu, S.cl_z, zero_add]

theorem acts_of_mem_QG {g : G} {F : Nat → Nat} (hgQ : g ∈ S.QG) (hg : Acts S φ g F) :
    ∀ c < 2 ^ 32, F c = c := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := exists_psi S φ hc
  rw [← hg u hu, cl_conj_of_mem_QG hgQ hu]

theorem Acts.invol {x : G} {F : Nat → Nat} (hx : IsConj S.z x) (hxM : x ∈ S.M)
    (hF : Acts S φ x F) : ∀ c < 2 ^ 32, F (F c) = c := by
  have h1 : x * x = 1 := mul_self_eq_one_of_isConj S hx
  apply acts_of_mem_QG (g := x * x) (by rw [h1]; exact S.QG.one_mem) (hF.mul hxM hF)

end Action

section Pair

variable {G : Type} [Group G] [Finite G] {S : Setting G}
  {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {x y : G} {A B : Nat → Nat}

theorem sq_mem_of_comm (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A) (hB : Acts S φ y B)
    (hAA : ∀ c < 2 ^ 32, A (A c) = c) (hBB : ∀ c < 2 ^ 32, B (B c) = c)
    (hc : ∀ c < 2 ^ 32, A (B c) = B (A c)) : (x * y) ^ 2 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  rw [sq]
  refine mem_QG_of_acts (S.M.mul_mem hm hm) (hxy.mul hm hxy) fun c hc' => ?_
  rw [hc c hc', hBB _ (hA.lt hc'), hAA c hc']

theorem cube_mem_of_braid (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ c < 2 ^ 32, A (A c) = c) (hBB : ∀ c < 2 ^ 32, B (B c) = c)
    (hbr : ∀ c < 2 ^ 32, A (B (A c)) = B (A (B c))) : (x * y) ^ 3 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  rw [show (x * y) ^ 3 = x * y * (x * y * (x * y)) by rw [pow_succ, sq, mul_assoc]]
  refine mem_QG_of_acts (S.M.mul_mem hm (S.M.mul_mem hm hm))
    (hxy.mul (S.M.mul_mem hm hm) (hxy.mul hm hxy)) fun c hc' => ?_
  have h1 : B c < 2 ^ 32 := hB.lt hc'
  have h2 : A (B c) < 2 ^ 32 := hA.lt h1
  rw [hbr _ (hB.lt h2), hBB _ h2, hAA _ h1, hBB c hc']

omit [Finite G] in
theorem braid_of_cube_mem (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ c < 2 ^ 32, A (A c) = c) (hBB : ∀ c < 2 ^ 32, B (B c) = c)
    (hcu : (x * y) ^ 3 ∈ S.QG) : ∀ c < 2 ^ 32, A (B (A c)) = B (A (B c)) := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  rw [show (x * y) ^ 3 = x * y * (x * y * (x * y)) by rw [pow_succ, sq, mul_assoc]] at hcu
  have hF := acts_of_mem_QG hcu (hxy.mul (S.M.mul_mem hm hm) (hxy.mul hm hxy))
  intro c hc
  have h1 : B c < 2 ^ 32 := hB.lt hc
  have h2 : A (B c) < 2 ^ 32 := hA.lt h1
  have := hF (B (A (B c))) (hB.lt h2)
  change A (B (A (B (A (B (B (A (B c)))))))) = B (A (B c)) at this
  rwa [hBB _ h2, hAA _ h1, hBB c hc] at this

theorem fourth_mem_of_dihedral (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ c < 2 ^ 32, A (A c) = c) (hBB : ∀ c < 2 ^ 32, B (B c) = c)
    (hd8 : ∀ c < 2 ^ 32, A (B (A (B c))) = B (A (B (A c)))) : (x * y) ^ 4 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (fun c => A (B c)) := hA.mul hyM hB
  have hxy2 := hxy.mul hm hxy
  have hxy3 := hxy.mul (S.M.mul_mem hm hm) hxy2
  have hxy4 := hxy.mul (S.M.mul_mem hm (S.M.mul_mem hm hm)) hxy3
  rw [show (x * y) ^ 4 = x * y * (x * y * (x * y * (x * y))) by
    rw [pow_succ, pow_succ, sq, mul_assoc, mul_assoc]]
  refine mem_QG_of_acts (S.M.mul_mem hm (S.M.mul_mem hm (S.M.mul_mem hm hm))) hxy4
    fun c hc => ?_
  have hAc : A c < 2 ^ 32 := hA.lt hc
  have hBAc : B (A c) < 2 ^ 32 := hB.lt hAc
  have hABAc : A (B (A c)) < 2 ^ 32 := hA.lt hBAc
  have hD : A (B (A (B c))) = B (A (B (A c))) := hd8 c hc
  change A (B (A (B (A (B (A (B c))))))) = c
  rw [hD, hBB _ hABAc, hAA _ hBAc, hBB _ hAc]
  exact hAA c hc

theorem code_mem_commQt {w : G} {T : Nat → Nat} (hwM : w ∈ S.M) (hT : Acts S φ w T)
    {v : S.Qt} (hv : v ∈ S.commQt w) : ∃ c < 2 ^ 32, code32 (φ v) = T c ^^^ c := by
  obtain ⟨u, hu, rfl⟩ := (S.mem_commQt_iff hwM).mp hv
  refine ⟨code32 (φ (S.cl u)), psi_lt S φ _, ?_⟩
  rw [S.cl_mul (S.conj_mem_QG hwM hu) (S.QG.inv_mem hu), S.cl_inv hu, psi_add, hT u hu]

end Pair

theorem smithE7E23_of (hF : E7ModelFacts) (hM : SmithE7Module) : SmithE7E23 := by
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

theorem smithE7E25_of (hF : E7ModelFacts) (hM : SmithE7Module) : SmithE7E25 := by
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
  have hint : ∀ v ∈ S.commQt x ⊓ S.commQt y, code32 (φ v) = 0 ∨
      ((∀ e < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) e) =
        applyCols (tvCols l) (applyCols (tvCols k) e)) ∧ ∃ j < 75735, wt j = code32 (φ v)) := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := code_mem_commQt hxM hA hv.1
    obtain ⟨c', hc', hcv'⟩ := code_mem_commQt hyM hB hv.2
    rw [hcv]
    exact hF.int_rel_sym hk hl hkl hc hc' (hcv.symm.trans hcv')
  have hzero : ∀ {v : S.Qt}, code32 (φ v) = 0 → v = 0 :=
    fun h => psi_inj S φ (by rw [h, psi_zero])
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
          _ = applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c)) :=
              hbr c hc'
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

end CFSG.GF2Type.SmithTypeE.E7
