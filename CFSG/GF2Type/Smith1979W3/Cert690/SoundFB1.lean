module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check
public import CFSG.GF2Type.Smith1979W3.Cert690.Dict

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem array_getElem!_eq_getElem_of_lt {α : Type*} [Inhabited α] {A : Array α} {i : ℕ}
    (h : i < A.size) : A[i]! = A[i] := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?]
  simp [h]

namespace EnumCert

variable {gens : List ℕ} {E : List ℕ}

noncomputable def code (h : EnumCert gens E) (g : V₀ ≃ₗ[ZMod 2] V₀) : ℕ := by
  classical
  exact if hg : g ∈ codeSubgroup gens then Classical.choose (h.exists_code_mem hg) else 0

theorem code_mem (h : EnumCert gens E) {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) : h.code g ∈ E := by
  unfold code
  rw [dif_pos hg]
  exact (Classical.choose_spec (h.exists_code_mem hg)).1

theorem hasCode_code (h : EnumCert gens E) {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) (h.code g) := by
  unfold code
  rw [dif_pos hg]
  exact (Classical.choose_spec (h.exists_code_mem hg)).2

noncomputable def elem (h : EnumCert gens E) (c : ℕ) : V₀ ≃ₗ[ZMod 2] V₀ := by
  classical
  exact if hc : c ∈ E then Classical.choose (h.exists_mem hc) else 1

theorem elem_mem (h : EnumCert gens E) {c : ℕ} (hc : c ∈ E) :
    h.elem c ∈ codeSubgroup gens := by
  unfold elem
  rw [dif_pos hc]
  exact (Classical.choose_spec (h.exists_mem hc)).1

theorem hasCode_elem (h : EnumCert gens E) {c : ℕ} (hc : c ∈ E) :
    Code.HasCode (h.elem c : V₀ →ₗ[ZMod 2] V₀) c := by
  unfold elem
  rw [dif_pos hc]
  exact (Classical.choose_spec (h.exists_mem hc)).2

theorem code_elem (h : EnumCert gens E) {c : ℕ} (hc : c ∈ E) : h.code (h.elem c) = c := by
  apply Code.HasCode.code_eq (h.hasCode_code (h.elem_mem hc)) (h.hasCode_elem hc)
    (h.lt _ (h.code_mem (h.elem_mem hc))) (h.lt c hc)

theorem elem_code (h : EnumCert gens E) {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) : h.elem (h.code g) = g :=
  Code.HasCode.eq_of_equiv (h.hasCode_elem (h.code_mem hg)) (h.hasCode_code hg)

theorem eq_of_code_eq (h : EnumCert gens E) {g g' : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) (hg' : g' ∈ codeSubgroup gens)
    (hc : h.code g = h.code g') : g = g' := by
  rw [← h.elem_code hg, ← h.elem_code hg', hc]

theorem code_inj (h : EnumCert gens E) {g g' : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) (hg' : g' ∈ codeSubgroup gens) :
    h.code g = h.code g' ↔ g = g' := by
  constructor
  · exact h.eq_of_code_eq hg hg'
  · rintro rfl; rfl

theorem code_mul (h : EnumCert gens E) {g g' : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) (hg' : g' ∈ codeSubgroup gens) :
    h.code (g * g') = Code.mul (h.code g) (h.code g') := by
  apply Code.HasCode.code_eq (h.hasCode_code (Subgroup.mul_mem (H := codeSubgroup gens) hg hg'))
    ((h.hasCode_code hg).mul (h.hasCode_code hg'))
    (h.lt _ (h.code_mem (Subgroup.mul_mem (H := codeSubgroup gens) hg hg'))) (Code.mul_lt _ _)

theorem code_one (h : EnumCert gens E) : h.code 1 = Code.one := by
  apply Code.HasCode.code_eq (h.hasCode_code (Subgroup.one_mem _)) Code.hasCode_one
    (h.lt _ (h.code_mem (Subgroup.one_mem _))) Code.one_lt

theorem mul_mem_elems (h : EnumCert gens E) {a b : ℕ} (ha : a ∈ E) (hb : b ∈ E) :
    Code.mul a b ∈ E := by
  have hmem : h.elem a * h.elem b ∈ codeSubgroup gens :=
    Subgroup.mul_mem (H := codeSubgroup gens) (h.elem_mem ha) (h.elem_mem hb)
  have hcode := h.code_mem hmem
  rwa [h.code_mul (h.elem_mem ha) (h.elem_mem hb), h.code_elem ha, h.code_elem hb] at hcode

theorem code_mul_comm_one {a b : ℕ} (h : Code.mul a b = Code.one) :
    Code.mul b a = Code.one := by
  apply Code.eq_of_mat_eq (Code.mul_lt _ _) Code.one_lt
  rw [Code.mat_mul, Code.mat_one]
  apply mul_eq_one_comm.mp
  rw [← Code.mat_mul, h, Code.mat_one]

theorem code_inv_of_mul_eq_one (h : EnumCert gens E) {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) {d : ℕ} (hd : d ∈ E) (hmul : Code.mul (h.code g) d = Code.one) :
    h.code g⁻¹ = d := by
  obtain ⟨H, hHcode⟩ := exists_equiv_of_mul_eq_one (code_mul_comm_one hmul)
  have hGH : g * H = 1 := by
    apply Code.HasCode.eq_of_equiv ((h.hasCode_code hg).mul hHcode)
      (by rw [hmul]; exact Code.hasCode_one)
  have hHeq : H = g⁻¹ := eq_inv_of_mul_eq_one_right hGH
  have hHd : H = h.elem d := Code.HasCode.eq_of_equiv hHcode (h.hasCode_elem hd)
  rw [← hHeq, hHd, h.code_elem hd]

theorem code_one_mul_of_lt {b : ℕ} (hb : b < 2 ^ 36) : Code.mul Code.one b = b := by
  apply Code.eq_of_mat_eq (Code.mul_lt _ _) hb
  rw [Code.mat_mul, Code.mat_one, one_mul]

theorem gens_mem_elems (h : EnumCert gens E) (hlt : ∀ g ∈ gens, g < 2 ^ 36) :
    ∀ g ∈ gens, g ∈ E := by
  intro g hg
  have h1 : Code.mul Code.one g ∈ E := h.closed Code.one h.one_mem g hg
  rwa [code_one_mul_of_lt (hlt g hg)] at h1

noncomputable def subtypeEquivFilter (h : EnumCert gens E) (P : ℕ → Bool) :
    {g : codeSubgroup gens // P (h.code g) = true} ≃ {c // c ∈ E.filter P} where
  toFun g := ⟨h.code g, List.mem_filter.mpr ⟨h.code_mem g.1.2, g.2⟩⟩
  invFun c := ⟨⟨h.elem c.1, h.elem_mem (List.mem_filter.mp c.2).1⟩, by
    rw [h.code_elem (List.mem_filter.mp c.2).1]
    exact (List.mem_filter.mp c.2).2⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact h.elem_code g.1.2
  right_inv c := by
    apply Subtype.ext
    exact h.code_elem (List.mem_filter.mp c.2).1

theorem natCard_filter (h : EnumCert gens E) (P : ℕ → Bool) :
    Nat.card {g : codeSubgroup gens // P (h.code g) = true} = (E.filter P).length := by
  rw [Nat.card_congr (h.subtypeEquivFilter P)]
  rw [Nat.card_congr (List.Nodup.getEquiv (E.filter P) (h.nodup.filter P)).symm]
  simp

end EnumCert

theorem mem_KPGL_iff_of_enum {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    g ∈ KPGL ↔ c ∈ D.elems := by
  rw [KPGL, hK.mem_iff hg hc, Array.mem_toList_iff]

theorem mem_KPGL0_iff_of_enum {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    g ∈ KPGL0 ↔ c ∈ D.elems0 := by
  rw [KPGL0, hK0.mem_iff hg hc, Array.mem_toList_iff]

end CFSG.GF2Type.Smith1979W3.Cert690
