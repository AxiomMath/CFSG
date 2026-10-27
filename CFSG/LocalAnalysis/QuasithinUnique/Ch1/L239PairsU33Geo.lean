module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonLines

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F]

@[expose] def ev (F : Type) [Field F] (j : Fin 3) : Fin 3 → F := Pi.single j 1

theorem ev_apply (j k : Fin 3) : ev F j k = if k = j then 1 else 0 := by
  simp [ev, Pi.single_apply]

theorem norm_ev (j : Fin 3) : ∑ k, (ev F j k) ^ 3 * ev F j k = 1 := by
  fin_cases j <;> simp [ev_apply]

variable (hF : Nat.card F = 9)

@[expose] noncomputable def Pt (j : Fin 3) : NonisoLine F :=
  lineOf (h := unitaryFieldData_of_card hF) (ev F j) (by
    rw [gramForm_one_apply]
    rw [norm_ev]
    exact one_ne_zero)

theorem Pt_val (j : Fin 3) : (Pt hF j).1 = F ∙ ev F j := rfl

variable {hF}

theorem orth_Pt {j k : Fin 3} (hjk : j ≠ k) : Orth (Pt hF j) (Pt hF k) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = j
  · subst hl
    simp [ev_apply, hjk]
  · simp [ev_apply, hl]

theorem Pt_injective : Function.Injective (Pt hF (F := F)) := by
  intro j k hjk
  by_contra hne
  exact (orth_Pt hne).ne hjk

variable (hF)

@[expose] noncomputable def ell0 : HexLine F :=
  ⟨{Pt hF 0, Pt hF 1, Pt hF 2}, by
    rw [Finset.card_eq_three]
    exact ⟨Pt hF 0, Pt hF 1, Pt hF 2, (orth_Pt (by decide)).ne, (orth_Pt (by decide)).ne,
      (orth_Pt (by decide)).ne, rfl⟩, by
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | exact orth_Pt (by decide)⟩

variable {hF}

theorem mem_ell0 {q : NonisoLine F} :
    q ∈ (ell0 hF).1 ↔ q = Pt hF 0 ∨ q = Pt hF 1 ∨ q = Pt hF 2 := by
  simp [ell0]

theorem Pt_mem_ell0 (j : Fin 3) : Pt hF j ∈ (ell0 hF).1 := by
  fin_cases j <;> simp [mem_ell0]

@[expose] def mkSU (hF : Nat.card F = 9) (M : Matrix (Fin 3) (Fin 3) F)
    (hu : (M.map (· ^ 3))ᵀ * M = 1) (hd : M.det = 1) : StatedSU 3 3 F :=
  ⟨⟨M, (M.map (· ^ 3))ᵀ, mul_eq_one_comm.mp hu, hu⟩, by
    rw [← SetLike.mem_coe, coe_statedSU hF]
    exact ⟨hu, hd⟩⟩

theorem eq_of_matrix {g g' : StatedSU 3 3 F}
    (h : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : g = g' :=
  Subtype.ext (Units.ext h)

theorem coe_mul_matrix (g g' : StatedSU 3 3 F) :
    (((g * g' : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem commutatorElement_eq_of_mul {H : Type*} [Group H] {x y z : H} (h : z * y = x * y * x⁻¹) :
    x * y * x⁻¹ * y⁻¹ = z := by
  rw [← h]
  group

variable (hF)

theorem lineAct_Pt_eq {g : StatedSU 3 3 F} {j k : Fin 3} {c : F} (hc : c ≠ 0)
    (h : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ev F j = c • ev F k) :
    lineAct hF g (Pt hF j) = Pt hF k := by
  apply Subtype.ext
  rw [lineAct_val, Pt_val, Pt_val, Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, h]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) _

variable {hF}

variable (hF)

@[expose] noncomputable def stab0 : Subgroup (StatedSU 3 3 F) where
  carrier := {g | lineActLin hF g (ell0 hF) = ell0 hF}
  one_mem' := lineActLin_one hF _
  mul_mem' := fun {a b} ha hb => by
    show lineActLin hF (a * b) _ = _
    rw [lineActLin_mul, show lineActLin hF b (ell0 hF) = ell0 hF from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    show lineActLin hF a⁻¹ _ = _
    have := congrArg (lineActLin hF a⁻¹) (show lineActLin hF a (ell0 hF) = ell0 hF from ha)
    rw [← lineActLin_mul, inv_mul_cancel, lineActLin_one] at this
    exact this.symm

variable {hF}

theorem mem_stab0_iff {g : StatedSU 3 3 F} :
    g ∈ stab0 hF ↔ lineActLin hF g (ell0 hF) = ell0 hF := Iff.rfl

theorem mem_stab0_of_forall {g : StatedSU 3 3 F}
    (h : ∀ j : Fin 3, ∃ k : Fin 3, lineAct hF g (Pt hF j) = Pt hF k) : g ∈ stab0 hF := by
  rw [mem_stab0_iff]
  apply Subtype.ext
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_lineActLin hF g (ell0 hF) x).1 hx
    rcases mem_ell0.1 ha with rfl | rfl | rfl
    · obtain ⟨k, hk⟩ := h 0
      rw [hk]
      exact Pt_mem_ell0 k
    · obtain ⟨k, hk⟩ := h 1
      rw [hk]
      exact Pt_mem_ell0 k
    · obtain ⟨k, hk⟩ := h 2
      rw [hk]
      exact Pt_mem_ell0 k
  · rw [(ell0 hF).2.1, (lineActLin hF g (ell0 hF)).2.1]

theorem exists_lineAct_Pt_of_mem_stab0 {g : StatedSU 3 3 F} (hg : g ∈ stab0 hF) (j : Fin 3) :
    ∃ k : Fin 3, lineAct hF g (Pt hF j) = Pt hF k := by
  have h1 : lineAct hF g (Pt hF j) ∈ (lineActLin hF g (ell0 hF)).1 :=
    (lineAct_mem_lineActLin hF g (ell0 hF) _).2 (Pt_mem_ell0 j)
  rw [mem_stab0_iff.1 hg] at h1
  rcases mem_ell0.1 h1 with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem mem_stab0_of_monomial {g : StatedSU 3 3 F}
    (h : ∀ j : Fin 3, ∃ k : Fin 3, ∃ c : F, c ≠ 0 ∧
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ev F j = c • ev F k) :
    g ∈ stab0 hF := by
  refine mem_stab0_of_forall fun j => ?_
  obtain ⟨k, c, hc, hk⟩ := h j
  exact ⟨k, lineAct_Pt_eq hF hc hk⟩

end CFSG.QuasithinUnique.Vol2Native.L239.U33
