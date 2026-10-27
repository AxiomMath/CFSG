module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Mat3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Out
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.ComponentClassification CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
  CFSG.QuasithinUnique.Setup.Family CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

section Basic

abbrev tau32 : MulAut GL32 := CatalogueBGraphForm.glGraphAut 3 (ZMod 2)

theorem tau32_tau32 (g : GL32) : tau32 (tau32 g) = g :=
  Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose g

theorem coe_tau32 (g : GL32) : ((tau32 g : GL32) : Mat3) = ((g⁻¹ : GL32) : Mat3)ᵀ :=
  CatalogueBGraphForm.glGraphAut_matrix 3 (ZMod 2) g

theorem isInner_iff_conj {Y : Type} [Group Y] {α : MulAut Y} :
    IsInner α ↔ ∃ k : Y, α = MulAut.conj k := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, MulEquiv.ext fun y => by rw [hk, MulAut.conj_apply]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, fun y => MulAut.conj_apply k y⟩

theorem exists_outer_form {α : MulAut GL32} (hα : ¬ IsInner α) :
    ∃ s : GL32, α = MulAut.conj s * tau32 := by
  rcases aut_GL32_cases α with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact absurd (isInner_iff_conj.mpr ⟨s, hs⟩) hα
  · exact ⟨s, hs⟩

theorem not_isInner_conj_mul_tau32 (s : GL32) : ¬ IsInner (MulAut.conj s * tau32) := by
  intro h
  obtain ⟨k, hk⟩ := isInner_iff_conj.mp h
  apply glGraphAut_ne_conj (s⁻¹ * k)
  refine MulEquiv.ext fun y => ?_
  have h1 := congrArg (fun φ : MulAut GL32 => φ y) hk
  simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
  show tau32 y = (s⁻¹ * k) * y * (s⁻¹ * k)⁻¹
  calc tau32 y = s⁻¹ * (s * tau32 y * s⁻¹) * s := by group
    _ = s⁻¹ * (k * y * k⁻¹) * s := by rw [h1]
    _ = (s⁻¹ * k) * y * (s⁻¹ * k)⁻¹ := by group

theorem out_mul32 (α β : MulAut GL32) (hα : ¬ IsInner α) (hβ : ¬ IsInner β) : IsInner (α * β) := by
  obtain ⟨s, rfl⟩ := exists_outer_form hα
  obtain ⟨t, rfl⟩ := exists_outer_form hβ
  refine ⟨s * tau32 t, fun y => ?_⟩
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, tau32_tau32, _root_.mul_inv_rev]
  group

end Basic

section Fix

theorem card_autFix_tau32 : Nat.card ↥(autFix tau32) = 6 := by
  have e : ↥(autFix tau32) ≃ {A : Mat3 // A * Aᵀ = 1} :=
    { toFun := fun g => ⟨(g.1 : Mat3), by
        have h1 : tau32 g.1 = g.1 := g.2
        have h2 : ((g.1 : GL32) : Mat3) = ((g.1⁻¹ : GL32) : Mat3)ᵀ := by
          rw [← coe_tau32, h1]
        have h3 : ((g.1 : GL32) : Mat3)ᵀ = ((g.1⁻¹ : GL32) : Mat3) := by
          rw [h2, Matrix.transpose_transpose]
        rw [h3]
        exact Units.mul_inv g.1⟩
      invFun := fun A => ⟨⟨A.1, A.1ᵀ, A.2, mul_eq_one_comm.mp A.2⟩, by
        show tau32 _ = _
        refine Units.ext ?_
        rw [coe_tau32]
        exact Matrix.transpose_transpose _⟩
      left_inv := fun g => Subtype.ext (Units.ext rfl)
      right_inv := fun A => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_mat3_orthogonal

theorem mul_tau32_eq_one {s : GL32} (h : (MulAut.conj s * tau32) * (MulAut.conj s * tau32) = 1) :
    s * tau32 s = 1 := by
  have h1 : ∀ y : GL32, s * tau32 (s * tau32 y * s⁻¹) * s⁻¹ = y := fun y =>
    DFunLike.congr_fun h y
  have hc : s * tau32 s ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := h1 y
    simp only [map_mul, map_inv, tau32_tau32] at h2
    calc y * (s * tau32 s) = (s * tau32 s) * ((s * tau32 s)⁻¹ * y * (s * tau32 s)) := by group
      _ = (s * tau32 s) * ((s * tau32 s)⁻¹ * (s * ((tau32 s) * y * (tau32 s)⁻¹) * s⁻¹) *
          (s * tau32 s)) := by rw [h2]
      _ = (s * tau32 s) * y := by group
  rw [center_GL32] at hc
  exact Subgroup.mem_bot.mp hc

theorem transpose_eq_of_mul_tau32 {s : GL32} (h : s * tau32 s = 1) :
    ((s : GL32) : Mat3)ᵀ = (s : Mat3) := by
  have h1 : tau32 s = s⁻¹ := eq_inv_of_mul_eq_one_right h
  have hu : ((s⁻¹ : GL32) : Mat3)ᵀ = ((s⁻¹ : GL32) : Mat3) := by rw [← coe_tau32, h1]
  have h2 : ((s⁻¹ : GL32) : Mat3) * (s : Mat3)ᵀ = 1 := by
    have := congrArg Matrix.transpose (Units.mul_inv s)
    rw [Matrix.transpose_mul, hu, Matrix.transpose_one] at this
    exact this
  calc (s : Mat3)ᵀ = ((s : Mat3) * ((s⁻¹ : GL32) : Mat3)) * (s : Mat3)ᵀ := by
        rw [Units.mul_inv, Matrix.one_mul]
    _ = (s : Mat3) * (((s⁻¹ : GL32) : Mat3) * (s : Mat3)ᵀ) := by rw [Matrix.mul_assoc]
    _ = (s : Mat3) := by rw [h2, Matrix.mul_one]

theorem det_gl32 (g : GL32) : ((g : GL32) : Mat3).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

theorem exists_eq_mul_tau32_inv {s : GL32} (h : s * tau32 s = 1) :
    ∃ g : GL32, s = g * tau32 g⁻¹ := by
  obtain ⟨H, hdet, hH⟩ := mat3_symm_eq_mul_transpose (s : Mat3) (transpose_eq_of_mul_tau32 h)
    (det_gl32 s)
  refine ⟨Matrix.GeneralLinearGroup.mk'' H (by rw [hdet]; exact isUnit_one), Units.ext ?_⟩
  rw [Units.val_mul, coe_tau32, inv_inv]
  simpa using hH.symm

theorem card_autFix_outer {α : MulAut GL32} (hα : ¬ IsInner α) (h2 : α * α = 1) :
    Nat.card ↥(autFix α) = 6 := by
  obtain ⟨s, rfl⟩ := exists_outer_form hα
  obtain ⟨g, hg⟩ := exists_eq_mul_tau32_inv (mul_tau32_eq_one h2)
  rw [← card_autFix_tau32]
  have key : ∀ y : GL32, (MulAut.conj s * tau32) y = g * tau32 (g⁻¹ * y * g) * g⁻¹ := by
    intro y
    have e : (MulAut.conj s * tau32) y = s * tau32 y * s⁻¹ := rfl
    rw [e, hg]
    simp only [map_mul, map_inv]
    group
  have fixiff : ∀ k : GL32,
      (MulAut.conj s * tau32) k = k ↔ tau32 (g⁻¹ * k * g) = g⁻¹ * k * g := by
    intro k
    rw [key]
    constructor
    · intro h
      calc tau32 (g⁻¹ * k * g) = g⁻¹ * (g * tau32 (g⁻¹ * k * g) * g⁻¹) * g := by group
        _ = g⁻¹ * k * g := by rw [h]
    · intro h
      rw [h]
      group
  exact Nat.card_congr
    { toFun := fun k => ⟨g⁻¹ * k.1 * g, (fixiff k.1).mp (mem_autFix.mp k.2)⟩
      invFun := fun k => ⟨g * k.1 * g⁻¹, mem_autFix.mpr ((fixiff _).mpr (by
        have e : g⁻¹ * (g * k.1 * g⁻¹) * g = k.1 := by group
        rw [e]
        exact mem_autFix.mp k.2))⟩
      left_inv := fun k => Subtype.ext (by group)
      right_inv := fun k => Subtype.ext (by group) }

end Fix

section Sylow

@[expose] def w0 : GL32 := ⟨antiDiag, antiDiag, antiDiag_mul_self, antiDiag_mul_self⟩

theorem w0_mul_self : w0 * w0 = 1 := Units.ext antiDiag_mul_self

theorem w0_inv : w0⁻¹ = w0 := inv_eq_of_mul_eq_one_right w0_mul_self

theorem tau32_w0 : tau32 w0 = w0 :=
  Units.ext (by rw [coe_tau32]; exact antiDiag_transpose)

@[expose] def alpha0 : MulAut GL32 := MulAut.conj w0 * tau32

theorem alpha0_apply (y : GL32) : alpha0 y = w0 * tau32 y * w0⁻¹ := rfl

theorem alpha0_alpha0 : alpha0 * alpha0 = 1 := by
  refine MulEquiv.ext fun y => ?_
  show w0 * tau32 (w0 * tau32 y * w0⁻¹) * w0⁻¹ = y
  simp only [map_mul, tau32_tau32, tau32_w0, w0_inv]
  calc w0 * (w0 * y * w0) * w0 = (w0 * w0) * y * (w0 * w0) := by group
    _ = y := by rw [w0_mul_self]; group

theorem alpha0_mem_sylowT {t : GL32} (ht : t ∈ sylowT) : alpha0 t ∈ sylowT := by
  obtain ⟨a, b, c, rfl⟩ := ht
  refine ⟨c, a * c + b, a, Units.ext ?_⟩
  rw [alpha0_apply, Units.val_mul, Units.val_mul, coe_tau32]
  exact antiDiag_unitri a b c

theorem mem_smul_sylow_iff' {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g y : G) :
    y ∈ (g • P : Sylow p G) ↔ g⁻¹ * y * g ∈ P := by
  change y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem sylowT_card : Nat.card sylowT = 8 := by
  rw [Nat.card_congr tripleEquiv.symm]
  simp

theorem exists_conj_sylowT {P : Subgroup GL32} (hP : Nat.card P = 8) :
    ∃ h : GL32, ∀ y : GL32, y ∈ P ↔ h⁻¹ * y * h ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardG : Nat.card GL32 = 168 := card_GL_three_zmod_two
  have hidx : ∀ Q : Subgroup GL32, Nat.card Q = 8 → ¬ 2 ∣ Q.index := by
    intro Q hQ hd
    have h1 := Subgroup.card_mul_index Q
    rw [hQ, hcardG] at h1
    have h21 : Q.index = 21 := by omega
    rw [h21] at hd
    omega
  have hpg : ∀ Q : Subgroup GL32, Nat.card Q = 8 → IsPGroup 2 Q := fun Q hQ =>
    IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  let SP : Sylow 2 GL32 := (hpg P hP).toSylow (hidx P hP)
  let ST : Sylow 2 GL32 := (hpg sylowT sylowT_card).toSylow (hidx sylowT sylowT_card)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq GL32 ST SP
  refine ⟨h, fun y => ?_⟩
  have hy : y ∈ SP ↔ h⁻¹ * y * h ∈ ST := by rw [← hh]; exact mem_smul_sylow_iff' ST h y
  exact hy

theorem exists_outer_inv32 (P : Subgroup GL32) (hP : Nat.card P = 8) :
    ∃ α : MulAut GL32, ¬ IsInner α ∧ α * α = 1 ∧ ∀ y ∈ P, α y ∈ P := by
  obtain ⟨h, hh⟩ := exists_conj_sylowT hP
  set c : MulAut GL32 := MulAut.conj h with hcdef
  refine ⟨c * alpha0 * c⁻¹, ?_, ?_, ?_⟩
  · intro hin
    apply not_isInner_conj_mul_tau32 w0
    have e : MulAut.conj w0 * tau32 = c⁻¹ * (c * alpha0 * c⁻¹) * c := by
      show alpha0 = _
      group
    rw [e]
    have hc : IsInner c := ⟨h, fun y => MulAut.conj_apply h y⟩
    have hc' : IsInner c⁻¹ := ⟨h⁻¹, fun y => by rw [hcdef, MulAut.conj_inv_apply]; group⟩
    exact (hc'.mul hin).mul hc
  · calc c * alpha0 * c⁻¹ * (c * alpha0 * c⁻¹) = c * (alpha0 * alpha0) * c⁻¹ := by group
      _ = 1 := by rw [alpha0_alpha0]; group
  · intro y hy
    have ht : h⁻¹ * y * h ∈ sylowT := (hh y).mp hy
    have h1 := alpha0_mem_sylowT ht
    show h * alpha0 (h⁻¹ * y * h) * h⁻¹ ∈ P
    rw [hh]
    have e : h⁻¹ * (h * alpha0 (h⁻¹ * y * h) * h⁻¹) * h = alpha0 (h⁻¹ * y * h) := by group
    rw [e]
    exact h1

end Sylow

theorem l27Aut_gl32 : L27Aut GL32 where
  out_mul := out_mul32
  outer_fix_card := fun _ hα h2 => card_autFix_outer hα h2
  exists_outer_inv := exists_outer_inv32

section Transport

variable {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')

theorem congr_apply_eq (α : MulAut Y) (y' : Y') :
    (MulAut.congr e α) y' = e (α (e.symm y')) := rfl

theorem isInner_congr_of_isInner {α : MulAut Y} (h : IsInner α) : IsInner (MulAut.congr e α) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨e k, fun y' => ?_⟩
  rw [congr_apply_eq, hk, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem isInner_of_isInner_congr {α : MulAut Y} (h : IsInner (MulAut.congr e α)) : IsInner α := by
  obtain ⟨k', hk'⟩ := h
  refine ⟨e.symm k', fun y => ?_⟩
  have h1 := hk' (e y)
  rw [congr_apply_eq, MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem card_autFix_congr (α : MulAut Y) :
    Nat.card ↥(autFix (MulAut.congr e α)) = Nat.card ↥(autFix α) := by
  refine Nat.card_congr
    { toFun := fun k => ⟨e.symm k.1, ?_⟩
      invFun := fun k => ⟨e k.1, ?_⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  · have h1 := mem_autFix.mp k.2
    rw [congr_apply_eq] at h1
    apply e.injective
    rw [h1]
    simp
  · rw [mem_autFix, congr_apply_eq]
    have h1 := mem_autFix.mp k.2
    simp [h1]

end Transport

theorem L27Aut.of_mulEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (e : Y ≃* Y') (h : L27Aut Y') : L27Aut Y where
  out_mul := fun α β hα hβ => by
    apply isInner_of_isInner_congr e
    rw [map_mul]
    exact h.out_mul _ _ (fun hi => hα (isInner_of_isInner_congr e hi))
      (fun hi => hβ (isInner_of_isInner_congr e hi))
  outer_fix_card := fun α hα h2 => by
    rw [← card_autFix_congr e α]
    refine h.outer_fix_card _ (fun hi => hα (isInner_of_isInner_congr e hi)) ?_
    rw [← map_mul, h2, map_one]
  exists_outer_inv := fun P hP => by
    obtain ⟨α', hα', h2', hP'⟩ := h.exists_outer_inv (P.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, hP])
    refine ⟨(MulAut.congr e).symm α', ?_, ?_, ?_⟩
    · intro hi
      apply hα'
      have := isInner_congr_of_isInner e hi
      rwa [MulEquiv.apply_symm_apply] at this
    · apply (MulAut.congr e).injective
      rw [map_mul, MulEquiv.apply_symm_apply, map_one]
      exact h2'
    · intro y hy
      have h1 := hP' (e y) ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hpe⟩ := h1
      have h2 : ((MulAut.congr e).symm α') y = e.symm (α' (e y)) := by
        have := congrArg (fun φ : MulAut Y' => φ (e y)) ((MulAut.congr e).apply_symm_apply α').symm
        simp only [congr_apply_eq, MulEquiv.symm_apply_apply] at this
        apply e.injective
        rw [MulEquiv.apply_symm_apply, this]
      rw [h2, ← hpe]
      simpa using hp

theorem l27AutFact : ∀ (Y : Type) [Group Y] [Finite Y], Nonempty (Y ≃* PSL(2, ZMod 7)) → L27Aut Y := by
  intro Y _ _ ⟨e⟩
  obtain ⟨e₄⟩ := nonempty_GL_three_two_equiv_PSL_two_seven
  exact L27Aut.of_mulEquiv (e.trans e₄.symm) l27Aut_gl32

end CFSG.QuasithinUnique.DoubleA3
