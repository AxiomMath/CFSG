module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentBasic
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

namespace AnisoPair

variable (P : AnisoPair Q)

noncomputable def rot : V ≃ₗ[ZMod 2] V := reflect Q P.a * reflect Q P.b

theorem rot_mem : P.rot ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _)

theorem reflect_a_apply (v : V) : reflect Q P.a v = v + polar Q v P.a • P.a :=
  reflect_apply_of_map_eq_one P.Q_a v

theorem reflect_b_apply (v : V) : reflect Q P.b v = v + polar Q v P.b • P.b :=
  reflect_apply_of_map_eq_one P.Q_b v

theorem rot_apply (v : V) :
    P.rot v = v + polar Q v P.b • (P.a + P.b) + polar Q v P.a • P.a := by
  rw [rot, LinearEquiv.mul_apply, P.reflect_b_apply, P.reflect_a_apply, polar_add_left,
    polar_smul_left_eq, P.polar_ba]
  module

theorem rot_apply_of_orth {v : V} (ha : polar Q P.a v = 0) (hb : polar Q P.b v = 0) :
    P.rot v = v := by
  rw [P.rot_apply, polar_comm Q v P.b, polar_comm Q v P.a, ha, hb]
  simp

theorem rot_a : P.rot P.a = P.b := by
  rw [P.rot_apply, P.polar_aa, P.polar_ab]
  simp only [one_smul, zero_smul, add_zero]
  rw [← add_assoc, add_self_eq_zero', zero_add]

theorem rot_a_ne : P.rot P.a ≠ P.a := by
  rw [P.rot_a]
  exact P.a_ne_b.symm

theorem reflect_braid_left :
    reflect Q P.a * reflect Q P.b * reflect Q P.a = reflect Q (P.a + P.b) := by
  have h := reflect_conj (reflect_mem_orthogonalGroup Q P.a) P.b
  rw [reflect_inv, P.reflect_a_apply, P.polar_ba, one_smul, add_comm] at h
  exact h

theorem reflect_braid_right :
    reflect Q P.b * reflect Q P.a * reflect Q P.b = reflect Q (P.a + P.b) := by
  have h := reflect_conj (reflect_mem_orthogonalGroup Q P.b) P.a
  rw [reflect_inv, P.reflect_b_apply, P.polar_ab, one_smul] at h
  exact h

theorem rot_pow_three : P.rot ^ 3 = 1 := by
  calc P.rot ^ 3 = (reflect Q P.a * reflect Q P.b * reflect Q P.a) *
        (reflect Q P.b * reflect Q P.a * reflect Q P.b) := by
        simp only [rot, pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [P.reflect_braid_left, P.reflect_braid_right, reflect_mul_self]

def shift : AnisoPair Q where
  a := P.b
  b := P.a + P.b
  Q_a := P.Q_b
  Q_b := by rw [QuadraticMap.map_add Q, P.Q_a, P.Q_b, P.polar_ab]; decide
  polar_ab := by rw [polar_add_right, P.polar_ba, P.polar_bb]; simp

theorem shift_rot : P.shift.rot = P.rot := by
  have h3 := P.rot_pow_three
  have hAA : ∀ y : V ≃ₗ[ZMod 2] V, reflect Q P.a * (reflect Q P.a * y) = y := fun y => by
    rw [← mul_assoc, reflect_mul_self, one_mul]
  have hBB : reflect Q P.b * reflect Q P.b = 1 := reflect_mul_self Q P.b
  have h6 : reflect Q P.a * reflect Q P.b * reflect Q P.a * reflect Q P.b * reflect Q P.a *
      reflect Q P.b = 1 := by
    simpa [rot, pow_succ, mul_assoc] using h3
  rw [shift, rot, ← P.reflect_braid_left]
  show reflect Q P.b * (reflect Q P.a * reflect Q P.b * reflect Q P.a) =
    reflect Q P.a * reflect Q P.b
  calc reflect Q P.b * (reflect Q P.a * reflect Q P.b * reflect Q P.a)
      = reflect Q P.a * (reflect Q P.a * reflect Q P.b * reflect Q P.a * reflect Q P.b *
          reflect Q P.a * reflect Q P.b) * reflect Q P.b := by
        simp only [mul_assoc, hAA, hBB, mul_one]
    _ = reflect Q P.a * reflect Q P.b := by rw [h6, mul_one]

theorem conj_rot {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    x * P.rot * x⁻¹ = reflect Q (x P.a) * reflect Q (x P.b) := by
  rw [rot]
  calc x * (reflect Q P.a * reflect Q P.b) * x⁻¹
      = (x * reflect Q P.a * x⁻¹) * (x * reflect Q P.b * x⁻¹) := by group
    _ = _ := by rw [reflect_conj hx, reflect_conj hx]

theorem rot_comm_of_cyc {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ha : x P.a = P.b) (hb : x P.b = P.a + P.b) : x * P.rot = P.rot * x := by
  have h := P.conj_rot hx
  rw [ha, hb] at h
  have h2 : x * P.rot * x⁻¹ = P.rot := by
    rw [h]
    exact P.shift_rot
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem rot_comm_of_fix {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ha : x P.a = P.a) (hb : x P.b = P.b) : x * P.rot = P.rot * x := by
  have h := P.conj_rot hx
  rw [ha, hb] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end AnisoPair

theorem finite_linearEquiv [FiniteDimensional (ZMod 2) V] : Finite (V ≃ₗ[ZMod 2] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective

def stabSubgroup (v : V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g v = v}
  one_mem' := rfl
  mul_mem' := fun {g h} (hg : g v = v) (hh : h v = v) => by
    change (g * h) v = v
    rw [LinearEquiv.mul_apply, hh, hg]
  inv_mem' := fun {g} (hg : g v = v) => by
    change g⁻¹ v = v
    calc g⁻¹ v = g⁻¹ (g v) := by rw [hg]
      _ = v := LinearEquiv.inv_apply_apply' g v

def rotSubgroup (Ps : List (AnisoPair Q)) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  Subgroup.closure {g | ∃ P ∈ Ps, g = P.rot}

theorem rot_commute_of_orth {P P' : AnisoPair Q} (h : P.Orth P') : Commute P.rot P'.rot := by
  have hc : ∀ {u w : V}, polar Q u w = 0 → Commute (reflect Q u) (reflect Q w) := by
    intro u w huw
    have h1 := reflect_conj (reflect_mem_orthogonalGroup Q u) w
    rw [reflect_apply_of_polar_eq_zero huw] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  rw [AnisoPair.rot, AnisoPair.rot]
  have h1 : Commute (reflect Q P.a) (reflect Q P'.a * reflect Q P'.b) :=
    (hc h.aa).mul_right (hc h.ab)
  have h2 : Commute (reflect Q P.b) (reflect Q P'.a * reflect Q P'.b) :=
    (hc h.ba).mul_right (hc h.bb)
  exact h1.mul_left h2

theorem rotSubgroup_commute {Ps : List (AnisoPair Q)} (hpw : Ps.Pairwise AnisoPair.Orth) :
    ∀ g ∈ rotSubgroup Ps, ∀ h ∈ rotSubgroup Ps, g * h = h * g := by
  have hrel : Ps.Pairwise (fun P P' => Commute P.rot P'.rot) :=
    hpw.imp fun {P P'} h => rot_commute_of_orth h
  have : Std.Symm (fun P P' : AnisoPair Q => Commute P.rot P'.rot) :=
    ⟨fun _ _ h => h.symm⟩
  have hall := List.Pairwise.forall_of_forall
    (R := fun P P' : AnisoPair Q => Commute P.rot P'.rot) (fun P _ => Commute.refl _) hrel
  have hS : ({g | ∃ P ∈ Ps, g = P.rot} : Set (V ≃ₗ[ZMod 2] V)).Pairwise Commute := by
    rintro _ ⟨P, hP, rfl⟩ _ ⟨P', hP', rfl⟩ _
    exact hall hP hP'
  have : IsMulCommutative (rotSubgroup Ps) := Subgroup.isMulCommutative_closure hS
  intro g hg h hh
  exact congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : rotSubgroup Ps) ⟨h, hh⟩)

theorem rotSubgroup_pow_three {Ps : List (AnisoPair Q)} (hpw : Ps.Pairwise AnisoPair.Orth) :
    ∀ g ∈ rotSubgroup Ps, g ^ 3 = 1 := by
  have hcomm := rotSubgroup_commute hpw
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨P, -, rfl⟩ := hy
    exact P.rot_pow_three
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := hcomm a ha b hb
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem rotSubgroup_le_orthogonalGroup (Ps : List (AnisoPair Q)) :
    rotSubgroup Ps ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [rotSubgroup, Subgroup.closure_le]
  rintro _ ⟨P, -, rfl⟩
  exact P.rot_mem

theorem rotSubgroup_le_stab {Ps : List (AnisoPair Q)} {v : V}
    (hv : ∀ P ∈ Ps, polar Q P.a v = 0 ∧ polar Q P.b v = 0) : rotSubgroup Ps ≤ stabSubgroup v := by
  rw [rotSubgroup, Subgroup.closure_le]
  rintro _ ⟨P, hP, rfl⟩
  exact P.rot_apply_of_orth (hv P hP).1 (hv P hP).2

theorem exists_card_rotSubgroup [FiniteDimensional (ZMod 2) V] :
    ∀ Ps : List (AnisoPair Q), Ps.Pairwise AnisoPair.Orth →
      ∃ t : ℕ, Ps.length ≤ t ∧ Nat.card (rotSubgroup Ps) = 3 ^ t := by
  have := finite_linearEquiv (V := V)
  intro Ps
  induction Ps with
  | nil =>
    intro _
    refine ⟨0, le_rfl, ?_⟩
    have : rotSubgroup ([] : List (AnisoPair Q)) = ⊥ := by
      rw [rotSubgroup]
      simp
    rw [this]
    simp
  | cons P Ps ih =>
    intro hpw
    rw [List.pairwise_cons] at hpw
    obtain ⟨hPorth, hpw'⟩ := hpw
    obtain ⟨t, hlen, hcard⟩ := ih hpw'
    have hle : rotSubgroup Ps ≤ rotSubgroup (P :: Ps) := by
      apply Subgroup.closure_mono
      rintro _ ⟨R, hR, rfl⟩
      exact ⟨R, List.mem_cons_of_mem _ hR, rfl⟩
    have hmem : P.rot ∈ rotSubgroup (P :: Ps) :=
      Subgroup.subset_closure ⟨P, List.mem_cons_self, rfl⟩
    have hnot : P.rot ∉ rotSubgroup Ps := by
      intro h
      have hstab : rotSubgroup Ps ≤ stabSubgroup P.a := by
        apply rotSubgroup_le_stab
        intro R hR
        have := hPorth R hR
        exact ⟨by rw [polar_comm]; exact this.aa, by rw [polar_comm]; exact this.ab⟩
      exact P.rot_a_ne (hstab h)
    have hlt : rotSubgroup Ps < rotSubgroup (P :: Ps) :=
      lt_of_le_of_ne hle (fun h => hnot (h ▸ hmem))
    have hY3 : IsPGroup 3 (rotSubgroup (P :: Ps)) := by
      intro y
      refine ⟨1, ?_⟩
      apply Subtype.ext
      rw [pow_one]
      exact rotSubgroup_pow_three (List.pairwise_cons.2 ⟨hPorth, hpw'⟩) y y.2
    obtain ⟨t', ht'⟩ := IsPGroup.iff_card.1 hY3
    have hcl := Subgroup.card_lt_of_lt hlt
    rw [hcard, ht'] at hcl
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hcl
    refine ⟨t', ?_, ht'⟩
    simp only [List.length_cons]
    omega

theorem exists_rotSubgroup [FiniteDimensional (ZMod 2) V] (Ps : List (AnisoPair Q))
    (hpw : Ps.Pairwise AnisoPair.Orth) {x : V ≃ₗ[ZMod 2] V}
    (hx : ∀ P ∈ Ps, x * P.rot = P.rot * x) :
    ∃ Y : Subgroup (V ≃ₗ[ZMod 2] V), Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      Y ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) ∧ (∀ g ∈ Y, g ^ 3 = 1) ∧
      (∀ g ∈ Y, ∀ h ∈ Y, g * h = h * g) ∧ ∃ t : ℕ, Ps.length ≤ t ∧ Nat.card Y = 3 ^ t := by
  refine ⟨rotSubgroup Ps, rotSubgroup_le_orthogonalGroup Ps, ?_, rotSubgroup_pow_three hpw,
    rotSubgroup_commute hpw, exists_card_rotSubgroup Ps hpw⟩
  rw [rotSubgroup, Subgroup.closure_le]
  rintro _ ⟨P, hP, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hx P hP

end CFSG.AGLEmbedding.OmegaMinusCent
