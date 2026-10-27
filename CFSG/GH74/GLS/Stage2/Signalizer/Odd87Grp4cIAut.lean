module

public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.GH74.GLS.Bg.TwoGroups
open scoped Pointwise

namespace Aut34

section Basic

variable {F : Type} [Field F]

theorem mul_a (x y : UT3 F) : (x * y).a = x.a + y.a := by rw [UT3.mul_def]

theorem mul_b (x y : UT3 F) : (x * y).b = x.b + y.b := by rw [UT3.mul_def]

theorem mul_c (x y : UT3 F) : (x * y).c = x.c + y.c + x.a * y.b := by rw [UT3.mul_def]

theorem comm_iff (x y : UT3 F) : x * y = y * x ↔ x.a * y.b = y.a * x.b := by
  constructor
  · intro h
    have := congrArg UT3.c h
    rw [mul_c, mul_c] at this
    linear_combination this
  · intro h
    refine UT3.ext ?_ ?_ ?_
    · rw [mul_a, mul_a, add_comm]
    · rw [mul_b, mul_b, add_comm]
    · rw [mul_c, mul_c]; linear_combination h

theorem decomp (x : UT3 F) :
    x = (⟨x.a, 0, 0⟩ : UT3 F) * ⟨0, x.b, 0⟩ * ⟨0, 0, x.c - x.a * x.b⟩ := by
  refine UT3.ext ?_ ?_ ?_
  · simp only [mul_a]; ring
  · simp only [mul_b]; ring
  · simp only [mul_c, mul_a]; ring

theorem comm_map (φ : MulAut (UT3 F)) (x v : UT3 F) :
    φ x * φ v = φ v * φ x ↔ x * v = v * x := by
  rw [← map_mul, ← map_mul, φ.injective.eq_iff]

def M1 (F : Type) [Field F] : Set (UT3 F) := {x | x.b = 0}

def M2 (F : Type) [Field F] : Set (UT3 F) := {x | x.a = 0}

def Aut0 (F : Type) [Field F] : Subgroup (MulAut (UT3 F)) :=
  MulAction.stabilizer (MulAut (UT3 F)) (M1 F)

theorem pres_b_of_mem {φ : MulAut (UT3 F)} (h : φ ∈ Aut0 F) :
    ∀ x, (φ x).b = 0 ↔ x.b = 0 := by
  intro x
  have h' : φ • M1 F = M1 F := MulAction.mem_stabilizer_iff.mp h
  have hx : φ x ∈ φ • M1 F ↔ φ x ∈ M1 F := by rw [h']
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
  simpa [M1, MulAut.smul_def] using hx.symm

structure FixesAxes (φ : MulAut (UT3 F)) : Prop where
  b : ∀ x, (φ x).b = 0 ↔ x.b = 0
  a : ∀ x, (φ x).a = 0 ↔ x.a = 0

def axis1 (φ : MulAut (UT3 F)) (a : F) : F := (φ ⟨a, 0, 0⟩).a

def axis2 (φ : MulAut (UT3 F)) (b : F) : F := (φ ⟨0, b, 0⟩).b

theorem coord_eq_axis {φ : MulAut (UT3 F)} (h : FixesAxes φ) (x : UT3 F) :
    (φ x).a = axis1 φ x.a ∧ (φ x).b = axis2 φ x.b := by
  have hx : φ x = φ ⟨x.a, 0, 0⟩ * φ ⟨0, x.b, 0⟩ * φ ⟨0, 0, x.c - x.a * x.b⟩ := by
    rw [← map_mul, ← map_mul, ← decomp x]
  have e1 : (φ ⟨0, x.b, 0⟩).a = 0 := (h.a _).2 rfl
  have e2 : (φ ⟨0, 0, x.c - x.a * x.b⟩).a = 0 := (h.a _).2 rfl
  have e3 : (φ ⟨x.a, 0, 0⟩).b = 0 := (h.b _).2 rfl
  have e4 : (φ ⟨0, 0, x.c - x.a * x.b⟩).b = 0 := (h.b _).2 rfl
  constructor
  · rw [hx, mul_a, mul_a, e1, e2, add_zero, add_zero]; rfl
  · rw [hx, mul_b, mul_b, e3, e4, zero_add, add_zero]; rfl

theorem axis1_mul {φ : MulAut (UT3 F)} (h : FixesAxes φ) (ψ : MulAut (UT3 F)) (a : F) :
    axis1 (φ * ψ) a = axis1 φ (axis1 ψ a) :=
  (coord_eq_axis h (ψ ⟨a, 0, 0⟩)).1

theorem axis2_mul {φ : MulAut (UT3 F)} (h : FixesAxes φ) (ψ : MulAut (UT3 F)) (b : F) :
    axis2 (φ * ψ) b = axis2 φ (axis2 ψ b) :=
  (coord_eq_axis h (ψ ⟨0, b, 0⟩)).2

theorem axis1_one (a : F) : axis1 (1 : MulAut (UT3 F)) a = a := by simp [axis1]

theorem axis2_one (b : F) : axis2 (1 : MulAut (UT3 F)) b = b := by simp [axis2]

def permHom (f : MulAut (UT3 F) → F → F)
    (hmul : ∀ φ ∈ Aut0 F, ∀ ψ a, f (φ * ψ) a = f φ (f ψ a)) (hone : ∀ a, f 1 a = a) :
    ↥(Aut0 F) →* Equiv.Perm F :=
  MonoidHom.mk'
    (fun φ =>
      { toFun := f (φ : MulAut (UT3 F))
        invFun := f ((φ⁻¹ : ↥(Aut0 F)) : MulAut (UT3 F))
        left_inv := fun a => by
          show f _ (f _ a) = a
          rw [← hmul _ (φ⁻¹).2, ← Subgroup.coe_mul, inv_mul_cancel]
          exact hone a
        right_inv := fun a => by
          show f _ (f _ a) = a
          rw [← hmul _ φ.2, ← Subgroup.coe_mul, mul_inv_cancel]
          exact hone a })
    (fun φ ψ => by
      ext a
      exact hmul _ φ.2 ψ a)

end Basic

section Char2

variable {F : Type} [Field F] [CharP F 2]

theorem add_self' (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem mul_self_eq (x : UT3 F) : x * x = ⟨0, 0, x.a * x.b⟩ := by
  refine UT3.ext ?_ ?_ ?_
  · rw [mul_a, add_self']
  · rw [mul_b, add_self']
  · rw [mul_c, add_self', zero_add]

theorem mul_self_eq_one {x : UT3 F} (h : x * x = 1) : x.a * x.b = 0 := by
  have := congrArg UT3.c h
  rwa [mul_self_eq] at this

theorem u_sq : (⟨1, 0, 0⟩ : UT3 F) * ⟨1, 0, 0⟩ = 1 := by
  rw [mul_self_eq]; simp [UT3.one_def]

theorem w_sq : (⟨0, 1, 0⟩ : UT3 F) * ⟨0, 1, 0⟩ = 1 := by
  rw [mul_self_eq]; simp [UT3.one_def]

theorem comm_class_aux (z : UT3 F) (hz : z * z = 1) (hnc : ∃ y : UT3 F, z * y ≠ y * z) :
    (∀ x : UT3 F, x * z = z * x ↔ x.b = 0) ∨ (∀ x : UT3 F, x * z = z * x ↔ x.a = 0) := by
  have hab := mul_self_eq_one hz
  have hne : z.a ≠ 0 ∨ z.b ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    obtain ⟨y, hy⟩ := hnc
    apply hy
    rw [comm_iff, h.1, h.2]; ring
  rcases hne with h | h
  · have hb : z.b = 0 := (mul_eq_zero.mp hab).resolve_left h
    left
    intro x
    rw [comm_iff, hb]
    constructor
    · intro hx
      have : z.a * x.b = 0 := by linear_combination -hx
      exact (mul_eq_zero.mp this).resolve_left h
    · intro hx; rw [hx]; ring
  · have ha : z.a = 0 := by
      by_contra h'
      exact h ((mul_eq_zero.mp hab).resolve_left h')
    right
    intro x
    rw [comm_iff, ha]
    constructor
    · intro hx
      have : x.a * z.b = 0 := by linear_combination hx
      exact (mul_eq_zero.mp this).resolve_right h
    · intro hx; rw [hx]; ring

theorem comm_class (φ : MulAut (UT3 F)) (u w : UT3 F) (hu : u * u = 1) (huw : u * w ≠ w * u) :
    (∀ x, φ x * u = u * φ x ↔ x.b = 0) ∨ (∀ x, φ x * u = u * φ x ↔ x.a = 0) := by
  have hv : φ (φ⁻¹ u) = u := MulAut.apply_inv_self _ φ u
  have hvv : φ⁻¹ u * φ⁻¹ u = 1 := by
    apply φ.injective
    rw [map_mul, hv, hu, map_one]
  have hnc : ∃ y : UT3 F, φ⁻¹ u * y ≠ y * φ⁻¹ u := by
    refine ⟨φ⁻¹ w, fun h => huw ?_⟩
    have := (comm_map φ (φ⁻¹ u) (φ⁻¹ w)).2 h
    rwa [MulAut.apply_inv_self, MulAut.apply_inv_self] at this
  have e : ∀ x : UT3 F, φ x * u = u * φ x ↔ x * φ⁻¹ u = φ⁻¹ u * x := by
    intro x
    rw [← comm_map φ x (φ⁻¹ u), hv]
  rcases comm_class_aux _ hvv hnc with h | h
  · exact Or.inl fun x => (e x).trans (h x)
  · exact Or.inr fun x => (e x).trans (h x)

theorem pres_b_or (φ : MulAut (UT3 F)) :
    (∀ x, (φ x).b = 0 ↔ x.b = 0) ∨ (∀ x, (φ x).b = 0 ↔ x.a = 0) := by
  have e : ∀ x : UT3 F, φ x * ⟨1, 0, 0⟩ = ⟨1, 0, 0⟩ * φ x ↔ (φ x).b = 0 := by
    intro x; rw [comm_iff]; simp [eq_comm]
  have h := comm_class φ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ u_sq (by rw [Ne, comm_iff]; simp)
  simpa only [e] using h

theorem pres_a_or (φ : MulAut (UT3 F)) :
    (∀ x, (φ x).a = 0 ↔ x.b = 0) ∨ (∀ x, (φ x).a = 0 ↔ x.a = 0) := by
  have e : ∀ x : UT3 F, φ x * ⟨0, 1, 0⟩ = ⟨0, 1, 0⟩ * φ x ↔ (φ x).a = 0 := by
    intro x; rw [comm_iff]; simp [eq_comm]
  have h := comm_class φ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ w_sq (by rw [Ne, comm_iff]; simp)
  simpa only [e] using h

theorem pres_a_of_pres_b (φ : MulAut (UT3 F)) (h1 : ∀ x, (φ x).b = 0 ↔ x.b = 0) :
    ∀ x, (φ x).a = 0 ↔ x.a = 0 := by
  rcases pres_a_or φ with h2 | h2
  · exfalso
    have hb : (φ ⟨0, 1, 0⟩).b ≠ 0 := fun h => one_ne_zero ((h1 _).1 h)
    have ha : (φ ⟨0, 1, 0⟩).a ≠ 0 := fun h => one_ne_zero ((h2 _).1 h)
    have : (φ ⟨0, 1, 0⟩).a * (φ ⟨0, 1, 0⟩).b = 0 := by
      apply mul_self_eq_one
      rw [← map_mul, w_sq, map_one]
    exact mul_ne_zero ha hb this
  · exact h2

theorem fixesAxes_of_mem {φ : MulAut (UT3 F)} (h : φ ∈ Aut0 F) : FixesAxes φ :=
  ⟨pres_b_of_mem h, pres_a_of_pres_b φ (pres_b_of_mem h)⟩

theorem orbit_subset : MulAction.orbit (MulAut (UT3 F)) (M1 F) ⊆ {M1 F, M2 F} := by
  rintro _ ⟨φ, rfl⟩
  rcases pres_b_or φ⁻¹ with h | h
  · left
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simpa [M1, MulAut.smul_def] using h y
  · right
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simpa [M1, M2, MulAut.smul_def] using h y

theorem index_Aut0_le : (Aut0 F).index ≤ 2 := by
  rw [Aut0, MulAction.index_stabilizer]
  calc (MulAction.orbit (MulAut (UT3 F)) (M1 F)).ncard
      ≤ ({M1 F, M2 F} : Set (Set (UT3 F))).ncard :=
        Set.ncard_le_ncard orbit_subset (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

theorem sq_of_diag {ψ : MulAut (UT3 F)} (h : ∀ x, (ψ x).a = x.a ∧ (ψ x).b = x.b) :
    ψ * ψ = 1 := by
  have hZ : ∀ c : F, ψ ⟨0, 0, c⟩ = ⟨0, 0, c⟩ := by
    intro c
    have h1 : (⟨1, c, 0⟩ : UT3 F) * ⟨1, c, 0⟩ = ⟨0, 0, c⟩ := by
      rw [mul_self_eq]; simp
    have h2 : ψ ⟨1, c, 0⟩ = ⟨1, c, (ψ ⟨1, c, 0⟩).c⟩ := UT3.ext (h _).1 (h _).2 rfl
    calc ψ ⟨0, 0, c⟩ = ψ (⟨1, c, 0⟩ * ⟨1, c, 0⟩) := by rw [h1]
      _ = ⟨0, 0, c⟩ := by rw [map_mul, h2, mul_self_eq]; simp
  have hform : ∀ x : UT3 F, ψ x = ⟨x.a, x.b, (ψ ⟨x.a, x.b, 0⟩).c + x.c⟩ := by
    intro x
    have hx : (⟨x.a, x.b, 0⟩ : UT3 F) * ⟨0, 0, x.c⟩ = x := by
      refine UT3.ext ?_ ?_ ?_ <;> simp [mul_a, mul_b, mul_c]
    have h2 : ψ ⟨x.a, x.b, 0⟩ = ⟨x.a, x.b, (ψ ⟨x.a, x.b, 0⟩).c⟩ := UT3.ext (h _).1 (h _).2 rfl
    calc ψ x = ψ (⟨x.a, x.b, 0⟩ * ⟨0, 0, x.c⟩) := by rw [hx]
      _ = _ := by
        rw [map_mul, hZ, h2]
        refine UT3.ext ?_ ?_ ?_ <;> simp [mul_a, mul_b, mul_c]
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.one_apply, hform (ψ x), (h x).1, (h x).2,
    congrArg UT3.c (hform x)]
  refine UT3.ext rfl rfl ?_
  show _ + (_ + x.c) = x.c
  rw [← add_assoc, add_self', zero_add]

def axisPerm1 (F : Type) [Field F] [CharP F 2] : ↥(Aut0 F) →* Equiv.Perm F :=
  permHom axis1 (fun _ hφ => axis1_mul (fixesAxes_of_mem hφ)) axis1_one

def axisPerm2 (F : Type) [Field F] [CharP F 2] : ↥(Aut0 F) →* Equiv.Perm F :=
  permHom axis2 (fun _ hφ => axis2_mul (fixesAxes_of_mem hφ)) axis2_one

theorem ker_isPGroup : IsPGroup 2 ((axisPerm1 F).prod (axisPerm2 F)).ker := by
  intro g
  refine ⟨1, ?_⟩
  have hg := g.2
  rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hg
  have h1 : ∀ a, axis1 ((g : ↥(Aut0 F)) : MulAut (UT3 F)) a = a := fun a =>
    congrArg (fun p : Equiv.Perm F => p a) hg.1
  have h2 : ∀ b, axis2 ((g : ↥(Aut0 F)) : MulAut (UT3 F)) b = b := fun b =>
    congrArg (fun p : Equiv.Perm F => p b) hg.2
  have hd : ∀ x, (((g : ↥(Aut0 F)) : MulAut (UT3 F)) x).a = x.a ∧
      (((g : ↥(Aut0 F)) : MulAut (UT3 F)) x).b = x.b := fun x => by
    have hx := coord_eq_axis (fixesAxes_of_mem (g : ↥(Aut0 F)).2) x
    rw [hx.1, hx.2, h1, h2]
    exact ⟨rfl, rfl⟩
  rw [pow_one, pow_two]
  apply Subtype.ext
  apply Subtype.ext
  exact sq_of_diag hd

theorem natCard_dvd (F : Type) [Field F] [CharP F 2] [Finite F] :
    ∃ k : ℕ, Nat.card (MulAut (UT3 F)) ∣ 2 ^ (k + 1) * ((Nat.card F).factorial) ^ 2 := by
  have hfin : Finite (UT3 F) := Finite.of_injective (fun x : UT3 F => (x.a, x.b, x.c)) (by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact UT3.ext h.1 h.2.1 h.2.2)
  have hfinA : Finite (MulAut (UT3 F)) :=
    Finite.of_injective (fun φ : MulAut (UT3 F) => (φ : UT3 F → UT3 F)) DFunLike.coe_injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (ker_isPGroup (F := F))
  have h1 : (Aut0 F).index * Nat.card (Aut0 F) = Nat.card (MulAut (UT3 F)) :=
    Subgroup.index_mul_card _
  have h2 : ((axisPerm1 F).prod (axisPerm2 F)).ker.index *
      Nat.card ((axisPerm1 F).prod (axisPerm2 F)).ker = Nat.card (Aut0 F) :=
    Subgroup.index_mul_card _
  have h3 : ((axisPerm1 F).prod (axisPerm2 F)).ker.index =
      Nat.card ((axisPerm1 F).prod (axisPerm2 F)).range := Subgroup.index_ker _
  have h4 : Nat.card ((axisPerm1 F).prod (axisPerm2 F)).range ∣
      Nat.card (Equiv.Perm F × Equiv.Perm F) := Subgroup.card_subgroup_dvd_card _
  have h5 : Nat.card (Equiv.Perm F × Equiv.Perm F) = ((Nat.card F).factorial) ^ 2 := by
    rw [Nat.card_prod, Nat.card_perm]; ring
  have h6 : (Aut0 F).index ∣ 2 := by
    have hpos : 0 < (Aut0 F).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hle := index_Aut0_le (F := F)
    interval_cases h : (Aut0 F).index
    · exact one_dvd _
    · exact dvd_rfl
  refine ⟨k, ?_⟩
  rw [← h1, ← h2, h3, hk]
  rw [h5] at h4
  refine (Nat.mul_dvd_mul h6 (Nat.mul_dvd_mul h4 dvd_rfl)).trans (dvd_of_eq ?_)
  ring

end Char2

theorem oddPart_dvd_nine {n : ℕ} (hn : n ≠ 0) (k : ℕ) (h : n ∣ 2 ^ k * 9) :
    CFSG.GH74.GLS.Stage2.Signalizer.oddPart n ∣ 9 := by
  have hcop : Nat.Coprime 2 (n / 2 ^ n.factorization 2) := Nat.coprime_ordCompl Nat.prime_two hn
  have hdvd : n / 2 ^ n.factorization 2 ∣ n := Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2)
  exact ((Nat.Coprime.pow_left k hcop).symm).dvd_of_dvd_mul_left (hdvd.trans h)

end Aut34

theorem aut34Odd (W : Type) [Group W] [Finite W] (hW : CFSG.GH74.GLS.Stage2.Local.IsL34Two W) :
    CFSG.GH74.GLS.Stage2.Signalizer.oddPart (Nat.card (MulAut W)) ∣ 9 := by
  obtain ⟨e⟩ := hW
  have hfin : Finite SylSL3_4 := Finite.of_equiv W e.toEquiv
  have hfinA : Finite (MulAut SylSL3_4) :=
    Finite.of_injective (fun φ : MulAut SylSL3_4 => (φ : SylSL3_4 → SylSL3_4))
      DFunLike.coe_injective
  have hcard : Nat.card (MulAut W) = Nat.card (MulAut SylSL3_4) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hF : Nat.card F4 = 4 := by
    have := GaloisField.card 2 2 (by norm_num)
    simpa using this
  obtain ⟨k, hk⟩ := Aut34.natCard_dvd F4
  have hpos : Nat.card (MulAut SylSL3_4) ≠ 0 := Nat.card_pos.ne'
  rw [hcard]
  refine Aut34.oddPart_dvd_nine hpos (k + 1 + 6) ?_
  refine hk.trans (dvd_of_eq ?_)
  rw [hF]
  show 2 ^ (k + 1) * (Nat.factorial 4) ^ 2 = 2 ^ (k + 1 + 6) * 9
  norm_num [Nat.factorial]
  ring

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
