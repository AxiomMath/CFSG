module

public import CFSG.Blueprint.ChevalleyRootGroupsTorus
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.Blueprint.Chevalley

open scoped commutatorElement

universe u v

private local instance instRingEndRootModule (τ : Tag) (R : Type*) [CommRing R] :
    Ring (Module.End R (RootModule τ R)) :=
  Module.End.instRing

variable {τ : Tag}

namespace Label

theorem Precedes.irrefl (a : Label τ) : ¬a.Precedes a := by
  rcases a with i | α
  · simp [Precedes]
  · simp only [Precedes, lt_self_iff_false, true_and, false_or]
    exact lt_irrefl _

theorem Precedes.trans {a b c : Label τ} (hab : a.Precedes b) (hbc : b.Precedes c) :
    a.Precedes c := by
  unfold Precedes at hab hbc ⊢
  rcases hab with h₁ | ⟨h₁, h₁'⟩ <;> rcases hbc with h₂ | ⟨h₂, h₂'⟩
  · exact .inl (by omega)
  · exact .inl (by omega)
  · exact .inl (by omega)
  · refine .inr ⟨h₁.trans h₂, ?_⟩
    rcases a with i | α <;> rcases b with j | β <;> rcases c with k | γ <;>
      simp only at h₁' h₂' ⊢ <;> first | exact h₁'.elim | exact h₂'.elim | exact lt_trans h₁' h₂'

theorem precedes_or_precedes {a b : Label τ} (hab : a ≠ b) : a.Precedes b ∨ b.Precedes a := by
  unfold Precedes
  rcases lt_trichotomy a.weight b.weight with h | h | h
  · exact .inr (.inl h)
  · rcases a with i | ⟨α, hα⟩ <;> rcases b with j | ⟨β, hβ⟩
    · rcases lt_trichotomy i j with hij | rfl | hij
      · exact .inl (.inr ⟨h, hij⟩)
      · exact absurd rfl hab
      · exact .inr (.inr ⟨h.symm, hij⟩)
    · simp only [weight] at h
      exact absurd h.symm hβ.height_ne_zero
    · simp only [weight] at h
      exact absurd h hα.height_ne_zero
    · rcases lt_trichotomy (toLex α) (toLex β) with hl | hl | hl
      · exact .inl (.inr ⟨h, hl⟩)
      · exact absurd (congrArg Sum.inr (Subtype.ext (toLex_inj.1 hl))) hab
      · exact .inr (.inr ⟨h.symm, hl⟩)
  · exact .inl (.inl h)

open Classical in
@[expose] def position (a : Label τ) : ℕ :=
  (Finset.univ.filter fun b : Label τ => b.Precedes a).card

open Classical in
@[expose] def coposition (a : Label τ) : ℕ :=
  (Finset.univ.filter fun b : Label τ => a.Precedes b).card

theorem position_lt_position {a b : Label τ} (h : a.Precedes b) : a.position < b.position := by
  classical
  unfold position
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun c hc => ?_).2 ⟨a, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans h
  · simpa using h
  · simpa using Precedes.irrefl a

theorem coposition_lt_coposition {a b : Label τ} (h : a.Precedes b) :
    b.coposition < a.coposition := by
  classical
  unfold coposition
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun c hc => ?_).2 ⟨b, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact h.trans hc
  · simpa using h
  · simpa using Precedes.irrefl b

theorem position_lt_card (a : Label τ) : a.position < Fintype.card (Label τ) := by
  classical
  unfold position
  rw [← Finset.card_univ]
  exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, Precedes.irrefl a⟩)

theorem coposition_lt_card (a : Label τ) : a.coposition < Fintype.card (Label τ) := by
  classical
  unfold coposition
  rw [← Finset.card_univ]
  exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, Precedes.irrefl a⟩)

end Label

theorem card_label (τ : Tag) :
    Fintype.card (Label τ) = τ.rank + Nat.card {v : Fin τ.rank → ℤ // IsRoot τ v} := by
  rw [Fintype.card_sum, Fintype.card_fin, Nat.card_eq_fintype_card]

variable {R : Type*} [CommRing R]

@[expose] def IsUpperUnitriangular (A : Module.End R (RootModule τ R)) : Prop :=
  (∀ b : Label τ, A (Finsupp.single b 1) b = 1) ∧
    ∀ a b : Label τ, b.Precedes a → A (Finsupp.single b 1) a = 0

@[expose] def IsLowerUnitriangular (A : Module.End R (RootModule τ R)) : Prop :=
  (∀ b : Label τ, A (Finsupp.single b 1) b = 1) ∧
    ∀ a b : Label τ, a.Precedes b → A (Finsupp.single b 1) a = 0

@[expose] def RaisesPos (pos : Label τ → ℕ) (m : ℕ) (A : Module.End R (RootModule τ R)) :
    Prop :=
  ∀ a b : Label τ, A (Finsupp.single b 1) a ≠ 0 → pos a + m ≤ pos b

namespace RaisesPos

variable {pos : Label τ → ℕ} {m n : ℕ} {A B : Module.End R (RootModule τ R)}

theorem zero (m : ℕ) : RaisesPos (R := R) pos m 0 := fun _ _ h => absurd rfl h

theorem one : RaisesPos (R := R) pos 0 1 := fun a b h => by
  rw [Module.End.one_apply] at h
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
  omega

theorem mono (h : RaisesPos pos m A) (hnm : n ≤ m) : RaisesPos pos n A := fun a b hab => by
  have := h a b hab
  omega

theorem add (hA : RaisesPos pos m A) (hB : RaisesPos pos m B) : RaisesPos pos m (A + B) :=
  fun a b hab => by
    rw [LinearMap.add_apply, Finsupp.add_apply] at hab
    by_cases h : A (Finsupp.single b 1) a = 0
    · rw [h, zero_add] at hab
      exact hB a b hab
    · exact hA a b h

theorem neg (hA : RaisesPos pos m A) : RaisesPos pos m (-A) := fun a b hab =>
  hA a b (by simpa using hab)

theorem sub (hA : RaisesPos pos m A) (hB : RaisesPos pos m B) : RaisesPos pos m (A - B) := by
  rw [sub_eq_add_neg]
  exact hA.add hB.neg

theorem mul (hA : RaisesPos pos m A) (hB : RaisesPos pos n B) : RaisesPos pos (m + n) (A * B) :=
  fun a b hab => by
    rw [Module.End.mul_apply, ← Finsupp.sum_single (B (Finsupp.single b 1)), Finsupp.sum,
      map_sum, Finsupp.finsetSum_apply] at hab
    obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
    have h₁ := hA a c (right_ne_zero_of_mul hc')
    have h₂ := hB c b (Finsupp.mem_support_iff.mp hc)
    omega

theorem pow (hA : RaisesPos pos m A) (k : ℕ) : RaisesPos pos (k * m) (A ^ k) := by
  induction k with
  | zero => simpa using one (R := R) (pos := pos)
  | succ k ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul hA

theorem eq_zero {N : ℕ} (hpos : ∀ a, pos a < N) (hA : RaisesPos pos N A) : A = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    Finsupp.zero_apply]
  by_contra h
  have h₁ := hA a b h
  have h₂ := hpos b
  omega

end RaisesPos

private theorem mul_sub_one_eq (X P : Module.End R (RootModule τ R)) :
    X * P - 1 = (X - 1) + (P - 1) + (X - 1) * (P - 1) := by
  noncomm_ring

@[expose] def posFiltration (pos : Label τ → ℕ) (m : ℕ) :
    Subgroup (Module.End R (RootModule τ R))ˣ where
  carrier := {g | RaisesPos pos m ((g : Module.End R (RootModule τ R)) - 1) ∧
    RaisesPos pos m (((g⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) - 1)}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, mul_sub_one_eq]
      exact (hg.1.add hh.1).add ((hg.1.mul hh.1).mono (by omega))
    · rw [mul_inv_rev, Units.val_mul, mul_sub_one_eq]
      exact (hh.2.add hg.2).add ((hh.2.mul hg.2).mono (by omega))
  one_mem' := ⟨by simpa using RaisesPos.zero (R := R) (pos := pos) m,
    by simpa using RaisesPos.zero (R := R) (pos := pos) m⟩
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

variable {pos : Label τ → ℕ}

private theorem raisesPos_zero_of_mem {m : ℕ} {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ posFiltration pos m) :
    RaisesPos pos 0 (g : Module.End R (RootModule τ R)) ∧
      RaisesPos pos 0 (((g⁻¹ : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R))) := by
  refine ⟨?_, ?_⟩
  · rw [← sub_add_cancel (g : Module.End R (RootModule τ R)) 1]
    exact (hg.1.mono (Nat.zero_le m)).add RaisesPos.one
  · rw [← sub_add_cancel (((g⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R))) 1]
    exact (hg.2.mono (Nat.zero_le m)).add RaisesPos.one

private theorem raisesPos_commutator {m n : ℕ} {x y : (Module.End R (RootModule τ R))ˣ}
    (hx : RaisesPos pos m ((x : Module.End R (RootModule τ R)) - 1))
    (hy : RaisesPos pos n ((y : Module.End R (RootModule τ R)) - 1))
    (hx' : RaisesPos pos 0 (((x⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R))))
    (hy' : RaisesPos pos 0 (((y⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)))) :
    RaisesPos pos (m + n) (((⁅x, y⁆ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) - 1) := by
  set X := (x : Module.End R (RootModule τ R))
  set Y := (y : Module.End R (RootModule τ R))
  set X' := ((x⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
  set Y' := ((y⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
  have hXY : (X - 1) * (Y - 1) - (Y - 1) * (X - 1) = X * Y - Y * X := by noncomm_ring
  have h₁ : Y * X * (X' * Y') = 1 := by
    rw [mul_assoc, ← mul_assoc X, Units.mul_inv x, one_mul, Units.mul_inv y]
  have key : X * Y * X' * Y' - 1 = ((X - 1) * (Y - 1) - (Y - 1) * (X - 1)) * (X' * Y') := by
    rw [hXY, sub_mul, h₁, mul_assoc (X * Y)]
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, key]
  have h₂ := ((hx.mul hy).sub ((hy.mul hx).mono (by omega))).mul (hx'.mul hy')
  simpa using h₂

theorem commutator_mem_posFiltration {m : ℕ} {x y : (Module.End R (RootModule τ R))ˣ}
    (hx : x ∈ posFiltration pos m) (hy : y ∈ posFiltration pos 1) :
    ⁅x, y⁆ ∈ posFiltration pos (m + 1) := by
  obtain ⟨hx₁, hx₂⟩ := raisesPos_zero_of_mem hx
  obtain ⟨hy₁, hy₂⟩ := raisesPos_zero_of_mem hy
  refine ⟨raisesPos_commutator hx.1 hy.1 hx₂ hy₂, ?_⟩
  rw [commutatorElement_inv, add_comm]
  exact raisesPos_commutator hy.1 hx.1 hy₂ hx₂

theorem lowerCentralSeries_le_posFiltration {H : Subgroup (Module.End R (RootModule τ R))ˣ}
    (hH : H ≤ posFiltration pos 1) (n : ℕ) :
    H.lowerCentralSeries n ≤ posFiltration pos (n + 1) := by
  induction n with
  | zero => simpa using hH
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    exact fun x hx y hy => commutator_mem_posFiltration (ih hx) (hH hy)

theorem posFiltration_eq_bot {N : ℕ} (hpos : ∀ a, pos a < N) :
    posFiltration (R := R) pos N = ⊥ := by
  refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Units.ext ?_)
  rw [Units.val_one, ← sub_eq_zero]
  exact hg.1.eq_zero hpos

theorem nilpotent_of_le_posFiltration {N : ℕ} (hN : 0 < N) (hpos : ∀ a, pos a < N)
    {H : Subgroup (Module.End R (RootModule τ R))ˣ} (hH : H ≤ posFiltration pos 1) :
    Group.IsNilpotent H ∧ Group.nilpotencyClass H ≤ N - 1 := by
  have h : H.lowerCentralSeries (N - 1) = ⊥ := by
    refine eq_bot_iff.2 ((lowerCentralSeries_le_posFiltration hH (N - 1)).trans ?_)
    rw [Nat.sub_add_cancel hN, posFiltration_eq_bot hpos]
  have hnil := Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot h
  refine ⟨hnil, ?_⟩
  have h' : (⊤ : Subgroup H).lowerCentralSeries (N - 1) = ⊥ := by
    rw [← Subgroup.map_subtype_inj, Subgroup.map_bot, Subgroup.top_subtype_lowerCentralSeries, h]
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.1 h'

theorem isPGroup_of_le_posFiltration {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {N : ℕ} (hpos : ∀ a, pos a < N) {H : Subgroup (Module.End K (RootModule τ K))ˣ}
    (hH : H ≤ posFiltration pos 1) : IsPGroup p H := by
  have : Nonempty (Label τ) := ⟨.inl ⟨0, τ.rank_pos⟩⟩
  have : CharP (Module.End K (RootModule τ K)) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p
  intro g
  refine ⟨N, Subtype.ext (Units.ext ?_)⟩
  have hG : RaisesPos pos 1 ((((g : H) : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) - 1) := (hH g.2).1
  have hGN := (by simpa using hG.pow N : RaisesPos pos N _).eq_zero hpos
  have hGp := pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hGN
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one,
    ← sub_add_cancel (((g : H) : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) 1, add_comm,
    add_pow_char_pow_of_commute p N (Commute.one_left _), hGp, one_pow, add_zero]

private theorem height_add_nsmul (u v : Fin τ.rank → ℤ) (k : ℕ) :
    height (u + k • v) = height u + k * height v := by
  unfold height
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem raisesPos_pinnedX_of_pos {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hpos : 0 < height α)
    (c : R) :
    RaisesPos Label.position 1 ((pinnedX τ R α c : Module.End R (RootModule τ R)) - 1) := by
  intro a b hab
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, sub_ne_zero] at hab
  obtain ⟨k, hk, hw⟩ := pinnedX_weight_shift hα c a b hab
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  refine Label.position_lt_position (.inl ?_)
  rw [Label.weight_eq_height_latticeWeight, Label.weight_eq_height_latticeWeight, hw,
    height_add_nsmul]
  nlinarith

theorem raisesPos_pinnedX_of_neg {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hneg : height α < 0)
    (c : R) :
    RaisesPos Label.coposition 1 ((pinnedX τ R α c : Module.End R (RootModule τ R)) - 1) := by
  intro a b hab
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, sub_ne_zero] at hab
  obtain ⟨k, hk, hw⟩ := pinnedX_weight_shift hα c a b hab
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  refine Label.coposition_lt_coposition (.inl ?_)
  rw [Label.weight_eq_height_latticeWeight, Label.weight_eq_height_latticeWeight, hw,
    height_add_nsmul]
  nlinarith

variable (τ R) in
theorem posUnipotent_le_posFiltration :
    posUnipotent τ R ≤ posFiltration Label.position 1 := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine ⟨raisesPos_pinnedX_of_pos hα.1 hα.2 c, ?_⟩
  rw [pinnedX_neg]
  exact raisesPos_pinnedX_of_pos hα.1 hα.2 (-c)

variable (τ R) in
theorem negUnipotent_le_posFiltration :
    negUnipotent τ R ≤ posFiltration Label.coposition 1 := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine ⟨raisesPos_pinnedX_of_neg hα.1 hα.2 c, ?_⟩
  rw [pinnedX_neg]
  exact raisesPos_pinnedX_of_neg hα.1 hα.2 (-c)

theorem isUpperUnitriangular_of_mem {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ posFiltration Label.position 1) :
    IsUpperUnitriangular (g : Module.End R (RootModule τ R)) := by
  refine ⟨fun b => ?_, fun a b hba => ?_⟩
  · by_contra h
    have := hg.1 b b (by
      rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
      exact sub_ne_zero.2 h)
    omega
  · by_contra h
    have hab : a ≠ b := fun h' => Label.Precedes.irrefl b (h' ▸ hba)
    have h₁ := hg.1 a b (by
      rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne hab, sub_zero]
      exact h)
    have h₂ := Label.position_lt_position hba
    omega

theorem isLowerUnitriangular_of_mem {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ posFiltration Label.coposition 1) :
    IsLowerUnitriangular (g : Module.End R (RootModule τ R)) := by
  refine ⟨fun b => ?_, fun a b hab' => ?_⟩
  · by_contra h
    have := hg.1 b b (by
      rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
      exact sub_ne_zero.2 h)
    omega
  · by_contra h
    have hab : a ≠ b := fun h' => Label.Precedes.irrefl a (h' ▸ hab')
    have h₁ := hg.1 a b (by
      rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne hab, sub_zero]
      exact h)
    have h₂ := Label.coposition_lt_coposition hab'
    omega

variable (τ R) in
theorem posUnipotent_inf_negUnipotent : posUnipotent τ R ⊓ negUnipotent τ R = ⊥ := by
  refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Units.ext ?_)
  have h₁ := posUnipotent_le_posFiltration τ R hg.1
  have h₂ := negUnipotent_le_posFiltration τ R hg.2
  rw [Units.val_one, ← sub_eq_zero]
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    Finsupp.zero_apply]
  by_contra h
  have p₁ := h₁.1 a b h
  have p₂ := h₂.1 a b h
  rcases eq_or_ne a b with rfl | hab
  · omega
  · rcases Label.precedes_or_precedes hab with hp | hp
    · have := Label.coposition_lt_coposition hp
      omega
    · have := Label.position_lt_position hp
      omega

theorem positive_root_triangularity (τ : Tag) :
    (∀ (R : Type u) [CommRing R],
      (∀ g ∈ posUnipotent τ R, IsUpperUnitriangular (g : Module.End R (RootModule τ R))) ∧
        (∀ g ∈ negUnipotent τ R, IsLowerUnitriangular (g : Module.End R (RootModule τ R))) ∧
        posUnipotent τ R ⊓ negUnipotent τ R = ⊥ ∧
        Group.IsNilpotent (posUnipotent τ R) ∧
        Group.nilpotencyClass (posUnipotent τ R) ≤
          τ.rank + Nat.card {v : Fin τ.rank → ℤ // IsRoot τ v} - 1 ∧
        Group.IsNilpotent (negUnipotent τ R) ∧
        Group.nilpotencyClass (negUnipotent τ R) ≤
          τ.rank + Nat.card {v : Fin τ.rank → ℤ // IsRoot τ v} - 1) ∧
      ∀ (K : Type v) [Field K] [Finite K] (p : ℕ) [CharP K p],
        Finite (posUnipotent τ K) ∧ IsPGroup p (posUnipotent τ K) ∧
          Finite (negUnipotent τ K) ∧ IsPGroup p (negUnipotent τ K) := by
  have hN : 0 < Fintype.card (Label τ) := Fintype.card_pos_iff.2 ⟨.inl ⟨0, τ.rank_pos⟩⟩
  refine ⟨fun R _ => ?_, fun K _ _ p _ => ?_⟩
  · obtain ⟨hn₁, hc₁⟩ := nilpotent_of_le_posFiltration hN Label.position_lt_card
      (posUnipotent_le_posFiltration τ R)
    obtain ⟨hn₂, hc₂⟩ := nilpotent_of_le_posFiltration hN Label.coposition_lt_card
      (negUnipotent_le_posFiltration τ R)
    rw [card_label] at hc₁ hc₂
    exact ⟨fun g hg => isUpperUnitriangular_of_mem (posUnipotent_le_posFiltration τ R hg),
      fun g hg => isLowerUnitriangular_of_mem (negUnipotent_le_posFiltration τ R hg),
      posUnipotent_inf_negUnipotent τ R, hn₁, hc₁, hn₂, hc₂⟩
  · have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
    have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
    exact ⟨inferInstance, isPGroup_of_le_posFiltration p Label.position_lt_card
      (posUnipotent_le_posFiltration τ K), inferInstance,
      isPGroup_of_le_posFiltration p Label.coposition_lt_card
        (negUnipotent_le_posFiltration τ K)⟩

end CFSG.Blueprint.Chevalley
