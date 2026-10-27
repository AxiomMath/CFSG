module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.LieType.BorelTits.Kempf

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open
open scoped RealInnerProductSpace Pointwise

@[expose] def glRep {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (H : Subgroup (LinearMap.GeneralLinearGroup K V)) : H →* Module.End K V :=
  (Units.coeHom (Module.End K V)).comp H.subtype

@[simp] theorem glRep_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (H : Subgroup (LinearMap.GeneralLinearGroup K V)) (h : H) (x : V) :
    glRep H h x = ((h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x :=
  rfl

theorem glRep_injective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (H : Subgroup (LinearMap.GeneralLinearGroup K V)) : Function.Injective (glRep H) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ g : G, ∀ q ∈ Q, g⁻¹ * q * g ∈ (S : Subgroup G) := by
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, fun q hq => ?_⟩
  have h := hQT hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
  simpa [MulAut.smul_def, mul_assoc] using h

namespace Weighted

variable {ι K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (b : Module.Basis ι K V) (wt : ι → E)

@[expose] def Raises (v : E) (r : ℝ) (f : Module.End K V) : Prop :=
  ∀ i j, b.repr (f (b j)) i ≠ 0 → ⟪wt j, v⟫ + r ≤ ⟪wt i, v⟫

variable {b wt}

theorem exists_of_repr_mul_ne_zero {f g : Module.End K V} {i j : ι}
    (h : b.repr ((f * g) (b j)) i ≠ 0) :
    ∃ k, b.repr (f (b k)) i ≠ 0 ∧ b.repr (g (b j)) k ≠ 0 := by
  rw [Module.End.mul_apply, ← b.linearCombination_repr (g (b j)),
    Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum, Finsupp.sum_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  beta_reduce at hk
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul] at hk
  exact ⟨k, right_ne_zero_of_mul hk, left_ne_zero_of_mul hk⟩

theorem Raises.mul {v : E} {r s : ℝ} {f g : Module.End K V} (hf : Raises b wt v r f)
    (hg : Raises b wt v s g) : Raises b wt v (r + s) (f * g) := by
  intro i j hij
  obtain ⟨k, h1, h2⟩ := exists_of_repr_mul_ne_zero hij
  have := hf i k h1
  have := hg k j h2
  linarith

theorem Raises.add {v : E} {r : ℝ} {f g : Module.End K V} (hf : Raises b wt v r f)
    (hg : Raises b wt v r g) : Raises b wt v r (f + g) := by
  intro i j hij
  rw [LinearMap.add_apply, map_add, Finsupp.add_apply] at hij
  by_cases h : b.repr (f (b j)) i = 0
  · rw [h, zero_add] at hij
    exact hg i j hij
  · exact hf i j h

theorem Raises.mono {v : E} {r r' : ℝ} {f : Module.End K V} (h : r' ≤ r)
    (hf : Raises b wt v r f) : Raises b wt v r' f := fun i j hij => by
  have := hf i j hij
  linarith

theorem raises_one (v : E) : Raises b wt v 0 (1 : Module.End K V) := by
  classical
  intro i j hij
  rw [Module.End.one_apply, b.repr_self, Finsupp.single_apply] at hij
  split_ifs at hij with h
  · subst h
    simp
  · exact absurd rfl hij

theorem raises_zero (v : E) (r : ℝ) : Raises b wt v r (0 : Module.End K V) := by
  intro i j hij
  simp at hij

theorem Raises.pow {v : E} {r : ℝ} {f : Module.End K V} (hf : Raises b wt v r f) (m : ℕ) :
    Raises b wt v (m * r) (f ^ m) := by
  induction m with
  | zero => simpa using raises_one (b := b) (wt := wt) v
  | succ m ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast
    ring

theorem Raises.eq_zero {v : E} {r : ℝ} {f : Module.End K V} (hf : Raises b wt v r f)
    (hr : ∀ i j, ⟪wt i, v⟫ - ⟪wt j, v⟫ < r) : f = 0 := by
  refine b.ext fun j => (b.ext_elem_iff).mpr fun i => ?_
  by_contra hne
  rw [LinearMap.zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hne
  have := hf i j hne
  have := hr i j
  linarith

variable {W : Type*} [Group W]

theorem raises_conj_of_monomial (act : W →* (E ≃ₗᵢ[ℝ] E)) (w : W) {N N' : Module.End K V}
    (hN : ∀ i j, b.repr (N (b j)) i ≠ 0 → wt i = act w (wt j))
    (hN' : ∀ i j, b.repr (N' (b j)) i ≠ 0 → act w (wt i) = wt j) {v : E} {r : ℝ}
    {T : Module.End K V} (hT : Raises b wt (act w v) r T) : Raises b wt v r (N' * T * N) := by
  intro i j hij
  obtain ⟨l, hl, hlj⟩ := exists_of_repr_mul_ne_zero hij
  obtain ⟨k, hik, hkl⟩ := exists_of_repr_mul_ne_zero hl
  have e1 := hN' i k hik
  have e2 := hN l j hlj
  have := hT k l hkl
  rw [← e1, e2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map] at this
  exact this

theorem raises_conj_of_monomial' (act : W →* (E ≃ₗᵢ[ℝ] E)) (w : W) {N N' : Module.End K V}
    (hN : ∀ i j, b.repr (N (b j)) i ≠ 0 → wt i = act w (wt j))
    (hN' : ∀ i j, b.repr (N' (b j)) i ≠ 0 → act w (wt i) = wt j) {v : E} {r : ℝ}
    {S : Module.End K V} (hS : Raises b wt v r S) : Raises b wt (act w v) r (N * S * N') := by
  intro i j hij
  obtain ⟨l, hl, hlj⟩ := exists_of_repr_mul_ne_zero hij
  obtain ⟨k, hik, hkl⟩ := exists_of_repr_mul_ne_zero hl
  have e1 := hN i k hik
  have e2 := hN' l j hlj
  have := hS k l hkl
  rw [e1, ← e2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  exact this

variable {G : Type*} [Group G] (ρ : G →* Module.End K V)

theorem rep_inv_mul (a : G) : ρ a⁻¹ * ρ a = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem rep_mul_inv (a : G) : ρ a * ρ a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem rep_conj_sub_one (c x : G) :
    ρ (c⁻¹ * x * c) - 1 = ρ c⁻¹ * (ρ x - 1) * ρ c := by
  rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, rep_inv_mul]

theorem inv_eq_pow_card_sub_one [Finite G] (x : G) : x⁻¹ = x ^ (Nat.card G - 1) := by
  have h1 : 1 ≤ Nat.card G := Nat.card_pos
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel h1, pow_card_eq_one']

variable (b wt) in
@[expose] def triangular [Finite G] (v : E) : Subgroup G where
  carrier := {x | Raises b wt v 0 (ρ x)}
  mul_mem' := by
    intro x y hx hy
    change Raises b wt v 0 (ρ (x * y))
    rw [map_mul]
    simpa using (show Raises b wt v 0 (ρ x) from hx).mul (show Raises b wt v 0 (ρ y) from hy)
  one_mem' := by
    change Raises b wt v 0 (ρ 1)
    rw [map_one]
    exact raises_one v
  inv_mem' := by
    intro x hx
    change Raises b wt v 0 (ρ x⁻¹)
    rw [inv_eq_pow_card_sub_one, map_pow]
    simpa using (show Raises b wt v 0 (ρ x) from hx).pow (Nat.card G - 1)

theorem mem_triangular [Finite G] {v : E} {x : G} :
    x ∈ triangular b wt ρ v ↔ Raises b wt v 0 (ρ x) :=
  Iff.rfl

variable (b wt) in
@[expose] def gradedKernelSet (v : E) : Set G :=
  {x | ∃ c : ℝ, 0 < c ∧ Raises b wt v c (ρ x - 1)}

theorem gradedKernelSet_mul {v : E} {x y : G} (hx : x ∈ gradedKernelSet b wt ρ v)
    (hy : y ∈ gradedKernelSet b wt ρ v) : x * y ∈ gradedKernelSet b wt ρ v := by
  obtain ⟨c₁, hc₁, h₁⟩ := hx
  obtain ⟨c₂, hc₂, h₂⟩ := hy
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  have hid : ρ (x * y) - 1 = (ρ x - 1) * (ρ y - 1) + (ρ x - 1) + (ρ y - 1) := by
    rw [map_mul]
    noncomm_ring
  rw [hid]
  refine ((Raises.mono ?_ (h₁.mul h₂)).add (h₁.mono (min_le_left _ _))).add
    (h₂.mono (min_le_right _ _))
  have := min_le_left c₁ c₂
  linarith

theorem one_mem_gradedKernelSet (v : E) : (1 : G) ∈ gradedKernelSet b wt ρ v :=
  ⟨1, one_pos, by rw [map_one, sub_self]; exact raises_zero v 1⟩

theorem pow_mem_gradedKernelSet {v : E} {x : G} (hx : x ∈ gradedKernelSet b wt ρ v) (m : ℕ) :
    x ^ m ∈ gradedKernelSet b wt ρ v := by
  induction m with
  | zero => simpa using one_mem_gradedKernelSet ρ v
  | succ m ih => rw [pow_succ]; exact gradedKernelSet_mul ρ ih hx

variable (b wt) in
@[expose] def gradedKernel [Finite G] (v : E) : Subgroup G where
  carrier := gradedKernelSet b wt ρ v
  mul_mem' := gradedKernelSet_mul ρ
  one_mem' := one_mem_gradedKernelSet ρ v
  inv_mem' := by
    intro x hx
    rw [inv_eq_pow_card_sub_one]
    exact pow_mem_gradedKernelSet ρ hx _

theorem mem_gradedKernel [Finite G] {v : E} {x : G} :
    x ∈ gradedKernel b wt ρ v ↔ ∃ c : ℝ, 0 < c ∧ Raises b wt v c (ρ x - 1) :=
  Iff.rfl

theorem gradedKernel_le_triangular [Finite G] (v : E) :
    gradedKernel b wt ρ v ≤ triangular b wt ρ v := by
  intro x hx
  obtain ⟨c, hc, h⟩ := hx
  rw [mem_triangular]
  have : ρ x = 1 + (ρ x - 1) := by abel
  rw [this]
  exact (raises_one v).add (h.mono hc.le)

theorem conj_mem_gradedKernel [Finite G] {v : E} {y x : G} (hy : y ∈ triangular b wt ρ v)
    (hx : x ∈ gradedKernel b wt ρ v) : y * x * y⁻¹ ∈ gradedKernel b wt ρ v := by
  obtain ⟨c, hc, h⟩ := hx
  refine ⟨c, hc, ?_⟩
  have hyi : y⁻¹ ∈ triangular b wt ρ v := inv_mem hy
  have hid : ρ (y * x * y⁻¹) - 1 = ρ y * (ρ x - 1) * ρ y⁻¹ := by
    rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, rep_mul_inv]
  rw [hid]
  have := ((show Raises b wt v 0 (ρ y) from hy).mul h).mul
    (show Raises b wt v 0 (ρ y⁻¹) from hyi)
  simpa using this

theorem triangular_le_normalizer_gradedKernel [Finite G] (v : E) :
    triangular b wt ρ v ≤ Subgroup.normalizer (gradedKernel b wt ρ v : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_gradedKernel ρ hy hx, fun hx => ?_⟩
  have := conj_mem_gradedKernel ρ (inv_mem hy) hx
  simpa [mul_assoc] using this

theorem isPGroup_gradedKernel [Finite G] [Finite ι] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : Function.Injective ρ) (v : E) : IsPGroup p (gradedKernel b wt ρ v) := by
  classical
  have := Fintype.ofFinite ι
  intro x
  obtain ⟨c, hc, h⟩ := x.2
  set T : Module.End K V := ρ (x : G) - 1 with hT
  set R : ℝ := 2 * ∑ k, |⟪wt k, v⟫| with hR
  have hbound : ∀ i j, ⟪wt i, v⟫ - ⟪wt j, v⟫ ≤ R := by
    intro i j
    have hi : |⟪wt i, v⟫| ≤ ∑ k, |⟪wt k, v⟫| :=
      Finset.single_le_sum (f := fun k => |⟪wt k, v⟫|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hj : |⟪wt j, v⟫| ≤ ∑ k, |⟪wt k, v⟫| :=
      Finset.single_le_sum (f := fun k => |⟪wt k, v⟫|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ j)
    have := le_abs_self ⟪wt i, v⟫
    have := neg_abs_le ⟪wt j, v⟫
    linarith
  set m : ℕ := ⌈R / c⌉₊ + 1 with hm
  have hmc : R < m * c := by
    have h1 : R / c ≤ ⌈R / c⌉₊ := Nat.le_ceil _
    have h2 : R / c < (m : ℝ) := by rw [hm]; push_cast; linarith
    rwa [div_lt_iff₀ hc] at h2
  have hTm : T ^ m = 0 := (h.pow m).eq_zero fun i j => (hbound i j).trans_lt hmc
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hmp : m ≤ p ^ m := (Nat.lt_pow_self hp).le
  have hTp : T ^ (p ^ m) = 0 := by
    rw [← Nat.sub_add_cancel hmp, pow_add, hTm, mul_zero]
  refine ⟨m, Subtype.ext (hρ ?_)⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Subsingleton.elim _ _
  have hinj : Function.Injective (algebraMap K (Module.End K V)) := by
    intro a a' haa
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have := congrArg (fun f : Module.End K V => f u) haa
    simp only [Module.algebraMap_end_apply] at this
    exact smul_left_injective K hu this
  have : CharP (Module.End K V) p := charP_of_injective_algebraMap hinj p
  have hcomm : Commute T 1 := Commute.one_right _
  have key := add_pow_char_pow_of_commute p m hcomm
  rw [hT, sub_add_cancel] at key
  rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one, key, ← hT, hTp, one_pow, zero_add]

theorem gradedKernel_le_pCoreOf [Finite G] [Finite ι] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : Function.Injective ρ) (v : E) :
    gradedKernel b wt ρ v ≤ pCoreOf p (triangular b wt ρ v) :=
  le_pCoreOf_of_le_normalizer p (gradedKernel_le_triangular ρ v)
    (triangular_le_normalizer_gradedKernel ρ v) (isPGroup_gradedKernel ρ p hρ v)

variable (b wt) in
structure WeightedBruhat (act : W →* (E ≃ₗᵢ[ℝ] E)) (n : W → G) (B U : Subgroup G) (D : Set E)
    (v₀ : E) : Prop where
  span_wt : Submodule.span ℝ (Set.range wt) = ⊤
  fixfree : ∀ v : E, (∀ w, act w v = v) → v = 0
  mono : ∀ w i j, b.repr (ρ (n w) (b j)) i ≠ 0 → wt i = act w (wt j)
  mono_inv : ∀ w i j, b.repr (ρ (n w)⁻¹ (b j)) i ≠ 0 → act w (wt i) = wt j
  cover : ∀ x : E, ∃ w, ∃ y ∈ D, x = act w y
  borel : ∀ x ∈ B, ∀ v ∈ D, ∀ i j, b.repr (ρ x (b j)) i ≠ 0 → ⟪wt j, v⟫ ≤ ⟪wt i, v⟫
  bruhat : ∀ g : G, ∃ w, ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n w * b₂
  unip : ∀ u ∈ U, ∀ i j, b.repr (ρ u (b j) - b j) i ≠ 0 → ⟪wt j, v₀⟫ < ⟪wt i, v₀⟫

variable {act : W →* (E ≃ₗᵢ[ℝ] E)} {n : W → G} {B U : Subgroup G} {D : Set E} {v₀ : E}

@[expose] def WeightedBruhat.data (h : WeightedBruhat b wt ρ act n B U D v₀) :
    Kempf.Data G W E where
  act := act
  n := n
  B := B
  D := D
  cover := h.cover
  bruhat := h.bruhat

theorem WeightedBruhat.raises_borel (h : WeightedBruhat b wt ρ act n B U D v₀) {x : G}
    (hx : x ∈ B) {v : E} (hv : v ∈ D) : Raises b wt v 0 (ρ x) :=
  fun i j hij => by simpa using h.borel x hx v hv i j hij

theorem WeightedBruhat.borel_mem [Finite G] (h : WeightedBruhat b wt ρ act n B U D v₀)
    {v : E} (hv : v ∈ D) : B ≤ triangular b wt ρ v :=
  fun _ hx => (mem_triangular ρ).mpr (h.raises_borel ρ hx hv)

theorem n_mem_triangular [Finite G] (h : WeightedBruhat b wt ρ act n B U D v₀) {w : W} {v : E}
    (hwv : act w v = v) : n w ∈ triangular b wt ρ v := by
  rw [mem_triangular]
  intro i j hij
  rw [h.mono w i j hij]
  have key : ⟪act w (wt j), v⟫ = ⟪wt j, v⟫ := by
    calc ⟪act w (wt j), v⟫ = ⟪act w (wt j), act w v⟫ := by rw [hwv]
      _ = ⟪wt j, v⟫ := LinearIsometryEquiv.inner_map_map _ _ _
  rw [key, add_zero]

theorem act_eq_of_mem_triangular [Finite G] [Finite W] (h : WeightedBruhat b wt ρ act n B U D v₀)
    {w : W} {v : E} (hn : n w ∈ triangular b wt ρ v) : act w v = v := by
  have step : ∀ j, ∃ i, wt i = act w (wt j) ∧ ⟪wt j, v⟫ ≤ ⟪wt i, v⟫ := by
    intro j
    have h1 : b.repr ((ρ (n w)⁻¹ * ρ (n w)) (b j)) j ≠ 0 := by
      rw [rep_inv_mul]
      simp
    obtain ⟨i, -, hij⟩ := exists_of_repr_mul_ne_zero h1
    refine ⟨i, h.mono w i j hij, ?_⟩
    have := (mem_triangular ρ).mp hn i j hij
    linarith
  have act_mul : ∀ (a c : W) (x : E), act (a * c) x = act a (act c x) := fun a c x => by
    rw [map_mul]
    rfl
  have iter : ∀ k : ℕ, ∀ j, ∃ i, wt i = act (w ^ k) (wt j) ∧ ⟪wt j, v⟫ ≤ ⟪wt i, v⟫ := by
    intro k
    induction k with
    | zero => intro j; exact ⟨j, by simp, le_rfl⟩
    | succ k ih =>
      intro j
      obtain ⟨i₁, e₁, h₁⟩ := ih j
      obtain ⟨i₂, e₂, h₂⟩ := step i₁
      refine ⟨i₂, ?_, h₁.trans h₂⟩
      rw [e₂, e₁, pow_succ', act_mul]
  have hmpos : 0 < orderOf w := orderOf_pos w
  have hfix : ∀ j, ⟪act w (wt j), v⟫ = ⟪wt j, v⟫ := by
    intro j
    obtain ⟨i₁, e₁, h₁⟩ := step j
    obtain ⟨i₂, e₂, h₂⟩ := iter (orderOf w - 1) i₁
    have : wt i₂ = wt j := by
      rw [e₂, e₁, ← act_mul, ← pow_succ, Nat.sub_add_cancel hmpos, pow_orderOf_eq_one,
        map_one]
      rfl
    rw [this] at h₂
    rw [← e₁]
    linarith
  set u : E := (act w).symm v - v with hu
  have horth : ∀ j, ⟪wt j, u⟫ = 0 := by
    intro j
    have h1 : ⟪act w (wt j), v⟫ = ⟪wt j, (act w).symm v⟫ := by
      calc ⟪act w (wt j), v⟫ = ⟪act w (wt j), act w ((act w).symm v)⟫ := by simp
        _ = ⟪wt j, (act w).symm v⟫ := LinearIsometryEquiv.inner_map_map _ _ _
    rw [hu, inner_sub_right, ← h1, hfix j, sub_self]
  have hu0 : u = 0 := by
    let F : E →ₗ[ℝ] ℝ := innerₛₗ ℝ u
    have hle : Submodule.span ℝ (Set.range wt) ≤ LinearMap.ker F := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, F, innerₛₗ_apply_apply]
      rw [real_inner_comm]
      exact horth j
    rw [h.span_wt] at hle
    have : F u = 0 := hle Submodule.mem_top
    simp only [F, innerₛₗ_apply_apply] at this
    exact inner_self_eq_zero.mp this
  have : (act w).symm v = v := sub_eq_zero.mp hu0
  calc act w v = act w ((act w).symm v) := by rw [this]
    _ = v := by simp

theorem triangular_ne_top [Finite G] [Finite W] (h : WeightedBruhat b wt ρ act n B U D v₀)
    {v : E} (hv : v ≠ 0) : triangular b wt ρ v ≠ ⊤ := by
  intro htop
  apply hv
  apply h.fixfree
  intro w
  exact act_eq_of_mem_triangular ρ h (htop ▸ Subgroup.mem_top _)

variable [Finite ι]

open _root_.Classical in
variable (b) in
@[expose] noncomputable def supp (Q : Subgroup G) (g : G) : Finset (ι × ι) :=
  (Set.toFinite {ij : ι × ι | ∃ q ∈ Q, b.repr ((ρ (g⁻¹ * q * g) - 1) (b ij.2)) ij.1 ≠ 0}).toFinset

variable (b wt) in
@[expose] noncomputable def score (Q : Subgroup G) (g : G) (v : E) : ℝ :=
  if h : (supp b ρ Q g).Nonempty then
    (supp b ρ Q g).inf' h (fun ij => ⟪wt ij.1, v⟫ - ⟪wt ij.2, v⟫)
  else 0

theorem mem_supp {Q : Subgroup G} {g : G} {i j : ι} :
    (i, j) ∈ supp b ρ Q g ↔ ∃ q ∈ Q, b.repr ((ρ (g⁻¹ * q * g) - 1) (b j)) i ≠ 0 := by
  simp [supp]

theorem le_score_iff {Q : Subgroup G} {g : G} (h : (supp b ρ Q g).Nonempty) {v : E} {r : ℝ} :
    r ≤ score b wt ρ Q g v ↔ ∀ q ∈ Q, Raises b wt v r (ρ (g⁻¹ * q * g) - 1) := by
  rw [score, dite_eq_left h, Finset.le_inf'_iff]
  constructor
  · intro H q hq i j hij
    have := H (i, j) ((mem_supp ρ).mpr ⟨q, hq, hij⟩)
    simp only at this
    linarith
  · rintro H ⟨i, j⟩ hij
    obtain ⟨q, hq, hne⟩ := (mem_supp ρ).mp hij
    have := H q hq i j hne
    simp only
    linarith

theorem supp_nonempty {Q : Subgroup G} (hQ : Q ≠ ⊥) (hρ : Function.Injective ρ) (g : G) :
    (supp b ρ Q g).Nonempty := by
  obtain ⟨⟨q, hq⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQ
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hne : g⁻¹ * q * g ≠ 1 := by
    intro h
    apply hq1'
    calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hT : ρ (g⁻¹ * q * g) - 1 ≠ 0 := by
    intro h0
    apply hne
    apply hρ
    rw [map_one]
    exact sub_eq_zero.mp h0
  obtain ⟨i, j, hij⟩ : ∃ i j, b.repr ((ρ (g⁻¹ * q * g) - 1) (b j)) i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hT (b.ext fun j => (b.ext_elem_iff).mpr fun i => by simpa using hall i j)
  exact ⟨(i, j), (mem_supp ρ).mpr ⟨q, hq, hij⟩⟩

theorem score_isScore (h : WeightedBruhat b wt ρ act n B U D v₀) {Q : Subgroup G} (hQ : Q ≠ ⊥)
    (hρ : Function.Injective ρ) : Kempf.IsScore (h.data ρ) (score b wt ρ Q) where
  usc g := by
    apply Continuous.upperSemicontinuous
    have hne := supp_nonempty (b := b) ρ hQ hρ g
    have : score b wt ρ Q g =
        fun v => (supp b ρ Q g).inf' hne (fun ij => ⟪wt ij.1, v⟫ - ⟪wt ij.2, v⟫) := by
      funext v
      rw [score, dite_eq_left hne]
    rw [this]
    exact Continuous.finset_inf'_apply _ fun ij _ =>
      (continuous_const.inner continuous_id).sub (continuous_const.inner continuous_id)
  smul g t v ht := by
    have hne := supp_nonempty (b := b) ρ hQ hρ g
    rw [score, score, dite_eq_left hne, dite_eq_left hne]
    simp_rw [real_inner_smul_right, ← mul_sub]
    exact (Finset.apply_inf'_eq_inf'_comp hne (fun x => t * x)
      (fun x y => mul_min_of_nonneg x y ht)).symm
  superadd g x y _ _ := by
    have hne := supp_nonempty (b := b) ρ hQ hρ g
    rw [score, score, score, dite_eq_left hne, dite_eq_left hne, dite_eq_left hne]
    apply Finset.le_inf'
    intro ij hij
    have h1 : (supp b ρ Q g).inf' hne (fun ij => ⟪wt ij.1, x⟫ - ⟪wt ij.2, x⟫) ≤
        ⟪wt ij.1, x⟫ - ⟪wt ij.2, x⟫ := Finset.inf'_le _ hij
    have h2 : (supp b ρ Q g).inf' hne (fun ij => ⟪wt ij.1, y⟫ - ⟪wt ij.2, y⟫) ≤
        ⟪wt ij.1, y⟫ - ⟪wt ij.2, y⟫ := Finset.inf'_le _ hij
    simp only [inner_add_right]
    linarith
  borel g x hx v hv _ := by
    have hne := supp_nonempty (b := b) ρ hQ hρ g
    have hne' := supp_nonempty (b := b) ρ hQ hρ (g * x)
    rw [le_score_iff ρ hne']
    intro q hq
    have H := (le_score_iff (wt := wt) (v := v) ρ hne).mp le_rfl q hq
    have hc : (g * x)⁻¹ * q * (g * x) = x⁻¹ * (g⁻¹ * q * g) * x := by group
    rw [hc, rep_conj_sub_one]
    have := ((h.raises_borel ρ (inv_mem hx) hv).mul H).mul (h.raises_borel ρ hx hv)
    simpa using this
  weyl g w v := by
    have hne := supp_nonempty (b := b) ρ hQ hρ g
    have hne' := supp_nonempty (b := b) ρ hQ hρ (g * n w)
    have hc : ∀ q, (g * n w)⁻¹ * q * (g * n w) = (n w)⁻¹ * (g⁻¹ * q * g) * n w :=
      fun q => by group
    change score b wt ρ Q (g * n w) v = score b wt ρ Q g (act w v)
    apply le_antisymm
    · rw [le_score_iff ρ hne]
      intro q hq
      have H := (le_score_iff (wt := wt) (v := v) ρ hne').mp le_rfl q hq
      rw [hc, rep_conj_sub_one] at H
      have := raises_conj_of_monomial' act w (h.mono w) (h.mono_inv w) H
      have e : ρ (n w) * (ρ (n w)⁻¹ * (ρ (g⁻¹ * q * g) - 1) * ρ (n w)) * ρ (n w)⁻¹ =
          ρ (g⁻¹ * q * g) - 1 := by
        simp only [← mul_assoc, rep_mul_inv, one_mul]
        rw [mul_assoc, rep_mul_inv, mul_one]
      rwa [e] at this
    · rw [le_score_iff ρ hne']
      intro q hq
      have H := (le_score_iff (wt := wt) (v := act w v) ρ hne).mp le_rfl q hq
      rw [hc, rep_conj_sub_one]
      exact raises_conj_of_monomial act w (h.mono w) (h.mono_inv w) H

theorem score_normalizer {Q : Subgroup G} {h : G} (hh : h ∈ Subgroup.normalizer (Q : Set G))
    (g : G) (v : E) : score b wt ρ Q (h * g) v = score b wt ρ Q g v := by
  have hs : supp b ρ Q (h * g) = supp b ρ Q g := by
    ext ⟨i, j⟩
    rw [mem_supp, mem_supp]
    constructor
    · rintro ⟨q, hq, hne⟩
      refine ⟨h⁻¹ * q * h, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) q).mp hq
        simpa using this
      · have e : g⁻¹ * (h⁻¹ * q * h) * g = (h * g)⁻¹ * q * (h * g) := by group
        rw [e]
        exact hne
    · rintro ⟨q, hq, hne⟩
      refine ⟨h * q * h⁻¹, (Subgroup.mem_normalizer_iff.mp hh q).mp hq, ?_⟩
      have e : (h * g)⁻¹ * (h * q * h⁻¹) * (h * g) = g⁻¹ * q * g := by group
      rw [e]
      exact hne
  simp only [score, hs]

theorem score_pos (h : WeightedBruhat b wt ρ act n B U D v₀) {Q : Subgroup G} (hQ : Q ≠ ⊥)
    (hρ : Function.Injective ρ) {g₀ : G} (hg₀ : ∀ q ∈ Q, g₀⁻¹ * q * g₀ ∈ U) :
    0 < score b wt ρ Q g₀ v₀ := by
  rw [score, dite_eq_left (supp_nonempty ρ hQ hρ g₀), Finset.lt_inf'_iff]
  rintro ⟨i, j⟩ hij
  obtain ⟨q, hq, hne⟩ := (mem_supp ρ).mp hij
  have hne' : b.repr (ρ (g₀⁻¹ * q * g₀) (b j) - b j) i ≠ 0 := by
    simpa [LinearMap.sub_apply] using hne
  have := h.unip _ (hg₀ q hq) i j hne'
  simp only
  linarith

theorem exists_triangular_of_weightedBruhat [Finite G] [Finite W] [FiniteDimensional ℝ E]
    (h : WeightedBruhat b wt ρ act n B U D v₀) (hρ : Function.Injective ρ) {Q : Subgroup G}
    (hQ : Q ≠ ⊥) (hconj : ∃ g₀ : G, ∀ q ∈ Q, g₀⁻¹ * q * g₀ ∈ U) :
    ∃ g : G, ∃ v ∈ D, v ≠ 0 ∧
      (∀ x ∈ Subgroup.normalizer (Q : Set G), g⁻¹ * x * g ∈ triangular b wt ρ v) ∧
      (∀ q ∈ Q, g⁻¹ * q * g ∈ gradedKernel b wt ρ v) := by
  have hf := score_isScore ρ h hQ hρ
  obtain ⟨g₀, hg₀⟩ := hconj
  obtain ⟨M, hM, hmax, g, v, hvD, hvn, hfv⟩ :=
    Kempf.exists_max hf ⟨g₀, v₀, score_pos ρ h hQ hρ hg₀⟩
  refine ⟨g, v, hvD, ?_, ?_, ?_⟩
  · rintro rfl
    simp at hvn
  · intro x hx
    obtain ⟨w, hwv, b₁, hb₁, b₂, hb₂, hbr⟩ :=
      Kempf.conj_mem_of_invariant hf hM hmax hvD hvn hfv (score_normalizer ρ hx)
    rw [hbr]
    exact mul_mem (mul_mem (h.borel_mem ρ hvD hb₁) (n_mem_triangular ρ h hwv))
      (h.borel_mem ρ hvD hb₂)
  · intro q hq
    exact ⟨M, hM, (le_score_iff ρ (supp_nonempty ρ hQ hρ g)).mp (le_of_eq hfv.symm) q hq⟩

theorem holds_of_weightedBruhat [Finite G] [Finite W] [FiniteDimensional ℝ E] (p : ℕ)
    [Fact p.Prime] [CharP K p] (hρ : Function.Injective ρ) (S : Sylow p G)
    (h : WeightedBruhat b wt ρ act n B S D v₀)
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ B) : Holds G p := by
  intro Q hQ hQp
  set R := pCoreOf p (Subgroup.normalizer (Q : Set G)) with hRdef
  have hQR : Q ≤ R := le_pCoreOf_normalizer p Q hQp
  have hR : R ≠ ⊥ := fun h0 => hQ (le_bot_iff.mp (h0 ▸ hQR))
  have hRp : IsPGroup p R := pCoreOf_isPGroup p _
  obtain ⟨g, v, hvD, hv0, hN, hK⟩ :=
    exists_triangular_of_weightedBruhat ρ h hρ hR (exists_conj_mem_sylow S hRp)
  let c : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hc : ∀ x, c x = g⁻¹ * x * g := fun x => by simp [c]
  set P := (triangular b wt ρ v).comap c with hP
  set N := (gradedKernel b wt ρ v).comap c with hNdef
  have hNP : N ≤ P := Subgroup.comap_mono (gradedKernel_le_triangular ρ v)
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    have hy1 : c y ∈ triangular b wt ρ v := hy
    have hy2 : c y⁻¹ ∈ triangular b wt ρ v := by rw [map_inv]; exact inv_mem hy1
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx1 : c x ∈ gradedKernel b wt ρ v := hx
      show c (y * x * y⁻¹) ∈ gradedKernel b wt ρ v
      have := conj_mem_gradedKernel ρ hy1 hx1
      rwa [← map_inv, ← map_mul, ← map_mul] at this
    · intro hx
      have hx1 : c (y * x * y⁻¹) ∈ gradedKernel b wt ρ v := hx
      show c x ∈ gradedKernel b wt ρ v
      have h1 := conj_mem_gradedKernel ρ hy2 hx1
      have e : c y⁻¹ * c (y * x * y⁻¹) * (c y⁻¹)⁻¹ = c x := by
        rw [← map_inv, inv_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rwa [e] at h1
  have hNp : IsPGroup p N := by
    intro x
    obtain ⟨k, hk⟩ := isPGroup_gradedKernel ρ p hρ v ⟨c x, x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : c ((x : G) ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hinj : Function.Injective c := (MulAut.conj g⁻¹).injective
    have : (x : G) ^ p ^ k = 1 := hinj (by rw [hk', map_one])
    simpa using this
  have hNcore : N ≤ pCoreOf p P := le_pCoreOf_of_le_normalizer p hNP hPN hNp
  have hPtop : P ≠ ⊤ := by
    intro htop
    apply triangular_ne_top ρ h hv0
    rw [eq_top_iff]
    intro x _
    have : g * x * g⁻¹ ∈ P := htop ▸ Subgroup.mem_top _
    rw [hP, Subgroup.mem_comap, hc] at this
    simpa [mul_assoc] using this
  refine conclusion_of_core p Q hQp (g • S) P hPtop ?_ ?_ ?_
  · intro x hx
    have hxR : x ∈ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf p _ hx
    rw [hP, Subgroup.mem_comap, hc]
    exact hN x hxR
  · intro x hx
    refine hNcore ?_
    rw [hNdef, Subgroup.mem_comap, hc]
    exact hK x hx
  · intro x hx
    rw [hP, Subgroup.mem_comap, hc]
    refine h.borel_mem ρ hvD (hNS ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : ∀ z : G, z ∈ ((g • S : Sylow p G) : Subgroup G) ↔
        g⁻¹ * z * g ∈ (S : Subgroup G) := by
      intro z
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def, mul_assoc]
    have hx' := Subgroup.mem_normalizer_iff.mp hx (g * y * g⁻¹)
    rw [key, key] at hx'
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1, e2] at hx'
    exact hx'

end Weighted

end CFSG.LieType.BorelTits
