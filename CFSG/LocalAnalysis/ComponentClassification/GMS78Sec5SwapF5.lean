module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5CoordSz

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.BenderSuzuki.PFAppendixIII

namespace SwapF5

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem sum_sum_eq_sum_diag {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CharP R 2]
    (f : ι → ι → R) (hf : ∀ i j, f i j = f j i) : ∑ i, ∑ j, f i j = ∑ i, f i i := by
  rw [← Finset.sum_product' (f := f), ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  have hoff : ∑ p ∈ (Finset.univ : Finset ι).offDiag, f p.1 p.2 = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) (fun p _ => ?_) (fun p hp _ => ?_)
      (fun p hp => ?_) (fun p _ => rfl)
    · simp only
      rw [hf p.2 p.1, CharTwo.add_self_eq_zero]
    · intro h
      have h1 : p.2 = p.1 := (Prod.ext_iff.mp h).1
      exact (Finset.mem_offDiag.mp hp).2.2 h1.symm
    · rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩
  rw [hoff, add_zero]

omit [CharP K 2] in
theorem pow_two_pow_eq_mod {m : ℕ} (hK : Fintype.card K = 2 ^ m) (x : K) (k : ℕ) :
    x ^ 2 ^ k = x ^ 2 ^ (k % m) := by
  have h1 : x ^ 2 ^ m = x := by rw [← hK]; exact FiniteField.pow_card x
  have h2 : ∀ t : ℕ, x ^ 2 ^ (m * t) = x := VLike.pow_two_pow_mul_eq_self h1
  conv_lhs => rw [← Nat.div_add_mod k m, pow_add, pow_mul, h2]

theorem exists_monomial_of_quadratic {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {α β : K →+ K} (hα : ∃ w, α w ≠ 0)
    (h : ∀ w : K, β (w ^ (2 ^ (a + 1) + 1)) = α w ^ (2 ^ (a + 1) + 1)) :
    ∃ (c : K) (i : ℕ), ∀ w, α w = c * w ^ 2 ^ i := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m := 2 * a + 1 with hm
  have : NeZero m := ⟨by omega⟩
  have hKn : Nat.card K = 2 ^ m := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨hlin, -, -, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases (K := K) Nat.prime_two
      (by omega : 1 ≤ m) hKn
  obtain ⟨c, hc, -⟩ := hlin α
  obtain ⟨d, hd, -⟩ := hlin β
  have hlt : 2 ^ (m - 1) < Fintype.card K := by
    rw [hK]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  set θ := 2 ^ (a + 1) with hθ
  set s : Fin m := ⟨a + 1, by omega⟩ with hs
  have hss : s + s = 1 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one', hs]
    simp only
    rw [show a + 1 + (a + 1) = 1 + 1 * (2 * a + 1) by ring, Nat.add_mul_mod_self_right]
  have hs0 : ∀ x : Fin m, x + s ≠ x := by
    intro x hx
    have h1 : s = 0 := by simpa using hx
    have h2 := congrArg Fin.val h1
    simp [hs] at h2
  have hshift : ∀ (x : K) (i : Fin m), (x ^ 2 ^ (i : ℕ)) ^ θ = x ^ 2 ^ ((i + s : Fin m) : ℕ) := by
    intro x i
    rw [hθ, ← pow_mul, ← pow_add, pow_two_pow_eq_mod hK x ((i : ℕ) + (a + 1)), Fin.val_add]
  have hαθ : ∀ u : K, α u ^ θ = ∑ x : Fin m, c (x - s) ^ θ * u ^ 2 ^ (x : ℕ) := by
    intro u
    rw [hc, hθ, sum_pow_char_pow]
    simp_rw [mul_pow, ← hθ, hshift]
    rw [← Equiv.sum_comp (Equiv.addRight s) (fun x => c (x - s) ^ θ * u ^ 2 ^ (x : ℕ))]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have hβθ : ∀ u w : K, β (u ^ θ * w) =
      ∑ x : Fin m, ∑ y : Fin m, (if x = y + s then d y else 0) * (u ^ 2 ^ (x : ℕ) *
        w ^ 2 ^ (y : ℕ)) := by
    intro u w
    rw [hd, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (y + s) (fun x _ hx => by rw [ite_eq_right hx, zero_mul]) (by simp),
      ite_eq_left rfl, mul_pow, ← pow_mul, mul_comm θ, pow_mul, hshift]
  set δ : Fin m → Fin m → K := fun x y => c (x - s) ^ θ * c y + (if x = y + s then d y else 0)
    with hδ
  have hD : ∀ u w : K, α u ^ θ * α w + β (u ^ θ * w) =
      ∑ x : Fin m, ∑ y : Fin m, δ x y * (u ^ 2 ^ (x : ℕ) * w ^ 2 ^ (y : ℕ)) := by
    intro u w
    rw [hαθ, hc w, hβθ, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hδ]
    ring
  have hdiag : ∀ u : K, α u ^ θ * α u + β (u ^ θ * u) = 0 := by
    intro u
    rw [← pow_succ, ← pow_succ, h u, CharTwo.add_self_eq_zero]
  have hθadd : ∀ x y : K, (x + y) ^ θ = x ^ θ + y ^ θ := fun x y => VLike.add_pow_two_pow x y _
  have hsymm : ∀ u w : K, α u ^ θ * α w + β (u ^ θ * w) = α w ^ θ * α u + β (w ^ θ * u) := by
    intro u w
    have h1 := hdiag (u + w)
    simp only [map_add, hθadd, add_mul, mul_add] at h1
    have h2 := hdiag u
    have h3 := hdiag w
    have e : α u ^ θ * α w + β (u ^ θ * w) + (α w ^ θ * α u + β (w ^ θ * u)) = 0 := by
      linear_combination h1 - h2 - h3
    exact (CharTwo.add_eq_zero.mp e)
  have hδsymm : ∀ x y, δ x y = δ y x := by
    have h0 := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_sum_mul_pow_eq_zero
      (p := 2) hlt (a := fun x y => δ x y + δ y x) fun u w => by
        have e1 := hD u w
        have e2 := hD w u
        rw [hsymm u w, e2] at e1
        have e3 : ∑ x : Fin m, ∑ y : Fin m, δ x y * (w ^ 2 ^ (x : ℕ) * u ^ 2 ^ (y : ℕ)) =
            ∑ x : Fin m, ∑ y : Fin m, δ y x * (u ^ 2 ^ (x : ℕ) * w ^ 2 ^ (y : ℕ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        rw [e3] at e1
        simp only [add_mul, Finset.sum_add_distrib, ← e1, CharTwo.add_self_eq_zero]
    intro x y
    exact CharTwo.add_eq_zero.mp (congrFun (congrFun h0 x) y)
  have hδdiag : ∀ x, δ x x = 0 := by
    have hsq : ∀ u : K, ∑ x : Fin m, δ x x * (u ^ 2) ^ 2 ^ (x : ℕ) = 0 := by
      intro u
      have e1 := hD u u
      rw [hdiag u, sum_sum_eq_sum_diag _ fun x y => by rw [hδsymm x y]; ring] at e1
      rw [e1]
      exact Finset.sum_congr rfl fun x _ => by rw [← pow_mul, mul_comm 2, pow_mul, sq]
    have h0 := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_mul_pow_eq_zero
      (p := 2) hlt (a := fun x => δ x x) fun w => by
        obtain ⟨u, rfl⟩ := VLike.pow_two_pow_surjective (K := K) 1 w
        simpa using hsq u
    exact fun x => congrFun h0 x
  have hD1 : ∀ x, c (x - s) ^ θ * c x = 0 := by
    intro x
    have h1 := hδdiag x
    rw [hδ] at h1
    simp only [ite_eq_right (fun h : x = x + s => hs0 x h.symm), add_zero] at h1
    exact h1
  have hcθ : ∀ i, c i ≠ 0 → c i ^ θ ≠ 0 := fun i hi => pow_ne_zero _ hi
  have hstep : ∀ i j, c i ≠ 0 → c j ≠ 0 → i ≠ j → j = i + 1 := by
    intro i j hi hj hij
    have his : c (i + s) = 0 := by
      have h1 := hD1 (i + s)
      rw [add_sub_cancel_right] at h1
      exact (mul_eq_zero.mp h1).resolve_left (hcθ i hi)
    have h1 := hδsymm (i + s) j
    rw [hδ] at h1
    simp only [add_sub_cancel_right, his, mul_zero, zero_add] at h1
    rw [ite_eq_right (fun h => hij (add_right_cancel h))] at h1
    by_contra hne
    have hne' : ¬ j = i + s + s := by rwa [add_assoc, hss]
    rw [ite_eq_right hne', add_zero] at h1
    exact mul_ne_zero (hcθ i hi) hj h1
  obtain ⟨w₀, hw₀⟩ := hα
  have hsupp : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw₀
    rw [hc w₀]
    exact Finset.sum_eq_zero fun i _ => by rw [hcon i, zero_mul]
  obtain ⟨i₀, hi₀⟩ := hsupp
  have hone : ∀ j, j ≠ i₀ → c j = 0 := by
    intro j hj
    by_contra hcj
    have e1 := hstep i₀ j hi₀ hcj (Ne.symm hj)
    have e2 := hstep j i₀ hcj hi₀ hj
    have e3 : (1 + 1 : Fin m) = 0 := by
      have : i₀ = i₀ + (1 + 1) := by rw [← add_assoc, ← e1, e2]
      simpa using this
    have e4 := congrArg Fin.val e3
    rw [Fin.val_add, Fin.val_one'] at e4
    simp only [Fin.val_zero] at e4
    have h5 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h5, Nat.mod_eq_of_lt (by omega)] at e4
    omega
  refine ⟨c i₀, i₀, fun w => ?_⟩
  rw [hc w, Finset.sum_eq_single i₀ (fun j _ hj => by rw [hone j hj, zero_mul]) (by simp)]

end SwapF5

namespace RootCoords

variable {G : Type} [Group G] {P : Subgroup G} {a : ℕ} {y : G}
  {u v : G → BinaryGaloisField (2 * a + 1)} {κ : BinaryGaloisField (2 * a + 1)}

theorem u_eq_zero_iff_sq_eq_one (h : RootCoords P a y u v κ) {x : G} (hx : x ∈ P) :
    u x = 0 ↔ x ^ 2 = 1 := by
  obtain ⟨hu2, hv2⟩ := h.sq hx
  constructor
  · intro hu
    refine h.inj _ (pow_mem hx 2) _ (one_mem _) (by rw [hu2, h.u_one]) ?_
    rw [hv2, h.v_one, hu, zero_pow (by positivity)]
  · intro h1
    rw [h1, h.v_one] at hv2
    exact pow_eq_zero_iff (by positivity) |>.mp hv2.symm

theorem u_conj_eq_of_u_eq (h : RootCoords P a y u v κ) {g : G}
    (hg : g ∈ normalizer (P : Set G)) {x x' : G} (hx : x ∈ P) (hx' : x' ∈ P) (hxx' : u x = u x') :
    u (g * x * g⁻¹) = u (g * x' * g⁻¹) := by
  have hgP : ∀ z ∈ P, g * z * g⁻¹ ∈ P := fun z hz => (mem_normalizer_iff.mp hg z).mp hz
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  have hz : x⁻¹ * x' ∈ P := mul_mem (inv_mem hx) hx'
  have hzu : u (x⁻¹ * x') = 0 := by
    rw [(h.mul _ (inv_mem hx) _ hx').1, (h.inv hx).1, hxx']
    exact CharTwo.add_self_eq_zero _
  have hsq : (g * (x⁻¹ * x') * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, (h.u_eq_zero_iff_sq_eq_one hz).mp hzu]
    group
  have hu0 := (h.u_eq_zero_iff_sq_eq_one (hgP _ hz)).mpr hsq
  have e : g * (x⁻¹ * x') * g⁻¹ = (g * x * g⁻¹)⁻¹ * (g * x' * g⁻¹) := by group
  rw [e, (h.mul _ (inv_mem (hgP _ hx)) _ (hgP _ hx')).1, (h.inv (hgP _ hx)).1] at hu0
  exact CharTwo.add_eq_zero.mp hu0

theorem exists_monomial_conj (h : RootCoords P a y u v κ) (ha : 1 ≤ a) {g : G}
    (hg : g ∈ normalizer (P : Set G)) :
    ∃ (c : BinaryGaloisField (2 * a + 1)) (i : ℕ), ∀ x ∈ P, u (g * x * g⁻¹) = c * u x ^ 2 ^ i := by
  classical
  have hgP : ∀ z ∈ P, g * z * g⁻¹ ∈ P := fun z hz => (mem_normalizer_iff.mp hg z).mp hz
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  let xs : BinaryGaloisField (2 * a + 1) → G := fun w => (h.surj w 0).choose
  have hxs : ∀ w, xs w ∈ P ∧ u (xs w) = w ∧ v (xs w) = 0 := fun w => (h.surj w 0).choose_spec
  have hαspec : ∀ x ∈ P, u (g * xs (u x) * g⁻¹) = u (g * x * g⁻¹) := fun x hx =>
    h.u_conj_eq_of_u_eq hg (hxs _).1 hx (hxs _).2.1
  let α : BinaryGaloisField (2 * a + 1) →+ BinaryGaloisField (2 * a + 1) :=
    { toFun := fun w => u (g * xs w * g⁻¹)
      map_zero' := by
        have e := hαspec 1 (one_mem _)
        rw [h.u_one] at e
        rw [e, show g * 1 * g⁻¹ = 1 by group, h.u_one]
      map_add' := by
        intro w w'
        obtain ⟨hx, hxu, -⟩ := hxs w
        obtain ⟨hx', hxu', -⟩ := hxs w'
        have hm := (h.mul _ hx _ hx').1
        rw [hxu, hxu'] at hm
        show u (g * xs (w + w') * g⁻¹) = u (g * xs w * g⁻¹) + u (g * xs w' * g⁻¹)
        rw [← hm, hαspec _ (mul_mem hx hx'),
          show g * (xs w * xs w') * g⁻¹ = g * xs w * g⁻¹ * (g * xs w' * g⁻¹) by group,
          (h.mul _ (hgP _ hx) _ (hgP _ hx')).1] }
  have hα : ∀ x ∈ P, α (u x) = u (g * x * g⁻¹) := hαspec
  let zs : BinaryGaloisField (2 * a + 1) → G := fun w => (h.surj 0 w).choose
  have hzs : ∀ w, zs w ∈ P ∧ u (zs w) = 0 ∧ v (zs w) = w := fun w => (h.surj 0 w).choose_spec
  have hzs_eq : ∀ x ∈ P, u x = 0 → zs (v x) = x := fun x hx hu =>
    h.inj _ (hzs _).1 _ hx (by rw [(hzs _).2.1, hu]) (hzs _).2.2
  have hconj0 : ∀ x ∈ P, u x = 0 → u (g * x * g⁻¹) = 0 := by
    intro x hx hu
    rw [h.u_eq_zero_iff_sq_eq_one (hgP _ hx), conj_pow, (h.u_eq_zero_iff_sq_eq_one hx).mp hu]
    group
  have hvadd : ∀ x ∈ P, ∀ x' ∈ P, u x = 0 → v (x * x') = v x + v x' := by
    intro x hx x' hx' hu
    rw [(h.mul _ hx _ hx').2, hu, zero_mul, add_zero]
  let β : BinaryGaloisField (2 * a + 1) →+ BinaryGaloisField (2 * a + 1) :=
    { toFun := fun w => v (g * zs w * g⁻¹)
      map_zero' := by
        have e := hzs_eq 1 (one_mem _) h.u_one
        rw [h.v_one] at e
        show v (g * zs 0 * g⁻¹) = 0
        rw [e, show g * 1 * g⁻¹ = 1 by group, h.v_one]
      map_add' := by
        intro w w'
        obtain ⟨hz, hzu, hzv⟩ := hzs w
        obtain ⟨hz', hzu', hzv'⟩ := hzs w'
        have hm := hvadd _ hz _ hz' hzu
        rw [hzv, hzv'] at hm
        have hmu : u (zs w * zs w') = 0 := by rw [(h.mul _ hz _ hz').1, hzu, hzu', add_zero]
        show v (g * zs (w + w') * g⁻¹) = v (g * zs w * g⁻¹) + v (g * zs w' * g⁻¹)
        rw [← hm, hzs_eq _ (mul_mem hz hz') hmu,
          show g * (zs w * zs w') * g⁻¹ = g * zs w * g⁻¹ * (g * zs w' * g⁻¹) by group,
          hvadd _ (hgP _ hz) _ (hgP _ hz') (hconj0 _ hz hzu)] }
  have hβ : ∀ x ∈ P, u x = 0 → β (v x) = v (g * x * g⁻¹) := by
    intro x hx hu
    show v (g * zs (v x) * g⁻¹) = _
    rw [hzs_eq x hx hu]
  have hquad : ∀ w, β (w ^ (2 ^ (a + 1) + 1)) = α w ^ (2 ^ (a + 1) + 1) := by
    intro w
    obtain ⟨hx, hxu, -⟩ := hxs w
    obtain ⟨hu2, hv2⟩ := h.sq hx
    have e1 : β (u (xs w) ^ (2 ^ (a + 1) + 1)) = v (g * xs w ^ 2 * g⁻¹) := by
      rw [← hv2]
      exact hβ _ (pow_mem hx 2) hu2
    have e2 : v (g * xs w ^ 2 * g⁻¹) = u (g * xs w * g⁻¹) ^ (2 ^ (a + 1) + 1) := by
      rw [← conj_pow]
      exact (h.sq (hgP _ hx)).2
    conv_lhs => rw [← hxu]
    rw [e1, e2]
    rfl
  have hαne : ∃ w, α w ≠ 0 := by
    refine ⟨1, fun h0 => ?_⟩
    obtain ⟨hx, hxu, -⟩ := hxs 1
    have h1 : u (g * xs 1 * g⁻¹) = 0 := h0
    have h2 := (h.u_eq_zero_iff_sq_eq_one (hgP _ hx)).mp h1
    rw [conj_pow] at h2
    have h3 : xs 1 ^ 2 = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) h2
      simpa [mul_assoc] using this
    have h4 := (h.u_eq_zero_iff_sq_eq_one hx).mpr h3
    rw [hxu] at h4
    exact one_ne_zero h4
  obtain ⟨c, i, hci⟩ := SwapF5.exists_monomial_of_quadratic ha hK hαne hquad
  exact ⟨c, i, fun x hx => by rw [← hα x hx, hci]⟩

theorem conj_eq_of_pow_two_pow_eq_one (h : RootCoords P a y u v κ) (ha : 1 ≤ a) {g : G}
    (hg : g ∈ normalizer (P : Set G)) {k : ℕ} (hgk : g ^ 2 ^ k = 1) :
    (∀ x ∈ P, u (g * x * g⁻¹) = u x) ∧ ∀ x ∈ P, u x = 0 → g * x * g⁻¹ = x := by
  classical
  have hgP : ∀ z ∈ P, g * z * g⁻¹ ∈ P := fun z hz => (mem_normalizer_iff.mp hg z).mp hz
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  obtain ⟨c, i, hci⟩ := h.exists_monomial_conj ha hg
  have hgnP : ∀ n : ℕ, ∀ z ∈ P, g ^ n * z * (g ^ n)⁻¹ ∈ P := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      have e : g ^ (n + 1) * z * (g ^ (n + 1))⁻¹ = g * (g ^ n * z * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e]
      exact hgP _ (ih z hz)
  have hiter : ∀ n : ℕ, ∃ cn : BinaryGaloisField (2 * a + 1),
      ∀ x ∈ P, u (g ^ n * x * (g ^ n)⁻¹) = cn * u x ^ 2 ^ (i * n) := by
    intro n
    induction n with
    | zero => exact ⟨1, fun x _ => by simp⟩
    | succ n ih =>
      obtain ⟨cn, hcn⟩ := ih
      refine ⟨c * cn ^ 2 ^ i, fun x hx => ?_⟩
      have e : g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e, hci _ (hgnP n x hx), hcn x hx, mul_pow, ← pow_mul, ← pow_add, Nat.mul_succ]
      ring
  obtain ⟨cN, hcN⟩ := hiter (2 ^ k)
  have hfix : ∀ w : BinaryGaloisField (2 * a + 1), w = cN * w ^ 2 ^ (i * 2 ^ k) := by
    intro w
    obtain ⟨x, hx, hxu, -⟩ := h.surj w 0
    have := hcN x hx
    rw [hgk, one_mul, inv_one, mul_one, hxu] at this
    exact this
  have hcN1 : cN = 1 := by
    have := hfix 1
    rw [one_pow, mul_one] at this
    exact this.symm
  have hred : ∀ (w : BinaryGaloisField (2 * a + 1)) (j : ℕ),
      w ^ 2 ^ j = w ^ 2 ^ (j % (2 * a + 1)) :=
    fun w j => SwapF5.pow_two_pow_eq_mod hK w j
  have hmod : (i * 2 ^ k) % (2 * a + 1) = 0 := by
    by_contra hr
    have hrm : (i * 2 ^ k) % (2 * a + 1) < 2 * a + 1 := Nat.mod_lt _ (by omega)
    set jr : Fin (2 * a + 1) := ⟨(i * 2 ^ k) % (2 * a + 1), hrm⟩ with hjr
    set j0 : Fin (2 * a + 1) := ⟨0, by omega⟩ with hj0
    have hne : jr ≠ j0 := fun h => hr (congrArg Fin.val h)
    have hlt : 2 ^ (2 * a + 1 - 1) < Fintype.card (BinaryGaloisField (2 * a + 1)) := by
      rw [hK]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h0 := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_mul_pow_eq_zero
      (p := 2) (n := 2 * a + 1) hlt
      (a := fun j : Fin (2 * a + 1) => (if j = jr then 1 else 0) + (if j = j0 then 1 else 0))
      fun w => by
        have e := hfix w
        rw [hcN1, one_mul, hred] at e
        simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [hjr, hj0]
        simp only [pow_zero, pow_one]
        rw [← e]
        exact CharTwo.add_self_eq_zero w
    have h1 := congrFun h0 jr
    simp only [ite_eq_right hne, add_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hmi : 2 * a + 1 ∣ i := by
    have h1 : 2 * a + 1 ∣ i * 2 ^ k := Nat.dvd_of_mod_eq_zero hmod
    have h2 : Nat.Coprime (2 * a + 1) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (odd_two_mul_add_one a))
    exact h2.dvd_of_dvd_mul_right h1
  have hfrob : ∀ w : BinaryGaloisField (2 * a + 1), w ^ 2 ^ i = w := by
    intro w
    rw [hred, Nat.mod_eq_zero_of_dvd hmi, pow_zero, pow_one]
  have hci' : ∀ x ∈ P, u (g * x * g⁻¹) = c * u x := fun x hx => by rw [hci x hx, hfrob]
  have hpow : ∀ n : ℕ, ∀ x ∈ P, u (g ^ n * x * (g ^ n)⁻¹) = c ^ n * u x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have e : g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e, hci' _ (hgnP n x hx), ih x hx, pow_succ]
      ring
  have hc1 : c = 1 := by
    obtain ⟨x, hx, hxu, -⟩ := h.surj 1 0
    have e := hpow (2 ^ k) x hx
    rw [hgk, one_mul, inv_one, mul_one, hxu, mul_one] at e
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by positivity)] at e
      exact one_ne_zero e
    have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one e.symm
    have h2 : orderOf c ∣ 2 ^ (2 * a + 1) - 1 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hK]
      exact FiniteField.pow_card_sub_one_eq_one c hc0
    have hodd : Odd (2 ^ (2 * a + 1) - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have h3 : Nat.Coprime (2 ^ k) (2 ^ (2 * a + 1) - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have h4 := Nat.dvd_gcd h1 h2
    rw [h3.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  have hθinj : Function.Injective fun w : BinaryGaloisField (2 * a + 1) =>
      w ^ (2 ^ (a + 1) + 1) := by
    intro w w' hww'
    simp only at hww'
    by_cases hw' : w' = 0
    · subst hw'
      rw [zero_pow (by positivity)] at hww'
      exact (pow_eq_zero_iff (by positivity)).mp hww'
    · set ρ := w / w' with hρdef
      have hρ : ρ ^ (2 ^ (a + 1) + 1) = 1 := by
        rw [hρdef, div_pow, hww', div_self (pow_ne_zero _ hw')]
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by positivity)] at hρ
        exact zero_ne_one hρ
      have e1 : ρ ^ 2 ^ (a + 1) * ρ = 1 := by rw [← pow_succ]; exact hρ
      have h1 : ρ ^ 2 ^ (a + 1) = ρ⁻¹ := eq_inv_of_mul_eq_one_left e1
      have e2 : (ρ⁻¹) ^ 2 ^ (a + 1) = ρ := by
        rw [inv_pow, h1, inv_inv]
      have e3 : ρ ^ 2 ^ (2 * a + 2) = ρ := by
        rw [show 2 * a + 2 = (a + 1) + (a + 1) by ring, pow_add, pow_mul, h1, e2]
      have e4 : ρ ^ 2 = ρ := by
        have h5 := hred ρ (2 * a + 2)
        have h6 : (2 * a + 2) % (2 * a + 1) = 1 := by
          rw [show 2 * a + 2 = 1 + 1 * (2 * a + 1) by ring, Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt (by omega)
        rw [e3, h6, pow_one] at h5
        exact h5.symm
      have h7 : ρ = 1 := by
        have h8 : ρ * (ρ - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, e4, sub_self]
        rcases mul_eq_zero.mp h8 with h9 | h9
        · exact absurd h9 hρ0
        · exact sub_eq_zero.mp h9
      exact (div_eq_one_iff_eq hw').mp h7
  have hθsurj := Finite.injective_iff_surjective.mp hθinj
  refine ⟨fun x hx => by rw [hci' x hx, hc1, one_mul], fun x hx hu => ?_⟩
  obtain ⟨w, hw⟩ := hθsurj (v x)
  simp only at hw
  obtain ⟨z, hz, hzu, -⟩ := h.surj w 0
  have hz2 : z ^ 2 = x := by
    obtain ⟨hu2, hv2⟩ := h.sq hz
    refine h.inj _ (pow_mem hz 2) _ hx (by rw [hu2, hu]) ?_
    rw [hv2, hzu, hw]
  have hgz : u (g * z * g⁻¹) = w := by rw [hci' z hz, hc1, one_mul, hzu]
  obtain ⟨hu2', hv2'⟩ := h.sq (hgP _ hz)
  rw [← hz2, ← conj_pow]
  refine h.inj _ (pow_mem (hgP _ hz) 2) _ (pow_mem hz 2) ?_ ?_
  · rw [hu2', (h.sq hz).1]
  · rw [hv2', hgz, (h.sq hz).2, hzu]

end RootCoords

end CFSG.ComponentClassification.GMS78
