module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferCocycle

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

variable {G : Type*} [Group G] {S : Subgroup G} {I : Type*} {r : I → G}

@[expose] def IsRightTransversal (S : Subgroup G) (r : I → G) : Prop :=
  ∀ g : G, ∃! i : I, g * (r i)⁻¹ ∈ S

namespace IsRightTransversal

theorem of_injective [Finite G] (hinj : ∀ i j, r i * (r j)⁻¹ ∈ S → i = j)
    (hcard : S.index ≤ Nat.card I) : IsRightTransversal S r := by
  let φ : I → Quotient (QuotientGroup.rightRel S) := fun i => Quotient.mk'' (r i)
  have hφ : Function.Injective φ := by
    intro i j h
    have h' := Quotient.exact' h
    rw [QuotientGroup.rightRel_apply] at h'
    exact (hinj j i h').symm
  have hcardQ : Nat.card (Quotient (QuotientGroup.rightRel S)) = S.index := by
    rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S),
      Subgroup.index_eq_card]
  have hbij := hφ.bijective_of_nat_card_le (hcardQ.trans_le hcard)
  intro g
  obtain ⟨i, hi⟩ := hbij.2 (Quotient.mk'' g)
  have hgi : g * (r i)⁻¹ ∈ S := QuotientGroup.rightRel_apply.1 (Quotient.exact' hi)
  refine ⟨i, hgi, fun j hj => hinj j i ?_⟩
  have := S.mul_mem (S.inv_mem hj) hgi
  rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at this

theorem of_surjective [Finite G] (hcov : ∀ g, ∃ i, g * (r i)⁻¹ ∈ S)
    (hcard : Nat.card I ≤ S.index) [Finite I] : IsRightTransversal S r := by
  let φ : I → Quotient (QuotientGroup.rightRel S) := fun i => Quotient.mk'' (r i)
  have hφ : Function.Surjective φ := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      obtain ⟨i, hi⟩ := hcov g
      exact ⟨i, Quotient.sound' (QuotientGroup.rightRel_apply.2 hi)⟩
  have hcardQ : Nat.card (Quotient (QuotientGroup.rightRel S)) = S.index := by
    rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S),
      Subgroup.index_eq_card]
  have hbij := hφ.bijective_of_nat_card_le (hcard.trans_eq hcardQ.symm)
  intro g
  obtain ⟨i, hi⟩ := hcov g
  refine ⟨i, hi, fun j hj => hbij.1 ?_⟩
  refine Quotient.sound' (QuotientGroup.rightRel_apply.2 ?_)
  have := S.mul_mem (S.inv_mem hi) hj
  rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at this

theorem exists_mul_inv_mem_of_closure [Finite G] {X : Set G} (hX : closure X = ⊤) {i₀ : I}
    (hi₀ : r i₀ ∈ S) (hstep : ∀ i, ∀ x ∈ X, ∃ j, r i * x * (r j)⁻¹ ∈ S) (g : G) :
    ∃ i, g * (r i)⁻¹ ∈ S := by
  have hright : ∀ y ∈ X, ∀ x : G, (∃ i, x * (r i)⁻¹ ∈ S) → ∃ i, x * y * (r i)⁻¹ ∈ S := by
    rintro y hy x ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hstep i y hy
    refine ⟨j, ?_⟩
    have := S.mul_mem hi hj
    simpa only [mul_assoc, inv_mul_cancel_left] using this
  have hpow : ∀ y ∈ X, ∀ n : ℕ, ∀ x : G, (∃ i, x * (r i)⁻¹ ∈ S) →
      ∃ i, x * y ^ n * (r i)⁻¹ ∈ S := by
    intro y hy n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, ← mul_assoc]
      exact hright y hy _ (ih x hx)
  have hg : g ∈ closure X := hX ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨i₀, by rw [one_mul]; exact S.inv_mem hi₀⟩
  | mul_right x _ y hy ih => exact hright y hy x ih
  | mul_inv_cancel x _ y hy ih =>
    have hinv : y ^ (orderOf y - 1) = y⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos y),
        pow_orderOf_eq_one]
    have h := hpow y hy (orderOf y - 1) x ih
    rwa [hinv] at h

variable (hr : IsRightTransversal S r)
include hr

@[expose] noncomputable def index (g : G) : I := (hr g).exists.choose

theorem mul_inv_mem_index (g : G) : g * (r (hr.index g))⁻¹ ∈ S :=
  (hr g).exists.choose_spec

theorem index_eq_iff {g : G} {i : I} : hr.index g = i ↔ g * (r i)⁻¹ ∈ S :=
  ⟨fun h => h ▸ hr.mul_inv_mem_index g, fun h => (hr g).unique (hr.mul_inv_mem_index g) h⟩

theorem eq_of_mul_inv_mem {i j : I} (h : r i * (r j)⁻¹ ∈ S) : i = j :=
  (hr.index_eq_iff.2 (by rw [mul_inv_cancel]; exact S.one_mem)).symm.trans (hr.index_eq_iff.2 h)

theorem injective : Function.Injective r := fun i j h =>
  hr.eq_of_mul_inv_mem (by rw [h, mul_inv_cancel]; exact S.one_mem)

theorem card_eq_index : Nat.card I = S.index := by
  let φ : I → Quotient (QuotientGroup.rightRel S) := fun i => Quotient.mk'' (r i)
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j h
      exact (hr.eq_of_mul_inv_mem (QuotientGroup.rightRel_apply.1 (Quotient.exact' h))).symm
    · intro q
      induction q using Quotient.inductionOn' with
      | h g => exact ⟨hr.index g,
          Quotient.sound' (QuotientGroup.rightRel_apply.2 (hr.mul_inv_mem_index g))⟩
  rw [Nat.card_congr (Equiv.ofBijective φ hφ),
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S),
    Subgroup.index_eq_card]

theorem fintype_card_eq_index [Fintype I] : Fintype.card I = S.index := by
  rw [← Nat.card_eq_fintype_card, hr.card_eq_index]

@[expose] noncomputable def act (i : I) (g : G) : I := hr.index (r i * g)

@[expose] noncomputable def coef (i : I) (g : G) : S :=
  ⟨r i * g * (r (hr.act i g))⁻¹, hr.mul_inv_mem_index _⟩

theorem coe_coef (i : I) (g : G) : (hr.coef i g : G) = r i * g * (r (hr.act i g))⁻¹ := rfl

theorem r_mul (i : I) (g : G) : r i * g = hr.coef i g * r (hr.act i g) := by
  rw [coe_coef, inv_mul_cancel_right]

theorem act_eq_of_eq {i j : I} {g s : G} (hs : s ∈ S) (h : r i * g = s * r j) :
    hr.act i g = j :=
  hr.index_eq_iff.2 (by rw [h, mul_inv_cancel_right]; exact hs)

theorem coe_coef_eq_of_eq {i j : I} {g s : G} (hs : s ∈ S) (h : r i * g = s * r j) :
    (hr.coef i g : G) = s := by
  rw [coe_coef, hr.act_eq_of_eq hs h, h, mul_inv_cancel_right]

theorem act_one (i : I) : hr.act i 1 = i :=
  hr.act_eq_of_eq (j := i) S.one_mem (by simp)

theorem coef_one (i : I) : hr.coef i 1 = 1 :=
  Subtype.ext (hr.coe_coef_eq_of_eq (j := i) S.one_mem (by simp))

theorem r_mul_mul (i : I) (g k : G) :
    r i * (g * k) = ((hr.coef i g * hr.coef (hr.act i g) k : S) : G) *
      r (hr.act (hr.act i g) k) := by
  rw [← mul_assoc, hr.r_mul i g, mul_assoc, hr.r_mul (hr.act i g) k, Subgroup.coe_mul,
    mul_assoc]

theorem act_mul (i : I) (g k : G) : hr.act i (g * k) = hr.act (hr.act i g) k :=
  hr.act_eq_of_eq (SetLike.coe_mem _) (hr.r_mul_mul i g k)

theorem coef_mul (i : I) (g k : G) :
    hr.coef i (g * k) = hr.coef i g * hr.coef (hr.act i g) k :=
  Subtype.ext (hr.coe_coef_eq_of_eq (SetLike.coe_mem _) (hr.r_mul_mul i g k))

noncomputable def actPerm (g : G) : Equiv.Perm I where
  toFun i := hr.act i g
  invFun i := hr.act i g⁻¹
  left_inv i := by
    change hr.act (hr.act i g) g⁻¹ = i
    rw [← hr.act_mul, mul_inv_cancel, hr.act_one]
  right_inv i := by
    change hr.act (hr.act i g⁻¹) g = i
    rw [← hr.act_mul, inv_mul_cancel, hr.act_one]

theorem sum_act [Fintype I] {M : Type*} [AddCommMonoid M] (φ : I → M) (g : G) :
    ∑ i, φ (hr.act i g) = ∑ i, φ i :=
  Equiv.sum_comp (hr.actPerm g) φ

variable [Fintype I]

@[expose] noncomputable def transfer₂ (f : S → S → ZMod 2) (g k : G) : ZMod 2 :=
  ∑ i, f (hr.coef i g) (hr.coef (hr.act i g) k)

@[expose] noncomputable def transfer₁ (b : S → ZMod 2) (g : G) : ZMod 2 :=
  ∑ i, b (hr.coef i g)

theorem transfer₂_apply (f : S → S → ZMod 2) (g k : G) :
    hr.transfer₂ f g k = ∑ i, f (hr.coef i g) (hr.coef (hr.act i g) k) := rfl

theorem transfer₁_apply (b : S → ZMod 2) (g : G) :
    hr.transfer₁ b g = ∑ i, b (hr.coef i g) := rfl

theorem transfer₂_add_coboundary (f : S → S → ZMod 2) (b : S → ZMod 2) (g k : G) :
    hr.transfer₂ (fun s t => f s t + coboundary b s t) g k =
      hr.transfer₂ f g k + coboundary (hr.transfer₁ b) g k := by
  simp only [transfer₂, transfer₁, coboundary_apply, Finset.sum_add_distrib]
  rw [hr.sum_act (fun i => b (hr.coef i k)) g]
  simp only [← hr.coef_mul]

theorem transfer₁_one {b : S → ZMod 2} (hb : b 1 = 0) : hr.transfer₁ b 1 = 0 := by
  simp [transfer₁, hr.coef_one, hb]

@[expose] noncomputable def transferCocycle (f : NormCocycle S) : NormCocycle G where
  toFun := hr.transfer₂ f
  map_one_left k := by simp [transfer₂, hr.coef_one, hr.act_one, f.map_one_left]
  map_one_right g := by simp [transfer₂, hr.coef_one, f.map_one_right]
  cocycle g h k := by
    simp only [transfer₂]
    rw [← hr.sum_act (fun j => f (hr.coef j h) (hr.coef (hr.act j h) k)) g,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr.coef_mul i g h, hr.act_mul i g h, hr.coef_mul (hr.act i g) h k]
    exact f.cocycle _ _ _

@[simp] theorem transferCocycle_apply (f : NormCocycle S) (g k : G) :
    hr.transferCocycle f g k = hr.transfer₂ f g k := rfl

theorem transfer₂_isNormCocycle (f : NormCocycle S) :
    (∀ k, hr.transfer₂ f 1 k = 0) ∧ (∀ g, hr.transfer₂ f g 1 = 0) ∧
      ∀ g h k, hr.transfer₂ f g h + hr.transfer₂ f (g * h) k =
        hr.transfer₂ f h k + hr.transfer₂ f g (h * k) :=
  ⟨(hr.transferCocycle f).map_one_left, (hr.transferCocycle f).map_one_right,
    (hr.transferCocycle f).cocycle⟩

section Comparison

variable {E : Type*} [Group E] {π : E →* G} {z : E}

omit [Fintype I] in
theorem exists_unique_exponents (hπ : IsCentralDoubleExt π z) (u : G → E)
    (hu : ∀ g, π (u g) = g) (R : I → E) (hR : ∀ i, π (R i) = r i) :
    (∃! h : G → G → ZMod 2, ∀ g k, u g * u k = z ^ (h g k).val * u (g * k)) ∧
      ∃! c : I → G → ZMod 2,
        ∀ i g, R i * u g = z ^ (c i g).val * u (hr.coef i g) * R (hr.act i g) := by
  refine ⟨⟨fun g k => binCoord (u g * u k) (u (g * k)), fun g k =>
      hπ.eq_pow_binCoord_mul (by rw [map_mul, hu, hu, hu]), fun h' hh' => ?_⟩,
    ⟨fun i g => binCoord (R i * u g) (u (hr.coef i g) * R (hr.act i g)), fun i g => ?_,
      fun c' hc' => ?_⟩⟩
  · funext g k
    exact (hπ.binCoord_eq (hh' g k)).symm
  · rw [mul_assoc]
    exact hπ.eq_pow_binCoord_mul (by simp only [map_mul, hu, hR]; exact hr.r_mul i g)
  · funext i g
    have h1 : R i * u g = z ^ (c' i g).val * (u (hr.coef i g) * R (hr.act i g)) := by
      rw [hc' i g, mul_assoc]
    exact (hπ.binCoord_eq h1).symm

theorem eq_transfer_add_coboundary (hπ : IsCentralDoubleExt π z) (hodd : Odd (Fintype.card I))
    (u : G → E) (hu1 : u 1 = 1) (h : G → G → ZMod 2)
    (hh : ∀ g k, u g * u k = z ^ (h g k).val * u (g * k)) (R : I → E) (c : I → G → ZMod 2)
    (hc : ∀ i g, R i * u g = z ^ (c i g).val * u (hr.coef i g) * R (hr.act i g)) :
    ∑ i, c i 1 = 0 ∧ ∀ g k,
      h g k = hr.transfer₂ (fun s t => h s t) g k + coboundary (fun g => ∑ i, c i g) g k := by
  refine ⟨Finset.sum_eq_zero fun i _ => ?_, fun g k => ?_⟩
  · apply hπ.pow_val_mul_cancel (x := R i)
    have h1 := hc i 1
    rw [hu1, mul_one, hr.coef_one, hr.act_one, OneMemClass.coe_one, hu1, mul_one] at h1
    rw [← h1, ZMod.val_zero, pow_zero, one_mul]
  have key : ∀ i, h g k + c i (g * k) =
      c i g + c (hr.act i g) k + h (hr.coef i g) (hr.coef (hr.act i g) k) := by
    intro i
    set X := u (↑(hr.coef i g) * ↑(hr.coef (hr.act i g) k)) * R (hr.act (hr.act i g) k)
    have hA : R i * (u g * u k) = z ^ (h g k + c i (g * k)).val * X := by
      rw [hh, hπ.mul_pow_val_mul, hc, hπ.pow_val_add, hr.coef_mul, hr.act_mul,
        Subgroup.coe_mul]
      simp only [X, mul_assoc]
    have hB : R i * u g * u k = z ^ (c i g + c (hr.act i g) k +
        h (hr.coef i g) (hr.coef (hr.act i g) k)).val * X := by
      rw [hc i g, mul_assoc (z ^ (c i g).val * u (hr.coef i g)), hc (hr.act i g) k]
      simp only [mul_assoc]
      rw [hπ.mul_pow_val_mul (c (hr.act i g) k) (u (hr.coef i g)),
        ← mul_assoc (u (hr.coef i g)) (u (hr.coef (hr.act i g) k)), hh, hπ.pow_val_add,
        hπ.pow_val_add]
      simp only [X, mul_assoc]
    exact hπ.pow_val_mul_cancel (hA.symm.trans ((mul_assoc _ _ _).symm.trans hB))
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hr.sum_act (fun i => c i k) g, nsmul_eq_mul,
    Odd.natCast_zmod_two hodd, one_mul] at hsum
  rw [coboundary_apply, transfer₂_apply]
  linear_combination hsum - (∑ i, c i (g * k)) * zmod_two_two

theorem exists_section_eq_transfer_add_coboundary (hπ : IsCentralDoubleExt π z)
    (hodd : Odd (Fintype.card I)) (u₀ : S → E) (hu₀ : ∀ s, π (u₀ s) = s) (hu₀1 : u₀ 1 = 1)
    (f : S → S → ZMod 2) (hf : ∀ s t, u₀ s * u₀ t = z ^ (f s t).val * u₀ (s * t)) :
    ∃ (u : G → E) (h : G → G → ZMod 2) (C : G → ZMod 2),
      (∀ g, π (u g) = g) ∧ u 1 = 1 ∧ (∀ s : S, u s = u₀ s) ∧
      (∀ g k, u g * u k = z ^ (h g k).val * u (g * k)) ∧ (∀ s t : S, h s t = f s t) ∧
      C 1 = 0 ∧ ∀ g k, h g k = hr.transfer₂ f g k + coboundary C g k := by
  classical
  let u : G → E := fun g => if hg : g ∈ S then u₀ ⟨g, hg⟩ else Function.surjInv hπ.surjective g
  have hu : ∀ g, π (u g) = g := by
    intro g
    by_cases hg : g ∈ S
    · simp only [u, hg, dite_true, hu₀]
    · simp only [u, hg, dite_false]
      exact Function.surjInv_eq hπ.surjective g
  have huS : ∀ s : S, u s = u₀ s := fun s => by simp [u]
  have hu1 : u 1 = 1 := by rw [← OneMemClass.coe_one S, huS, hu₀1]
  let h : G → G → ZMod 2 := fun g k => binCoord (u g * u k) (u (g * k))
  have hh : ∀ g k, u g * u k = z ^ (h g k).val * u (g * k) := fun g k =>
    hπ.eq_pow_binCoord_mul (by rw [map_mul, hu, hu, hu])
  let R : I → E := fun i => u (r i)
  let c : I → G → ZMod 2 := fun i g => binCoord (R i * u g) (u (hr.coef i g) * R (hr.act i g))
  have hc : ∀ i g, R i * u g = z ^ (c i g).val * u (hr.coef i g) * R (hr.act i g) := by
    intro i g
    rw [mul_assoc]
    exact hπ.eq_pow_binCoord_mul (by simp only [R, map_mul, hu]; exact hr.r_mul i g)
  obtain ⟨hC1, hC⟩ := hr.eq_transfer_add_coboundary hπ hodd u hu1 h hh R c hc
  have hhS : (fun s t : S => h s t) = f := by
    funext s t
    apply hπ.binCoord_eq
    have h1 : u (↑s * ↑t) = u₀ (s * t) := huS (s * t)
    rw [huS s, huS t, h1]
    exact hf s t
  refine ⟨u, h, fun g => ∑ i, c i g, hu, hu1, huS, hh, fun s t => congrFun (congrFun hhS s) t,
    hC1, fun g k => ?_⟩
  rw [hC g k, hhS]

theorem exists_coboundary_eq_transfer (hπ : IsCentralDoubleExt π z)
    (hodd : Odd (Fintype.card I)) (u₀ : S → E) (hu₀ : ∀ s, π (u₀ s) = s) (hu₀1 : u₀ 1 = 1)
    (f : S → S → ZMod 2) (hf : ∀ s t, u₀ s * u₀ t = z ^ (f s t).val * u₀ (s * t)) :
    ∃ C : G → ZMod 2, C 1 = 0 ∧ ∀ s t : S, f s t = hr.transfer₂ f s t + coboundary C s t := by
  obtain ⟨-, h, C, -, -, -, -, hhS, hC1, hC⟩ :=
    hr.exists_section_eq_transfer_add_coboundary hπ hodd u₀ hu₀ hu₀1 f hf
  exact ⟨C, hC1, fun s t => by rw [← hhS s t, hC s t]⟩

theorem central_double_extension_odd_index_transfer_comparison (hπ : IsCentralDoubleExt π z)
    (hodd : Odd (Fintype.card I)) :
    (∀ (f f' : S → S → ZMod 2) (b : S → ZMod 2), (∀ s t, f' s t = f s t + coboundary b s t) →
      ∀ g k, hr.transfer₂ f' g k = hr.transfer₂ f g k + coboundary (hr.transfer₁ b) g k) ∧
    (∀ (u : G → E) (h : G → G → ZMod 2) (R : I → E) (c : I → G → ZMod 2), u 1 = 1 →
      (∀ g k, u g * u k = z ^ (h g k).val * u (g * k)) →
      (∀ i g, R i * u g = z ^ (c i g).val * u (hr.coef i g) * R (hr.act i g)) →
      ∑ i, c i 1 = 0 ∧ ∀ g k,
        h g k = hr.transfer₂ (fun s t => h s t) g k + coboundary (fun g => ∑ i, c i g) g k) ∧
    ∀ (u₀ : S → E) (f : S → S → ZMod 2), (∀ s, π (u₀ s) = s) → u₀ 1 = 1 →
      (∀ s t, u₀ s * u₀ t = z ^ (f s t).val * u₀ (s * t)) →
      ∃ (u : G → E) (h : G → G → ZMod 2) (C : G → ZMod 2),
        (∀ g, π (u g) = g) ∧ u 1 = 1 ∧ (∀ s : S, u s = u₀ s) ∧
        (∀ g k, u g * u k = z ^ (h g k).val * u (g * k)) ∧ (∀ s t : S, h s t = f s t) ∧
        C 1 = 0 ∧ (∀ g k, h g k = hr.transfer₂ f g k + coboundary C g k) ∧
        ∀ s t : S, f s t = hr.transfer₂ f s t + coboundary C s t := by
  refine ⟨fun f f' b hf' g k => ?_, fun u h R c hu1 hh hc =>
    hr.eq_transfer_add_coboundary hπ hodd u hu1 h hh R c hc, fun u₀ f hu₀ hu₀1 hf => ?_⟩
  · rw [← hr.transfer₂_add_coboundary]
    exact congrArg (fun f'' => hr.transfer₂ f'' g k) (funext₂ hf')
  · obtain ⟨u, h, C, hu, hu1, huS, hh, hhS, hC1, hC⟩ :=
      hr.exists_section_eq_transfer_add_coboundary hπ hodd u₀ hu₀ hu₀1 f hf
    exact ⟨u, h, C, hu, hu1, huS, hh, hhS, hC1, hC, fun s t => by rw [← hhS s t, hC s t]⟩

end Comparison

end IsRightTransversal

end CFSG.ComponentClassification.CentralCover
