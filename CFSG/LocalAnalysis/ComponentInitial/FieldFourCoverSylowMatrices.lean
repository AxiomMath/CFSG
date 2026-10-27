module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

open Matrix Subgroup LinearFlag CFSG.LieType.Chevalley
open scoped commutatorElement

variable {k : Type} [Field k]

theorem commutatorElement_unipU (a b c a' b' c' : k) :
    ⁅unipU k a b c, unipU k a' b' c'⁆ = unipU k 0 0 (a * b' - a' * b) := by
  rw [commutatorElement_def, unipU_inv, unipU_inv, unipU_mul, unipU_mul, unipU_mul]
  congr 1 <;> ring

theorem unipU_sq_of_card [Finite k] (hk : Nat.card k = 4) (a b c : k) :
    unipU k a b c ^ 2 = unipU k 0 0 (a * b) := by
  have := charP_two_of_card hk
  rw [sq, unipU_mul]
  congr 1
  · exact CharTwo.add_self_eq_zero a
  · exact CharTwo.add_self_eq_zero b
  · rw [CharTwo.add_self_eq_zero c, zero_add]

theorem proj_commutatorElement_mem (x y : projectiveSL 3 k) (hx : x ∈ projUnip k)
    (hy : y ∈ projUnip k) : ⁅x, y⁆ ∈ projCenterW k := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  obtain ⟨a', b', c', rfl⟩ := mem_projUnip.1 hy
  rw [← map_commutatorElement, commutatorElement_unipU]
  exact mem_projCenterW.2 ⟨_, rfl⟩

theorem sq_mem_projCenterW [Finite k] (hk : Nat.card k = 4) {x : projectiveSL 3 k}
    (hx : x ∈ projUnip k) : x ^ 2 ∈ projCenterW k := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [← map_pow, unipU_sq_of_card hk]
  exact mem_projCenterW.2 ⟨_, rfl⟩

theorem mem_projRad_of_sq_eq_one [Finite k] (hk : Nat.card k = 4) {x : projectiveSL 3 k}
    (hx : x ∈ projUnip k) (h2 : x ^ 2 = 1) : x ∈ projRad k 0 ∨ x ∈ projRad k 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [← map_pow, unipU_sq_of_card hk, proj_unipU_eq_one_iff] at h2
  rcases mul_eq_zero.1 h2.2.2 with ha | hb
  · exact Or.inr (mem_projRad_one.2 ⟨b, c, by rw [ha]⟩)
  · exact Or.inl (mem_projRad_zero.2 ⟨a, c, by rw [hb]⟩)

theorem commutator_projUnip : ⁅projUnip k, projUnip k⁆ = projCenterW k := by
  refine le_antisymm ((Subgroup.commutator_le).2 fun x hx y hy =>
    proj_commutatorElement_mem x y hx hy) fun x hx => ?_
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hx
  have h : ⁅proj 3 k (unipU k c 0 0), proj 3 k (unipU k 0 1 0)⁆ = proj 3 k (unipU k 0 0 c) := by
    rw [← map_commutatorElement, commutatorElement_unipU]
    congr 2
    ring
  rw [← h]
  exact Subgroup.commutator_mem_commutator (mem_projUnip.2 ⟨_, _, _, rfl⟩)
    (mem_projUnip.2 ⟨_, _, _, rfl⟩)

theorem mem_projRad_of_commute (i : Fin 2) {x : projectiveSL 3 k} (hx : x ∈ projRad k i)
    (hxW : x ∉ projCenterW k) {y : projectiveSL 3 k} (hy : y ∈ projUnip k) (hxy : x * y = y * x) :
    y ∈ projRad k i := by
  obtain ⟨a', b', c', rfl⟩ := mem_projUnip.1 hy
  rw [← commutatorElement_eq_one_iff_mul_comm] at hxy
  fin_cases i
  · obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
    have ha : a ≠ 0 := fun h => hxW (mem_projCenterW.2 ⟨c, by rw [h]⟩)
    rw [← map_commutatorElement, commutatorElement_unipU, proj_unipU_eq_one_iff] at hxy
    have hb : b' = 0 := by
      have h := hxy.2.2
      rw [mul_zero, sub_zero] at h
      exact (mul_eq_zero.1 h).resolve_left ha
    exact mem_projRad_zero.2 ⟨a', c', by rw [hb]⟩
  · obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
    have hb : b ≠ 0 := fun h => hxW (mem_projCenterW.2 ⟨c, by rw [h]⟩)
    rw [← map_commutatorElement, commutatorElement_unipU, proj_unipU_eq_one_iff] at hxy
    have ha : a' = 0 := by
      have h := hxy.2.2
      rw [zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_right hb
    exact mem_projRad_one.2 ⟨b', c', by rw [ha]⟩

theorem projUnip_le_normalizer_projRad (i : Fin 2) :
    projUnip k ≤ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
  have hconj : ∀ u ∈ projUnip k, ∀ r ∈ projRad k i, u * r * u⁻¹ ∈ projRad k i := by
    intro u hu r hr
    have h : u * r * u⁻¹ = ⁅u, r⁆ * r := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact mul_mem (projCenterW_le_projRad i
      (proj_commutatorElement_mem u r hu (projRad_le_projUnip i hr))) hr
  intro u hu
  refine mem_normalizer_of_conj_mem (fun r hr => hconj u hu r hr) fun r hr => ?_
  have h := hconj u⁻¹ (inv_mem hu) r hr
  rwa [inv_inv] at h

variable (k) in
@[expose] def sl2Torus : Subgroup (SL2 k) where
  carrier := {B | ∃ l : kˣ, HSL l = B}
  mul_mem' := by
    rintro _ _ ⟨l, rfl⟩ ⟨l', rfl⟩
    refine ⟨l * l', ?_⟩
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  one_mem' := ⟨1, SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])
    (by simp [coe_HSL])⟩
  inv_mem' := by
    rintro _ ⟨l, rfl⟩
    refine ⟨l⁻¹, ?_⟩
    rw [eq_inv_iff_mul_eq_one]
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_sl2Torus {B : SL2 k} : B ∈ sl2Torus k ↔ ∃ l : kˣ, HSL l = B :=
  Iff.rfl

theorem HSL_mul (l l' : kˣ) : HSL l * HSL l' = HSL (l * l') := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one : HSL (1 : kˣ) = (1 : SL2 k) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]

theorem HSL_inv (l : kˣ) : HSL l⁻¹ = (HSL l)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, HSL_mul, inv_mul_cancel, HSL_one]

theorem HSL_injective : Function.Injective (HSL : kˣ → SL2 k) := fun l l' h => by
  have := congrArg (fun B : SL2 k => (B : Matrix (Fin 2) (Fin 2) k) 0 0) h
  exact Units.ext (by simpa [coe_HSL] using this)

theorem card_sl2Torus [Finite k] : Nat.card (sl2Torus k) = Nat.card k - 1 := by
  let f : kˣ → sl2Torus k := fun l => ⟨HSL l, l, rfl⟩
  have hf : Function.Bijective f :=
    ⟨fun l l' h => HSL_injective (congrArg Subtype.val h), fun ⟨_, l, rfl⟩ => ⟨l, rfl⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_units]

theorem commute_of_mem_sl2Torus {B B' : SL2 k} (hB : B ∈ sl2Torus k) (hB' : B' ∈ sl2Torus k) :
    B * B' = B' * B := by
  obtain ⟨l, rfl⟩ := hB
  obtain ⟨l', rfl⟩ := hB'
  rw [HSL_mul, HSL_mul, mul_comm]

theorem leviOne_HSL_mul_unipU (l : kˣ) (a b c : k) :
    leviOne k (HSL l) * unipU k a b c =
      unipU k ((l : k)⁻¹ * a) ((l : k) * l * b) ((l : k) * c) * leviOne k (HSL l) := by
  have h1 : (l : k) * (l : k)⁻¹ = 1 := mul_inv_cancel₀ l.ne_zero
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_leviOne, coe_unipU, coe_unipU,
    coe_HSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (-a) * h1
  · linear_combination (-c) * h1
  · linear_combination (-(l : k) * b) * h1

theorem leviProj_HSL_conj (l : kˣ) (a b c : k) :
    leviProj k 0 (HSL l) * proj 3 k (unipU k a b c) * (leviProj k 0 (HSL l))⁻¹ =
      proj 3 k (unipU k ((l : k)⁻¹ * a) ((l : k) * l * b) ((l : k) * c)) := by
  change proj 3 k (leviOne k (HSL l)) * proj 3 k (unipU k a b c) *
    (proj 3 k (leviOne k (HSL l)))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviOne_HSL_mul_unipU l a b c)]

variable (k) in
@[expose] def projTorus : Subgroup (projectiveSL 3 k) :=
  (sl2Torus k).map (leviProj k 0)

theorem projTorus_le_normalizer_projUnip :
    projTorus k ≤ normalizer (projUnip k : Set (projectiveSL 3 k)) := by
  have hconj : ∀ l : kˣ, ∀ x ∈ projUnip k,
      leviProj k 0 (HSL l) * x * (leviProj k 0 (HSL l))⁻¹ ∈ projUnip k := by
    intro l x hx
    obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
    rw [leviProj_HSL_conj]
    exact mem_projUnip.2 ⟨_, _, _, rfl⟩
  rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
  refine mem_normalizer_of_conj_mem (hconj l) fun x hx => ?_
  have h := hconj l⁻¹ x hx
  rwa [HSL_inv, map_inv, inv_inv] at h

theorem projTorus_le_normalizer_projRad (i : Fin 2) :
    projTorus k ≤ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
  have hconj : ∀ l : kˣ, ∀ x ∈ projRad k i,
      leviProj k 0 (HSL l) * x * (leviProj k 0 (HSL l))⁻¹ ∈ projRad k i := by
    intro l x hx
    fin_cases i
    · obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
      rw [leviProj_HSL_conj, mul_zero]
      exact mem_projRad_zero.2 ⟨_, _, rfl⟩
    · obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
      rw [leviProj_HSL_conj, mul_zero]
      exact mem_projRad_one.2 ⟨_, _, rfl⟩
  rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
  refine mem_normalizer_of_conj_mem (hconj l) fun x hx => ?_
  have h := hconj l⁻¹ x hx
  rwa [HSL_inv, map_inv, inv_inv] at h

theorem eq_unipU_mul_leviOne_HSL {g : SpecialLinearGroup (Fin 3) k}
    (h00 : (g : Matrix (Fin 3) (Fin 3) k) 0 0 = 1) (h10 : (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0) :
    ∃ (a b c : k) (l : kˣ), g = unipU k a b c * leviOne k (HSL l) := by
  set M := (g : Matrix (Fin 3) (Fin 3) k) with hM
  have hdet : M 1 1 * M 2 2 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_three, ← hM, h00, h10, h20, h21] at h
    linear_combination h
  have h11 : M 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h22 : M 2 2 = (M 1 1)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  refine ⟨M 0 1 * (M 1 1)⁻¹, M 1 2 * M 1 1, M 0 2 * M 1 1, Units.mk0 _ h11, ?_⟩
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_unipU, coe_leviOne, coe_HSL, ← hM]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, h21,
    h22, h11]

theorem normalizer_projUnip [Finite k] (hk : Nat.card k = 4) :
    normalizer (projUnip k : Set (projectiveSL 3 k)) = projUnip k ⊔ projTorus k := by
  refine le_antisymm (fun x hx => ?_) (sup_le le_normalizer projTorus_le_normalizer_projUnip)
  obtain ⟨g, rfl⟩ := proj_surjective 3 k x
  have htr : ∀ y ∈ unipAll k, trace (y : Matrix (Fin 3) (Fin 3) k) = 3 := by
    rintro _ ⟨a, b, c, rfl⟩
    exact trace_unipU a b c
  have h3 := three_ne_zero_of_card hk
  have hx' : proj 3 k g ∈ normalizer (((unipAll k).map (proj 3 k) : Subgroup _) :
      Set (projectiveSL 3 k)) := hx
  obtain ⟨y₁, ⟨a₁, b₁, c₁, rfl⟩, hy₁⟩ :=
    exists_mul_eq_mul_of_mem_normalizer htr h3 hx' (x := unipU k 1 0 0) ⟨1, 0, 0, rfl⟩
  obtain ⟨y₂, ⟨a₂, b₂, c₂, rfl⟩, hy₂⟩ :=
    exists_mul_eq_mul_of_mem_normalizer htr h3 hx' (x := unipU k 0 0 1) ⟨0, 0, 1, rfl⟩
  obtain ⟨y₃, ⟨a₃, b₃, c₃, rfl⟩, hy₃⟩ :=
    exists_mul_eq_mul_of_mem_normalizer htr h3 hx' (x := unipU k 0 1 0) ⟨0, 1, 0, rfl⟩
  have e1 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 0 0) hy₁
  have e2 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 0 0) hy₂
  have e3 := congrArg (fun M : SpecialLinearGroup (Fin 3) k =>
    (M : Matrix (Fin 3) (Fin 3) k) 1 1) hy₃
  simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, coe_unipU] at e1 e2 e3
  have e3' : (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
    rw [e1, zero_mul, zero_add] at e3
    linear_combination e3
  have hdet := g.2
  rw [Matrix.det_fin_three, e1, e2, e3'] at hdet
  have hα : (g : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  obtain ⟨g', hg', hentry⟩ := exists_proj_eq_scalar_mul hk hα
  obtain ⟨a, b, c, l, hB⟩ := eq_unipU_mul_leviOne_HSL (g := g')
    (by rw [hentry, inv_mul_cancel₀ hα]) (by rw [hentry, e1, mul_zero])
    (by rw [hentry, e2, mul_zero]) (by rw [hentry, e3', mul_zero])
  rw [← hg', hB, map_mul]
  exact mul_mem_sup (mem_projUnip.2 ⟨a, b, c, rfl⟩) ⟨_, ⟨l, rfl⟩, rfl⟩

theorem projUnip_inf_projTorus : projUnip k ⊓ projTorus k = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, _, ⟨l, rfl⟩, rfl⟩
  obtain ⟨a, b, c, habc⟩ := mem_projUnip.1 hx1
  obtain ⟨d, -, hd⟩ := eq_mul_scalar_of_proj_eq habc
  have h00 := congrFun (congrFun hd 0) 0
  have h11 := congrFun (congrFun hd 1) 1
  simp [coe_unipU] at h00 h11
  rw [← h00] at h11
  have hl : l = 1 := Units.ext h11
  rw [Subgroup.mem_bot, hl, HSL_one, map_one]

theorem projUnip_eq_sup : projUnip k = projRad k 0 ⊔ projRad k 1 := by
  refine le_antisymm (fun x hx => ?_) (sup_le (projRad_le_projUnip 0) (projRad_le_projUnip 1))
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := exists_mul_eq_of_mem_projUnip hx
  exact mul_mem_sup hr₁ hr₂

theorem normalizer_projUnip_eq_inf [Finite k] (hk : Nat.card k = 4) :
    normalizer (projUnip k : Set (projectiveSL 3 k)) =
      normalizer (projRad k 0 : Set (projectiveSL 3 k)) ⊓
        normalizer (projRad k 1 : Set (projectiveSL 3 k)) := by
  refine le_antisymm ?_ ?_
  · rw [normalizer_projUnip hk]
    exact sup_le (le_inf (projUnip_le_normalizer_projRad 0) (projUnip_le_normalizer_projRad 1))
      (le_inf (projTorus_le_normalizer_projRad 0) (projTorus_le_normalizer_projRad 1))
  · rw [projUnip_eq_sup]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _

theorem eq_one_of_conj_torus_eq [Finite k] (hk : Nat.card k = 4) {l : kˣ} (hl : l ≠ 1)
    {x : projectiveSL 3 k} (hx : x ∈ projUnip k)
    (h : leviProj k 0 (HSL l) * x * (leviProj k 0 (HSL l))⁻¹ = x) : x = 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_projUnip.1 hx
  rw [leviProj_HSL_conj] at h
  obtain ⟨ha, hb, hc⟩ := unipU_eq_of_proj_eq h
  have hl1 : (l : k) ≠ 1 := fun h => hl (Units.ext h)
  have hl0 : (l : k) ≠ 0 := l.ne_zero
  have hl3 : (l : k) ^ 3 = 1 := pow_three_eq_one_of_card hk hl0
  have hc0 : c = 0 := by
    have : ((l : k) - 1) * c = 0 := by linear_combination hc
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl1)
  have ha0 : a = 0 := by
    have : ((l : k) - 1) * a = 0 := by
      have e : (l : k) * ((l : k)⁻¹ * a) = a := by field_simp
      linear_combination e - (l : k) * ha
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl1)
  have hb0 : b = 0 := by
    have hl2 : (l : k) * l ≠ 1 := by
      intro h2
      apply hl1
      calc (l : k) = (l : k) ^ 3 * ((l : k) * l)⁻¹ := by field_simp
        _ = 1 := by rw [hl3, h2, inv_one, mul_one]
    have : ((l : k) * l - 1) * b = 0 := by linear_combination hb
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl2)
  rw [ha0, hb0, hc0, unipU_zero, map_one]

theorem card_projTorus [Finite k] (hk : Nat.card k = 4) : Nat.card (projTorus k) = 3 := by
  rw [projTorus, Subgroup.card_map_of_injective (leviProj_injective 0), card_sl2Torus, hk]

theorem eq_zero_or_one_or_of_card [Finite k] (hk : Nat.card k = 4) {t : k} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (a : k) : a = 0 ∨ a = 1 ∨ a = t ∨ a = 1 + t := by
  classical
  have := Fintype.ofFinite k
  have h1t0 : 1 + t ≠ 0 := fun h => ht1 (by
    rw [show t = -1 by linear_combination h, neg_eq_self_of_card hk])
  have h1t1 : 1 + t ≠ 1 := fun h => ht0 (by linear_combination h)
  have h1tt : 1 + t ≠ t := fun h => one_ne_zero (by linear_combination h)
  have hcard : ({0, 1, t, 1 + t} : Finset k).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h1tt.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ht1.symm, h1t1.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨zero_ne_one, ht0.symm, h1t0.symm⟩
  have huniv : ({0, 1, t, 1 + t} : Finset k) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, hk])
  have ha : a ∈ ({0, 1, t, 1 + t} : Finset k) := huniv ▸ Finset.mem_univ a
  simpa using ha

theorem leviProj_HSL_conj_W (l : kˣ) (c : k) :
    leviProj k 0 (HSL l) * proj 3 k (unipU k 0 0 c) * (leviProj k 0 (HSL l))⁻¹ =
      proj 3 k (unipU k 0 0 ((l : k) * c)) := by
  rw [leviProj_HSL_conj, mul_zero, mul_zero]

theorem projRad_zero_le_sup [Finite k] (hk : Nat.card k = 4) {t : k} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) :
    projRad k 0 ≤ projCenterW k ⊔ zpowers (proj 3 k (unipU k 1 0 0)) ⊔
      zpowers (proj 3 k (unipU k t 0 0)) := by
  intro x hx
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
  have hw : proj 3 k (unipU k 0 0 c) ∈ projCenterW k ⊔ zpowers (proj 3 k (unipU k 1 0 0)) ⊔
      zpowers (proj 3 k (unipU k t 0 0)) :=
    mem_sup_left (mem_sup_left (mem_projCenterW.2 ⟨c, rfl⟩))
  have h1 : proj 3 k (unipU k 1 0 0) ∈ projCenterW k ⊔ zpowers (proj 3 k (unipU k 1 0 0)) ⊔
      zpowers (proj 3 k (unipU k t 0 0)) := mem_sup_left (mem_sup_right (mem_zpowers _))
  have h2 : proj 3 k (unipU k t 0 0) ∈ projCenterW k ⊔ zpowers (proj 3 k (unipU k 1 0 0)) ⊔
      zpowers (proj 3 k (unipU k t 0 0)) := mem_sup_right (mem_zpowers _)
  rcases eq_zero_or_one_or_of_card hk ht0 ht1 a with ha | ha | ha | ha <;> rw [ha]
  · exact hw
  · have e : proj 3 k (unipU k 1 0 c) = proj 3 k (unipU k 0 0 c) * proj 3 k (unipU k 1 0 0) := by
      rw [← map_mul, unipU_mul]
      congr 2 <;> ring
    rw [e]
    exact mul_mem hw h1
  · have e : proj 3 k (unipU k t 0 c) = proj 3 k (unipU k 0 0 c) * proj 3 k (unipU k t 0 0) := by
      rw [← map_mul, unipU_mul]
      congr 2 <;> ring
    rw [e]
    exact mul_mem hw h2
  · have e : proj 3 k (unipU k (1 + t) 0 c) = proj 3 k (unipU k 0 0 c) *
        proj 3 k (unipU k 1 0 0) * proj 3 k (unipU k t 0 0) := by
      rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
      congr 2 <;> ring
    rw [e]
    exact mul_mem (mul_mem hw h1) h2

theorem projRad_one_le_sup [Finite k] (hk : Nat.card k = 4) {t : k} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) :
    projRad k 1 ≤ projCenterW k ⊔ zpowers (proj 3 k (unipU k 0 1 0)) ⊔
      zpowers (proj 3 k (unipU k 0 t 0)) := by
  intro x hx
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
  have hw : proj 3 k (unipU k 0 0 c) ∈ projCenterW k ⊔ zpowers (proj 3 k (unipU k 0 1 0)) ⊔
      zpowers (proj 3 k (unipU k 0 t 0)) :=
    mem_sup_left (mem_sup_left (mem_projCenterW.2 ⟨c, rfl⟩))
  have h1 : proj 3 k (unipU k 0 1 0) ∈ projCenterW k ⊔ zpowers (proj 3 k (unipU k 0 1 0)) ⊔
      zpowers (proj 3 k (unipU k 0 t 0)) := mem_sup_left (mem_sup_right (mem_zpowers _))
  have h2 : proj 3 k (unipU k 0 t 0) ∈ projCenterW k ⊔ zpowers (proj 3 k (unipU k 0 1 0)) ⊔
      zpowers (proj 3 k (unipU k 0 t 0)) := mem_sup_right (mem_zpowers _)
  rcases eq_zero_or_one_or_of_card hk ht0 ht1 b with hb | hb | hb | hb <;> rw [hb]
  · exact hw
  · have e : proj 3 k (unipU k 0 1 c) = proj 3 k (unipU k 0 0 c) * proj 3 k (unipU k 0 1 0) := by
      rw [← map_mul, unipU_mul]
      congr 2 <;> ring
    rw [e]
    exact mul_mem hw h1
  · have e : proj 3 k (unipU k 0 t c) = proj 3 k (unipU k 0 0 c) * proj 3 k (unipU k 0 t 0) := by
      rw [← map_mul, unipU_mul]
      congr 2 <;> ring
    rw [e]
    exact mul_mem hw h2
  · have e : proj 3 k (unipU k 0 (1 + t) c) = proj 3 k (unipU k 0 0 c) *
        proj 3 k (unipU k 0 1 0) * proj 3 k (unipU k 0 t 0) := by
      rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
      congr 2 <;> ring
    rw [e]
    exact mul_mem (mul_mem hw h1) h2

theorem proj_unipU_one_one_sq_ne_one [Finite k] (hk : Nat.card k = 4) :
    proj 3 k (unipU k 1 1 0) ^ 2 ≠ 1 := by
  rw [← map_pow, unipU_sq_of_card hk, one_mul]
  exact proj_unipU_ne_one (by simp)

end CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
