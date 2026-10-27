module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpEichler
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.QuadIsotropic
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpRouteA
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {K : Type} [Field K] {r : ℕ}

section Heis

theorem Eel_comm {v u u' : Fin r ⊕ Fin r → K} (c c' : K) (hu : form u v = 0)
    (hu' : form u' v = 0) (h : form u u' = 0) :
    Eel v u c hu * Eel v u' c' hu' = Eel v u' c' hu' * Eel v u c hu := by
  rw [Eel_mul, Eel_mul]
  refine Eel_congr _ _ (add_comm u u') ?_
  rw [form_antisymm u u', h]
  ring

theorem Eel_mul_comm_eq {v u u' : Fin r ⊕ Fin r → K} (c c' : K) (hu : form u v = 0)
    (hu' : form u' v = 0) :
    Eel v u c hu * Eel v u' c' hu' =
      Eel v u' c' hu' * (Eel v u c hu * Eel v 0 (-2 * form u u') (form_zero_left v)) := by
  rw [Eel_mul, Eel_mul, Eel_mul]
  refine Eel_congr _ _ (by simp [add_comm]) ?_
  simp only [form_add_right, form_zero_right, form_antisymm u u']
  ring

theorem heisCfg_Eel {p n : ℕ} [CharP K p] (hp2 : (2 : K) ≠ 0) {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0)
    (a b : Fin n → Fin r ⊕ Fin r → K) (hav : ∀ i, form (a i) v = 0) (hbv : ∀ i, form (b i) v = 0)
    (haa : ∀ i j, form (a i) (a j) = 0) (hbb : ∀ i j, form (b i) (b j) = 0)
    (hab : ∀ i j, form (a i) (b j) = if i = j then 1 else 0) :
    HeisCfg p n (fun i => Eel v (a i) 0 (hav i)) (fun i => Eel v (b i) 0 (hbv i))
      (Eel v 0 (-2) (form_zero_left v)) where
  xp i := Eel_pow_char _ _ p
  zp := Eel_pow_char _ _ p
  zx i := Eel_comm _ _ _ _ (form_zero_right _)
  zy i := Eel_comm _ _ _ _ (form_zero_right _)
  yx i := by
    have h1 : form (a i) (b i) = 1 := by rw [hab]; simp
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, Eel_mul_comm_eq _ _ (hav i) (hbv i), h1, mul_one]
  xx i j := Eel_comm _ _ _ _ (haa i j)
  yy i j _ := Eel_comm _ _ _ _ (hbb i j)
  xy i j hij := Eel_comm _ _ _ _ (by rw [hab]; simp [hij])
  z1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_form_ne_zero hv
    have e := congrArg (fun g => mat r K g *ᵥ w) h
    simp only [Eel_mulVec, map_one, Matrix.one_mulVec, form_zero_right, zero_smul, add_zero] at e
    have e2 : (-2 * form w v) • v = 0 := by
      have := congrArg (fun x => x - w) e
      simpa using this
    rcases smul_eq_zero.1 e2 with h0 | h0
    · apply hw
      have : form v w = 0 := by
        have h3 : (-2 : K) * form w v = 0 := h0
        have := (mul_eq_zero.1 h3).resolve_left (by simpa using hp2)
        rw [form_antisymm, this, neg_zero]
      exact this
    · exact hv h0

end Heis

section Scalar

theorem scalar_matrix_eq (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem mk_eq_one_of_mulVec (g : StatedSp r K) (c : Kˣ)
    (h : ∀ w, mat r K g *ᵥ w = (c : K) • w) :
    (QuotientGroup.mk g : StatedProj (StatedSp r K)) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨c, Units.ext ?_⟩
  rw [scalar_matrix_eq, ← mat_apply]
  refine (Matrix.ext_iff_mulVec.2 fun w => ?_).symm
  rw [h w, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_mulVec_of_mk_eq_one (g : StatedSp r K)
    (h : (QuotientGroup.mk g : StatedProj (StatedSp r K)) = 1) :
    ∃ c : Kˣ, ∀ w, mat r K g *ᵥ w = (c : K) • w := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun w => ?_⟩
  have : mat r K g = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [mat_apply, ← hc, scalar_matrix_eq]
  rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem sq_of_mk_sq [NeZero r] {g : StatedSp r K}
    (h : (QuotientGroup.mk g : StatedProj (StatedSp r K)) * QuotientGroup.mk g = 1) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ w, mat r K g *ᵥ (mat r K g *ᵥ w) = ε • w := by
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hm : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r K := by
    rw [hc]; exact (g * g).2
  have hcc := scalar_sq_eq_one_of_mem_statedSp c hm
  have hcc' : (c : K) * c = 1 := by simpa using congrArg Units.val hcc
  refine ⟨c, ?_, fun w => ?_⟩
  · have : ((c : K) - 1) * ((c : K) + 1) = 0 := by linear_combination hcc'
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · have : mat r K (g * g) = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [mat_apply, ← hc, scalar_matrix_eq]
    rw [Matrix.mulVec_mulVec, ← map_mul, this, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem mk_ne_one_of_fixed {g : StatedSp r K} (hg : g ≠ 1) {w₀ : Fin r ⊕ Fin r → K}
    (hw₀ : w₀ ≠ 0) (hfix : mat r K g *ᵥ w₀ = w₀) :
    (QuotientGroup.mk g : StatedProj (StatedSp r K)) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := exists_mulVec_of_mk_eq_one g h
  have e := hc w₀
  rw [hfix] at e
  have hc1 : (c : K) = 1 := by
    have h0 : ((c : K) - 1) • w₀ = 0 := by rw [sub_smul, ← e, one_smul, sub_self]
    have := (smul_eq_zero.1 h0).resolve_right hw₀
    linear_combination this
  apply hg
  refine Sp_ext_mulVec fun w => ?_
  rw [hc w, hc1, one_smul, map_one, Matrix.one_mulVec]

end Scalar

section Pairs

theorem Eel_congr' {v v' u u' : Fin r ⊕ Fin r → K} {c c' : K} (hu : form u v = 0)
    (hu' : form u' v' = 0) (h0 : v = v') (h1 : u = u') (h2 : c = c') :
    Eel v u c hu = Eel v' u' c' hu' := by
  subst h0; subst h1; subst h2; rfl

theorem conj_inv_Eel (g : StatedSp r K) {v u : Fin r ⊕ Fin r → K} (hu : form u v = 0)
    (hinv : (mat r K g *ᵥ v = v ∧ mat r K g *ᵥ u = -u) ∨
      (mat r K g *ᵥ v = u ∧ mat r K g *ᵥ u = -v)) :
    g * Eel v u 0 hu * g⁻¹ = (Eel v u 0 hu)⁻¹ := by
  rw [conj_Eel, Eel_inv]
  rcases hinv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Eel_congr' _ _ h1 h2 (by simp)
  · have hvu : form v u = 0 := by rw [form_antisymm, hu, neg_zero]
    have hnv : form (-v) u = 0 := by rw [form_neg_left, hvu, neg_zero]
    have hnu : form (-u) v = 0 := by rw [form_neg_left, hu, neg_zero]
    exact (Eel_congr' _ hnv h1 h2 rfl).trans
      ((Eel_swap_neg hnv hnu).trans (Eel_congr' _ _ rfl rfl neg_zero.symm))

theorem exists_form_one_zero {x y : Fin r ⊕ Fin r → K} (hy : y ≠ 0) (hxy : ∀ k : K, x ≠ k • y) :
    ∃ w, form x w = 1 ∧ form y w = 0 := by
  by_contra hcon
  have h1 : ∀ w, form y w = 0 → form x w = 0 := by
    intro w hw
    by_contra hx
    exact hcon ⟨(form x w)⁻¹ • w, by rw [form_smul_right, inv_mul_cancel₀ hx],
      by rw [form_smul_right, hw, mul_zero]⟩
  obtain ⟨s, hs⟩ := exists_form_ne_zero hy
  set w₁ := (form y s)⁻¹ • s with hw₁
  have hw₁1 : form y w₁ = 1 := by rw [hw₁, form_smul_right, inv_mul_cancel₀ hs]
  refine hxy (form x w₁) (eq_of_sub_eq_zero (eq_zero_of_forall_form_eq_zero fun w => ?_))
  have h2 : form y (w - form y w • w₁) = 0 := by
    rw [form_sub_right, form_smul_right, hw₁1, mul_one, sub_self]
  have h3 := h1 _ h2
  rw [form_sub_right, form_smul_right] at h3
  rw [form_sub_left, form_smul_left]
  linear_combination h3

theorem form_eq_zero_of_eig (g : StatedSp r K) (hK2 : (2 : K) ≠ 0) {x y : Fin r ⊕ Fin r → K}
    (hx : mat r K g *ᵥ x = x) (hy : mat r K g *ᵥ y = -y) : form x y = 0 := by
  have h := form_mulVec g x y
  rw [hx, hy, form_neg_right] at h
  have : (2 : K) * form x y = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left hK2

theorem exists_eig_partner (g : StatedSp r K) (hK2 : (2 : K) ≠ 0)
    (hG2 : ∀ w, mat r K g *ᵥ (mat r K g *ᵥ w) = w) {ε : K} (hε : ε * ε = 1)
    {x : Fin r ⊕ Fin r → K} (hx0 : x ≠ 0) (hx : mat r K g *ᵥ x = ε • x) :
    ∃ y, mat r K g *ᵥ y = ε • y ∧ form x y = 1 := by
  obtain ⟨s, hs⟩ := exists_form_ne_zero hx0
  set y₀ := s + ε • (mat r K g *ᵥ s) with hy₀
  have h1 : mat r K g *ᵥ y₀ = ε • y₀ := by
    rw [hy₀, Matrix.mulVec_add, Matrix.mulVec_smul, hG2, smul_add, smul_smul, hε, one_smul,
      add_comm]
  have h2 : form x y₀ = 2 * form x s := by
    have : form x (mat r K g *ᵥ s) = ε * form x s := by
      rw [← form_mulVec g x (mat r K g *ᵥ s), hx, hG2, form_smul_left]
    rw [hy₀, form_add_right, form_smul_right, this]
    linear_combination (form x s) * hε
  have hne : form x y₀ ≠ 0 := by rw [h2]; exact mul_ne_zero hK2 hs
  refine ⟨(form x y₀)⁻¹ • y₀, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, h1, smul_comm]
  · rw [form_smul_right, inv_mul_cancel₀ hne]

def PairData (g : StatedSp r K) (a₀ b₀ v v' : Fin r ⊕ Fin r → K) : Prop :=
  form a₀ b₀ = 1 ∧ form v v' = 1 ∧ form a₀ v = 0 ∧ form a₀ v' = 0 ∧ form b₀ v = 0 ∧
    form b₀ v' = 0 ∧
    ((mat r K g *ᵥ v = v ∧ mat r K g *ᵥ a₀ = -a₀) ∨
      (mat r K g *ᵥ v = a₀ ∧ mat r K g *ᵥ a₀ = -v))

theorem exists_pairData_one (g : StatedSp r K) (hK2 : (2 : K) ≠ 0)
    (hG2 : ∀ w, mat r K g *ᵥ (mat r K g *ᵥ w) = w)
    (hns : ∀ c : K, c ≠ 0 → ¬ ∀ w, mat r K g *ᵥ w = c • w) :
    ∃ a₀ b₀ v v', PairData g a₀ b₀ v v' := by
  obtain ⟨w₁, hw₁⟩ := not_forall.1 (hns 1 one_ne_zero)
  obtain ⟨w₂, hw₂⟩ := not_forall.1 (hns (-1) (neg_ne_zero.2 one_ne_zero))
  rw [one_smul] at hw₁
  rw [neg_one_smul] at hw₂
  set a₀ := w₁ - mat r K g *ᵥ w₁ with ha₀
  set v := w₂ + mat r K g *ᵥ w₂ with hv
  have hGa : mat r K g *ᵥ a₀ = (-1 : K) • a₀ := by
    rw [ha₀, Matrix.mulVec_sub, hG2, neg_one_smul, neg_sub]
  have hGv : mat r K g *ᵥ v = (1 : K) • v := by
    rw [hv, Matrix.mulVec_add, hG2, one_smul, add_comm]
  have ha0 : a₀ ≠ 0 := fun h => hw₁ (by rw [ha₀] at h; exact (sub_eq_zero.1 h).symm)
  have hv0 : v ≠ 0 := fun h => hw₂ (by rw [hv] at h; exact eq_neg_of_add_eq_zero_right h)
  obtain ⟨b₀, hb₀, hab⟩ := exists_eig_partner g hK2 hG2 (ε := -1) (by norm_num) ha0 hGa
  obtain ⟨v', hv', hvv⟩ := exists_eig_partner g hK2 hG2 (ε := 1) (by norm_num) hv0 hGv
  rw [one_smul] at hv' hGv
  rw [neg_one_smul] at hb₀ hGa
  have o1 : form v a₀ = 0 := form_eq_zero_of_eig g hK2 hGv hGa
  have o2 : form v b₀ = 0 := form_eq_zero_of_eig g hK2 hGv hb₀
  have o3 : form v' a₀ = 0 := form_eq_zero_of_eig g hK2 hv' hGa
  have o4 : form v' b₀ = 0 := form_eq_zero_of_eig g hK2 hv' hb₀
  refine ⟨a₀, b₀, v, v', hab, hvv, ?_, ?_, ?_, ?_, Or.inl ⟨hGv, hGa⟩⟩
  · rw [form_antisymm, o1, neg_zero]
  · rw [form_antisymm, o3, neg_zero]
  · rw [form_antisymm, o2, neg_zero]
  · rw [form_antisymm, o4, neg_zero]

theorem exists_pairData_neg [Finite K] (g : StatedSp r K) (hK2 : (2 : K) ≠ 0)
    (hK : ¬ IsSquare (-1 : K)) (hr : 2 ≤ r)
    (hG2 : ∀ w, mat r K g *ᵥ (mat r K g *ᵥ w) = -w) :
    ∃ a₀ b₀ v v', PairData g a₀ b₀ v v' := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : 3 ≤ Fintype.card (Fin r ⊕ Fin r) := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hcard (gram K r * mat r K g)
  have hQ : form v (mat r K g *ᵥ v) = 0 := by
    unfold form
    rw [← Matrix.mulVec_mulVec] at hvQ
    exact hvQ
  have hQ' : form (mat r K g *ᵥ v) v = 0 := by rw [form_antisymm, hQ, neg_zero]
  have hGv0 : mat r K g *ᵥ v ≠ 0 := by
    intro h
    apply hv0
    have := hG2 v
    rw [h, Matrix.mulVec_zero] at this
    exact neg_eq_zero.1 this.symm
  have hind : ∀ k : K, v ≠ k • (mat r K g *ᵥ v) := by
    intro k hk
    have h1 : mat r K g *ᵥ v = (-k) • v := by
      have := congrArg (fun x => mat r K g *ᵥ x) hk
      simp only [Matrix.mulVec_smul, hG2] at this
      rw [this, smul_neg, neg_smul]
    have e : v = (-(k * k)) • v := by
      calc v = k • (mat r K g *ᵥ v) := hk
        _ = k • ((-k) • v) := by rw [h1]
        _ = (-(k * k)) • v := by rw [smul_smul]; congr 1; ring
    have h2 : (1 + k * k) • v = 0 := by
      have : v - (-(k * k)) • v = 0 := sub_eq_zero.2 e
      rw [← this]; module
    have h3 := (smul_eq_zero.1 h2).resolve_right hv0
    exact hK ⟨k, by linear_combination -h3⟩
  obtain ⟨v₀, hv₀1, hv₀2⟩ := exists_form_one_zero hGv0 hind
  have h2inv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ hK2
  obtain ⟨s, hs⟩ : ∃ s : K, s = -(form v₀ (mat r K g *ᵥ v₀) * 2⁻¹) := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : Fin r ⊕ Fin r → K, v₁ = v₀ + s • (mat r K g *ᵥ v) := ⟨_, rfl⟩
  have hGv₁ : mat r K g *ᵥ v₁ = mat r K g *ᵥ v₀ - s • v := by
    rw [hv₁, Matrix.mulVec_add, Matrix.mulVec_smul, hG2]; module
  have hv₀v : form v₀ v = -1 := by rw [form_antisymm, hv₀1]
  have hGG : form (mat r K g *ᵥ v) (mat r K g *ᵥ v₀) = 1 := by rw [form_mulVec, hv₀1]
  have hQ₁ : form v₁ (mat r K g *ᵥ v₁) = 0 := by
    rw [hGv₁]
    simp only [hv₁, form_add_left, form_smul_left, form_sub_right, form_smul_right, hv₀v, hGG,
      hQ']
    linear_combination 2 * hs + (-(form v₀ (mat r K g *ᵥ v₀))) * h2inv
  have h₂ : form v v₁ = 1 := by
    rw [hv₁, form_add_right, form_smul_right, hQ, hv₀1]; ring
  have o2 : form (mat r K g *ᵥ v) v₁ = 0 := by
    rw [hv₁, form_add_right, form_smul_right, hv₀2, form_self]; ring
  have h₁ : form (mat r K g *ᵥ v) (mat r K g *ᵥ v₁) = 1 := by rw [form_mulVec, h₂]
  have o3 : form (mat r K g *ᵥ v₁) v = 0 := by
    rw [← form_mulVec g (mat r K g *ᵥ v₁) v, hG2, form_neg_left, form_antisymm (mat r K g *ᵥ v) v₁,
      o2, neg_zero, neg_zero]
  refine ⟨mat r K g *ᵥ v, mat r K g *ᵥ v₁, v, v₁, h₁, h₂, hQ', o2, o3, ?_,
    Or.inr ⟨rfl, hG2 v⟩⟩
  · rw [form_antisymm, hQ₁, neg_zero]

end Pairs

section Main

theorem form_e_e (i j : Fin r) :
    form (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin r → K) (Pi.single (Sum.inl j) 1) = 0 := by
  rw [form_single_right]; simp [Pi.single_apply]

theorem form_f_f (i j : Fin r) :
    form (Pi.single (Sum.inr i) 1 : Fin r ⊕ Fin r → K) (Pi.single (Sum.inr j) 1) = 0 := by
  rw [form_single_right]; simp [Pi.single_apply]

theorem form_e_f (i j : Fin r) :
    form (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin r → K) (Pi.single (Sum.inr j) 1) =
      if i = j then 1 else 0 := by
  rw [form_single_right]; simp [Pi.single_apply, eq_comm]

theorem form_f_e (i j : Fin r) :
    form (Pi.single (Sum.inr i) 1 : Fin r ⊕ Fin r → K) (Pi.single (Sum.inl j) 1) =
      if i = j then -1 else 0 := by
  rw [form_single_right]; simp [Pi.single_apply, eq_comm]; split_ifs <;> simp

theorem succAbove_one_zero (n : ℕ) : (1 : Fin (n + 1 + 1)).succAbove 0 = 0 := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by simp)]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_heisCfg_of_involution {p n : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
    (hp2 : p ≠ 2) (hK : ¬ IsSquare (-1 : K)) (t : StatedProj (StatedSp (n + 1 + 1) K))
    (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ (x y : Fin (n + 1) → StatedProj (StatedSp (n + 1 + 1) K))
      (z : StatedProj (StatedSp (n + 1 + 1) K)),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹ := by
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).1 h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨ε, hε, hsq⟩ := sq_of_mk_sq ht
  have hns : ∀ c : K, c ≠ 0 → ¬ ∀ w, mat _ K g *ᵥ w = c • w := fun c hc h =>
    ht1 (mk_eq_one_of_mulVec g (Units.mk0 c hc) h)
  obtain ⟨a₀, b₀, v, v', hpd⟩ : ∃ a₀ b₀ v v', PairData g a₀ b₀ v v' := by
    rcases hε with rfl | rfl
    · exact exists_pairData_one g hK2 (fun w => by rw [hsq, one_smul]) hns
    · exact exists_pairData_neg g hK2 hK (by omega) (fun w => by rw [hsq, neg_one_smul])
  obtain ⟨h1, h2, o1, o2, o3, o4, hinv⟩ := hpd
  obtain ⟨h, ha, hb, hc, hd⟩ := exists_sp_apply_eq_two a₀ b₀ v v' h1 h2 o1 o2 o3 o4
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv, form_zero_left] at h2
    exact zero_ne_one h2
  have hσ1 : ∀ i : Fin (n + 1), (1 : Fin (n + 1 + 1)).succAbove i ≠ 1 := fun i =>
    Fin.succAbove_ne _ _
  have hσinj : Function.Injective (1 : Fin (n + 1 + 1)).succAbove :=
    Fin.succAbove_right_injective
  let a : Fin (n + 1) → Fin (n + 1 + 1) ⊕ Fin (n + 1 + 1) → K := fun i =>
    mat _ K h *ᵥ Pi.single (Sum.inl ((1 : Fin (n + 1 + 1)).succAbove i)) 1
  let b : Fin (n + 1) → Fin (n + 1 + 1) ⊕ Fin (n + 1 + 1) → K := fun i =>
    mat _ K h *ᵥ Pi.single (Sum.inr ((1 : Fin (n + 1 + 1)).succAbove i)) 1
  have hav : ∀ i, form (a i) v = 0 := fun i => by
    rw [← hc]; exact (form_mulVec h _ _).trans (form_e_e _ _)
  have hbv : ∀ i, form (b i) v = 0 := fun i => by
    rw [← hc]
    refine (form_mulVec h _ _).trans ?_
    rw [form_f_e]; simp [hσ1 i]
  have haa : ∀ i j, form (a i) (a j) = 0 := fun i j =>
    (form_mulVec h _ _).trans (form_e_e _ _)
  have hbb : ∀ i j, form (b i) (b j) = 0 := fun i j =>
    (form_mulVec h _ _).trans (form_f_f _ _)
  have hab : ∀ i j, form (a i) (b j) = if i = j then 1 else 0 := fun i j => by
    refine (form_mulVec h _ _).trans ?_
    rw [form_e_f]
    simp only [hσinj.eq_iff]
  have hH := heisCfg_Eel (p := p) hK2 hv0 a b hav hbv haa hbb hab
  have ha0 : a 0 = a₀ := by
    show mat _ K h *ᵥ Pi.single (Sum.inl ((1 : Fin (n + 1 + 1)).succAbove 0)) 1 = a₀
    rw [succAbove_one_zero]; exact ha
  have ha0ne : a 0 ≠ 0 := by
    intro h0
    have := hab 0 0
    rw [h0, form_zero_left] at this
    simp at this
  have hzfix : mat _ K (Eel v 0 (-2) (form_zero_left v)) *ᵥ a 0 = a 0 := by
    rw [Eel_mulVec, hav 0]
    simp [form_zero_right]
  have hmap := hH.map (QuotientGroup.mk'
    ((StatedScalars (Fin (n + 1 + 1) ⊕ Fin (n + 1 + 1)) K).subgroupOf (StatedSp (n + 1 + 1) K)))
    (mk_ne_one_of_fixed hH.z1 ha0ne hzfix)
  refine ⟨_, _, _, hmap, fun i => ?_, ?_⟩
  · rw [← map_pow, Eel_pow_char, map_one]
  · have hinv' : (mat _ K g *ᵥ v = v ∧ mat _ K g *ᵥ a 0 = -a 0) ∨
        (mat _ K g *ᵥ v = a 0 ∧ mat _ K g *ᵥ a 0 = -v) := by
      rw [ha0]; exact hinv
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      conj_inv_Eel g (hav 0) hinv', QuotientGroup.mk_inv]

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
