module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12Seven
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Fischer.Classification

namespace S12Insp4P

theorem closure_comm_sq {X : Type*} [Group X] {s : Set X}
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (h2 : ∀ a ∈ s, a * a = 1) :
    (∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x) ∧
      ∀ x ∈ Subgroup.closure s, x ^ 2 = 1 := by
  have hs : Subgroup.closure s ≤ centralizer s :=
    (closure_le _).mpr fun a ha => mem_centralizer_iff.mpr fun b hb => hc b hb a ha
  have hs' : Subgroup.closure s ≤ centralizer (Subgroup.closure s : Set X) :=
    (closure_le _).mpr fun a ha => mem_centralizer_iff.mpr fun b hb =>
      ((mem_centralizer_iff.mp (hs hb)) a ha).symm
  have hcomm : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.mp (hs' hy) x hx
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem a ha => rw [sq]; exact h2 a ha
  | one => rw [one_pow]
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (hcomm x hx y hy) 2), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem nondegOn_perp_orthonormal (hf : IsF3Form f) {k : ℕ} {w : Fin k → Fin m → ZMod 3}
    (hw : ∀ i j, f (w i) (w j) = if i = j then 1 else 0) :
    ∀ y ∈ F3.perpSub f w, y ≠ 0 → ∃ y' ∈ F3.perpSub f w, f y y' ≠ 0 := by
  refine F3.nondegOn_of_proj hf (fun y => y - ∑ i, f y (w i) • w i)
    (fun y => F3.mem_perpSub.2 fun j => ?_) fun x hx y => ?_
  · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left]
    simp only [LinearMap.BilinForm.smul_left, hw, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]
  · rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sum_right]
    simp only [LinearMap.BilinForm.smul_right, F3.mem_perpSub.1 hx, mul_zero,
      Finset.sum_const_zero, sub_zero]

theorem exists_orthonormal (hf : IsF3Form f) :
    ∀ k, k < m → ∃ w : Fin k → Fin m → ZMod 3, ∀ i j, f (w i) (w j) = if i = j then 1 else 0
  | 0, _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | k + 1, hk => by
    obtain ⟨w, hw⟩ := exists_orthonormal hf k (by omega)
    obtain ⟨v, hvU, hv⟩ := F3.exists_mem_norm_eq hf (nondegOn_perp_orthonormal hf hw)
      (F3.perpSub_twoDim hf (by omega) w) (one_ne_zero (α := ZMod 3))
    have hvw : ∀ i, f v (w i) = 0 := F3.mem_perpSub.1 hvU
    have hwv : ∀ i, f (w i) v = 0 := fun i => by rw [hf.symm]; exact hvw i
    refine ⟨Fin.cons v w, fun i j => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hv]
    · simp [hvw, (Fin.succ_ne_zero j).symm]
    · simp [hwv, Fin.succ_ne_zero i]
    · simp [hw, Fin.succ_inj]

theorem two_pow_le_card_closure (hf : IsF3Form f) (hm : 4 ≤ m) {K : ℕ} (hKm : K < m)
    {w : Fin K → Fin m → ZMod 3} (hw : ∀ i j, f (w i) (w j) = if i = j then 1 else 0) :
    2 ^ K ≤ Nat.card (Subgroup.closure (Set.range fun i => reflBar f (w i))) := by
  have hn1 : ∀ i, f (w i) (w i) = 1 := fun i => by simp [hw]
  have hn0 : ∀ i j, i ≠ j → f (w i) (w j) = 0 := fun i j h => by simp [hw, h]
  obtain ⟨u, hu0, hu⟩ := F3.exists_ne_zero_perp (f := f) hKm w
  have hmono : ∀ k, Subgroup.closure {x : R3 f | ∃ i : Fin K, (i : ℕ) < k ∧ reflBar f (w i) = x}
      ≤ Subgroup.closure {x : R3 f | ∃ i : Fin K, (i : ℕ) < k + 1 ∧ reflBar f (w i) = x} :=
    fun k => closure_mono fun x ⟨i, hi, hx⟩ => ⟨i, by omega, hx⟩
  have hlift : ∀ k (hk : k < K), ∀ x ∈ Subgroup.closure
      {x : R3 f | ∃ i : Fin K, (i : ℕ) < k ∧ reflBar f (w i) = x}, ∃ g : F3.reflGroup f,
      (QuotientGroup.mk g : R3 f) = x ∧ F3.act (g : GL (Fin m) (ZMod 3)) (w ⟨k, hk⟩) = w ⟨k, hk⟩ ∧
        F3.act (g : GL (Fin m) (ZMod 3)) u = u := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hik : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; exact lt_irrefl _ hi
      refine ⟨reflElt f (w i), rfl, ?_, ?_⟩
      · rw [coe_reflElt]
        exact F3.act_refl_of_perp (hn1 i) (hn0 _ _ hik.symm)
      · rw [coe_reflElt]
        exact F3.act_refl_of_perp (hn1 i) (hu i)
    | one => exact ⟨1, rfl, F3.act_one _, F3.act_one _⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨g₁, rfl, h₁, h₁'⟩ := ihx
      obtain ⟨g₂, rfl, h₂, h₂'⟩ := ihy
      refine ⟨g₁ * g₂, rfl, ?_, ?_⟩
      · rw [Subgroup.coe_mul, F3.act_mul, h₂, h₁]
      · rw [Subgroup.coe_mul, F3.act_mul, h₂', h₁']
    | inv x _ ih =>
      obtain ⟨g, rfl, h₁, h₁'⟩ := ih
      refine ⟨g⁻¹, rfl, ?_, ?_⟩
      · conv_lhs => rw [← h₁]
        rw [Subgroup.coe_inv, F3.act_inv_act]
      · conv_lhs => rw [← h₁']
        rw [Subgroup.coe_inv, F3.act_inv_act]
  have hnot : ∀ k (hk : k < K), reflBar f (w ⟨k, hk⟩) ∉ Subgroup.closure
      {x : R3 f | ∃ i : Fin K, (i : ℕ) < k ∧ reflBar f (w i) = x} := by
    intro k hk hmem
    obtain ⟨g, hg, h₁, h₁'⟩ := hlift k hk _ hmem
    rw [reflBar_def, QuotientGroup.eq] at hg
    have hcoe : ((g⁻¹ * reflElt f (w ⟨k, hk⟩) : F3.reflGroup f) : GL (Fin m) (ZMod 3)) =
        (g : GL (Fin m) (ZMod 3))⁻¹ * F3.refl f (w ⟨k, hk⟩) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_reflElt]
    have hginv : ∀ v, F3.act (g : GL (Fin m) (ZMod 3)) v = v →
        F3.act (g : GL (Fin m) (ZMod 3))⁻¹ v = v := fun v hv => by
      conv_lhs => rw [← hv]
      rw [F3.act_inv_act]
    rcases F3.coe_eq_of_mem_center hf hm hg with h | h <;> rw [hcoe] at h
    · have e := congrArg (fun γ => F3.act γ (w ⟨k, hk⟩)) h
      rw [F3.act_mul, F3.act_refl_self (hn1 _), F3.act_neg, hginv _ h₁, F3.act_one] at e
      exact F3.ne_zero_of_norm_one (hn1 ⟨k, hk⟩) (F3.eq_zero_of_eq_neg e.symm)
    · have e := congrArg (fun γ => F3.act γ u) h
      rw [F3.act_mul, F3.act_refl_of_perp (hn1 _) (hu _), hginv _ h₁', F3.act_neg_one] at e
      exact hu0 (F3.eq_zero_of_eq_neg e)
  have hcard : ∀ k, k ≤ K → 2 ^ k ≤ Nat.card (Subgroup.closure
      {x : R3 f | ∃ i : Fin K, (i : ℕ) < k ∧ reflBar f (w i) = x}) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    | succ k ih =>
      intro hk
      have hk' : k < K := by omega
      have h1 := ih hk'.le
      obtain ⟨c, hc⟩ := card_dvd_of_le (hmono k)
      have hc2 : 2 ≤ c := by
        by_contra hlt
        have hc1 : c = 1 ∨ c = 0 := by omega
        rcases hc1 with rfl | rfl
        · refine hnot k hk' ?_
          rw [eq_of_le_of_card_ge (hmono k) (by rw [hc, mul_one])]
          exact subset_closure ⟨⟨k, hk'⟩, Nat.lt_succ_self k, rfl⟩
        · rw [mul_zero] at hc
          exact Nat.card_pos.ne' hc
      calc 2 ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ _ * c := Nat.mul_le_mul h1 hc2
        _ = _ := hc.symm
  have hset : {x : R3 f | ∃ i : Fin K, (i : ℕ) < K ∧ reflBar f (w i) = x} =
      Set.range fun i => reflBar f (w i) := by
    ext x
    exact ⟨fun ⟨i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i, i.2, hx⟩⟩
  have := hcard K le_rfl
  rwa [hset] at this

end S12Insp4P

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_reflGroup_ge_six {g : G}
    (hE : ∀ P : Subgroup S.Mbar, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ 2 = 1) →
      Nat.card P ≤ 2 ^ 4)
    {m : ℕ} (hm : 6 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, -⟩ := (fischerCentralQuotientModel_iff _).1 hmod
  obtain ⟨w, hw⟩ := S12Insp4P.exists_orthonormal hf 5 (by omega)
  have hn1 : ∀ i, f (w i) (w i) = 1 := fun i => by simp [hw]
  let E := Subgroup.closure (Set.range fun i => reflBar f (w i))
  have h32 : 2 ^ 5 ≤ Nat.card E := S12Insp4P.two_pow_le_card_closure hf (by omega) (by omega) hw
  obtain ⟨hcomm, hsq⟩ := S12Insp4P.closure_comm_sq (s := Set.range fun i => reflBar f (w i))
    (fun a ⟨i, hi⟩ b ⟨j, hj⟩ => by
      subst hi hj
      by_cases hij : i = j
      · rw [hij]
      · exact (reflBar_commute_iff hf (by omega) (hn1 i) (hn1 j)).2
          (Or.inl (by simp [hw, hij])))
    (fun a ⟨i, hi⟩ => by subst hi; exact reflBar_mul_self _)
  let θ : R3 f →* S.Mbar := (inclusion (Xbar12_le_Mbar (S := S) (g := g))).comp
    ψ.symm.toMonoidHom
  have hθ : Function.Injective θ :=
    (inclusion_injective (Xbar12_le_Mbar (S := S) (g := g))).comp ψ.symm.injective
  have hP := hE (E.map θ) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hsq a ha, map_one])
  rw [card_map_of_injective hθ] at hP
  omega

end Setting

end CFSG.LargeExtraspecial
