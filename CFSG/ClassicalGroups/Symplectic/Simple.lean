module

public import CFSG.Assembly.LowTwoRankDefs
import CFSG.ClassicalGroups.Symplectic.Model
import CFSG.ClassicalGroups.Symplectic.Perfect
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_12
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SumRootGeneration

public noncomputable section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix CFSG.Assembly.LowTwoRank
open scoped LinearAlgebra.Projectivization commutatorElement

variable {n : ℕ} {K : Type} [Field K]

private def form (n : ℕ) (K : Type) [Field K] :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) →ₗ[K] K :=
  Matrix.toLinearMap₂' K (J (Fin n) K)

private theorem form_apply (x y : Fin n ⊕ Fin n → K) :
    form n K x y = ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i)) := by
  simp [form, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Matrix.J,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

private theorem form_self (x : Fin n ⊕ Fin n → K) : form n K x x = 0 := by
  rw [form_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

private theorem form_swap (x y : Fin n ⊕ Fin n → K) : form n K y x = -form n K x y := by
  rw [form_apply, form_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem form_swap_ne_zero {x y : Fin n ⊕ Fin n → K} (h : form n K x y ≠ 0) :
    form n K y x ≠ 0 := by
  rw [form_swap]
  exact neg_ne_zero.mpr h

private theorem form_single_inl (x : Fin n ⊕ Fin n → K) (i : Fin n) :
    form n K x (Pi.single (Sum.inl i) 1) = x (Sum.inr i) := by
  rw [form_apply]
  simp [Pi.single_apply]

private theorem form_single_inr (x : Fin n ⊕ Fin n → K) (i : Fin n) :
    form n K x (Pi.single (Sum.inr i) 1) = -x (Sum.inl i) := by
  rw [form_apply]
  simp [Pi.single_apply]

private theorem eq_zero_of_form_eq_zero {x : Fin n ⊕ Fin n → K} (h : ∀ y, form n K x y = 0) :
    x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    rw [form_single_inr] at this
    simpa using this
  · have := h (Pi.single (Sum.inl i) 1)
    rwa [form_single_inl] at this

private theorem exists_form_ne_zero {x : Fin n ⊕ Fin n → K} (hx : x ≠ 0) :
    ∃ y, form n K x y ≠ 0 := by
  by_contra h
  exact hx (eq_zero_of_form_eq_zero fun y => not_not.mp fun hy => h ⟨y, hy⟩)

private theorem exists_form_ne_zero_ne_zero {v w : Fin n ⊕ Fin n → K} (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ z, form n K v z ≠ 0 ∧ form n K w z ≠ 0 := by
  obtain ⟨y₁, hy₁⟩ := exists_form_ne_zero hv
  obtain ⟨y₂, hy₂⟩ := exists_form_ne_zero hw
  by_cases h₁ : form n K w y₁ = 0
  · by_cases h₂ : form n K v y₂ = 0
    · refine ⟨y₁ + y₂, ?_, ?_⟩
      · rwa [map_add, h₂, add_zero]
      · rwa [map_add, h₁, zero_add]
    · exact ⟨y₂, h₂, hy₂⟩
  · exact ⟨y₁, hy₁, h₁⟩

private theorem exists_form_eq_zero_ne_zero {u v : Fin n ⊕ Fin n → K}
    (hv : ∀ c : K, v ≠ c • u) : ∃ z, form n K u z = 0 ∧ form n K v z ≠ 0 := by
  by_cases hu : u = 0
  · subst hu
    have hv0 : v ≠ 0 := by simpa using hv 0
    obtain ⟨z, hz⟩ := exists_form_ne_zero hv0
    exact ⟨z, by simp, hz⟩
  · obtain ⟨y, hy⟩ := exists_form_ne_zero hu
    by_contra hcon
    apply hv (form n K v y / form n K u y)
    have h0 : v - (form n K v y / form n K u y) • u = 0 := by
      apply eq_zero_of_form_eq_zero
      intro x
      have hz : form n K v (x - (form n K u x / form n K u y) • y) = 0 := by
        by_contra hne
        refine hcon ⟨x - (form n K u x / form n K u y) • y, ?_, hne⟩
        rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hy, sub_self]
      rw [map_sub, map_smul, smul_eq_mul] at hz
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination hz
    exact sub_eq_zero.mp h0

private theorem exists_form_eq_zero_ne_zero_ne_zero {u v w : Fin n ⊕ Fin n → K}
    (hv : ∀ c : K, v ≠ c • u) (hw : ∀ c : K, w ≠ c • u) :
    ∃ z, form n K u z = 0 ∧ form n K v z ≠ 0 ∧ form n K w z ≠ 0 := by
  obtain ⟨z₁, hu₁, hv₁⟩ := exists_form_eq_zero_ne_zero hv
  obtain ⟨z₂, hu₂, hw₂⟩ := exists_form_eq_zero_ne_zero hw
  by_cases h₁ : form n K w z₁ = 0
  · by_cases h₂ : form n K v z₂ = 0
    · refine ⟨z₁ + z₂, by rw [map_add, hu₁, hu₂, add_zero], ?_, ?_⟩
      · rwa [map_add, h₂, add_zero]
      · rwa [map_add, h₁, zero_add]
    · exact ⟨z₂, hu₂, h₂, hw₂⟩
  · exact ⟨z₁, hu₁, hv₁, h₁⟩

private theorem mem_symplecticGroup_iff_form (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    A ∈ symplecticGroup (Fin n) K ↔ ∀ x y, form n K (A *ᵥ x) (A *ᵥ y) = form n K x y := by
  have key : ∀ x y, form n K (A *ᵥ x) (A *ᵥ y) =
      Matrix.toLinearMap₂' K (Aᵀ * J (Fin n) K * A) x y := by
    intro x y
    rw [← Matrix.toLinearMap₂'_comp]
    simp [form, Matrix.toLin'_apply]
  rw [SymplecticGroup.mem_iff']
  constructor
  · intro h x y
    rw [key, h]
    rfl
  · intro h
    have h2 : (Matrix.toLinearMap₂' K (Aᵀ * J (Fin n) K * A) :
        (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) →ₗ[K] K) = form n K := by
      apply LinearMap.ext₂
      intro x y
      rw [← key, h]
    have h3 := congrArg (LinearMap.toMatrix₂' K) h2
    rwa [form, LinearMap.toMatrix'_toLinearMap₂', LinearMap.toMatrix'_toLinearMap₂'] at h3

private def ofLin (f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))
    (hf : ∀ x y, form n K (f x) (f y) = form n K x y) : TauCeti.GLSymplectic (Fin n) K :=
  ⟨TauCeti.GLSymplectic.ofSymplecticGroup (Fin n) K
    ⟨LinearMap.toMatrix' f, (mem_symplecticGroup_iff_form _).mpr (by
      simpa [LinearMap.toMatrix'_mulVec] using hf)⟩,
    TauCeti.GLSymplectic.ofSymplecticGroup_mem _ _ _⟩

private theorem ofLin_smul (f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))
    (hf : ∀ x y, form n K (f x) (f y) = form n K x y) (x : Fin n ⊕ Fin n → K) :
    ofLin f hf • x = f x := by
  change (TauCeti.GLSymplectic.ofSymplecticGroup (Fin n) K _ :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x = f x
  rw [TauCeti.GLSymplectic.coe_ofSymplecticGroup]
  exact LinearMap.toMatrix'_mulVec f x

private theorem form_smul (g : TauCeti.GLSymplectic (Fin n) K) (x y : Fin n ⊕ Fin n → K) :
    form n K (g • x) (g • y) = form n K x y :=
  (mem_symplecticGroup_iff_form _).mp (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp g.2)
    x y

private theorem ext_smul {g h : TauCeti.GLSymplectic (Fin n) K}
    (H : ∀ x : Fin n ⊕ Fin n → K, g • x = h • x) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => H _))

private def tv (u : Fin n ⊕ Fin n → K) (c : K) : TauCeti.GLSymplectic (Fin n) K :=
  ofLin (LinearMap.id + (c • (form n K).flip u).smulRight u) (by
    intro x y
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, map_add, map_smul, form_self]
    rw [form_swap u y]
    ring)

private theorem tv_smul (u : Fin n ⊕ Fin n → K) (c : K) (x : Fin n ⊕ Fin n → K) :
    tv u c • x = x + (c * form n K x u) • u := by
  rw [tv, ofLin_smul]
  simp

private theorem tv_zero (u : Fin n ⊕ Fin n → K) : tv u (0 : K) = 1 :=
  ext_smul fun x => by simp [tv_smul]

private theorem tv_add (u : Fin n ⊕ Fin n → K) (c d : K) : tv u (c + d) = tv u c * tv u d :=
  ext_smul fun x => by
    rw [mul_smul, tv_smul, tv_smul, tv_smul]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, form_self,
      smul_eq_mul, mul_zero, add_zero]
    module

private theorem tv_conj (g : TauCeti.GLSymplectic (Fin n) K) (u : Fin n ⊕ Fin n → K) (c : K) :
    g * tv u c * g⁻¹ = tv (g • u) c :=
  ext_smul fun x => by
    rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, smul_inv_smul, smul_comm g _ u,
      ← form_smul g (g⁻¹ • x) u, smul_inv_smul]

private theorem tv_smul_vec (a c : K) (u : Fin n ⊕ Fin n → K) :
    tv (a • u) c = tv u (a ^ 2 * c) :=
  ext_smul fun x => by
    rw [tv_smul, tv_smul, map_smul, smul_smul, smul_eq_mul]
    congr 2
    ring

private def tvHom (u : Fin n ⊕ Fin n → K) :
    Multiplicative K →* TauCeti.GLSymplectic (Fin n) K where
  toFun c := tv u c.toAdd
  map_one' := tv_zero u
  map_mul' c d := tv_add u c.toAdd d.toAdd

private theorem exists_fix_map {u v w : Fin n ⊕ Fin n → K}
    (h : form n K u v = form n K u w) (hvw : form n K v w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin n) K, g • u = u ∧ g • v = w := by
  refine ⟨tv (w - v) (form n K v w)⁻¹, ?_, ?_⟩
  · rw [tv_smul, map_sub, h, sub_self, mul_zero, zero_smul, add_zero]
  · rw [tv_smul, map_sub, form_self, sub_zero, inv_mul_cancel₀ hvw, one_smul]
    abel

private theorem exists_fix_map_two {u v z w : Fin n ⊕ Fin n → K}
    (h₁ : form n K u v = form n K u z) (h₂ : form n K u z = form n K u w)
    (hvz : form n K v z ≠ 0) (hzw : form n K z w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin n) K, g • u = u ∧ g • v = w := by
  obtain ⟨g₁, hg₁u, hg₁v⟩ := exists_fix_map h₁ hvz
  obtain ⟨g₂, hg₂u, hg₂z⟩ := exists_fix_map h₂ hzw
  exact ⟨g₂ * g₁, by rw [mul_smul, hg₁u, hg₂u], by rw [mul_smul, hg₁v, hg₂z]⟩

private theorem exists_smul_eq_vec {v w : Fin n ⊕ Fin n → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin n) K, g • v = w := by
  by_cases hvw : form n K v w = 0
  · obtain ⟨z, hvz, hwz⟩ := exists_form_ne_zero_ne_zero hv hw
    obtain ⟨g, -, hg⟩ := exists_fix_map_two (u := 0) (v := v) (z := z) (w := w)
      (by simp) (by simp) hvz (form_swap_ne_zero hwz)
    exact ⟨g, hg⟩
  · obtain ⟨g, -, hg⟩ := exists_fix_map (u := 0) (by simp) hvw
    exact ⟨g, hg⟩

private theorem single_ne_zero (k : Fin n ⊕ Fin n) :
    (Pi.single k 1 : Fin n ⊕ Fin n → K) ≠ 0 := by
  intro h
  have := congrFun h k
  simp at this

private theorem smul_mk' (g : TauCeti.GLSymplectic (Fin n) K) {v : Fin n ⊕ Fin n → K}
    (hv : v ≠ 0) :
    g • Projectivization.mk K v hv =
      Projectivization.mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv) :=
  rfl

private theorem smul_mk_of_smul_eq {g : TauCeti.GLSymplectic (Fin n) K}
    {u v : Fin n ⊕ Fin n → K} (hu : u ≠ 0) (hv : v ≠ 0) (h : g • u = v) :
    g • Projectivization.mk K u hu = Projectivization.mk K v hv := by
  rw [smul_mk', Projectivization.mk_eq_mk_iff']
  exact ⟨1, by rw [one_smul, h]⟩

private theorem exists_fix_smul_mk_of_form_ne_zero {u v w : Fin n ⊕ Fin n → K} (hv : v ≠ 0)
    (hw : w ≠ 0) (huv : form n K u v ≠ 0) (huw : form n K u w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin n) K,
      g • u = u ∧ g • Projectivization.mk K v hv = Projectivization.mk K w hw := by
  set a := form n K u v / form n K u w with ha
  have hw' : a • w ≠ 0 := smul_ne_zero (div_ne_zero huv huw) hw
  have huw' : form n K u (a • w) = form n K u v := by
    rw [map_smul, smul_eq_mul, ha, div_mul_cancel₀ _ huw]
  suffices ∃ g : TauCeti.GLSymplectic (Fin n) K, g • u = u ∧ g • v = a • w by
    obtain ⟨g, hgu, hgv⟩ := this
    refine ⟨g, hgu, ?_⟩
    rw [smul_mk', Projectivization.mk_eq_mk_iff']
    exact ⟨a, hgv.symm⟩
  by_cases hvw : form n K v (a • w) = 0
  · refine exists_fix_map_two (z := v + u) ?_ ?_ ?_ ?_
    · rw [map_add, form_self, add_zero]
    · rw [map_add, form_self, add_zero, huw']
    · rw [map_add, form_self, zero_add]
      exact form_swap_ne_zero huv
    · rw [map_add, LinearMap.add_apply, hvw, zero_add, huw']
      exact huv
  · exact exists_fix_map huw'.symm hvw

private theorem exists_fix_smul_mk_of_form_eq_zero {u v w : Fin n ⊕ Fin n → K} (hv : v ≠ 0)
    (hw : w ≠ 0) (huv : form n K u v = 0) (huw : form n K u w = 0) (hvu : ∀ c : K, v ≠ c • u)
    (hwu : ∀ c : K, w ≠ c • u) :
    ∃ g : TauCeti.GLSymplectic (Fin n) K,
      g • u = u ∧ g • Projectivization.mk K v hv = Projectivization.mk K w hw := by
  suffices ∃ g : TauCeti.GLSymplectic (Fin n) K, g • u = u ∧ g • v = w by
    obtain ⟨g, hgu, hgv⟩ := this
    exact ⟨g, hgu, smul_mk_of_smul_eq hv hw hgv⟩
  by_cases hvw : form n K v w = 0
  · obtain ⟨z, huz, hvz, hwz⟩ := exists_form_eq_zero_ne_zero_ne_zero hvu hwu
    exact exists_fix_map_two (by rw [huv, huz]) (by rw [huz, huw]) hvz (form_swap_ne_zero hwz)
  · exact exists_fix_map (by rw [huv, huw]) hvw

private theorem isPretransitive :
    MulAction.IsPretransitive (TauCeti.GLSymplectic (Fin n) K) (ℙ K (Fin n ⊕ Fin n → K)) := by
  refine ⟨fun x y => ?_⟩
  induction x using Projectivization.ind with | h v hv => ?_
  induction y using Projectivization.ind with | h w hw => ?_
  obtain ⟨z, hvz, hwz⟩ := exists_form_ne_zero_ne_zero hv hw
  obtain ⟨g, -, hg⟩ := exists_fix_smul_mk_of_form_ne_zero (u := z) hv hw
    (form_swap_ne_zero hvz) (form_swap_ne_zero hwz)
  exact ⟨g, hg⟩

section Blocks

variable {B : Set (ℙ K (Fin n ⊕ Fin n → K))}

private theorem smul_mem_of_isBlock
    (hB : MulAction.IsBlock (TauCeti.GLSymplectic (Fin n) K) B)
    {x y : ℙ K (Fin n ⊕ Fin n → K)} (hx : x ∈ B) (hy : y ∈ B)
    {g : TauCeti.GLSymplectic (Fin n) K} (hg : g • x = x) : g • y ∈ B := by
  have h := hB.smul_eq_of_mem hx (by rwa [hg])
  rw [← h]
  exact Set.smul_mem_smul_set hy

private theorem mem_of_isBlock_of_form_ne_zero
    (hB : MulAction.IsBlock (TauCeti.GLSymplectic (Fin n) K) B) {u v w : Fin n ⊕ Fin n → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (huB : Projectivization.mk K u hu ∈ B)
    (hvB : Projectivization.mk K v hv ∈ B) (huv : form n K u v ≠ 0) (huw : form n K u w ≠ 0) :
    Projectivization.mk K w hw ∈ B := by
  obtain ⟨g, hgu, hg⟩ := exists_fix_smul_mk_of_form_ne_zero hv hw huv huw
  rw [← hg]
  exact smul_mem_of_isBlock hB huB hvB (smul_mk_of_smul_eq hu hu hgu)

private theorem mem_of_isBlock_of_form_eq_zero
    (hB : MulAction.IsBlock (TauCeti.GLSymplectic (Fin n) K) B) {u v w : Fin n ⊕ Fin n → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (huB : Projectivization.mk K u hu ∈ B)
    (hvB : Projectivization.mk K v hv ∈ B) (huv : form n K u v = 0) (hvu : ∀ c : K, v ≠ c • u)
    (huw : form n K u w = 0) (hwu : ∀ c : K, w ≠ c • u) :
    Projectivization.mk K w hw ∈ B := by
  obtain ⟨g, hgu, hg⟩ := exists_fix_smul_mk_of_form_eq_zero hv hw huv huw hvu hwu
  rw [← hg]
  exact smul_mem_of_isBlock hB huB hvB (smul_mk_of_smul_eq hu hu hgu)

private theorem eq_univ_of_isBlock
    (hB : MulAction.IsBlock (TauCeti.GLSymplectic (Fin n) K) B) {u v : Fin n ⊕ Fin n → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (huB : Projectivization.mk K u hu ∈ B)
    (hvB : Projectivization.mk K v hv ∈ B) (huv : form n K u v ≠ 0) : B = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Projectivization.ind with | h w hw => ?_
  by_cases huw : form n K u w = 0
  · obtain ⟨z, huz, hwz⟩ := exists_form_ne_zero_ne_zero hu hw
    have hz : z ≠ 0 := by
      rintro rfl
      simp at huz
    have hzB := mem_of_isBlock_of_form_ne_zero hB hu hv hz huB hvB huv huz
    exact mem_of_isBlock_of_form_ne_zero hB hz hu hw hzB huB (form_swap_ne_zero huz)
      (form_swap_ne_zero hwz)
  · exact mem_of_isBlock_of_form_ne_zero hB hu hv hw huB hvB huv huw

end Blocks

private theorem isPreprimitive (hn : 1 ≤ n) :
    MulAction.IsPreprimitive (TauCeti.GLSymplectic (Fin n) K) (ℙ K (Fin n ⊕ Fin n → K)) := by
  have := isPretransitive (n := n) (K := K)
  set e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl ⟨0, hn⟩) 1
  have he : e ≠ 0 := single_ne_zero _
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (Projectivization.mk K e he)
  intro B haB hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨b, hbB, hba⟩ : ∃ b ∈ B, b ≠ Projectivization.mk K e he := by
    by_contra hcon
    refine hsub fun x hx y hy => ?_
    have hx' : x = Projectivization.mk K e he := not_not.mp fun h => hcon ⟨x, hx, h⟩
    have hy' : y = Projectivization.mk K e he := not_not.mp fun h => hcon ⟨y, hy, h⟩
    rw [hx', hy']
  induction b using Projectivization.ind with | h v hv => ?_
  by_cases hev : form n K e v = 0
  · have hev' : ∀ c : K, e ≠ c • v := by
      intro c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact he (by rw [hc, zero_smul])
      apply hba
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨c⁻¹, by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
    obtain ⟨z, hvz, hez⟩ := exists_form_eq_zero_ne_zero hev'
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hez
    have hzv : ∀ c : K, z ≠ c • v := by
      intro c hc
      apply hez
      rw [hc, map_smul, hev, smul_zero]
    have hzB := mem_of_isBlock_of_form_eq_zero hB hv he hz hbB haB
      (by rw [form_swap, hev, neg_zero]) hev' hvz hzv
    exact eq_univ_of_isBlock hB he hz haB hzB hez
  · exact eq_univ_of_isBlock hB he hv haB hbB hev

private theorem transvection_mulVec_single (i j : Fin n ⊕ Fin n) (c : K)
    (x : Fin n ⊕ Fin n → K) :
    Matrix.transvection i j c *ᵥ x = x + (c * x j) • Pi.single i 1 := by
  ext k
  by_cases hk : k = i
  · subst hk
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hk]

private theorem mulEquiv_positiveLong (i : Fin n) (c : K) :
    TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K
        (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit i c) =
      tv (Pi.single (Sum.inl i) 1) c := by
  apply ext_smul
  intro x
  rw [tv_smul, form_single_inl]
  change (((TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K
      (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit i c) :
        TauCeti.GLSymplectic (Fin n) K) : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x = _
  rw [TauCeti.GLSymplecticFin.coe_mulEquivGLSymplectic,
    TauCeti.GLSymplecticFin.coe_positiveLongRootTransvectionUnit,
    TauCeti.GLSymplecticFin.reindexGL_transvectionUnit (Sum.inl i) (Sum.inr i) Sum.inl_ne_inr c,
    TauCeti.coe_transvectionUnit, transvection_mulVec_single]

private theorem mulEquiv_negativeLong (i : Fin n) (c : K) :
    TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K
        (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit i c) =
      tv (Pi.single (Sum.inr i) 1) (-c) := by
  apply ext_smul
  intro x
  rw [tv_smul, form_single_inr, neg_mul_neg]
  change (((TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K
      (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit i c) :
        TauCeti.GLSymplectic (Fin n) K) : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x = _
  rw [TauCeti.GLSymplecticFin.coe_mulEquivGLSymplectic,
    TauCeti.GLSymplecticFin.coe_negativeLongRootTransvectionUnit,
    TauCeti.GLSymplecticFin.reindexGL_transvectionUnit (Sum.inr i) (Sum.inl i) Sum.inr_ne_inl c,
    TauCeti.coe_transvectionUnit, transvection_mulVec_single]

open TauCeti.GLSymplecticFin in
private theorem normalClosure_range_tvHom (hn : 1 ≤ n) :
    Subgroup.normalClosure
      (Set.range (tvHom (n := n) (K := K) (Pi.single (Sum.inl ⟨0, hn⟩) 1))) = ⊤ := by
  set e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl ⟨0, hn⟩) 1
  have he : e ≠ 0 := single_ne_zero _
  set N := Subgroup.normalClosure (Set.range (tvHom (n := n) (K := K) e))
  have hN : N.Normal := Subgroup.normalClosure_normal
  have htv : ∀ u : Fin n ⊕ Fin n → K, u ≠ 0 → ∀ c : K, tv u c ∈ N := by
    intro u hu c
    obtain ⟨g, hg⟩ := exists_smul_eq_vec he hu
    rw [← hg, ← tv_conj]
    exact hN.conj_mem _ (Subgroup.subset_normalClosure ⟨Multiplicative.ofAdd c, rfl⟩) g
  set φ := mulEquivGLSymplectic n K
  set N' := N.comap φ.toMonoidHom
  have hN' : N'.Normal := hN.comap _
  have hpos : ∀ (i : Fin n) (c : K),
      positiveLongRootTransvectionUnit i c ∈ N' := by
    intro i c
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mulEquiv_positiveLong]
    exact htv _ (single_ne_zero _) c
  have hneg : ∀ (i : Fin n) (c : K),
      negativeLongRootTransvectionUnit i c ∈ N' := by
    intro i c
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mulEquiv_negativeLong]
    exact htv _ (single_ne_zero _) _
  have hcomm : ∀ g x : TauCeti.GLSymplecticFin n K, x ∈ N' → ⁅g, x⁆ ∈ N' := by
    intro g x hx
    rw [commutatorElement_def]
    exact N'.mul_mem (hN'.conj_mem x hx g) (N'.inv_mem hx)
  have hdiff : ∀ {i j : Fin n} (hij : i ≠ j) (c : K),
      differenceShortRootUnit hij c ∈ N' := by
    intro i j hij c
    have h := hcomm (positiveSumShortRootUnit hij 1) _ (hneg j c)
    rw [commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit] at h
    simp only [one_mul, one_pow] at h
    exact (N'.mul_mem_cancel_right (hpos i _)).mp h
  have htop : N' = ⊤ := eq_top_of_root_subgroups N'
    (rootSubgroupHom_mem_of_difference_long N' hdiff hpos hneg)
  rw [eq_top_iff]
  intro g _
  have hg : φ.symm g ∈ N' := by
    rw [htop]
    exact Subgroup.mem_top _
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hg

private theorem smul_eq_of_mem_scalars {g : TauCeti.GLSymplectic (Fin n) K}
    (hg : g ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (TauCeti.GLSymplectic (Fin n) K))
    (x : ℙ K (Fin n ⊕ Fin n → K)) : g • x = x := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨u, hu⟩ := hg
  induction x using Projectivization.ind with | h v hv => ?_
  rw [smul_mk', Projectivization.mk_eq_mk_iff']
  refine ⟨(u : K), ?_⟩
  change (u : K) • v = ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n)
    (Fin n ⊕ Fin n) K) *ᵥ v
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext k
  simp [Matrix.mulVec_diagonal]

private theorem mem_scalars_of_forall_smul_eq (hn : 1 ≤ n) {g : TauCeti.GLSymplectic (Fin n) K}
    (hg : ∀ x : ℙ K (Fin n ⊕ Fin n → K), g • x = x) :
    g ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (TauCeti.GLSymplectic (Fin n) K) := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := ((g : GL (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hM
  have hgM : ∀ v, g • v = M *ᵥ v := fun v => rfl
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := Matrix.toLin' M) (fun v => by
      by_cases hv : v = 0
      · subst hv
        intro hli
        exact hli.ne_zero 0 rfl
      · rw [LinearIndependent.pair_iff' hv]
        intro hli
        have hp := hg (Projectivization.mk K v hv)
        rw [smul_mk', Projectivization.mk_eq_mk_iff'] at hp
        obtain ⟨c, hc⟩ := hp
        exact hli c (by rw [Matrix.toLin'_apply, hc, hgM]))
  have hMv : ∀ v, M *ᵥ v = a • v := by
    intro v
    have := LinearMap.congr_fun ha v
    simpa [Matrix.toLin'_apply] using this
  set e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl ⟨0, hn⟩) 1
  have he : e ≠ 0 := single_ne_zero _
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply he
    have h0 : g • e = 0 := by rw [hgM, hMv, zero_smul]
    exact (smul_eq_zero_iff_eq g).mp h0
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hM]
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [hMv, Matrix.scalar_apply]
  ext l
  simp [Matrix.mulVec_diagonal]

private theorem isSimpleGroup_statedProj_GLSymplectic (K : Type) [Field K] (n : ℕ)
    (hn : 1 ≤ n)
    (h : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ n) ∨ (Nat.card K = 2 ∧ 3 ≤ n)) :
    IsSimpleGroup (StatedProj (TauCeti.GLSymplectic (Fin n) K)) := by
  let G := TauCeti.GLSymplectic (Fin n) K
  let X := ℙ K (Fin n ⊕ Fin n → K)
  let Z := (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf G
  let P := StatedProj G
  have hZ : Z ≤ (MulAction.toPermHom G X).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun x => smul_eq_of_mem_scalars hg x
  let ρ : P →* Equiv.Perm X := QuotientGroup.lift Z (MulAction.toPermHom G X) hZ
  let _ : MulAction P X := MulAction.compHom X ρ
  have hsmul : ∀ (g : G) (x : X), ((g : P)) • x = g • x := fun _ _ => rfl
  set e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl ⟨0, hn⟩) 1
  have he : e ≠ 0 := single_ne_zero _
  have : FaithfulSMul P X := faithfulSMul_iff.mpr (by
    intro p hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [QuotientGroup.eq_one_iff]
    exact mem_scalars_of_forall_smul_eq hn fun x => hp x)
  have : MulAction.IsPreprimitive G X := isPreprimitive hn
  have : MulAction.IsPreprimitive P X :=
    MulAction.IsPreprimitive.of_surjective
      (f := (⟨id, fun _ _ => rfl⟩ : X →ₑ[(QuotientGroup.mk : G → P)] X)) Function.surjective_id
  have : Nontrivial P := by
    set e' : Fin n ⊕ Fin n → K := Pi.single (Sum.inr ⟨0, hn⟩) 1
    have he' : e' ≠ 0 := single_ne_zero _
    refine ⟨⟨((tv e 1 : G) : P), 1, fun h1 => ?_⟩⟩
    have hx := congrArg (· • Projectivization.mk K e' he') h1
    simp only [one_smul] at hx
    rw [hsmul, smul_mk', Projectivization.mk_eq_mk_iff'] at hx
    obtain ⟨c, hc⟩ := hx
    have hc' := congrFun hc (Sum.inl ⟨0, hn⟩)
    rw [tv_smul, form_single_inl] at hc'
    simp [e, e'] at hc'
  have hperfect : commutator P = ⊤ := by
    have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) := isPerfect_GLSymplecticFin K n h
    have : Group.IsPerfect G := Group.IsPerfect.ofSurjective
      (f := (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).toMonoidHom)
      (MulEquiv.surjective _)
    exact Group.IsPerfect.commutator_eq_top
  let T : Subgroup P := ((QuotientGroup.mk' Z).comp (tvHom e)).range
  have hT : ∀ c, ((QuotientGroup.mk' Z).comp (tvHom e)) c = ((tv e c.toAdd : G) : P) :=
    fun _ => rfl
  have hTle : T ≤ MulAction.stabilizer P (Projectivization.mk K e he) := by
    rintro _ ⟨c, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change tv e c.toAdd • Projectivization.mk K e he = Projectivization.mk K e he
    exact smul_mk_of_smul_eq he he (by rw [tv_smul, form_self, mul_zero, zero_smul, add_zero])
  have hTnormal : (T.subgroupOf (MulAction.stabilizer P (Projectivization.mk K e he))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTle]
    rintro _ p ⟨c, rfl⟩ hp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [MulAction.mem_stabilizer_iff, hsmul, smul_mk',
      Projectivization.mk_eq_mk_iff'] at hp
    obtain ⟨l, hl⟩ := hp
    refine ⟨Multiplicative.ofAdd (l ^ 2 * c.toAdd), ?_⟩
    rw [hT, hT, toAdd_ofAdd, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, tv_conj, ← hl, tv_smul_vec]
  have hTsolv : Group.IsSolvable T := by
    apply Group.isSolvable_of_comm
    rintro ⟨_, ⟨c, rfl⟩⟩ ⟨_, ⟨d, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  have hTgen : Subgroup.normalClosure (T : Set P) = ⊤ := by
    have hset : (T : Set P) = QuotientGroup.mk' Z '' Set.range (tvHom e) := by
      rw [MonoidHom.coe_range, MonoidHom.coe_comp, Set.range_comp]
    rw [hset, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective Z),
      normalClosure_range_tvHom hn,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]
  exact CFSG.BenderSuzuki.External.huppert_II_6_12 hperfect (Projectivization.mk K e he) T
    hTle hTnormal hTsolv hTgen

theorem isSimpleGroup_statedProj_statedSp (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n)
    (h : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ n) ∨ (Nat.card K = 2 ∧ 3 ≤ n)) :
    IsSimpleGroup (StatedProj (StatedSp n K)) := by
  rw [statedSp_eq_GLSymplectic]
  exact isSimpleGroup_statedProj_GLSymplectic K n hn h

theorem finite_statedProj_statedSp (n : ℕ) (K : Type) [Field K] [Finite K] :
    Finite (StatedProj (StatedSp n K)) :=
  inferInstance

theorem fam_symplectic_projective_simple (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n)
    (h : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ n) ∨ (Nat.card K = 2 ∧ 3 ≤ n)) :
    IsSimpleGroup (StatedProj (StatedSp n K)) ∧
      (Finite K → Finite (StatedProj (StatedSp n K))) :=
  ⟨isSimpleGroup_statedProj_statedSp K n hn h, fun _ => finite_statedProj_statedSp n K⟩

theorem isSimpleGroup_of_statedClassicalModel_PSp (G : Type) [Group G] (n p f : ℕ)
    (h : StatedClassicalModel G .PSp n p f) : IsSimpleGroup G := by
  obtain ⟨⟨hp, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have := isSimpleGroup_statedProj_statedSp K n (by omega) (by
    rw [hK]
    rcases Nat.lt_or_ge (p ^ f) 4 with h4 | h4
    · rcases (show p ^ f = 2 ∨ p ^ f = 3 by omega) with h2 | h3
      · have hn2 : n ≠ 2 := by
          rintro rfl
          exact hne (by rw [h2])
        exact Or.inr (Or.inr ⟨h2, by omega⟩)
      · exact Or.inr (Or.inl ⟨h3, hn⟩)
    · exact Or.inl (Or.inr h4))
  exact e.isSimpleGroup

end CFSG.ClassicalGroups.Symplectic
