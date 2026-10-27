module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.V_comm_A₂ (hd : d.Hyp) {v a : G} (hv : v ∈ d.V) (ha : a ∈ d.A₂) : v * a = a * v :=
  (mem_centralizer_iff.1 (hd.CB₄I₃_le_centralizer_P (hd.V_le_CB₄I₃ hv)) a (d.A₂_le_P ha)).symm

theorem Hyp.t_comm_A₂ (hd : d.Hyp) {a : G} (ha : a ∈ d.A₂) : d.t * a = a * d.t :=
  (hd.comm_t (d.A₂_le_L ha)).symm

theorem Hyp.V_inf_A₂ (hd : d.Hyp) : d.V ⊓ d.A₂ = d.Zp :=
  le_antisymm (fun x hx => by rw [← hd.V_inf_B₂]; exact ⟨hx.1, mem_sup_right hx.2⟩)
    (le_inf hd.Zp_le_V d.Zp_le_A₂)

theorem Hyp.V_le_B₄ (hd : d.Hyp) : d.V ≤ d.B₄ := hd.V_le_CB₄I₃.trans d.CB₄I₃_le

theorem Hyp.B₂_le_B₄ (hd : d.Hyp) : d.B₂ ≤ d.B₄ := hd.B₄_eq_V_sup_B₂ ▸ le_sup_right

theorem Hyp.A₂_le_B₄ (hd : d.Hyp) : d.A₂ ≤ d.B₄ := (le_sup_right : d.A₂ ≤ d.B₂).trans hd.B₂_le_B₄

theorem Hyp.t_mem_B₄ (hd : d.Hyp) : d.t ∈ d.B₄ := hd.B₂_le_B₄ (mem_sup_left (mem_zpowers _))

theorem Hyp.VA_le_B₄ (hd : d.Hyp) : d.V ⊔ d.A₂ ≤ d.B₄ := sup_le hd.V_le_B₄ hd.A₂_le_B₄

theorem Hyp.t_conj_mem_V (hd : d.Hyp) {v : G} (hv : v ∈ d.V) : d.t * v * d.t ∈ d.V := by
  rw [show d.t * v * d.t = v * (v⁻¹ * d.t * v * d.t) by group]
  exact mul_mem hv (hd.Zp_le_V (hd.cr_mem (hd.V_le_B₄ hv)))

theorem Hyp.exists_mul_of_mem_VA (hd : d.Hyp) {x : G} (hx : x ∈ d.V ⊔ d.A₂) :
    ∃ v ∈ d.V, ∃ a ∈ d.A₂, x = v * a :=
  exists_mul_of_mem_sup_of_le_normalizer (fun _ ha => Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ hv => hd.V_comm_A₂ hv ha)) hx

theorem Hyp.comm_V_of_mem_VA (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x v : G} (hx : x ∈ d.V ⊔ d.A₂) (hv : v ∈ d.V) : x * v = v * x := by
  obtain ⟨w, hw, a, ha, rfl⟩ := hd.exists_mul_of_mem_VA hx
  rw [mul_assoc, ← hd.V_comm_A₂ hv ha, ← mul_assoc, hd.comm_of_mem_V hGMS hw hv, mul_assoc]

theorem Hyp.exists_of_mem_B₄ (hd : d.Hyp) {x : G} (hx : x ∈ d.B₄) :
    ∃ v ∈ d.V, ∃ a ∈ d.A₂, x = v * a ∨ x = d.t * (v * a) := by
  rw [hd.B₄_eq_V_sup_B₂] at hx
  have hBV : d.B₂ ≤ normalizer (d.V : Set G) := by
    refine sup_le (zpowers_le.2 (mem_normalizer_fintype fun v hv => ?_)) fun _ ha =>
      Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun _ hv => hd.V_comm_A₂ hv ha)
    rw [show d.t * v * d.t⁻¹ = d.t * v * d.t by rw [inv_eq_of_mul_eq_one_right hd.t_mul_t]]
    exact hd.t_conj_mem_V hv
  obtain ⟨v, hv, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBV hx
  obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hb <;> subst b
  · exact ⟨v, hv, a, ha, Or.inl rfl⟩
  · refine ⟨d.t * v * d.t, hd.t_conj_mem_V hv, a, ha, Or.inr ?_⟩
    calc v * (d.t * a) = (d.t * d.t) * v * d.t * a := by rw [hd.t_mul_t]; group
      _ = d.t * (d.t * v * d.t * a) := by group

theorem Hyp.exists_Zp_ne_ne (hd : d.Hyp) (a b : G) : ∃ z ∈ d.Zp, z ≠ a ∧ z ≠ b :=
  exists_mem_ne_ne (by rw [d.card_Zp]; have := hd.four_le; omega) a b

theorem Hyp.exists_V_not_comm_t (hd : d.Hyp) : ∃ w ∈ d.V, d.t * w ≠ w * d.t := by
  obtain ⟨z, hz, hz1, -⟩ := hd.exists_Zp_ne_ne 1 1
  obtain ⟨w, hw, hwz⟩ := hd.exists_V_cr_eq hz
  refine ⟨w, hw, fun e => hz1 ?_⟩
  rw [← hwz]
  calc w⁻¹ * d.t * w * d.t = w⁻¹ * (d.t * w) * d.t := by group
    _ = w⁻¹ * (w * d.t) * d.t := by rw [e]
    _ = d.t * d.t := by group
    _ = 1 := hd.t_mul_t

theorem Hyp.t_not_mem_VA (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.t ∉ d.V ⊔ d.A₂ := fun ht => by
  obtain ⟨w, hw, hwt⟩ := hd.exists_V_not_comm_t
  exact hwt (hd.comm_V_of_mem_VA hGMS ht hw)

theorem Hyp.exists_A₂_not_comm (hd : d.Hyp) {a : G} (ha : a ∈ d.A₂) (haZ : a ∉ d.Zp) :
    ∃ m₁ ∈ d.A₂, ∃ m₂ ∈ d.A₂, m₁ * a * m₁⁻¹ ≠ a ∧ m₂ * a * m₂⁻¹ ≠ a ∧
      m₁ * a * m₁⁻¹ ≠ m₂ * a * m₂⁻¹ := by
  obtain ⟨g, hg, rfl⟩ := ha
  have hgZ : g ∉ ZPsub h := fun hgZ => haZ ⟨g, hgZ, rfl⟩
  obtain ⟨m₁, hm₁, m₂, hm₂, h1, h2, h12⟩ := exists_A₂sub_not_comm hd.two_le hg hgZ
  have hU : ∀ {x : hypSU h 2 1}, x ∈ A₂sub h → x ∈ hypUnitriangular h 2 1 := fun hx =>
    A₂sub_le_U hx
  have hc : ∀ {m : hypSU h 2 1}, m ∈ A₂sub h → d.η m * d.η g * (d.η m)⁻¹ = d.η g →
      m * g = g * m := fun {m} hm e => by
    have e' : m * g * m⁻¹ = g := d.η_injOn (hU (mul_mem (mul_mem hm hg) (inv_mem hm))) (hU hg)
      (by rw [map_mul, map_mul, map_inv]; exact e)
    calc m * g = m * g * m⁻¹ * m := by group
      _ = g * m := by rw [e']
  refine ⟨d.η m₁, ⟨m₁, hm₁, rfl⟩, d.η m₂, ⟨m₂, hm₂, rfl⟩, fun e => h1 (hc hm₁ e),
    fun e => h2 (hc hm₂ e), fun e => h12 ?_⟩
  refine d.η_injOn (hU (mul_mem (mul_mem hm₁ hg) (inv_mem hm₁)))
    (hU (mul_mem (mul_mem hm₂ hg) (inv_mem hm₂))) ?_
  simpa only [map_mul, map_inv] using e

theorem Hyp.exists_conj_ne_of_not_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {x : G} (hx : x ∈ d.B₄) (hxV : x ∉ d.V) :
    ∃ m₁ ∈ d.B₄, ∃ m₂ ∈ d.B₄, m₁ * x * m₁⁻¹ ≠ x ∧ m₂ * x * m₂⁻¹ ≠ x ∧
      m₁ * x * m₁⁻¹ ≠ m₂ * x * m₂⁻¹ := by
  have hne : ∀ {z y : G}, z ≠ 1 → z * y ≠ y := fun hz e =>
    hz (mul_right_cancel (e.trans (one_mul _).symm))
  have hne' : ∀ {z z' y : G}, z ≠ z' → z * y ≠ z' * y := fun hz e => hz (mul_right_cancel e)
  obtain ⟨v, hv, a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₄ hx
  · have haZ : a ∉ d.Zp := fun haZ => hxV (mul_mem hv (hd.Zp_le_V haZ))
    obtain ⟨m₁, hm₁, m₂, hm₂, h1, h2, h12⟩ := hd.exists_A₂_not_comm ha haZ
    have key : ∀ m ∈ d.A₂, m * (v * a) * m⁻¹ = v * (m * a * m⁻¹) := fun m hm => by
      calc m * (v * a) * m⁻¹ = (m * v) * a * m⁻¹ := by group
        _ = (v * m) * a * m⁻¹ := by rw [hd.V_comm_A₂ hv hm]
        _ = v * (m * a * m⁻¹) := by group
    refine ⟨m₁, hd.A₂_le_B₄ hm₁, m₂, hd.A₂_le_B₄ hm₂, ?_, ?_, ?_⟩
    · rw [key m₁ hm₁]
      exact fun e => h1 (mul_left_cancel e)
    · rw [key m₂ hm₂]
      exact fun e => h2 (mul_left_cancel e)
    · rw [key m₁ hm₁, key m₂ hm₂]
      exact fun e => h12 (mul_left_cancel e)
  · obtain ⟨z₁, hz₁, hz₁1, -⟩ := hd.exists_Zp_ne_ne 1 1
    obtain ⟨z₂, hz₂, hz₂1, hz₂₁⟩ := hd.exists_Zp_ne_ne 1 z₁
    obtain ⟨w₁, hw₁, hw₁z⟩ := hd.exists_V_cr_eq hz₁
    obtain ⟨w₂, hw₂, hw₂z⟩ := hd.exists_V_cr_eq hz₂
    have hva : v * a ∈ d.V ⊔ d.A₂ := mul_mem (mem_sup_left hv) (mem_sup_right ha)
    have key : ∀ w ∈ d.V, w⁻¹ * (d.t * (v * a)) * w⁻¹⁻¹ =
        (w⁻¹ * d.t * w * d.t) * (d.t * (v * a)) := by
      intro w hw
      calc w⁻¹ * (d.t * (v * a)) * w⁻¹⁻¹ = w⁻¹ * d.t * ((v * a) * w) := by group
        _ = w⁻¹ * d.t * (w * (v * a)) := by rw [hd.comm_V_of_mem_VA hGMS hva hw]
        _ = w⁻¹ * d.t * w * (d.t * d.t) * (v * a) := by rw [hd.t_mul_t]; group
        _ = (w⁻¹ * d.t * w * d.t) * (d.t * (v * a)) := by group
    refine ⟨w₁⁻¹, inv_mem (hd.V_le_B₄ hw₁), w₂⁻¹, inv_mem (hd.V_le_B₄ hw₂), ?_, ?_, ?_⟩
    · rw [key w₁ hw₁, hw₁z]
      exact hne hz₁1
    · rw [key w₂ hw₂, hw₂z]
      exact hne hz₂1
    · rw [key w₁ hw₁, key w₂ hw₂, hw₁z, hw₂z]
      exact hne' (Ne.symm hz₂₁)

theorem Hyp.conj_V_eq_or (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {v m : G} (hv : v ∈ d.V) (hm : m ∈ d.B₄) :
    m * v * m⁻¹ = v ∨ m * v * m⁻¹ = d.t * v * d.t⁻¹ := by
  obtain ⟨w, hw, a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₄ hm
  · left
    rw [hd.comm_V_of_mem_VA hGMS (mul_mem (mem_sup_left hw) (mem_sup_right ha)) hv,
      mul_inv_cancel_right]
  · right
    rw [show d.t * (w * a) * v * (d.t * (w * a))⁻¹ =
        d.t * ((w * a) * v * (w * a)⁻¹) * d.t⁻¹ by group,
      hd.comm_V_of_mem_VA hGMS (mul_mem (mem_sup_left hw) (mem_sup_right ha)) hv,
      mul_inv_cancel_right]

theorem Hyp.mem_V_iff (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x : G}
    (hx : x ∈ d.B₄) :
    x ∈ d.V ↔ ∀ m₁ ∈ d.B₄, ∀ m₂ ∈ d.B₄,
      m₁ * x * m₁⁻¹ = x ∨ m₂ * x * m₂⁻¹ = x ∨ m₁ * x * m₁⁻¹ = m₂ * x * m₂⁻¹ := by
  constructor
  · intro hxV m₁ hm₁ m₂ hm₂
    rcases hd.conj_V_eq_or hGMS hxV hm₁ with h1 | h1
    · exact Or.inl h1
    rcases hd.conj_V_eq_or hGMS hxV hm₂ with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (h1.trans h2.symm))
  · intro hP
    by_contra hxV
    obtain ⟨m₁, hm₁, m₂, hm₂, h1, h2, h12⟩ := hd.exists_conj_ne_of_not_mem_V hGMS hx hxV
    rcases hP m₁ hm₁ m₂ hm₂ with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h12 h

theorem Hyp.normalizer_B₄_le_normalizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : normalizer (d.B₄ : Set G) ≤ normalizer (d.V : Set G) := by
  intro n hn
  refine mem_normalizer_fintype fun v hv => ?_
  have hx : n * v * n⁻¹ ∈ d.B₄ := (mem_normalizer_iff.1 hn v).1 (hd.V_le_B₄ hv)
  have hconj : ∀ m ∈ d.B₄, n⁻¹ * m * n ∈ d.B₄ := fun m hm => by
    have := (mem_normalizer_iff.1 (inv_mem hn) m).1 hm
    rwa [inv_inv] at this
  have e1 : ∀ m : G, m * (n * v * n⁻¹) * m⁻¹ =
      n * ((n⁻¹ * m * n) * v * (n⁻¹ * m * n)⁻¹) * n⁻¹ := fun m => by group
  rw [SetLike.mem_coe, hd.mem_V_iff hGMS hx]
  intro m₁ hm₁ m₂ hm₂
  rw [e1, e1]
  rcases (hd.mem_V_iff hGMS (hd.V_le_B₄ hv)).1 hv _ (hconj m₁ hm₁) _ (hconj m₂ hm₂) with
    h1 | h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (Or.inl (by rw [h1]))
  · exact Or.inr (Or.inr (by rw [h1]))

theorem Hyp.mem_VA_of_comm (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.B₄) (hxV : ∀ v ∈ d.V, x * v = v * x) : x ∈ d.V ⊔ d.A₂ := by
  obtain ⟨w, hw, a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₄ hx
  · exact mul_mem (mem_sup_left hw) (mem_sup_right ha)
  · exfalso
    obtain ⟨u, hu, hut⟩ := hd.exists_V_not_comm_t
    have hwa := hd.comm_V_of_mem_VA hGMS (mul_mem (mem_sup_left hw) (mem_sup_right ha)) hu
    have h3 := hxV u hu
    apply hut
    have e : d.t * u * (w * a) = u * d.t * (w * a) := by
      calc d.t * u * (w * a) = d.t * ((w * a) * u) := by rw [hwa]; group
        _ = d.t * (w * a) * u := by group
        _ = u * (d.t * (w * a)) := h3
        _ = u * d.t * (w * a) := by group
    exact mul_right_cancel e

theorem Hyp.normalizer_B₄_le_normalizer_VA (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    normalizer (d.B₄ : Set G) ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_fintype fun w hw => ?_
  refine hd.mem_VA_of_comm hGMS ((mem_normalizer_iff.1 hn w).1 (hd.VA_le_B₄ hw)) fun v hv => ?_
  have hv' : n⁻¹ * v * n ∈ d.V := by
    have := (mem_normalizer_iff.1 (hd.normalizer_B₄_le_normalizer_V hGMS (inv_mem hn)) v).1 hv
    rwa [inv_inv] at this
  have hc := hd.comm_V_of_mem_VA hGMS hw hv'
  calc n * w * n⁻¹ * v = n * (w * (n⁻¹ * v * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * v * n) * w) * n⁻¹ := by rw [hc]
    _ = v * (n * w * n⁻¹) := by group

omit [Finite G] in
theorem mem_normalizer_centerIn {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer (CFSG.centerIn X : Set G) :=
  Common.mem_normalizer_inf hg (Prelim.normalizer_le_normalizer_centralizer X hg)

theorem Hyp.centerIn_B₂ (hd : d.Hyp) : CFSG.centerIn d.B₂ = d.ZtP := by
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  have hta : ∀ {a : G}, a ∈ d.A₂ → d.t * a = a * d.t := fun ha => hd.t_comm_A₂ ha
  apply le_antisymm
  · rintro x ⟨hxB, hxc⟩
    obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hxB <;> subst x
    · have haZ : a ∈ d.Zp := by
        rw [← hZA]
        exact ⟨ha, mem_centralizer_iff.2 fun y hy =>
          mem_centralizer_iff.1 hxc y (mem_sup_right hy)⟩
      rw [hd.ZtP_eq]
      exact mem_sup_right haZ
    · have haZ : a ∈ d.Zp := by
        rw [← hZA]
        refine ⟨ha, mem_centralizer_iff.2 fun y hy => ?_⟩
        have e := mem_centralizer_iff.1 hxc y (mem_sup_right hy)
        have e1 : d.t * (y * a) = d.t * (a * y) := by
          calc d.t * (y * a) = (d.t * y) * a := by group
            _ = (y * d.t) * a := by rw [hta hy]
            _ = y * (d.t * a) := by group
            _ = (d.t * a) * y := e
            _ = d.t * (a * y) := by group
        exact mul_left_cancel e1
      rw [hd.ZtP_eq]
      exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right haZ)
  · intro z hz
    refine ⟨hd.B₂_spec.1 hz, mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [hd.ZtP_eq] at hz
    have hty : y * d.t = d.t * y := by
      obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hy <;> subst y
      · exact (hta ha).symm
      · rw [mul_assoc, ← hta ha]
    have hZc : ∀ z' ∈ d.Zp, y * z' = z' * y := fun z' hz' => by
      rw [← hZA] at hz'
      have htz : d.t * z' = z' * d.t := hta hz'.1
      obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hy <;> subst y
      · exact mem_centralizer_iff.1 hz'.2 a ha
      · calc d.t * a * z' = d.t * (a * z') := by group
          _ = d.t * (z' * a) := by rw [mem_centralizer_iff.1 hz'.2 a ha]
          _ = (d.t * z') * a := by group
          _ = (z' * d.t) * a := by rw [htz]
          _ = z' * (d.t * a) := by group
    obtain ⟨z', hz', e | e⟩ := hd.exists_of_mem_zpowers_sup d.Zp_le_L hz <;> subst z
    · exact hZc z' hz'
    · calc y * (d.t * z') = (y * d.t) * z' := by group
        _ = (d.t * y) * z' := by rw [hty]
        _ = d.t * (y * z') := by group
        _ = d.t * (z' * y) := by rw [hZc z' hz']
        _ = d.t * z' * y := by group

theorem Hyp.normalizer_B₄_inf_C (hd : d.Hyp) :
    normalizer (d.B₄ : Set G) ⊓ centralizer ({d.t} : Set G) =
      normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) := by
  obtain ⟨-, -, hB₂, -, -⟩ := hd.two_core_B₄
  apply le_antisymm
  · intro c hc
    refine ⟨?_, hc.2⟩
    rw [← hB₂]
    exact Common.mem_normalizer_inf hc.1 (le_normalizer hc.2)
  · intro c hc
    refine ⟨d.le_normalizer_B₄ ?_, hc.2⟩
    rw [← hd.centerIn_B₂]
    exact mem_normalizer_centerIn hc.1

@[expose] def C₀ (d : Data G h) : Subgroup G :=
  centralizerMod (normalizer (d.B₄ : Set G) ⊓ normalizer (d.V : Set G) ⊓
      normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G)) (d.V ⊔ d.A₂) d.V
    (fun _ hg y hy => (mem_normalizer_iff.1 hg.2 y).1 hy)
    (fun _ hg b hb => (mem_normalizer_iff.1 hg.1.2 b).1 hb)

theorem Hyp.mem_C₀_iff (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {g : G} :
    g ∈ d.C₀ ↔ g ∈ normalizer (d.B₄ : Set G) ∧ ∀ y ∈ d.V ⊔ d.A₂, g * y * g⁻¹ * y⁻¹ ∈ d.V := by
  constructor
  · rintro ⟨hg, hgy⟩
    exact ⟨hg.1.1, hgy⟩
  · rintro ⟨hg, hgy⟩
    exact ⟨⟨⟨hg, hd.normalizer_B₄_le_normalizer_V hGMS hg⟩,
      hd.normalizer_B₄_le_normalizer_VA hGMS hg⟩, hgy⟩

omit [Finite G] in
theorem C₀_le_normalizer_B₄ (d : Data G h) : d.C₀ ≤ normalizer (d.B₄ : Set G) :=
  fun _ hg => hg.1.1.1

omit [Finite G] in
theorem commutator_mem_V_of_mem_C₀ (d : Data G h) {g y : G} (hg : g ∈ d.C₀)
    (hy : y ∈ d.V ⊔ d.A₂) : g * y * g⁻¹ * y⁻¹ ∈ d.V :=
  hg.2 y hy

theorem Hyp.normalizer_B₄_le_normalizer_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : normalizer (d.B₄ : Set G) ≤ normalizer (d.C₀ : Set G) := fun _ hn =>
  mem_normalizer_of_conj_le fun _ hg => conj_mem_centralizerMod
    ⟨⟨hn, hd.normalizer_B₄_le_normalizer_V hGMS hn⟩, hd.normalizer_B₄_le_normalizer_VA hGMS hn⟩ hg

theorem Hyp.B₄_le_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.B₄ ≤ d.C₀ := by
  have hVA : d.V ⊔ d.A₂ ≤ d.C₀ := fun x hx => (hd.mem_C₀_iff hGMS).2
    ⟨le_normalizer (hd.VA_le_B₄ hx), fun y hy => (hd.elemAbMod_V_sup_A₂ hGMS).2 x hx y hy⟩
  have ht : d.t ∈ d.C₀ := by
    refine (hd.mem_C₀_iff hGMS).2 ⟨le_normalizer hd.t_mem_B₄, fun y hy => ?_⟩
    obtain ⟨v, hv, a, ha, rfl⟩ := hd.exists_mul_of_mem_VA hy
    have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
    have e : d.t * (v * a) * d.t⁻¹ * (v * a)⁻¹ = (d.t * v * d.t) * v⁻¹ := by
      rw [htinv]
      calc d.t * (v * a) * d.t * (v * a)⁻¹ = d.t * v * (a * d.t) * a⁻¹ * v⁻¹ := by group
        _ = d.t * v * (d.t * a) * a⁻¹ * v⁻¹ := by rw [← hd.t_comm_A₂ ha]
        _ = (d.t * v * d.t) * v⁻¹ := by group
    rw [e]
    exact mul_mem (hd.t_conj_mem_V hv) (inv_mem hv)
  intro x hx
  obtain ⟨v, hv, a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₄ hx
  · exact hVA (mul_mem (mem_sup_left hv) (mem_sup_right ha))
  · exact mul_mem ht (hVA (mul_mem (mem_sup_left hv) (mem_sup_right ha)))

theorem Hyp.cr_mem_VA (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.B₄ : Set G)) : g⁻¹ * d.t * g * d.t ∈ d.V ⊔ d.A₂ := by
  have h1 : g⁻¹ * d.t * g ∈ d.B₄ := by
    have := (mem_normalizer_iff.1 (inv_mem hg) d.t).1 hd.t_mem_B₄
    rwa [inv_inv] at this
  obtain ⟨v, hv, a, ha, e | e⟩ := hd.exists_of_mem_B₄ h1
  · exfalso
    apply hd.t_not_mem_VA hGMS
    have h2 : g * (g⁻¹ * d.t * g) * g⁻¹ ∈ d.V ⊔ d.A₂ := (mem_normalizer_iff.1
      (hd.normalizer_B₄_le_normalizer_VA hGMS hg) _).1 (e ▸ mul_mem (mem_sup_left hv)
        (mem_sup_right ha))
    rwa [show g * (g⁻¹ * d.t * g) * g⁻¹ = d.t by group] at h2
  · have e2 : d.t * (v * a) * d.t = (d.t * v * d.t) * a := by
      calc d.t * (v * a) * d.t = d.t * v * (a * d.t) := by group
        _ = d.t * v * (d.t * a) := by rw [← hd.t_comm_A₂ ha]
        _ = (d.t * v * d.t) * a := by group
    rw [e, e2]
    exact mul_mem (mem_sup_left (hd.t_conj_mem_V hv)) (mem_sup_right ha)

theorem Hyp.cr_mul_mod (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x y : G}
    (hx : x ∈ d.C₀) (hy : y ∈ d.C₀) :
    ∃ v ∈ d.V, (x * y)⁻¹ * d.t * (x * y) * d.t =
      v * ((x⁻¹ * d.t * x * d.t) * (y⁻¹ * d.t * y * d.t)) := by
  have hcx := hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ hx)
  have hv := d.commutator_mem_V_of_mem_C₀ (inv_mem hy) hcx
  refine ⟨y⁻¹ * (x⁻¹ * d.t * x * d.t) * y⁻¹⁻¹ * (x⁻¹ * d.t * x * d.t)⁻¹, hv, ?_⟩
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  calc (x * y)⁻¹ * d.t * (x * y) * d.t =
      y⁻¹ * (x⁻¹ * d.t * x * d.t) * (d.t⁻¹ * y * d.t) := by group
    _ = y⁻¹ * (x⁻¹ * d.t * x * d.t) * y⁻¹⁻¹ * (y⁻¹ * d.t * y * d.t) := by rw [htinv]; group
    _ = _ := by group

theorem Hyp.exists_mul_of_cr_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {k : G} (hk : k ∈ normalizer (d.B₄ : Set G)) (hkV : k⁻¹ * d.t * k * d.t ∈ d.V) :
    ∃ c ∈ normalizer (d.B₄ : Set G) ⊓ centralizer ({d.t} : Set G), ∃ w ∈ d.V, k = c * w := by
  set x := k⁻¹ * d.t * k * d.t with hx
  have e0 : x * d.t = k⁻¹ * d.t * k := by
    rw [hx, mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
  have hyy : (x * d.t) * (x * d.t) = 1 := by
    rw [e0]
    calc k⁻¹ * d.t * k * (k⁻¹ * d.t * k) = k⁻¹ * (d.t * d.t) * k := by group
      _ = 1 := by rw [hd.t_mul_t]; group
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hd.mul_self_eq_one_of_mem_V hGMS hkV)
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  have hxt : d.t * x = x * d.t := by
    have := inv_eq_of_mul_eq_one_right hyy
    rwa [mul_inv_rev, htinv, hxinv] at this
  have hxZ : x ∈ d.Zp := by
    rw [← hd.V_inf_centralizer_t]
    exact ⟨hkV, mem_centralizer_singleton_iff.2 hxt.symm⟩
  obtain ⟨w, hw, hwx⟩ := hd.exists_V_cr_eq hxZ
  have e1 : w⁻¹ * d.t * w = k⁻¹ * d.t * k := by
    rw [← e0, ← hwx, mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
  have hwN : w⁻¹ ∈ normalizer (d.B₄ : Set G) := inv_mem (le_normalizer (hd.V_le_B₄ hw))
  have hkw : k * w⁻¹ ∈ normalizer (d.B₄ : Set G) := mul_mem hk hwN
  exact ⟨k * w⁻¹, Subgroup.mem_inf.2 ⟨hkw, mul_inv_mem_centralizer_of_conj_eq e1⟩, w, hw,
    by group⟩

theorem Hyp.C₀_inf_C_le_B₂ (hd : d.Hyp) :
    d.C₀ ⊓ centralizer ({d.t} : Set G) ≤ d.B₂ := by
  rintro c ⟨hc0, hct⟩
  have hcN : c ∈ normalizer (d.B₄ : Set G) := d.C₀_le_normalizer_B₄ hc0
  have hcZ : c ∈ normalizer (d.ZtP : Set G) := by
    have := (hd.normalizer_B₄_inf_C.le ⟨hcN, hct⟩).1
    rw [← hd.centerIn_B₂]
    exact mem_normalizer_centerIn this
  have hcL := hd.centralizer_le_normalizer hct
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  obtain ⟨hcol, hrow⟩ := hd.lift_flag hcZ hcL hy
  have hA : ∀ a ∈ A₂sub h, ∃ z ∈ ZPsub h, actΓ h y a = z * a := by
    intro g hg
    have hga : d.η g ∈ d.A₂ := ⟨g, hg, rfl⟩
    have h1 : c * d.η g * c⁻¹ * (d.η g)⁻¹ ∈ d.Zp := by
      rw [← hd.V_inf_A₂]
      have hA2 : c * d.η g * c⁻¹ * (d.η g)⁻¹ ∈ d.A₂ :=
        mul_mem (hd.conj_mem_A₂ hcZ hct hga) (inv_mem hga)
      exact Subgroup.mem_inf.2 ⟨d.commutator_mem_V_of_mem_C₀ hc0 (mem_sup_right hga), hA2⟩
    rw [d.conj_η_eq hcL hy] at h1
    obtain ⟨z, hz, hze⟩ := h1
    refine ⟨z, hz, ?_⟩
    have hyA := act_mem_A₂sub hcol hrow hg
    have hzU : z ∈ hypUnitriangular h 2 1 :=
      A₂sub_le_U (Z₂Psub_le_A₂sub (ZPsub_le_Z₂Psub hz))
    refine d.η_injOn (A₂sub_le_U hyA) (mul_mem hzU (A₂sub_le_U hg)) ?_
    rw [map_mul, hze]
    group
  obtain ⟨u, hu, hPhi⟩ := exists_eq_innM_of_fixes_A₂ hcol hrow hA
  have hact : d.act ⟨c, hcL⟩ = d.act ⟨d.η u, le_normalizer (d.η_mem u)⟩ := by
    rw [← hy, hPhi, d.act_η]
  have hηN : d.η u ∈ normalizer (d.L : Set G) := le_normalizer (d.η_mem u)
  have hmem : (d.η u)⁻¹ * c ∈ normalizer (d.L : Set G) := mul_mem (inv_mem hηN) hcL
  have huc : (d.η u)⁻¹ * c ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨(d.η u)⁻¹ * c, hmem⟩).1 ?_
    have e : (⟨(d.η u)⁻¹ * c, hmem⟩ : normalizer (d.L : Set G)) =
        (⟨d.η u, hηN⟩ : normalizer (d.L : Set G))⁻¹ * ⟨c, hcL⟩ := rfl
    rw [e, map_mul, map_inv, hact, inv_mul_cancel]
  have hut : (d.η u)⁻¹ * c ∈ zpowers d.t := by
    rw [← hd.sec3_1'.1]
    have hηC : (d.η u)⁻¹ * c ∈ centralizer ({d.t} : Set G) :=
      mul_mem (inv_mem (hd.L_le_centralizer (d.η_mem u))) hct
    exact Subgroup.mem_inf.2 ⟨huc, hηC⟩
  rw [show c = d.η u * ((d.η u)⁻¹ * c) by group]
  exact mul_mem (mem_sup_right ⟨u, hu, rfl⟩) (mem_sup_left hut)

theorem Hyp.mem_B₄_of_mem_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {g : G}
    (hg : g ∈ d.C₀) (hgV : g⁻¹ * d.t * g * d.t ∈ d.V) : g ∈ d.B₄ := by
  obtain ⟨c, hc, w, hw, rfl⟩ := hd.exists_mul_of_cr_mem_V hGMS (d.C₀_le_normalizer_B₄ hg) hgV
  have hwC : w ∈ d.C₀ := hd.B₄_le_C₀ hGMS (hd.V_le_B₄ hw)
  have hcC : c ∈ d.C₀ := by
    have := mul_mem hg (inv_mem hwC)
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (hd.B₂_le_B₄ (hd.C₀_inf_C_le_B₂ ⟨hcC, hc.2⟩)) (hd.V_le_B₄ hw)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
