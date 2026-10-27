module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3F

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem mat_inv_e₁e₂ {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1) :
    mat g⁻¹ ιe₁ ιe₂ = mat g ιe₁ ιe₂ := by
  have := h.charP
  have e := mul_e₁e₂ hg (inv_mem hg)
  rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at e
  linear_combination -e - CharTwo.add_self_eq_zero (mat g ιe₁ ιe₂)

theorem exists_I₄sub_generic (hf : 2 ≤ f) :
    ∃ τ ∈ I₄sub h, (∀ u ∈ hypUnitriangular h 2 1, τ * u * τ⁻¹ * u⁻¹ ∈ Vsub h → u ∈ Vsub h) ∧
      ∀ g ∈ patSub h sI₁ isPattern_sI₁, ∃ g' ∈ patSub h sI₁ isPattern_sI₁,
        g = τ * g' * τ⁻¹ * g'⁻¹ := by
  have := h.charP
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq := four_le_q hf
  obtain ⟨t, ht, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 1 (-((2 ^ f : ℕ) : ℤ))
  have e3' : mat t ιz ιz = ((ω ^ (2 * ((2 ^ f : ℕ) : ℤ) - 2) : Kˣ) : K) :=
    e3.trans (zpow_val_eq hω (-1) (by ring))
  have e5' : mat t ιf₂ ιf₂ = ((ω ^ (1 : ℤ) : Kˣ) : K) := e5.trans (zpow_val_eq hω 1 (by ring))
  have htI : t ∈ I₄sub h := mem_I₄sub.2 ⟨ht, by rw [e1, e5']⟩
  have w12 : mat t ιe₁ ιe₁ ≠ mat t ιe₂ ιe₂ := by
    rw [e1, e2]
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  have w2z : mat t ιe₂ ιe₂ ≠ mat t ιz ιz := by
    rw [e2, e3']
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  have w1z : mat t ιe₁ ιe₁ ≠ mat t ιz ιz := by
    rw [e1, e3']
    refine zpow_val_ne hω 0 ?_ ?_ ?_ <;> generalize ((2 ^ f : ℕ) : ℤ) = q at hq ⊢ <;>
      first | omega | nlinarith
  have hfix : ∀ {a b : HypIndex 2 1} {x : K}, mat t a a ≠ mat t b b →
      mat t a a * x * (mat t b b)⁻¹ = x → x = 0 := by
    intro a b x hab hx
    have hb := torus_ne_zero ht b
    have : x * (mat t a a - mat t b b) = 0 := by
      field_simp at hx
      linear_combination hx
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hab)
  refine ⟨t, htI, fun u hu hc => ?_, fun g hg => ?_⟩
  ·
    have hcU : t * u * t⁻¹ * u⁻¹ ∈ hypUnitriangular h 2 1 :=
      mul_mem (torus_conj_mem_U ht hu) (inv_mem hu)
    obtain ⟨-, c1, -, c3, -, c5, -⟩ := mem_Vsub'.1 hc
    have heq : t * u * t⁻¹ = (t * u * t⁻¹ * u⁻¹) * u := by group
    have a12 : mat u ιe₁ ιe₂ = 0 := by
      refine hfix w12 ?_
      rw [← torus_conj_apply ht, heq, mul_e₁e₂ hcU hu, c1, zero_add]
    have a2z : mat u ιe₂ ιz = 0 := by
      refine hfix w2z ?_
      rw [← torus_conj_apply ht, heq, mul_e₂z hcU hu, c5, zero_add]
    have a1z : mat u ιe₁ ιz = 0 := by
      refine hfix w1z ?_
      rw [← torus_conj_apply ht, heq, mul_e₁z hcU hu, c3, c1, zero_add, zero_mul, add_zero]
    obtain ⟨r1, r2, r3, -⟩ := U_rel hu
    refine mem_Vsub'.2 ⟨hu, a12, by rw [r1, a12, map_zero], a1z, ?_, a2z,
      by rw [r2, a2z, map_zero]⟩
    rw [r3, a1z, a12]
    simp
  ·
    have hb := torus_ne_zero ht ιe₂
    set l := mat t ιe₁ ιe₁ * (mat t ιe₂ ιe₂)⁻¹ with hl
    have hl1 : l + 1 ≠ 0 := by
      intro e
      apply w12
      have : mat t ιe₁ ιe₁ * (mat t ιe₂ ιe₂)⁻¹ = 1 := by
        linear_combination e - CharTwo.add_self_eq_zero (1 : K)
      field_simp at this
      exact this
    obtain ⟨g', hg', hg'a⟩ := exists_rootI₁ h (mat g ιe₁ ιe₂ / (l + 1))
    have hg'U := patSub_le_U _ _ hg'
    have hmem : t * g' * t⁻¹ * g'⁻¹ ∈ patSub h sI₁ isPattern_sI₁ :=
      mul_mem (torus_conj_mem_patSub _ ht hg') (inv_mem hg')
    refine ⟨g', hg', eq_of_mem_patSub_I₁ hg hmem ?_⟩
    rw [mul_e₁e₂ (torus_conj_mem_U ht hg'U) (inv_mem hg'U), torus_conj_apply ht,
      mat_inv_e₁e₂ hg'U, hg'a]
    calc mat g ιe₁ ιe₂ = (l + 1) * (mat g ιe₁ ιe₂ / (l + 1)) := by field_simp
      _ = _ := by rw [hl]; ring

theorem mem_Ssub_of_commutator_Vsub {u : hypSU h 2 1} (hu : u ∈ hypUnitriangular h 2 1)
    (hc : ∀ a ∈ Vsub h, ⁅u, a⁆ ∈ ZPsub h) : u ∈ Ssub h := by
  obtain ⟨a, ha, ha1⟩ := exists_rootI₆ h (c := 1) (by simp)
  obtain ⟨haU, b1, b2, b3, b4, b5, b6, b7, b8, -⟩ := mem_patSub_sI₆.1 ha
  have haV : a ∈ Vsub h := by
    rw [Vsub_eq_patSub]
    exact patSub_mono _ _ (by decide) ha
  have e := (commutator_mem_ZPsub_iff hu haU).1 (hc a haV) ιe₁ ιf₂ (by decide) (by decide)
  rw [mul_e₁f₂ hu haU, mul_e₁f₂ haU hu, b7, b1, b3, ha1, b6] at e
  have h12 : mat u ιe₁ ιe₂ = 0 := by linear_combination e
  refine mem_Ssub'.2 ⟨hu, h12, ?_⟩
  rw [(U_rel hu).1, h12, map_zero]

theorem mem_Vsub_of_commutator_Ssub {u : hypSU h 2 1} (hu : u ∈ Ssub h)
    (hc : ∀ a ∈ Ssub h, ⁅u, a⁆ ∈ ZPsub h) : u ∈ Vsub h := by
  obtain ⟨huU, u12, u21⟩ := mem_Ssub'.1 hu
  obtain ⟨c, hcc⟩ := trace_surj (hK := h) (a := 1 * h.bar 1) (by simp)
  obtain ⟨a, ha, ha1, -⟩ := exists_rootI₂ h hcc
  obtain ⟨haU, a1, a2, a3, a4, a5, a6, a7⟩ := mem_patSub_sI₂.1 ha
  have ea := (commutator_mem_ZPsub_iff huU haU).1 (hc a (patSub_I₂_le_Ssub ha)) ιe₁ ιf₂
    (by decide) (by decide)
  rw [mul_e₁f₂ huU haU, mul_e₁f₂ haU huU, a5, a1, a3, u12, (U_rel haU).2.1, ha1] at ea
  have h1z : mat u ιe₁ ιz = 0 := by
    simp only [map_one, mul_one, zero_mul, add_zero, zero_add] at ea
    linear_combination ea
  obtain ⟨b, hb, hb1, -⟩ := exists_rootI₅ h hcc
  obtain ⟨hbU, b1, b2, b3, b4, b5, b6, b7⟩ := mem_patSub_sI₅.1 hb
  have eb := (commutator_mem_ZPsub_iff huU hbU).1
    (hc b (Ssub_eq_patSub (h := h) ▸ (patSub_I₅_le_A₂sub_inf_Ssub hb).2)) ιe₂ ιf₁
    (by decide) (by decide)
  rw [mul_e₂f₁ huU hbU, mul_e₂f₁ hbU huU, b6, b3, b7, b2, mat_zf₁_of_patSub_I₅ hb, hb1] at eb
  have h2z : mat u ιe₂ ιz = 0 := by
    simp only [map_one, mul_one, zero_mul, add_zero, zero_add, mul_zero] at eb
    linear_combination eb
  obtain ⟨r1, r2, r3, -⟩ := U_rel huU
  refine mem_Vsub'.2 ⟨huU, u12, u21, h1z, ?_, h2z, by rw [r2, h2z, map_zero]⟩
  rw [r3, h1z, u12]
  simp

section Generic

variable {G : Type*} [Group G]

theorem mem_map_upperCentralSeries_two {H : Subgroup G} {x : G} :
    x ∈ (Subgroup.upperCentralSeries H 2).map H.subtype ↔
      x ∈ H ∧ ∀ y ∈ H, ⁅x, y⁆ ∈ CFSG.centerIn H := by
  rw [CFSG.centerIn_eq_map_center]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    have := (Subgroup.mem_upperCentralSeries_succ_iff (G := H) (n := 1)).1 hz ⟨y, hy⟩
    rw [Subgroup.upperCentralSeries_one] at this
    exact ⟨_, this, rfl⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, (Subgroup.mem_upperCentralSeries_succ_iff (G := H) (n := 1)).2
      fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one]
    obtain ⟨w, hw, hwe⟩ := hc y y.2
    have : w = ⁅(⟨x, hx⟩ : H), y⁆ := Subtype.ext (by
      rw [Subgroup.coe_subtype] at hwe
      rw [hwe, commutatorElement_def, commutatorElement_def]
      rfl)
    rw [← this]
    exact hw

@[expose] def commNormSub (V : Subgroup G) (c : G) : Subgroup G where
  carrier := {y | y ∈ normalizer (V : Set G) ∧ ⁅c, y⁆ ∈ V}
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨mul_mem hxN hyN, ?_⟩
    have e : ⁅c, x * y⁆ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hx ((mem_normalizer_iff.1 hxN _).1 hy)
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨inv_mem hxN, ?_⟩
    have e : ⁅c, x⁻¹⁆ = x⁻¹ * ⁅c, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hxN) _).1 (inv_mem hx)

theorem commutator_conj_comm {c i c₁ v z : G} (hic : i * c = c * i) (hiz : i * z = z * i)
    (hX : ⁅c, c₁⁆ = v * z) (hvg : v * (i * c₁ * i⁻¹ * c₁⁻¹) = (i * c₁ * i⁻¹ * c₁⁻¹) * v) :
    ⁅c, i * c₁ * i⁻¹ * c₁⁻¹⁆ = (i * v * i⁻¹) * ⁅z, i * c₁ * i⁻¹ * c₁⁻¹⁆ * v⁻¹ := by
  rw [commutatorElement_def] at hX
  have h1 : c * i * c⁻¹ = i := by rw [← hic]; group
  have h2 : c * c₁ * c⁻¹ = v * z * c₁ := by rw [← hX]; group
  have key : c * (i * c₁ * i⁻¹ * c₁⁻¹) * c⁻¹ =
      (c * i * c⁻¹) * (c * c₁ * c⁻¹) * (c * i * c⁻¹)⁻¹ * (c * c₁ * c⁻¹)⁻¹ := by group
  rw [h1, h2] at key
  have hvg' : v⁻¹ * (i * c₁ * i⁻¹ * c₁⁻¹)⁻¹ = (i * c₁ * i⁻¹ * c₁⁻¹)⁻¹ * v⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hvg]
  calc ⁅c, i * c₁ * i⁻¹ * c₁⁻¹⁆ =
        c * (i * c₁ * i⁻¹ * c₁⁻¹) * c⁻¹ * (i * c₁ * i⁻¹ * c₁⁻¹)⁻¹ := by
          rw [commutatorElement_def]
    _ = i * v * z * c₁ * i⁻¹ * c₁⁻¹ * z⁻¹ * (v⁻¹ * (i * c₁ * i⁻¹ * c₁⁻¹)⁻¹) := by
          rw [key]; group
    _ = i * v * i⁻¹ * (i * z) * (c₁ * i⁻¹ * c₁⁻¹ * z⁻¹ * (i * c₁ * i⁻¹ * c₁⁻¹)⁻¹ * v⁻¹) := by
          rw [hvg']; group
    _ = i * v * i⁻¹ * (z * i) * (c₁ * i⁻¹ * c₁⁻¹ * z⁻¹ * (i * c₁ * i⁻¹ * c₁⁻¹)⁻¹ * v⁻¹) := by
          rw [hiz]
    _ = (i * v * i⁻¹) * ⁅z, i * c₁ * i⁻¹ * c₁⁻¹⁆ * v⁻¹ := by
          rw [commutatorElement_def]; group

end Generic

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem P_inf_centralizer_I₁ (hf : 2 ≤ f) :
    d.P ⊓ centralizer (d.I₁ : Set G) = d.pull (patSub h sI₁ isPattern_sI₁) := by
  rw [Data.I₁, ← d.pull_U_inf_centralizer (X := I₁sub h) (torusEq_le _), U_inf_centralizer_I₁ hf]

theorem I₄_le_I : d.I₄ ≤ d.I := d.pull_mono (torusEq_le _)

theorem exists_I₄_generic (hf : 2 ≤ f) :
    ∃ i ∈ d.I₄, (∀ p ∈ d.P, i * p * i⁻¹ * p⁻¹ ∈ d.A₁ → p ∈ d.A₁) ∧
      ∀ c ∈ d.P ⊓ centralizer (d.I₁ : Set G), ∃ c' ∈ d.P ⊓ centralizer (d.I₁ : Set G),
        c = i * c' * i⁻¹ * c'⁻¹ := by
  obtain ⟨τ, hτ, h1, h2⟩ := exists_I₄sub_generic (h := h) hf
  refine ⟨d.η τ, ⟨τ, hτ, rfl⟩, ?_, fun c hc => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ hc
    have hcU : τ * u * τ⁻¹ * u⁻¹ ∈ hypUnitriangular h 2 1 :=
      mul_mem (torus_conj_mem_U (torusEq_le _ hτ) hu) (inv_mem hu)
    have e : d.η τ * d.η u * (d.η τ)⁻¹ * (d.η u)⁻¹ = d.η (τ * u * τ⁻¹ * u⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e] at hc
    exact ⟨u, h1 u hu ((d.η_mem_pull_iff (Vsub_le_Ssub.trans Ssub_le_Usub) hcU).1 hc), rfl⟩
  · rw [d.P_inf_centralizer_I₁ hf] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨g', hg', rfl⟩ := h2 g hg
    refine ⟨d.η g', (d.P_inf_centralizer_I₁ hf).symm ▸ ⟨g', hg', rfl⟩, ?_⟩
    simp only [map_mul, map_inv]

variable [Finite G]

theorem I_le_normalizer_A₁ : d.I ≤ normalizer (d.A₁ : Set G) := by
  rintro _ ⟨τ, hτ, rfl⟩
  refine mem_normalizer_of_conj_le fun a ha => ?_
  obtain ⟨v, hv, rfl⟩ := ha
  refine ⟨τ * v * τ⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [Vsub_eq_patSub] at hv ⊢
  exact torus_conj_mem_patSub _ hτ hv

@[expose] def W (d : Data G h) : Subgroup G :=
  d.V ⊔ ((d.F ⊔ d.P) ⊓ centralizer (d.I₄ : Set G))

variable {d}

theorem Hyp.I_le_normalizer_B₁ (hd : d.Hyp) :
    d.I ≤ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) := by
  intro i hi
  have hit : i ∈ centralizer ({d.t} : Set G) := (hd.I_le hi).1
  have hiA := d.I_le_normalizer_A₁ hi
  refine ⟨mem_normalizer_of_conj_le fun b hb => ?_, hit⟩
  have hct : i * d.t * i⁻¹ = d.t := by
    rw [mem_centralizer_singleton_iff.1 hit, mul_inv_cancel_right]
  obtain ⟨a, ha, hba | hba⟩ := hd.exists_of_mem_B₁ hb <;> rw [hba]
  · exact mem_sup_right ((mem_normalizer_iff.1 hiA a).1 ha)
  · rw [show i * (d.t * a) * i⁻¹ = (i * d.t * i⁻¹) * (i * a * i⁻¹) by group, hct]
    exact mul_mem (mem_sup_left (mem_zpowers _))
      (mem_sup_right ((mem_normalizer_iff.1 hiA a).1 ha))

end Data

end CFSG.LocalAnalysis.EvenBN.U5
