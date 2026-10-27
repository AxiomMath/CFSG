module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeBlocks
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.LinearPilot (diagUnit coe_diagUnit)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem one_ne_two_three : (1 : Fin 3) ≠ 2 := by decide

variable (K) in
@[expose] def shortParamHom : Kˣ →* (Fin 3 → Kˣ) where
  toFun r := ![1, r, r⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    funext i
    fin_cases i <;> simp [mul_comm]

variable (K) in
@[expose] noncomputable def shortTorusHom : Kˣ →* StatedSp 3 K :=
  (diagSp K 3).comp (shortParamHom K)

variable (K) in
@[expose] noncomputable def shortTorus : Subgroup (StatedSp 3 K) :=
  (shortTorusHom K).range

theorem shortTorusHom_apply (r : Kˣ) : shortTorusHom K r = diagSp K 3 ![1, r, r⁻¹] :=
  rfl

theorem mem_shortTorus {x : StatedSp 3 K} :
    x ∈ shortTorus K ↔ ∃ r : Kˣ, diagSp K 3 ![1, r, r⁻¹] = x :=
  Iff.rfl

theorem diagSp_mem_shortTorus (κ : Kˣ) : diagSp K 3 ![1, κ, κ⁻¹] ∈ shortTorus K :=
  ⟨κ, rfl⟩

theorem shortTorusHom_eq_shortBlock (r : Kˣ) :
    shortTorusHom K r = shortBlock K one_ne_two_three (diagUnit r) := by
  rw [shortBlock_diagUnit, shortTorusHom_apply]
  congr 1
  funext l
  fin_cases l <;> simp [shortParam]

theorem shortTorus_le_range_shortBlock :
    shortTorus K ≤ (shortBlock K one_ne_two_three).range := by
  rintro _ ⟨r, rfl⟩
  exact ⟨diagUnit r, (shortTorusHom_eq_shortBlock r).symm⟩

theorem card_shortTorus [Finite K] : Nat.card (shortTorus K) = Nat.card Kˣ := by
  have hinj : Function.Injective (shortTorusHom K) := by
    intro r s h
    have h1 := congrFun (diagSp_injective h) 1
    simpa [shortParamHom] using h1
  rw [shortTorus, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem not_two_dvd_card_shortTorus [Finite K] [CharP K 2] : ¬ 2 ∣ Nat.card (shortTorus K) := by
  rw [card_shortTorus, Nat.card_congr (rootTorusSpEquiv (K := K) (n := 1) 0).toEquiv]
  exact fun h => (Nat.not_even_iff_odd.2 (odd_card_rootTorusSp 0)) (even_iff_two_dvd.2 h)

theorem shortTorus_le_a2Levi : shortTorus K ≤ a2Levi K 0 :=
  shortTorus_le_range_shortBlock.trans le_sup_left

theorem diagSpEntry_short_ne {κ : Kˣ} (hκ : κ ≠ 1) {a b : Fin 3 ⊕ Fin 3}
    (ha : a ∈ coords (0 : Fin 3)) (hb : b ∉ coords (0 : Fin 3)) :
    diagSpEntry ![1, κ, κ⁻¹] a ≠ diagSpEntry ![1, κ, κ⁻¹] b := by
  have hκ' : (κ : K) ≠ 1 := fun h => hκ (Units.ext h)
  have hκ'' : ((κ⁻¹ : Kˣ) : K) ≠ 1 := fun h => hκ (inv_eq_one.1 (Units.ext h))
  rcases mem_coords.1 ha with rfl | rfl <;> rcases b with i | i <;> fin_cases i <;>
    simp_all [mem_coords, diagSpEntry, eq_comm]

theorem centralizer_shortTorus_le {κ : Kˣ} (hκ : κ ≠ 1) :
    centralizer (shortTorus K : Set (StatedSp 3 K)) ≤
      longRootSp2 K 3 (0 : Fin 3) ⊔ complSp K (0 : Fin 3) := by
  intro x hx
  have hc : Commute x (diagSp K 3 ![1, κ, κ⁻¹]) :=
    ((mem_centralizer_iff.1 hx) _ (diagSp_mem_shortTorus κ)).symm
  have hz := (commute_diagSp_iff x _).1 hc
  exact mem_longRootSp2_sup_complSp_of_block fun a b ha hb =>
    ⟨hz a b (diagSpEntry_short_ne hκ ha hb), hz b a (diagSpEntry_short_ne hκ ha hb).symm⟩

@[expose] def shortCentMat (a b c d : K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  Matrix.of fun r s =>
    if r = s then
      (if r = Sum.inl 0 ∨ r = Sum.inr 0 then 1 else if r = Sum.inl 1 ∨ r = Sum.inr 2 then a else c)
    else if r = Sum.inl 1 ∧ s = Sum.inr 2 then b
    else if r = Sum.inl 2 ∧ s = Sum.inr 1 then d else 0

theorem shortCentMat_mul_comm (a b c d a' b' c' d' : K) :
    shortCentMat a b c d * shortCentMat a' b' c' d' =
      shortCentMat a' b' c' d' * shortCentMat a b c d := by
  ext r s
  rcases r with i | i <;> rcases s with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, shortCentMat] <;> ring

variable [CharP K 2]

omit [CharP K 2] in
theorem twoCentralElt_mem_complSp_zero :
    twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 ∈ complSp K (0 : Fin 3) :=
  twoCentralElt_mem_complSp (by decide) (by decide) 0 1

theorem units_ne_inv_of_ne_one {κ : Kˣ} (hκ : κ ≠ 1) : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := by
  intro h
  have h1 : (κ : K) * κ = 1 := by
    calc (κ : K) * κ = (κ : K) * ((κ⁻¹ : Kˣ) : K) := by rw [← h]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((κ : K) - 1) ^ 2 = 0 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h1 + (1 - (κ : K)) * h22
  exact hκ (Units.ext (by simpa [sub_eq_zero] using h2))

@[expose] def shortWt : Fin 3 ⊕ Fin 3 → Fin 3 :=
  Sum.elim ![0, 1, 2] ![0, 2, 1]

theorem diagSpEntry_short_ne_of_shortWt_ne {κ : Kˣ} (hκ : κ ≠ 1) {a b : Fin 3 ⊕ Fin 3}
    (h : shortWt a ≠ shortWt b) : diagSpEntry ![1, κ, κ⁻¹] a ≠ diagSpEntry ![1, κ, κ⁻¹] b := by
  have hκ1 : (κ : K) ≠ 1 := fun h => hκ (Units.ext h)
  have hκinv : (κ : K)⁻¹ ≠ 1 := fun h => hκ1 (by simpa using congrArg Inv.inv h)
  have hκκ : (κ : K) ≠ (κ : K)⁻¹ := by simpa using units_ne_inv_of_ne_one hκ
  have hκκu : κ ≠ κ⁻¹ := fun h => units_ne_inv_of_ne_one hκ (congrArg Units.val h)
  have hκu : κ⁻¹ ≠ 1 := fun h => hκ (inv_eq_one.1 h)
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [shortWt] at h ⊢ <;>
    first
    | exact hκ | exact Ne.symm hκ | exact hκu | exact Ne.symm hκu | exact hκκu
    | exact Ne.symm hκκu | exact hκ1 | exact Ne.symm hκ1 | exact hκinv | exact Ne.symm hκinv
    | exact hκκ | exact Ne.symm hκκ

theorem mat_eq_shortCentMat {κ : Kˣ} (hκ : κ ≠ 1) {u : StatedSp 3 K}
    (hu : u ∈ complSp K (0 : Fin 3)) (hd : Commute u (diagSp K 3 ![1, κ, κ⁻¹]))
    (ha : u * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 =
      twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 * u) :
    mat 3 K u = shortCentMat (mat 3 K u (Sum.inl 1) (Sum.inl 1))
      (mat 3 K u (Sum.inl 1) (Sum.inr 2)) (mat 3 K u (Sum.inl 2) (Sum.inl 2))
      (mat 3 K u (Sum.inl 2) (Sum.inr 1)) := by
  have hz := (commute_diagSp_iff u _).1 hd
  have hG := (commute_twoCentralElt_iff (p := (1 : Fin 3)) (q := 2) (0 : K) 1).1 ha
  have e1 := congrFun (congrFun hG (Sum.inl 1)) (Sum.inr 2)
  have e2 := congrFun (congrFun hG (Sum.inl 2)) (Sum.inr 1)
  have e3 := congrFun (congrFun hG (Sum.inr 2)) (Sum.inr 2)
  have e4 := congrFun (congrFun hG (Sum.inr 1)) (Sum.inr 1)
  rw [mul_zHat_apply, zHat_mul_apply] at e1 e2 e3 e4
  simp at e1 e2 e3 e4
  have hc : ∀ t ∈ coords (0 : Fin 3), ∀ r,
      mat 3 K u r t = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) r t :=
    fun t ht r => hu r t fun h => h.2 ht
  have hzero : ∀ a b, shortWt a ≠ shortWt b → mat 3 K u a b = 0 := fun a b h =>
    hz a b (diagSpEntry_short_ne_of_shortWt_ne hκ h)
  have hm0 : Sum.inl (0 : Fin 3) ∈ coords (0 : Fin 3) := inl_mem_coords 0
  have hm1 : Sum.inr (0 : Fin 3) ∈ coords (0 : Fin 3) := by simp [mem_coords]
  have h00 : mat 3 K u (Sum.inl 0) (Sum.inl 0) = 1 := by simpa using hc _ hm0 (Sum.inl 0)
  have h01 : mat 3 K u (Sum.inl 0) (Sum.inr 0) = 0 := by simpa using hc _ hm1 (Sum.inl 0)
  have h10 : mat 3 K u (Sum.inr 0) (Sum.inl 0) = 0 := by simpa using hc _ hm0 (Sum.inr 0)
  have h11 : mat 3 K u (Sum.inr 0) (Sum.inr 0) = 1 := by simpa using hc _ hm1 (Sum.inr 0)
  ext r s
  rcases r with i | i <;> rcases s with j | j <;> fin_cases i <;> fin_cases j <;>
    simp only [shortCentMat, Matrix.of_apply] <;> simp <;>
    first
    | exact hzero _ _ (by decide)
    | exact h00 | exact h01 | exact h10 | exact h11
    | exact e1 | exact e1.symm | exact e2 | exact e2.symm | exact e3 | exact e4

theorem commute_of_mem_shortCent {κ : Kˣ} (hκ : κ ≠ 1) {u v : StatedSp 3 K}
    (hu : u ∈ complSp K (0 : Fin 3)) (hud : Commute u (diagSp K 3 ![1, κ, κ⁻¹]))
    (hua : u * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 =
      twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 * u)
    (hv : v ∈ complSp K (0 : Fin 3)) (hvd : Commute v (diagSp K 3 ![1, κ, κ⁻¹]))
    (hva : v * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 =
      twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 * v) :
    Commute u v := by
  apply mat_injective
  rw [map_mul, map_mul, mat_eq_shortCentMat hκ hu hud hua, mat_eq_shortCentMat hκ hv hvd hva,
    shortCentMat_mul_comm]

omit [CharP K 2] in
theorem diagSp_short_mem_complSp (κ : Kˣ) : diagSp K 3 ![1, κ, κ⁻¹] ∈ complSp K (0 : Fin 3) := by
  rw [mem_complSp]
  intro r t h
  rw [mat_diagSp]
  rcases r with i | i <;> rcases t with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords] at h ⊢

omit [CharP K 2] in
theorem exists_eq_mul_of_mem_centralizer_shortTorus {κ : Kˣ} (hκ : κ ≠ 1) {x : StatedSp 3 K}
    (hxa : x ∈ centralizer ({twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1} : Set (StatedSp 3 K)))
    (hxT : x ∈ centralizer (shortTorus K : Set (StatedSp 3 K))) :
    ∃ u ∈ complSp K (0 : Fin 3), ∃ a ∈ longRootSp2 K 3 (0 : Fin 3),
      Commute u (diagSp K 3 ![1, κ, κ⁻¹]) ∧
      u * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 = twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 * u ∧
      x = u * a := by
  obtain ⟨a, ha, u, hu, rfl⟩ := F4Pilot.exists_mul_eq_of_mem_sup_of_commute
    (fun a ha u hu => commute_of_mem_longRootSp2_of_mem_complSp ha hu)
    (centralizer_shortTorus_le hκ hxT)
  have hau : Commute a u := commute_of_mem_longRootSp2_of_mem_complSp ha hu
  have hd : Commute (a * u) (diagSp K 3 ![1, κ, κ⁻¹]) :=
    ((mem_centralizer_iff.1 hxT) _ (diagSp_mem_shortTorus κ)).symm
  have hda : Commute a (diagSp K 3 ![1, κ, κ⁻¹]) :=
    commute_of_mem_longRootSp2_of_mem_complSp ha (diagSp_short_mem_complSp κ)
  have hz : Commute (a * u) (twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1) :=
    mem_centralizer_singleton_iff.1 hxa
  have hza : Commute a (twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1) :=
    commute_of_mem_longRootSp2_of_mem_complSp ha twoCentralElt_mem_complSp_zero
  have hu' : u = a⁻¹ * (a * u) := by group
  refine ⟨u, hu, a, ha, ?_, ?_, hau.eq⟩
  · rw [hu']
    exact hda.inv_left.mul_left hd
  · have h := hza.inv_left.mul_left hz
    rw [← hu'] at h
    exact h.eq

theorem le_longRootSp2_of_perfect_of_le_centralizer_shortTorus {κ : Kˣ} (hκ : κ ≠ 1)
    {P : Subgroup (StatedSp 3 K)} (hP : ⁅P, P⁆ = P)
    (hPa : P ≤ centralizer ({twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1} : Set (StatedSp 3 K)))
    (hPT : P ≤ centralizer (shortTorus K : Set (StatedSp 3 K))) :
    P ≤ longRootSp2 K 3 (0 : Fin 3) := by
  rw [← hP, Subgroup.commutator_le]
  intro p₁ hp₁ p₂ hp₂
  obtain ⟨u₁, hu₁, a₁, ha₁, hd₁, hz₁, rfl⟩ :=
    exists_eq_mul_of_mem_centralizer_shortTorus hκ (hPa hp₁) (hPT hp₁)
  obtain ⟨u₂, hu₂, a₂, ha₂, hd₂, hz₂, rfl⟩ :=
    exists_eq_mul_of_mem_centralizer_shortTorus hκ (hPa hp₂) (hPT hp₂)
  have c : ∀ {u a : StatedSp 3 K}, u ∈ complSp K (0 : Fin 3) → a ∈ longRootSp2 K 3 (0 : Fin 3) →
      Commute u a := fun hu ha => (commute_of_mem_longRootSp2_of_mem_complSp ha hu).symm
  rw [commutatorElement_mul_mul_of_commute (c hu₁ ha₁) (c hu₁ ha₂)
    (commute_of_mem_shortCent hκ hu₁ hd₁ hz₁ hu₂ hd₂ hz₂) (c hu₂ ha₁) (c hu₂ ha₂),
    commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)

end CFSG.SeitzReduction.SymplecticPilot
