module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools

public section

namespace CFSG.ComponentClassification.Sol76.RankOneClass

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreIn_le_coreActionKernel_self (X : Subgroup G) :
    oddCoreIn X ≤ coreActionKernel X := by
  rintro _ ⟨o, ho, rfl⟩
  refine mem_coreActionKernel.mpr ⟨le_normalizer o.2, fun v hv => ?_⟩
  have h1 : (⟨v, hv⟩ : X)⁻¹ * o⁻¹ * ⟨v, hv⟩ * o ∈ pPrimeCore 2 ↥X :=
    mul_mem (by
      have := (pPrimeCore_normal (p := 2) (G := X)).conj_mem _ (inv_mem ho) (⟨v, hv⟩ : X)⁻¹
      simpa using this) ho
  exact ⟨_, h1, by simp⟩

theorem twoLayerIn_le_sup_coreActionKernel {H X : Subgroup G} (hX : IsTwoComponentIn X H) :
    twoLayerIn H ≤ X ⊔ coreActionKernel X :=
  Sol76T13.twoLayerIn_le_of_forall fun Y hY => by
    by_cases hYX : Y = X
    · rw [hYX]
      exact le_sup_left
    · exact (GSThmB.B5a.le_coreActionKernel_of_ne hX.1 hY.1 hX.2 hY.2 (Ne.symm hYX)).trans
        le_sup_right

omit [Finite G] in
theorem mem_oddCoreIn_of_mem_coreActionKernel {X : Subgroup G}
    (hZ : center (↥X ⧸ pPrimeCore 2 ↥X) = ⊥) {x : G} (hxX : x ∈ X)
    (hxC : x ∈ coreActionKernel X) : x ∈ oddCoreIn X := by
  have hc : (QuotientGroup.mk ⟨x, hxX⟩ : ↥X ⧸ pPrimeCore 2 ↥X) ∈
      center (↥X ⧸ pPrimeCore 2 ↥X) := by
    rw [FooteLit.mk_mem_center_iff]
    intro y
    have h1 := (mem_coreActionKernel.mp hxC).2 y y.2
    rw [mem_pPrimeCore_iff_mem_oddCoreIn]
    have e : (((y * ⟨x, hxX⟩)⁻¹ * (⟨x, hxX⟩ * y) : ↥X) : G) =
        ((y : G)⁻¹ * x⁻¹ * (y : G) * x)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact inv_mem h1
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hc
  exact (mem_pPrimeCore_iff_mem_oddCoreIn _).mp hc

omit [Finite G] in
theorem le_normalizer_biSup {𝒮 : Set (Subgroup G)} {N : Subgroup G}
    (h : ∀ X ∈ 𝒮, N ≤ normalizer (X : Set G)) :
    N ≤ normalizer ((⨆ X ∈ 𝒮, X : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  refine iSup_congr fun X => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hX => mem_normalizer_iff_map_conj_eq.mp (h X hX hg)

theorem twoLayerIn_le_normalizer_oddCoreIn {H X : Subgroup G} (hX : IsTwoComponentIn X H) :
    twoLayerIn H ≤ normalizer (oddCoreIn X : Set G) := fun _ hg =>
  mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (twoLayerIn_le_normalizer hX.1 hX.2 hg))

theorem mem_biSup_oddCoreIn_of_mem_biSup {H : Subgroup G} {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ X ∈ 𝒮, IsTwoComponentIn X H)
    (hZ : ∀ X ∈ 𝒮, center (↥X ⧸ pPrimeCore 2 ↥X) = ⊥) {p : G}
    (hp : p ∈ (⨆ X ∈ 𝒮, X : Subgroup G)) (hpC : ∀ X ∈ 𝒮, p ∈ coreActionKernel X) :
    p ∈ (⨆ X ∈ 𝒮, oddCoreIn X : Subgroup G) := by
  have key : ∀ 𝒯 : Set (Subgroup G), 𝒯.Finite → 𝒯 ⊆ 𝒮 → ∀ p : G,
      p ∈ (⨆ X ∈ 𝒯, X : Subgroup G) → (∀ X ∈ 𝒯, p ∈ coreActionKernel X) →
        p ∈ (⨆ X ∈ 𝒯, oddCoreIn X : Subgroup G) := by
    intro 𝒯 h𝒯
    induction 𝒯, h𝒯 using Set.Finite.induction_on with
    | empty =>
      intro _ p hp _
      simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, mem_bot] at hp
      rw [hp]
      exact one_mem _
    | @insert Y 𝒯 hY𝒯 _ ih =>
      intro hsub p hp hpC
      have hY := h𝒮 Y (hsub (Set.mem_insert Y 𝒯))
      have hsub' : 𝒯 ⊆ 𝒮 := fun X hX => hsub (Set.mem_insert_of_mem Y hX)
      rw [iSup_insert] at hp ⊢
      have hYN : Y ≤ normalizer ((⨆ X ∈ 𝒯, X : Subgroup G) : Set G) :=
        le_normalizer_biSup fun X hX => (le_twoLayerIn_of_isTwoComponentIn hY).trans
          (twoLayerIn_le_normalizer (h𝒮 X (hsub' hX)).1 (h𝒮 X (hsub' hX)).2)
      obtain ⟨q, hq, y, hy, rfl⟩ :=
        Sol76.exists_mul_of_mem_sup_normalizer hYN (by rwa [sup_comm] at hp)
      have hne : ∀ X ∈ 𝒯, X ≠ Y := fun X hX h => hY𝒯 (h ▸ hX)
      have hyC : ∀ X ∈ 𝒯, y ∈ coreActionKernel X := fun X hX =>
        GSThmB.B5a.le_coreActionKernel_of_ne (h𝒮 X (hsub' hX)).1 hY.1 (h𝒮 X (hsub' hX)).2 hY.2
          (hne X hX) hy
      have hqC : ∀ X ∈ 𝒯, q ∈ coreActionKernel X := fun X hX => by
        have h1 := mul_mem (hpC X (Set.mem_insert_of_mem Y hX)) (inv_mem (hyC X hX))
        rwa [mul_inv_cancel_right] at h1
      have hq' := ih hsub' q hq hqC
      have hQY : (⨆ X ∈ 𝒯, oddCoreIn X : Subgroup G) ≤ coreActionKernel Y :=
        iSup₂_le fun X hX => (map_subtype_le _ : oddCoreIn X ≤ X).trans
          (GSThmB.B5a.le_coreActionKernel_of_ne hY.1 (h𝒮 X (hsub' hX)).1 hY.2
            (h𝒮 X (hsub' hX)).2 (Ne.symm (hne X hX)))
      have hyCY : y ∈ coreActionKernel Y := by
        have h1 := mul_mem (inv_mem (hQY hq')) (hpC Y (Set.mem_insert Y 𝒯))
        rwa [inv_mul_cancel_left] at h1
      have hyO := mem_oddCoreIn_of_mem_coreActionKernel (hZ Y (hsub (Set.mem_insert Y 𝒯))) hy hyCY
      exact mul_mem (mem_sup_right hq') (mem_sup_left hyO)
  exact key 𝒮 (Set.toFinite 𝒮) le_rfl p hp hpC

theorem le_sup_of_le_twoLayerIn {H J : Subgroup G} (hJL : J ≤ twoLayerIn H)
    (hJperf : ⁅J, J⁆ = J) :
    J ≤ (⨆ X ∈ {X | IsTwoComponentIn X H ∧ ¬ J ≤ coreActionKernel X}, X : Subgroup G) ⊔
      (⨆ X ∈ {X | IsTwoComponentIn X H}, oddCoreIn X : Subgroup G) := by
  set Smv := {X | IsTwoComponentIn X H ∧ ¬ J ≤ coreActionKernel X} with hSmv
  set Sun := {X | IsTwoComponentIn X H ∧ J ≤ coreActionKernel X} with hSun
  set P : Subgroup G := ⨆ X ∈ Smv, X with hP
  set U : Subgroup G := ⨆ X ∈ Sun, X with hU
  set N₀ : Subgroup G := ⨆ X ∈ {X | IsTwoComponentIn X H}, oddCoreIn X with hN₀
  set E := twoLayerIn H with hE
  have hEP : E ≤ normalizer (P : Set G) :=
    le_normalizer_biSup fun X hX => twoLayerIn_le_normalizer hX.1.1 hX.1.2
  have hEN : E ≤ normalizer (N₀ : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
    refine iSup_congr fun X => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hX => mem_normalizer_iff_map_conj_eq.mp
      (twoLayerIn_le_normalizer_oddCoreIn hX hg)
  have hUE : U ≤ E := iSup₂_le fun X hX => le_twoLayerIn_of_isTwoComponentIn hX.1
  have hEPU : E ≤ P ⊔ U := Sol76T13.twoLayerIn_le_of_forall fun X hX => by
    by_cases hJX : J ≤ coreActionKernel X
    · exact (le_biSup (fun X => X) (show X ∈ Sun from ⟨hX, hJX⟩)).trans le_sup_right
    · exact (le_biSup (fun X => X) (show X ∈ Smv from ⟨hX, hJX⟩)).trans le_sup_left
  have hconjN : ∀ u ∈ E, ∀ n ∈ N₀, u * n * u⁻¹ ∈ N₀ := fun u hu n hn =>
    (mem_normalizer_iff.mp (hEN hu) n).mp hn
  let D : Subgroup G :=
    { carrier := {u | u ∈ E ∧ ∀ j ∈ J, u * j * u⁻¹ * j⁻¹ ∈ N₀}
      mul_mem' := by
        rintro u₁ u₂ ⟨hu₁, h₁⟩ ⟨hu₂, h₂⟩
        refine ⟨mul_mem hu₁ hu₂, fun j hj => ?_⟩
        have e : u₁ * u₂ * j * (u₁ * u₂)⁻¹ * j⁻¹ =
            u₁ * (u₂ * j * u₂⁻¹ * j⁻¹) * u₁⁻¹ * (u₁ * j * u₁⁻¹ * j⁻¹) := by group
        rw [e]
        exact mul_mem (hconjN u₁ hu₁ _ (h₂ j hj)) (h₁ j hj)
      one_mem' := ⟨one_mem _, fun j _ => by simp⟩
      inv_mem' := by
        rintro u ⟨hu, h⟩
        refine ⟨inv_mem hu, fun j hj => ?_⟩
        have e : u⁻¹ * j * u⁻¹⁻¹ * j⁻¹ = u⁻¹ * (u * j * u⁻¹ * j⁻¹)⁻¹ * u⁻¹⁻¹ := by group
        rw [e]
        exact hconjN u⁻¹ (inv_mem hu) _ (inv_mem (h j hj)) }
  have hUD : U ≤ D := iSup₂_le fun X hX x hx => by
    refine ⟨le_twoLayerIn_of_isTwoComponentIn hX.1 hx, fun j hj => ?_⟩
    have h1 := (mem_coreActionKernel.mp (inv_mem (hX.2 hj))).2 x⁻¹ (inv_mem hx)
    rw [inv_inv, inv_inv] at h1
    exact (le_biSup (fun X => oddCoreIn X) (show X ∈ {X | IsTwoComponentIn X H} from hX.1)) h1
  rw [← hJperf]
  refine commutator_le.mpr fun j₁ hj₁ j₂ hj₂ => ?_
  obtain ⟨a, ha, u, hu, rfl⟩ :=
    Sol76.exists_mul_of_mem_sup_normalizer (hUE.trans hEP) (hEPU (hJL hj₁))
  have hc : u * j₂ * u⁻¹ * j₂⁻¹ ∈ N₀ := (hUD hu).2 j₂ hj₂
  have ha' : j₂ * a⁻¹ * j₂⁻¹ ∈ P := (mem_normalizer_iff.mp (hEP (hJL hj₂)) a⁻¹).mp (inv_mem ha)
  have e : ⁅a * u, j₂⁆ = a * (u * j₂ * u⁻¹ * j₂⁻¹) * (j₂ * a⁻¹ * j₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right hc)) (mem_sup_left ha')

omit [Finite G] in
theorem conj_mem_coreActionKernel {X : Subgroup G} {x g : G} (hx : x ∈ normalizer (X : Set G))
    (hg : g ∈ coreActionKernel X) : x * g * x⁻¹ ∈ coreActionKernel X := by
  obtain ⟨hgN, hgk⟩ := mem_coreActionKernel.mp hg
  refine mem_coreActionKernel.mpr ⟨mul_mem (mul_mem hx hgN) (inv_mem hx), fun j hj => ?_⟩
  have hj' : x⁻¹ * j * x ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem hx) j).mp hj
    rwa [inv_inv] at this
  have hON : x ∈ normalizer (oddCoreIn X : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hx)
  have h1 := (mem_normalizer_iff.mp hON _).mp (hgk _ hj')
  have e : j⁻¹ * (x * g * x⁻¹)⁻¹ * j * (x * g * x⁻¹) =
      x * ((x⁻¹ * j * x)⁻¹ * g⁻¹ * (x⁻¹ * j * x) * g) * x⁻¹ := by group
  rw [e]
  exact h1

theorem mem_coreActionKernel_of_center_eq_bot {H J X : Subgroup G} {z : G}
    (hX : IsTwoComponentIn X H) (hJL : J ≤ twoLayerIn H) (hJres : oddResidualIn J = J)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hJX : ¬ J ≤ coreActionKernel X)
    (hZ : center (↥X ⧸ pPrimeCore 2 ↥X) = ⊥)
    (hcard : Nat.card (↥X ⧸ Open.fusionZStar ↥X) ≤ Nat.card (↥J ⧸ Open.fusionZStar ↥J))
    (hzJ : z ∈ J) (hzc : ∀ j ∈ J, j * z = z * j) : z ∈ coreActionKernel X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel X with hC
  set W := X ⊔ C with hW
  have hXW : X ≤ W := le_sup_left
  have hCW : C ≤ W := le_sup_right
  have hJW : J ≤ W := hJL.trans (twoLayerIn_le_sup_coreActionKernel hX)
  have hCN : C ≤ normalizer (X : Set G) := fun g hg => (mem_coreActionKernel.mp hg).1
  have hXNC : X ≤ normalizer (C : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => conj_mem_coreActionKernel (le_normalizer hx) hg, fun hg => ?_⟩
    have h1 := conj_mem_coreActionKernel (inv_mem (le_normalizer hx)) hg
    rwa [inv_inv, show x⁻¹ * (x * g * x⁻¹) * x = g by group] at h1
  have hWNC : W ≤ normalizer (C : Set G) := sup_le hXNC le_normalizer
  have : (C.subgroupOf W).Normal := (normal_subgroupOf_iff_le_normalizer hCW).mpr hWNC
  have hcen : center (↥W ⧸ C.subgroupOf W) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, c, hc, hw⟩ := Sol76.exists_mul_of_mem_sup_normalizer hCN w.2
    have hwN : (w : G) ∈ normalizer (X : Set G) := by
      rw [hw]
      exact mul_mem (le_normalizer hx) (hCN hc)
    have hxO : x ∈ oddCoreIn X := by
      refine mem_oddCoreIn_of_mem_coreActionKernel hZ hx
        (mem_coreActionKernel.mpr ⟨le_normalizer hx, fun y hy => ?_⟩)
      have hq' := (FooteLit.mk_mem_center_iff _ w).mp hq ⟨y, hXW hy⟩
      rw [mem_subgroupOf] at hq'
      have hk : (w : G)⁻¹ * y⁻¹ * w * y ∈ C := by
        have e : (((⟨y, hXW hy⟩ * w)⁻¹ * (w * ⟨y, hXW hy⟩) : ↥W) : G) =
            (w : G)⁻¹ * y⁻¹ * w * y := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [← e]
        exact hq'
      have hkX : (w : G)⁻¹ * y⁻¹ * w * y ∈ X := by
        have h1 : (w : G)⁻¹ * y⁻¹ * w ∈ X := by
          have := (mem_normalizer_iff.mp (inv_mem hwN) y⁻¹).mp (inv_mem hy)
          rwa [inv_inv] at this
        exact mul_mem h1 hy
      have hkO := mem_oddCoreIn_of_mem_coreActionKernel hZ hkX hk
      have hm : x⁻¹ * y⁻¹ * x ∈ X := mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx
      have ho₁ : c⁻¹ * (x⁻¹ * y⁻¹ * x) * c * (x⁻¹ * y⁻¹ * x)⁻¹ ∈ oddCoreIn X := by
        have h1 := (mem_coreActionKernel.mp hc).2 _ (inv_mem hm)
        have e : c⁻¹ * (x⁻¹ * y⁻¹ * x) * c * (x⁻¹ * y⁻¹ * x)⁻¹ =
            ((x⁻¹ * y⁻¹ * x)⁻¹⁻¹ * c⁻¹ * (x⁻¹ * y⁻¹ * x)⁻¹ * c)⁻¹ := by group
        rw [e]
        exact inv_mem h1
      have e : y⁻¹ * x⁻¹ * y * x = ((c⁻¹ * (x⁻¹ * y⁻¹ * x) * c * (x⁻¹ * y⁻¹ * x)⁻¹)⁻¹ *
          ((w : G)⁻¹ * y⁻¹ * w * y))⁻¹ := by
        rw [hw]
        group
      rw [e]
      exact inv_mem (mul_mem (inv_mem ho₁) hkO)
    rw [mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf, hw]
    exact mul_mem (oddCoreIn_le_coreActionKernel_self X hxO) hc
  have hQX : Nat.card (↥W ⧸ C.subgroupOf W) ≤ Nat.card (↥X ⧸ Open.fusionZStar ↥X) := by
    rw [(Sol78.fusionZStar_eq_iff ↥X).mpr hZ]
    let f : ↥X →* ↥W ⧸ C.subgroupOf W := (QuotientGroup.mk' _).comp (Subgroup.inclusion hXW)
    have hfO : pPrimeCore 2 ↥X ≤ f.ker := fun o ho => by
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' _ (Subgroup.inclusion hXW o) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact oddCoreIn_le_coreActionKernel_self X ((mem_pPrimeCore_iff_mem_oddCoreIn o).mp ho)
    have hfs : Function.Surjective f := by
      intro q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, hx, c, hc, hw⟩ := Sol76.exists_mul_of_mem_sup_normalizer hCN w.2
      refine ⟨⟨x, hx⟩, ?_⟩
      change QuotientGroup.mk' _ (Subgroup.inclusion hXW ⟨x, hx⟩) = QuotientGroup.mk w
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [hw, inv_mul_cancel_left]
      exact hc
    exact Nat.card_le_card_of_surjective _
      (QuotientGroup.lift_surjective_of_surjective _ f hfs hfO)
  let g : ↥J →* ↥W ⧸ C.subgroupOf W := (QuotientGroup.mk' _).comp (Subgroup.inclusion hJW)
  have hgker : ∀ j : ↥J, j ∈ g.ker ↔ (j : G) ∈ C := fun j => by
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' _ (Subgroup.inclusion hJW j) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have hker : g.ker ≤ Open.fusionZStar ↥J := by
    rw [Sol78.fusionZStar_eq_comap]
    set π := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπ
    have hNn : (g.ker.map π).Normal :=
      (MonoidHom.normal_ker g).map π (QuotientGroup.mk'_surjective _)
    obtain ⟨hperf, hsimple, -⟩ := hJq
    set π₂ := QuotientGroup.mk' (center (↥J ⧸ pPrimeCore 2 ↥J)) with hπ₂
    have hN2 : ((g.ker.map π).map π₂).Normal := hNn.map π₂ (QuotientGroup.mk'_surjective _)
    rcases hN2.eq_bot_or_eq_top with hbot | htop
    · intro j hj
      rw [mem_comap]
      have h1 : π j ∈ (g.ker.map π) := mem_map_of_mem π hj
      have h2 : π₂ (π j) ∈ ((g.ker.map π).map π₂) := mem_map_of_mem π₂ h1
      rw [hbot, mem_bot, hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    · exfalso
      apply hJX
      have hsup : g.ker.map π ⊔ center (↥J ⧸ pPrimeCore 2 ↥J) = ⊤ := by
        have hcomap := Subgroup.comap_map_eq π₂ (g.ker.map π)
        rw [htop, Subgroup.comap_top, hπ₂, QuotientGroup.ker_mk'] at hcomap
        exact hcomap.symm
      have hder : commutator (↥J ⧸ pPrimeCore 2 ↥J) ≤ g.ker.map π :=
        Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
      rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hder
      rw [← hJres]
      refine (closure_le _).mpr ?_
      rintro y ⟨hyJ, k, hk⟩
      have hy : π ⟨y, hyJ⟩ ∈ g.ker.map π := hder ▸ mem_top _
      obtain ⟨n, hn, hny⟩ := hy
      have hno : n⁻¹ * ⟨y, hyJ⟩ ∈ pPrimeCore 2 ↥J := QuotientGroup.eq.mp hny
      set o : ↥J := n⁻¹ * ⟨y, hyJ⟩ with hodef
      have hoodd : Odd (orderOf (o : G)) := by
        rw [Subgroup.orderOf_coe]
        have h1 := orderOf_dvd_natCard (⟨o, hno⟩ : pPrimeCore 2 ↥J)
        rw [Subgroup.orderOf_mk] at h1
        exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
      have hCJ : C ⊓ J ≤ J := inf_le_right
      have hJCJ : J ≤ normalizer ((C ⊓ J : Subgroup G) : Set G) := by
        intro j hj
        rw [mem_normalizer_iff]
        intro u
        constructor
        · intro hu
          obtain ⟨huC, huJ⟩ := mem_inf.mp hu
          exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hWNC (hJW hj)) u).mp huC,
            mul_mem (mul_mem hj huJ) (inv_mem hj)⟩
        · intro hu
          obtain ⟨huC, huJ⟩ := mem_inf.mp hu
          refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hWNC (hJW hj)) u).mpr huC, ?_⟩
          have h1 := mul_mem (mul_mem (inv_mem hj) huJ) hj
          rwa [show j⁻¹ * (j * u * j⁻¹) * j = u by group] at h1
      have hnC : ((n : ↥J) : G) ∈ C ⊓ J := mem_inf.mpr ⟨(hgker n).mp hn, n.2⟩
      have hy' : y = ((n : G) * (o : G) * (n : G)⁻¹) * (n : G) := by
        rw [hodef]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hoodd' : Odd (orderOf ((n : G) * (o : G) * (n : G)⁻¹)) := by
        rw [show (n : G) * (o : G) * (n : G)⁻¹ = (MulAut.conj (n : G)) (o : G) by simp,
          MulEquiv.orderOf_eq]
        exact hoodd
      have hmem := Sol76.mem_of_eq_mul_of_odd hCJ hJCJ hy'
        (mul_mem (mul_mem n.2 o.2) (J.inv_mem n.2)) hnC hoodd' hk
      exact (mem_inf.mp hmem).1
  have hJg : Nat.card (↥J ⧸ Open.fusionZStar ↥J) ≤ Nat.card g.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le hker)
  have hrange : g.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm (Subgroup.card_le_card_group _) (hQX.trans (hcard.trans hJg))
  have hzcen : (QuotientGroup.mk ⟨z, hJW hzJ⟩ : ↥W ⧸ C.subgroupOf W) ∈ center _ := by
    rw [mem_center_iff]
    intro q
    have hq : q ∈ g.range := hrange ▸ mem_top q
    obtain ⟨j, rfl⟩ := hq
    change QuotientGroup.mk' _ (Subgroup.inclusion hJW j) * _ =
      _ * QuotientGroup.mk' _ (Subgroup.inclusion hJW j)
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
    exact hzc j j.2
  rw [hcen, mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf] at hzcen
  exact hzcen

theorem exists_center_ne_bot_of_moves {H J : Subgroup G} {z : G}
    (hJL : J ≤ twoLayerIn H) (hJperf : ⁅J, J⁆ = J) (hJres : oddResidualIn J = J)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hzc : ∀ j ∈ J, j * z = z * j)
    (hcard : ∀ X : Subgroup G, IsTwoComponentIn X H → ¬ J ≤ coreActionKernel X →
      Nat.card (↥X ⧸ Open.fusionZStar ↥X) ≤ Nat.card (↥J ⧸ Open.fusionZStar ↥J)) :
    ∃ X : Subgroup G, IsTwoComponentIn X H ∧ ¬ J ≤ coreActionKernel X ∧
      center (↥X ⧸ pPrimeCore 2 ↥X) ≠ ⊥ := by
  by_contra hno
  push Not at hno
  set Smv := {X | IsTwoComponentIn X H ∧ ¬ J ≤ coreActionKernel X} with hSmv
  set N₀ : Subgroup G := ⨆ X ∈ {X | IsTwoComponentIn X H}, oddCoreIn X with hN₀
  have hzC : ∀ X, IsTwoComponentIn X H → z ∈ coreActionKernel X := fun X hX => by
    by_cases hJX : J ≤ coreActionKernel X
    · exact hJX hzJ
    · exact mem_coreActionKernel_of_center_eq_bot hX hJL hJres hJq hJX (hno X hX hJX)
        (hcard X hX hJX) hzJ hzc
  have hN₀C : ∀ X, IsTwoComponentIn X H → N₀ ≤ coreActionKernel X := fun X hX =>
    iSup₂_le fun Y hY => by
      by_cases hYX : Y = X
      · rw [hYX]
        exact oddCoreIn_le_coreActionKernel_self X
      · exact (map_subtype_le _ : oddCoreIn Y ≤ Y).trans
          (GSThmB.B5a.le_coreActionKernel_of_ne hX.1 hY.1 hX.2 hY.2 (Ne.symm hYX))
  have hzP := le_sup_of_le_twoLayerIn hJL hJperf hzJ
  have hN₀L : N₀ ≤ twoLayerIn H := iSup₂_le fun Y hY =>
    (map_subtype_le _ : oddCoreIn Y ≤ Y).trans (le_twoLayerIn_of_isTwoComponentIn hY)
  have hN₀P : N₀ ≤ normalizer ((⨆ X ∈ Smv, X : Subgroup G) : Set G) :=
    le_normalizer_biSup fun X hX => hN₀L.trans (twoLayerIn_le_normalizer hX.1.1 hX.1.2)
  obtain ⟨p, hp, o, ho, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hN₀P hzP
  have hpC : ∀ X ∈ Smv, p ∈ coreActionKernel X := fun X hX => by
    have h1 := mul_mem (hzC X hX.1) (inv_mem (hN₀C X hX.1 ho))
    rwa [mul_inv_cancel_right] at h1
  have hpO := mem_biSup_oddCoreIn_of_mem_biSup (fun X hX => hX.1) (fun X hX => hno X hX.1 hX.2)
    hp hpC
  have hpN : p ∈ N₀ :=
    (iSup₂_le fun X hX => le_biSup (fun X => oddCoreIn X) (show X ∈ {X | IsTwoComponentIn X H}
      from hX.1) : (⨆ X ∈ Smv, oddCoreIn X : Subgroup G) ≤ N₀) hpO
  have hN₀O : N₀ ≤ oddCoreIn H := iSup₂_le fun X hX => oddCoreIn_le_of_isTwoComponentIn hX
  have hzO : p * o ∈ oddCoreIn H := hN₀O (mul_mem hpN ho)
  have h1 := orderOf_dvd_natCard (⟨p * o, hzO⟩ : oddCoreIn H)
  rw [Subgroup.orderOf_mk, hz] at h1
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn H) h1) (by norm_num)

end CFSG.ComponentClassification.Sol76.RankOneClass
