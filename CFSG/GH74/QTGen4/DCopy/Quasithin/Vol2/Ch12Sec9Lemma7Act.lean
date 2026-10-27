module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Act
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma9W0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement Pointwise

namespace L1297

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem isPGroup_centralizerMod_sup_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    IsPGroup 2 ↥(centralizerMod V₁ (L ⊔ T) V) := by
  obtain ⟨-, hsq, -⟩ := h.card_sq
  have hT2 : IsPGroup 2 T := h.hyp.sylow.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hQ := (inf_centralizer_eq_sup_inf_centralizer_F4 h1222 h).1
  intro x
  obtain ⟨hxX, hxN, hxc⟩ := x.2
  have hx2 : (x : G) * (x : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hQ]
    refine ⟨Subgroup.mul_mem _ hxX hxX, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    set c := (x : G) * u * (x : G)⁻¹ * u⁻¹ with hcdef
    have hd : c ∈ V₁ := hxc u hu
    have hxc' : (x : G) * c * (x : G)⁻¹ = c := by
      have h1 := Subgroup.mem_centralizer_iff.1
        (le_centralizer_normalizer_of_card_eq_two hV₁2 hd) _ hxN
      rw [h1, mul_inv_cancel_right]
    have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hV₁.1 hd)
    have hxu : (x : G) * u * (x : G)⁻¹ = c * u := by rw [hcdef]; group
    have key : (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ = u := by
      calc (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ =
            (x : G) * ((x : G) * u * (x : G)⁻¹) * (x : G)⁻¹ := by group
        _ = (x : G) * (c * u) * (x : G)⁻¹ := by rw [hxu]
        _ = ((x : G) * c * (x : G)⁻¹) * ((x : G) * u * (x : G)⁻¹) := by group
        _ = c * (c * u) := by rw [hxc', hxu]
        _ = u := by rw [← mul_assoc, hcc, one_mul]
    calc u * ((x : G) * (x : G)) =
          ((x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹) * ((x : G) * (x : G)) := by
          rw [key]
      _ = (x : G) * (x : G) * u := by group
  obtain ⟨k, hk⟩ := (hT2.to_le inf_le_left) ⟨_, hx2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
  rw [pow_succ', pow_mul, sq]
  exact h1

theorem centralizerMod_sup_le_T_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    centralizerMod V₁ (L ⊔ T) V ≤ T := by
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  exact L1296.le_of_isPGroup h.hyp.sylow (isPGroup_centralizerMod_sup_F4 h1222 h hV₁)
    (L1296.le_normalizer_centralizerMod (le_sup_right.trans Subgroup.le_normalizer) hV₁.2.2 hTV)

theorem exists_mem_T_conj_mul_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {z : G}
    (hz : z ∈ V₁) (hz1 : z ≠ 1) {u : G} (hu : u ∈ V) (huV₁ : u ∉ V₁) :
    ∃ t ∈ T, t * u * t⁻¹ = u * z ∧ ∀ x ∈ V₁, t * x * t⁻¹ = x := by
  classical
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hzV := hV₁.1 hz
  let _ := zmodModuleOf hsq
  set a₁ : Additive ↥V := Additive.ofMul ⟨z, hzV⟩ with ha₁
  set a₂ : Additive ↥V := Additive.ofMul ⟨u, hu⟩ with ha₂
  have ha : a₂ ∉ (ZMod 2) ∙ a₁ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      apply huV₁
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₂, toMul_ofMul, toMul_zero, OneMemClass.coe_one] at this
      rw [← this]
      exact V₁.one_mem
    · rw [one_smul] at hc
      apply huV₁
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₁, ha₂, toMul_ofMul] at this
      rw [← this]
      exact hz
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem ha
  have hfa₁ : f a₁ = 0 := LinearMap.mem_ker.1 (hf2 (Submodule.mem_span_singleton_self a₁))
  have hfa₂ : f a₂ = 1 := Flag.zmod_two_eq_one hf1
  let τ0 : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight a₁
  have hτ0 : ∀ x, τ0 x = x + f x • a₁ := fun x => rfl
  have hinv : Function.Involutive τ0 := by
    intro x
    rw [hτ0, hτ0, map_add, map_smul, hfa₁, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  let α : MulAut ↥V :=
    { toFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      invFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      right_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, toMul_add] }
  have hα : ∀ x : ↥V, ((α x : ↥V) : G) = (x : G) ∨ ((α x : ↥V) : G) = (x : G) * z := by
    intro x
    have e : α x = x * Additive.toMul (f (Additive.ofMul x) • a₁) := by
      show Additive.toMul (τ0 (Additive.ofMul x)) = _
      rw [hτ0, toMul_add, toMul_ofMul]
    rcases zmod_two_cases (f (Additive.ofMul x)) with h0 | h1
    · left
      rw [e, h0, zero_smul, toMul_zero, mul_one]
    · right
      rw [e, h1, one_smul, Subgroup.coe_mul, ha₁, toMul_ofMul]
  have hαu : ((α ⟨u, hu⟩ : ↥V) : G) = u * z := by
    show ((Additive.toMul (τ0 a₂) : ↥V) : G) = _
    rw [hτ0, hfa₂, one_smul, toMul_add, Subgroup.coe_mul, ha₁, ha₂, toMul_ofMul, toMul_ofMul]

  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨g, hgN⟩, hgL, hgα⟩ := hαL
  have hgL' : g ∈ L := Subgroup.mem_subgroupOf.1 hgL
  have hconj : ∀ x (hx : x ∈ V), g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hgα]
    rfl

  have hgV₁ : ∀ x ∈ V₁, g * x * g⁻¹ = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      group
    have e := SteinbergBS.eq_of_card_le_two hV₁2.le hx hz hx1 hz1
    subst e
    rw [hconj x hzV]
    show ((Additive.toMul (τ0 a₁) : ↥V) : G) = x
    rw [hτ0, hfa₁, zero_smul, add_zero, ha₁, toMul_ofMul]
  have hgN₁ : g ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => by
      have := hgV₁ x hx
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group)
  have hgE : g ∈ centralizerMod V₁ (L ⊔ T) V := by
    refine ⟨Subgroup.mem_sup_left hgL', hgN₁, fun w hw => ?_⟩
    rw [hconj w hw]
    rcases hα ⟨w, hw⟩ with e | e
    · rw [e, mul_inv_cancel]
      exact V₁.one_mem
    · rw [e, show w * z * w⁻¹ = z from by rw [hab w hw z hzV]; group]
      exact hz
  exact ⟨g, centralizerMod_sup_le_T_F4 h1222 h hV₁ hgE, by rw [hconj u hu, hαu], hgV₁⟩

theorem exists_mem_sup_conj_eq_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {u u' : G}
    (hu : u ∈ V) (hu' : u' ∈ V) (huV₁ : u ∉ V₁) (hu'V₁ : u' ∉ V₁) :
    ∃ s ∈ lOne L V₁ ⊔ T, s * u * s⁻¹ = u' := by
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  obtain ⟨σ, hσ, hσu⟩ := exists_mem_lOne_conj h hV₁ hu hu' huV₁ hu'V₁
  set c := σ * u * σ⁻¹ * u'⁻¹ with hc
  by_cases hc1 : c = 1
  · refine ⟨σ, Subgroup.mem_sup_left hσ, ?_⟩
    calc σ * u * σ⁻¹ = c * u' := by rw [hc]; group
      _ = u' := by rw [hc1, one_mul]

  have hu'c : u' * c ∈ V := V.mul_mem hu' (hV₁.1 hσu)
  have hu'cV₁ : u' * c ∉ V₁ := fun h1 => hu'V₁ (by
    have := V₁.mul_mem h1 (V₁.inv_mem hσu)
    rwa [mul_inv_cancel_right] at this)
  obtain ⟨t, htT, htu, -⟩ := exists_mem_T_conj_mul_F4 h1222 h hV₁ hσu hc1 hu'c hu'cV₁
  refine ⟨t * σ, Subgroup.mul_mem _ (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hσ), ?_⟩
  have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hV₁.1 hσu)
  have hσu' : σ * u * σ⁻¹ = u' * c := by
    rw [hab u' hu' c (hV₁.1 hσu), hc]
    group
  calc t * σ * u * (t * σ)⁻¹ = t * (σ * u * σ⁻¹) * t⁻¹ := by group
    _ = t * (u' * c) * t⁻¹ := by rw [hσu']
    _ = u' * c * c := htu
    _ = u' := by rw [mul_assoc, hcc, mul_one]

theorem sup_le_of_not_le_normalizer_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {X : Subgroup G}
    (hL₁X : lOne L V₁ ⊔ T ≤ X) (hXLT : X ≤ L ⊔ T)
    (hXN : ¬ X ≤ Subgroup.normalizer (V₁ : Set G)) : L ⊔ T ≤ X := by
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le h.hyp.irrPlus.2.2.1 hTV
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ V₁, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall V₁).2 hall
    rw [this, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  have hzV := hV₁.1 hz
  obtain ⟨x, hxX, hxN⟩ := IsConcreteLE.not_le_iff_exists.1 hXN
  have hxLT := hXLT hxX
  intro l hl
  by_cases hlN : l ∈ Subgroup.normalizer (V₁ : Set G)
  · exact hL₁X (normalizer_sup_inf_le h hV₁ ⟨hl, hlN⟩)
  have ha := conj_not_mem_of_not_mem_normalizer hV₁2 hz hz1 hxN
  have hb := conj_not_mem_of_not_mem_normalizer hV₁2 hz hz1 hlN
  have haV : x * z * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLTV hxLT) z).1 hzV
  have hbV : l * z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLTV hl) z).1 hzV
  obtain ⟨s, hs, hsab⟩ := exists_mem_sup_conj_eq_F4 h1222 h hV₁ haV hbV ha hb
  have hsLT : s ∈ L ⊔ T := (sup_le_sup_right ((oTwoUpper_le _).trans inf_le_left) T) hs
  set g := l⁻¹ * s * x with hg
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = l⁻¹ * (s * (x * z * x⁻¹) * s⁻¹) * l := by rw [hg]; group
      _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [hsab]
      _ = z := by group
  have hgN := mem_normalizer_of_conj_eq hV₁2 hz hz1 hgz
  have hgLT : g ∈ L ⊔ T := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) hsLT)
    hxLT
  have hgX : g ∈ X := hL₁X (normalizer_sup_inf_le h hV₁ ⟨hgLT, hgN⟩)
  have hl' : l = s * x * g⁻¹ := by rw [hg]; group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL₁X hs) hxX) (Subgroup.inv_mem _ hgX)

end L1297

end CFSG.Quasithin.H13
