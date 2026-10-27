module

public import CFSG.LieType.SeitzGeneration.ClassicalSeitzStatus
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration
open scoped commutatorElement

section Pure

theorem exists_fixed_mul_central {Y : Type*} [Group Y]
    (hcop : (Nat.card (Subgroup.center Y)).Coprime 3) (ε : MulAut Y) (hε : ε ^ 3 = 1) {x : Y}
    (hx0 : x⁻¹ * ε x ∈ Subgroup.center Y) :
    ∃ w ∈ Subgroup.center Y, ε (x * w) = x * w := by
  classical
  have hZfin : Finite (Subgroup.center Y) := by
    have h0 : Nat.card (Subgroup.center Y) ≠ 0 := by
      intro h
      rw [h] at hcop
      norm_num at hcop
    exact Nat.finite_of_card_ne_zero h0
  have hx : ε x * x⁻¹ ∈ Subgroup.center Y := by
    have hc := Subgroup.mem_center_iff.1 hx0 x
    have h1 : ε x * x⁻¹ = x⁻¹ * ε x := by
      calc ε x * x⁻¹ = (x * (x⁻¹ * ε x)) * x⁻¹ := by group
        _ = ((x⁻¹ * ε x) * x) * x⁻¹ := by rw [hc]
        _ = x⁻¹ * ε x := by group
    rw [h1]
    exact hx0
  have hεZ : ∀ z ∈ Subgroup.center Y, ε z ∈ Subgroup.center Y := fun z hz => by
    have := Subgroup.map_center_eq ε
    rw [← this]
    exact Subgroup.mem_map_of_mem _ hz
  let α : Type _ := {y : Y // x⁻¹ * y ∈ Subgroup.center Y}
  haveI : Finite α := by
    refine Finite.of_injective (fun y : α => (⟨x⁻¹ * y.1, y.2⟩ : Subgroup.center Y)) ?_
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this
  haveI : Fintype α := Fintype.ofFinite α
  have hcoset : ∀ y : Y, x⁻¹ * y ∈ Subgroup.center Y → x⁻¹ * ε y ∈ Subgroup.center Y := by
    intro y hy
    have h1 : ε y = ε x * ε (x⁻¹ * y) := by
      rw [← map_mul]
      simp
    have h3 : x⁻¹ * ε y = (ε x * x⁻¹) * ε (x⁻¹ * y) := by
      rw [h1]
      have hc : ∀ g : Y, g * (ε x * x⁻¹) = (ε x * x⁻¹) * g := fun g =>
        Subgroup.mem_center_iff.1 hx g
      calc x⁻¹ * (ε x * ε (x⁻¹ * y))
          = (x⁻¹ * (ε x * x⁻¹)) * (x * ε (x⁻¹ * y)) := by group
        _ = ((ε x * x⁻¹) * x⁻¹) * (x * ε (x⁻¹ * y)) := by rw [hc x⁻¹]
        _ = (ε x * x⁻¹) * ε (x⁻¹ * y) := by group
    rw [h3]
    exact Subgroup.mul_mem _ hx (hεZ _ hy)
  let f : α → α := fun y => ⟨ε y.1, hcoset y.1 y.2⟩
  have hf3 : ∀ y : α, f (f (f y)) = y := by
    intro y
    apply Subtype.ext
    have h3 : (ε ^ 3) y.1 = y.1 := by rw [hε]; rfl
    have : ε (ε (ε y.1)) = y.1 := by
      simpa [pow_succ, MulAut.mul_apply] using h3
    exact this
  let σ : Equiv.Perm α := ⟨f, fun y => f (f y), fun y => hf3 y, fun y => hf3 y⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext y
    simp only [pow_one, Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq]
    exact congrArg Subtype.val (hf3 y)
  have hαZ : α ≃ Subgroup.center Y :=
    { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
      invFun := fun z => ⟨x * z.1, by simp⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  have hcardα : Fintype.card α = Nat.card (Subgroup.center Y) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr hαZ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hndvd : ¬ 3 ∣ Fintype.card α := by
    rw [hcardα]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop.symm
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hndvd hσ
  refine ⟨x⁻¹ * y.1, y.2, ?_⟩
  have hy' : ε y.1 = y.1 := congrArg Subtype.val hy
  simpa using hy'

theorem commutatorElement_mul_center_left {Y : Type*} [Group Y] {g h z : Y}
    (hz : z ∈ Subgroup.center Y) : ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hzh : h * z = z * h := Subgroup.mem_center_iff.1 hz h
  simp only [commutatorElement_def]
  calc g * z * h * (g * z)⁻¹ * h⁻¹ = g * (z * h) * z⁻¹ * g⁻¹ * h⁻¹ := by group
    _ = g * (h * z) * z⁻¹ * g⁻¹ * h⁻¹ := by rw [hzh]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem commutatorElement_mul_center_right {Y : Type*} [Group Y] {g h z : Y}
    (hz : z ∈ Subgroup.center Y) : ⁅g, h * z⁆ = ⁅g, h⁆ := by
  have hzg : g⁻¹ * z = z * g⁻¹ := Subgroup.mem_center_iff.1 hz g⁻¹
  simp only [commutatorElement_def]
  calc g * (h * z) * g⁻¹ * (h * z)⁻¹ = g * h * (z * g⁻¹) * z⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * z) * z⁻¹ * h⁻¹ := by rw [hzg]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem eq_one_of_inv_mul_mem_center {Y : Type*} [Group Y] (hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤)
    (α : MulAut Y) (h : ∀ y, y⁻¹ * α y ∈ Subgroup.center Y) : α = 1 := by
  let f : Y →* Y :=
    { toFun := fun y => y⁻¹ * α y
      map_one' := by simp
      map_mul' := fun y y' => by
        have h1 : y'⁻¹ * (y⁻¹ * α y) = (y⁻¹ * α y) * y'⁻¹ := Subgroup.mem_center_iff.1 (h y) y'⁻¹
        calc (y * y')⁻¹ * α (y * y') = y'⁻¹ * (y⁻¹ * α y) * α y' := by
              rw [map_mul]; group
          _ = (y⁻¹ * α y) * y'⁻¹ * α y' := by rw [h1]
          _ = (y⁻¹ * α y) * (y'⁻¹ * α y') := by group }
  have hker : (⊤ : Subgroup Y) ≤ f.ker := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (h a) (f b)).symm
  ext y
  have h1 : y⁻¹ * α y = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top y))
  have h2 : α y = y := by
    calc α y = y * (y⁻¹ * α y) := by group
      _ = y := by rw [h1, mul_one]
  simpa using h2

@[expose] def resAut {G : Type*} [Group G] (J : Subgroup G) (ε : MulAut G) (h : ∀ u ∈ J, ε u ∈ J)
    (h' : ∀ u ∈ J, ε.symm u ∈ J) : MulAut J where
  toFun u := ⟨ε u, h u u.2⟩
  invFun u := ⟨ε.symm u, h' u u.2⟩
  left_inv u := Subtype.ext (ε.symm_apply_apply u)
  right_inv u := Subtype.ext (ε.apply_symm_apply u)
  map_mul' a b := Subtype.ext (map_mul ε (a : G) (b : G))

@[expose] def resHom {G : Type*} [Group G] (J : Subgroup G) (E : Subgroup (MulAut G))
    (hE : ∀ ε ∈ E, ∀ u ∈ J, ε u ∈ J) : E →* MulAut J where
  toFun ε := resAut J ε.1 (hE ε.1 ε.2) (fun u hu => hE ε.1⁻¹ (E.inv_mem ε.2) u hu)
  map_one' := by
    ext u
    rfl
  map_mul' a b := by
    ext u
    rfl

theorem resHom_apply {G : Type*} [Group G] (J : Subgroup G) (E : Subgroup (MulAut G))
    (hE : ∀ ε ∈ E, ∀ u ∈ J, ε u ∈ J) (ε : E) (u : J) :
    ((resHom J E hE ε u : J) : G) = ε.1 u := rfl

@[expose] def inducedAut {Y C : Type*} [Group Y] [Group C] (φ : Y ⧸ Subgroup.center Y ≃* C) (α : MulAut Y) :
    MulAut C :=
  φ.symm.trans ((QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) α
    (Subgroup.map_center_eq α)).trans φ)

theorem inducedAut_apply {Y C : Type*} [Group Y] [Group C] (φ : Y ⧸ Subgroup.center Y ≃* C)
    (α : MulAut Y) (y : Y) :
    inducedAut φ α (φ (QuotientGroup.mk y)) = φ (QuotientGroup.mk (α y)) := by
  simp [inducedAut]

@[expose] def inducedHom {Y C : Type*} [Group Y] [Group C] (φ : Y ⧸ Subgroup.center Y ≃* C) :
    MulAut Y →* MulAut C where
  toFun := inducedAut φ
  map_one' := by
    ext c
    obtain ⟨q, rfl⟩ := φ.surjective c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    simp [inducedAut_apply]
  map_mul' a b := by
    ext c
    obtain ⟨q, rfl⟩ := φ.surjective c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    simp [inducedAut_apply]

end Pure

section Seitz


theorem planeGen_of_central_quotient {Y : Type*} [Group Y]
    (hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤) (hZ : (Nat.card (Subgroup.center Y)).Coprime 3)
    (d : TauCeti.ValidLieTypeIndex) (hchar : 3 ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException 3 d.1) (hcl : IsClassicalIndex d.1) (hD4 : ¬ IsDFourIndex d.1)
    (φ : Y ⧸ Subgroup.center Y ≃* Cat d) (E' : Subgroup (MulAut Y)) (hE' : IsElemAbelian 3 E')
    (hcard : Nat.card E' = 3 ^ 2) :
    Subgroup.closure {u : Y | ∃ ε ∈ E', ε ≠ 1 ∧ ε u = u} = ⊤ := by
  classical
  set ψ : MulAut Y →* MulAut (Cat d) := inducedHom φ with hψ
  have hψapply : ∀ (ε : MulAut Y) (y : Y),
      ψ ε (φ (QuotientGroup.mk y)) = φ (QuotientGroup.mk (ε y)) := fun ε y =>
    inducedAut_apply φ ε y
  have hker : ∀ ε ∈ E', ψ ε = 1 → ε = 1 := by
    intro ε _ h1
    refine eq_one_of_inv_mul_mem_center hperf ε fun y => ?_
    have h2 : φ (QuotientGroup.mk (ε y)) = φ (QuotientGroup.mk y) := by
      rw [← hψapply, h1]
      rfl
    have h3 := φ.injective h2
    exact QuotientGroup.eq.1 h3.symm
  have hE''ab : IsElemAbelian 3 (E'.map ψ) := CFSG.Open.IsElemAbelian.map hE' ψ
  have hE''card : Nat.card (E'.map ψ) = 3 ^ 2 := by
    rw [← hcard]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun ε : E' => (⟨ψ ε, Subgroup.mem_map_of_mem _ ε.2⟩ : E'.map ψ)) ⟨?_, ?_⟩)
    · intro a b h
      have h1 : ψ a = ψ b := congrArg Subtype.val h
      have h2 : ψ ((a⁻¹ * b : E') : MulAut Y) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hker _ (E'.mul_mem (E'.inv_mem a.2) b.2) h2
      have h4 : a⁻¹ * b = 1 := Subtype.ext h3
      exact (inv_mul_eq_one.1 h4)
    · rintro ⟨_, ε, hε, rfl⟩
      exact ⟨⟨ε, hε⟩, rfl⟩
  have hPG : planeClosure (E'.map ψ) = ⊤ := by
    by_cases hin : InnerPlane d 3 (E'.map ψ)
    · exact seitzInnerThreeClassical_holds d 3 Nat.prime_three (by norm_num) hchar hex _ hE''ab
        hE''card ⟨hin, rfl, hcl⟩
    · exact seitzOuterClassical_holds d 3 Nat.prime_three (by norm_num) hchar hex _ hE''ab
        hE''card ⟨hin, hcl, fun h => hD4 h.2⟩
  set M : Subgroup Y := Subgroup.closure {u : Y | ∃ ε ∈ E', ε ≠ 1 ∧ ε u = u} with hM
  set q : Y →* Cat d := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hq
  have hq_apply : ∀ y, q y = φ (QuotientGroup.mk y) := fun y => rfl
  have hq_surj : Function.Surjective q := by
    intro c
    obtain ⟨x, rfl⟩ := φ.surjective c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨y, rfl⟩
  have hqM : M.map q = ⊤ := by
    rw [eq_top_iff, ← hPG]
    refine (Subgroup.closure_le _).2 ?_
    rintro k ⟨ē, hē, hē1, hēk⟩
    obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.1 hē
    obtain ⟨y, rfl⟩ := hq_surj k
    have hε1 : ε ≠ 1 := fun h => hē1 (by rw [h, map_one])
    have h1 : φ (QuotientGroup.mk (ε y)) = φ (QuotientGroup.mk y) := by
      rw [← hψapply]
      exact hēk
    have h2 : y⁻¹ * ε y ∈ Subgroup.center Y := QuotientGroup.eq.1 (φ.injective h1).symm
    obtain ⟨w, hw, hεw⟩ := exists_fixed_mul_central hZ ε (by
      have := hE'.2 ε hε
      simpa using this) h2
    refine ⟨y * w, Subgroup.subset_closure ⟨ε, hε, hε1, hεw⟩, ?_⟩
    rw [map_mul, hq_apply w, (QuotientGroup.eq_one_iff w).2 hw, map_one, mul_one]
  have hMZ : ∀ y : Y, ∃ m ∈ M, m⁻¹ * y ∈ Subgroup.center Y := by
    intro y
    have : q y ∈ M.map q := by rw [hqM]; exact Subgroup.mem_top _
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 this
    refine ⟨m, hm, ?_⟩
    exact QuotientGroup.eq.1 (φ.injective hmy)
  have hcomm : (⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ : Subgroup Y) ≤ M := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    obtain ⟨m₁, hm₁, hz₁⟩ := hMZ g₁
    obtain ⟨m₂, hm₂, hz₂⟩ := hMZ g₂
    have e1 : g₁ = m₁ * (m₁⁻¹ * g₁) := by group
    have e2 : g₂ = m₂ * (m₂⁻¹ * g₂) := by group
    rw [e1, e2, commutatorElement_mul_center_left hz₁, commutatorElement_mul_center_right hz₂]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
  rw [hperf] at hcomm
  exact top_le_iff.1 hcomm

theorem levi_le_planeClosure {G : Type*} [Group G] (J : Subgroup G) (E : Subgroup (MulAut G))
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hinv : ∀ ε ∈ E, ∀ u ∈ J, ε u ∈ J) (hperf : ⁅J, J⁆ = J)
    (hZ : (Nat.card (Subgroup.center J)).Coprime 3)
    (d : TauCeti.ValidLieTypeIndex) (hchar : 3 ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException 3 d.1) (hcl : IsClassicalIndex d.1) (hD4 : ¬ IsDFourIndex d.1)
    (φ : J ⧸ Subgroup.center J ≃* Cat d) :
    J ≤ planeClosure E := by
  classical
  by_cases hfix : ∃ ε ∈ E, ε ≠ 1 ∧ ∀ u ∈ J, ε u = u
  · obtain ⟨ε, hε, hε1, hεJ⟩ := hfix
    intro u hu
    exact mem_planeClosure_of_fixed hε hε1 (hεJ u hu)
  · push Not at hfix
    set ρ : E →* MulAut J := resHom J E hinv with hρ
    have hρinj : Function.Injective ρ := by
      refine (injective_iff_map_eq_one ρ).2 fun ε hε1 => ?_
      by_contra hne
      have hne' : ε.1 ≠ 1 := fun h => hne (Subtype.ext h)
      obtain ⟨u, hu, hεu⟩ := hfix ε.1 ε.2 hne'
      apply hεu
      have := congrArg (fun a : MulAut J => ((a ⟨u, hu⟩ : J) : G)) hε1
      simpa [hρ, resHom_apply] using this
    set E' : Subgroup (MulAut J) := ρ.range with hE'
    have hE'ab : IsElemAbelian 3 E' := by
      obtain ⟨hc, he⟩ := hE
      refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
      · obtain ⟨_, ε₁, rfl⟩ := a
        obtain ⟨_, ε₂, rfl⟩ := b
        apply Subtype.ext
        change ρ ε₁ * ρ ε₂ = ρ ε₂ * ρ ε₁
        rw [← map_mul, ← map_mul, mul_comm' ε₁ ε₂]
      · obtain ⟨ε, rfl⟩ := hx
        rw [← map_pow]
        have : ε ^ 3 = 1 := Subtype.ext (he ε.1 ε.2)
        rw [this, map_one]
    have hE'card : Nat.card E' = 3 ^ 2 := by
      rw [← hcard]
      exact (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
    have hperf' : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
      apply Subgroup.map_injective (Subgroup.subtype_injective J)
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hperf
    have hgen := planeGen_of_central_quotient hperf' hZ d hchar hex hcl hD4 φ E' hE'ab hE'card
    intro u hu
    have hmem : (⟨u, hu⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
    rw [← hgen] at hmem
    have hS : Subgroup.map J.subtype (Subgroup.closure {v : J | ∃ ε ∈ E', ε ≠ 1 ∧ ε v = v}) ≤
        planeClosure E := by
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨v, ⟨ε', hε', hε'1, hε'v⟩, rfl⟩
      obtain ⟨ε, rfl⟩ := hε'
      refine mem_planeClosure_of_fixed ε.2 ?_ ?_
      · intro h1
        apply hε'1
        have : ε = 1 := Subtype.ext h1
        rw [this, map_one]
      · have := congrArg Subtype.val hε'v
        simpa [hρ, resHom_apply] using this
    exact hS (Subgroup.mem_map.2 ⟨_, hmem, rfl⟩)

end Seitz

end CFSG.LieType.SeitzGeneration.ExcWideThree
