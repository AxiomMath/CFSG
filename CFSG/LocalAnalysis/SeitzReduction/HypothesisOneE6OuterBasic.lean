module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalBasic
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizerBasic

public section

namespace CFSG.SeitzReduction

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LieType.Chevalley (mulAut_conj_injective_of_center_eq_bot mulAut_mul_conj_mul_inv)
open CFSG.LieType.Chevalley.E6SecondGraphFull (SecondGraphFullCentralizer)

theorem NoNormalZ4OrZ2xZ4.of_conj {C : Type*} [Group C] {H : Subgroup (MulAut C)}
    {α η ψ : MulAut C} (hψ : ψ * α * ψ⁻¹ = η)
    (h : NoNormalZ4OrZ2xZ4 ↥(H.map (MulAut.conj ψ).toMonoidHom ⊓
      centralizer ({η} : Set (MulAut C)))) :
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({α} : Set (MulAut C))) := by
  have hcentr : H.map (MulAut.conj ψ).toMonoidHom ⊓ centralizer ({η} : Set (MulAut C)) =
      (H ⊓ centralizer ({α} : Set (MulAut C))).map (MulAut.conj ψ).toMonoidHom := by
    ext y
    simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzη⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [← hψ] at hzη
      have : ψ * (z * α) * ψ⁻¹ = ψ * (α * z) * ψ⁻¹ := by
        calc ψ * (z * α) * ψ⁻¹ = ψ * z * ψ⁻¹ * (ψ * α * ψ⁻¹) := by group
          _ = ψ * α * ψ⁻¹ * (ψ * z * ψ⁻¹) := hzη
          _ = ψ * (α * z) * ψ⁻¹ := by group
      simpa using this
    · rintro ⟨z, ⟨hz, hzα⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [← hψ]
      calc ψ * z * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (z * α) * ψ⁻¹ := by group
        _ = ψ * (α * z) * ψ⁻¹ := by rw [hzα]
        _ = ψ * α * ψ⁻¹ * (ψ * z * ψ⁻¹) := by group
  exact h.of_mulEquiv (((MulAut.conj ψ).subgroupMap _).trans
    (MulEquiv.subgroupCongr hcentr.symm)).symm

theorem abelianNormalCardLeTwo_of_simple_inner {G : Type*} [Group G] {C J : Subgroup G}
    {η : MulAut C} (hη : η ^ 2 = 1) (hJC : J ≤ C) (hJs : IsSimpleGroup J)
    (hinj : Set.InjOn (MulAut.conj : C →* MulAut C) (J.subgroupOf C))
    (hNη : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ centralizer {η})
    (hNnorm : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (centralizer {η})).Normal)
    (hcent : centralizer {η} ⊓ centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = zpowers η)
    (hηI : η ∉ inner C) (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer ({η} : Set (MulAut C))) := by
  set N := (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) with hN
  let φ : ↥(J.subgroupOf C) →* N :=
    ((MulAut.conj : C →* MulAut C).comp (J.subgroupOf C).subtype).codRestrict N
      fun x => ⟨x, x.2, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have : IsSimpleGroup N :=
    ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.ofBijective φ hφ)).symm.isSimpleGroup
  refine abelianNormalCardLeTwo_of_isSimpleGroup hη ?_ hNη ?_ ?_ ?_
  · rintro _ ⟨j, -, rfl⟩
    exact hIH ⟨j, rfl⟩
  · rintro ⟨j, -, hj⟩
    exact hηI ⟨j, hj⟩
  · intro c hc n hn
    exact mem_subgroupOf.1 (hNnorm.conj_mem ⟨n, hNη hn⟩ (mem_subgroupOf.2 hn) ⟨c, hc⟩)
  · intro c hc hcN
    rw [← hcent]
    exact mem_inf.2 ⟨hc, mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩

theorem card_le_and_exponent_of_iso {G : Type*} [Group G] {B : Subgroup G}
    (hiso : Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) :
    Nat.card B ≤ 8 ∧ (∀ b ∈ B, b ^ 4 = 1) ∧ ∃ b ∈ B, b ^ 2 ≠ 1 := by
  rcases hiso with hi | hi
  · obtain ⟨i⟩ := hi
    refine ⟨?_, fun b hb => ?_, ⟨_, (i.symm (Multiplicative.ofAdd 1)).2, fun h => ?_⟩⟩
    · rw [Nat.card_congr i.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]
      omega
    · have h4 : (⟨b, hb⟩ : B) ^ 4 = 1 := i.injective (by
        rw [map_pow, map_one]
        exact (by decide : ∀ x : Multiplicative (ZMod 4), x ^ 4 = 1) _)
      simpa using congrArg Subtype.val h4
    · have h2 : (i.symm (Multiplicative.ofAdd 1)) ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
      have := congrArg i h2
      rw [map_pow, MulEquiv.apply_symm_apply, map_one i] at this
      exact (by decide : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1) this
  · obtain ⟨i⟩ := hi
    refine ⟨?_, fun b hb => ?_, ⟨_, (i.symm (1, Multiplicative.ofAdd 1)).2, fun h => ?_⟩⟩
    · rw [Nat.card_congr i.toEquiv, Nat.card_eq_fintype_card, Fintype.card_prod,
        Fintype.card_multiplicative, Fintype.card_multiplicative, ZMod.card, ZMod.card]
    · have h4 : (⟨b, hb⟩ : B) ^ 4 = 1 := i.injective (by
        rw [map_pow, map_one]
        exact (by decide : ∀ x : Multiplicative (ZMod 2) × Multiplicative (ZMod 4), x ^ 4 = 1) _)
      simpa using congrArg Subtype.val h4
    · have h2 : (i.symm (1, Multiplicative.ofAdd 1)) ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
      have := congrArg i h2
      rw [map_pow, MulEquiv.apply_symm_apply, map_one i] at this
      exact (by decide : ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠
        1) this

theorem sup_inf_centralizer_conj_eq {J : Type*} [Group J] (hZJ : center J = ⊥) {t : J}
    {A : Subgroup (MulAut J)} (hfix : ∀ a ∈ A, a t = t)
    (hIA : ∀ x : J, x * t = t * x → MulAut.conj x ∈ A) :
    (inner J ⊔ A) ⊓ centralizer ({MulAut.conj t} : Set (MulAut J)) = A := by
  have hAτ : A ≤ centralizer ({MulAut.conj t} : Set (MulAut J)) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    have h2 := mulAut_mul_conj_mul_inv a t
    rw [hfix a ha] at h2
    calc a * MulAut.conj t = (a * MulAut.conj t * a⁻¹) * a := by group
      _ = MulAut.conj t * a := by rw [h2]
  refine le_antisymm (fun y hy => ?_) (le_inf le_sup_right hAτ)
  obtain ⟨hyL, hyτ⟩ := mem_inf.1 hy
  have : (inner J).Normal := inner_normal J
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hyL
  obtain ⟨i, hi, a, ha, rfl⟩ := hyL
  obtain ⟨z, rfl⟩ := hi
  have haτ := mem_centralizer_singleton_iff.1 (hAτ ha)
  have hyτ' := mem_centralizer_singleton_iff.1 hyτ
  have hzτ : MulAut.conj t * MulAut.conj z = MulAut.conj z * MulAut.conj t := by
    have h1 : MulAut.conj t * MulAut.conj z * a = MulAut.conj z * MulAut.conj t * a := by
      calc MulAut.conj t * MulAut.conj z * a = MulAut.conj t * (MulAut.conj z * a) := by group
        _ = MulAut.conj z * a * MulAut.conj t := hyτ'.symm
        _ = MulAut.conj z * (a * MulAut.conj t) := by group
        _ = MulAut.conj z * (MulAut.conj t * a) := by rw [haτ]
        _ = MulAut.conj z * MulAut.conj t * a := by group
    exact mul_right_cancel h1
  have hzt : z * t = t * z := by
    have h1 : MulAut.conj (z * t * z⁻¹) = MulAut.conj t := by
      rw [map_mul, map_mul, map_inv, ← hzτ]
      group
    have h2 := mulAut_conj_injective_of_center_eq_bot hZJ h1
    calc z * t = (z * t * z⁻¹) * z := by group
      _ = t * z := by rw [h2]
  exact mul_mem (hIA z hzt) ha

theorem noNormalZ4OrZ2xZ4_inf_centralizer_xi {G : Type*} [Group G] {C J : Subgroup G} {P t : G}
    {F : Type*} {act : F → MulAut J} (hSG : SecondGraphFullCentralizer C J P t act)
    (hP2 : P * P = 1) (hZJ : center J = ⊥) (η : MulAut C) (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (ξ : MulAut C) (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hF4 : ∀ τJ : MulAut J, (∀ x : J, (τJ x : G) = t * x * t⁻¹) →
      ∀ L : Subgroup (MulAut J), inner J ≤ L →
        NoNormalZ4OrZ2xZ4 ↥(L ⊓ centralizer ({τJ} : Set (MulAut J))))
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H)
    (hsq : ∀ B : Subgroup ↥(H ⊓ centralizer ({ξ} : Set (MulAut C))), B.Normal →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → ∀ b ∈ B, (b : MulAut C) ^ 2 ≠ η) :
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({ξ} : Set (MulAut C))) := by
  classical
  obtain ⟨htJ, hJC, η', hη', -, res, -, hker, -, -, hfixt, hinner, -⟩ := hSG
  have e : η = η' := MulEquiv.ext fun g => Subtype.ext (by rw [hη', hη])
  subst e
  have hξη : ξ = MulAut.conj (⟨t, hJC htJ⟩ : C) * η := MulEquiv.ext fun g => Subtype.ext (by
    rw [hξ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη])
  subst hξη
  set τ : MulAut J := MulAut.conj (⟨t, htJ⟩ : J) with hτdef
  have hτ : ∀ x : J, (τ x : G) = t * x * t⁻¹ := fun x => rfl
  have hη2 : η ^ 2 = 1 := MulEquiv.ext fun g => Subtype.ext (by
    rw [pow_two, MulAut.mul_apply, hη, hη, MulAut.one_apply]
    calc P * (P * (g : G) * P⁻¹) * P⁻¹ = (P * P) * g * (P * P)⁻¹ := by group
      _ = g := by rw [hP2, one_mul, inv_one, mul_one])
  set ZH := H ⊓ centralizer ({MulAut.conj (⟨t, hJC htJ⟩ : C) * η} : Set (MulAut C)) with hZH
  have hZHZ : ZH ≤ centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η} := inf_le_right
  set resH : ZH →* MulAut J := res.comp (Subgroup.inclusion hZHZ) with hresHdef
  set A := resH.range with hAdef
  have hfixA : ∀ a ∈ A, a ⟨t, htJ⟩ = ⟨t, htJ⟩ := by
    rintro _ ⟨z, rfl⟩
    exact hfixt _ ⟨_, rfl⟩
  have hIA : ∀ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x → MulAut.conj x ∈ A := by
    intro x hx
    obtain ⟨hxZ, hres⟩ := hinner x hx
    refine ⟨⟨_, hIH ⟨⟨x, hJC x.2⟩, rfl⟩, hxZ⟩, ?_⟩
    rw [hresHdef, MonoidHom.comp_apply]
    exact hres
  have hA : NoNormalZ4OrZ2xZ4 A := by
    have h := hF4 τ hτ (inner J ⊔ A) le_sup_left
    rwa [sup_inf_centralizer_conj_eq hZJ hfixA hIA] at h
  have hkerH : ∀ z : ZH, resH z = 1 → (z : MulAut C) = 1 ∨ (z : MulAut C) = η := by
    intro z hz
    refine eq_one_or_eq_of_mem_zpowers hη2 ?_
    rw [← hker]
    exact ⟨Subgroup.inclusion hZHZ z, hz, rfl⟩
  intro B hB hiso
  obtain ⟨hcardB, hexp, b, hbB, hb2⟩ := card_le_and_exponent_of_iso hiso
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rcases hiso with hi | hi
    · obtain ⟨i⟩ := hi
      exact mul_comm_of_mulEquiv i
    · obtain ⟨i⟩ := hi
      exact mul_comm_of_mulEquiv i
  have hbη := hsq B hB hBab b hbB
  have : Finite B := by
    rcases hiso with hi | hi
    · obtain ⟨i⟩ := hi
      exact Finite.of_equiv _ i.symm.toEquiv
    · obtain ⟨i⟩ := hi
      exact Finite.of_equiv _ i.symm.toEquiv
  set g : B →* A := resH.rangeRestrict.comp B.subtype with hgdef
  have hgn : g.range.Normal := by
    rw [hgdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hB.map _ resH.rangeRestrict_surjective
  refine hA g.range hgn ?_
  by_cases hinj : Function.Injective g
  ·
    have e := (MonoidHom.ofInjective hinj).symm
    rcases hiso with hi | hi
    · obtain ⟨i⟩ := hi
      exact Or.inl ⟨e.trans i⟩
    · obtain ⟨i⟩ := hi
      exact Or.inr ⟨e.trans i⟩
  ·
    left
    have hgb : ((g ⟨b, hbB⟩ : A) : MulAut J) = resH b := rfl
    have hb4 : (g ⟨b, hbB⟩) ^ 2 ^ (1 + 1) = 1 := by
      have h4 : (⟨b, hbB⟩ : B) ^ 2 ^ (1 + 1) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp b hbB)
      rw [← map_pow, h4, map_one]
    have hb2' : ¬ (g ⟨b, hbB⟩) ^ 2 ^ 1 = 1 := by
      intro h
      have h' : resH (b ^ 2) = 1 := by
        have h1 := congrArg Subtype.val h
        rw [pow_one, Subgroup.coe_pow, hgb, Subgroup.coe_one, ← map_pow] at h1
        exact h1
      rcases hkerH _ h' with h1 | h1
      · exact hb2 (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h1))
      · exact hbη (by rw [← h1, Subgroup.coe_pow])
    have hord : orderOf (g ⟨b, hbB⟩) = 4 := orderOf_eq_prime_pow hb2' hb4
    have : Finite g.range := Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
    have hcard : Nat.card g.range * Nat.card g.ker = Nat.card B := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    have hker2 : 2 ≤ Nat.card g.ker := by
      have hne : g.ker ≠ ⊥ := fun h => hinj ((MonoidHom.ker_eq_bot_iff g).1 h)
      have := (Subgroup.one_lt_card_iff_ne_bot g.ker).2 hne
      omega
    have hle : Nat.card g.range ≤ 4 := by
      by_contra hlt
      have h5 : 5 * 2 ≤ Nat.card g.range * Nat.card g.ker := Nat.mul_le_mul (by omega) hker2
      omega
    set c : g.range := ⟨g ⟨b, hbB⟩, ⟨_, rfl⟩⟩ with hcdef
    have hc : orderOf c = 4 := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    have hcard4 : Nat.card g.range = 4 :=
      le_antisymm hle (hc ▸ Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard c))
    have hcyc : IsCyclic g.range := isCyclic_of_orderOf_eq_card c (by rw [hc, hcard4])
    have e := zmodCyclicMulEquiv hcyc
    rw [hcard4] at e
    exact ⟨e.symm⟩

@[expose] def AbelianNormalInner {J : Type*} [Group J] (τ : MulAut J) : Prop :=
  ∀ L : Subgroup (MulAut J), inner J ≤ L →
    ∀ N : Subgroup ↥(L ⊓ centralizer ({τ} : Set (MulAut J))), N.Normal →
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) → ∀ n ∈ N, (n : MulAut J) ∈ inner J

theorem sq_ne_of_abelianNormalInner {G : Type*} [Group G] {C J : Subgroup G} {P t : G}
    {F : Type*} {act : F → MulAut J} (hSG : SecondGraphFullCentralizer C J P t act)
    (hP2 : P * P = 1) (hZJ : center J = ⊥) (η : MulAut C) (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hηI : η ∉ inner C) (ξ : MulAut C) (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hY : ∀ τJ : MulAut J, (∀ x : J, (τJ x : G) = t * x * t⁻¹) → AbelianNormalInner τJ)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    ∀ B : Subgroup ↥(H ⊓ centralizer ({ξ} : Set (MulAut C))), B.Normal →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → ∀ b ∈ B, (b : MulAut C) ^ 2 ≠ η := by
  classical
  obtain ⟨htJ, hJC, η', hη', -, res, hres, hker, -, -, hfixt, hinner, -⟩ := hSG
  have e : η = η' := MulEquiv.ext fun g => Subtype.ext (by rw [hη', hη])
  subst e
  have hξη : ξ = MulAut.conj (⟨t, hJC htJ⟩ : C) * η := MulEquiv.ext fun g => Subtype.ext (by
    rw [hξ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη])
  subst hξη
  set τ : MulAut J := MulAut.conj (⟨t, htJ⟩ : J) with hτdef
  have hτ : ∀ x : J, (τ x : G) = t * x * t⁻¹ := fun x => rfl
  have hη2 : η * η = 1 := MulEquiv.ext fun g => Subtype.ext (by
    rw [MulAut.mul_apply, hη, hη, MulAut.one_apply]
    calc P * (P * (g : G) * P⁻¹) * P⁻¹ = (P * P) * g * (P * P)⁻¹ := by group
      _ = g := by rw [hP2, one_mul, inv_one, mul_one])
  set ZH := H ⊓ centralizer ({MulAut.conj (⟨t, hJC htJ⟩ : C) * η} : Set (MulAut C)) with hZH
  have hZHZ : ZH ≤ centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η} := inf_le_right
  set resH : ZH →* MulAut J := res.comp (Subgroup.inclusion hZHZ) with hresHdef
  set A := resH.range with hAdef
  have hfixA : ∀ a ∈ A, a ⟨t, htJ⟩ = ⟨t, htJ⟩ := by
    rintro _ ⟨z, rfl⟩
    exact hfixt _ ⟨_, rfl⟩
  have hIA : ∀ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x → MulAut.conj x ∈ A := by
    intro x hx
    obtain ⟨hxZ, hres⟩ := hinner x hx
    refine ⟨⟨_, hIH ⟨⟨x, hJC x.2⟩, rfl⟩, hxZ⟩, ?_⟩
    rw [hresHdef, MonoidHom.comp_apply]
    exact hres
  have hLA := sup_inf_centralizer_conj_eq hZJ hfixA hIA
  intro B hB hBab b hbB hb
  set eA : A ≃* ↥((inner J ⊔ A) ⊓ centralizer ({τ} : Set (MulAut J))) :=
    MulEquiv.subgroupCongr hLA.symm with heA
  set N : Subgroup ↥((inner J ⊔ A) ⊓ centralizer ({τ} : Set (MulAut J))) :=
    (B.map resH.rangeRestrict).map eA.toMonoidHom with hN
  have hNn : N.Normal := (hB.map _ resH.rangeRestrict_surjective).map _ eA.surjective
  have hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hBab x hx y hy]
  have hbN : eA (resH.rangeRestrict b) ∈ N := ⟨_, ⟨b, hbB, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := hY τ hτ (inner J ⊔ A) le_sup_left N hNn hNab _ hbN
  have hy' : MulAut.conj y = resH b := hy
  have hyt : y * ⟨t, htJ⟩ = ⟨t, htJ⟩ * y := by
    have h1 := hfixA (resH b) ⟨b, rfl⟩
    rw [← hy', MulAut.conj_apply] at h1
    calc y * ⟨t, htJ⟩ = (y * ⟨t, htJ⟩ * y⁻¹) * y := by group
      _ = ⟨t, htJ⟩ * y := by rw [h1]
  obtain ⟨hyZ, hresy⟩ := hinner y hyt
  have hz1 : res (Subgroup.inclusion hZHZ b * (⟨_, hyZ⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hresy]
    change resH b * (MulAut.conj y)⁻¹ = 1
    rw [← hy', mul_inv_cancel]
  have hzη : ((Subgroup.inclusion hZHZ b * (⟨_, hyZ⟩)⁻¹ :
      centralizer ({MulAut.conj (⟨t, hJC htJ⟩ : C) * η} : Set (MulAut C))) : MulAut C) ∈
        zpowers η := by
    rw [← hker]
    exact ⟨_, hz1, rfl⟩
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hzη
  have hηJ : ∀ x : J, η ⟨x, hJC x.2⟩ = ⟨x, hJC x.2⟩ := by
    have hηk : η ∈ res.ker.map (centralizer ({MulAut.conj (⟨t, hJC htJ⟩ : C) * η} :
        Set (MulAut C))).subtype := by
      rw [hker]
      exact mem_zpowers η
    obtain ⟨w, hw, hwη⟩ := hηk
    intro x
    have h1 := hres w x
    rw [MonoidHom.mem_ker.1 hw, MulAut.one_apply] at h1
    have hwη' : (w : MulAut C) = η := hwη
    rw [hwη'] at h1
    exact Subtype.ext h1.symm
  have hcomm : Commute η (MulAut.conj (⟨y, hJC y.2⟩ : C)) := by
    have h1 := mulAut_mul_conj_mul_inv η (⟨y, hJC y.2⟩ : C)
    rw [hηJ y] at h1
    calc η * MulAut.conj (⟨y, hJC y.2⟩ : C) =
        (η * MulAut.conj (⟨y, hJC y.2⟩ : C) * η⁻¹) * η := by group
      _ = MulAut.conj (⟨y, hJC y.2⟩ : C) * η := by rw [h1]
  have hb' : (b : MulAut C) = η ^ m * MulAut.conj (⟨y, hJC y.2⟩ : C) := by
    rw [hm]
    change (b : MulAut C) = (b : MulAut C) * (MulAut.conj (⟨y, hJC y.2⟩ : C))⁻¹ *
      MulAut.conj (⟨y, hJC y.2⟩ : C)
    group
  have hb2 : (b : MulAut C) ^ 2 = MulAut.conj ((⟨y, hJC y.2⟩ : C) ^ 2) := by
    rw [hb', (hcomm.zpow_left m).mul_pow, map_pow, ← zpow_natCast (η ^ m), ← zpow_mul, mul_comm,
      zpow_mul, Nat.cast_ofNat, zpow_two, hη2, one_zpow, one_mul]
  exact hηI ⟨(⟨y, hJC y.2⟩ : C) ^ 2, by rw [← hb2, hb]⟩

end CFSG.SeitzReduction
