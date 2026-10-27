module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneE6OuterBasic

public section

namespace CFSG.SeitzReduction

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LieType.Chevalley (mulAut_conj_injective_of_center_eq_bot mulAut_mul_conj_mul_inv)
open CFSG.LieType.Chevalley.E6SecondGraphFull (SecondGraphFullCentralizer)
open scoped commutatorElement

theorem sq_mem_of_ne_of_iso {B : Type*} [Group B]
    (hiso : Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))
    {x y z : B} (hx : x ^ 2 ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) (hyz : y ≠ z) :
    x ^ 2 = y ∨ x ^ 2 = z ∨ x ^ 2 = y ^ 2 ∨ x ^ 2 = z ^ 2 ∨ x ^ 2 = y * z := by
  rcases hiso with hi | hi
  · obtain ⟨i⟩ := hi
    have key : ∀ x y z : Multiplicative (ZMod 4), x ^ 2 ≠ 1 → y ≠ 1 → z ≠ 1 → y ≠ z →
        x ^ 2 = y ∨ x ^ 2 = z ∨ x ^ 2 = y ^ 2 ∨ x ^ 2 = z ^ 2 ∨ x ^ 2 = y * z := by
      decide
    have h := key (i x) (i y) (i z)
    simp only [← map_pow, ← map_mul, ne_eq, MulEquiv.map_eq_one_iff,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact h hx hy hz hyz
  · obtain ⟨i⟩ := hi
    have key : ∀ x y z : Multiplicative (ZMod 2) × Multiplicative (ZMod 4), x ^ 2 ≠ 1 → y ≠ 1 →
        z ≠ 1 → y ≠ z →
        x ^ 2 = y ∨ x ^ 2 = z ∨ x ^ 2 = y ^ 2 ∨ x ^ 2 = z ^ 2 ∨ x ^ 2 = y * z := by
      set_option synthInstance.maxSize 2000 in decide
    have h := key (i x) (i y) (i z)
    simp only [← map_pow, ← map_mul, ne_eq, MulEquiv.map_eq_one_iff,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact h hx hy hz hyz

theorem mul_comm_of_mem_inf_of_sq_not_mem {Z : Type*} [Group Z] {B N : Subgroup Z}
    (hB : B.Normal) (hN : N.Normal)
    (hiso : Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))
    {b : Z} (hbB : b ∈ B) (hbN : b ^ 2 ∉ N) {s : Z} (hsB : s ∈ B) (hsN : s ∈ N) (g : Z) :
    g * s = s * g := by
  by_contra hne
  have hs'B : g * s * g⁻¹ ∈ B := hB.conj_mem s hsB g
  have hs'N : g * s * g⁻¹ ∈ N := hN.conj_mem s hsN g
  have hss' : s ≠ g * s * g⁻¹ := fun h => hne (by
    calc g * s = g * s * g⁻¹ * g := by group
      _ = s * g := by rw [← h])
  have hs1 : s ≠ 1 := fun h => hne (by rw [h, mul_one, one_mul])
  have hs'1 : g * s * g⁻¹ ≠ 1 := fun h => hs1 (by
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hb2 : (⟨b, hbB⟩ : B) ^ 2 ≠ 1 := fun h => hbN (by
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
    rw [h']
    exact one_mem N)
  have key := sq_mem_of_ne_of_iso hiso (x := ⟨b, hbB⟩) (y := ⟨s, hsB⟩) (z := ⟨_, hs'B⟩) hb2
    (fun h => hs1 (congrArg Subtype.val h)) (fun h => hs'1 (congrArg Subtype.val h))
    (fun h => hss' (congrArg Subtype.val h))
  apply hbN
  rcases key with h | h | h | h | h
  · rw [show b ^ 2 = s from congrArg Subtype.val h]
    exact hsN
  · rw [show b ^ 2 = g * s * g⁻¹ from congrArg Subtype.val h]
    exact hs'N
  · rw [show b ^ 2 = s ^ 2 from congrArg Subtype.val h]
    exact pow_mem hsN 2
  · rw [show b ^ 2 = (g * s * g⁻¹) ^ 2 from congrArg Subtype.val h]
    exact pow_mem hs'N 2
  · rw [show b ^ 2 = s * (g * s * g⁻¹) from congrArg Subtype.val h]
    exact mul_mem hsN hs'N

theorem commute_map_commutator_of_conj_mem {Y Z : Type*} [Group Y] [Group Z] (ψ : Y →* Z)
    {B : Subgroup Z} (hBab : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a) {b : Z}
    (hc : ∀ y : Y, ψ y * b * (ψ y)⁻¹ * b⁻¹ ∈ B)
    (hcomm : ∀ y y' : Y, ψ y * b * (ψ y)⁻¹ * b⁻¹ * ψ y' = ψ y' * (ψ y * b * (ψ y)⁻¹ * b⁻¹))
    (u v : Y) : ψ ⁅u, v⁆ * b = b * ψ ⁅u, v⁆ := by
  let c : Y →* B :=
    { toFun := fun y => ⟨ψ y * b * (ψ y)⁻¹ * b⁻¹, hc y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ψ (x * y) * b * (ψ (x * y))⁻¹ * b⁻¹ =
          (ψ x * b * (ψ x)⁻¹ * b⁻¹) * (ψ y * b * (ψ y)⁻¹ * b⁻¹)
        have h1 : ψ (x * y) * b * (ψ (x * y))⁻¹ * b⁻¹ =
            (ψ x * (ψ y * b * (ψ y)⁻¹ * b⁻¹) * (ψ x)⁻¹) * (ψ x * b * (ψ x)⁻¹ * b⁻¹) := by
          rw [map_mul]
          group
        have h2 : ψ x * (ψ y * b * (ψ y)⁻¹ * b⁻¹) * (ψ x)⁻¹ = ψ y * b * (ψ y)⁻¹ * b⁻¹ := by
          rw [← hcomm y x, mul_inv_cancel_right]
        rw [h1, h2]
        exact hBab _ (hc y) _ (hc x)) }
  have hcuv : c ⁅u, v⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hBab _ (c u).2 _ (c v).2)
  have h := congrArg Subtype.val hcuv
  change ψ ⁅u, v⁆ * b * (ψ ⁅u, v⁆)⁻¹ * b⁻¹ = 1 at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem sq_ne_of_commutator_rigid {G : Type*} [Group G] {C J : Subgroup G} {P t : G}
    {F : Type*} {act : F → MulAut J} (hSG : SecondGraphFullCentralizer C J P t act)
    (hP2 : P * P = 1) (hZJ : center J = ⊥) (η : MulAut C) (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hηI : η ∉ inner C) (ξ : MulAut C) (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hrig : ∀ (y : J) (φ : F), (y : G) * t = t * y →
      (∀ u v : J, (u : G) * t = t * u → (v : G) * t = t * v →
        (MulAut.conj y * act φ) ⁅u, v⁆ = ⁅u, v⁆) → MulAut.conj y * act φ ∈ inner J)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    ∀ B : Subgroup ↥(H ⊓ centralizer ({ξ} : Set (MulAut C))), B.Normal →
      (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
        Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) →
      ∀ b ∈ B, (b : MulAut C) ^ 2 ≠ η := by
  classical
  obtain ⟨htJ, hJC, η', hη', -, res, hres, hker, hrange, -, hfixt, hinner, -⟩ := hSG
  have e : η = η' := MulEquiv.ext fun g => Subtype.ext (by rw [hη', hη])
  subst e
  have hξη : ξ = MulAut.conj (⟨t, hJC htJ⟩ : C) * η := MulEquiv.ext fun g => Subtype.ext (by
    rw [hξ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη])
  subst hξη
  have hη2 : η * η = 1 := MulEquiv.ext fun g => Subtype.ext (by
    rw [MulAut.mul_apply, hη, hη, MulAut.one_apply]
    calc P * (P * (g : G) * P⁻¹) * P⁻¹ = (P * P) * g * (P * P)⁻¹ := by group
      _ = g := by rw [hP2, one_mul, inv_one, mul_one])
  set ZH := H ⊓ centralizer ({MulAut.conj (⟨t, hJC htJ⟩ : C) * η} : Set (MulAut C)) with hZH
  have hZHZ : ZH ≤ centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η} := inf_le_right
  set resH : ZH →* MulAut J := res.comp (Subgroup.inclusion hZHZ) with hresHdef
  intro B hB hiso b hbB hb
  have hBab : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := by
    rcases hiso with hi | hi
    · obtain ⟨i⟩ := hi
      exact mul_comm_of_mulEquiv i
    · obtain ⟨i⟩ := hi
      exact mul_comm_of_mulEquiv i
  set N : Subgroup ZH := Subgroup.comap ZH.subtype (inner C) with hNdef
  have hNn : N.Normal := (inner_normal C).comap _
  have hbN : b ^ 2 ∉ N := fun h => hηI (by
    rw [← hb, ← Subgroup.coe_pow]
    exact Subgroup.mem_comap.1 h)
  set CJ : Subgroup J := centralizer {(⟨t, htJ⟩ : J)} with hCJ
  have hCJt : ∀ x : CJ, (x : J) * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x := fun x =>
    mem_centralizer_singleton_iff.1 x.2
  set ψ : CJ →* ZH := ((MulAut.conj : C →* MulAut C).comp
      ((Subgroup.inclusion hJC).comp CJ.subtype)).codRestrict ZH
    (fun x => ⟨hIH ⟨_, rfl⟩, (hinner x (hCJt x)).1⟩) with hψdef
  have hψN : ∀ x : CJ, ψ x ∈ N := fun x => Subgroup.mem_comap.2 ⟨_, rfl⟩
  have hresψ : ∀ x : CJ, resH (ψ x) = MulAut.conj (x : J) := fun x => (hinner x (hCJt x)).2
  have hcB : ∀ x : CJ, ψ x * b * (ψ x)⁻¹ * b⁻¹ ∈ B := fun x =>
    mul_mem (hB.conj_mem b hbB (ψ x)) (inv_mem hbB)
  have hcN : ∀ x : CJ, ψ x * b * (ψ x)⁻¹ * b⁻¹ ∈ N := fun x => by
    have e : ψ x * b * (ψ x)⁻¹ * b⁻¹ = ψ x * (b * (ψ x)⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem (hψN x) (hNn.conj_mem _ (inv_mem (hψN x)) b)
  have hcomm : ∀ x x' : CJ,
      ψ x * b * (ψ x)⁻¹ * b⁻¹ * ψ x' = ψ x' * (ψ x * b * (ψ x)⁻¹ * b⁻¹) := fun x x' =>
    (mul_comm_of_mem_inf_of_sq_not_mem hB hNn hiso hbB hbN (hcB x) (hcN x) (ψ x')).symm
  have hfix : ∀ u v : CJ, resH b ⁅(u : J), (v : J)⁆ = ⁅(u : J), (v : J)⁆ := by
    intro u v
    have h1 := congrArg resH (commute_map_commutator_of_conj_mem ψ hBab hcB hcomm u v)
    rw [map_mul, map_mul, hresψ] at h1
    change MulAut.conj ⁅(u : J), (v : J)⁆ * resH b = resH b * MulAut.conj ⁅(u : J), (v : J)⁆ at h1
    have h3 : MulAut.conj (resH b ⁅(u : J), (v : J)⁆) = MulAut.conj ⁅(u : J), (v : J)⁆ := by
      rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact mulAut_conj_injective_of_center_eq_bot hZJ h3
  obtain ⟨y, hyt, φ, hyφ⟩ := (hrange (resH b)).1 ⟨_, rfl⟩
  have hinn : resH b ∈ inner J := by
    rw [hyφ]
    refine hrig y φ (congrArg Subtype.val hyt) fun u v hu hv => ?_
    rw [← hyφ]
    exact hfix ⟨u, mem_centralizer_singleton_iff.2 (Subtype.ext hu)⟩
      ⟨v, mem_centralizer_singleton_iff.2 (Subtype.ext hv)⟩
  obtain ⟨y', hy'⟩ := hinn
  have hy'' : MulAut.conj y' = resH b := hy'
  have hyt' : y' * ⟨t, htJ⟩ = ⟨t, htJ⟩ * y' := by
    have h1 := hfixt (resH b) ⟨_, rfl⟩
    rw [← hy'', MulAut.conj_apply] at h1
    calc y' * ⟨t, htJ⟩ = (y' * ⟨t, htJ⟩ * y'⁻¹) * y' := by group
      _ = ⟨t, htJ⟩ * y' := by rw [h1]
  obtain ⟨hyZ, hresy⟩ := hinner y' hyt'
  have hz1 : res (Subgroup.inclusion hZHZ b * (⟨_, hyZ⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hresy]
    change resH b * (MulAut.conj y')⁻¹ = 1
    rw [← hy'', mul_inv_cancel]
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
  have hcomm' : Commute η (MulAut.conj (⟨y', hJC y'.2⟩ : C)) := by
    have h1 := mulAut_mul_conj_mul_inv η (⟨y', hJC y'.2⟩ : C)
    rw [hηJ y'] at h1
    calc η * MulAut.conj (⟨y', hJC y'.2⟩ : C) =
        (η * MulAut.conj (⟨y', hJC y'.2⟩ : C) * η⁻¹) * η := by group
      _ = MulAut.conj (⟨y', hJC y'.2⟩ : C) * η := by rw [h1]
  have hb' : (b : MulAut C) = η ^ m * MulAut.conj (⟨y', hJC y'.2⟩ : C) := by
    rw [hm]
    change (b : MulAut C) = (b : MulAut C) * (MulAut.conj (⟨y', hJC y'.2⟩ : C))⁻¹ *
      MulAut.conj (⟨y', hJC y'.2⟩ : C)
    group
  have hb2 : (b : MulAut C) ^ 2 = MulAut.conj ((⟨y', hJC y'.2⟩ : C) ^ 2) := by
    rw [hb', (hcomm'.zpow_left m).mul_pow, map_pow, ← zpow_natCast (η ^ m), ← zpow_mul, mul_comm,
      zpow_mul, Nat.cast_ofNat, zpow_two, hη2, one_zpow, one_mul]
  exact hηI ⟨(⟨y', hJC y'.2⟩ : C) ^ 2, by rw [← hb2, hb]⟩

theorem noNormalZ4OrZ2xZ4_inf_centralizer_xi_of_sq_ne {G : Type*} [Group G] {C J : Subgroup G}
    {P t : G} {F : Type*} {act : F → MulAut J} (hSG : SecondGraphFullCentralizer C J P t act)
    (hP2 : P * P = 1) (hZJ : center J = ⊥) (η : MulAut C) (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (ξ : MulAut C) (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hF4 : ∀ τJ : MulAut J, (∀ x : J, (τJ x : G) = t * x * t⁻¹) →
      ∀ L : Subgroup (MulAut J), inner J ≤ L →
        NoNormalZ4OrZ2xZ4 ↥(L ⊓ centralizer ({τJ} : Set (MulAut J))))
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H)
    (hsq : ∀ B : Subgroup ↥(H ⊓ centralizer ({ξ} : Set (MulAut C))), B.Normal →
      (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
        Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) →
      ∀ b ∈ B, (b : MulAut C) ^ 2 ≠ η) :
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
  have hbη := hsq B hB hiso b hbB
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

theorem noNormalZ4OrZ2xZ4_inf_centralizer_xi_of_rigid {G : Type*} [Group G] {C J : Subgroup G}
    {P t : G} {F : Type*} {act : F → MulAut J} (hSG : SecondGraphFullCentralizer C J P t act)
    (hP2 : P * P = 1) (hZJ : center J = ⊥) (η : MulAut C) (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hηI : η ∉ inner C) (ξ : MulAut C) (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hF4 : ∀ τJ : MulAut J, (∀ x : J, (τJ x : G) = t * x * t⁻¹) →
      ∀ L : Subgroup (MulAut J), inner J ≤ L →
        NoNormalZ4OrZ2xZ4 ↥(L ⊓ centralizer ({τJ} : Set (MulAut J))))
    (hrig : ∀ (y : J) (φ : F), (y : G) * t = t * y →
      (∀ u v : J, (u : G) * t = t * u → (v : G) * t = t * v →
        (MulAut.conj y * act φ) ⁅u, v⁆ = ⁅u, v⁆) → MulAut.conj y * act φ ∈ inner J)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({ξ} : Set (MulAut C))) :=
  noNormalZ4OrZ2xZ4_inf_centralizer_xi_of_sq_ne hSG hP2 hZJ η hη ξ hξ hF4 H hIH
    (sq_ne_of_commutator_rigid hSG hP2 hZJ η hη hηI ξ hξ hrig H hIH)

end CFSG.SeitzReduction
