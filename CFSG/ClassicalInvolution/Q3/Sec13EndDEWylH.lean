module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylP
public import CFSG.ClassicalInvolution.Q3.Sec13RecogS
public import CFSG.ClassicalInvolution.Q3.Sec13RecogQ8
public import CFSG.ClassicalInvolution.Q3.Sec13EndAGLFin
public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLC

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

@[expose] def edgeCoset {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) (f : G → ZMod 2) :
    Set G :=
  {a | a ∈ dewA S b ∧ dewFun S a = f}

@[expose] def edgeSet {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) (f : G → ZMod 2) :
    Set G :=
  {e | e ∈ edgeCoset S b f ∧ ∃ K ∈ Ω, e ∈ dewDelta K (S.shift b K)}

@[expose] def IsEdge {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) (X Y : Set (Subgroup G))
    (e : G) : Prop :=
  e ∈ edgeCoset S b (dewEps X Y) ∧
    ∀ x ∈ zGroup Ω, x ≠ 1 → dewEps X Y x = 0 → ∀ M ∈ dew1V Ω x, M ∉ X →
      e ∈ dewDelta M (S.shift b M)

open Classical in
@[expose] noncomputable def dewEdge {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2)
    (X Y : Set (Subgroup G)) : G :=
  if hE : ∃ e, IsEdge S b X Y e then hE.choose else 1

private theorem dewh_even_mem_closure (T : Set (Fin 8)) (f : Multiplicative (Fin 8 → ZMod 2))
    (hf : ∑ i, f.toAdd i = 0) (hT : ∀ i, i ∉ T → f.toAdd i = 0) :
    f ∈ Subgroup.closure {x | ∃ i ∈ T, ∃ j ∈ T,
      x = Multiplicative.ofAdd (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2))} := by
  by_cases h0 : f.toAdd = 0
  · have : f = 1 := Multiplicative.toAdd.injective h0
    rw [this]
    exact Subgroup.one_mem _
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀, f.toAdd i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 (funext hcon)
    have hi₀T : i₀ ∈ T := by
      by_contra hn
      exact hi₀ (hT i₀ hn)
    have key : f.toAdd =
        ∑ j, f.toAdd j • (Pi.single i₀ (1 : ZMod 2) + Pi.single j (1 : ZMod 2)) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        ← Finset.sum_mul, hf]
    have hprod : f = ∏ j, Multiplicative.ofAdd
        (f.toAdd j • (Pi.single i₀ (1 : ZMod 2) + Pi.single j (1 : ZMod 2))) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      exact key
    rw [hprod]
    refine Subgroup.prod_mem _ (fun j _ => ?_)
    rcases zmod2_cases (f.toAdd j) with hj | hj
    · rw [hj, zero_smul]
      exact Subgroup.one_mem _
    · rw [hj, one_smul]
      have hjT : j ∈ T := by
        by_contra hn
        have := hT j hn
        rw [hj] at this
        exact one_ne_zero this
      exact Subgroup.subset_closure ⟨i₀, hi₀T, j, hjT, rfl⟩


private abbrev dewh_pv (i j : Fin 8) : Multiplicative (Fin 8 → ZMod 2) :=
  Multiplicative.ofAdd (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2))

private def dewh_even : Subgroup (Multiplicative (Fin 8 → ZMod 2)) where
  carrier := {f | ∑ i, f.toAdd i = 0}
  mul_mem' {f g} hf hg := by
    change ∑ i, f.toAdd i = 0 at hf
    change ∑ i, g.toAdd i = 0 at hg
    change ∑ i, (f.toAdd i + g.toAdd i) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  one_mem' := Finset.sum_const_zero
  inv_mem' {f} hf := by
    change ∑ i, f.toAdd i = 0 at hf
    change ∑ i, -f.toAdd i = 0
    rw [Finset.sum_neg_distrib, hf, neg_zero]

private theorem dewh_card_even : Nat.card dewh_even = 128 := by
  have e : dewh_even ≃ {f : Fin 8 → ZMod 2 // ∑ i, f i = 0} :=
    { toFun := fun f => ⟨f.1.toAdd, f.2⟩
      invFun := fun f => ⟨Multiplicative.ofAdd f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

private def dewh_supp (T : Set (Fin 8)) : Subgroup (Multiplicative (Fin 8 → ZMod 2)) where
  carrier := {f | ∑ i, f.toAdd i = 0 ∧ ∀ i, i ∉ T → f.toAdd i = 0}
  mul_mem' {f g} hf hg := by
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hg1, hg2⟩ := hg
    refine ⟨?_, fun i hi => ?_⟩
    · change ∑ i, (f.toAdd i + g.toAdd i) = 0
      rw [Finset.sum_add_distrib, hf1, hg1, add_zero]
    · change f.toAdd i + g.toAdd i = 0
      rw [hf2 i hi, hg2 i hi, add_zero]
  one_mem' := ⟨Finset.sum_const_zero, fun _ _ => rfl⟩
  inv_mem' {f} hf := by
    obtain ⟨hf1, hf2⟩ := hf
    refine ⟨?_, fun i hi => ?_⟩
    · change ∑ i, -f.toAdd i = 0
      rw [Finset.sum_neg_distrib, hf1, neg_zero]
    · change -f.toAdd i = 0
      rw [hf2 i hi, neg_zero]

private theorem dewh_pv_even (i j : Fin 8) : dewh_pv i j ∈ dewh_even := by
  change ∑ k, (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin 8 → ZMod 2) k = 0
  simp [Finset.sum_add_distrib, Pi.single_apply]
  decide


private theorem dewh_vecMap_conj {M : Type*} [Group M] (β : Multiplicative (Fin 8 → ZMod 2) →* M)
    (Y : Fin 8 → Fin 8 → M) (hβ : ∀ i j, β (dewh_pv i j) = Y i j) (g : M) (s : Equiv.Perm (Fin 8))
    (hg : ∀ i j, g * Y i j * g⁻¹ = Y (s i) (s j)) (f : Multiplicative (Fin 8 → ZMod 2))
    (hf : ∑ i, f.toAdd i = 0) :
    g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd (s.symm i)) := by
  let π : Multiplicative (Fin 8 → ZMod 2) →* Multiplicative (Fin 8 → ZMod 2) :=
    { toFun := fun f => Multiplicative.ofAdd fun i => f.toAdd (s.symm i)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let lhs : Multiplicative (Fin 8 → ZMod 2) →* M := (MulAut.conj g).toMonoidHom.comp β
  let rhs : Multiplicative (Fin 8 → ZMod 2) →* M := β.comp π
  have hle : Subgroup.closure {x | ∃ i ∈ (Set.univ : Set (Fin 8)), ∃ j ∈ (Set.univ : Set (Fin 8)),
      x = dewh_pv i j} ≤ MonoidHom.eqLocus lhs rhs := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, -, j, -, rfl⟩
    show lhs (dewh_pv i j) = rhs (dewh_pv i j)
    have h1 : lhs (dewh_pv i j) = g * Y i j * g⁻¹ := by
      show g * β (dewh_pv i j) * g⁻¹ = _
      rw [hβ]
    have h2 : rhs (dewh_pv i j) = Y (s i) (s j) := by
      show β (Multiplicative.ofAdd fun k =>
        (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin 8 → ZMod 2) (s.symm k)) = _
      rw [← hβ]
      congr 1
      apply Multiplicative.toAdd.injective
      funext k
      simp [Pi.single_apply, Equiv.symm_apply_eq]
    rw [h1, h2, hg]
  exact hle (dewh_even_mem_closure Set.univ f hf (fun i hi => absurd (Set.mem_univ i) hi))


private theorem dewh_exists_hom_pi {E : Type*} [CommGroup E] (hE : ∀ x : E, x * x = 1)
    (c : Fin 8 → E) :
    ∃ β : Multiplicative (Fin 8 → ZMod 2) →* E, ∀ i j, β (dewh_pv i j) = c i * c j := by
  classical
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    exact Additive.toMul.injective (hE (Additive.toMul x)))
  let a : Fin 8 → Additive E := fun j => Additive.ofMul (c j)
  let β₀ : (Fin 8 → ZMod 2) →+ Additive E :=
    { toFun := fun f => ∑ j, f j • a j
      map_zero' := by simp
      map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib] }
  have hβ₀e : ∀ j, β₀ (Pi.single j 1) = a j := by
    intro j
    simp [β₀, Pi.single_apply, ite_smul]
  refine ⟨{ toFun := fun f => Additive.toMul (β₀ f.toAdd)
            map_one' := by simp
            map_mul' := fun f g => by simp }, fun i j => ?_⟩
  show Additive.toMul (β₀ (Pi.single i 1 + Pi.single j 1)) = c i * c j
  rw [β₀.map_add, hβ₀e, hβ₀e]
  rfl

@[instance_reducible]
private def dewh_commGroup {M : Type*} [Group M] (A : Subgroup M)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : CommGroup ↥A :=
  { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hAc a a.2 b b.2) }

private theorem dewh_vecMap {M : Type*} [Group M] {A : Subgroup M}
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAcard : Nat.card A = 64) (Y : Fin 8 → Fin 8 → M) (hYA : ∀ i j, Y i j ∈ A)
    (hYself : ∀ i, Y i i = 1) (hYcyc : ∀ i j k, Y i j * Y j k = Y i k)
    (hYprod : Y 0 1 * Y 0 2 * Y 0 3 * Y 0 4 * Y 0 5 * Y 0 6 * Y 0 7 = 1)
    (hYgen : Subgroup.closure {x | ∃ i j, x = Y i j} = A) :
    ∃ β : Multiplicative (Fin 8 → ZMod 2) →* M, (∀ i j, β (dewh_pv i j) = Y i j) ∧
      (∀ g : M, g ∈ A ↔ ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g) ∧
      (∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
        (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)) ∧
      (∀ (T : Set (Fin 8)) (q : M), q ∈ Subgroup.closure {x | ∃ i ∈ T, ∃ j ∈ T, x = Y i j} ↔
        ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧
          (∀ i, i ∉ T → f.toAdd i = 0) ∧ β f = q) := by
  classical
  have hYform : ∀ i j, Y 0 i * Y 0 j = Y i j := by
    intro i j
    have h1 := hYcyc 0 i j
    calc Y 0 i * Y 0 j = Y 0 i * (Y 0 i * Y i j) := by rw [h1]
      _ = (Y 0 i * Y 0 i) * Y i j := by rw [mul_assoc]
      _ = Y i j := by rw [hA2 _ (hYA 0 i), one_mul]
  obtain ⟨β', hβ'⟩ := @dewh_exists_hom_pi ↥A (dewh_commGroup A hAc)
    (fun x => Subtype.ext (hA2 _ x.2)) (fun j => ⟨Y 0 j, hYA 0 j⟩)
  let β : Multiplicative (Fin 8 → ZMod 2) →* M := A.subtype.comp β'
  have hβpair : ∀ i j, β (dewh_pv i j) = Y i j := by
    intro i j
    have h1 := congrArg Subtype.val (hβ' i j)
    exact h1.trans (hYform i j)
  have hβA : ∀ f, β f ∈ A := fun f => (β' f).2
  have hsurj : ∀ g ∈ A, ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g := by
    intro g hg
    rw [← hYgen] at hg
    have hle : Subgroup.closure {x | ∃ i j, x = Y i j} ≤ Subgroup.map β dewh_even := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, j, rfl⟩
      exact ⟨dewh_pv i j, dewh_pv_even i j, hβpair i j⟩
    obtain ⟨f, hfE, hfg⟩ := hle hg
    exact ⟨f, hfE, hfg⟩
  have hπeven : (Multiplicative.ofAdd fun _ => (1 : ZMod 2) :
      Multiplicative (Fin 8 → ZMod 2)) ∈ dewh_even := by
    show ∑ _i : Fin 8, (1 : ZMod 2) = 0
    decide
  have hπ : β (Multiplicative.ofAdd fun _ => (1 : ZMod 2)) = 1 := by
    have hvec : (Multiplicative.ofAdd fun _ => (1 : ZMod 2) : Multiplicative (Fin 8 → ZMod 2)) =
        dewh_pv 0 1 * dewh_pv 2 3 * dewh_pv 4 5 * dewh_pv 6 7 := by
      apply Multiplicative.toAdd.injective
      decide +kernel
    rw [hvec, map_mul, map_mul, map_mul, hβpair, hβpair, hβpair, hβpair, ← hYform 2 3,
      ← hYform 4 5, ← hYform 6 7]
    calc Y 0 1 * (Y 0 2 * Y 0 3) * (Y 0 4 * Y 0 5) * (Y 0 6 * Y 0 7)
        = Y 0 1 * Y 0 2 * Y 0 3 * Y 0 4 * Y 0 5 * Y 0 6 * Y 0 7 := by simp only [mul_assoc]
      _ = 1 := hYprod
  have hker : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1) := by
    intro f hf
    constructor
    · intro hβf
      let φ : dewh_even →* ↥A := β'.comp dewh_even.subtype
      have hφsurj : Function.Surjective φ := by
        intro x
        obtain ⟨f, hf, hfx⟩ := hsurj x x.2
        exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
      have hcard := Subgroup.card_ker_mul_card_of_surjective hφsurj
      rw [hAcard, dewh_card_even] at hcard
      have hk2 : Nat.card φ.ker = 2 := by omega
      obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : φ.ker)).mp hk2
      let kf : φ.ker := ⟨⟨f, hf⟩, Subtype.ext hβf⟩
      let kπ : φ.ker := ⟨⟨Multiplicative.ofAdd fun _ => (1 : ZMod 2), hπeven⟩, Subtype.ext hπ⟩
      have hkπ : kπ ≠ 1 := by
        intro h1
        have h2 : (Multiplicative.ofAdd fun _ => (1 : ZMod 2) :
            Multiplicative (Fin 8 → ZMod 2)) = 1 := congrArg (fun x : φ.ker => x.1.1) h1
        have h3 := congrFun (congrArg Multiplicative.toAdd h2) 0
        exact one_ne_zero h3
      by_cases hkf : kf = 1
      · left
        have h2 : f = 1 := congrArg (fun x : φ.ker => x.1.1) hkf
        rw [h2]
        rfl
      · right
        have h3 : kf = kπ := (huniq kf hkf).trans (huniq kπ hkπ).symm
        have h4 : f = Multiplicative.ofAdd fun _ => (1 : ZMod 2) :=
          congrArg (fun x : φ.ker => x.1.1) h3
        rw [h4]
        rfl
    · rintro (h0 | h1)
      · have : f = 1 := Multiplicative.toAdd.injective h0
        rw [this, map_one]
      · have : f = Multiplicative.ofAdd fun _ => (1 : ZMod 2) := Multiplicative.toAdd.injective h1
        rw [this]
        exact hπ
  have hT : ∀ (T : Set (Fin 8)) (q : M), q ∈ Subgroup.closure {x | ∃ i ∈ T, ∃ j ∈ T, x = Y i j} ↔
      ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧
        (∀ i, i ∉ T → f.toAdd i = 0) ∧ β f = q := by
    intro T q
    constructor
    · intro hq
      have hle : Subgroup.closure {x | ∃ i ∈ T, ∃ j ∈ T, x = Y i j} ≤
          Subgroup.map β (dewh_supp T) := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, hi, j, hj, rfl⟩
        refine ⟨dewh_pv i j, ⟨dewh_pv_even i j, fun k hk => ?_⟩, hβpair i j⟩
        have hki : k ≠ i := fun e => hk (e ▸ hi)
        have hkj : k ≠ j := fun e => hk (e ▸ hj)
        simp [dewh_pv, Pi.single_apply, hki, hkj]
      obtain ⟨f, ⟨hf, hfT⟩, hfq⟩ := hle hq
      exact ⟨f, hf, hfT, hfq⟩
    · rintro ⟨f, hf, hfT, rfl⟩
      have h1 := dewh_even_mem_closure T f hf hfT
      have h2 : β f ∈ Subgroup.map β (Subgroup.closure
          {x | ∃ i ∈ T, ∃ j ∈ T, x = dewh_pv i j}) := Subgroup.mem_map_of_mem β h1
      rw [MonoidHom.map_closure] at h2
      refine Subgroup.closure_mono ?_ h2
      rintro _ ⟨_, ⟨i, hi, j, hj, rfl⟩, rfl⟩
      exact ⟨i, hi, j, hj, hβpair i j⟩
  exact ⟨β, hβpair, fun g => ⟨hsurj g, fun ⟨f, _, hf⟩ => hf ▸ hβA f⟩, hker, hT⟩

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

private theorem dewh1_smul_inj : ∀ b : Lab2, b ≠ 0 → ∀ c c' : ZMod 2, c • b = c' • b → c = c' := by
  decide

private theorem dewh1_zpowers_invol {N : Subgroup G} {x g : G} (hN : IsUniqueInvolution N x)
    (hg : g ∈ Subgroup.zpowers x) : g = 1 ∨ g = x := by
  have hsq : g * g = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← (Commute.refl x).mul_zpow k, hN.sq, one_zpow]
  exact hN.unique g ((Subgroup.zpowers_le.mpr hN.mem) hg) hsq

private theorem dewh1_shift_mem_dew1V (S : TwinShift Ω) {N : Subgroup G} {x : G}
    (hN : N ∈ dew1V Ω x) (m : Lab2) : S.shift m N ∈ dew1V Ω x := by
  rw [dew1V_eq_twinSet hN.1 hN.2]
  exact S.shift_mem m N hN.1

private theorem dewh1_twins (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {N : Subgroup G} {x : G}
    (hN : N ∈ dew1V Ω x) : DewTwins Ω N (S.shift b N) x := by
  have hs := dewh1_shift_mem_dew1V h S hN b
  refine ⟨hN.1, hs.1, hN.2, hs.2, ?_⟩
  intro hNs
  exact hb (S.shift_free b N hN.1 hNs.symm)

private theorem dewh1_shift_eq_of_mem (S : TwinShift Ω) {x : G} {M : Subgroup G}
    (hM : M ∈ dew1V Ω x) {N : Subgroup G} (hN : N ∈ dew1V Ω x) :
    ∃ m : Lab2, N = S.shift m M := by
  have hinj : Function.Injective (fun m : Lab2 => S.shift m M) :=
    fun m m' hmm => S.shift_injective hM.1 hmm
  have hT : ((fun m : Lab2 => S.shift m M) '' Set.univ).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp [Nat.card_prod, ZMod.card]
  have hsub : (fun m : Lab2 => S.shift m M) '' Set.univ ⊆ dew1V Ω x := by
    rintro _ ⟨m, -, rfl⟩
    exact dewh1_shift_mem_dew1V h S hM m
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [h.ncard_dew1V hM.1 hM.2, hT])
  have hNm : N ∈ (fun m : Lab2 => S.shift m M) '' Set.univ := by
    rw [heq]
    exact hN
  obtain ⟨m, -, hm⟩ := hNm
  exact ⟨m, hm.symm⟩

private theorem dewh1_q8_rel {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    z * i = i * z ∧ z * j = j * z ∧ j * (z * i) = i * j := by
  have hzi : z * i = i * z := by
    rw [← hQ.sq_i]
    group
  have hzj : z * j = j * z := by
    rw [← hQ.sq_j]
    group
  have h2 : j * (z * i) = i * j := by
    calc j * (z * i) = j * z * i := by group
      _ = j * (j * j) * i := by rw [hQ.sq_j]
      _ = (j * j) * (j * i) := by group
      _ = z * (z * (i * j)) := by rw [hQ.sq_j, hQ.comm]
      _ = (z * z) * (i * j) := by group
      _ = i * j := by rw [hQ.inv.sq, one_mul]
  exact ⟨hzi, hzj, h2⟩

private theorem dewh1_q8_center {N : Subgroup G} {x k : G} (hN : N ∈ Ω)
    (hx : IsUniqueInvolution N x) (hk : k ∈ N) (hc : ∀ y ∈ N, y * k = k * y) :
    k = 1 ∨ k = x := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hx (h.isQuatSub_of_mem hN) (h.card N hN)
  have hQ : Q8Data N x i j := ⟨hx, hi, hj, hii, hjj, hji, hNF⟩
  obtain ⟨hzi, -, h2⟩ := h.dewh1_q8_rel hQ
  have hzz := hQ.inv.sq
  have hnot : ∀ w : G, x * w = w → False := fun w hw =>
    hQ.inv.ne_one (mul_right_cancel (hw.trans (one_mul w).symm))
  have e3 : i * (i * j) = x * j := by
    rw [← mul_assoc, hQ.sq_i]
  have h5 : i * j * i = j := by
    calc i * j * i = i * (j * i) := by group
      _ = i * (x * (i * j)) := by rw [hQ.comm]
      _ = x * (i * (i * j)) := by rw [← mul_assoc, ← hzi, mul_assoc]
      _ = x * (x * j) := by rw [e3]
      _ = j := by rw [← mul_assoc, hzz, one_mul]
  have e4 : i * (x * (i * j)) = x * (x * j) := by
    rw [← mul_assoc, ← hzi, mul_assoc, e3]
  have e5 : x * (i * j) * i = x * j := by
    rw [mul_assoc, h5]
  have e6a : i * (x * j) = x * (i * j) := by
    rw [← mul_assoc i x j, ← hzi, mul_assoc x i j]
  have e6b : x * j * i = i * j := by
    rw [mul_assoc x j i, hQ.comm, ← mul_assoc x x (i * j), hzz, one_mul]
  rcases hQ.nf k hk with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have h6 := hc j hQ.mem_j
    rw [h1, hQ.comm] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc j hQ.mem_j
    rw [h1, h2, mul_assoc x i j] at h6
    exact hnot _ h6.symm
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, hQ.comm] at h6
    exact hnot _ h6.symm
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, e6a, e6b] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, h5, e3] at h6
    exact hnot _ h6
  · exfalso
    have h6 := hc i hQ.mem_i
    rw [h1, e4, e5] at h6
    have h7 : x * j = j := by
      calc x * j = x * (x * j) := h6.symm
        _ = (x * x) * j := by group
        _ = j := by rw [hzz, one_mul]
    exact hnot _ h7

private theorem dewh1_ker_ncard {f : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) :
    ({d | d ∈ zGroup Ω ∧ f d = 0} : Set G).ncard = 4 := by
  obtain ⟨hF1, hFo, hFa⟩ := hf
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨g₀, hg₀D, hg₀⟩ : ∃ g₀ ∈ zGroup Ω, f g₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    funext d
    by_cases hd : d ∈ zGroup Ω
    · exact hcon d hd
    · exact hFo d hd
  have hg₀1 : f g₀ = 1 := (hcase _).resolve_left hg₀
  have hinv : f g₀⁻¹ = 1 := by
    have h1 := hFa g₀ hg₀D g₀⁻¹ ((zGroup Ω).inv_mem hg₀D)
    rw [mul_inv_cancel, hF1, hg₀1] at h1
    have h2 : ∀ a : ZMod 2, 0 = 1 + a → a = 1 := by decide
    exact h2 _ h1
  have hD : ((zGroup Ω : Subgroup G) : Set G) =
      {d | d ∈ zGroup Ω ∧ f d = 0} ∪ {d | d ∈ zGroup Ω ∧ f d = 1} := by
    ext d
    simp only [SetLike.mem_coe, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hd
      rcases hcase (f d) with h0 | h1
      · exact Or.inl ⟨hd, h0⟩
      · exact Or.inr ⟨hd, h1⟩
    · rintro (⟨hd, -⟩ | ⟨hd, -⟩) <;> exact hd
  have hdisj : Disjoint {d | d ∈ zGroup Ω ∧ f d = 0} {d | d ∈ zGroup Ω ∧ f d = 1} := by
    rw [Set.disjoint_left]
    rintro d ⟨-, h0⟩ ⟨-, h1⟩
    rw [h0] at h1
    exact zero_ne_one h1
  have himg : {d | d ∈ zGroup Ω ∧ f d = 1} =
      (fun d => g₀ * d) '' {d | d ∈ zGroup Ω ∧ f d = 0} := by
    ext d
    constructor
    · rintro ⟨hd, hd1⟩
      refine ⟨g₀⁻¹ * d, ⟨(zGroup Ω).mul_mem ((zGroup Ω).inv_mem hg₀D) hd, ?_⟩, by group⟩
      rw [hFa g₀⁻¹ ((zGroup Ω).inv_mem hg₀D) d hd, hinv, hd1]
      decide
    · rintro ⟨d', ⟨hd', hf'⟩, rfl⟩
      refine ⟨(zGroup Ω).mul_mem hg₀D hd', ?_⟩
      rw [hFa g₀ hg₀D d' hd', hg₀1, hf', add_zero]
  have hcard : ((zGroup Ω : Subgroup G) : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_zGroup
  rw [hD, Set.ncard_union_eq hdisj, himg, Set.ncard_image_of_injective _ (mul_right_injective g₀)]
    at hcard
  omega

private theorem dewh1_ker_eq {f : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0)
    {v c : G} (hv : v ∈ zGroup Ω) (hv1 : v ≠ 1) (hfv : f v = 0)
    (hc : c ∈ zGroup Ω) (hc1 : c ≠ 1) (hcv : c ≠ v) (hfc : f c = 0) (d : G) :
    (d ∈ zGroup Ω ∧ f d = 0) ↔ (d = 1 ∨ d = v ∨ d = c ∨ d = v * c) := by
  have hF1 : f 1 = 0 := hf.1
  have hFo : ∀ x, x ∉ zGroup Ω → f x = 0 := hf.2.1
  have hFa : ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, f (x * y) = f x + f y := hf.2.2
  have hvv : v * v = 1 := h.zGroup_mul_self v hv
  have hset : ({1, v, c, v * c} : Set G) = {d | d ∈ zGroup Ω ∧ f d = 0} := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro d hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨(zGroup Ω).one_mem, hF1⟩
      · exact ⟨hv, hfv⟩
      · exact ⟨hc, hfc⟩
      · exact ⟨(zGroup Ω).mul_mem hv hc, by rw [hFa v hv c hc, hfv, hfc, add_zero]⟩
    · rw [h.dewh1_ker_ncard hf hf0]
      have hn1 : (1 : G) ∉ ({v, c, v * c} : Set G) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨fun h1 => hv1 h1.symm, fun h1 => hc1 h1.symm, fun h1 => hcv ?_⟩
        calc c = v * v * c := by rw [hvv, one_mul]
          _ = v * (v * c) := by group
          _ = v := by rw [← h1, mul_one]
      have hn2 : v ∉ ({c, v * c} : Set G) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h1 => hcv h1.symm, fun h1 => hc1 (mul_left_cancel ((mul_one v).trans h1)).symm⟩
      have hn3 : c ≠ v * c := fun h1 => hv1 (mul_right_cancel ((one_mul c).trans h1)).symm
      rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2, Set.ncard_pair hn3]
  have key := Set.ext_iff.mp hset d
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at key
  exact key.symm

private theorem dewh1_conj_inv {f : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0)
    {x u y : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) (hfx : f x = 0)
    (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hfu : f u = 0) (hxu : x ≠ u)
    (hy : y ^ 3 = 1) (hyx : y * x * y⁻¹ = u) (hyu : y * u * y⁻¹ = x * u) (g : G) :
    f (y * g * y⁻¹) = f g := by
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy
  have hF1 : f 1 = 0 := hf.1
  have hFo : ∀ z, z ∉ zGroup Ω → f z = 0 := hf.2.1
  have hFa : ∀ z ∈ zGroup Ω, ∀ w ∈ zGroup Ω, f (z * w) = f z + f w := hf.2.2
  have hK := h.dewh1_ker_eq hf hf0 hx hx1 hfx hu hu1 (Ne.symm hxu) hfu
  have hyD : ∀ z ∈ zGroup Ω, y * z * y⁻¹ ∈ zGroup Ω := fun z hz =>
    h.zGroup_normal.conj_mem z hz y
  have hconjK : ∀ d, d ∈ zGroup Ω → f d = 0 →
      y * d * y⁻¹ ∈ zGroup Ω ∧ f (y * d * y⁻¹) = 0 := by
    intro d hd hfd
    rcases (hK d).mp ⟨hd, hfd⟩ with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [mul_one, mul_inv_cancel]
      exact ⟨(zGroup Ω).one_mem, hF1⟩
    · rw [hyx]
      exact ⟨hu, hfu⟩
    · rw [hyu]
      exact ⟨(zGroup Ω).mul_mem hx hu, by rw [hFa x hx u hu, hfx, hfu, add_zero]⟩
    · have e : y * (x * u) * y⁻¹ = x := by
        rw [show y * (x * u) * y⁻¹ = (y * x * y⁻¹) * (y * u * y⁻¹) by group, hyx, hyu,
          ← mul_assoc, h.zGroup_comm u hu x hx, mul_assoc, h.zGroup_mul_self u hu, mul_one]
      rw [e]
      exact ⟨hx, hfx⟩
  have hinvD : ∀ d, d ∈ zGroup Ω → f d ≠ 0 → f (y * d * y⁻¹) ≠ 0 := by
    intro d hd hfd h0
    obtain ⟨hD2, hf2⟩ := hconjK _ (hyD d hd) h0
    obtain ⟨-, hf3⟩ := hconjK _ hD2 hf2
    have hcube : y * (y * (y * d * y⁻¹) * y⁻¹) * y⁻¹ = d := by
      have e : y * (y * (y * d * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * d * (y * y * y)⁻¹ := by
        group
      rw [e, hy3']
      simp
    rw [hcube] at hf3
    exact hfd hf3
  by_cases hgD : g ∈ zGroup Ω
  · rcases hcase (f g) with h0 | h1
    · rw [h0]
      exact (hconjK g hgD h0).2
    · have hne := hinvD g hgD (by rw [h1]; decide)
      rw [h1]
      rcases hcase (f (y * g * y⁻¹)) with h2 | h2
      · exact absurd h2 hne
      · exact h2
  · rw [hFo g hgD]
    have hnD : y * g * y⁻¹ ∉ zGroup Ω := by
      intro hm
      apply hgD
      have e : y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g := by group
      have := h.zGroup_normal.conj_mem _ hm y⁻¹
      rw [e] at this
      exact this
    exact hFo _ hnD

private theorem dewh1_cube_ker {f : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω) {y a : G}
    (hy : y ^ 3 = 1) (hinv : ∀ g, f (y * g * y⁻¹) = f g)
    (hc : a⁻¹ * (y * a * y⁻¹) ∈ zGroup Ω) : f (a⁻¹ * (y * a * y⁻¹)) = 0 := by
  have hcase : ∀ c : ZMod 2, c + c + c = 0 → c = 0 := by decide
  have hF1 : f 1 = 0 := hf.1
  have hFa : ∀ z ∈ zGroup Ω, ∀ w ∈ zGroup Ω, f (z * w) = f z + f w := hf.2.2
  have hyD : ∀ z ∈ zGroup Ω, y * z * y⁻¹ ∈ zGroup Ω := fun z hz =>
    h.zGroup_normal.conj_mem z hz y
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy
  have hQ : y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = a := by
    have e : y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * a * (y * y * y)⁻¹ := by
      group
    rw [e, hy3']
    simp
  have hc1 : y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹ ∈ zGroup Ω := hyD _ hc
  have hc2 : y * (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) * y⁻¹ ∈ zGroup Ω := hyD _ hc1
  have hf1 : f (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) = f (a⁻¹ * (y * a * y⁻¹)) := hinv _
  have hf2 : f (y * (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) * y⁻¹) = f (a⁻¹ * (y * a * y⁻¹)) := by
    rw [hinv, hf1]
  have e1 : y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹ = (y * a * y⁻¹)⁻¹ * (y * (y * a * y⁻¹) * y⁻¹) := by
    simp only [mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, mul_one, one_mul, inv_mul_cancel, mul_inv_cancel]
  have e2 : y * (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) * y⁻¹ =
      (y * (y * a * y⁻¹) * y⁻¹)⁻¹ * a := by
    have i1 : y * (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) * y⁻¹ =
        (y * (y * a * y⁻¹) * y⁻¹)⁻¹ * (y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹) := by
      rw [e1]
      simp only [mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, mul_one, one_mul, inv_mul_cancel, mul_inv_cancel]
    rw [i1, hQ]
  have hprod : (a⁻¹ * (y * a * y⁻¹)) * (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) *
      (y * (y * (a⁻¹ * (y * a * y⁻¹)) * y⁻¹) * y⁻¹) = 1 := by
    rw [e2, e1]
    simp only [mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, mul_one, one_mul, inv_mul_cancel, mul_inv_cancel]
  have hsum := hFa _ ((zGroup Ω).mul_mem hc hc1) _ hc2
  have hsum' := hFa _ hc _ hc1
  rw [hprod, hF1, hsum', hf1, hf2] at hsum
  exact hcase _ hsum.symm

private theorem dewh1_dewFun_conj (S : TwinShift Ω) {b : Lab2} {f : G → ZMod 2} {a g : G}
    (ha : a ∈ dewA S b) (hfa : dewFun S a = f) (hg : ∀ z, f (g * z * g⁻¹) = f z) :
    dewFun S (g * a * g⁻¹) = f := by
  funext z
  have hl := h.lam_conj S ha.1 g (g⁻¹ * z * g)
  rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hl
  have h3 := hg (g⁻¹ * z * g)
  rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h3
  have h2 : dewFun S a (g⁻¹ * z * g) = f (g⁻¹ * z * g) := congrFun hfa _
  unfold dewFun at h2 ⊢
  rw [hl]
  rw [h2] at *
  exact h3.symm

private theorem dewh1_coset (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {e a : G}
    (he : e ∈ dewA S b) (ha : a ∈ dewA S b) (hea : dewFun S e = dewFun S a) :
    e⁻¹ * a ∈ zGroup Ω := by
  refine (h.lam_eq_zero_iff S ((pCore 2 G).mul_mem ((pCore 2 G).inv_mem he.1) ha.1)).mp ?_
  intro z
  rw [h.lam_mul S ((pCore 2 G).inv_mem he.1) ha.1 z, h.lam_inv S he.1 z,
    h.lam_eq_smul_dewFun S hb he z, h.lam_eq_smul_dewFun S hb ha z, hea]
  exact lab2_add_self _

private theorem dewh1_dewFun_mul (S : TwinShift Ω) {b : Lab2} {e c : G}
    (he : e ∈ dewA S b) (hc : c ∈ zGroup Ω) : dewFun S (e * c) = dewFun S e := by
  funext z
  have hl : S.lam (e * c) z = S.lam e z := by
    rw [h.lam_mul S he.1 (h.zGroup_le_pCore hc) z, h.lam_of_mem_zGroup S hc z, add_zero]
  unfold dewFun
  rw [hl]

private theorem dewh1_exists_elt (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) {x : G} {M : Subgroup G} (hM : M ∈ dew1V Ω x)
    (hfx : f x = 0) :
    ∃ e ∈ dewDelta M (S.shift b M), e ∈ dewA S b ∧ dewFun S e = f := by
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨q, hq, hql⟩ := (h.lam_dewDelta_range S hb hM.1 hM.2).2 f hf hfx
  have hqQ : q ∈ pCore 2 G := dewDelta_le_pCore M (S.shift b M) hq
  have hqA : q ∈ dewA S b := (h.mem_dewA_iff S b hqQ).mpr fun z => by
    rw [hql z]
    rcases hcase (f z) with h0 | h1
    · simp [h0]
    · simp [h1]
  refine ⟨q, hq, hqA, ?_⟩
  funext z
  have h1 := h.lam_eq_smul_dewFun S hb hqA z
  rw [hql z] at h1
  exact (h.dewh1_smul_inj b hb _ _ h1).symm

private theorem dewh1_label (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) {e : G} (he : e ∈ dewA S b) (hef : dewFun S e = f)
    {K : Subgroup G} {u : G} (hK : K ∈ Ω) (hu : IsUniqueInvolution K u)
    (heK : e ∈ dewDelta K (S.shift b K)) : f u = 0 := by
  obtain ⟨φ, -, hφu, hφ⟩ := (h.lam_dewDelta_range S hb hK hu).1 e heK
  have h1 := h.lam_eq_smul_dewFun S hb he u
  rw [hφ u, hef] at h1
  exact ((h.dewh1_smul_inj b hb _ _ h1).symm).trans hφu

private theorem dewh1_eq_or_mul_x (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {x : G}
    {N : Subgroup G} (hN : N ∈ dew1V Ω x) {e₁ e₂ : G}
    (he₁ : e₁ ∈ dewDelta N (S.shift b N)) (he₂ : e₂ ∈ dewDelta N (S.shift b N))
    (hD : e₁⁻¹ * e₂ ∈ zGroup Ω) : e₂ = e₁ ∨ e₂ = e₁ * x := by
  have hinf := h.dewDelta_inf_zGroup (h.dewh1_twins S hb hN)
  have hg : e₁⁻¹ * e₂ ∈ dewDelta N (S.shift b N) ⊓ zGroup Ω :=
    ⟨(dewDelta N (S.shift b N)).mul_mem ((dewDelta N (S.shift b N)).inv_mem he₁) he₂, hD⟩
  rw [hinf] at hg
  rcases h.dewh1_zpowers_invol hN.2 hg with h1 | h1
  · left
    calc e₂ = e₁ * (e₁⁻¹ * e₂) := by group
      _ = e₁ := by rw [h1, mul_one]
  · right
    calc e₂ = e₁ * (e₁⁻¹ * e₂) := by group
      _ = e₁ * x := by rw [h1]

private theorem dewh1_delta_swap (S : TwinShift Ω) {b : Lab2} {N : Subgroup G} (hN : N ∈ Ω) :
    dewDelta (S.shift b N) (S.shift b (S.shift b N)) = dewDelta N (S.shift b N) := by
  rw [S.shift_shift_self b hN]
  unfold dewDelta
  rw [sup_comm]

private theorem dewh1_orbit (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b' ≠ b) {x : G} {M : Subgroup G} (hM : M ∈ dew1V Ω x) {N : Subgroup G}
    (hN : N ∈ dew1V Ω x) :
    N = M ∨ N = S.shift b M ∨ N = S.shift b' M ∨ N = S.shift b (S.shift b' M) := by
  obtain ⟨m, rfl⟩ := h.dewh1_shift_eq_of_mem S hM hN
  have hcase : ∀ m b b' : Lab2, (b ≠ 0 ∧ b' ≠ 0 ∧ b' ≠ b) →
      m = 0 ∨ m = b ∨ m = b' ∨ m = b + b' := by decide
  rcases hcase m b b' ⟨hb, hb', hbb'⟩ with h1 | h1 | h1 | h1
  · left
    rw [h1, S.shift_zero M hM.1]
  · right
    left
    rw [h1]
  · right
    right
    left
    rw [h1]
  · right
    right
    right
    rw [h1, S.shift_add b b' M hM.1]

private theorem dewh1_mk_coset (S : TwinShift Ω) {b : Lab2} {f : G → ZMod 2} {a : G}
    (ha : a ∈ dewA S b) (hfa : dewFun S a = f) : a ∈ edgeCoset S b f :=
  show a ∈ dewA S b ∧ dewFun S a = f from ⟨ha, hfa⟩

private theorem dewh1_second (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    (hfx : f x = 0) {M : Subgroup G} (hM : M ∈ dew1V Ω x) {e : G} (he : e ∈ dewA S b)
    (hef : dewFun S e = f) (heM : e ∈ dewDelta M (S.shift b M)) {b' : Lab2} (hb' : b' ≠ 0)
    (hbb' : b' ≠ b) :
    ∃ c ∈ zGroup Ω, c ≠ 1 ∧ c ≠ x ∧ f c = 0 ∧
      e * c ∈ dewDelta (S.shift b' M) (S.shift b (S.shift b' M)) ∧ e * c ∈ dewA S b ∧
      dewFun S (e * c) = f := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨φ, hφ, hφne⟩ := h.exists_dual_ne hx (zGroup Ω).one_mem hx1
  have hφ1 : φ 1 = 0 := hφ.1
  have hφx : φ x = 1 := by
    rcases hcase (φ x) with h0 | h1
    · exact absurd (by rw [h0, hφ1]) hφne
    · exact h1
  have hF : (fun z => φ z • b') ∈ dewDual2 Ω := by
    refine ⟨?_, ?_, ?_⟩
    · show φ 1 • b' = 0
      rw [hφ1, zero_smul]
    · intro z hz
      show φ z • b' = 0
      rw [hφ.2.1 z hz, zero_smul]
    · intro z hz w hw
      show φ (z * w) • b' = φ z • b' + φ w • b'
      rw [hφ.2.2 z hz w hw, add_smul]
  obtain ⟨a', ha'Q, ha'l⟩ := h.lam_surj S hF
  have ha'A : a' ∈ dewA S b' := (h.mem_dewA_iff S b' ha'Q).mpr fun z => by
    rw [ha'l z]
    show φ z • b' = 0 ∨ φ z • b' = b'
    rcases hcase (φ z) with h0 | h1
    · left
      rw [h0, zero_smul]
    · right
      rw [h1, one_smul]
  have hlx : S.lam a' x = b' := by
    rw [ha'l x, hφx, one_smul]
  have hfa'x : dewFun S a' x = 1 := by
    unfold dewFun
    rw [hlx]
    exact if_neg hb'
  have hfg : dewFun S e ≠ dewFun S a' := fun h1 => by
    have h2 := congrFun h1 x
    rw [hef, hfa'x, hfx] at h2
    exact zero_ne_one h2
  obtain ⟨c, hc, hc1, hce, hca', -, hcomm⟩ :=
    h.commutator_dewA_of_independent S hb hb' hbb'.symm he ha'A
      (by rw [hef]; exact hf0)
      (fun h0 => by
        have h2 := congrFun h0 x
        rw [hfa'x] at h2
        exact one_ne_zero h2) hfg
  have hcx : c ≠ x := by
    intro hcx
    have h2 := hca'
    rw [hcx, hfa'x] at h2
    exact one_ne_zero h2
  have hfc : f c = 0 := by
    rw [← hef]
    exact hce
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (h.zGroup_mul_self c hc)
  have hconj : a' * e * a'⁻¹ = e * c := by
    have e1 : a' * e * a'⁻¹ = (e * a' * e⁻¹ * a'⁻¹)⁻¹ * e := by group
    rw [hcomm, hcinv] at e1
    rw [e1]
    exact Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup he.1) c hc
  have hconjM : conjSub a' M = S.shift b' M := by
    rw [h.lam_spec S ha'Q hM, hlx]
  have tw := h.dewh1_twins S hb hM
  obtain ⟨k, hk, j, hj, hkj, -⟩ := (h.mem_dewDelta_iff tw).mp heM
  have hkA : a' * k * a'⁻¹ ∈ S.shift b' M := by
    rw [← hconjM]
    exact conj_mem_conjSub hk
  have hjA : a' * j * a'⁻¹ ∈ S.shift b (S.shift b' M) := by
    rw [← hconjM, S.shift_conj b a' M hM.1]
    exact conj_mem_conjSub hj
  have hmemD : e * c ∈ dewDelta (S.shift b' M) (S.shift b (S.shift b' M)) := by
    have e2 : e * c = (a' * k * a'⁻¹) * (a' * j * a'⁻¹)⁻¹ := by
      rw [← hconj, hkj]
      group
    unfold dewDelta
    refine Subgroup.mem_inf.mpr ⟨?_, (pCore 2 G).mul_mem he.1 (h.zGroup_le_pCore hc)⟩
    rw [e2]
    exact Subgroup.mul_mem_sup hkA ((S.shift b (S.shift b' M)).inv_mem hjA)
  have heA : e * c ∈ dewA S b := (dewA S b).mul_mem he (h.zGroup_le_dewA S b hc)
  exact ⟨c, hc, hc1, hcx, hfc, hmemD, heA, (h.dewh1_dewFun_mul S he hc).trans hef⟩

private theorem dewh1_struct (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    (hfx : f x = 0) {M : Subgroup G} (hM : M ∈ dew1V Ω x) {e : G} (he : e ∈ dewA S b)
    (hef : dewFun S e = f) (heM : e ∈ dewDelta M (S.shift b M)) :
    ∃ c ∈ zGroup Ω, c ≠ 1 ∧ c ≠ x ∧ f c = 0 ∧
      {e' | e' ∈ edgeCoset S b f ∧ ∃ N ∈ dew1V Ω x, e' ∈ dewDelta N (S.shift b N)} =
        ({e, e * x, e * c, e * c * x} : Set G) := by
  obtain ⟨b', hb'0, hbb'⟩ : ∃ b' : Lab2, b' ≠ 0 ∧ b' ≠ b := by
    have key : ∀ b : Lab2, b ≠ 0 → ∃ b' : Lab2, b' ≠ 0 ∧ b' ≠ b := by decide
    exact key b hb
  obtain ⟨c, hc, hc1, hcx, hfc, hecM', heA, hefc⟩ :=
    h.dewh1_second S hb hf hf0 hx hx1 hfx hM he hef heM hb'0 hbb'
  have hM' : S.shift b' M ∈ dew1V Ω x := h.dewh1_shift_mem_dew1V S hM b'
  have hxA : x ∈ dewA S b := h.zGroup_le_dewA S b hx
  have hfdx : ∀ d ∈ zGroup Ω, dewFun S (e * d) = f := fun d hd =>
    (h.dewh1_dewFun_mul S he hd).trans hef
  have hEM : ∀ e' ∈ dewA S b, dewFun S e' = f → e' ∈ dewDelta M (S.shift b M) →
      e' = e ∨ e' = e * x := fun e' he'A he'f he'M =>
    h.dewh1_eq_or_mul_x S hb hM heM he'M (h.dewh1_coset S hb he he'A (hef.trans he'f.symm))
  have hecM'' : e * c ∈ dewDelta (S.shift b' M) (S.shift b (S.shift b' M)) := hecM'
  have hEM' : ∀ e' ∈ dewA S b, dewFun S e' = f →
      e' ∈ dewDelta (S.shift b' M) (S.shift b (S.shift b' M)) → e' = e * c ∨ e' = e * c * x :=
    fun e' he'A he'f he'M =>
      h.dewh1_eq_or_mul_x S hb hM' hecM'' he'M
        (h.dewh1_coset S hb heA he'A (hefc.trans he'f.symm))
  refine ⟨c, hc, hc1, hcx, hfc, ?_⟩
  ext e'
  constructor
  · rintro ⟨he'c, N, hN, he'N⟩
    have he'A : e' ∈ dewA S b := he'c.1
    have he'f : dewFun S e' = f := he'c.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h.dewh1_orbit S hb hb'0 hbb' hM hN with h1 | h1 | h1 | h1
    · rw [h1] at he'N
      rcases hEM e' he'A he'f he'N with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · rw [h1, h.dewh1_delta_swap S hM.1] at he'N
      rcases hEM e' he'A he'f he'N with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · rw [h1] at he'N
      rcases hEM' e' he'A he'f he'N with h2 | h2
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h2))
    · rw [h1, h.dewh1_delta_swap S hM'.1] at he'N
      rcases hEM' e' he'A he'f he'N with h2 | h2
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h2))
  · intro h'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'
    rcases h' with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact ⟨h.dewh1_mk_coset S he (hef), M, hM, heM⟩
    · exact ⟨h.dewh1_mk_coset S ((dewA S b).mul_mem he hxA) (hfdx x hx), M, hM,
        (dewDelta M (S.shift b M)).mul_mem heM
          (h.zpowers_le_dewDelta (h.dewh1_twins S hb hM) (Subgroup.mem_zpowers x))⟩
    · exact ⟨h.dewh1_mk_coset S ((dewA S b).mul_mem he (h.zGroup_le_dewA S b hc)) (hfdx c hc),
        S.shift b' M, hM', hecM'⟩
    · exact ⟨h.dewh1_mk_coset S ((dewA S b).mul_mem heA hxA)
        ((h.dewh1_dewFun_mul S heA hx).trans hefc), S.shift b' M, hM',
        (dewDelta (S.shift b' M) (S.shift b (S.shift b' M))).mul_mem hecM'
          (h.zpowers_le_dewDelta (h.dewh1_twins S hb hM') (Subgroup.mem_zpowers x))⟩

private theorem dewh1_noncomm (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {x : G}
    {M : Subgroup G} (hM : M ∈ dew1V Ω x) {e : G} (heM : e ∈ dewDelta M (S.shift b M))
    (heD : e ∉ zGroup Ω) : ∃ j ∈ M, e * j ≠ j * e := by
  by_contra hcon
  push Not at hcon
  have tw := h.dewh1_twins S hb hM
  obtain ⟨k, hk, j, hj, hkj, -⟩ := (h.mem_dewDelta_iff tw).mp heM
  have hj'M : ∀ m ∈ M, j * m = m * j := fun m hm => h.commutes_of_dewTwins tw.symm j hj m hm
  have hjinv : ∀ m ∈ M, j⁻¹ * m = m * j⁻¹ := by
    intro m hm
    have h1 : j⁻¹ * m * j = m := by
      calc j⁻¹ * m * j = j⁻¹ * (m * j) := by group
        _ = j⁻¹ * (j * m) := by rw [hj'M m hm]
        _ = m := by group
    calc j⁻¹ * m = (j⁻¹ * m * j) * j⁻¹ := by group
      _ = m * j⁻¹ := by rw [h1]
  have hkm : ∀ m ∈ M, k * m = m * k := by
    intro m hm
    have h1 := hcon m hm
    rw [hkj] at h1
    have h2 : (k * m) * j⁻¹ = (m * k) * j⁻¹ := by
      calc (k * m) * j⁻¹ = k * (m * j⁻¹) := by group
        _ = k * (j⁻¹ * m) := by rw [hjinv m hm]
        _ = k * j⁻¹ * m := by group
        _ = m * (k * j⁻¹) := h1
        _ = (m * k) * j⁻¹ := by group
    exact mul_right_cancel h2
  have hk1 : k = 1 ∨ k = x :=
    h.dewh1_q8_center hM.1 hM.2 hk (fun y hy => (hkm y hy).symm)
  have hsb := h.dewh1_shift_mem_dew1V S hM b
  have hkS : k ∈ S.shift b M := by
    rcases hk1 with h1 | h1
    · rw [h1]
      exact (S.shift b M).one_mem
    · rw [h1]
      exact hsb.2.mem
  have heS : e ∈ S.shift b M := by
    rw [hkj]
    exact (S.shift b M).mul_mem hkS ((S.shift b M).inv_mem hj)
  have heInf : e ∈ S.shift b M ⊓ pCore 2 G := ⟨heS, dewDelta_le_pCore M (S.shift b M) heM⟩
  rw [h.inf_pCore hsb.1 hsb.2] at heInf
  have hxD : x ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hM.1 hM.2
  exact heD ((Subgroup.zpowers_le.mpr hxD) heInf)

private theorem dewh1_conj_delta (S : TwinShift Ω) {b : Lab2} {N : Subgroup G} {u : G}
    (tw : DewTwins Ω N (S.shift b N) u) (g e : G) (he : e ∈ dewDelta N (S.shift b N)) :
    g * e * g⁻¹ ∈ dewDelta (conjSub g N) (S.shift b (conjSub g N)) := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨k, hk, j, hj, hkj, hQ⟩ := (h.mem_dewDelta_iff tw).mp he
  rw [S.shift_conj b g N tw.memK]
  have hA : g * k * g⁻¹ ∈ conjSub g N := conj_mem_conjSub hk
  have hB : g * j * g⁻¹ ∈ conjSub g (S.shift b N) := conj_mem_conjSub hj
  have hmem : g * e * g⁻¹ = (g * k * g⁻¹) * (g * j * g⁻¹)⁻¹ := by
    rw [hkj]
    group
  unfold dewDelta
  refine Subgroup.mem_inf.mpr ⟨?_, (inferInstance : (pCore 2 G).Normal).conj_mem e hQ g⟩
  rw [hmem]
  exact Subgroup.mul_mem_sup hA ((conjSub g (S.shift b N)).inv_mem hB)

theorem edgeSet_eq (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    (hfx : f x = 0) :
    edgeSet S b f =
      {e | e ∈ edgeCoset S b f ∧ ∃ M ∈ dew1V Ω x, e ∈ dewDelta M (S.shift b M)} := by
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  ext e'
  constructor
  · rintro ⟨he'c, K, hK, heK⟩
    obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
    have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
    have hu1 : u ≠ 1 := hu.ne_one
    have hfu : f u = 0 := h.dewh1_label S hb hf he'c.1 he'c.2 hK hu heK
    by_cases hux : u = x
    · refine ⟨he'c, K, ?_, heK⟩
      rw [hux] at hu
      exact ⟨hK, hu⟩
    · obtain ⟨y, hy3, hyx, hyu⟩ := h.exists_cube hx huD hx1 hu1 (Ne.symm hux)
      have hinv := h.dewh1_conj_inv hf hf0 hx hx1 hfx huD hu1 hfu (Ne.symm hux) hy3 hyx hyu
      obtain ⟨M0, hM0⟩ := h.exists_mem_dew1V hx hx1
      obtain ⟨e0, he0M, he0A, he0f⟩ := h.dewh1_exists_elt S hb hf hM0 hfx
      obtain ⟨c, hc, hc1, hcx, hfc, hstruct⟩ :=
        h.dewh1_struct S hb hf hf0 hx hx1 hfx hM0 he0A he0f he0M
      have hKf := h.dewh1_ker_eq hf hf0 hx hx1 hfx hc hc1 hcx hfc
      have hKfD : ∀ d, d ∈ zGroup Ω → f d = 0 →
          d = 1 ∨ d = x ∨ d = c ∨ d = x * c := fun d hd hfd => (hKf d).mp ⟨hd, hfd⟩
      have hyx' : y⁻¹ * u * y⁻¹⁻¹ = x := by
        rw [← hyx]
        group
      have hK' : conjSub y⁻¹ K ∈ dew1V Ω x := by
        refine ⟨S.conj_mem y⁻¹ K hK, ?_⟩
        have := hu.conj y⁻¹
        rwa [hyx'] at this
      have he''D := h.dewh1_conj_delta S (h.dewh1_twins S hb (⟨hK, hu⟩ : K ∈ dew1V Ω u)) y⁻¹ e' heK
      have he''A : y⁻¹ * e' * y⁻¹⁻¹ ∈ dewA S b := (h.dewA_normal S b).conj_mem e' he'c.1 y⁻¹
      have hconj_inv : ∀ z, f (y⁻¹ * z * y⁻¹⁻¹) = f z := fun z => by
        have := hinv (y⁻¹ * z * y⁻¹⁻¹)
        rw [show y * (y⁻¹ * z * y⁻¹⁻¹) * y⁻¹ = z by group] at this
        exact this.symm
      have hfe'' : dewFun S (y⁻¹ * e' * y⁻¹⁻¹) = f :=
        h.dewh1_dewFun_conj S he'c.1 he'c.2 hconj_inv
      have he''S : y⁻¹ * e' * y⁻¹⁻¹ ∈ ({e0, e0 * x, e0 * c, e0 * c * x} : Set G) := by
        rw [← hstruct]
        exact ⟨h.dewh1_mk_coset S he''A hfe'', conjSub y⁻¹ K, hK', he''D⟩
      have hFa := hf.2.2
      obtain ⟨d, hdE, hd4⟩ : ∃ d, y⁻¹ * e' * y⁻¹⁻¹ = e0 * d ∧
          (d = 1 ∨ d = x ∨ d = c ∨ d = x * c) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he''S
        rcases he''S with h1 | h1 | h1 | h1
        · exact ⟨1, by rw [mul_one]; exact h1, Or.inl rfl⟩
        · exact ⟨x, h1, Or.inr (Or.inl rfl)⟩
        · exact ⟨c, h1, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨x * c, by rw [h1, mul_assoc, h.zGroup_comm c hc x hx],
            Or.inr (Or.inr (Or.inr rfl))⟩
      have hdK : d ∈ zGroup Ω ∧ f d = 0 := (hKf d).mpr hd4
      have hd'D : y * d * y⁻¹ ∈ zGroup Ω := h.zGroup_normal.conj_mem d hdK.1 y
      have hd'f : f (y * d * y⁻¹) = 0 := (hinv d).trans hdK.2
      have hc0D : e0⁻¹ * (y * e0 * y⁻¹) ∈ zGroup Ω := by
        refine h.dewh1_coset S hb he0A ((h.dewA_normal S b).conj_mem e0 he0A y) ?_
        exact he0f.trans (h.dewh1_dewFun_conj S he0A he0f hinv).symm
      have hc0f : f (e0⁻¹ * (y * e0 * y⁻¹)) = 0 := h.dewh1_cube_ker hf hy3 hinv hc0D
      have hkD : (e0⁻¹ * (y * e0 * y⁻¹)) * (y * d * y⁻¹) ∈ zGroup Ω :=
        (zGroup Ω).mul_mem hc0D hd'D
      have hkf : f ((e0⁻¹ * (y * e0 * y⁻¹)) * (y * d * y⁻¹)) = 0 := by
        rw [hFa _ hc0D _ hd'D, hc0f, hd'f, add_zero]
      have hek : e' = e0 * ((e0⁻¹ * (y * e0 * y⁻¹)) * (y * d * y⁻¹)) := by
        calc e' = y * (y⁻¹ * e' * y⁻¹⁻¹) * y⁻¹ := by group
          _ = y * (e0 * d) * y⁻¹ := by rw [hdE]
          _ = e0 * ((e0⁻¹ * (y * e0 * y⁻¹)) * (y * d * y⁻¹)) := by group
      generalize hk : (e0⁻¹ * (y * e0 * y⁻¹)) * (y * d * y⁻¹) = k at hek hkD hkf
      have hk4 := hKfD k hkD hkf
      have hmemR : e' ∈ ({e0, e0 * x, e0 * c, e0 * c * x} : Set G) := by
        rw [hek]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hk4 with h1 | h1 | h1 | h1
        · left
          rw [h1, mul_one]
        · right
          left
          rw [h1]
        · right
          right
          left
          rw [h1]
        · right
          right
          right
          rw [h1, mul_assoc, h.zGroup_comm x hx c hc]
      rw [← hstruct] at hmemR
      exact hmemR
  · rintro ⟨he'c, M, hM, heM⟩
    exact ⟨he'c, M, hM.1, heM⟩

theorem ncard_edgeSet (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) : (edgeSet S b f).ncard = 4 := by
  obtain ⟨x, hx, hx1, hfx, -⟩ := h.exists_involution_ker hf hf
  rw [h.edgeSet_eq S hb hf hf0 hx hx1 hfx]
  obtain ⟨M, hM⟩ := h.exists_mem_dew1V hx hx1
  obtain ⟨e, heM, heA, hef⟩ := h.dewh1_exists_elt S hb hf hM hfx
  obtain ⟨c, hc, hc1, hcx, -, hset⟩ := h.dewh1_struct S hb hf hf0 hx hx1 hfx hM heA hef heM
  rw [hset]
  have hne : ∀ d : G, e * d = e → d = 1 := fun d hd => mul_left_cancel (hd.trans (mul_one e).symm)
  have hex : e ≠ e * x := fun h1 => hx1 (hne x h1.symm)
  have hec : e ≠ e * c := fun h1 => hc1 (hne c h1.symm)
  have hecx : e ≠ e * c * x := by
    intro h1
    have hcx1 : c * x = 1 := hne (c * x) (by rw [← mul_assoc]; exact h1.symm)
    apply hcx
    calc c = c * (x * x) := by rw [h.zGroup_mul_self x hx, mul_one]
      _ = (c * x) * x := by rw [mul_assoc]
      _ = x := by rw [hcx1, one_mul]
  have hexec : e * x ≠ e * c := fun h1 => hcx (mul_left_cancel h1).symm
  have hexecx : e * x ≠ e * c * x := fun h1 => hc1 (hne c (mul_right_cancel h1).symm)
  have heccx : e * c ≠ e * c * x :=
    fun h1 => hx1 (mul_left_cancel ((mul_one (e * c)).trans h1)).symm
  have hn1 : e ∉ ({e * x, e * c, e * c * x} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hex, hec, hecx⟩
  have hn2 : e * x ∉ ({e * c, e * c * x} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hexec, hexecx⟩
  rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2, Set.ncard_pair heccx]

theorem edgeSet_centralizes (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) {e : G} (he : e ∈ edgeSet S b f) {x : G}
    (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) (hfx : f x = 0) {M : Subgroup G} (hM : M ∈ dew1V Ω x)
    (heM : e ∈ dewDelta M (S.shift b M)) :
    (∀ J ∈ dew1V Ω x, J ≠ M → J ≠ S.shift b M → ∀ j ∈ J, e * j = j * e) ∧
      ∀ J ∈ dew1V Ω x, (J = M ∨ J = S.shift b M) → ∃ j ∈ J, e * j ≠ j * e := by
  have heD : e ∉ zGroup Ω := by
    intro heD
    obtain ⟨y, hfy⟩ : ∃ y, f y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (funext hcon)
    have h1 := h.lam_eq_smul_dewFun S hb he.1.1 y
    rw [h.lam_of_mem_zGroup S heD y, he.1.2] at h1
    exact hfy (h.dewh1_smul_inj b hb _ _ (h1.symm.trans (zero_smul (ZMod 2) b).symm))
  refine ⟨?_, ?_⟩
  · intro J hJ hJM hJs j hj
    obtain ⟨k, hk, j', hj', hkj, -⟩ := (h.mem_dewDelta_iff (h.dewh1_twins S hb hM)).mp heM
    have tw1 : DewTwins Ω M J x := ⟨hM.1, hJ.1, hM.2, hJ.2, Ne.symm hJM⟩
    have hsb := h.dewh1_shift_mem_dew1V S hM b
    have tw2 : DewTwins Ω (S.shift b M) J x :=
      ⟨hsb.1, hJ.1, hsb.2, hJ.2, Ne.symm hJs⟩
    have hkJ : k * j = j * k := h.commutes_of_dewTwins tw1 k hk j hj
    have hj'J : j' * j = j * j' := h.commutes_of_dewTwins tw2 j' hj' j hj
    have hjinv : j'⁻¹ * j = j * j'⁻¹ := by
      calc j'⁻¹ * j = j'⁻¹ * (j * j') * j'⁻¹ := by group
        _ = j'⁻¹ * (j' * j) * j'⁻¹ := by rw [hj'J]
        _ = j * j'⁻¹ := by group
    rw [hkj]
    calc k * j'⁻¹ * j = k * (j'⁻¹ * j) := by group
      _ = k * (j * j'⁻¹) := by rw [hjinv]
      _ = (k * j) * j'⁻¹ := by group
      _ = (j * k) * j'⁻¹ := by rw [hkJ]
      _ = j * (k * j'⁻¹) := by group
  · intro J hJ hJcase
    rcases hJcase with h1 | h1
    · rw [h1]
      exact h.dewh1_noncomm S hb hM heM heD
    · have hsb := h.dewh1_shift_mem_dew1V S hM b
      have heM' : e ∈ dewDelta (S.shift b M) (S.shift b (S.shift b M)) := by
        rw [h.dewh1_delta_swap S hM.1]
        exact heM
      rw [h1]
      exact h.dewh1_noncomm S hb hsb heM' heD

theorem dewh2_two_zeros {f : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω) :
    ∃ x ∈ zGroup Ω, ∃ x' ∈ zGroup Ω, x ≠ 1 ∧ x' ≠ 1 ∧ x ≠ x' ∧ f x = 0 ∧ f x' = 0 := by
  obtain ⟨u, hu, hu1, hfu, -⟩ := h.exists_involution_ker hf hf
  obtain ⟨g, hg, hgne⟩ := h.exists_dual_ne (one_mem _) hu hu1.symm
  have hg1 : g 1 = 0 := hg.1
  have hgu : g u ≠ 0 := fun h0 => hgne (by rw [hg1, h0])
  obtain ⟨u', hu', hu'1, hfu', hgu'⟩ := h.exists_involution_ker hf hg
  exact ⟨u, hu, u', hu', hu1, hu'1, fun h0 => hgu (by rw [h0]; exact hgu'), hfu, hfu'⟩

omit h in
theorem dewh2_zpowers_inv {x g : G} (hx : x * x = 1) (hg : g ∈ Subgroup.zpowers x) :
    g = 1 ∨ g = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hx, one_zpow, one_mul]

omit h in
theorem dewh2_mul_ne {a d : G} (hd : d ≠ 1) : a ≠ a * d :=
  fun h0 => hd (mul_left_cancel (h0.symm.trans (mul_one a).symm))

omit h in
theorem dewh2_eq_of_four {α : Type*} {s : Set α} (hs : s.ncard = 4) (hfin : s.Finite)
    {a b c d y : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hy : y ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    y = a ∨ y = b ∨ y = c ∨ y = d := by
  have hsub : ({a, b, c, d} : Set α) ⊆ s := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have h1 : a ∉ ({b, c, d} : Set α) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Set α) := by simp [hbc, hbd]
  have h4 : ({a, b, c, d} : Set α).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair hcd]
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hs, h4])) hfin
  rw [← heq] at hy
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy

theorem dewh2_ne_shift (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) : K ≠ S.shift b K :=
  fun e => hb (S.shift_free b K hK e.symm)

theorem dewh2_shift_not_mem (S : TwinShift Ω) {b : Lab2} {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {M : Subgroup G} (hM : M ∈ Ω) (hMX : M ∉ X) :
    S.shift b M ∉ X := by
  intro h1
  apply hMX
  have h2 := hX.2.1 _ h1
  rwa [S.shift_shift_self b hM] at h2

theorem dewh2_shift_mem_dew1V (S : TwinShift Ω) {b : Lab2} {M : Subgroup G} {x : G}
    (hM : M ∈ dew1V Ω x) : S.shift b M ∈ dew1V Ω x := by
  rw [dew1V_eq_twinSet hM.1 hM.2]
  exact S.shift_mem b M hM.1

theorem dewh2_twins (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {M : Subgroup G} {x : G}
    (hM : M ∈ dew1V Ω x) : DewTwins Ω M (S.shift b M) x :=
  ⟨hM.1, (h.dewh2_shift_mem_dew1V S hM).1, hM.2, (h.dewh2_shift_mem_dew1V S hM).2,
    h.dewh2_ne_shift S hb hM.1⟩

theorem dewh2_inf_zGroup (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {M : Subgroup G} {x : G}
    (hM : M ∈ dew1V Ω x) : dewDelta M (S.shift b M) ⊓ zGroup Ω = Subgroup.zpowers x :=
  h.dewDelta_inf_zGroup (h.dewh2_twins S hb hM)

theorem dewh2_zpowers_le (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {M : Subgroup G} {x : G}
    (hM : M ∈ dew1V Ω x) : Subgroup.zpowers x ≤ dewDelta M (S.shift b M) :=
  h.zpowers_le_dewDelta (h.dewh2_twins S hb hM)

theorem dewh2_dewDelta_shift (S : TwinShift Ω) {b : Lab2} {M : Subgroup G} (hM : M ∈ Ω) :
    dewDelta (S.shift b M) (S.shift b (S.shift b M)) = dewDelta M (S.shift b M) := by
  rw [S.shift_shift_self b hM]
  unfold dewDelta
  rw [sup_comm]

theorem dewh2_exists_compl (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) :
    ∃ M ∈ dew1V Ω x, M ∉ X := by
  obtain ⟨K, hK, hKx⟩ := h.pt_exists_mem S hX hx hx1
  have hKΩ : K ∈ Ω := hX.1 hK
  have hT : dew1V Ω x = twinSet Ω K := dew1V_eq_twinSet hKΩ hKx
  by_contra hcon
  have hsub : twinSet Ω K ⊆ X := fun M hM =>
    by_contra fun hMX => hcon ⟨M, by rw [hT]; exact hM, hMX⟩
  have hI : twinSet Ω K ∩ X = twinSet Ω K := Set.inter_eq_left.mpr hsub
  have h3 := h.pt_twin_inter S hb hX hK
  rw [hI] at h3
  have h4 := congrArg Set.ncard h3
  rw [Set.ncard_pair (h.dewh2_ne_shift S hb hKΩ), h.twin4 K hKΩ] at h4
  omega

theorem dewh2_compl_pair (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    {M N : Subgroup G} (hM : M ∈ dew1V Ω x) (hMX : M ∉ X) (hN : N ∈ dew1V Ω x)
    (hNX : N ∉ X) : N = M ∨ N = S.shift b M := by
  obtain ⟨K, hK, hKx⟩ := h.pt_exists_mem S hX hx hx1
  have hKΩ : K ∈ Ω := hX.1 hK
  have hMΩ : M ∈ Ω := hM.1
  have hT : dew1V Ω x = twinSet Ω K := dew1V_eq_twinSet hKΩ hKx
  have hbM : S.shift b M ∉ X := h.dewh2_shift_not_mem S hX hMΩ hMX
  have hbK : S.shift b K ∈ X := hX.2.1 K hK
  have hbMT : S.shift b M ∈ dew1V Ω x := h.dewh2_shift_mem_dew1V S hM
  have hbKT : S.shift b K ∈ dew1V Ω x := by
    rw [hT]
    exact S.shift_mem b K hKΩ
  have hKT : K ∈ dew1V Ω x := ⟨hKΩ, hKx⟩
  have hdisj : Disjoint ({K, S.shift b K} : Set (Subgroup G)) {M, S.shift b M} := by
    rw [Set.disjoint_left]
    intro Y hY1 hY2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY1 hY2
    have hYX : Y ∈ X := by
      rcases hY1 with rfl | rfl
      · exact hK
      · exact hbK
    have hYX' : Y ∉ X := by
      rcases hY2 with rfl | rfl
      · exact hMX
      · exact hbM
    exact hYX' hYX
  have hcardA₁ : ({K, S.shift b K} : Set (Subgroup G)).ncard = 2 :=
    Set.ncard_pair (h.dewh2_ne_shift S hb hKΩ)
  have hcardA₂ : ({M, S.shift b M} : Set (Subgroup G)).ncard = 2 :=
    Set.ncard_pair (h.dewh2_ne_shift S hb hMΩ)
  have hcardU : ({K, S.shift b K} ∪ {M, S.shift b M} : Set (Subgroup G)).ncard = 4 := by
    rw [Set.ncard_union_eq hdisj, hcardA₁, hcardA₂]
  have hsubU : ({K, S.shift b K} ∪ {M, S.shift b M} : Set (Subgroup G)) ⊆ dew1V Ω x := by
    intro Y hY
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    rcases hY with (rfl | rfl) | (rfl | rfl)
    · exact hKT
    · exact hbKT
    · exact hM
    · exact hbMT
  have heq : ({K, S.shift b K} ∪ {M, S.shift b M} : Set (Subgroup G)) = dew1V Ω x :=
    Set.eq_of_subset_of_ncard_le hsubU (le_of_eq (by rw [hcardU, hT, h.twin4 K hKΩ]))
  have hN' : N ∈ ({K, S.shift b K} ∪ {M, S.shift b M} : Set (Subgroup G)) := by
    rw [heq]
    exact hN
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
  rcases hN' with (rfl | rfl) | (rfl | rfl)
  · exact absurd hK hNX
  · exact absurd hbK hNX
  · left
    rfl
  · right
    rfl

theorem dewh2_exists_q (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) {M : Subgroup G} {x : G} (hM : M ∈ dew1V Ω x)
    (hfx : f x = 0) : ∃ q ∈ edgeSet S b f, q ∈ dewDelta M (S.shift b M) := by
  obtain ⟨q, hq, hqlam⟩ := (h.lam_dewDelta_range S hb hM.1 hM.2).2 f hf hfx
  have hqQ : q ∈ pCore 2 G := dewDelta_le_pCore _ _ hq
  have hqA : q ∈ dewA S b := by
    refine (h.mem_dewA_iff S b hqQ).mpr (fun z => ?_)
    rw [hqlam z]
    rcases zmod2_cases (f z) with h0 | h0 <;> simp [h0]
  have hqf : dewFun S q = f := by
    funext z
    simp only [dewFun, hqlam z]
    rcases zmod2_cases (f z) with h0 | h0 <;> simp [h0, hb]
  exact ⟨q, ⟨⟨hqA, hqf⟩, M, hM.1, hq⟩, hq⟩

theorem dewh2_dewFun_mul (S : TwinShift Ω) {b : Lab2} {a d : G} (ha : a ∈ dewA S b)
    (hd : d ∈ zGroup Ω) : dewFun S (a * d) = dewFun S a := by
  funext z
  simp only [dewFun, h.lam_mul S ha.1 (h.zGroup_le_pCore hd), h.lam_of_mem_zGroup S hd,
    add_zero]

theorem dewh2_inv_mul (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {a a' : G}
    (ha : a ∈ dewA S b) (ha' : a' ∈ dewA S b) (hf : dewFun S a = dewFun S a') :
    a⁻¹ * a' ∈ zGroup Ω := by
  have hpa : a⁻¹ ∈ pCore 2 G := (pCore 2 G).inv_mem ha.1
  rw [← h.lam_eq_zero_iff S ((pCore 2 G).mul_mem hpa ha'.1)]
  intro z
  rw [h.lam_mul S hpa ha'.1 z, h.lam_inv S ha.1 z, h.lam_eq_smul_dewFun S hb ha z,
    h.lam_eq_smul_dewFun S hb ha' z, congrFun hf z, ← add_smul, zmod2_add_self, zero_smul]

theorem dewh2_dewEps_ne (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) (hXY : X ≠ Y) : dewEps X Y ≠ 0 := by
  intro h0
  apply hXY
  apply h.pt_eq_of_subset S hX hY
  intro K hK
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution (hX.1 hK)
  exact (h.mem_iff_dewEps S hb hX hY hK hz).mpr (congrFun h0 z)

theorem dewh2_centralize_dewStar {K₁ K₂ : Subgroup G} {x x' : G} (sp : DewPair Ω K₁ K₂ x x')
    {e : G} (h₁ : ∀ k ∈ K₁, e * k = k * e) (h₂ : ∀ j ∈ K₂, e * j = j * e) :
    ∀ n ∈ dewStar K₁ K₂, e * n = n * e := by
  obtain ⟨k₀, hk₀, hk₀x⟩ := h.exists_not_comm_of_dewPair sp
  rw [h.dewStar_eq sp hk₀ hk₀x]
  intro n hn
  obtain ⟨j, hj, rfl⟩ : ∃ j ∈ K₂, n = k₀ * j * k₀⁻¹ :=
    ⟨k₀⁻¹ * n * k₀, mem_conjSub_iff.mp hn, by group⟩
  have hc : Commute e k₀ := h₁ k₀ hk₀
  have hej : Commute e j := h₂ j hj
  exact (((hc.mul_right hej).mul_right hc.inv_right)).eq

theorem edge_unique (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) {e e' : G}
    (he : IsEdge S b X Y e) (he' : IsEdge S b X Y e') : e = e' := by
  have hXd : IsDewPoint S b X := hX
  have hYd : IsDewPoint S b Y := hY
  obtain ⟨hC, hΔ⟩ := he
  obtain ⟨hC', hΔ'⟩ := he'
  have hf : dewEps X Y ∈ DE2Hyp.deq2Dual Ω := h.dewEps_mem_dual S hb hXd hYd
  obtain ⟨x, hx, x', hx', hx1, hx'1, hxx', hfx, hfx'⟩ := h.dewh2_two_zeros hf
  have hD : e⁻¹ * e' ∈ zGroup Ω :=
    h.dewh2_inv_mul S hb hC.1 hC'.1 (hC.2.trans hC'.2.symm)
  have hzp : ∀ y ∈ zGroup Ω, y ≠ 1 → dewEps X Y y = 0 →
      e⁻¹ * e' ∈ Subgroup.zpowers y := by
    intro y hy hy1 hfy
    obtain ⟨M, hM, hMX⟩ := h.dewh2_exists_compl S hb hXd hy hy1
    have h1 : e⁻¹ * e' ∈ dewDelta M (S.shift b M) :=
      mul_mem (inv_mem (hΔ y hy hy1 hfy M hM hMX)) (hΔ' y hy hy1 hfy M hM hMX)
    rw [← h.dewh2_inf_zGroup S hb hM]
    exact Subgroup.mem_inf.mpr ⟨h1, hD⟩
  rcases dewh2_zpowers_inv (h.zGroup_mul_self x hx) (hzp x hx hx1 hfx) with h1 | h1
  · exact inv_mul_eq_one.mp h1
  · rcases dewh2_zpowers_inv (h.zGroup_mul_self x' hx') (hzp x' hx' hx'1 hfx') with h2 | h2
    · exact absurd (h1.symm.trans h2) hx1
    · exact absurd (h1.symm.trans h2) hxx'

theorem exists_edge (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) : ∃ e, IsEdge S b X Y e := by
  have hXd : IsDewPoint S b X := hX
  have hYd : IsDewPoint S b Y := hY
  have hf : dewEps X Y ∈ DE2Hyp.deq2Dual Ω := h.dewEps_mem_dual S hb hXd hYd
  have hf0 : dewEps X Y ≠ 0 := h.dewh2_dewEps_ne S hb hXd hYd hXY
  obtain ⟨x, hx, x', hx', hx1, hx'1, hxx', hfx, hfx'⟩ := h.dewh2_two_zeros hf
  have hxx : x * x = 1 := h.zGroup_mul_self x hx
  have hx'x' : x' * x' = 1 := h.zGroup_mul_self x' hx'
  have hD'' : x * x' ∈ zGroup Ω := (zGroup Ω).mul_mem hx hx'
  have hx''1 : x * x' ≠ 1 := fun h1 => hxx' (mul_left_cancel (h1.trans hxx.symm)).symm
  have hfx'' : dewEps X Y (x * x') = 0 := by
    rw [hf.2.2 x hx x' hx', hfx, hfx', add_zero]
  have hstepA : ∀ e ∈ edgeSet S b (dewEps X Y), ∀ d ∈ zGroup Ω, d ≠ 1 →
      dewEps X Y d = 0 → e * d ∈ edgeSet S b (dewEps X Y) := by
    intro e he d hd hd1 hfd
    rw [h.edgeSet_eq S hb hf hf0 hd hd1 hfd] at he ⊢
    obtain ⟨⟨heA, hefe⟩, M, hM, heM⟩ := he
    refine ⟨⟨(dewA S b).mul_mem heA (h.zGroup_le_dewA S b hd), ?_⟩, M, hM, ?_⟩
    · rw [h.dewh2_dewFun_mul S heA hd, hefe]
    · exact mul_mem heM (h.dewh2_zpowers_le S hb hM (Subgroup.mem_zpowers d))
  obtain ⟨M₁, hM₁, hM₁X⟩ := h.dewh2_exists_compl S hb hXd hx hx1
  obtain ⟨M₂, hM₂, hM₂X⟩ := h.dewh2_exists_compl S hb hXd hx' hx'1
  obtain ⟨q₁, hq₁E, hq₁Δ⟩ := h.dewh2_exists_q S hb hf hM₁ hfx
  obtain ⟨q₂, hq₂E, hq₂Δ⟩ := h.dewh2_exists_q S hb hf hM₂ hfx'
  have hmemE : ∀ y ∈ edgeSet S b (dewEps X Y),
      y = q₁ ∨ y = q₁ * x ∨ y = q₁ * x' ∨ y = q₁ * (x * x') := by
    intro y hy
    refine dewh2_eq_of_four (h.ncard_edgeSet S hb hf hf0) (Set.toFinite _)
      hq₁E (hstepA q₁ hq₁E x hx hx1 hfx) (hstepA q₁ hq₁E x' hx' hx'1 hfx')
      (hstepA q₁ hq₁E (x * x') hD'' hx''1 hfx'') hy
      (dewh2_mul_ne hx1) (dewh2_mul_ne hx'1) (dewh2_mul_ne hx''1) ?_ ?_ ?_
    · exact fun h0 => hxx' (mul_left_cancel h0)
    · intro h0
      have h1 := mul_left_cancel h0
      exact hx'1 (mul_left_cancel (h1.symm.trans (mul_one x).symm))
    · intro h0
      have h1 := mul_left_cancel h0
      exact hx1 (mul_right_cancel ((one_mul x').trans h1)).symm
  obtain ⟨e₀, he₀E, he₀₁, he₀₂⟩ : ∃ e₀, e₀ ∈ edgeSet S b (dewEps X Y) ∧
      e₀ ∈ dewDelta M₁ (S.shift b M₁) ∧ e₀ ∈ dewDelta M₂ (S.shift b M₂) := by
    rcases hmemE q₂ hq₂E with h2 | h2 | h2 | h2
    · exact ⟨q₁, hq₁E, hq₁Δ, h2 ▸ hq₂Δ⟩
    · exact ⟨q₂, hq₂E, h2 ▸ mul_mem hq₁Δ (h.dewh2_zpowers_le S hb hM₁ (Subgroup.mem_zpowers x)),
        hq₂Δ⟩
    · refine ⟨q₁, hq₁E, hq₁Δ, ?_⟩
      have e : q₁ = q₂ * x' := by rw [h2, mul_assoc, hx'x', mul_one]
      rw [e]
      exact mul_mem hq₂Δ (h.dewh2_zpowers_le S hb hM₂ (Subgroup.mem_zpowers x'))
    · refine ⟨q₁ * x, hstepA q₁ hq₁E x hx hx1 hfx,
        mul_mem hq₁Δ (h.dewh2_zpowers_le S hb hM₁ (Subgroup.mem_zpowers x)), ?_⟩
      have e : q₁ * x = q₂ * x' := by rw [h2, mul_assoc, mul_assoc, hx'x', mul_one]
      rw [e]
      exact mul_mem hq₂Δ (h.dewh2_zpowers_le S hb hM₂ (Subgroup.mem_zpowers x'))
  have hC1 : ∀ J ∈ X, IsUniqueInvolution J x → ∀ j ∈ J, e₀ * j = j * e₀ := by
    intro J hJ hJx
    have hcen := h.edgeSet_centralizes S hb hf hf0 he₀E hx hx1 hfx hM₁ he₀₁
    exact hcen.1 J ⟨hXd.1 hJ, hJx⟩ (fun e => hM₁X (e ▸ hJ))
      (fun e => h.dewh2_shift_not_mem S hXd hM₁.1 hM₁X (e ▸ hJ))
  have hC2 : ∀ J ∈ X, IsUniqueInvolution J x' → ∀ j ∈ J, e₀ * j = j * e₀ := by
    intro J hJ hJx
    have hcen := h.edgeSet_centralizes S hb hf hf0 he₀E hx' hx'1 hfx' hM₂ he₀₂
    exact hcen.1 J ⟨hXd.1 hJ, hJx⟩ (fun e => hM₂X (e ▸ hJ))
      (fun e => h.dewh2_shift_not_mem S hXd hM₂.1 hM₂X (e ▸ hJ))
  have hC3 : ∀ J ∈ X, IsUniqueInvolution J (x * x') → ∀ j ∈ J, e₀ * j = j * e₀ := by
    intro J hJ hJv
    obtain ⟨K₁, hK₁, hK₁x⟩ := h.pt_exists_mem S hXd hx hx1
    obtain ⟨K₂, hK₂, hK₂x⟩ := h.pt_exists_mem S hXd hx' hx'1
    have hK₁Ω : K₁ ∈ Ω := hXd.1 hK₁
    have hK₂Ω : K₂ ∈ Ω := hXd.1 hK₂
    have sp : DewPair Ω K₁ K₂ x x' := ⟨hK₁Ω, hK₂Ω, hK₁x, hK₂x, hxx'⟩
    have hN₁X : dewStar K₁ K₂ ∈ X := hXd.2.2.2 K₁ hK₁ K₂ hK₂ x x' sp
    have hN₁T := h.dewStar_mem_dew1V sp
    have hT3 : dew1V Ω (x * x') = twinSet Ω (dewStar K₁ K₂) :=
      dew1V_eq_twinSet hN₁T.1 hN₁T.2
    have hJT : J ∈ twinSet Ω (dewStar K₁ K₂) := by
      rw [← hT3]
      exact ⟨hXd.1 hJ, hJv⟩
    have hJ' : J ∈ ({dewStar K₁ K₂, S.shift b (dewStar K₁ K₂)} : Set (Subgroup G)) := by
      rw [← h.pt_twin_inter S hb hXd hN₁X]
      exact ⟨hJT, hJ⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ'
    have hcN₁ : ∀ n ∈ dewStar K₁ K₂, e₀ * n = n * e₀ :=
      h.dewh2_centralize_dewStar sp (hC1 K₁ hK₁ hK₁x) (hC2 K₂ hK₂ hK₂x)
    have hsh₂ : S.shift b K₂ ∈ dew1V Ω x' := h.dewh2_shift_mem_dew1V S ⟨hK₂Ω, hK₂x⟩
    have sp' : DewPair Ω K₁ (S.shift b K₂) x x' := ⟨hK₁Ω, hsh₂.1, hK₁x, hsh₂.2, hxx'⟩
    have hcN₁' : ∀ n ∈ dewStar K₁ (S.shift b K₂), e₀ * n = n * e₀ :=
      h.dewh2_centralize_dewStar sp' (hC1 K₁ hK₁ hK₁x)
        (hC2 (S.shift b K₂) (hXd.2.1 K₂ hK₂) hsh₂.2)
    have hshN : dewStar K₁ (S.shift b K₂) = S.shift b (dewStar K₁ K₂) := by
      have e1 := h.dewStar_shift S sp 0 b
      rwa [S.shift_zero K₁ hK₁Ω, zero_add] at e1
    rw [hshN] at hcN₁'
    rcases hJ' with rfl | rfl
    · exact hcN₁
    · exact hcN₁'
  obtain ⟨M₃, hM₃, he₀M₃⟩ : ∃ M₃ ∈ dew1V Ω (x * x'), e₀ ∈ dewDelta M₃ (S.shift b M₃) := by
    have hE := he₀E
    rw [h.edgeSet_eq S hb hf hf0 hD'' hx''1 hfx''] at hE
    obtain ⟨-, M₃, hM₃, hmem⟩ := hE
    exact ⟨M₃, hM₃, hmem⟩
  have hM₃X : M₃ ∉ X := by
    intro hM₃X
    obtain ⟨j, hj, hne⟩ := (h.edgeSet_centralizes S hb hf hf0 he₀E hD'' hx''1 hfx'' hM₃
      he₀M₃).2 M₃ hM₃ (Or.inl rfl)
    exact hne (hC3 M₃ hM₃X hM₃.2 j hj)
  have he₀C : e₀ ∈ edgeCoset S b (dewEps X Y) := he₀E.1
  refine ⟨e₀, ?_⟩
  unfold IsEdge
  refine ⟨he₀C, ?_⟩
  intro x₀ hx₀ hx₀1 hfx₀ M hM hMX
  have hx₀cases : x₀ = x ∨ x₀ = x' ∨ x₀ = x * x' := by
    rcases hmemE (q₁ * x₀) (hstepA q₁ hq₁E x₀ hx₀ hx₀1 hfx₀) with h2 | h2 | h2 | h2
    · exact absurd (mul_left_cancel (h2.trans (mul_one q₁).symm)) hx₀1
    · exact Or.inl (mul_left_cancel h2)
    · exact Or.inr (Or.inl (mul_left_cancel h2))
    · exact Or.inr (Or.inr (mul_left_cancel h2))
  rcases hx₀cases with rfl | rfl | rfl
  · rcases h.dewh2_compl_pair S hb hXd hx hx1 hM₁ hM₁X hM hMX with h1 | h1
    · rw [h1]
      exact he₀₁
    · rw [h1, h.dewh2_dewDelta_shift S hM₁.1]
      exact he₀₁
  · rcases h.dewh2_compl_pair S hb hXd hx' hx'1 hM₂ hM₂X hM hMX with h1 | h1
    · rw [h1]
      exact he₀₂
    · rw [h1, h.dewh2_dewDelta_shift S hM₂.1]
      exact he₀₂
  · rcases h.dewh2_compl_pair S hb hXd hD'' hx''1 hM₃ hM₃X hM hMX with h1 | h1
    · rw [h1]
      exact he₀M₃
    · rw [h1, h.dewh2_dewDelta_shift S hM₃.1]
      exact he₀M₃

theorem dewEdge_isEdge (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) :
    IsEdge S b X Y (dewEdge S b X Y) := by
  unfold dewEdge
  rw [dif_pos (h.exists_edge S hb hX hY hXY)]
  exact (h.exists_edge S hb hX hY hXY).choose_spec

theorem dewEdge_eq (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) {e : G}
    (he : IsEdge S b X Y e) : dewEdge S b X Y = e :=
  h.edge_unique S hb hX hY hXY (h.dewEdge_isEdge S hb hX hY hXY) he

private theorem dewh3_exists_pair {f g : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω)
    (hg : g ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hfg : f ≠ g) :
    ∃ x ∈ zGroup Ω, f x = 0 ∧ g x = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf0 (funext hall)
  have hx₀D : x₀ ∈ zGroup Ω := by
    by_contra hnot
    exact hx₀ (hf.2.1 x₀ hnot)
  have hfx₀ : f x₀ = 1 := by
    rcases zmod2_cases (f x₀) with c | c
    · exact absurd c hx₀
    · exact c
  have key : ∀ a c : ZMod 2, a + c = 0 → a = c := by decide
  have hgx : ∀ x ∈ zGroup Ω, g x = if f x = 0 then 0 else g x₀ := by
    intro x hx
    rcases zmod2_cases (f x) with c | c
    · rw [if_pos c]
      rcases zmod2_cases (g x) with d | d
      · exact d
      · exact absurd d (hcon x hx c)
    · rw [if_neg (by rw [c]; decide)]
      have hxx : f (x * x₀) = 0 := by
        rw [hf.2.2 x hx x₀ hx₀D, c, hfx₀]
        decide
      have hg' : g (x * x₀) = 0 := by
        rcases zmod2_cases (g (x * x₀)) with d | d
        · exact d
        · exact absurd d (hcon _ ((zGroup Ω).mul_mem hx hx₀D) hxx)
      have hsum := hg.2.2 x hx x₀ hx₀D
      rw [hg'] at hsum
      exact key _ _ hsum.symm
  rcases zmod2_cases (g x₀) with c0 | c1
  · apply hg0
    funext x
    by_cases hx : x ∈ zGroup Ω
    · rw [hgx x hx, c0]
      by_cases hfx : f x = 0 <;> simp [hfx]
    · exact hg.2.1 x hx
  · apply hfg
    funext x
    by_cases hx : x ∈ zGroup Ω
    · rw [hgx x hx, c1]
      rcases zmod2_cases (f x) with d | d <;> simp [d]
    · rw [hg.2.1 x hx, hf.2.1 x hx]

private theorem dewh3_eps_zero_off (S : TwinShift Ω) {b : Lab2} {P Q : Set (Subgroup G)}
    (hP : IsDewPoint S b P) {x : G} (hx : ¬(x ∈ zGroup Ω ∧ x ≠ 1)) :
    dewEps P Q x = 0 := by
  rw [dewEps_eq_zero_iff]
  rintro ⟨L, hLP, hL, -⟩
  exact hx ⟨dew1_involution_mem h.toDEHyp (hP.1 hLP) hL, hL.ne_one⟩

private theorem dewh3_eps_ne_zero (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) (hXY : X ≠ Y) : dewEps X Y ≠ 0 := by
  intro h0
  apply hXY
  refine h.pt_eq_of_subset S hX hY fun K hK => ?_
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution (hX.1 hK)
  exact (h.mem_iff_dewEps S hb hX hY hK hz).mpr (congrFun h0 z)

private theorem dewh3_exists_not_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X : Set (Subgroup G)}
    (hX : IsDewPoint S b X) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) :
    ∃ M, M ∈ dew1V Ω x ∧ M ∉ X := by
  obtain ⟨K, hKX, hKx⟩ := h.pt_exists_mem S hX hx hx1
  have hKΩ : K ∈ Ω := hX.1 hKX
  by_contra hcon
  push Not at hcon
  have hsub : dew1V Ω x ⊆ twinSet Ω K ∩ X := fun M hM => by
    refine ⟨?_, hcon M hM⟩
    rw [← dew1V_eq_twinSet hKΩ hKx]
    exact hM
  have h1 := h.pt_twin_inter S hb hX hKX
  have hcard := h.ncard_dew1V hKΩ hKx
  have hne : K ≠ S.shift b K := fun e => hb (S.shift_free b K hKΩ e.symm)
  have hle := Set.ncard_le_ncard (hsub.trans (le_of_eq h1))
  rw [hcard, Set.ncard_pair hne] at hle
  norm_num at hle

private theorem dewh3_not_mem_of_eps_zero (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X Y : Set (Subgroup G)} (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) {x : G}
    (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) (hε : dewEps X Y x = 0) {M : Subgroup G}
    (hM : M ∈ dew1V Ω x) (hMX : M ∉ X) : M ∉ Y := by
  intro hMY
  obtain ⟨K, hKX, hKx⟩ := h.pt_exists_mem S hX hx hx1
  have hKY : K ∈ Y := (h.mem_iff_dewEps S hb hX hY hKX hKx).mpr hε
  have hKtw : K ∈ twinSet Ω M := by
    rw [← dew1V_eq_twinSet hM.1 hM.2]
    exact ⟨hX.1 hKX, hKx⟩
  have h1 := h.pt_twin_inter S hb hY hMY
  have hK2 : K ∈ ({M, S.shift b M} : Set (Subgroup G)) := by
    rw [← h1]
    exact ⟨hKtw, hKY⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK2
  rcases hK2 with hKM | hKM
  · exact hMX (hKM ▸ hKX)
  · have hsh : S.shift b K = M := by
      rw [hKM, S.shift_shift_self b hM.1]
    exact hMX (hsh ▸ hX.2.1 K hKX)

private theorem dewh3_eps_add (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y Z : Set (Subgroup G)}
    (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) (hZ : IsDewPoint S b Z) (x : G) :
    dewEps X Z x = dewEps X Y x + dewEps Y Z x := by
  by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
  swap
  · rw [h.dewh3_eps_zero_off S hX (Q := Z) hx, h.dewh3_eps_zero_off S hX (Q := Y) hx,
      h.dewh3_eps_zero_off S hY (Q := Z) hx]
    simp
  have key1 : ∀ a c : ZMod 2, (a = 0 ↔ c = 0) → a = c := by decide
  have key2 : ∀ a c : ZMod 2, (a = 0 ↔ ¬ c = 0) → a = 1 + c := by decide
  obtain ⟨K, hKX, hKx⟩ := h.pt_exists_mem S hX hx.1 hx.2
  obtain ⟨N, hNY, hNx⟩ := h.pt_exists_mem S hY hx.1 hx.2
  have hKΩ : K ∈ Ω := hX.1 hKX
  have hNΩ : N ∈ Ω := hY.1 hNY
  rcases zmod2_cases (dewEps X Y x) with h1 | h1
  · have hKY : K ∈ Y := (h.mem_iff_dewEps S hb hX hY hKX hKx).mpr h1
    have hiff : dewEps X Z x = 0 ↔ dewEps Y Z x = 0 := by
      rw [← h.mem_iff_dewEps S hb hX hZ hKX hKx, ← h.mem_iff_dewEps S hb hY hZ hKY hKx]
    rw [h1, zero_add]
    exact key1 _ _ hiff
  · have hNX : N ∉ X := fun hNX' => by
      exact ((h.mem_iff_of_dewEps_eq_one S hb hX hY h1 hNΩ hNx).mp hNX') hNY
    have hKY : K ∉ Y := fun hKY' => by
      have := (h.mem_iff_dewEps S hb hX hY hKX hKx).mp hKY'
      rw [h1] at this
      exact one_ne_zero this
    have hcl : K ∈ Z ↔ ¬ N ∈ Z := by
      constructor
      · intro hKZ hNZ
        have hKtw : K ∈ twinSet Ω N := by
          rw [← dew1V_eq_twinSet hNΩ hNx]
          exact ⟨hKΩ, hKx⟩
        have h2 := h.pt_twin_inter S hb hZ hNZ
        have hK2 : K ∈ ({N, S.shift b N} : Set (Subgroup G)) := by
          rw [← h2]
          exact ⟨hKtw, hKZ⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK2
        rcases hK2 with hKN | hKN
        · exact hKY (hKN ▸ hNY)
        · have hsh : S.shift b K = N := by
            rw [hKN, S.shift_shift_self b hNΩ]
          exact hNX (hsh ▸ hX.2.1 K hKX)
      · intro hNZ'
        by_contra hKZ
        obtain ⟨R, hRZ, hRx⟩ := h.pt_exists_mem S hZ hx.1 hx.2
        have hRΩ : R ∈ Ω := hZ.1 hRZ
        have hRcases : R = K ∨ R = S.shift b K ∨ R = N ∨ R = S.shift b N := by
          by_cases hRX : R ∈ X
          · have hRtw : R ∈ twinSet Ω K := by
              rw [← dew1V_eq_twinSet hKΩ hKx]
              exact ⟨hRΩ, hRx⟩
            have h2 := h.pt_twin_inter S hb hX hKX
            have hR2 : R ∈ ({K, S.shift b K} : Set (Subgroup G)) := by
              rw [← h2]
              exact ⟨hRtw, hRX⟩
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR2
            rcases hR2 with h3 | h3
            · exact Or.inl h3
            · exact Or.inr (Or.inl h3)
          · have hRY : R ∈ Y := by
              by_contra hc
              exact hRX ((h.mem_iff_of_dewEps_eq_one S hb hX hY h1 hRΩ hRx).mpr hc)
            have hRtw : R ∈ twinSet Ω N := by
              rw [← dew1V_eq_twinSet hNΩ hNx]
              exact ⟨hRΩ, hRx⟩
            have h2 := h.pt_twin_inter S hb hY hNY
            have hR2 : R ∈ ({N, S.shift b N} : Set (Subgroup G)) := by
              rw [← h2]
              exact ⟨hRtw, hRY⟩
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR2
            rcases hR2 with h3 | h3
            · exact Or.inr (Or.inr (Or.inl h3))
            · exact Or.inr (Or.inr (Or.inr h3))
        rcases hRcases with h3 | h3 | h3 | h3
        · exact hKZ (by rw [← h3]; exact hRZ)
        · apply hKZ
          have hsh : S.shift b R = K := by
            rw [h3, S.shift_shift_self b hKΩ]
          rw [← hsh]
          exact hZ.2.1 R hRZ
        · exact hNZ' (by rw [← h3]; exact hRZ)
        · apply hNZ'
          have hsh : S.shift b R = N := by
            rw [h3, S.shift_shift_self b hNΩ]
          rw [← hsh]
          exact hZ.2.1 R hRZ
    have hiff : dewEps X Z x = 0 ↔ ¬ dewEps Y Z x = 0 := by
      rw [← h.mem_iff_dewEps S hb hX hZ hKX hKx, ← h.mem_iff_dewEps S hb hY hZ hNY hNx]
      exact hcl
    rw [h1]
    exact key2 _ _ hiff

private theorem dewh3_comm_of_isEdge (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X Y : Set (Subgroup G)} (hX : IsDewPoint S b X) (hY : IsDewPoint S b Y) (hXY : X ≠ Y)
    {e : G} (he : IsEdge S b X Y e) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    (hfx : dewEps X Y x = 0) {K : Subgroup G} (hK : K ∈ X) (hKx : IsUniqueInvolution K x) :
    ∀ j ∈ K, e * j = j * e := by
  obtain ⟨M₀, hM₀, hM₀X⟩ := h.dewh3_exists_not_mem S hb hX hx hx1
  have hΔ : e ∈ dewDelta M₀ (S.shift b M₀) := he.2 x hx hx1 hfx M₀ hM₀ hM₀X
  have hf0 := h.dewh3_eps_ne_zero S hb hX hY hXY
  have he' : e ∈ edgeSet S b (dewEps X Y) := ⟨he.1, M₀, hM₀.1, hΔ⟩
  have hKM : K ≠ M₀ := fun hKM => hM₀X (hKM ▸ hK)
  have hKs : K ≠ S.shift b M₀ := by
    intro hKs
    apply hM₀X
    have hsh : S.shift b K = M₀ := by rw [hKs, S.shift_shift_self b hM₀.1]
    exact hsh ▸ hX.2.1 K hK
  exact (h.edgeSet_centralizes S hb (h.dewEps_mem_dual S hb hX hY) hf0 he' hx hx1 hfx hM₀
    hΔ).1 K ⟨hX.1 hK, hKx⟩ hKM hKs

omit h in
private theorem dewh3_mem_zpowers_involution {x u : G} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hu : u ∈ Subgroup.zpowers x) : u = 1 ∨ u = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  rw [← zpow_mod_orderOf, hord]
  simp only [Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h0]
    simp
  · right
    rw [h1]
    simp

omit h in
private theorem dewh3_eq_one_of_zpowers {x w u : G} (hx : x * x = 1) (hx1 : x ≠ 1) (hw : w * w = 1)
    (hw1 : w ≠ 1) (hxw : x ≠ w) (hux : u ∈ Subgroup.zpowers x)
    (huw : u ∈ Subgroup.zpowers w) : u = 1 := by
  rcases dewh3_mem_zpowers_involution hx hx1 hux with h1 | h1
  · exact h1
  · rcases dewh3_mem_zpowers_involution hw hw1 huw with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hxw

omit h in
private theorem dewh3_dewFun_eq (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {a : G} {f : G → ZMod 2}
    (hf : ∀ x, S.lam a x = f x • b) : dewFun S a = f := by
  funext x
  rcases zmod2_cases (f x) with c | c
  · simp [dewFun, hf x, c]
  · simp [dewFun, hf x, c, hb]

theorem dewEdge_symm (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) :
    dewEdge S b X Y = dewEdge S b Y X := by
  have hX' : IsDewPoint S b X := hX
  have hY' : IsDewPoint S b Y := hY
  have hI : IsEdge S b X Y (dewEdge S b X Y) := h.dewEdge_isEdge S hb hX hY hXY
  have hsym : ∀ x, dewEps Y X x = dewEps X Y x := by
    intro x
    have h1 := h.dewh3_eps_add S hb hX' hY' hX' x
    have h0 : dewEps X X x = 0 :=
      dewEps_eq_zero_iff.mpr (fun ⟨L, hL, _, hLX⟩ => hLX hL)
    rw [h0] at h1
    have key : ∀ a c : ZMod 2, (0 : ZMod 2) = a + c → c = a := by decide
    exact key _ _ h1
  have hfun : dewEps Y X = dewEps X Y := funext hsym
  have hYX : IsEdge S b Y X (dewEdge S b X Y) := by
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hI.1
    · intro x hx hx1 hε M hM hMY
      have hε' : dewEps X Y x = 0 := by
        rw [← hfun]
        exact hε
      have hMX : M ∉ X := h.dewh3_not_mem_of_eps_zero S hb hY' hX' hx hx1 hε hM hMY
      exact hI.2 x hx hx1 hε' M hM hMX
  exact (h.dewEdge_eq S hb hY hX hXY.symm hYX).symm

theorem dewEdge_trans (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y Z : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hZ : Z ∈ dewPts S b) (hXY : X ≠ Y)
    (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    dewEdge S b X Y * dewEdge S b Y Z = dewEdge S b X Z := by
  have hX' : IsDewPoint S b X := hX
  have hY' : IsDewPoint S b Y := hY
  have hZ' : IsDewPoint S b Z := hZ
  have hyI : IsEdge S b X Y (dewEdge S b X Y) := h.dewEdge_isEdge S hb hX hY hXY
  have htI : IsEdge S b X Z (dewEdge S b X Z) := h.dewEdge_isEdge S hb hX hZ hXZ
  have he3I : IsEdge S b Y Z (dewEdge S b Y Z) := h.dewEdge_isEdge S hb hY hZ hYZ
  set y := dewEdge S b X Y
  set t := dewEdge S b X Z
  set e3 := dewEdge S b Y Z
  set f₁ := dewEps X Y
  set f₂ := dewEps X Z
  set f₃ := dewEps Y Z
  have hcoc : ∀ x, f₂ x = f₁ x + f₃ x := fun x => h.dewh3_eps_add S hb hX' hY' hZ' x
  have hcoc3 : ∀ x, f₃ x = f₁ x + f₂ x := by
    have key : ∀ a b c : ZMod 2, b = a + c → c = a + b := by decide
    intro x
    exact key _ _ _ (hcoc x)
  have hsum0 : ∀ x, f₁ x + f₂ x + f₃ x = 0 := by
    have key : ∀ a b c : ZMod 2, b = a + c → a + b + c = 0 := by decide
    intro x
    exact key _ _ _ (hcoc x)
  have hf₁ : f₁ ∈ DE2Hyp.deq2Dual Ω := h.dewEps_mem_dual S hb hX' hY'
  have hf₂ : f₂ ∈ DE2Hyp.deq2Dual Ω := h.dewEps_mem_dual S hb hX' hZ'
  have hf₃ : f₃ ∈ DE2Hyp.deq2Dual Ω := h.dewEps_mem_dual S hb hY' hZ'
  have hf₁0 : f₁ ≠ 0 := h.dewh3_eps_ne_zero S hb hX' hY' hXY
  have hf₂0 : f₂ ≠ 0 := h.dewh3_eps_ne_zero S hb hX' hZ' hXZ
  have hf₃0 : f₃ ≠ 0 := h.dewh3_eps_ne_zero S hb hY' hZ' hYZ
  have hf₁₂ : f₁ ≠ f₂ := by
    intro heq
    apply hf₃0
    funext x
    rw [hcoc3 x, ← heq]
    exact zmod2_add_self _
  obtain ⟨w, hwD, hw1, hfw₁, hfw₂⟩ := h.exists_involution_ker hf₁ hf₂
  have hfw₃ : f₃ w = 0 := by rw [hcoc3 w, hfw₁, hfw₂, zero_add]
  obtain ⟨M, hMw, hMX⟩ := h.dewh3_exists_not_mem S hb hX' hwD hw1
  have hMΩ : M ∈ Ω := hMw.1
  have hMinv : IsUniqueInvolution M w := hMw.2
  have hMY : M ∉ Y := h.dewh3_not_mem_of_eps_zero S hb hX' hY' hwD hw1 hfw₁ hMw hMX
  have hyΔ : y ∈ dewDelta M (S.shift b M) := hyI.2 w hwD hw1 hfw₁ M hMw hMX
  have htΔ : t ∈ dewDelta M (S.shift b M) := htI.2 w hwD hw1 hfw₂ M hMw hMX
  have he3Δ : e3 ∈ dewDelta M (S.shift b M) := he3I.2 w hwD hw1 hfw₃ M hMw hMY
  have hMsh : S.shift b M ∈ dew1V Ω w := by
    rw [dew1V_eq_twinSet hMΩ hMinv]
    exact S.shift_mem b M hMΩ
  have hne_M : M ≠ S.shift b M := fun e => hb (S.shift_free b M hMΩ e.symm)
  have tw_w : DewTwins Ω M (S.shift b M) w := ⟨hMΩ, hMsh.1, hMinv, hMsh.2, hne_M⟩
  have hyA : y ∈ dewA S b := hyI.1.1
  have htA : t ∈ dewA S b := htI.1.1
  have he3A : e3 ∈ dewA S b := he3I.1.1
  have hlam_y : ∀ x, S.lam y x = f₁ x • b := fun x => by
    rw [h.lam_eq_smul_dewFun S hb hyA x, hyI.1.2]
  have hlam_t : ∀ x, S.lam t x = f₂ x • b := fun x => by
    rw [h.lam_eq_smul_dewFun S hb htA x, htI.1.2]
  have hlam_e3 : ∀ x, S.lam e3 x = f₃ x • b := fun x => by
    rw [h.lam_eq_smul_dewFun S hb he3A x, he3I.1.2]
  have hyP : y ∈ pCore 2 G := hyA.1
  have htP : t ∈ pCore 2 G := htA.1
  have he3P : e3 ∈ pCore 2 G := he3A.1
  have hq₀D : y * t * e3 ∈ zGroup Ω := by
    refine (h.lam_eq_zero_iff S ((pCore 2 G).mul_mem ((pCore 2 G).mul_mem hyP htP) he3P)).mp ?_
    intro x
    rw [h.lam_mul S ((pCore 2 G).mul_mem hyP htP) he3P x, h.lam_mul S hyP htP x, hlam_y x,
      hlam_t x, hlam_e3 x, ← add_smul, ← add_smul, hsum0 x, zero_smul]
  have hq₀Δ : y * t * e3 ∈ dewDelta M (S.shift b M) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyΔ htΔ) he3Δ
  have hq₀w : y * t * e3 ∈ Subgroup.zpowers w := by
    rw [← h.dewDelta_inf_zGroup tw_w]
    exact ⟨hq₀Δ, hq₀D⟩
  obtain ⟨a, haD, hfa₁, hfa₂⟩ := h.dewh3_exists_pair hf₁ hf₂ hf₁0 hf₂0 hf₁₂
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, hf₂.1] at hfa₂
    exact zero_ne_one hfa₂
  obtain ⟨K, hKX, hKa⟩ := h.pt_exists_mem S hX' haD ha1
  have hKΩ : K ∈ Ω := hX'.1 hKX
  have hKmem : K ∈ dew1V Ω a := ⟨hKΩ, hKa⟩
  obtain ⟨k, hkK, hkφ⟩ := h.exists_mem_isElationOf hKΩ hKa hf₁ hfa₁
  have hKsh : S.shift b K ∈ dew1V Ω a := by
    rw [dew1V_eq_twinSet hKΩ hKa]
    exact S.shift_mem b K hKΩ
  have hne_K : K ≠ S.shift b K := fun e => hb (S.shift_free b K hKΩ e.symm)
  have tw_a : DewTwins Ω K (S.shift b K) a := ⟨hKΩ, hKsh.1, hKa, hKsh.2, hne_K⟩
  have hconjt : conjSub t K = S.shift b K := by
    have hla : S.lam t a = b := by rw [hlam_t a, hfa₂, one_smul]
    rw [h.lam_spec S htP hKmem, hla]
  set j := t * k * t⁻¹ with hj_def
  have hj : j ∈ S.shift b K := by
    rw [← hconjt]
    exact conj_mem_conjSub hkK
  have hjt : j * t = t * k := by
    rw [hj_def]
    group
  have hδQ : k * j⁻¹ ∈ pCore 2 G := by
    haveI : (pCore 2 G).Normal := CFSG.pCore_normal
    have hkt : k * t * k⁻¹ ∈ pCore 2 G := (inferInstance : (pCore 2 G).Normal).conj_mem t htP k
    have e1 : k * j⁻¹ = (k * t * k⁻¹) * t⁻¹ := by
      rw [hj_def]
      group
    rw [e1]
    exact (pCore 2 G).mul_mem hkt ((pCore 2 G).inv_mem htP)
  have hδΔ : k * j⁻¹ ∈ dewDelta K (S.shift b K) :=
    (h.mem_dewDelta_iff tw_a).mpr ⟨k, hkK, j, hj, rfl, hδQ⟩
  have hδlam : ∀ x, S.lam (k * j⁻¹) x = f₁ x • b := fun x =>
    h.lam_dewDelta S hb hKΩ hKa hf₁ hkK hj hkφ hδQ x
  have hδA : k * j⁻¹ ∈ dewA S b := by
    refine (h.mem_dewA_iff S b hδQ).mpr (fun x => ?_)
    rw [hδlam x]
    rcases zmod2_cases (f₁ x) with c | c <;> simp [c]
  have hδF : dewFun S (k * j⁻¹) = f₁ := dewh3_dewFun_eq S hb hδlam
  set d := (k * j⁻¹)⁻¹ * y with hd_def
  have hdQ : d ∈ pCore 2 G := (pCore 2 G).mul_mem ((pCore 2 G).inv_mem hδQ) hyP
  have hdlam : ∀ x, S.lam d x = 0 := fun x => by
    rw [hd_def, h.lam_mul S ((pCore 2 G).inv_mem hδQ) hyP x, h.lam_inv S hδQ x, hδlam x,
      hlam_y x, ← add_smul, zmod2_add_self, zero_smul]
  have hdD : d ∈ zGroup Ω := (h.lam_eq_zero_iff S hdQ).mp hdlam
  have hkj : k * j = j * k := h.commutes_of_dewTwins tw_a k hkK j hj
  have hkinv : k⁻¹ * j = j * k⁻¹ := by
    calc k⁻¹ * j = k⁻¹ * (j * k) * k⁻¹ := by group
      _ = k⁻¹ * (k * j) * k⁻¹ := by rw [← hkj]
      _ = j * k⁻¹ := by group
  have hyK : ∀ l ∈ K, y * l = l * y := fun l hl =>
    h.dewh3_comm_of_isEdge S hb hX' hY' hXY hyI haD ha1 hfa₁ hKX hKa l hl
  have hyKs : ∀ l ∈ S.shift b K, y * l = l * y := fun l hl =>
    h.dewh3_comm_of_isEdge S hb hX' hY' hXY hyI haD ha1 hfa₁ (hX'.2.1 K hKX) hKsh.2 l hl
  have hyj : y * j = j * y := hyKs j hj
  have hdeq : d = k⁻¹ * y * j := by
    calc d = j * k⁻¹ * y := by rw [hd_def]; group
      _ = k⁻¹ * j * y := by rw [hkinv]
      _ = k⁻¹ * (j * y) := by group
      _ = k⁻¹ * (y * j) := by rw [hyj]
      _ = k⁻¹ * y * j := by group
  have hd1 : d ≠ 1 := by
    intro hd1
    have hyδ : y = k * j⁻¹ := (inv_mul_eq_one.mp hd1).symm
    have hyΔK : y ∈ dewDelta K (S.shift b K) := by
      rw [hyδ]
      exact hδΔ
    have hyE : y ∈ edgeSet S b f₁ := ⟨hyI.1, K, hKΩ, hyΔK⟩
    obtain ⟨j₀, hj₀, hne⟩ :=
      (h.edgeSet_centralizes S hb hf₁ hf₁0 hyE haD ha1 hfa₁ hKmem hyΔK).2 K hKmem (Or.inl rfl)
    exact hne (hyK j₀ hj₀)
  obtain ⟨a'₀, ha'₀D, hfa'₂, hfa'₁⟩ := h.dewh3_exists_pair hf₂ hf₁ hf₂0 hf₁0 hf₁₂.symm
  obtain ⟨a', ha'D, hfa'2, hfa'1, hda'⟩ :
      ∃ a' ∈ zGroup Ω, f₂ a' = 0 ∧ f₁ a' = 1 ∧ d ≠ a' := by
    by_cases hda : d = a'₀
    · refine ⟨a'₀ * w, (zGroup Ω).mul_mem ha'₀D hwD, ?_, ?_, ?_⟩
      · rw [hf₂.2.2 a'₀ ha'₀D w hwD, hfa'₂, hfw₂, zero_add]
      · rw [hf₁.2.2 a'₀ ha'₀D w hwD, hfa'₁, hfw₁, add_zero]
      · intro h'
        have h2 : a'₀ * w = a'₀ := h'.symm.trans hda
        exact hw1 (mul_left_cancel (h2.trans (mul_one a'₀).symm))
    · exact ⟨a'₀, ha'₀D, hfa'₂, hfa'₁, hda⟩
  have ha'1 : a' ≠ 1 := by
    intro h1
    rw [h1, hf₁.1] at hfa'1
    exact zero_ne_one hfa'1
  obtain ⟨L, hLX, hLa'⟩ := h.pt_exists_mem S hX' ha'D ha'1
  have hLΩ : L ∈ Ω := hX'.1 hLX
  have htL : ∀ l ∈ L, t * l = l * t := fun l hl =>
    h.dewh3_comm_of_isEdge S hb hX' hZ' hXZ htI ha'D ha'1 hfa'2 hLX hLa' l hl
  have hf1x : f₁ (a * a') = 1 := by
    rw [hf₁.2.2 a haD a' ha'D, hfa₁, hfa'1, zero_add]
  have hf2x : f₂ (a * a') = 1 := by
    rw [hf₂.2.2 a haD a' ha'D, hfa₂, hfa'2, add_zero]
  have hf3x : f₃ (a * a') = 0 := by
    rw [hcoc3 (a * a'), hf1x, hf2x]
    decide
  have hx₁D : a * a' ∈ zGroup Ω := (zGroup Ω).mul_mem haD ha'D
  have hx₁1 : a * a' ≠ 1 := by
    intro e
    rw [e, hf₁.1] at hf1x
    exact zero_ne_one hf1x
  have hx₁w : a * a' ≠ w := by
    intro e
    rw [e, hfw₁] at hf1x
    exact zero_ne_one hf1x
  have hne_aa' : a ≠ a' := by
    intro e
    rw [e, hfa'1] at hfa₁
    exact one_ne_zero hfa₁
  have hsp : DewPair Ω K L a a' := ⟨hKΩ, hLΩ, hKa, hLa', hne_aa'⟩
  have hMX' : dewStar K L ∈ X := hX'.2.2.2 K hKX L hLX a a' hsp
  have hMdew : dewStar K L ∈ dew1V Ω (a * a') := h.dewStar_mem_dew1V hsp
  have hka' : k * a' ≠ a' * k := by
    intro hc
    have hk := hkφ a' ha'D
    rw [if_neg (by rw [hfa'1]; exact one_ne_zero)] at hk
    have hk2 : k * a' * k⁻¹ = a' := by
      rw [hc]
      group
    have ha1' : a = 1 := mul_eq_right.mp (hk.symm.trans hk2)
    exact ha1 ha1'
  have hMeq : dewStar K L = conjSub k L := h.dewStar_eq hsp hkK hka'
  have hzA : y * t ∈ dewA S b := (dewA S b).mul_mem hyA htA
  have hzF : dewFun S (y * t) = f₃ := by
    refine dewh3_dewFun_eq S hb (fun x => ?_)
    rw [h.lam_mul S hyP htP x, hlam_y x, hlam_t x, ← add_smul, ← hcoc3 x]
  have hzΔ : y * t ∈ dewDelta M (S.shift b M) := Subgroup.mul_mem _ hyΔ htΔ
  have hzE : y * t ∈ edgeSet S b f₃ := ⟨⟨hzA, hzF⟩, M, hMΩ, hzΔ⟩
  have hE := h.edgeSet_eq S hb hf₃ hf₃0 hx₁D hx₁1 hf3x
  obtain ⟨M'', hM''mem, hzM''⟩ :
      ∃ M'' ∈ dew1V Ω (a * a'), y * t ∈ dewDelta M'' (S.shift b M'') := by
    have hz2 := hzE
    rw [hE] at hz2
    exact hz2.2
  by_cases hM''X : M'' ∈ X
  ·
    have hM''Y : M'' ∉ Y :=
      (h.mem_iff_of_dewEps_eq_one S hb hX' hY' hf1x hM''mem.1 hM''mem.2).mp hM''X
    have he3Δ' : e3 ∈ dewDelta M'' (S.shift b M'') :=
      he3I.2 (a * a') hx₁D hx₁1 hf3x M'' hM''mem hM''Y
    have hq'Δ : y * t * e3 ∈ dewDelta M'' (S.shift b M'') :=
      Subgroup.mul_mem _ hzM'' he3Δ'
    have hne'' : M'' ≠ S.shift b M'' := fun e => hb (S.shift_free b M'' hM''mem.1 e.symm)
    have hsh'' : S.shift b M'' ∈ dew1V Ω (a * a') := by
      rw [dew1V_eq_twinSet hM''mem.1 hM''mem.2]
      exact S.shift_mem b M'' hM''mem.1
    have tw'' : DewTwins Ω M'' (S.shift b M'') (a * a') :=
      ⟨hM''mem.1, hsh''.1, hM''mem.2, hsh''.2, hne''⟩
    have hq'x : y * t * e3 ∈ Subgroup.zpowers (a * a') := by
      rw [← h.dewDelta_inf_zGroup tw'']
      exact ⟨hq'Δ, hq₀D⟩
    have hq1 : y * t * e3 = 1 :=
      dewh3_eq_one_of_zpowers hM''mem.2.sq hM''mem.2.ne_one hMinv.sq hMinv.ne_one hx₁w hq'x
        hq₀w
    have he3sq : e3 * e3 = 1 := h.dewA_mul_self S hb he3A
    have hyt : y * t = e3 := by
      have h1 := eq_inv_of_mul_eq_one_left hq1
      rw [h1, inv_eq_of_mul_eq_one_right he3sq]
    calc y * e3 = y * (y * t) := by rw [hyt]
      _ = (y * y) * t := by group
      _ = t := by rw [h.dewA_mul_self S hb hyA, one_mul]
  ·
    exfalso
    have hJ : dewStar K L ≠ M'' := fun e => hM''X (e ▸ hMX')
    have hJs : dewStar K L ≠ S.shift b M'' := by
      intro e
      apply hM''X
      have hsh : S.shift b (dewStar K L) = M'' := by
        rw [e, S.shift_shift_self b hM''mem.1]
      exact hsh ▸ hX'.2.1 _ hMX'
    have hcent := (h.edgeSet_centralizes S hb hf₃ hf₃0 hzE hx₁D hx₁1 hf3x hM''mem hzM'').1
      (dewStar K L) hMdew hJ hJs
    have hdl : ∀ l ∈ L, d * l = l * d := by
      intro l hl
      have hmem : k * l * k⁻¹ ∈ dewStar K L := by
        rw [hMeq]
        exact conj_mem_conjSub hl
      have hc := hcent (k * l * k⁻¹) hmem
      have hA : (k⁻¹ * y * j * t) * l = l * (k⁻¹ * y * j * t) := by
        calc (k⁻¹ * y * j * t) * l = k⁻¹ * y * (j * t) * l := by group
          _ = k⁻¹ * y * (t * k) * l := by rw [hjt]
          _ = k⁻¹ * ((y * t) * (k * l * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * l * k⁻¹) * (y * t)) * k := by rw [hc]
          _ = l * (k⁻¹ * (y * t) * k) := by group
          _ = l * (k⁻¹ * y * (t * k)) := by group
          _ = l * (k⁻¹ * y * (j * t)) := by rw [hjt]
          _ = l * (k⁻¹ * y * j * t) := by group
      have htl := htL l hl
      have e1 : (k⁻¹ * y * j * t) * l = ((k⁻¹ * y * j) * l) * t := by
        calc (k⁻¹ * y * j * t) * l = (k⁻¹ * y * j) * (t * l) := by group
          _ = (k⁻¹ * y * j) * (l * t) := by rw [htl]
          _ = ((k⁻¹ * y * j) * l) * t := by group
      have e2 : l * (k⁻¹ * y * j * t) = (l * (k⁻¹ * y * j)) * t := by group
      have hB : ((k⁻¹ * y * j) * l) * t = (l * (k⁻¹ * y * j)) * t := by
        rw [← e1, hA, e2]
      rw [hdeq]
      exact mul_right_cancel hB
    have hd_zp : d ∉ Subgroup.zpowers a' := by
      intro hmem
      rcases dewh3_mem_zpowers_involution hLa'.sq hLa'.ne_one hmem with h1 | h1
      · exact hd1 h1
      · exact hda' h1
    have hcard := h.card_inf_centralizer_dew hLΩ hLa' hdD hd_zp
    have hLle : L ≤ Subgroup.centralizer {d} := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      first
        | exact hdl l hl
        | exact (hdl l hl).symm
    rw [inf_eq_left.mpr hLle, h.toDEHyp.card L hLΩ] at hcard
    norm_num at hcard

theorem dewh4_dewEps_eq_add (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    (C : DewPointCoord S b) {X Y : Set (Subgroup G)} (hX : X ∈ dewPts S b)
    (hY : Y ∈ dewPts S b) (x : G) : dewEps X Y x = C.coord X x + C.coord Y x := by
  obtain ⟨m, hm⟩ := lab2_exists_dewQb_one b hb
  have hcX : C.coord X ∈ DE2Hyp.deq2Dual Ω := C.bijOn.mapsTo hX
  have hcY : C.coord Y ∈ DE2Hyp.deq2Dual Ω := C.bijOn.mapsTo hY
  obtain ⟨hX1, hXout, hXadd⟩ := hcX
  obtain ⟨hY1, hYout, hYadd⟩ := hcY
  have hsmul : ∀ c : ZMod 2, dewQb b (c • m) = c := by
    intro c
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · rw [zero_smul, dewQb_zero]
    · rw [one_smul, hm]
  have key : ∀ a c : ZMod 2, a + (a + c) = c := by decide
  let F : G → Lab2 := fun y => (C.coord X y + C.coord Y y) • m
  have hF : F ∈ dewDual2 Ω := by
    refine ⟨?_, ?_, ?_⟩
    · simp [F, hX1, hY1]
    · intro y hy
      simp [F, hXout y hy, hYout y hy]
    · intro y hy z hz
      show (C.coord X (y * z) + C.coord Y (y * z)) • m
          = (C.coord X y + C.coord Y y) • m + (C.coord X z + C.coord Y z) • m
      rw [hXadd y hy z hz, hYadd y hy z hz, ← add_smul]
      congr 1
      ring
  obtain ⟨q, hq, hqS⟩ := h.lam_surj S hF
  have hqX : conjSub q '' X ∈ dewPts S b := h.isDewPoint_conjSub S hX q
  have hcoord : C.coord (conjSub q '' X) = C.coord Y := by
    funext z
    rw [C.qAct q hq X hX]
    simp only [Pi.add_apply, hqS, F, hsmul]
    exact key _ _
  have hqXY : conjSub q '' X = Y := C.bijOn.injOn hqX hY hcoord
  have hdq := h.dq_lam_eq_dewEps S hb hX hY hq hqXY x
  rw [← hdq, hqS]
  simp only [F, hsmul]

omit h in
theorem dewh4_exists_kernel_nonvanish {f g : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω)
    (hg : g ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hgf : g ≠ f) :
    ∃ x ∈ zGroup Ω, x ≠ 1 ∧ f x = 0 ∧ g x = 1 := by
  have z2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  by_contra hcon
  push Not at hcon
  obtain ⟨hf1, hfout, hfadd⟩ := hf
  obtain ⟨hg1, hgout, hgadd⟩ := hg
  have hg_ker : ∀ x ∈ zGroup Ω, f x = 0 → g x = 0 := by
    intro x hx hfx
    by_cases hx1 : x = 1
    · subst hx1
      exact hg1
    · exact (z2 (g x)).resolve_right (hcon x hx hx1 hfx)
  obtain ⟨d, hd, hfd⟩ : ∃ d ∈ zGroup Ω, f d = 1 := by
    by_contra hno
    push Not at hno
    apply hf0
    funext y
    by_cases hy : y ∈ zGroup Ω
    · have hfy : f y = 0 := (z2 (f y)).resolve_right (fun e => hno y hy e)
      simp [hfy]
    · simp [hfout y hy]
  have hformula : ∀ x ∈ zGroup Ω, g x = if f x = 0 then 0 else g d := by
    intro x hx
    by_cases hfx : f x = 0
    · simp [hfx, hg_ker x hx hfx]
    · have hfx1 : f x = 1 := (z2 (f x)).resolve_left hfx
      have hdinv : d⁻¹ ∈ zGroup Ω := inv_mem hd
      have hfdinv : f d⁻¹ = 1 := by
        have h1 := hfadd d hd d⁻¹ hdinv
        rw [mul_inv_cancel, hf1, hfd] at h1
        have h2 : ∀ t : ZMod 2, (0 : ZMod 2) = 1 + t → t = 1 := by decide
        exact h2 _ h1
      have hxd : x * d⁻¹ ∈ zGroup Ω := mul_mem hx hdinv
      have hfxd : f (x * d⁻¹) = 0 := by
        rw [hfadd x hx d⁻¹ hdinv, hfx1, hfdinv]
        decide
      have hgxd : g (x * d⁻¹) = 0 := hg_ker _ hxd hfxd
      have h2 := hgadd (x * d⁻¹) hxd d hd
      rw [show x * d⁻¹ * d = x by group, hgxd, zero_add] at h2
      rw [if_neg hfx, h2]
  rcases z2 (g d) with hgd | hgd
  · apply hg0
    funext y
    by_cases hy : y ∈ zGroup Ω
    · have := hformula y hy
      split_ifs at this with hfy
      · simpa using this
      · simpa [hgd] using this
    · exact hgout y hy
  · apply hgf
    funext y
    by_cases hy : y ∈ zGroup Ω
    · have := hformula y hy
      rw [hgd] at this
      split_ifs at this with hfy
      · simp [hfy, this]
      · rcases z2 (f y) with h0 | h1
        · exact absurd h0 hfy
        · simp [h1, this]
    · simp [hgout y hy, hfout y hy]

theorem dewh4_lam_of_mem_delta (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) {q : G}
    (hq : q ∈ dewDelta K (S.shift b K)) :
    (∀ x, S.lam q x = dewFun S q x • b) ∧ dewFun S q ∈ DE2Hyp.deq2Dual Ω ∧ dewFun S q u = 0 := by
  obtain ⟨f, hf, hfu, hlam⟩ := (h.lam_dewDelta_range S hb hK hu).1 q hq
  have hdf : dewFun S q = f := by
    funext x
    unfold dewFun
    rw [hlam x]
    rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) (f x) with h0 | h1
    · simp [h0]
    · simp only [h1, one_smul]
      rw [if_neg hb]
  refine ⟨fun x => ?_, hdf ▸ hf, hdf ▸ hfu⟩
  rw [hdf, hlam x]

omit h in
theorem dewh4_dewTwins_shift (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) : DewTwins Ω K (S.shift b K) u := by
  obtain ⟨z, hz, hz'⟩ := (S.shift_mem b K hK).2
  have hzu : z = u := hz.eq hu
  refine ⟨hK, (S.shift_mem b K hK).1, hu, hzu ▸ hz', fun e => hb (S.shift_free b K hK e.symm)⟩

omit h in
theorem dewh4_zpowers_involution {u g : G} (hu : u * u = 1) (hg : g ∈ Subgroup.zpowers u) :
    g = 1 ∨ g = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, hu2, one_zpow]
  · right
    have : u ^ (2 * m) = 1 := by rw [zpow_mul, hu2, one_zpow]
    rw [zpow_add_one, this, one_mul]

theorem dewh4_eq_of_dewEps_eq_zero (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    (C : DewPointCoord S b) {X Y : Set (Subgroup G)} (hX : X ∈ dewPts S b)
    (hY : Y ∈ dewPts S b) (h0 : dewEps X Y = 0) : X = Y := by
  apply C.bijOn.injOn hX hY
  funext z
  have hz := congrFun h0 z
  rw [dewh4_dewEps_eq_add h S hb C hX hY z, Pi.zero_apply] at hz
  exact (show ∀ a c : ZMod 2, a + c = 0 → a = c by decide) _ _ hz

theorem dewh4_mul_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} (hK : K ∈ Ω)
    {u : G} (hu : IsUniqueInvolution K u) {q e : G}
    (hq : q ∈ dewDelta K (S.shift b K)) (he : e ∈ dewDelta K (S.shift b K))
    (hfe : dewFun S e = dewFun S q) : q * e = 1 ∨ q * e = u := by
  have hqp : q ∈ pCore 2 G := (Subgroup.mem_inf.mp hq).2
  have hep : e ∈ pCore 2 G := (Subgroup.mem_inf.mp he).2
  obtain ⟨hlq, -, -⟩ := h.dewh4_lam_of_mem_delta S hb hK hu hq
  obtain ⟨hle, -, -⟩ := h.dewh4_lam_of_mem_delta S hb hK hu he
  have hz : q * e ∈ zGroup Ω := by
    refine (h.lam_eq_zero_iff S (mul_mem hqp hep)).1 (fun x => ?_)
    rw [h.lam_mul S hqp hep x, hlq x, hle x, hfe, ← add_smul]
    rw [(show ∀ t : ZMod 2, t + t = 0 by decide) (dewFun S q x), zero_smul]
  have hmem : q * e ∈ dewDelta K (S.shift b K) ⊓ zGroup Ω :=
    ⟨mul_mem hq he, hz⟩
  rw [h.dewDelta_inf_zGroup (dewh4_dewTwins_shift S hb hK hu)] at hmem
  exact dewh4_zpowers_involution hu.sq hmem

theorem dewh4_edge_mem_delta (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) {K : Subgroup G} (hK : K ∈ Ω)
    {u : G} (hu : IsUniqueInvolution K u) (hKX : K ∉ X) (hKY : K ∉ Y) :
    dewEdge S b X Y ∈ dewDelta K (S.shift b K) := by
  obtain ⟨C⟩ := h.exists_pointCoord S hb
  obtain ⟨c, hc⟩ := h.dagl_mem_iff_coord hb C hK hu
  have hcX : C.coord X u ≠ c := fun e => hKX ((hc X hX).2 e)
  have hcY : C.coord Y u ≠ c := fun e => hKY ((hc Y hY).2 e)
  have hcXY : C.coord X u = C.coord Y u :=
    (show ∀ a d c : ZMod 2, a ≠ c → d ≠ c → a = d by decide) _ _ c hcX hcY
  have hε : dewEps X Y u = 0 := by
    rw [dewh4_dewEps_eq_add h S hb C hX hY u, hcXY]
    exact (show ∀ t : ZMod 2, t + t = 0 by decide) _
  have hu0 : u ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hu⟩
  exact (h.dewEdge_isEdge S hb hX hY hXY).2 u hu0 hu.ne_one hε K ⟨hK, hu⟩ hKX

theorem dewh4_edge_ne (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y X' Y' : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hX' : X' ∈ dewPts S b) (hY' : Y' ∈ dewPts S b)
    (hXY : X ≠ Y) (hX'Y' : X' ≠ Y') (hf : dewEps X Y = dewEps X' Y')
    (hX'X : X' ≠ X) (hX'Y : X' ≠ Y) : dewEdge S b X Y ≠ dewEdge S b X' Y' := by
  intro heq
  obtain ⟨C⟩ := h.exists_pointCoord S hb
  have hf0 : dewEps X Y ≠ 0 := fun h0 => hXY (h.dewh4_eq_of_dewEps_eq_zero S hb C hX hY h0)
  have hgX : dewEps X X' ≠ 0 := fun h0 =>
    hX'X (h.dewh4_eq_of_dewEps_eq_zero S hb C hX hX' h0).symm
  have hgf : dewEps X X' ≠ dewEps X Y := by
    intro e
    apply hX'Y
    apply C.bijOn.injOn hX' hY
    funext z
    have hz := congrFun e z
    rw [dewh4_dewEps_eq_add h S hb C hX hX' z, dewh4_dewEps_eq_add h S hb C hX hY z] at hz
    exact add_left_cancel hz
  obtain ⟨x, hx, hx1, hfx, hgx⟩ := dewh4_exists_kernel_nonvanish
    (h.dewEps_mem_dual S hb hX hY) (h.dewEps_mem_dual S hb hX hX') hf0 hgX hgf
  have hdual := h.dewEps_mem_dual S hb hX hY
  have hfx' : dewEps X' Y' x = 0 := hf ▸ hfx
  obtain ⟨M, hMX', hMx⟩ := h.pt_exists_mem S hX' hx hx1
  have hMΩ : M ∈ Ω := hX'.1 hMX'
  have hMX : M ∉ X := fun hMX =>
    (h.mem_iff_of_dewEps_eq_one S hb hX hX' hgx hMΩ hMx).1 hMX hMX'
  obtain ⟨M', hM'X, hM'x⟩ := h.pt_exists_mem S hX hx hx1
  have hM'Ω : M' ∈ Ω := hX.1 hM'X
  have hM'X' : M' ∉ X' := fun hM'X' =>
    (h.mem_iff_of_dewEps_eq_one S hb hX hX' hgx hM'Ω hM'x).1 hM'X hM'X'
  have heM : dewEdge S b X Y ∈ dewDelta M (S.shift b M) :=
    (h.dewEdge_isEdge S hb hX hY hXY).2 x hx hx1 hfx M ⟨hMΩ, hMx⟩ hMX
  have heM' : dewEdge S b X' Y' ∈ dewDelta M' (S.shift b M') :=
    (h.dewEdge_isEdge S hb hX' hY' hX'Y').2 x hx hx1 hfx' M' ⟨hM'Ω, hM'x⟩ hM'X'
  rw [← heq] at heM'
  have hset : dewEdge S b X Y ∈ edgeSet S b (dewEps X Y) :=
    ⟨(h.dewEdge_isEdge S hb hX hY hXY).1, M, hMΩ, heM⟩
  obtain ⟨hcent, -⟩ := h.edgeSet_centralizes S hb hdual hf0 hset hx hx1 hfx ⟨hMΩ, hMx⟩ heM
  obtain ⟨-, hnon⟩ := h.edgeSet_centralizes S hb hdual hf0 hset hx hx1 hfx ⟨hM'Ω, hM'x⟩ heM'
  have hsh : S.shift b M ∈ X' := (h.pt_shift_mem S hb hX' hMX' b).2 (by simp [dewQb])
  have hM'M : M' ≠ M := fun e => hM'X' (e ▸ hMX')
  have hM'sh : M' ≠ S.shift b M := fun e => hM'X' (e ▸ hsh)
  have hcM' := hcent M' ⟨hM'Ω, hM'x⟩ hM'M hM'sh
  obtain ⟨j, hj, hne⟩ := hnon M' ⟨hM'Ω, hM'x⟩ (Or.inl rfl)
  exact hne (hcM' j hj)

theorem dewh4_edge_mul_eq_u (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) {X Y X' Y' : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hX' : X' ∈ dewPts S b)
    (hY' : Y' ∈ dewPts S b) (hXY : X ≠ Y) (hX'Y' : X' ≠ Y') (hf : dewEps X Y = dewEps X' Y')
    (hX'X : X' ≠ X) (hX'Y : X' ≠ Y) (hKX : K ∉ X) (hKY : K ∉ Y) (hKX' : K ∉ X')
    (hKY' : K ∉ Y') : dewEdge S b X Y * dewEdge S b X' Y' = u := by
  have hE1 := h.dewh4_edge_mem_delta S hb hX hY hXY hK hu hKX hKY
  have hE2 := h.dewh4_edge_mem_delta S hb hX' hY' hX'Y' hK hu hKX' hKY'
  have hfe : dewFun S (dewEdge S b X' Y') = dewFun S (dewEdge S b X Y) := by
    rw [(h.dewEdge_isEdge S hb hX' hY' hX'Y').1.2, (h.dewEdge_isEdge S hb hX hY hXY).1.2, hf]
  have hne := h.dewh4_edge_ne S hb hX hY hX' hY' hXY hX'Y' hf hX'X hX'Y
  rcases h.dewh4_mul_mem S hb hK hu hE1 hE2 hfe with h1 | h1
  · exfalso
    apply hne
    have hsq : dewEdge S b X' Y' * dewEdge S b X' Y' = 1 :=
      h.dewA_mul_self S hb (h.dewEdge_isEdge S hb hX' hY' hX'Y').1.1
    calc dewEdge S b X Y = dewEdge S b X Y * (dewEdge S b X' Y' * dewEdge S b X' Y') := by
          rw [hsq, mul_one]
      _ = (dewEdge S b X Y * dewEdge S b X' Y') * dewEdge S b X' Y' := by group
      _ = dewEdge S b X' Y' := by rw [h1, one_mul]
  · exact h1

theorem dewh4_ncard_avoid (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) : {X | X ∈ dewPts S b ∧ K ∉ X}.ncard = 4 := by
  have h1 := h.ncard_dewPts_mem S hb hK
  have h2 := h.ncard_dewPts S hb
  have hunion : {X | X ∈ dewPts S b ∧ K ∈ X} ∪ {X | X ∈ dewPts S b ∧ K ∉ X} = dewPts S b := by
    ext X
    by_cases hK' : K ∈ X <;> simp [hK']
  have hdisj : Disjoint {X | X ∈ dewPts S b ∧ K ∈ X} {X | X ∈ dewPts S b ∧ K ∉ X} := by
    rw [Set.disjoint_left]
    intro X hX1 hX2
    exact hX2.2 hX1.2
  have hsum := Set.ncard_union_eq hdisj
  rw [hunion, h2, h1] at hsum
  omega

theorem dewh4_partner (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) : ∃ Y ∈ dewPts S b, dewEps X Y = f := by
  have key : ∀ a c : ZMod 2, a + (a + c) = c := by decide
  have hsum : C.coord X + f ∈ DE2Hyp.deq2Dual Ω := by
    obtain ⟨hX1, hXout, hXadd⟩ := (C.bijOn.mapsTo hX : C.coord X ∈ DE2Hyp.deq2Dual Ω)
    obtain ⟨hf1, hfout, hfadd⟩ := hf
    refine ⟨?_, ?_, ?_⟩
    · simp [hX1, hf1]
    · intro y hy
      simp [hXout y hy, hfout y hy]
    · intro y hy z hz
      simp only [Pi.add_apply, hXadd y hy z hz, hfadd y hy z hz]
      ring
  obtain ⟨Y, hY, hYc⟩ := C.bijOn.surjOn hsum
  refine ⟨Y, hY, ?_⟩
  funext x
  rw [h.dewh4_dewEps_eq_add S hb C hX hY x, hYc]
  simp only [Pi.add_apply]
  exact key _ _

theorem dewh4_partner_avoid (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) (hKX : K ∉ X) {f : G → ZMod 2}
    (hf : f ∈ DE2Hyp.deq2Dual Ω) (hfu : f u = 0) :
    ∃ Y ∈ dewPts S b, K ∉ Y ∧ dewEps X Y = f := by
  obtain ⟨c, hc⟩ := h.dagl_mem_iff_coord hb C hK hu
  obtain ⟨Y, hY, hXY⟩ := h.dewh4_partner S hb C hX hf
  refine ⟨Y, hY, ?_, hXY⟩
  have hcu : C.coord X u ≠ c := fun e => hKX ((hc X hX).2 e)
  have hYu : C.coord Y u = C.coord X u := by
    have h1 := congrFun hXY u
    rw [h.dewh4_dewEps_eq_add S hb C hX hY u, hfu] at h1
    exact (show ∀ a d : ZMod 2, a + d = 0 → d = a by decide) _ _ h1
  intro hKY
  exact hcu (by rw [← hYu]; exact (hc Y hY).1 hKY)

theorem dewh4_two_avoid (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧ K ∉ X ∧ K ∉ Y := by
  have hcard := h.dewh4_ncard_avoid S hb hK
  have hfin : {X | X ∈ dewPts S b ∧ K ∉ X}.Finite := Set.toFinite _
  obtain ⟨X, hX, Y, hY, hXY⟩ := (Set.one_lt_ncard hfin).1 (by omega)
  exact ⟨X, hX.1, Y, hY.1, hXY, hX.2, hY.2⟩

theorem dewh4_two_pairs (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    {X Y : Set (Subgroup G)} (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y)
    (hKX : K ∉ X) (hKY : K ∉ Y) :
    ∃ X' ∈ dewPts S b, ∃ Y' ∈ dewPts S b, K ∉ X' ∧ K ∉ Y' ∧ X' ≠ X ∧ X' ≠ Y ∧ X' ≠ Y' ∧
      dewEps X' Y' = dewEps X Y := by
  have hfu : dewEps X Y u = 0 := by
    obtain ⟨c, hc⟩ := h.dagl_mem_iff_coord hb C hK hu
    have hcX : C.coord X u ≠ c := fun e => hKX ((hc X hX).2 e)
    have hcY : C.coord Y u ≠ c := fun e => hKY ((hc Y hY).2 e)
    rw [h.dewh4_dewEps_eq_add S hb C hX hY u,
      (show ∀ a d c : ZMod 2, a ≠ c → d ≠ c → a = d by decide) _ _ c hcX hcY]
    exact (show ∀ t : ZMod 2, t + t = 0 by decide) _
  have hcard := h.dewh4_ncard_avoid S hb hK
  have hfin : {X | X ∈ dewPts S b ∧ K ∉ X}.Finite := Set.toFinite _
  have hex : ∃ X' ∈ dewPts S b, K ∉ X' ∧ X' ≠ X ∧ X' ≠ Y := by
    by_contra hno
    push Not at hno
    have hsub : {X | X ∈ dewPts S b ∧ K ∉ X} ⊆ {X, Y} := by
      intro Z hZ
      by_cases hZX : Z = X
      · exact Or.inl hZX
      · exact Or.inr (hno Z hZ.1 hZ.2 hZX)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hXY] at this
    omega
  obtain ⟨X', hX', hKX', hX'X, hX'Y⟩ := hex
  have hf := h.dewEps_mem_dual S hb hX hY
  obtain ⟨Y', hY', hKY', hXY'⟩ := h.dewh4_partner_avoid S hb C hK hu hX' hKX' hf hfu
  refine ⟨X', hX', Y', hY', hKX', hKY', hX'X, hX'Y, ?_, hXY'⟩
  intro e
  apply hXY
  apply h.dewh4_eq_of_dewEps_eq_zero S hb C hX hY
  rw [← hXY', e]
  funext z
  rw [h.dewh4_dewEps_eq_add S hb C hY' hY' z]
  exact (show ∀ t : ZMod 2, t + t = 0 by decide) _

theorem dewh4_delta_le_closure (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) :
    dewDelta K (S.shift b K) ≤
      Subgroup.closure {e | ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧ K ∉ X ∧ K ∉ Y ∧
        e = dewEdge S b X Y} := by
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  obtain ⟨C⟩ := h.exists_pointCoord S hb
  set Cl := Subgroup.closure {e | ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧ K ∉ X ∧ K ∉ Y ∧
        e = dewEdge S b X Y} with hCl
  have hedge : ∀ X ∈ dewPts S b, ∀ Y ∈ dewPts S b, X ≠ Y → K ∉ X → K ∉ Y →
      dewEdge S b X Y ∈ Cl := fun X hX Y hY hXY hKX hKY =>
    Subgroup.subset_closure ⟨X, hX, Y, hY, hXY, hKX, hKY, rfl⟩
  obtain ⟨X₁, hX₁, Y₁, hY₁, hXY₁, hKX₁, hKY₁⟩ := h.dewh4_two_avoid S hb hK
  have hu_mem : u ∈ Cl := by
    obtain ⟨X', hX', Y', hY', hKX', hKY', hX'X, hX'Y, hX'Y', heq⟩ :=
      h.dewh4_two_pairs S hb C hK hu hX₁ hY₁ hXY₁ hKX₁ hKY₁
    have hm := h.dewh4_edge_mul_eq_u S hb hK hu hX₁ hY₁ hX' hY' hXY₁ hX'Y' heq.symm hX'X
      hX'Y hKX₁ hKY₁ hKX' hKY'
    rw [← hm]
    exact Cl.mul_mem (hedge _ hX₁ _ hY₁ hXY₁ hKX₁ hKY₁) (hedge _ hX' _ hY' hX'Y' hKX' hKY')
  intro q hq
  have hqp : q ∈ pCore 2 G := (Subgroup.mem_inf.mp hq).2
  obtain ⟨hlq, hdq, hqu⟩ := h.dewh4_lam_of_mem_delta S hb hK hu hq
  by_cases hq0 : dewFun S q = 0
  · have hzq : q ∈ zGroup Ω := by
      refine (h.lam_eq_zero_iff S hqp).1 (fun x => ?_)
      rw [hlq x, hq0, Pi.zero_apply, zero_smul]
    have hmem : q ∈ dewDelta K (S.shift b K) ⊓ zGroup Ω := ⟨hq, hzq⟩
    rw [h.dewDelta_inf_zGroup (dewh4_dewTwins_shift S hb hK hu)] at hmem
    rcases dewh4_zpowers_involution hu.sq hmem with h1 | h1
    · rw [h1]
      exact Cl.one_mem
    · rw [h1]
      exact hu_mem
  · obtain ⟨Y, hY, hKY, hXY⟩ := h.dewh4_partner_avoid S hb C hK hu hX₁ hKX₁ hdq hqu
    have hX₁Y : X₁ ≠ Y := by
      intro e
      apply hq0
      rw [← hXY, e]
      funext z
      rw [h.dewh4_dewEps_eq_add S hb C hY hY z]
      exact (show ∀ t : ZMod 2, t + t = 0 by decide) _
    have hE1 := h.dewh4_edge_mem_delta S hb hX₁ hY hX₁Y hK hu hKX₁ hKY
    have hfe1 : dewFun S (dewEdge S b X₁ Y) = dewFun S q := by
      rw [(h.dewEdge_isEdge S hb hX₁ hY hX₁Y).1.2, hXY]
    have hsq : dewEdge S b X₁ Y * dewEdge S b X₁ Y = 1 :=
      h.dewA_mul_self S hb (h.dewEdge_isEdge S hb hX₁ hY hX₁Y).1.1
    obtain ⟨X', hX', Y', hY', hKX', hKY', hX'X, hX'Y, hX'Y', heq⟩ :=
      h.dewh4_two_pairs S hb C hK hu hX₁ hY hX₁Y hKX₁ hKY
    have hm := h.dewh4_edge_mul_eq_u S hb hK hu hX₁ hY hX' hY' hX₁Y hX'Y' heq.symm hX'X
      hX'Y hKX₁ hKY hKX' hKY'
    rcases h.dewh4_mul_mem S hb hK hu hE1 hq hfe1.symm with h1 | h1
    · have hqe : q = dewEdge S b X₁ Y := by
        calc q = dewEdge S b X₁ Y * (dewEdge S b X₁ Y * q) := by
              rw [← mul_assoc, hsq, one_mul]
          _ = dewEdge S b X₁ Y := by rw [h1, mul_one]
      rw [hqe]
      exact hedge _ hX₁ _ hY hX₁Y hKX₁ hKY
    · have hqe : q = dewEdge S b X' Y' := by
        apply mul_left_cancel (a := dewEdge S b X₁ Y)
        rw [h1, hm]
      rw [hqe]
      exact hedge _ hX' _ hY' hX'Y' hKX' hKY'

omit h in
theorem dewh4_isUnique_conj_iff (g x : G) (L : Subgroup G) :
    IsUniqueInvolution L (g * x * g⁻¹) ↔ IsUniqueInvolution (conjSub g⁻¹ L) x := by
  constructor
  · intro hL
    have := hL.conj g⁻¹
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  · intro hM
    have := hM.conj g
    rwa [conjSub_conjSub_inv] at this

omit h in
theorem dewh4_dewEps_conj (g x : G) (X Y : Set (Subgroup G)) :
    dewEps (conjSub g '' X) (conjSub g '' Y) (g * x * g⁻¹) = dewEps X Y x := by
  have hiff : (∃ L ∈ conjSub g '' X, IsUniqueInvolution L (g * x * g⁻¹) ∧
      L ∉ conjSub g '' Y) ↔ (∃ L ∈ X, IsUniqueInvolution L x ∧ L ∉ Y) := by
    constructor
    · rintro ⟨L, hL, hu, hLY⟩
      refine ⟨conjSub g⁻¹ L, mem_conjSub_image_iff.mp hL,
        (dewh4_isUnique_conj_iff g x L).mp hu, fun hm => hLY (mem_conjSub_image_iff.mpr hm)⟩
    · rintro ⟨L', hL', hu, hLY⟩
      refine ⟨conjSub g L', ⟨L', hL', rfl⟩, hu.conj g, ?_⟩
      intro hm
      apply hLY
      rw [mem_conjSub_image_iff, conjSub_inv_conjSub] at hm
      exact hm
  unfold dewEps
  by_cases hE : ∃ L ∈ X, IsUniqueInvolution L x ∧ L ∉ Y
  · rw [if_pos (hiff.mpr hE), if_pos hE]
  · rw [if_neg (fun h' => hE (hiff.mp h')), if_neg hE]

omit h in
theorem dewh4_conj_mem_dewDelta (g : G) {K J : Subgroup G} {e : G}
    (he : e ∈ dewDelta K J) : g * e * g⁻¹ ∈ dewDelta (conjSub g K) (conjSub g J) := by
  unfold dewDelta at he ⊢
  obtain ⟨hsup, hpc⟩ := Subgroup.mem_inf.mp he
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  refine Subgroup.mem_inf.mpr ⟨?_, (inferInstance : (pCore 2 G).Normal).conj_mem e hpc g⟩
  have hmap : conjSub g (K ⊔ J) = conjSub g K ⊔ conjSub g J := by
    unfold conjSub
    exact Subgroup.map_sup _ _ _
  rw [← hmap, mem_conjSub_iff, show g⁻¹ * (g * e * g⁻¹) * g = e by group]
  exact hsup

theorem dewh4_dewFun_conj (S : TwinShift Ω) {e : G} (he : e ∈ pCore 2 G) (g x : G) :
    dewFun S (g * e * g⁻¹) (g * x * g⁻¹) = dewFun S e x := by
  unfold dewFun
  rw [h.lam_conj S he g x]

theorem dewh4_dewEdge_mem (S : TwinShift Ω) {b : Lab2} (X Y : Set (Subgroup G)) :
    dewEdge S b X Y ∈ dewA S b := by
  unfold dewEdge
  split_ifs with hE
  · exact hE.choose_spec.1.1
  · exact (dewA S b).one_mem

omit h in
theorem dewh4_prod_univ_eq_one {A : Type*} [CommGroup A] (ψ : (Fin 3 → ZMod 2) → A)
    (hψ : ∀ u v, ψ (u + v) = ψ u * ψ v) (hψ0 : ψ 0 = 1) :
    ∏ v : Fin 3 → ZMod 2, ψ v = 1 := by
  let φ : Multiplicative (Fin 3 → ZMod 2) →* A :=
    { toFun := fun v => ψ (Multiplicative.toAdd v)
      map_one' := hψ0
      map_mul' := fun a b => hψ _ _ }
  have h1 : (∏ v : Fin 3 → ZMod 2, ψ v) =
      φ (∏ v : Fin 3 → ZMod 2, Multiplicative.ofAdd v) := by
    rw [map_prod]
    rfl
  have h2 : (∏ v : Fin 3 → ZMod 2, Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (∑ v : Fin 3 → ZMod 2, v) := (ofAdd_sum _ _).symm
  have h3 : (∑ v : Fin 3 → ZMod 2, v) = 0 := by decide
  rw [h1, h2, h3, ofAdd_zero, map_one]

omit h in
theorem dewh4_shift_dew1V (S : TwinShift Ω) {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) (m : Lab2) :
    S.shift m K ∈ Ω ∧ IsUniqueInvolution (S.shift m K) u := by
  obtain ⟨z, hz, hz'⟩ := (S.shift_mem m K hK).2
  exact ⟨(S.shift_mem m K hK).1, hz.eq hu ▸ hz'⟩

theorem dewh4_exists_avoid_member (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) :
    ∃ M ∈ Ω, IsUniqueInvolution M x ∧ M ∉ X := by
  obtain ⟨M, hM⟩ := h.exists_mem_dew1V hx hx1
  obtain ⟨hMΩ, hMu⟩ := hM
  by_cases hMX : M ∈ X
  · obtain ⟨c, hc⟩ := lab2_exists_dewQb_one b hb
    refine ⟨S.shift c M, (dewh4_shift_dew1V S hMΩ hMu c).1,
      (dewh4_shift_dew1V S hMΩ hMu c).2, fun hcX => ?_⟩
    have := (h.pt_shift_mem S hb hX hMX c).1 hcX
    rw [hc] at this
    exact one_ne_zero this
  · exact ⟨M, hMΩ, hMu, hMX⟩

omit h in
theorem dewh4_count_vec {lam : (Fin 3 → ZMod 2) → ZMod 2}
    (hadd : ∀ u v, lam (u + v) = lam u + lam v) (hne : ∃ v, lam v ≠ 0) :
    (Finset.univ.filter (fun v => lam v = 0)).card = 4 := by
  classical
  obtain ⟨v₁, hv₁⟩ := hne
  have hv₁1 : lam v₁ = 1 := (show ∀ t : ZMod 2, t ≠ 0 → t = 1 by decide) _ hv₁
  have hcard : (Finset.univ.filter (fun v => lam v = 0)).card =
      (Finset.univ.filter (fun v => ¬ lam v = 0)).card := by
    apply Finset.card_bij (fun v _ => v + v₁)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hadd, hv, hv₁1]
      decide
    · intro u _ v _ huv
      exact add_right_cancel huv
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hvv : ∀ w : Fin 3 → ZMod 2, w + w = 0 := by decide
      refine ⟨w + v₁, ?_, by show w + v₁ + v₁ = w; rw [add_assoc, hvv, add_zero]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hadd, hv₁1]
      rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) (lam w) with h0 | h1
      · exact absurd h0 hw
      · rw [h1]
        decide
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 3 → ZMod 2)))
    (fun v => lam v = 0)
  rw [Finset.card_univ, Fintype.card_fun] at htot
  simp only [Fintype.card_fin, ZMod.card] at htot
  omega

omit h in
theorem dewh4_deq2Dual_add {f g : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω)
    (hg : g ∈ DE2Hyp.deq2Dual Ω) : f + g ∈ DE2Hyp.deq2Dual Ω := by
  obtain ⟨hf1, hfout, hfadd⟩ := hf
  obtain ⟨hg1, hgout, hgadd⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · simp [hf1, hg1]
  · intro y hy
    simp [hfout y hy, hgout y hy]
  · intro y hy z hz
    simp only [Pi.add_apply, hfadd y hy z hz, hgadd y hy z hz]
    ring

theorem dewh4_basis (S : TwinShift Ω) {b : Lab2} :
    ∃ ψ : (Fin 3 → ZMod 2) → dewA S b, (∀ u v, ψ (u + v) = ψ u * ψ v) ∧ ψ 0 = 1 ∧
      Function.Injective ψ ∧ (∀ v, ((ψ v : dewA S b) : G) ∈ zGroup Ω) ∧
      ∀ x : dewA S b, (x : G) ∈ zGroup Ω → ∃ v, ψ v = x := by
  obtain ⟨e, he⟩ := TL4.exists_e8Basis (E := zGroup Ω) (fun x hx => h.zGroup_mul_self x hx)
    h.card_zGroup
  refine ⟨fun v => ⟨TL4.e8Coord e v, h.zGroup_le_dewA S b (TL4.e8Coord_mem he v)⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro u v
    exact Subtype.ext (TL4.e8Coord_add he u v)
  · exact Subtype.ext TL4.e8Coord_zero
  · intro u v huv
    exact TL4.e8Coord_injective he (congrArg Subtype.val huv)
  · intro v
    exact TL4.e8Coord_mem he v
  · intro x hx
    obtain ⟨v, hv⟩ := TL4.exists_e8Coord_eq he hx
    exact ⟨v, Subtype.ext hv⟩

theorem dewh4_sigma (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (C : DewPointCoord S b)
    {X₀ : Set (Subgroup G)} (hX₀ : X₀ ∈ dewPts S b) {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) :
    ∃ p₁ ∈ dewPts S b, ∃ p₂ ∈ dewPts S b, ∃ p₃ ∈ dewPts S b, p₁ ≠ X₀ ∧ p₂ ≠ X₀ ∧ p₃ ≠ X₀ ∧
      p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      (∀ Y ∈ dewPts S b, Y ≠ X₀ → C.coord Y x = C.coord X₀ x → Y = p₁ ∨ Y = p₂ ∨ Y = p₃) ∧
      C.coord p₁ x = C.coord X₀ x ∧ C.coord p₂ x = C.coord X₀ x ∧
      C.coord p₃ x = C.coord X₀ x ∧ C.coord p₃ = C.coord p₁ + C.coord p₂ + C.coord X₀ ∧
      ∃ M ∈ Ω, IsUniqueInvolution M x ∧
        ∀ Y ∈ dewPts S b, (M ∉ Y ↔ C.coord Y x = C.coord X₀ x) := by
  classical
  obtain ⟨M, hMΩ, hMx, hMX₀⟩ := h.dewh4_exists_avoid_member S hb hX₀ hx hx1
  obtain ⟨cM, hcM⟩ := h.dagl_mem_iff_coord hb C hMΩ hMx
  have hX0c : C.coord X₀ x ≠ cM := fun e => hMX₀ ((hcM X₀ hX₀).2 e)
  have hiff : ∀ Y ∈ dewPts S b, (M ∉ Y ↔ C.coord Y x = C.coord X₀ x) := by
    intro Y hY
    constructor
    · intro hMY
      have hYc : C.coord Y x ≠ cM := fun e => hMY ((hcM Y hY).2 e)
      exact (show ∀ a d c : ZMod 2, a ≠ c → d ≠ c → a = d by decide) _ _ cM hYc hX0c
    · intro e hMY
      apply hX0c
      rw [← e]
      exact (hcM Y hY).1 hMY
  have hB : {Y | Y ∈ dewPts S b ∧ C.coord Y x = C.coord X₀ x}.ncard = 4 := by
    rw [← h.dewh4_ncard_avoid S hb hMΩ]
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hY, e⟩
      exact ⟨hY, (hiff Y hY).2 e⟩
    · rintro ⟨hY, hMY⟩
      exact ⟨hY, (hiff Y hY).1 hMY⟩
  have hX₀B : X₀ ∈ {Y | Y ∈ dewPts S b ∧ C.coord Y x = C.coord X₀ x} := ⟨hX₀, rfl⟩
  have hB' : ({Y | Y ∈ dewPts S b ∧ C.coord Y x = C.coord X₀ x} \ {X₀}).ncard = 3 := by
    rw [Set.ncard_diff_singleton_of_mem hX₀B, hB]
  obtain ⟨p₁, p₂, p₃, h12, h13, h23, hB'eq⟩ := Set.ncard_eq_three.mp hB'
  have hmem : ∀ Y, (Y ∈ dewPts S b ∧ Y ≠ X₀ ∧ C.coord Y x = C.coord X₀ x) ↔
      (Y = p₁ ∨ Y = p₂ ∨ Y = p₃) := by
    intro Y
    have hY : Y ∈ {Y | Y ∈ dewPts S b ∧ C.coord Y x = C.coord X₀ x} \ {X₀} ↔
        Y ∈ ({p₁, p₂, p₃} : Set (Set (Subgroup G))) := by rw [hB'eq]
    rw [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact hY.1 ⟨⟨h1, h3⟩, h2⟩
    · intro hY'
      obtain ⟨⟨h1, h3⟩, h2⟩ := hY.2 hY'
      exact ⟨h1, h2, h3⟩
  obtain ⟨hp1m, hp1ne, hp1x⟩ := (hmem p₁).2 (Or.inl rfl)
  obtain ⟨hp2m, hp2ne, hp2x⟩ := (hmem p₂).2 (Or.inr (Or.inl rfl))
  obtain ⟨hp3m, hp3ne, hp3x⟩ := (hmem p₃).2 (Or.inr (Or.inr rfl))
  have hsum : C.coord p₁ + C.coord p₂ + C.coord X₀ ∈ DE2Hyp.deq2Dual Ω :=
    dewh4_deq2Dual_add (dewh4_deq2Dual_add (C.bijOn.mapsTo hp1m) (C.bijOn.mapsTo hp2m))
      (C.bijOn.mapsTo hX₀)
  obtain ⟨Z, hZ, hZc⟩ := C.bijOn.surjOn hsum
  have hZx : C.coord Z x = C.coord X₀ x := by
    rw [hZc]
    simp only [Pi.add_apply]
    rw [hp1x, hp2x]
    exact (show ∀ t : ZMod 2, t + t + t = t by decide) _
  have hd : C.coord p₃ = C.coord p₁ + C.coord p₂ + C.coord X₀ := by
    by_cases hZX : Z = X₀
    · exfalso
      rw [hZX] at hZc
      have hfun : C.coord p₁ = C.coord p₂ := by
        funext z
        have := congrFun hZc z
        simp only [Pi.add_apply] at this
        exact (show ∀ p q r : ZMod 2, r = p + q + r → p = q by decide) _ _ _ this
      exact h12 (C.bijOn.injOn hp1m hp2m hfun)
    · rcases (hmem Z).1 ⟨hZ, hZX, hZx⟩ with hZ1 | hZ2 | hZ3
      · exfalso
        rw [hZ1] at hZc
        have hfun : C.coord p₂ = C.coord X₀ := by
          funext z
          have := congrFun hZc z
          simp only [Pi.add_apply] at this
          exact (show ∀ p q r : ZMod 2, p = p + q + r → q = r by decide) _ _ _ this
        exact hp2ne (C.bijOn.injOn hp2m hX₀ hfun)
      · exfalso
        rw [hZ2] at hZc
        have hfun : C.coord p₁ = C.coord X₀ := by
          funext z
          have := congrFun hZc z
          simp only [Pi.add_apply] at this
          exact (show ∀ p q r : ZMod 2, q = p + q + r → p = r by decide) _ _ _ this
        exact hp1ne (C.bijOn.injOn hp1m hX₀ hfun)
      · rw [hZ3] at hZc
        exact hZc
  exact ⟨p₁, hp1m, p₂, hp2m, p₃, hp3m, hp1ne, hp2ne, hp3ne, h12, h13, h23,
    fun Y hY hYX hYx => (hmem Y).1 ⟨hY, hYX, hYx⟩, hp1x, hp2x, hp3x, hd, M, hMΩ, hMx, hiff⟩

theorem dewEdge_conj (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X Y : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b) (hXY : X ≠ Y) (g : G) :
    g * dewEdge S b X Y * g⁻¹ = dewEdge S b (conjSub g '' X) (conjSub g '' Y) := by
  have hgX : conjSub g '' X ∈ dewPts S b := h.isDewPoint_conjSub S hX g
  have hgY : conjSub g '' Y ∈ dewPts S b := h.isDewPoint_conjSub S hY g
  have hgXY : conjSub g '' X ≠ conjSub g '' Y := fun e =>
    hXY (Set.image_injective.mpr (conjSub_injective g) e)
  have hE := h.dewEdge_isEdge S hb hX hY hXY
  set e := dewEdge S b X Y with he
  have hA : e ∈ dewA S b := hE.1.1
  have hepc : e ∈ pCore 2 G := dewA_le_pCore S b hA
  have hdewA' : g * e * g⁻¹ ∈ dewA S b := (h.dewA_normal S b).conj_mem e hA g
  have hefun : dewFun S e = dewEps X Y := hE.1.2
  have hfun : dewFun S (g * e * g⁻¹) = dewEps (conjSub g '' X) (conjSub g '' Y) := by
    funext x'
    obtain ⟨x, rfl⟩ : ∃ x, x' = g * x * g⁻¹ := ⟨g⁻¹ * x' * g, by group⟩
    rw [h.dewh4_dewFun_conj S hepc g x, dewh4_dewEps_conj g x X Y]
    exact congrFun hefun x
  have hIsEdge : IsEdge S b (conjSub g '' X) (conjSub g '' Y) (g * e * g⁻¹) := by
    refine ⟨?_, ?_⟩
    · exact ⟨hdewA', hfun⟩
    · intro x hx hx1 hx' M hM hMX
      obtain ⟨hMΩ, hMu⟩ := hM
      obtain ⟨x₀, hx₀def⟩ : ∃ x₀, x₀ = g⁻¹ * x * g := ⟨_, rfl⟩
      have hxeq : x = g * x₀ * g⁻¹ := by rw [hx₀def]; group
      have hx₀ : x₀ ∈ zGroup Ω := by
        have := h.zGroup_normal.conj_mem x hx g⁻¹
        rw [inv_inv] at this
        rw [hx₀def]
        exact this
      have hx₀1 : x₀ ≠ 1 := by
        intro h1
        apply hx1
        rw [hxeq, h1]
        group
      have hε₀ : dewEps X Y x₀ = 0 := by
        rw [← dewh4_dewEps_conj g x₀ X Y, ← hxeq]
        exact hx'
      have hMx : IsUniqueInvolution M (g * x₀ * g⁻¹) := by
        rw [← hxeq]
        exact hMu
      have hM₀ : IsUniqueInvolution (conjSub g⁻¹ M) x₀ :=
        (dewh4_isUnique_conj_iff g x₀ M).mp hMx
      have hM₀Ω : conjSub g⁻¹ M ∈ Ω := S.conj_mem g⁻¹ M hMΩ
      have hM₀X : conjSub g⁻¹ M ∉ X := fun hc => hMX (mem_conjSub_image_iff.mpr hc)
      have hmem := (h.dewEdge_isEdge S hb hX hY hXY).2 x₀ hx₀ hx₀1 hε₀ (conjSub g⁻¹ M)
        ⟨hM₀Ω, hM₀⟩ hM₀X
      have hc := dewh4_conj_mem_dewDelta g hmem
      rw [← S.shift_conj b g _ hM₀Ω, conjSub_conjSub_inv] at hc
      exact hc
  exact (h.dewEdge_eq S hb hgX hgY hgXY hIsEdge).symm

theorem dewEdge_prod_eq_one (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X₀ : Set (Subgroup G)}
    (hX₀ : X₀ ∈ dewPts S b) (l : List (Set (Subgroup G))) (hl : l.Nodup)
    (hlmem : ∀ Y ∈ l, Y ∈ dewPts S b ∧ Y ≠ X₀) (hlen : l.length = 7) :
    (l.map (dewEdge S b X₀)).prod = 1 := by
  classical
  obtain ⟨C⟩ := h.exists_pointCoord S hb
  letI : CommGroup (dewA S b) :=
    { (inferInstance : Group (dewA S b)) with
      mul_comm := fun a c => Subtype.ext (h.dewA_comm S hb a.2 c.2) }
  haveI : Fintype (dewPts S b) := Fintype.ofFinite _
  set P : Finset (Set (Subgroup G)) := (dewPts S b).toFinset with hPdef
  have hmemP : ∀ Y, Y ∈ P ↔ Y ∈ dewPts S b := fun Y => Set.mem_toFinset
  have hPcard : P.card = 8 := by
    rw [hPdef, ← Set.ncard_eq_toFinset_card' (dewPts S b)]
    exact h.ncard_dewPts S hb
  have hX₀P : X₀ ∈ P := (hmemP X₀).2 hX₀
  set T : Finset (Set (Subgroup G)) := P.erase X₀ with hTdef
  have hmemT : ∀ Y, Y ∈ T ↔ Y ∈ dewPts S b ∧ Y ≠ X₀ := by
    intro Y
    rw [hTdef, Finset.mem_erase, hmemP]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  have hTcard : T.card = 7 := by
    rw [hTdef, Finset.card_erase_of_mem hX₀P, hPcard]
  have hlT : l.toFinset = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro Y hY
      rw [List.mem_toFinset] at hY
      rw [hmemT]
      exact hlmem Y hY
    · rw [hTcard, List.toFinset_card_of_nodup hl, hlen]
  let tA : Set (Subgroup G) → dewA S b :=
    fun Y => ⟨dewEdge S b X₀ Y, h.dewh4_dewEdge_mem S X₀ Y⟩
  have htA_sq : ∀ Y, tA Y * tA Y = 1 := fun Y =>
    Subtype.ext (h.dewA_mul_self S hb (h.dewh4_dewEdge_mem S X₀ Y))
  have htA_cube : ∀ Y, tA Y ^ 3 = tA Y := fun Y => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, htA_sq Y, one_mul]
  obtain ⟨ψ, hψmul, hψ0, hψinj, hψmem, hψsurj⟩ := h.dewh4_basis S (b := b)
  have hψne : ∀ v, v ≠ 0 → ((ψ v : dewA S b) : G) ≠ 1 := by
    intro v hv h1
    apply hv
    apply hψinj
    rw [hψ0]
    exact Subtype.ext h1
  have hstep1 : ∀ v ∈ Finset.univ.erase (0 : Fin 3 → ZMod 2),
      ∏ Y ∈ T.filter (fun Y => C.coord Y ((ψ v : dewA S b) : G) =
        C.coord X₀ ((ψ v : dewA S b) : G)), tA Y = ψ v := by
    intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, hX₁, hX₂, hX₃, h12, h13, h23, hcover, hc₁, hc₂, hc₃,
      hd, M, hMΩ, hMx, hiffM⟩ := h.dewh4_sigma S hb C hX₀ (hψmem v) (hψne v hv0)
    have hfilter : T.filter (fun Y => C.coord Y ((ψ v : dewA S b) : G) =
        C.coord X₀ ((ψ v : dewA S b) : G)) = {p₁, p₂, p₃} := by
      ext Y
      rw [Finset.mem_filter, hmemT]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hY, hYX⟩, hYx⟩
        exact hcover Y hY hYX hYx
      · rintro (rfl | rfl | rfl)
        · exact ⟨⟨hp₁, hX₁⟩, hc₁⟩
        · exact ⟨⟨hp₂, hX₂⟩, hc₂⟩
        · exact ⟨⟨hp₃, hX₃⟩, hc₃⟩
    rw [hfilter, Finset.prod_insert (show p₁ ∉ ({p₂, p₃} : Finset (Set (Subgroup G))) by
      simp [h12, h13]), Finset.prod_pair h23]
    apply Subtype.ext
    have hT1 : dewEdge S b X₀ p₁ * dewEdge S b p₁ p₂ = dewEdge S b X₀ p₂ :=
      h.dewEdge_trans S hb hX₀ hp₁ hp₂ hX₁.symm h12 hX₂.symm
    have he1 : dewEdge S b X₀ p₁ * dewEdge S b X₀ p₁ = 1 :=
      h.dewA_mul_self S hb (h.dewh4_dewEdge_mem S X₀ p₁)
    have hf : dewEps p₁ p₂ = dewEps X₀ p₃ := by
      funext z
      rw [h.dewh4_dewEps_eq_add S hb C hp₁ hp₂ z, h.dewh4_dewEps_eq_add S hb C hX₀ hp₃ z]
      have hz := congrFun hd z
      simp only [Pi.add_apply] at hz
      rw [hz]
      exact (show ∀ p q r : ZMod 2, p + q = r + (p + q + r) by decide) _ _ _
    have hE6 : dewEdge S b p₁ p₂ * dewEdge S b X₀ p₃ = ((ψ v : dewA S b) : G) :=
      h.dewh4_edge_mul_eq_u S hb hMΩ hMx hp₁ hp₂ hX₀ hp₃ h12 hX₃.symm hf hX₁.symm hX₂.symm
        ((hiffM p₁ hp₁).2 hc₁) ((hiffM p₂ hp₂).2 hc₂)
        ((hiffM X₀ hX₀).2 rfl) ((hiffM p₃ hp₃).2 hc₃)
    show dewEdge S b X₀ p₁ * (dewEdge S b X₀ p₂ * dewEdge S b X₀ p₃) = _
    rw [← hT1]
    calc dewEdge S b X₀ p₁ * ((dewEdge S b X₀ p₁ * dewEdge S b p₁ p₂) * dewEdge S b X₀ p₃)
        = (dewEdge S b X₀ p₁ * dewEdge S b X₀ p₁) * (dewEdge S b p₁ p₂ * dewEdge S b X₀ p₃) := by
          simp only [mul_assoc]
      _ = _ := by rw [he1, one_mul, hE6]
  have hcount : ∀ Y ∈ T, ((Finset.univ.erase (0 : Fin 3 → ZMod 2)).filter (fun v =>
      C.coord Y ((ψ v : dewA S b) : G) = C.coord X₀ ((ψ v : dewA S b) : G))).card = 3 := by
    intro Y hY
    rw [hmemT] at hY
    have hYd : C.coord Y ∈ DE2Hyp.deq2Dual Ω := C.bijOn.mapsTo hY.1
    have hXd : C.coord X₀ ∈ DE2Hyp.deq2Dual Ω := C.bijOn.mapsTo hX₀
    obtain ⟨hY1, hYout, -⟩ := hYd
    obtain ⟨hX1, hXout, -⟩ := hXd
    have hg : C.coord Y + C.coord X₀ ∈ DE2Hyp.deq2Dual Ω :=
      dewh4_deq2Dual_add (C.bijOn.mapsTo hY.1) (C.bijOn.mapsTo hX₀)
    obtain ⟨hg1, hgout, hgadd⟩ := hg
    have hg0 : C.coord Y + C.coord X₀ ≠ 0 := by
      intro h0
      apply hY.2
      apply C.bijOn.injOn hY.1 hX₀
      funext z
      have hz := congrFun h0 z
      simp only [Pi.add_apply, Pi.zero_apply] at hz
      exact (show ∀ p q : ZMod 2, p + q = 0 → p = q by decide) _ _ hz
    have hex : ∃ y ∈ zGroup Ω, (C.coord Y + C.coord X₀) y ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hg0
      funext y
      by_cases hy : y ∈ zGroup Ω
      · exact hno y hy
      · simp [hYout y hy, hXout y hy]
    obtain ⟨y, hy, hgy⟩ := hex
    have hlam : ∃ v : Fin 3 → ZMod 2, (C.coord Y + C.coord X₀) ((ψ v : dewA S b) : G) ≠ 0 := by
      obtain ⟨v, hv⟩ := hψsurj ⟨y, h.zGroup_le_dewA S b hy⟩ hy
      exact ⟨v, by rw [hv]; exact hgy⟩
    have hadd : ∀ u v : Fin 3 → ZMod 2,
        (C.coord Y + C.coord X₀) ((ψ (u + v) : dewA S b) : G) =
          (C.coord Y + C.coord X₀) ((ψ u : dewA S b) : G) +
            (C.coord Y + C.coord X₀) ((ψ v : dewA S b) : G) := by
      intro u v
      have hm : ((ψ (u + v) : dewA S b) : G) = ((ψ u : dewA S b) : G) * ((ψ v : dewA S b) : G) := by
        rw [hψmul, Subgroup.coe_mul]
      rw [hm]
      exact hgadd _ (hψmem u) _ (hψmem v)
    have hc4 : (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
        (C.coord Y + C.coord X₀) ((ψ v : dewA S b) : G) = 0)).card = 4 :=
      dewh4_count_vec (lam := fun v => (C.coord Y + C.coord X₀) ((ψ v : dewA S b) : G)) hadd hlam
    have hpred : ∀ v : Fin 3 → ZMod 2,
        (C.coord Y ((ψ v : dewA S b) : G) = C.coord X₀ ((ψ v : dewA S b) : G)) ↔
          (C.coord Y + C.coord X₀) ((ψ v : dewA S b) : G) = 0 := by
      intro v
      simp only [Pi.add_apply]
      exact (show ∀ p q : ZMod 2, p = q ↔ p + q = 0 by decide) _ _
    have h0mem : (0 : Fin 3 → ZMod 2) ∈ Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
        (C.coord Y + C.coord X₀) ((ψ v : dewA S b) : G) = 0) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hψ0]
      exact hg1
    rw [Finset.filter_congr (fun v _ => hpred v), Finset.filter_erase,
      Finset.card_erase_of_mem h0mem, hc4]
  have hdouble : ∏ v ∈ Finset.univ.erase (0 : Fin 3 → ZMod 2),
      ∏ Y ∈ T.filter (fun Y => C.coord Y ((ψ v : dewA S b) : G) =
        C.coord X₀ ((ψ v : dewA S b) : G)), tA Y = ∏ Y ∈ T, tA Y := by
    simp only [Finset.prod_filter]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro Y hY
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hcount Y hY,
      htA_cube]
  have hprodψ : ∏ v ∈ Finset.univ.erase (0 : Fin 3 → ZMod 2), ψ v = 1 := by
    have h1 := dewh4_prod_univ_eq_one ψ hψmul hψ0
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (0 : Fin 3 → ZMod 2)), hψ0, mul_one] at h1
    exact h1
  have hkey : ∏ Y ∈ T, tA Y = 1 := by
    rw [← hdouble, Finset.prod_congr rfl (fun v hv => hstep1 v hv), hprodψ]
  have hlist : (l.map tA).prod = 1 := by
    rw [← List.prod_toFinset tA hl, hlT, hkey]
  have hcoe : ∀ l' : List (Set (Subgroup G)),
      (((l'.map tA).prod : dewA S b) : G) = (l'.map (dewEdge S b X₀)).prod := by
    intro l'
    induction l' with
    | nil => rfl
    | cons a l' ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Subgroup.coe_mul, ih]
  rw [← hcoe l, hlist]
  rfl

theorem closure_dewEdge (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) :
    Subgroup.closure {e | ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧ e = dewEdge S b X Y} =
      dewA S b := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro e ⟨X, hX, Y, hY, hXY, rfl⟩
    exact (h.dewEdge_isEdge S hb hX hY hXY).1.1
  · rw [h.dewA_eq_closure S hb]
    apply (Subgroup.closure_le _).mpr
    rintro e ⟨K, hK, he⟩
    have hsub : Subgroup.closure {e | ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧ K ∉ X ∧
        K ∉ Y ∧ e = dewEdge S b X Y} ≤
        Subgroup.closure {e | ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧
          e = dewEdge S b X Y} :=
      Subgroup.closure_mono (fun e' he' => by
        obtain ⟨X, hX, Y, hY, hXY, -, -, rfl⟩ := he'
        exact ⟨X, hX, Y, hY, hXY, rfl⟩)
    exact hsub (h.dewh4_delta_le_closure S hb hK he)

theorem dewDelta_eq_closure_edges (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) :
    dewDelta K (S.shift b K) =
      Subgroup.closure {e | ∃ X ∈ dewPts S b, ∃ Y ∈ dewPts S b, X ≠ Y ∧ K ∉ X ∧ K ∉ Y ∧
        e = dewEdge S b X Y} := by
  apply le_antisymm (h.dewh4_delta_le_closure S hb hK)
  apply (Subgroup.closure_le _).mpr
  rintro e ⟨X, hX, Y, hY, hXY, hKX, hKY, rfl⟩
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  exact h.dewh4_edge_mem_delta S hb hX hY hXY hK hu hKX hKY

theorem exists_edgeMap (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (P : AGLPts S b) :
    ∃ β : Multiplicative (Fin 8 → ZMod 2) →* G,
      (∀ g : G, g ∈ dewA S b ↔ ∃ f : Multiplicative (Fin 8 → ZMod 2),
        ∑ i, f.toAdd i = 0 ∧ β f = g) ∧
      (∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
        (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)) ∧
      (∀ (g : G) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
        g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((P.σ g).symm i))) ∧
      (∀ K ∈ Ω, ∀ q : G, q ∈ dewDelta K (S.shift b K) ↔
        ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧
          (∀ i, i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∈ X} → f.toAdd i = 0) ∧ β f = q) := by
  classical
  choose pt hpt hlab using fun i : Fin 8 => P.bijOn.surjOn (Set.mem_univ i)
  have hptlab : ∀ X ∈ dewPts S b, pt (P.lab X) = X := fun X hX =>
    P.bijOn.injOn (hpt _) hX (hlab _)
  have hptinj : Function.Injective pt := fun i j hij => by
    rw [← hlab i, ← hlab j, hij]
  have hne : ∀ i j, i ≠ j → pt i ≠ pt j := fun i j hij e => hij (hptinj e)
  let Y : Fin 8 → Fin 8 → G := fun i j => if i = j then 1 else dewEdge S b (pt i) (pt j)
  have hY_ne : ∀ i j, i ≠ j → Y i j = dewEdge S b (pt i) (pt j) := fun i j hij => if_neg hij
  have hY_self : ∀ i, Y i i = 1 := fun i => if_pos rfl
  have hYA : ∀ i j, Y i j ∈ dewA S b := by
    intro i j
    by_cases hij : i = j
    · rw [hij, hY_self]
      exact Subgroup.one_mem _
    · rw [hY_ne i j hij]
      exact (h.dewEdge_isEdge S hb (hpt i) (hpt j) (hne i j hij)).1.1
  have hYsq : ∀ i j, Y i j * Y i j = 1 := fun i j => h.dewA_mul_self S hb (hYA i j)
  have hYsymm : ∀ i j, Y i j = Y j i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · rw [hY_ne i j hij, hY_ne j i (Ne.symm hij)]
      exact h.dewEdge_symm S hb (hpt i) (hpt j) (hne i j hij)
  have hYcyc : ∀ i j k, Y i j * Y j k = Y i k := by
    intro i j k
    by_cases hij : i = j
    · rw [hij, hY_self, one_mul]
    by_cases hjk : j = k
    · rw [hjk, hY_self, mul_one]
    by_cases hik : i = k
    · subst hik
      rw [← hYsymm i j, hYsq, hY_self]
    · rw [hY_ne i j hij, hY_ne j k hjk, hY_ne i k hik]
      exact h.dewEdge_trans S hb (hpt i) (hpt j) (hpt k) (hne i j hij) (hne j k hjk)
        (hne i k hik)
  have hYprod : Y 0 1 * Y 0 2 * Y 0 3 * Y 0 4 * Y 0 5 * Y 0 6 * Y 0 7 = 1 := by
    have hnz : ∀ k : Fin 8, k ∈ ([1, 2, 3, 4, 5, 6, 7] : List (Fin 8)) → k ≠ 0 := by decide
    have hl := h.dewEdge_prod_eq_one S hb (hpt 0) (([1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map pt)
      (List.Nodup.map hptinj (by decide))
      (fun Y' hY' => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hY'
        exact ⟨hpt k, hne k 0 (hnz k hk)⟩)
      rfl
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hl
    rw [hY_ne 0 1 (by decide), hY_ne 0 2 (by decide), hY_ne 0 3 (by decide),
      hY_ne 0 4 (by decide), hY_ne 0 5 (by decide), hY_ne 0 6 (by decide),
      hY_ne 0 7 (by decide)]
    simpa only [mul_assoc] using hl
  have hYgen : Subgroup.closure {x | ∃ i j, x = Y i j} = dewA S b := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, j, rfl⟩
      exact hYA i j
    · rw [← h.closure_dewEdge S hb, Subgroup.closure_le]
      rintro _ ⟨X, hX, Y', hY', hXY, rfl⟩
      apply Subgroup.subset_closure
      have hne' : P.lab X ≠ P.lab Y' := fun e => hXY (by rw [← hptlab X hX, ← hptlab Y' hY', e])
      refine ⟨P.lab X, P.lab Y', ?_⟩
      rw [hY_ne _ _ hne', hptlab X hX, hptlab Y' hY']
  have hΔ : ∀ K ∈ Ω, dewDelta K (S.shift b K) = Subgroup.closure
      {x | ∃ i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∉ X},
        ∃ j ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∉ X}, x = Y i j} := by
    intro K hK
    rw [h.dewDelta_eq_closure_edges S hb hK]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨X, hX, Y', hY', hXY, hKX, hKY, rfl⟩
      apply Subgroup.subset_closure
      have hne' : P.lab X ≠ P.lab Y' := fun e => hXY (by rw [← hptlab X hX, ← hptlab Y' hY', e])
      refine ⟨P.lab X, ⟨X, ⟨hX, hKX⟩, rfl⟩, P.lab Y', ⟨Y', ⟨hY', hKY⟩, rfl⟩, ?_⟩
      rw [hY_ne _ _ hne', hptlab X hX, hptlab Y' hY']
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, ⟨X, ⟨hX, hKX⟩, rfl⟩, j, ⟨X', ⟨hX', hKX'⟩, rfl⟩, rfl⟩
      by_cases hXX : X = X'
      · subst hXX
        rw [hY_self]
        exact Subgroup.one_mem _
      · apply Subgroup.subset_closure
        have hne' : P.lab X ≠ P.lab X' := fun e => hXX (P.bijOn.injOn hX hX' e)
        refine ⟨X, hX, X', hX', hXX, hKX, hKX', ?_⟩
        rw [hY_ne _ _ hne', hptlab X hX, hptlab X' hX']
  have hYconj : ∀ g : G, ∀ i j, g * Y i j * g⁻¹ = Y (P.σ g i) (P.σ g j) := by
    intro g i j
    by_cases hij : i = j
    · rw [hij, hY_self, hY_self]
      group
    · have hij' : P.σ g i ≠ P.σ g j := fun e => hij ((P.σ g).injective e)
      rw [hY_ne i j hij, hY_ne _ _ hij', h.dewEdge_conj S hb (hpt i) (hpt j) (hne i j hij) g]
      have hc : ∀ k, conjSub g '' pt k = pt (P.σ g k) := by
        intro k
        apply P.bijOn.injOn (h.isDewPoint_conjSub S (hpt k) g) (hpt _)
        rw [P.equivariant g (pt k) (hpt k), hlab, hlab]
      rw [hc, hc]
  obtain ⟨β, hβpair, hβA, hβker, hβT⟩ := dewh_vecMap (fun a ha => h.dewA_mul_self S hb ha)
    (fun a ha b' hb' => h.dewA_comm S hb ha hb') (h.card_dewA S hb) Y hYA hY_self hYcyc hYprod
    hYgen
  refine ⟨β, hβA, hβker, fun g f hf => dewh_vecMap_conj β Y hβpair g (P.σ g) (hYconj g) f hf,
    fun K hK q => ?_⟩
  rw [hΔ K hK, hβT]
  constructor
  · rintro ⟨f, hf, hfT, hfq⟩
    refine ⟨f, hf, fun i hi => ?_, hfq⟩
    obtain ⟨X, ⟨hX, hKX⟩, rfl⟩ := hi
    apply hfT
    rintro ⟨X', ⟨hX', hKX'⟩, hlabeq⟩
    exact hKX' ((P.bijOn.injOn hX' hX hlabeq) ▸ hKX)
  · rintro ⟨f, hf, hfT, hfq⟩
    refine ⟨f, hf, fun i hi => ?_, hfq⟩
    apply hfT
    have hK' : K ∈ pt i := by
      by_contra hKn
      exact hi ⟨pt i, ⟨hpt i, hKn⟩, hlab i⟩
    exact ⟨pt i, ⟨hpt i, hK'⟩, hlab i⟩

omit h in
private theorem dewh5_seven_fixed_unique {s : Equiv.Perm (Fin 8)} (hs7 : s ^ 7 = 1)
    (hs_ne : s ≠ 1) :
    ∃ p : Fin 8, s p = p ∧ ∀ x, s x = x → x = p := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7 : s ^ (7 ^ 1) = 1 := by rw [pow_one]; exact hs7
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := (⇑s : Function.End (Fin 8))) (p := 7)
    (n := 1) (by
      show (⇑s : Fin 8 → Fin 8)^[7 ^ 1] = id
      rw [Equiv.Perm.iterate_eq_pow, h7]
      rfl)
  have hset : Function.fixedPoints (⇑s : Function.End (Fin 8)) =
      ↑(Finset.univ.filter fun x => s x = x) := by
    ext x
    simp [Function.fixedPoints, Function.IsFixedPt]
  have h8 : Nat.card (Fin 8) = 8 := by simp
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h8, hset, Nat.card_coe_set_eq,
    Set.ncard_coe_finset] at hmod
  have hle : (Finset.univ.filter fun x => s x = x).card ≤ 8 := by
    have := Finset.card_le_univ (Finset.univ.filter fun x => s x = x)
    simpa using this
  have hne8 : (Finset.univ.filter fun x => s x = x).card ≠ 8 := by
    intro h8
    apply hs_ne
    have hall : Finset.univ.filter (fun x => s x = x) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h8)
    ext x
    have hx : x ∈ Finset.univ.filter (fun x => s x = x) := by rw [hall]; exact Finset.mem_univ x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  have h1 : (Finset.univ.filter fun x => s x = x).card = 1 := by
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  refine ⟨p, ?_, ?_⟩
  · have : p ∈ Finset.univ.filter (fun x => s x = x) := by
      rw [hp]; exact Finset.mem_singleton_self p
    simpa using this
  · intro x hx
    have : x ∈ Finset.univ.filter (fun x => s x = x) := by simpa using hx
    rw [hp] at this
    simpa using this

omit h in
private theorem dewh5_card_mul_le {M Δ V : Subgroup G} (hΔ : Δ ≤ M) (hV : V ≤ M)
    (hdisj : Δ ⊓ V = ⊥) : Nat.card Δ * Nat.card V ≤ Nat.card M := by
  let f : Δ × V → M := fun p => ⟨(p.1 : G) * (p.2 : G), M.mul_mem (hΔ p.1.2) (hV p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨d, hd⟩, ⟨v, hv⟩⟩ ⟨⟨d', hd'⟩, ⟨v', hv'⟩⟩ hf
    have h1 : d * v = d' * v' := congrArg Subtype.val hf
    have h2 : d'⁻¹ * d = v' * v⁻¹ := by
      calc d'⁻¹ * d = d'⁻¹ * (d * v) * v⁻¹ := by group
        _ = d'⁻¹ * (d' * v') * v⁻¹ := by rw [h1]
        _ = v' * v⁻¹ := by group
    have h3 : d'⁻¹ * d ∈ Δ ⊓ V :=
      ⟨Δ.mul_mem (Δ.inv_mem hd') hd, h2 ▸ V.mul_mem hv' (V.inv_mem hv)⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have hdd : d = d' := (inv_mul_eq_one.mp h3).symm
    subst hdd
    have h4 : v = v' := mul_left_cancel h1
    subst h4
    rfl
  have := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_prod] using this

omit h in
private theorem dewh5_mul_mem_of_card {M Δ V : Subgroup G} (hΔ : Δ ≤ M) (hV : V ≤ M)
    (hdisj : Δ ⊓ V = ⊥) (hcard : Nat.card Δ * Nat.card V = Nat.card M) {x : G} (hx : x ∈ M) :
    ∃ d ∈ Δ, ∃ v ∈ V, x = d * v := by
  let f : Δ × V → M := fun p => ⟨(p.1 : G) * (p.2 : G), M.mul_mem (hΔ p.1.2) (hV p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨d, hd⟩, ⟨v, hv⟩⟩ ⟨⟨d', hd'⟩, ⟨v', hv'⟩⟩ hf
    have h1 : d * v = d' * v' := congrArg Subtype.val hf
    have h2 : d'⁻¹ * d = v' * v⁻¹ := by
      calc d'⁻¹ * d = d'⁻¹ * (d * v) * v⁻¹ := by group
        _ = d'⁻¹ * (d' * v') * v⁻¹ := by rw [h1]
        _ = v' * v⁻¹ := by group
    have h3 : d'⁻¹ * d ∈ Δ ⊓ V :=
      ⟨Δ.mul_mem (Δ.inv_mem hd') hd, h2 ▸ V.mul_mem hv' (V.inv_mem hv)⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have hdd : d = d' := (inv_mul_eq_one.mp h3).symm
    subst hdd
    have h4 : v = v' := mul_left_cancel h1
    subst h4
    rfl
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  obtain ⟨⟨d, v⟩, hdv⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨d, d.2, v, v.2, (congrArg Subtype.val hdv).symm⟩

omit h in
private theorem dewh5_conjSub_one_image (X : Set (Subgroup G)) : conjSub (1 : G) '' X = X := by
  have e : conjSub (1 : G) = fun K => K := funext conjSub_one
  rw [e, Set.image_id']

private def dewh5_stab (X : Set (Subgroup G)) : Subgroup G where
  carrier := {g | conjSub g '' X = X}
  one_mem' := by
    show conjSub 1 '' X = X
    exact dewh5_conjSub_one_image X
  mul_mem' := by
    intro a c ha hc
    show conjSub (a * c) '' X = X
    rw [conjSub_image_mul, hc, ha]
  inv_mem' := by
    intro a ha
    show conjSub a⁻¹ '' X = X
    calc conjSub a⁻¹ '' X = conjSub a⁻¹ '' (conjSub a '' X) := by rw [ha]
      _ = conjSub (a⁻¹ * a) '' X := (conjSub_image_mul _ _ _).symm
      _ = X := by rw [inv_mul_cancel]; exact dewh5_conjSub_one_image X

omit h in
private theorem dewh5_mem_stab {X : Set (Subgroup G)} {g : G} :
    g ∈ dewh5_stab X ↔ conjSub g '' X = X := Iff.rfl

private theorem dewh5_le_stab (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) : pSpan X ≤ dewh5_stab X := by
  refine pSpan_le fun K hK => ?_
  have hKΩ : K ∈ Ω := (show IsDewPoint S b X from hX).1 hK
  have hfix : ∀ k ∈ K, conjSub k '' X = X :=
    (h.forall_conjSub_image_eq_iff_mem S hb (show IsDewPoint S b X from hX) hKΩ).mpr hK
  intro k hk
  exact hfix k hk

private theorem dewh5_dewA_le_stab (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) : dewA S b ≤ dewh5_stab X := by
  intro q hq
  exact dewh5_mem_stab.mpr
    ((h.conjSub_image_eq_iff S hb (show IsDewPoint S b X from hX) (dewA_le_pCore S b hq)).mpr hq)

private theorem dewh5_stab_sup (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) : dewh5_stab X ⊔ pCore 2 G = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hgX : IsDewPoint S b (conjSub g '' X) :=
    h.isDewPoint_conjSub S (show IsDewPoint S b X from hX) g
  obtain ⟨q, hq, hqX⟩ :=
    h.exists_pCore_conjSub_image S hb (show IsDewPoint S b X from hX) hgX
  have hmem : q⁻¹ * g ∈ dewh5_stab X := by
    rw [dewh5_mem_stab, conjSub_image_mul, ← hqX, ← conjSub_image_mul, inv_mul_cancel]
    exact dewh5_conjSub_one_image X
  have hg : g = q * (q⁻¹ * g) := by group
  rw [hg, sup_comm]
  exact Subgroup.mul_mem_sup hq hmem

private theorem dewh5_card_G (S : TwinShift Ω) {b' : Lab2} (hb' : b' ≠ 0) :
    Nat.card G = 86016 := by
  obtain ⟨P⟩ := h.exists_aglPts S hb'
  have hk := Subgroup.card_mul_index P.σ.ker
  rw [Subgroup.index_ker, P.ker_eq, P.range_eq, h.card_dewA S hb', h.dagl_card_agl32] at hk
  omega

private theorem dewh5_index_Q (S : TwinShift Ω) {b' : Lab2} (hb' : b' ≠ 0) :
    (pCore 2 G).index = 168 := by
  have hG := h.dewh5_card_G S hb'
  have hk := Subgroup.index_mul_card (pCore 2 G)
  rw [h.card_pCore_eq, hG] at hk
  omega

private theorem dewh5_relIndex_stab (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) :
    (dewA S b).relIndex (dewh5_stab X) = 168 := by
  haveI : (pCore 2 G).Normal := pCore_normal
  have hQS : pCore 2 G ⊓ dewh5_stab X = dewA S b := by
    apply le_antisymm
    · rintro q ⟨hq, hqS⟩
      exact (h.conjSub_image_eq_iff S hb (show IsDewPoint S b X from hX) hq).mp
        (dewh5_mem_stab.mp hqS)
    · intro q hq
      exact ⟨dewA_le_pCore S b hq, h.dewh5_dewA_le_stab S hb hX hq⟩
  have h1 := Subgroup.relIndex_sup_right (dewh5_stab X) (pCore 2 G)
  rw [h.dewh5_stab_sup S hb hX, Subgroup.relIndex_top_right, h.dewh5_index_Q S hb'] at h1
  rw [← hQS, Subgroup.inf_relIndex_right]
  omega

private theorem dewh5_dewA_inf_stab (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b ≠ b') {X Y : Set (Subgroup G)} (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b') :
    dewA S b ⊓ (dewh5_stab X ⊓ dewh5_stab Y) = zGroup Ω := by
  apply le_antisymm
  · rintro q ⟨hqA, hqS⟩
    have hqY : q ∈ dewA S b' :=
      (h.conjSub_image_eq_iff S hb' (show IsDewPoint S b' Y from hY) (dewA_le_pCore S b hqA)).mp
        (dewh5_mem_stab.mp hqS.2)
    rw [← h.dewA_inf_dewA S hb hb' hbb']
    exact ⟨hqA, hqY⟩
  · intro d hd
    refine ⟨h.zGroup_le_dewA S b hd, ⟨h.dewh5_dewA_le_stab S hb hX (h.zGroup_le_dewA S b hd),
      h.dewh5_dewA_le_stab S hb' hY (h.zGroup_le_dewA S b' hd)⟩⟩

private theorem dewh5_card_stab_le (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b ≠ b') {X Y : Set (Subgroup G)} (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b') :
    Nat.card ↥(dewh5_stab X ⊓ dewh5_stab Y) ≤ 1344 := by
  haveI : (dewA S b).Normal := h.dewA_normal S b
  have hle : (dewA S b).relIndex (dewh5_stab X ⊓ dewh5_stab Y) ≤ 168 := by
    rw [← Subgroup.relIndex_sup_right (dewh5_stab X ⊓ dewh5_stab Y) (dewA S b)]
    have hsub : (dewh5_stab X ⊓ dewh5_stab Y) ⊔ dewA S b ≤ dewh5_stab X :=
      sup_le inf_le_left (h.dewh5_dewA_le_stab S hb hX)
    have hne : (dewA S b).relIndex (dewh5_stab X) ≠ 0 := by
      rw [h.dewh5_relIndex_stab S hb hb' hX]
      norm_num
    calc (dewA S b).relIndex ((dewh5_stab X ⊓ dewh5_stab Y) ⊔ dewA S b)
        ≤ (dewA S b).relIndex (dewh5_stab X) := Subgroup.relIndex_le_of_le_right hsub hne
      _ = 168 := h.dewh5_relIndex_stab S hb hb' hX
  have hcard := Subgroup.relIndex_mul_card (dewA S b) (dewh5_stab X ⊓ dewh5_stab Y)
  rw [h.dewh5_dewA_inf_stab S hb hb' hbb' hX hY, h.card_zGroup] at hcard
  omega

private theorem dewh5_zGroup_le_pSpan (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) : zGroup Ω ≤ pSpan X := by
  unfold zGroup
  rw [Subgroup.closure_le]
  rintro u ⟨L, hL, hu⟩
  have huD : u ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL, hu⟩
  by_cases hu1 : u = 1
  · rw [hu1]
    exact (pSpan X).one_mem
  · obtain ⟨K, hKX, hKu⟩ := h.pt_exists_mem S (show IsDewPoint S b X from hX) huD hu1
    exact le_pSpan hKX hKu.mem

theorem pSpan_inf_pCore (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) : pSpan X ⊓ pCore 2 G = dewA S b := by
  apply le_antisymm
  · rintro q ⟨hqX, hqQ⟩
    exact (h.conjSub_image_eq_iff S hb (show IsDewPoint S b X from hX) hqQ).mp
      (dewh5_mem_stab.mp (h.dewh5_le_stab S hb hX hqX))
  · intro a ha
    refine ⟨?_, dewA_le_pCore S b ha⟩
    obtain ⟨u, huD, hu1, hfu, -⟩ :=
      h.exists_involution_ker (h.dewFun_mem_dual S ha) (h.dewFun_mem_dual S ha)
    obtain ⟨K, hKX, hKu⟩ := h.pt_exists_mem S (show IsDewPoint S b X from hX) huD hu1
    obtain ⟨d, hd, δ, hδ, rfl⟩ :=
      h.exists_eq_mul_dewDelta S hb ha ((show IsDewPoint S b X from hX).1 hKX) hKu hfu
    have hδ' : δ ∈ (K ⊔ S.shift b K) ⊓ pCore 2 G := hδ
    have hδK : δ ∈ K ⊔ S.shift b K := (Subgroup.mem_inf.mp hδ').1
    refine (pSpan X).mul_mem (h.dewh5_zGroup_le_pSpan S hb hX hd) ?_
    exact sup_le (le_pSpan hKX) (le_pSpan ((show IsDewPoint S b X from hX).2.1 K hKX)) hδK

theorem exists_common_member (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b ≠ b') {X Y : Set (Subgroup G)} (hX : X ∈ dewPts S b) (hY : Y ∈ dewPts S b')
    {x : G} (hx : x ∈ zGroup Ω) (hx1 : x ≠ 1) : ∃ M, M ∈ X ∧ M ∈ Y ∧ M ∈ dew1V Ω x := by
  have hX' : IsDewPoint S b X := hX
  have hY' : IsDewPoint S b' Y := hY
  obtain ⟨K, hKX, hKx⟩ := h.pt_exists_mem S hX' hx hx1
  obtain ⟨J, hJY, hJx⟩ := h.pt_exists_mem S hY' hx hx1
  have hKΩ : K ∈ Ω := hX'.1 hKX
  have hJΩ : J ∈ Ω := hY'.1 hJY
  have hV : dew1V Ω x = twinSet Ω K := dew1V_eq_twinSet hKΩ hKx
  have hJtw : J ∈ twinSet Ω K := by
    rw [← hV]
    exact ⟨hJΩ, hJx⟩
  obtain ⟨m, hm, -⟩ := h.exists_unique_shift S hKΩ hJtw
  obtain ⟨c, hc0, hcm⟩ : ∃ c : Lab2, (c = 0 ∨ c = b) ∧ (c = m ∨ c = m + b') := by
    have key : ∀ b₁ b₂ m₁ : Lab2, b₁ ≠ 0 → b₂ ≠ 0 → b₁ ≠ b₂ →
        ∃ c : Lab2, (c = 0 ∨ c = b₁) ∧ (c = m₁ ∨ c = m₁ + b₂) := by
      decide
    exact key b b' m hb hb' hbb'
  have hMΩ : S.shift c K ∈ dew1V Ω x := by
    rw [hV]
    exact S.shift_mem c K hKΩ
  refine ⟨S.shift c K, ?_, ?_, hMΩ⟩
  · rcases hc0 with h0 | h0
    · rw [h0, S.shift_zero K hKΩ]
      exact hKX
    · rw [h0]
      exact hX'.2.1 K hKX
  · rcases hcm with h0 | h0
    · rw [h0, hm]
      exact hJY
    · rw [h0, show m + b' = b' + m from add_comm m b', S.shift_add b' m K hKΩ, hm]
      exact hY'.2.1 J hJY

private theorem dewh5_L_inf_pCore (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {X : Set (Subgroup G)}
    (hX : X ∈ dewPts S b) {L : Subgroup G} (hLX : L ≤ pSpan X) (hLA : L ⊓ dewA S b = ⊥) :
    L ⊓ pCore 2 G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxS : x ∈ pSpan X ⊓ pCore 2 G := ⟨hLX hx.1, hx.2⟩
  rw [h.pSpan_inf_pCore S hb hX] at hxS
  have hxL : x ∈ L ⊓ dewA S b := ⟨hx.1, hxS⟩
  rw [hLA] at hxL
  exact hxL

end DE4Hyp

theorem transitive_of_card_seven {L : Subgroup (Equiv.Perm (Fin 8))} (h7 : 7 ∣ Nat.card L) :
    (∃ i, ∀ l ∈ L, l i = i) ∨ ∀ i j, ∃ l ∈ L, l i = j := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) 7 h7
  obtain ⟨s, hsL, hs7, hs_ne⟩ : ∃ s ∈ L, s ^ 7 = 1 ∧ s ≠ 1 := by
    refine ⟨(g : Equiv.Perm (Fin 8)), g.2, ?_, ?_⟩
    · have h1 : g ^ 7 = 1 := by rw [← hg, pow_orderOf_eq_one]
      have h2 := congrArg Subtype.val h1
      simpa using h2
    · intro h1
      have h2 : orderOf g = 1 := orderOf_eq_one_iff.mpr (Subtype.ext h1)
      rw [hg] at h2
      norm_num at h2
  obtain ⟨p, hsp, hpuniq⟩ := DE4Hyp.dewh5_seven_fixed_unique hs7 hs_ne
  have hpow7 : ∀ t : ℕ, s ^ (7 * t + 1) = s := by
    intro t
    rw [pow_succ, pow_mul, hs7, one_pow, one_mul]
  by_cases hp : ∀ l ∈ L, l p = p
  · exact Or.inl ⟨p, hp⟩
  right
  obtain ⟨l₀, hl₀, hne⟩ : ∃ l₀ ∈ L, l₀ p ≠ p := by
    by_contra hc
    exact hp fun l hl => by_contra fun h => hc ⟨l, hl, h⟩
  obtain ⟨q, hq_def⟩ : ∃ q, q = l₀ p := ⟨_, rfl⟩
  have hq_ne : q ≠ p := hq_def ▸ hne
  have key : ∀ k m t : ℕ, k * m = 7 * t + 1 → (s ^ k) q = q → s q = q := by
    intro k m t hkm hkq
    have h1 : ((s ^ k) ^ m) q = q := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hkq m
    calc s q = (s ^ (k * m)) q := by rw [hkm, hpow7 t]
      _ = q := by rw [pow_mul]; exact h1
  have hfix_q : ∀ d : ℕ, 0 < d → d < 7 → (s ^ d) q = q → False := by
    intro d hd0 hd7 hdq
    have hsq : s q = q := by
      have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
      · exact key 1 1 0 (by norm_num) hdq
      · exact key 2 4 1 (by norm_num) hdq
      · exact key 3 5 2 (by norm_num) hdq
      · exact key 4 2 1 (by norm_num) hdq
      · exact key 5 3 2 (by norm_num) hdq
      · exact key 6 6 5 (by norm_num) hdq
    exact hq_ne (hpuniq q hsq)
  have hinj : ∀ a b : ℕ, a < b → b < 7 → (s ^ a) q ≠ (s ^ b) q := by
    intro a b hab hb7 heq
    have h1 : (s ^ (b - a)) q = q := by
      have hb : b = a + (b - a) := by omega
      have h2 : (s ^ a) ((s ^ (b - a)) q) = (s ^ a) q := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, ← hb]
        exact heq.symm
      exact (s ^ a).injective h2
    exact hfix_q (b - a) (by omega) (by omega) h1
  have hcover : ∀ x : Fin 8, x ≠ p → ∃ k : ℕ, k < 7 ∧ (s ^ k) q = x := by
    intro x hxp
    let f : ℕ → Fin 8 := fun k => (s ^ k) q
    have hfinj : Set.InjOn f (Finset.range 7 : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      by_contra hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact hinj a b h hb hab
      · exact hinj b a h ha hab.symm
    have himg : (Finset.range 7).image f = Finset.univ.erase p := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro hfp
        have hkp : (s ^ k) p = p := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hsp k
        apply hq_ne
        exact (s ^ k).injective (hfp.trans hkp.symm)
      · rw [Finset.card_image_of_injOn hfinj, Finset.card_range, Finset.card_erase_of_mem
          (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hx : x ∈ (Finset.range 7).image f := by
      rw [himg, Finset.mem_erase]
      exact ⟨hxp, Finset.mem_univ _⟩
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
    exact ⟨k, Finset.mem_range.mp hk, hkx⟩
  have horbit : ∀ x : Fin 8, ∃ l ∈ L, l p = x := by
    intro x
    by_cases hxp : x = p
    · exact ⟨1, L.one_mem, by rw [hxp, Equiv.Perm.one_apply]⟩
    · obtain ⟨k, _, hk⟩ := hcover x hxp
      refine ⟨s ^ k * l₀, L.mul_mem (by simpa using L.pow_mem hsL k) hl₀, ?_⟩
      rw [Equiv.Perm.mul_apply, ← hq_def]
      exact hk
  intro i j
  obtain ⟨l₁, hl₁, h₁⟩ := horbit i
  obtain ⟨l₂, hl₂, h₂⟩ := horbit j
  refine ⟨l₂ * l₁⁻¹, L.mul_mem hl₂ (L.inv_mem hl₁), ?_⟩
  have hinv : l₁⁻¹ (l₁ p) = p := by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [Equiv.Perm.mul_apply, ← h₁, hinv, h₂]

private theorem dewh_card_affinePlane : ∀ β ∈ AE.affinePlanes, β.card = 4 := by decide +kernel

private theorem dewh_wr_eq_ofVec_mul_ofPerm {n : ℕ} (v : Fin n → ZMod 2)
    (s : Equiv.Perm (Fin n)) : (⟨v, s⟩ : AE.Wr n) = AE.Wr.ofVec v * AE.Wr.ofPerm s :=
  AE.Wr.ext (funext fun i => by show v i = v i + 0; rw [add_zero]) (one_mul _).symm

theorem mem_sup_memAt_of_perm {n : ℕ} {α : Finset (Fin n)} (hα : α.card = 4) {a : AE.Wr n}
    (hv : ∀ x, x ∉ α → a.vec x = 0) (hw : AE.Wr.wsum a = 0)
    (hp : ∃ d : Equiv.Perm (Fin 4), (d = 1 ∨ d = AE.d₁ ∨ d = AE.d₂ ∨ d = AE.d₃) ∧
      a.perm = AE.embedPerm (AE.emb α hα) d) :
    a ∈ AE.memAt α hα true ⊔ AE.memAt α hα false := by
  obtain ⟨d, hd, hpd⟩ := hp
  have hrange : Set.range (AE.emb α hα) = (α : Set (Fin n)) := AE.range_emb α hα
  obtain ⟨v, hsupp⟩ : ∃ v : Fin 4 → ZMod 2, ∀ x, a.vec x = AE.embedVec (AE.emb α hα) v x := by
    refine ⟨fun i => a.vec (AE.emb α hα i), fun x => ?_⟩
    by_cases hx : x ∈ Set.range (AE.emb α hα)
    · obtain ⟨i, rfl⟩ := hx
      rw [AE.embedVec_apply]
    · rw [AE.embedVec_of_not_mem _ _ hx]
      apply hv
      rw [hrange] at hx
      exact fun hxα => hx (Finset.mem_coe.mpr hxα)
  have hea : AE.embed (AE.emb α hα) ⟨v, d⟩ = a := by
    refine AE.Wr.ext (funext fun x => ?_) ?_
    · rw [AE.embed_vec]
      exact (hsupp x).symm
    · rw [AE.embed_perm]
      exact hpd.symm
  have hsum : ∑ i, v i = 0 := by
    calc ∑ i, v i = ∑ x, AE.embedVec (AE.emb α hα) v x := (AE.sum_embedVec _ v).symm
      _ = ∑ x, a.vec x := Finset.sum_congr rfl fun x _ => (hsupp x).symm
      _ = 0 := hw
  obtain ⟨x, hx, y, hy, hxy⟩ := deqi_C_kList_check v d hd hsum
  have hX : AE.embed (AE.emb α hα) x ∈ AE.memAt α hα true :=
    Subgroup.mem_map_of_mem _ (AE.mem_kQ.mpr hx)
  have hY : AE.embed (AE.emb α hα) y ∈ AE.memAt α hα false :=
    Subgroup.mem_map_of_mem _ (AE.mem_kQStar.mpr hy)
  rw [← hea, ← hxy, map_mul]
  exact Subgroup.mul_mem_sup hX hY

theorem exists_mul_eq_of_card {M Δ V : Subgroup G} (hΔ : Δ ≤ M) (hV : V ≤ M)
    (hdisj : Δ ⊓ V = ⊥) (hcard : Nat.card Δ * Nat.card V = Nat.card M) {x : G} (hx : x ∈ M) :
    ∃ d ∈ Δ, ∃ v ∈ V, x = d * v := by
  let f : Δ × V → M := fun p => ⟨(p.1 : G) * (p.2 : G), M.mul_mem (hΔ p.1.2) (hV p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨d, hd⟩, ⟨v, hv⟩⟩ ⟨⟨d', hd'⟩, ⟨v', hv'⟩⟩ hf
    have h1 : d * v = d' * v' := congrArg Subtype.val hf
    have h2 : d'⁻¹ * d = v' * v⁻¹ := by
      calc d'⁻¹ * d = d'⁻¹ * (d * v) * v⁻¹ := by group
        _ = d'⁻¹ * (d' * v') * v⁻¹ := by rw [h1]
        _ = v' * v⁻¹ := by group
    have h3 : d'⁻¹ * d ∈ Δ ⊓ V :=
      ⟨Δ.mul_mem (Δ.inv_mem hd') hd, h2 ▸ V.mul_mem hv' (V.inv_mem hv)⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have hdd : d = d' := (inv_mul_eq_one.mp h3).symm
    subst hdd
    have h4 : v = v' := mul_left_cancel h1
    subst h4
    rfl
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  obtain ⟨⟨d, v⟩, hdv⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨d, d.2, v, v.2, (congrArg Subtype.val hdv).symm⟩

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

private theorem dewh5_fixed_absurd (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b ≠ b') {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) {L : Subgroup G}
    (hLX : L ≤ pSpan X) (hL : Nat.card L = 168) (hLA : L ⊓ dewA S b = ⊥)
    (hgood : ∀ K ∈ X, Nat.card ↥(L ⊓ (K ⊔ S.shift b K)) = 4)
    {Y₀ : Set (Subgroup G)} (hY₀ : Y₀ ∈ dewPts S b')
    (hfix : ∀ l ∈ L, conjSub l '' Y₀ = Y₀) : False := by
  classical
  have hX' : IsDewPoint S b X := hX
  have hY₀' : IsDewPoint S b' Y₀ := hY₀
  have hdisjDL : zGroup Ω ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxA : x ∈ L ⊓ dewA S b := ⟨hx.2, h.zGroup_le_dewA S b hx.1⟩
    rw [hLA, Subgroup.mem_bot] at hxA
    rw [Subgroup.mem_bot]
    exact hxA
  have hDX : zGroup Ω ≤ dewh5_stab X := fun d hd => h.dewh5_dewA_le_stab S hb hX
    (h.zGroup_le_dewA S b hd)
  have hDY : zGroup Ω ≤ dewh5_stab Y₀ := fun d hd => h.dewh5_dewA_le_stab S hb' hY₀
    (h.zGroup_le_dewA S b' hd)
  have hLS : L ≤ dewh5_stab X ⊓ dewh5_stab Y₀ :=
    le_inf (hLX.trans (h.dewh5_le_stab S hb hX)) (fun l hl => dewh5_mem_stab.mpr (hfix l hl))
  have hDS : zGroup Ω ≤ dewh5_stab X ⊓ dewh5_stab Y₀ := le_inf hDX hDY
  have hcardS : Nat.card ↥(dewh5_stab X ⊓ dewh5_stab Y₀) ≤ 1344 :=
    h.dewh5_card_stab_le S hb hb' hbb' hX hY₀
  have hprod := dewh5_card_mul_le hDS hLS hdisjDL
  rw [h.card_zGroup, hL] at hprod
  have hcardEq : Nat.card ↥(zGroup Ω) * Nat.card ↥L =
      Nat.card ↥(dewh5_stab X ⊓ dewh5_stab Y₀) := by
    rw [h.card_zGroup, hL]
    omega
  have hdec : ∀ x ∈ dewh5_stab X ⊓ dewh5_stab Y₀, ∃ d ∈ zGroup Ω, ∃ v ∈ L, x = d * v :=
    fun x hx => dewh5_mul_mem_of_card hDS hLS hdisjDL hcardEq hx
  obtain ⟨u, huD, hu1⟩ : ∃ u ∈ zGroup Ω, u ≠ 1 := by
    have hnt : Nontrivial (zGroup Ω) := by
      rw [← Finite.one_lt_card_iff_nontrivial, h.card_zGroup]
      norm_num
    obtain ⟨x, hx⟩ := exists_ne (1 : zGroup Ω)
    exact ⟨x.1, x.2, fun e => hx (Subtype.ext e)⟩
  obtain ⟨K₀, hK₀X, hK₀u⟩ := h.pt_exists_mem S hX' huD hu1
  have hK₀Ω : K₀ ∈ Ω := hX'.1 hK₀X
  obtain ⟨Mu, hMuX, hMuY, hMuu⟩ := h.exists_common_member S hb hb' hbb' hX hY₀ huD hu1
  have hMuΩ : Mu ∈ Ω := hMuu.1
  have hMuinv : IsUniqueInvolution Mu u := hMuu.2
  have hMuS : Mu ≤ dewh5_stab X ⊓ dewh5_stab Y₀ := by
    intro k hk
    exact ⟨dewh5_mem_stab.mpr ((h.forall_conjSub_image_eq_iff_mem S hb hX' hMuΩ).mpr hMuX k hk),
      dewh5_mem_stab.mpr ((h.forall_conjSub_image_eq_iff_mem S hb' hY₀' hMuΩ).mpr hMuY k hk)⟩
  have hJX : S.shift b K₀ ∈ X := hX'.2.1 K₀ hK₀X
  have hJΩ : S.shift b K₀ ∈ Ω := hX'.1 hJX
  have hMuW : Mu ≤ K₀ ⊔ S.shift b K₀ := by
    have hMutw : Mu ∈ twinSet Ω K₀ := by
      rw [← dew1V_eq_twinSet hK₀Ω hK₀u]
      exact ⟨hMuΩ, hMuinv⟩
    have hmem : Mu ∈ twinSet Ω K₀ ∩ X := ⟨hMutw, hMuX⟩
    rw [h.pt_twin_inter S hb hX' hK₀X] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1]
      exact le_sup_right
  have hne : K₀ ≠ S.shift b K₀ := fun e => hb (S.shift_free b K₀ hK₀Ω e.symm)
  have hJinv : IsUniqueInvolution (S.shift b K₀) u := by
    obtain ⟨-, z, hz1, hz2⟩ := S.shift_mem b K₀ hK₀Ω
    have hzu : z = u := hz1.eq hK₀u
    rw [hzu] at hz2
    exact hz2
  let tw : DewTwins Ω K₀ (S.shift b K₀) u := ⟨hK₀Ω, hJΩ, hK₀u, hJinv, hne⟩
  have hWcard : Nat.card ↥(K₀ ⊔ S.shift b K₀) = 32 := h.card_sup_twins tw
  have hDcard : Nat.card ↥(dewDelta K₀ (S.shift b K₀)) = 8 := h.card_dewDelta tw
  have hDD : dewDelta K₀ (S.shift b K₀) ⊓ zGroup Ω = Subgroup.zpowers u :=
    h.dewDelta_inf_zGroup tw
  haveI : (pCore 2 G).Normal := pCore_normal
  have hQW : (pCore 2 G).relIndex (K₀ ⊔ S.shift b K₀) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (pCore 2 G) (K₀ ⊔ S.shift b K₀)
    have h2 : pCore 2 G ⊓ (K₀ ⊔ S.shift b K₀) = dewDelta K₀ (S.shift b K₀) := by
      unfold dewDelta
      exact inf_comm _ _
    rw [h2, hDcard, hWcard] at h1
    omega
  have hQWsup : Nat.card ↥(pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀)) = 2048 := by
    have e1 : (pCore 2 G).relIndex (pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀)) = 4 := by
      rw [sup_comm, Subgroup.relIndex_sup_right, hQW]
    have h3 := Subgroup.relIndex_mul_card (pCore 2 G) (pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀))
    rw [e1, inf_eq_left.mpr le_sup_left, h.card_pCore_eq] at h3
    omega
  have hLQ : L ⊓ pCore 2 G = ⊥ := h.dewh5_L_inf_pCore S hb hX hLX hLA
  have hbound : Nat.card ↥(L ⊓ (pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀))) ≤ 4 := by
    have hdis : (L ⊓ (pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀))) ⊓ pCore 2 G = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxL : x ∈ L ⊓ pCore 2 G := ⟨hx.1.1, hx.2⟩
      rw [hLQ, Subgroup.mem_bot] at hxL
      rw [Subgroup.mem_bot]
      exact hxL
    have h4 := dewh5_card_mul_le
      (M := pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀)) (Δ := L ⊓ (pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀)))
      (V := pCore 2 G) inf_le_right le_sup_left hdis
    rw [hQWsup, h.card_pCore_eq] at h4
    omega
  have hLWeq : L ⊓ (K₀ ⊔ S.shift b K₀) = L ⊓ (pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀)) := by
    apply Subgroup.eq_of_le_of_card_ge (inf_le_inf_left _ le_sup_right)
    rw [hgood K₀ hK₀X]
    exact hbound
  have hdecomp : ∀ w ∈ Mu, ∃ d ∈ Subgroup.zpowers u, ∃ l ∈ L ⊓ (K₀ ⊔ S.shift b K₀),
      w = d * l := by
    intro w hw
    obtain ⟨d, hd, v, hv, rfl⟩ := hdec _ (hMuS hw)
    have hdQ : d⁻¹ ∈ pCore 2 G := (pCore 2 G).inv_mem (h.zGroup_le_pCore hd)
    have hvQW : v ∈ pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀) := by
      have h5 : d⁻¹ * (d * v) ∈ pCore 2 G ⊔ (K₀ ⊔ S.shift b K₀) :=
        Subgroup.mul_mem_sup hdQ (hMuW hw)
      rwa [inv_mul_cancel_left] at h5
    have hvL : v ∈ L ⊓ (K₀ ⊔ S.shift b K₀) := by
      rw [hLWeq]
      exact ⟨hv, hvQW⟩
    have hdW : d ∈ K₀ ⊔ S.shift b K₀ := by
      have h6 : d * v * v⁻¹ ∈ K₀ ⊔ S.shift b K₀ :=
        (K₀ ⊔ S.shift b K₀).mul_mem (hMuW hw) ((K₀ ⊔ S.shift b K₀).inv_mem hvL.2)
      simpa using h6
    have hdz : d ∈ Subgroup.zpowers u := by
      rw [← hDD]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hdW, h.zGroup_le_pCore hd⟩, hd⟩
    exact ⟨d, hdz, v, hvL, rfl⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzcard : Nat.card ↥(Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · rw [pow_two]
      exact hMuinv.sq
    · exact hu1
  let φ : Subgroup.zpowers u × ↥(L ⊓ (K₀ ⊔ S.shift b K₀)) → G :=
    fun p => (p.1 : G) * (p.2 : G)
  have hsub : (Mu : Set G) ⊆ Set.range φ := by
    intro w hw
    obtain ⟨d, hd, l, hl, rfl⟩ := hdecomp w hw
    exact ⟨(⟨d, hd⟩, ⟨l, hl⟩), rfl⟩
  have hrange_card : (Set.range φ).ncard ≤ 8 := by
    rw [← Set.image_univ]
    calc (φ '' Set.univ).ncard
        ≤ (Set.univ : Set (Subgroup.zpowers u × ↥(L ⊓ (K₀ ⊔ S.shift b K₀)))).ncard :=
          Set.ncard_image_le
      _ = Nat.card (Subgroup.zpowers u × ↥(L ⊓ (K₀ ⊔ S.shift b K₀))) := Set.ncard_univ _
      _ = 8 := by rw [Nat.card_prod, hzcard, hgood K₀ hK₀X]
  have hMucard : (Mu : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card Mu hMuΩ
  have hMu_eq : (Mu : Set G) = Set.range φ :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  obtain ⟨ℓ, hℓ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ (K₀ ⊔ S.shift b K₀))) 2
    (by rw [hgood K₀ hK₀X]; norm_num)
  have hℓsq : (ℓ : G) * ℓ = 1 := by
    have h1 : ℓ * ℓ = 1 := by
      rw [← pow_two, ← hℓ, pow_orderOf_eq_one]
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hℓ1 : (ℓ : G) ≠ 1 := by
    intro e
    have h1 : ℓ = 1 := Subtype.ext e
    rw [h1, orderOf_one] at hℓ
    norm_num at hℓ
  have hℓMu : (ℓ : G) ∈ Mu := by
    have hmem : (ℓ : G) ∈ (Mu : Set G) := by
      rw [hMu_eq]
      exact ⟨((1 : Subgroup.zpowers u), ℓ), by simp [φ]⟩
    exact hmem
  have hℓu : (ℓ : G) = u := by
    rcases hMuinv.unique (ℓ : G) hℓMu hℓsq with e | e
    · exact absurd e hℓ1
    · exact e
  have huL : u ∈ L := by
    rw [← hℓu]
    exact (ℓ.2 : (ℓ : G) ∈ L ⊓ (K₀ ⊔ S.shift b K₀)).1
  have hu0 : u ∈ zGroup Ω ⊓ L := ⟨huD, huL⟩
  rw [hdisjDL, Subgroup.mem_bot] at hu0
  exact hu1 hu0

theorem transitive_of_good (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b ≠ b') {X : Set (Subgroup G)} (hX : X ∈ dewPts S b) {L : Subgroup G}
    (hLX : L ≤ pSpan X) (hL : Nat.card L = 168) (hLA : L ⊓ dewA S b = ⊥)
    (hgood : ∀ K ∈ X, Nat.card ↥(L ⊓ (K ⊔ S.shift b K)) = 4) :
    ∀ Y ∈ dewPts S b', ∀ Y' ∈ dewPts S b', ∃ l ∈ L, conjSub l '' Y = Y' := by
  classical
  obtain ⟨P⟩ := h.exists_aglPts S hb'
  have hLQ : L ⊓ pCore 2 G = ⊥ := h.dewh5_L_inf_pCore S hb hX hLX hLA
  let φL : L →* Equiv.Perm (Fin 8) := P.σ.comp L.subtype
  have hφL : Function.Injective φL := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hlA : (l : G) ∈ dewA S b' := by
      rw [← P.ker_eq]
      exact hl
    have hlQ : (l : G) ∈ L ⊓ pCore 2 G := ⟨l.2, dewA_le_pCore S b' hlA⟩
    rw [hLQ, Subgroup.mem_bot] at hlQ
    exact Subtype.ext hlQ
  have hC : Nat.card ↥φL.range = 168 := by
    rw [← hL]
    exact Nat.card_congr (MonoidHom.ofInjective hφL).symm.toEquiv
  have h7 : 7 ∣ Nat.card ↥φL.range := by
    rw [hC]
    norm_num
  rcases transitive_of_card_seven h7 with ⟨i, hi⟩ | htrans
  ·
    exfalso
    obtain ⟨Y₀, hY₀, hlab⟩ := P.bijOn.surjOn (Set.mem_univ i)
    refine h.dewh5_fixed_absurd S hb hb' hbb' hX hLX hL hLA hgood hY₀ ?_
    intro l hl
    have hfixi : P.σ l i = i := hi (φL ⟨l, hl⟩) (MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, rfl⟩)
    apply P.bijOn.injOn (h.isDewPoint_conjSub S (show IsDewPoint S b' Y₀ from hY₀) l) hY₀
    rw [P.equivariant l Y₀ hY₀, hlab, hfixi]
  · intro Y hY Y' hY'
    obtain ⟨c, hc, hci⟩ := htrans (P.lab Y) (P.lab Y')
    obtain ⟨⟨l, hl⟩, hφ⟩ := MonoidHom.mem_range.mp hc
    refine ⟨l, hl, ?_⟩
    apply P.bijOn.injOn (h.isDewPoint_conjSub S (show IsDewPoint S b' Y from hY) l) hY'
    rw [P.equivariant l Y hY]
    have hσc : P.σ l = c := hφ
    rw [hσc]
    exact hci

omit h in
def dewh6_M1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

omit h in
def dewh6_M2 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

omit h in
theorem dewh6_det1 : dewh6_M1.det = 1 := by decide

omit h in
theorem dewh6_det2 : dewh6_M2.det = 1 := by decide

omit h in
def dewh6_A1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨dewh6_M1, dewh6_det1⟩

omit h in
def dewh6_A2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨dewh6_M2, dewh6_det2⟩

omit h in
theorem dewh6_A1_ne : dewh6_A1 ≠ 1 := by decide

omit h in
theorem dewh6_A2_ne : dewh6_A2 ≠ 1 := by decide

omit h in
theorem dewh6_A12_ne : dewh6_A1 * dewh6_A2 ≠ 1 := by decide

omit h in
theorem dewh6_A1_sq : dewh6_A1 ^ 2 = 1 := by decide

omit h in
theorem dewh6_A2_cube : dewh6_A2 ^ 3 = 1 := by decide

omit h in
theorem dewh6_A12_seven : (dewh6_A1 * dewh6_A2) ^ 7 = 1 := by decide

omit h in
open scoped commutatorElement in
theorem dewh6_comm4 : ⁅dewh6_A1, dewh6_A2⁆ ^ 4 = 1 := by decide

omit h in
theorem dewh6_aperm_lin1 : TL4.aperm dewh6_A1 0 = AGLFin.lin₁ := by decide

omit h in
theorem dewh6_aperm_lin2 : TL4.aperm dewh6_A2 0 = AGLFin.lin₂ := by decide

omit h in
theorem dewh6_orderOf_A1 : orderOf dewh6_A1 = 2 :=
  orderOf_eq_prime dewh6_A1_sq dewh6_A1_ne

omit h in
theorem dewh6_orderOf_A2 : orderOf dewh6_A2 = 3 :=
  orderOf_eq_prime dewh6_A2_cube dewh6_A2_ne

omit h in
theorem dewh6_orderOf_A12 : orderOf (dewh6_A1 * dewh6_A2) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime dewh6_A12_seven dewh6_A12_ne

omit h in
theorem dewh6_sl32_closure :
    Subgroup.closure ({dewh6_A1, dewh6_A2} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) =
      ⊤ := by
  classical
  set H := Subgroup.closure
    ({dewh6_A1, dewh6_A2} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) with hH
  by_contra hne
  have hA1 : dewh6_A1 ∈ H := Subgroup.subset_closure (by simp)
  have hA2 : dewh6_A2 ∈ H := Subgroup.subset_closure (by simp)
  have hA12 : dewh6_A1 * dewh6_A2 ∈ H := H.mul_mem hA1 hA2
  have d2 : 2 ∣ Nat.card H := by
    have := H.orderOf_dvd_natCard hA1
    rwa [dewh6_orderOf_A1] at this
  have d3 : 3 ∣ Nat.card H := by
    have := H.orderOf_dvd_natCard hA2
    rwa [dewh6_orderOf_A2] at this
  have d7 : 7 ∣ Nat.card H := by
    have := H.orderOf_dvd_natCard hA12
    rwa [dewh6_orderOf_A12] at this
  have d42 : 42 ∣ Nat.card H := by omega
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hle : 42 ≤ Nat.card H := Nat.le_of_dvd hpos d42
  have hidx : Nat.card H * H.index = 168 := by
    rw [Subgroup.card_mul_index, TL4.card_sl3Two]
  have hidx4 : H.index ≤ 4 := by nlinarith
  have hnc : H.normalCore = ⊥ := by
    rcases TL4.isSimpleGroup_sl3Two.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exfalso
      apply hne
      exact eq_top_iff.mpr (h ▸ Subgroup.normalCore_le H)
  have hinj : Function.Injective (MulAction.toPermHom
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hnc]
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, TL4.card_sl3Two] at hcard
  have hfac : Nat.factorial H.index ≤ Nat.factorial 4 := Nat.factorial_le hidx4
  have h24 : Nat.factorial 4 = 24 := rfl
  change 168 ≤ Nat.factorial H.index at hcard
  omega

omit h in
theorem dewh6_rm_closed : ∀ r ∈ AGLFin.rmList, ∀ r' ∈ AGLFin.rmList,
    r + r' ∈ AGLFin.rmList := by decide +kernel

omit h in
theorem dewh6_rm_add_all :
    ∀ r ∈ AGLFin.rmList, r + AGLFin.allOnes ∈ AGLFin.rmList := by decide +kernel

omit h in
theorem dewh6_rm_zero : (0 : Fin 8 → ZMod 2) ∈ AGLFin.rmList := by decide +kernel

omit h in
theorem dewh6_rm_add_self : ∀ r ∈ AGLFin.rmList, r + r = 0 := by decide +kernel

omit h in
theorem dewh6_rm_even : ∀ r ∈ AGLFin.rmList, ∑ i, r i = 0 := by decide +kernel

omit h in
theorem dewh6_ind_mem : ∀ α ∈ AE.affinePlanes, AGLFin.ind α ∈ AGLFin.rmList := by decide +kernel

omit h in
theorem dewh6_trans_pl : ∀ α ∈ AE.affinePlanes, ∀ i ∈ α, ∀ j ∈ α, ∃ c : Fin 8,
    (∀ x ∈ α, AGLFin.trFun c x ∈ α) ∧ AGLFin.trFun c i = j := by decide +kernel

omit h in
theorem dewh6_compl_ne : ∀ α ∈ AE.affinePlanes, ∃ i, i ∉ α := by decide +kernel

omit h in
theorem dewh6_ne : ∀ α ∈ AE.affinePlanes, ∃ i, i ∈ α := by decide +kernel

omit h in
theorem dewh6_tr_eq : ∀ c : Fin 8, AGLFin.tr c = TL4.aperm 1 (TL4.bin c) := by decide +kernel

section Vec

variable (s t : Equiv.Perm (Fin 8))

omit h in
theorem dewh6_vact_add (v w : Fin 8 → ZMod 2) :
    AGLFin.vact s (v + w) = AGLFin.vact s v + AGLFin.vact s w := by
  funext i; rfl

omit h in
theorem dewh6_vact_zero : AGLFin.vact s 0 = 0 := by
  funext i; rfl

omit h in
theorem dewh6_vact_allOnes : AGLFin.vact s AGLFin.allOnes = AGLFin.allOnes := by
  funext i; rfl

omit h in
theorem dewh6_pol_add (v w : Fin 8 → ZMod 2) :
    AGLFin.pol s (v + w) = AGLFin.pol s v + AGLFin.pol s w := by
  unfold AGLFin.pol
  rw [dewh6_vact_add, dewh6_vact_add]
  funext i
  simp only [Pi.add_apply]
  ring

omit h in
theorem dewh6_pol_zero : AGLFin.pol s 0 = 0 := by
  unfold AGLFin.pol
  rw [dewh6_vact_zero, dewh6_vact_zero]
  funext i
  simp

omit h in
theorem dewh6_pol_allOnes : AGLFin.pol s AGLFin.allOnes = AGLFin.allOnes := by
  unfold AGLFin.pol
  rw [dewh6_vact_allOnes, dewh6_vact_allOnes]
  funext i
  simp only [AGLFin.allOnes, Pi.add_apply]
  decide

omit h in
theorem dewh6_IsT_zero : AGLFin.IsT s 0 := Or.inl (dewh6_pol_zero s)

omit h in
theorem dewh6_IsT_add {v w : Fin 8 → ZMod 2} (hv : AGLFin.IsT s v) (hw : AGLFin.IsT s w) :
    AGLFin.IsT s (v + w) := by
  unfold AGLFin.IsT at *
  rw [dewh6_pol_add]
  rcases hv with hv | hv <;> rcases hw with hw | hw <;> rw [hv, hw]
  · exact Or.inl (by simp)
  · exact Or.inr (by funext i; simp [AGLFin.allOnes])
  · exact Or.inr (by funext i; simp [AGLFin.allOnes])
  · exact Or.inl (by funext i; simp [AGLFin.allOnes]; decide)

omit h in
theorem dewh6_IsT_neg {v : Fin 8 → ZMod 2} (hv : AGLFin.IsT s v) : AGLFin.IsT s (-v) := by
  have h2 : -v = v := by
    funext i
    have := (show ∀ a : ZMod 2, -a = a from by decide) (v i)
    exact this
  rw [h2]; exact hv

end Vec

omit h in
@[expose] noncomputable def dewh6_transHom :
    Multiplicative (Fin 3 → ZMod 2) →* Equiv.Perm (Fin 8) where
  toFun v := TL4.aperm 1 (Multiplicative.toAdd v)
  map_one' := by
    show TL4.aperm 1 (Multiplicative.toAdd 1) = 1
    simpa using TL4.aperm_one_zero
  map_mul' v w := by
    show TL4.aperm 1 (Multiplicative.toAdd (v * w)) =
      TL4.aperm 1 (Multiplicative.toAdd v) * TL4.aperm 1 (Multiplicative.toAdd w)
    rw [TL4.aperm_mul]
    simp only [mul_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, toAdd_mul]
    rw [add_comm]

omit h in
theorem dewh6_transHom_apply (v : Multiplicative (Fin 3 → ZMod 2)) :
    dewh6_transHom v = TL4.aperm 1 (Multiplicative.toAdd v) := rfl

omit h in
theorem dewh6_transHom_injective : Function.Injective dewh6_transHom := by
  intro v w h
  exact (TL4.aperm_inj h).2

omit h in
theorem dewh6_card_transHom_range :
    Nat.card dewh6_transHom.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective dewh6_transHom_injective).toEquiv]
  rw [Nat.card_congr
    (Multiplicative.ofAdd.symm : Multiplicative (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))]
  simp

omit h in
@[expose] noncomputable def dewh6_Psi (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32) :
    G →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  TL4.linHom.comp (σ.codRestrict AE.agl32 hσ)

omit h in
theorem dewh6_Psi_apply (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32) (g : G) :
    dewh6_Psi σ hσ g = TL4.linPart ⟨σ g, hσ g⟩ := rfl

omit h in
theorem dewh6_Psi_aperm (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32) (g : G) :
    σ g = TL4.aperm (dewh6_Psi σ hσ g) (TL4.transPart ⟨σ g, hσ g⟩) := by
  rw [dewh6_Psi_apply]
  exact (TL4.aperm_linPart ⟨σ g, hσ g⟩).symm

omit h in
theorem dewh6_Psi_eq_one_iff (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32) (g : G) :
    dewh6_Psi σ hσ g = 1 ↔ ∃ v : Fin 3 → ZMod 2, σ g = TL4.aperm 1 v := by
  constructor
  · intro h
    refine ⟨TL4.transPart ⟨σ g, hσ g⟩, ?_⟩
    have := dewh6_Psi_aperm σ hσ g
    rwa [h] at this
  · rintro ⟨v, hv⟩
    rw [dewh6_Psi_apply]
    exact TL4.linPart_eq hv

omit h in
theorem dewh6_ker_card (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32)
    (hrange : σ.range = AE.agl32) (hk : Nat.card σ.ker = 64) :
    Nat.card (dewh6_Psi σ hσ).ker = 512 := by
  classical
  set N := (dewh6_Psi σ hσ).ker with hN
  have hkerN : σ.ker ≤ N := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [hN, MonoidHom.mem_ker, dewh6_Psi_eq_one_iff σ hσ]
    exact ⟨0, by rw [hg, TL4.aperm_one_zero]⟩
  let φ : N →* Equiv.Perm (Fin 8) := σ.comp N.subtype
  have hφker : φ.ker = σ.ker.subgroupOf N := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = dewh6_transHom.range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      have hg1 : dewh6_Psi σ hσ (g : G) = 1 := g.2
      obtain ⟨v, hv⟩ := (dewh6_Psi_eq_one_iff σ hσ g.1).mp hg1
      refine ⟨Multiplicative.ofAdd v, ?_⟩
      simp only [φ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      rw [dewh6_transHom_apply, toAdd_ofAdd, hv]
    · rintro ⟨v, rfl⟩
      have hmem : dewh6_transHom v ∈ σ.range := by
        rw [hrange, dewh6_transHom_apply]
        exact TL4.aperm_mem_agl32 1 _
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hmem
      have hgN : g ∈ N := by
        rw [hN, MonoidHom.mem_ker, dewh6_Psi_eq_one_iff σ hσ]
        rw [hg, dewh6_transHom_apply]
        exact ⟨_, rfl⟩
      exact ⟨⟨g, hgN⟩, by simp [φ, hg]⟩
  have h1 : Nat.card N = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker φ, Subgroup.card_mul_index]
  rw [h1, hφrange, dewh6_card_transHom_range, hφker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerN).toEquiv, hk]

omit h in
theorem dewh6_ker_le_pCore (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32)
    (hrange : σ.range = AE.agl32) (hk : Nat.card σ.ker = 64) :
    (dewh6_Psi σ hσ).ker ≤ CFSG.pCore 2 G := by
  have hcard := dewh6_ker_card σ hσ hrange hk
  have hP : IsPGroup 2 (dewh6_Psi σ hσ).ker := by
    rw [IsPGroup.iff_card]
    exact ⟨9, by rw [hcard]; norm_num⟩
  exact le_sSup ⟨inferInstance, hP⟩

omit h in
theorem dewh6_lift' (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32) (g : G) :
    σ g = AGLFin.tr (TL4.binIdx (TL4.transPart ⟨σ g, hσ g⟩)) *
      TL4.aperm (dewh6_Psi σ hσ g) 0 := by
  rw [dewh6_tr_eq, TL4.bin_binIdx, TL4.aperm_mul]
  have h := dewh6_Psi_aperm σ hσ g
  simp only [one_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
    Matrix.mulVec_zero, zero_add]
  exact h

omit h in
theorem dewh6_lift (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32) (g : G) :
    ∃ c : Fin 8, σ g = AGLFin.tr c * TL4.aperm (dewh6_Psi σ hσ g) 0 :=
  ⟨_, dewh6_lift' σ hσ g⟩

omit h in
theorem dewh6_inj (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32)
    (L : Subgroup G) (hLQ : L ⊓ CFSG.pCore 2 G = ⊥)
    (hN : (dewh6_Psi σ hσ).ker ≤ CFSG.pCore 2 G) {x y : G} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : dewh6_Psi σ hσ x = dewh6_Psi σ hσ y) : x = y := by
  have hk : x⁻¹ * y ∈ (dewh6_Psi σ hσ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hmem : x⁻¹ * y ∈ L ⊓ CFSG.pCore 2 G :=
    ⟨L.mul_mem (L.inv_mem hx) hy, hN hk⟩
  rw [hLQ, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

omit h in
theorem dewh6_surj (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32)
    (L : Subgroup G) (hcard : Nat.card L = 168)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, dewh6_Psi σ hσ x = dewh6_Psi σ hσ y → x = y)
    (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ x ∈ L, dewh6_Psi σ hσ x = A := by
  let f : L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (dewh6_Psi σ hσ).comp L.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hinj x.1 x.2 y.1 y.2 hxy)
  have hrange : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, TL4.card_sl3Two]
    simpa using hcard
  have hA : A ∈ f.range := by rw [hrange]; exact Subgroup.mem_top A
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hA
  exact ⟨x.1, x.2, hx⟩

omit h in
theorem dewh6_gen (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32)
    (L : Subgroup G) {l₁ l₂ : G} (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, dewh6_Psi σ hσ x = dewh6_Psi σ hσ y → x = y)
    (hgen : Subgroup.closure ({dewh6_A1, dewh6_A2} : Set (Matrix.SpecialLinearGroup (Fin 3)
      (ZMod 2))) = ⊤)
    (e₁ : dewh6_Psi σ hσ l₁ = dewh6_A1) (e₂ : dewh6_Psi σ hσ l₂ = dewh6_A2) :
    L ≤ Subgroup.closure {l₁, l₂} := by
  intro l hl
  have hmap : (Subgroup.closure {l₁, l₂}).map (dewh6_Psi σ hσ) = ⊤ := by
    rw [MonoidHom.map_closure, Set.image_pair, e₁, e₂, hgen]
  have hPl : dewh6_Psi σ hσ l ∈ (Subgroup.closure {l₁, l₂}).map (dewh6_Psi σ hσ) := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hPl
  have hkL : k ∈ L := by
    have : Subgroup.closure ({l₁, l₂} : Set G) ≤ L := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact h₁
      · exact h₂
    exact this hk
  have := hinj k hkL l hl hkl
  rw [← this]
  exact hk

omit h in
theorem dewh6_nofix (σ : G →* Equiv.Perm (Fin 8)) (L : Subgroup G) {l₁ l₂ : G}
    (hgenL : L ≤ Subgroup.closure {l₁, l₂})
    (htr : ∀ i j : Fin 8, ∃ l ∈ L, σ l i = j) (x : Fin 8) :
    ¬ (σ l₁ x = x ∧ σ l₂ x = x) := by
  rintro ⟨hx1, hx2⟩
  let Sx : Subgroup G := (MulAction.stabilizer (Equiv.Perm (Fin 8)) x).comap σ
  have hS : Subgroup.closure ({l₁, l₂} : Set G) ≤ Sx := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · show σ g x = x
      exact hx1
    · show σ g x = x
      exact hx2
  have hfix : ∀ l ∈ L, σ l x = x := fun l hl => by
    have := hS (hgenL hl)
    exact this
  have hne : ∀ y : Fin 8, y ≠ x → False := by
    intro y hy
    obtain ⟨l, hl, hlx⟩ := htr x y
    rw [hfix l hl] at hlx
    exact hy hlx.symm
  have hall : ∀ z : Fin 8, z + 1 ≠ z := by decide
  exact hne (x + 1) (hall x)

omit h in
open scoped commutatorElement in
theorem dewh6_hyp (σ : G →* Equiv.Perm (Fin 8)) (hσ : ∀ g, σ g ∈ AE.agl32)
    (L : Subgroup G) {l₁ l₂ : G} (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, dewh6_Psi σ hσ x = dewh6_Psi σ hσ y → x = y)
    (htr : ∀ i j : Fin 8, ∃ l ∈ L, σ l i = j)
    (hgenL : L ≤ Subgroup.closure {l₁, l₂})
    (e₁ : dewh6_Psi σ hσ l₁ = dewh6_A1) (e₂ : dewh6_Psi σ hσ l₂ = dewh6_A2) :
    ∃ c₁ c₂ : Fin 8, AGLFin.Hyp c₁ c₂ ∧ AGLFin.gen₁ c₁ = σ l₁ ∧ AGLFin.gen₂ c₂ = σ l₂ := by
  obtain ⟨c₁, hc₁⟩ := dewh6_lift σ hσ l₁
  obtain ⟨c₂, hc₂⟩ := dewh6_lift σ hσ l₂
  rw [e₁, dewh6_aperm_lin1] at hc₁
  rw [e₂, dewh6_aperm_lin2] at hc₂
  have hg1 : AGLFin.gen₁ c₁ = σ l₁ := hc₁.symm
  have hg2 : AGLFin.gen₂ c₂ = σ l₂ := hc₂.symm
  have hk : ∀ g : G, g ∈ L → dewh6_Psi σ hσ g = 1 → g = 1 := fun g hg hg1' =>
    hinj g hg 1 L.one_mem (by rw [hg1', map_one])
  refine ⟨c₁, c₂, ⟨?_, ?_, ?_, ?_, ?_⟩, hg1, hg2⟩
  · rw [hg1, ← map_mul]
    have : l₁ * l₁ = 1 := hinj _ (L.mul_mem h₁ h₁) 1 L.one_mem (by
      rw [map_mul, e₁, map_one, ← sq, dewh6_A1_sq])
    rw [this, map_one]
  · rw [hg2, ← map_pow]
    have : l₂ ^ 3 = 1 := hinj _ (L.pow_mem h₂ 3) 1 L.one_mem (by
      rw [map_pow, e₂, dewh6_A2_cube, map_one])
    rw [this, map_one]
  · rw [hg1, hg2, ← map_mul, ← map_pow]
    have : (l₁ * l₂) ^ 7 = 1 := hinj _ (L.pow_mem (L.mul_mem h₁ h₂) 7) 1 L.one_mem (by
      rw [map_pow, map_mul, e₁, e₂, dewh6_A12_seven, map_one])
    rw [this, map_one]
  · rw [hg1, hg2, ← map_commutatorElement, ← map_pow]
    have hc : ⁅l₁, l₂⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem h₁ h₂) (L.inv_mem h₁)) (L.inv_mem h₂)
    have : ⁅l₁, l₂⁆ ^ 4 = 1 := by
      refine hinj _ (L.pow_mem hc 4) 1 L.one_mem ?_
      rw [map_pow, map_commutatorElement, e₁, e₂, dewh6_comm4, map_one]
    rw [this, map_one]
  · intro x
    rw [hg1, hg2]
    by_contra hcon
    obtain ⟨hA, hB⟩ := not_or.mp hcon
    exact dewh6_nofix σ L hgenL htr x ⟨not_not.mp hA, not_not.mp hB⟩

omit h in
theorem dewh6_zpowers_inv {x u : G} (hu2 : u * u = 1) (hx : x ∈ Subgroup.zpowers u) :
    x = 1 ∨ x = u := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hsq : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu2
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, hsq, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]

theorem dewh6_cK_compl {S : TwinShift Ω} {b : Lab2} (P : AGLPts S b) {K : Subgroup G}
    {α : Finset (Fin 8)} (hα : (α : Set (Fin 8)) = P.lab '' {X | X ∈ dewPts S b ∧ K ∉ X})
    (i : Fin 8) : i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∈ X} ↔ i ∉ α := by
  constructor
  · rintro ⟨X, ⟨hX, hKX⟩, hXi⟩ hiα
    rw [← Finset.mem_coe, hα] at hiα
    obtain ⟨Y, ⟨hY, hKY⟩, hYi⟩ := hiα
    have hXY : X = Y := P.bijOn.injOn hX hY (hXi.trans hYi.symm)
    subst hXY
    exact hKY hKX
  · intro hi
    obtain ⟨X, hX, hXi⟩ := P.bijOn.surjOn (Set.mem_univ i)
    by_cases hK : K ∈ X
    · exact ⟨X, ⟨hX, hK⟩, hXi⟩
    · exfalso
      apply hi
      rw [← Finset.mem_coe, hα]
      exact ⟨X, ⟨hX, hK⟩, hXi⟩

theorem dewh6_plane_vec {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) {P : AGLPts S b}
    {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hβ1 : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1))
    (hβ2 : ∀ (g : G) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
      g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((P.σ g).symm i)))
    (hβ3 : ∀ K ∈ Ω, ∀ q : G, q ∈ dewDelta K (S.shift b K) ↔
      ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧
        (∀ i, i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∈ X} → f.toAdd i = 0) ∧ β f = q)
    {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u)
    {α : Finset (Fin 8)} (hα : α ∈ AE.affinePlanes)
    (hαK : (α : Set (Fin 8)) = P.lab '' {X | X ∈ dewPts S b ∧ K ∉ X}) :
    β (Multiplicative.ofAdd (AGLFin.ind α)) = u := by
  classical
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  obtain ⟨hJΩ, z, hz1, hz2⟩ := S.shift_mem b K hK
  have hzu : z = u := hz1.eq hu
  rw [hzu] at hz2
  have hne : K ≠ S.shift b K := by
    intro heq
    exact hb (S.shift_free b K hK heq.symm)
  have tw : DewTwins Ω K (S.shift b K) u := ⟨hK, hJΩ, hu, hz2, hne⟩
  have hu1 : u ∈ dewDelta K (S.shift b K) := h.zpowers_le_dewDelta tw (Subgroup.mem_zpowers u)
  obtain ⟨f₀, hf₀even, hf₀van, hf₀β⟩ := (hβ3 K hK u).mp hu1
  have hf₀ne' : f₀.toAdd ≠ 0 := by
    intro h0
    apply hu.ne_one
    rw [← hf₀β, toAdd_eq_zero.mp h0, map_one]
  have hvan_off : ∀ i, i ∉ α → f₀.toAdd i = 0 := fun i hi =>
    hf₀van i ((dewh6_cK_compl h P hαK i).mpr hi)
  have hinv : ∀ c : Fin 8, (∀ x ∈ α, AGLFin.trFun c x ∈ α) →
      ∀ x, f₀.toAdd ((AGLFin.tr c).symm x) = f₀.toAdd x := by
    intro c hc x
    have hTmem : AGLFin.tr c ∈ AE.agl32 := by
      rw [dewh6_tr_eq]
      exact TL4.aperm_mem_agl32 _ _
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (show AGLFin.tr c ∈ P.σ.range from by
      rw [P.range_eq]; exact hTmem)
    set F' : Multiplicative (Fin 8 → ZMod 2) :=
      Multiplicative.ofAdd fun i => f₀.toAdd ((AGLFin.tr c).symm i) with hF'
    have hF'tv : ∀ i, F'.toAdd i = f₀.toAdd ((AGLFin.tr c).symm i) := fun i => rfl
    have hF'sum : ∑ i, F'.toAdd i = 0 := by
      simp only [hF'tv]
      rw [Equiv.sum_comp (AGLFin.tr c).symm (fun i => f₀.toAdd i)]
      exact hf₀even
    have hβF' : g * β f₀ * g⁻¹ = β F' := by
      rw [hβ2 g f₀ hf₀even, hg]
    have hiα : ∀ i, i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∈ X} → (AGLFin.tr c).symm i ∉ α := by
      intro i hi hmem
      have h1 := (dewh6_cK_compl h P hαK i).mp hi
      apply h1
      have h2 := hc _ hmem
      have key : AGLFin.trFun c ((AGLFin.tr c).symm i) = i := AGLFin.trFun_trFun c i
      rwa [key] at h2
    have hF'van : ∀ i, i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∈ X} → F'.toAdd i = 0 := by
      intro i hi
      rw [hF'tv]
      exact hvan_off _ (hiα i hi)
    have hF'mem : β F' ∈ zGroup Ω := by
      rw [← hβF', hf₀β]
      exact h.zGroup_normal.conj_mem u huD g
    have hβF'mem : β F' ∈ dewDelta K (S.shift b K) :=
      (hβ3 K hK (β F')).mpr ⟨F', hF'sum, hF'van, rfl⟩
    have hmemD : β F' ∈ Subgroup.zpowers u := by
      rw [← h.dewDelta_inf_zGroup tw]
      exact Subgroup.mem_inf.mpr ⟨hβF'mem, hF'mem⟩
    rcases dewh6_zpowers_inv hu.sq hmemD with h1 | h1
    ·
      rcases (hβ1 F' hF'sum).mp h1 with h2 | h2
      · exfalso
        apply hf₀ne'
        funext y
        have h3 := congrFun h2 (AGLFin.tr c y)
        rw [hF'tv, Equiv.symm_apply_apply] at h3
        simpa using h3
      · exfalso
        obtain ⟨i, hi⟩ := dewh6_compl_ne α hα
        have hiC := (dewh6_cK_compl h P hαK i).mpr hi
        have h3 := hF'van i hiC
        rw [h2] at h3
        exact absurd h3 (by simp)
    ·
      have hG : β (F' * f₀⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, hf₀β, mul_inv_cancel]
      have hGsum : ∑ i, (F' * f₀⁻¹).toAdd i = 0 := by
        simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hF'sum, hf₀even, neg_zero, add_zero]
      rcases (hβ1 _ hGsum).mp hG with h2 | h2
      · have h3 := congrFun h2 x
        simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at h3
        rw [hF'tv, ← sub_eq_add_neg, sub_eq_zero] at h3
        exact h3
      · exfalso
        obtain ⟨i, hi⟩ := dewh6_compl_ne α hα
        have hiC := (dewh6_cK_compl h P hαK i).mpr hi
        have h3 := congrFun h2 i
        simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply] at h3
        rw [hF'tv, hvan_off i hi, hvan_off _ (hiα i hiC)] at h3
        exact absurd h3 (by decide)
  have hconst : ∀ i ∈ α, ∀ j ∈ α, f₀.toAdd i = f₀.toAdd j := by
    intro i hi j hj
    obtain ⟨c, hc, hcij⟩ := dewh6_trans_pl α hα i hi j hj
    have h1 := hinv c hc j
    have hsymm : (AGLFin.tr c).symm j = i := by
      show AGLFin.trFun c j = i
      rw [← hcij]
      exact AGLFin.trFun_trFun c i
    rw [hsymm] at h1
    exact h1
  obtain ⟨i₀, hi₀⟩ := dewh6_ne α hα
  have hval : f₀.toAdd i₀ = 1 := by
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) (f₀.toAdd i₀) with h0 | h0
    · exfalso
      apply hf₀ne'
      funext y
      by_cases hy : y ∈ α
      · rw [hconst y hy i₀ hi₀, h0]
        rfl
      · rw [hvan_off y hy]
        rfl
    · exact h0
  have hf : f₀.toAdd = AGLFin.ind α := by
    funext i
    by_cases hi : i ∈ α
    · rw [hconst i hi i₀ hi₀, hval]
      simp [AGLFin.ind, hi]
    · rw [hvan_off i hi]
      simp [AGLFin.ind, hi]
  rw [← hf, ofAdd_toAdd, hf₀β]

theorem dewh6_mem_D {S : TwinShift Ω} {b : Lab2} (hb : b ≠ 0) {P : AGLPts S b}
    {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hβ1 : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1))
    (hβ2 : ∀ (g : G) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
      g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((P.σ g).symm i)))
    (hβ3 : ∀ K ∈ Ω, ∀ q : G, q ∈ dewDelta K (S.shift b K) ↔
      ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧
        (∀ i, i ∈ P.lab '' {X | X ∈ dewPts S b ∧ K ∈ X} → f.toAdd i = 0) ∧ β f = q)
    {d : G} (hd : d ∈ zGroup Ω) :
    ∃ r ∈ AGLFin.rmList, β (Multiplicative.ofAdd r) = d := by
  let X : Subgroup G :=
    { carrier := {g | ∃ r ∈ AGLFin.rmList, β (Multiplicative.ofAdd r) = g}
      mul_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨r', hr', rfl⟩
        exact ⟨r + r', dewh6_rm_closed r hr r' hr', by rw [ofAdd_add, map_mul]⟩
      one_mem' := ⟨0, dewh6_rm_zero, by rw [ofAdd_zero, map_one]⟩
      inv_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        refine ⟨r, hr, ?_⟩
        have hneg : -r = r := neg_eq_iff_add_eq_zero.mpr (dewh6_rm_add_self r hr)
        rw [← map_inv, ← ofAdd_neg, hneg] }
  have hsub : zGroup Ω ≤ X := by
    unfold zGroup
    rw [Subgroup.closure_le]
    rintro u ⟨L, hL, hu⟩
    obtain ⟨α, hα, hαL⟩ := P.plane L hL
    refine ⟨AGLFin.ind α, dewh6_ind_mem α hα, ?_⟩
    exact dewh6_plane_vec h hb hβ1 hβ2 hβ3 hL hu hα hαL
  exact hsub hd

omit h in
@[expose] def dewh6_K (f : Equiv.Perm (Fin 8)) :
    Subgroup (Multiplicative (Fin 8 → ZMod 2)) where
  carrier := {x | AGLFin.IsT f (Multiplicative.toAdd x)}
  mul_mem' {x y} hx hy := by
    show AGLFin.IsT f (Multiplicative.toAdd (x * y))
    rw [toAdd_mul]
    exact dewh6_IsT_add f hx hy
  one_mem' := by
    show AGLFin.IsT f (Multiplicative.toAdd 1)
    rw [toAdd_one]
    exact dewh6_IsT_zero f
  inv_mem' {x} hx := by
    show AGLFin.IsT f (Multiplicative.toAdd x⁻¹)
    rw [toAdd_inv]
    exact dewh6_IsT_neg f hx

omit h in
theorem dewh6_card_K {f : Equiv.Perm (Fin 8)}
    (hcard : (Finset.univ.filter (AGLFin.IsT f)).card = 16) :
    Nat.card (dewh6_K f) = 16 := by
  let e : dewh6_K f ≃ {v : Fin 8 → ZMod 2 // AGLFin.IsT f v} :=
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, hcard]

omit h in
@[expose] noncomputable def dewh6_phi {G : Type} [Group G] (f : Equiv.Perm (Fin 8))
    (β : Multiplicative (Fin 8 → ZMod 2) →* G) : dewh6_K f →* G :=
  β.comp (dewh6_K f).subtype

omit h in
theorem dewh6_card_ker_phi {G : Type} [Group G] [Finite G] {f : Equiv.Perm (Fin 8)}
    {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hE : ∀ v, AGLFin.IsT f v → ∑ i, v i = 0)
    (hβ1 : ∀ x : Multiplicative (Fin 8 → ZMod 2), ∑ i, x.toAdd i = 0 →
      (β x = 1 ↔ x.toAdd = 0 ∨ x.toAdd = fun _ => 1))
    (hTπ : AGLFin.IsT f AGLFin.allOnes) :
    Nat.card (dewh6_phi f β).ker = 2 := by
  classical
  have hker : ∀ x : dewh6_K f, x ∈ (dewh6_phi f β).ker ↔
      x.1.toAdd = 0 ∨ x.1.toAdd = fun _ => 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    exact hβ1 x.1 (hE _ x.2)
  have hone : (1 : Multiplicative (Fin 8 → ZMod 2)) ∈ dewh6_K f := (dewh6_K f).one_mem
  have hallm : Multiplicative.ofAdd AGLFin.allOnes ∈ dewh6_K f := hTπ
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨⟨1, hone⟩, by rw [hker]; exact Or.inl (by simp)⟩,
    ⟨⟨Multiplicative.ofAdd AGLFin.allOnes, hallm⟩, by
      rw [hker]; exact Or.inr (by rw [toAdd_ofAdd]; rfl)⟩, ?_, ?_⟩
  · intro heq
    have h1 := congrArg (fun z : (dewh6_phi f β).ker => z.1.1.toAdd) heq
    simp only [toAdd_one] at h1
    have h2 := congrFun h1 0
    simp [AGLFin.allOnes] at h2
  · apply Set.eq_univ_iff_forall.mpr
    intro z
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (hker z.1).mp z.2 with h0 | h0
    · left
      apply Subtype.ext
      apply Subtype.ext
      rw [toAdd_eq_zero] at h0
      exact h0
    · right
      apply Subtype.ext
      apply Subtype.ext
      exact (ofAdd_toAdd _).symm.trans (congrArg Multiplicative.ofAdd h0)

omit h in
theorem dewh6_card_phi_range {G : Type} [Group G] [Finite G] {f : Equiv.Perm (Fin 8)}
    {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hE : ∀ v, AGLFin.IsT f v → ∑ i, v i = 0)
    (hβ1 : ∀ x : Multiplicative (Fin 8 → ZMod 2), ∑ i, x.toAdd i = 0 →
      (β x = 1 ↔ x.toAdd = 0 ∨ x.toAdd = fun _ => 1))
    (hTπ : AGLFin.IsT f AGLFin.allOnes)
    (hcard : (Finset.univ.filter (AGLFin.IsT f)).card = 16) :
    Nat.card (dewh6_phi f β).range = 8 := by
  have h1 := Subgroup.card_mul_index (dewh6_phi f β).ker
  rw [dewh6_card_ker_phi hE hβ1 hTπ, dewh6_card_K hcard, Subgroup.index_ker] at h1
  omega

omit h in
theorem dewh6_le_dewA {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {S : TwinShift Ω} {b : Lab2} {f : Equiv.Perm (Fin 8)}
    {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hA : ∀ g : G, g ∈ dewA S b ↔ ∃ x : Multiplicative (Fin 8 → ZMod 2),
      ∑ i, x.toAdd i = 0 ∧ β x = g)
    (hE : ∀ v, AGLFin.IsT f v → ∑ i, v i = 0) :
    (dewh6_phi f β).range ≤ dewA S b := by
  rintro t ⟨x, rfl⟩
  exact (hA _).mpr ⟨x.1, hE _ x.2, rfl⟩

omit h in
theorem dewh6_conj_mem {G : Type} [Group G] {f : Equiv.Perm (Fin 8)}
    {β : Multiplicative (Fin 8 → ZMod 2) →* G} {σ : G →* Equiv.Perm (Fin 8)}
    (hβ2 : ∀ (g : G) (x : Multiplicative (Fin 8 → ZMod 2)), ∑ i, x.toAdd i = 0 →
      g * β x * g⁻¹ = β (Multiplicative.ofAdd fun i => x.toAdd ((σ g).symm i)))
    (hE : ∀ v, AGLFin.IsT f v → ∑ i, v i = 0)
    {g : G} (hg : ∀ v, AGLFin.IsT f v → AGLFin.IsT f (AGLFin.vact (σ g) v)) :
    ∀ t ∈ (dewh6_phi f β).range, g * t * g⁻¹ ∈ (dewh6_phi f β).range := by
  rintro t ⟨x, rfl⟩
  refine ⟨⟨Multiplicative.ofAdd (fun i => x.1.toAdd ((σ g).symm i)), ?_⟩, ?_⟩
  · show AGLFin.IsT f (Multiplicative.toAdd (Multiplicative.ofAdd _))
    rw [toAdd_ofAdd]
    exact hg _ x.2
  · show β (Multiplicative.ofAdd (fun i => x.1.toAdd ((σ g).symm i))) = g * β x.1 * g⁻¹
    exact (hβ2 g x.1 (hE _ x.2)).symm

omit h in
theorem dewh6_fwd_mul {G : Type} [Group G] {T : Subgroup G} {g k : G}
    (h1 : ∀ t ∈ T, g * t * g⁻¹ ∈ T) (h2 : ∀ t ∈ T, k * t * k⁻¹ ∈ T) :
    ∀ t ∈ T, (g * k) * t * (g * k)⁻¹ ∈ T := by
  intro t ht
  have := h1 _ (h2 t ht)
  simpa [mul_assoc] using this

omit h in
theorem dewh6_normal_of_fwd {G : Type} [Group G] (T : Subgroup G) {g : G}
    (h1 : ∀ t ∈ T, g * t * g⁻¹ ∈ T) (h2 : ∀ t ∈ T, g⁻¹ * t * g⁻¹⁻¹ ∈ T) :
    g ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact h1 t ht
  · intro ht
    have := h2 _ ht
    simpa [mul_assoc] using this

theorem dewh6_inf_D {f : Equiv.Perm (Fin 8)} {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hE : ∀ v, AGLFin.IsT f v → ∑ i, v i = 0)
    (hβ1 : ∀ x : Multiplicative (Fin 8 → ZMod 2), ∑ i, x.toAdd i = 0 →
      (β x = 1 ↔ x.toAdd = 0 ∨ x.toAdd = fun _ => 1))
    (hRM : ∀ v, AGLFin.IsT f v → v ∈ AGLFin.rmList → v = 0 ∨ v = AGLFin.allOnes)
    (hD : ∀ d ∈ zGroup Ω, ∃ r ∈ AGLFin.rmList, β (Multiplicative.ofAdd r) = d) :
    (dewh6_phi f β).range ⊓ zGroup Ω = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, htD⟩
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ht
  have hx : AGLFin.IsT f x.1.toAdd := x.2
  obtain ⟨r, hr, hreq⟩ := hD _ htD
  have hreq' : β (Multiplicative.ofAdd r) = β x.1 := hreq
  have hk1 : β ((Multiplicative.ofAdd r)⁻¹ * x.1) = 1 := by
    rw [map_mul, map_inv, hreq', inv_mul_cancel]
  have hksum : ∑ i, ((Multiplicative.ofAdd r)⁻¹ * x.1).toAdd i = 0 := by
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, dewh6_rm_even r hr, hE _ hx, neg_zero,
      add_zero]
  have hk2 := (hβ1 _ hksum).mp hk1
  have hv : x.1.toAdd = r ∨ x.1.toAdd = r + AGLFin.allOnes := by
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd] at hk2
    rcases hk2 with h0 | h0
    · left
      exact (neg_add_eq_zero.mp h0).symm
    · right
      exact neg_add_eq_iff_eq_add.mp h0
  have hvmem : x.1.toAdd ∈ AGLFin.rmList := by
    rcases hv with hv | hv
    · rw [hv]
      exact hr
    · rw [hv]
      exact dewh6_rm_add_all r hr
  rw [Subgroup.mem_bot]
  show β x.1 = 1
  rcases hRM _ hx hvmem with h0 | h0
  · exact (hβ1 _ (hE _ hx)).mpr (Or.inl h0)
  · exact (hβ1 _ (hE _ hx)).mpr (Or.inr h0)

theorem exists_invariant_complement (S : TwinShift Ω) {b' : Lab2} (hb' : b' ≠ 0)
    {L : Subgroup G} (hL : Nat.card L = 168) (hLQ : L ⊓ pCore 2 G = ⊥)
    (htrans : ∀ Y ∈ dewPts S b', ∀ Y' ∈ dewPts S b', ∃ l ∈ L, conjSub l '' Y = Y') :
    ∃ T : Subgroup G, T ≤ dewA S b' ∧ T ⊓ zGroup Ω = ⊥ ∧ Nat.card T = 8 ∧
      ∀ l ∈ L, ∀ t ∈ T, l * t * l⁻¹ ∈ T := by
  classical
  obtain ⟨P⟩ := h.exists_aglPts S hb'
  obtain ⟨β, hβA, hβ1, hβ2, hβ3⟩ := h.exists_edgeMap S hb' P
  have hσ : ∀ g, P.σ g ∈ AE.agl32 := fun g => by
    rw [← P.range_eq]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hk : Nat.card P.σ.ker = 64 := by
    rw [P.ker_eq, h.card_dewA S hb']
  have hN := dewh6_ker_le_pCore P.σ hσ P.range_eq hk
  have hinj : ∀ x ∈ L, ∀ y ∈ L, dewh6_Psi P.σ hσ x = dewh6_Psi P.σ hσ y → x = y :=
    fun x hx y hy hxy => dewh6_inj P.σ hσ L hLQ hN hx hy hxy
  have htr : ∀ i j : Fin 8, ∃ l ∈ L, P.σ l i = j := by
    intro i j
    obtain ⟨X, hX, hXi⟩ := P.bijOn.surjOn (Set.mem_univ i)
    obtain ⟨Y, hY, hYj⟩ := P.bijOn.surjOn (Set.mem_univ j)
    obtain ⟨l, hl, hlXY⟩ := htrans X hX Y hY
    refine ⟨l, hl, ?_⟩
    rw [← hXi, ← P.equivariant l X hX, hlXY, hYj]
  obtain ⟨l₁, h₁, e₁⟩ := dewh6_surj P.σ hσ L hL hinj dewh6_A1
  obtain ⟨l₂, h₂, e₂⟩ := dewh6_surj P.σ hσ L hL hinj dewh6_A2
  have hgenL := dewh6_gen P.σ hσ L h₁ h₂ hinj dewh6_sl32_closure e₁ e₂
  obtain ⟨c₁, c₂, hyp, hg1, hg2⟩ := dewh6_hyp P.σ hσ L h₁ h₂ hinj htr hgenL e₁ e₂
  have hC := AGLFin.complement_fin c₁ c₂ hyp
  simp only [AGLFin.Concl] at hC
  obtain ⟨hE, hcard16, hRM, hinv, -⟩ := hC
  have hinv1 : ∀ v, AGLFin.IsT (AGLFin.gen₁ c₁ * AGLFin.gen₂ c₂) v →
      AGLFin.IsT (AGLFin.gen₁ c₁ * AGLFin.gen₂ c₂) (AGLFin.vact (P.σ l₁) v) := fun v hv => by
    rw [← hg1]
    exact (hinv v hv).1
  have hinv2 : ∀ v, AGLFin.IsT (AGLFin.gen₁ c₁ * AGLFin.gen₂ c₂) v →
      AGLFin.IsT (AGLFin.gen₁ c₁ * AGLFin.gen₂ c₂) (AGLFin.vact (P.σ l₂) v) := fun v hv => by
    rw [← hg2]
    exact (hinv v hv).2
  set f : Equiv.Perm (Fin 8) := AGLFin.gen₁ c₁ * AGLFin.gen₂ c₂ with hf
  have hTπ : AGLFin.IsT f AGLFin.allOnes := Or.inr (dewh6_pol_allOnes f)
  have hTA : (dewh6_phi f β).range ≤ dewA S b' := dewh6_le_dewA hβA hE
  have hTcard : Nat.card (dewh6_phi f β).range = 8 :=
    dewh6_card_phi_range hE hβ1 hTπ hcard16
  have hTD : (dewh6_phi f β).range ⊓ zGroup Ω = ⊥ :=
    h.dewh6_inf_D hE hβ1 hRM (fun d hd => dewh6_mem_D h hb' hβ1 hβ2 hβ3 hd)
  have hL1 : ∀ t ∈ (dewh6_phi f β).range, l₁ * t * l₁⁻¹ ∈ (dewh6_phi f β).range :=
    dewh6_conj_mem hβ2 hE hinv1
  have hL2 : ∀ t ∈ (dewh6_phi f β).range, l₂ * t * l₂⁻¹ ∈ (dewh6_phi f β).range :=
    dewh6_conj_mem hβ2 hE hinv2
  have hl1sq : l₁ * l₁ = 1 := hinj _ (L.mul_mem h₁ h₁) 1 L.one_mem (by
    rw [map_mul, e₁, map_one, ← sq, dewh6_A1_sq])
  have hl1inv : l₁⁻¹ = l₁ := inv_eq_of_mul_eq_one_right hl1sq
  have hl2cube : l₂ ^ 3 = 1 := hinj _ (L.pow_mem h₂ 3) 1 L.one_mem (by
    rw [map_pow, e₂, dewh6_A2_cube, map_one])
  have hl2inv : l₂⁻¹ = l₂ * l₂ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_three, hl2cube]
  have hN1 : l₁ ∈ Subgroup.normalizer ((dewh6_phi f β).range : Set G) :=
    dewh6_normal_of_fwd _ hL1 (fun t ht => by
      rw [inv_inv, hl1inv]
      have := hL1 t ht
      rwa [hl1inv] at this)
  have hN2 : l₂ ∈ Subgroup.normalizer ((dewh6_phi f β).range : Set G) :=
    dewh6_normal_of_fwd _ hL2 (fun t ht => by
      rw [hl2inv]
      exact dewh6_fwd_mul hL2 hL2 t ht)
  have hLN : L ≤ Subgroup.normalizer ((dewh6_phi f β).range : Set G) := by
    refine hgenL.trans ((Subgroup.closure_le _).mpr ?_)
    intro x hx
    rcases hx with rfl | rfl
    · exact hN1
    · exact hN2
  refine ⟨(dewh6_phi f β).range, hTA, hTD, hTcard, ?_⟩
  intro l hl t ht
  exact (Subgroup.mem_normalizer_iff.mp (hLN hl) t).mp ht

theorem exists_good_complement (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) :
    ∃ H : Subgroup G, (dewA S b).IsComplement' H ∧
      ∃ K ∈ Ω, Nat.card ↥(H ⊓ (K ⊔ S.shift b K)) = 4 := by
  have hΩne : Ω.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hg : pSpan Ω = ⊤ := h.gen
    rw [hne] at hg
    have hbot : pSpan (∅ : Set (Subgroup G)) = ⊥ := by simp [pSpan]
    have htop : (⊤ : Subgroup G) = ⊥ := by rw [← hg, hbot]
    have h1 : pCore 2 G = ⊥ := le_bot_iff.mp (le_top.trans htop.le)
    have hc := h.card_pCore_eq
    rw [h1, Subgroup.card_bot] at hc
    norm_num at hc
  obtain ⟨K₀, hK₀⟩ := hΩne
  obtain ⟨X, hX⟩ := h.exists_dewPoint S hb
  obtain ⟨K, hKX⟩ : (twinSet Ω K₀ ∩ X).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hX.2.2.1 K₀ hK₀]; norm_num)
  have hKΩ : K ∈ Ω := hX.1 hKX.2
  have hKX' : K ∈ X := hKX.2
  obtain ⟨L, hLX, hL, hLA, hgood⟩ := h.exists_good_pointComplement S hb hX
  obtain ⟨b', hb'0, hbb'⟩ : ∃ b' : Lab2, b' ≠ 0 ∧ b' ≠ b := by
    have key : ∀ c : Lab2, c ≠ 0 → ∃ c' : Lab2, c' ≠ 0 ∧ c' ≠ c := by decide
    exact key b hb
  have hLQ : L ⊓ pCore 2 G = ⊥ := by
    have h1 : L ⊓ pCore 2 G ≤ pSpan X ⊓ pCore 2 G := inf_le_inf_right _ hLX
    rw [h.pSpan_inf_pCore S hb hX] at h1
    exact eq_bot_iff.mpr (le_of_le_of_eq (le_inf inf_le_left h1) hLA)
  have htrans := h.transitive_of_good S hb hb'0 hbb'.symm hX hLX hL hLA hgood
  obtain ⟨T, hTA, hTz, hT8, hTL⟩ := h.exists_invariant_complement S hb'0 hL hLQ htrans
  have hTQ : T ≤ pCore 2 G := hTA.trans (dewA_le_pCore S b')
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact fun ht => hTL l hl t ht
    · intro ht
      have := hTL l⁻¹ (L.inv_mem hl) _ ht
      simpa [mul_assoc] using this
  have hLT : L ⊓ T = ⊥ := eq_bot_iff.mpr (le_of_le_of_eq (inf_le_inf_left L hTQ) hLQ)
  have hLTcard : Nat.card ↥(L ⊔ T) = 1344 := by
    have h1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := L) (B := T) hLN
    rw [hLT, Subgroup.card_bot, hL, hT8] at h1
    omega
  have hsupQ : ∀ g : G, g ∈ T ⊔ L → g ∈ pCore 2 G → g ∈ T := by
    intro g hg hgQ
    obtain ⟨t, ht, l, hl, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hLN hg
    have hlQ : l ∈ pCore 2 G := by
      have := (pCore 2 G).mul_mem (inv_mem (hTQ ht)) hgQ
      rwa [inv_mul_cancel_left] at this
    have hl1 : l = 1 := by
      have hlb : l ∈ L ⊓ pCore 2 G := ⟨hl, hlQ⟩
      rw [hLQ, Subgroup.mem_bot] at hlb
      exact hlb
    rw [hl1, mul_one]
    exact ht
  have hdisj : Disjoint (dewA S b) (T ⊔ L) := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr ?_
    rintro g ⟨hgA, hgH⟩
    have hgQ : g ∈ pCore 2 G := dewA_le_pCore S b hgA
    have hgT : g ∈ T := hsupQ g hgH hgQ
    have hgz : g ∈ zGroup Ω := by
      have hmem : g ∈ dewA S b ⊓ dewA S b' := ⟨hgA, hTA hgT⟩
      rwa [h.dewA_inf_dewA S hb hb'0 hbb'.symm] at hmem
    have hbot : g ∈ T ⊓ zGroup Ω := ⟨hgT, hgz⟩
    rwa [hTz] at hbot
  have hGcard : Nat.card G = 86016 := by
    have h1 := (Subgroup.centralizer (zGroup Ω : Set G)).card_mul_index
    rw [h.index_centralizer_zGroup, h.centralizer_zGroup_eq_pCore, h.card_pCore_eq] at h1
    omega
  have hcompl : (dewA S b).IsComplement' (T ⊔ L) := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ hdisj
    rw [h.card_dewA S hb, hGcard, sup_comm, hLTcard]
  refine ⟨T ⊔ L, hcompl, K, hKΩ, ?_⟩
  have hJ : S.shift b K ∈ twinSet Ω K := S.shift_mem b K hKΩ
  obtain ⟨hJΩ, z, hzK, hzJ⟩ := hJ
  have hne : K ≠ S.shift b K := fun e => hb (S.shift_free b K hKΩ e.symm)
  have tw : DewTwins Ω K (S.shift b K) z := ⟨hKΩ, hJΩ, hzK, hzJ, hne⟩
  have hPcard : Nat.card ↥(K ⊔ S.shift b K) = 32 := h.card_sup_twins tw
  have hΔcard : Nat.card ↥(dewDelta K (S.shift b K)) = 8 := h.card_dewDelta tw
  have hΔA : dewDelta K (S.shift b K) ≤ dewA S b := by
    rw [h.dewA_eq_closure S hb]
    exact fun x hx => Subgroup.subset_closure ⟨K, hKΩ, hx⟩
  have hlow : 4 ≤ Nat.card ↥((T ⊔ L) ⊓ (K ⊔ S.shift b K)) :=
    (hgood K hKX').symm.le.trans (Subgroup.card_le_of_le (inf_le_inf_right _ le_sup_right))
  have hup : Nat.card ↥((T ⊔ L) ⊓ (K ⊔ S.shift b K)) ≤ 4 := by
    haveI := h.dewA_normal S b
    have hAH : dewA S b ⊓ (T ⊔ L) = ⊥ := disjoint_iff.mp hdisj
    have hNorm : (T ⊔ L) ⊓ (K ⊔ S.shift b K) ≤
        Subgroup.normalizer ((dewA S b ⊓ (K ⊔ S.shift b K) : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyA, hyP⟩
        exact ⟨(h.dewA_normal S b).conj_mem y hyA x,
          (K ⊔ S.shift b K).mul_mem ((K ⊔ S.shift b K).mul_mem hx.2 hyP)
            ((K ⊔ S.shift b K).inv_mem hx.2)⟩
      · rintro ⟨hzA, hzP⟩
        have hyA : y ∈ dewA S b := by
          have := (h.dewA_normal S b).conj_mem _ hzA x⁻¹
          simpa [mul_assoc] using this
        have hyP : y ∈ K ⊔ S.shift b K := by
          have := (K ⊔ S.shift b K).mul_mem
            ((K ⊔ S.shift b K).mul_mem ((K ⊔ S.shift b K).inv_mem hx.2) hzP) hx.2
          simpa [mul_assoc] using this
        exact ⟨hyA, hyP⟩
    have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hNorm
    have hinf : ((T ⊔ L) ⊓ (K ⊔ S.shift b K)) ⊓ (dewA S b ⊓ (K ⊔ S.shift b K)) = ⊥ := by
      refine eq_bot_iff.mpr ?_
      rintro x ⟨⟨hxH, -⟩, ⟨hxA, -⟩⟩
      have hx : x ∈ dewA S b ⊓ (T ⊔ L) := ⟨hxA, hxH⟩
      rw [hAH] at hx
      exact hx
    have hsup : Nat.card ↥(((T ⊔ L) ⊓ (K ⊔ S.shift b K)) ⊔ (dewA S b ⊓ (K ⊔ S.shift b K)))
        ≤ 32 := by
      rw [← hPcard]
      exact Subgroup.card_le_of_le (sup_le inf_le_right inf_le_right)
    have hAP : 8 ≤ Nat.card ↥(dewA S b ⊓ (K ⊔ S.shift b K)) := by
      rw [← hΔcard]
      exact Subgroup.card_le_of_le (le_inf hΔA inf_le_left)
    rw [hinf, Subgroup.card_bot, mul_one] at hprod
    have hx8 : Nat.card ↥((T ⊔ L) ⊓ (K ⊔ S.shift b K)) * 8 ≤ 32 := by
      calc Nat.card ↥((T ⊔ L) ⊓ (K ⊔ S.shift b K)) * 8
          ≤ Nat.card ↥((T ⊔ L) ⊓ (K ⊔ S.shift b K)) * Nat.card ↥(dewA S b ⊓ (K ⊔ S.shift b K)) :=
            Nat.mul_le_mul_left _ hAP
        _ = Nat.card ↥(((T ⊔ L) ⊓ (K ⊔ S.shift b K)) ⊔ (dewA S b ⊓ (K ⊔ S.shift b K))) :=
            hprod.symm
        _ ≤ 32 := hsup
    omega
  exact le_antisymm hup hlow

private theorem dewh_twins (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} {u : G}
    (hK : K ∈ Ω) (hu : IsUniqueInvolution K u) : DewTwins Ω K (S.shift b K) u := by
  obtain ⟨hJ, z, hz, hzJ⟩ := S.shift_mem b K hK
  exact ⟨hK, hJ, hu, by rwa [show z = u from hz.eq hu] at hzJ,
    fun heq => hb (S.shift_free b K hK heq.symm)⟩

private theorem dewh_not_comm {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  obtain ⟨i, j, hi, hj, -, -, hcomm, -⟩ := exists_q8_gen hu (h.isQuatSub_of_mem hK) (h.card K hK)
  refine ⟨i, hi, j, hj, fun hc => hu.ne_one ?_⟩
  have h1 : u * (i * j) = i * j := by rw [← hcomm, ← hc]
  exact mul_right_cancel (h1.trans (one_mul _).symm)

private theorem dewh_dewDelta_le_dewA (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    (hK : K ∈ Ω) : dewDelta K (S.shift b K) ≤ dewA S b := by
  rw [h.dewA_eq_closure S hb]
  exact fun x hx => Subgroup.subset_closure ⟨K, hK, hx⟩

theorem sigma_embed_of_mem (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) (P : AGLPts S b)
    {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) {α : Finset (Fin 8)}
    (hα : α.card = 4) (hαK : (α : Set (Fin 8)) = P.lab '' {X | X ∈ dewPts S b ∧ K ∉ X})
    {k : G} (hk : k ∈ K) :
    ∃ d : Equiv.Perm (Fin 4), (d = 1 ∨ d = AE.d₁ ∨ d = AE.d₂ ∨ d = AE.d₃) ∧
      P.σ k = AE.embedPerm (AE.emb α hα) d := by
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have hσ1 : ∀ z ∈ Subgroup.zpowers u, P.σ z = 1 := by
    intro z hz
    have hzA : z ∈ dewA S b := h.zGroup_le_dewA S b ((Subgroup.zpowers_le.mpr huD) hz)
    rw [← P.ker_eq] at hzA
    exact hzA
  have hfixK : ∀ X ∈ dewPts S b, K ∈ X → P.σ k (P.lab X) = P.lab X := by
    intro X hX hKX
    have h1 := P.equivariant k X hX
    rw [(h.forall_conjSub_image_eq_iff_mem S hb hX hK).mpr hKX k hk] at h1
    exact h1.symm
  have hfixout : ∀ x, x ∉ Set.range (AE.emb α hα) → P.σ k x = x := by
    intro x hx
    obtain ⟨X, hX, rfl⟩ := P.bijOn.surjOn (Set.mem_univ x)
    rw [AE.range_emb, hαK] at hx
    have hKX : K ∈ X := by
      by_contra hKX
      exact hx (Set.mem_image_of_mem _ ⟨hX, hKX⟩)
    exact hfixK X hX hKX
  by_cases hex : ∃ i ∈ α, P.σ k i = i
  · obtain ⟨i, hiα, hfix⟩ := hex
    have hiα' : i ∈ (α : Set (Fin 8)) := hiα
    rw [hαK] at hiα'
    obtain ⟨X, ⟨hX, hKX⟩, rfl⟩ := hiα'
    have h2 : P.lab (conjSub k '' X) = P.lab X := (P.equivariant k X hX).trans hfix
    have h3 : conjSub k '' X = X :=
      P.bijOn.injOn (h.isDewPoint_conjSub S hX k) hX h2
    have hz := (h.dcount_stab_iff S hb hK hu hX hKX hk).mp h3
    exact ⟨1, Or.inl rfl, by rw [AE.embedPerm_one]; exact hσ1 k hz⟩
  push Not at hex
  obtain ⟨d, hdσ, hd⟩ := deqi_C_exists_embedPerm hfixout
  have hsq : P.σ k * P.σ k = 1 := by
    rw [← map_mul]
    apply hσ1
    rcases mul_self_eq_one_or_eq_of_q8 hu (h.card K hK) (h.dewh_not_comm hK hu) hk with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers u
  have hmemα : ∀ i, AE.emb α hα i ∈ α := fun i => by
    have h1 : AE.emb α hα i ∈ Set.range (AE.emb α hα) := Set.mem_range_self i
    rw [AE.range_emb] at h1
    exact Finset.mem_coe.mp h1
  have hdd : ∀ i, d (d i) = i := by
    intro i
    apply (AE.emb α hα).injective
    have h1 : P.σ k (P.σ k (AE.emb α hα i)) = AE.emb α hα i := by
      have h2 := congrArg (fun π : Equiv.Perm (Fin 8) => π (AE.emb α hα i)) hsq
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h2
    rw [← hd (d i), ← hd i]
    exact h1
  have hfpf : ∀ i, d i ≠ i := by
    intro i hdi
    apply hex (AE.emb α hα i) (hmemα i)
    rw [hd i, hdi]
  exact ⟨d, Or.inr (deqi_C_perm_fin4 d hdd hfpf), hdσ⟩

theorem nonempty_aeIdentOn_e29_of_aglPts' (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    (P : AGLPts S b) : Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) := by
  obtain ⟨H, hHc, K, hK, hgood⟩ := h.exists_good_complement S hb
  obtain ⟨β, hβmem, hβker, hβconj, hβΔ⟩ := h.exists_edgeMap S hb P
  have hHA : H ⊓ dewA S b = ⊥ := disjoint_iff.mp hHc.disjoint.symm
  let σH : H →* Equiv.Perm (Fin 8) := P.σ.comp H.subtype
  have hσinj : Function.Injective σH := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxA : (x : G) ∈ dewA S b := by
      rw [← P.ker_eq]
      exact hx
    have hxHA : (x : G) ∈ H ⊓ dewA S b := ⟨x.2, hxA⟩
    rw [hHA, Subgroup.mem_bot] at hxHA
    exact Subtype.ext hxHA
  have hσrange : σH.range = AE.agl32 := by
    rw [← P.range_eq]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨⟨⟨a, ha⟩, ⟨x, hx⟩⟩, hax⟩ := hHc.2 g
      have hax' : a * x = g := hax
      have haσ : P.σ a = 1 := by
        rw [← P.ker_eq] at ha
        exact ha
      refine ⟨⟨x, hx⟩, ?_⟩
      show P.σ x = P.σ g
      rw [← hax', map_mul, haσ, one_mul]
  have hS : AESplitHyp (dewA S b) H σH β :=
    ⟨hHc, hσinj, hβmem, hβker, fun x f hf => hβconj (x : G) f hf⟩
  obtain ⟨φ, hφinj, hφrange, hφβ, hφH⟩ := AESplitHyp.exists_hom_e29Sub hS hσrange
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have tw : DewTwins Ω K (S.shift b K) u := h.dewh_twins S hb hK hu
  obtain ⟨α, hαS, hαK⟩ := P.plane K hK
  have hα4 : α.card = 4 := dewh_card_affinePlane α hαS
  have hdisj : dewDelta K (S.shift b K) ⊓ (H ⊓ (K ⊔ S.shift b K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxA := h.dewh_dewDelta_le_dewA S hb hK (Subgroup.mem_inf.mp hx).1
    have hxH := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
    have hxHA : x ∈ H ⊓ dewA S b := ⟨hxH, hxA⟩
    rwa [hHA] at hxHA
  have hcard : Nat.card ↥(dewDelta K (S.shift b K)) * Nat.card ↥(H ⊓ (K ⊔ S.shift b K)) =
      Nat.card ↥(K ⊔ S.shift b K) := by
    rw [h.card_dewDelta tw, hgood, h.card_sup_twins tw]
  have hmap : K.map φ ≤ AE.memBar α hα4 true ⊔ AE.memBar α hα4 false := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨δ, hδ, v, hv, hkδv⟩ := exists_mul_eq_of_card inf_le_left inf_le_right hdisj hcard
      (Subgroup.mem_sup_left hk)
    have hvH : v ∈ H := (Subgroup.mem_inf.mp hv).1
    obtain ⟨f, hf0, hfsupp, hfδ⟩ := (hβΔ K hK δ).mp hδ
    have hfα : ∀ x, x ∉ α → f.toAdd x = 0 := by
      intro x hx
      obtain ⟨X, hX, rfl⟩ := P.bijOn.surjOn (Set.mem_univ x)
      apply hfsupp
      refine Set.mem_image_of_mem _ ⟨hX, ?_⟩
      by_contra hKX
      apply hx
      have hmem : P.lab X ∈ (α : Set (Fin 8)) := by
        rw [hαK]
        exact Set.mem_image_of_mem _ ⟨hX, hKX⟩
      exact Finset.mem_coe.mp hmem
    have hδA : δ ∈ dewA S b := h.dewh_dewDelta_le_dewA S hb hK hδ
    have hδσ : P.σ δ = 1 := by
      rw [← P.ker_eq] at hδA
      exact hδA
    have hφk : φ k = AE.mkQ 8 (⟨f.toAdd, P.σ k⟩ : AE.Wr 8) := by
      have h1 : φ δ = AE.mkQ 8 (AE.Wr.ofVec f.toAdd) := by
        rw [← hfδ]
        exact hφβ f hf0
      have h2 : φ v = AE.mkQ 8 (AE.Wr.ofPerm (P.σ v)) := hφH ⟨v, hvH⟩
      have h3 : P.σ v = P.σ k := by
        rw [hkδv, map_mul, hδσ, one_mul]
      have h4 : φ k = φ δ * φ v := by rw [hkδv, map_mul]
      rw [h4, h1, h2, h3, ← map_mul, ← dewh_wr_eq_ofVec_mul_ofPerm]
    have hmem : (⟨f.toAdd, P.σ k⟩ : AE.Wr 8) ∈ AE.memAt α hα4 true ⊔ AE.memAt α hα4 false :=
      mem_sup_memAt_of_perm hα4 hfα hf0 (h.sigma_embed_of_mem S hb P hK hu hα4 hαK hk)
    rw [hφk]
    have hmem' := Subgroup.mem_map_of_mem (AE.mkQ 8) hmem
    rw [Subgroup.map_sup] at hmem'
    exact hmem'
  have hcardK : Nat.card ↥(K.map φ) = 8 := by
    rw [Subgroup.card_map_of_injective hφinj, h.card K hK]
  have hw : IsUniqueInvolution (K.map φ) (φ u) :=
    { mem := Subgroup.mem_map_of_mem _ hu.mem
      ne_one := fun h1 => hu.ne_one (hφinj (h1.trans (map_one φ).symm))
      sq := by rw [← map_mul, hu.sq, map_one]
      unique := by
        rintro y ⟨g, hg, rfl⟩ hy
        have hgg : g * g = 1 := hφinj (by rw [map_one, map_mul]; exact hy)
        rcases hu.unique g hg hgg with rfl | rfl
        · exact Or.inl (map_one _)
        · exact Or.inr rfl }
  rcases eq_memBar_of_le_sup_memBar (by norm_num) hmap hcardK hw with heq | heq
  · exact nonempty_aeIdentOn_e29_of_hom S.conj_mem h.trans h.gen φ hφinj hφrange hK hαS hα4 heq
  · exact nonempty_aeIdentOn_e29_of_hom S.conj_mem h.trans h.gen φ hφinj hφrange hK hαS hα4 heq

theorem nonempty_aeIdentOn_e29' : Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) := by
  obtain ⟨S⟩ := h.exists_twinShift
  have hb : ((1 : ZMod 2), (0 : ZMod 2)) ≠ (0 : Lab2) := by decide
  obtain ⟨P⟩ := h.exists_aglPts S hb
  exact h.nonempty_aeIdentOn_e29_of_aglPts' S hb P

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
