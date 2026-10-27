module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement Pointwise

theorem y6_lab_exists {G : Type} [Group G] [Finite G] {V : Subgroup G} {U : Set G} {n : ℕ}
    (hn : 0 < n) (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v ∈ U) (hcard : Nat.card ↥U = n * Nat.card ↥V) :
    ∃ lab : G → Fin n, (∀ u ∈ U, ∀ u' ∈ U, lab u = lab u' ↔ u⁻¹ * u' ∈ V) ∧
      ∀ i : Fin n, ∃ u ∈ U, lab u = i := by
  classical
  have hmul : U * (V : Set G) = U := by
    ext g
    constructor
    · intro hg
      obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hg
      exact hUV u hu v hv
    · intro hg
      exact Set.mem_mul.mpr ⟨g, hg, 1, V.one_mem, mul_one g⟩
  have hcount := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient V U
  rw [hmul] at hcount
  have hVpos : 0 < Nat.card ↥V := by
    haveI : Nonempty ↥V := ⟨⟨1, V.one_mem⟩⟩
    exact Nat.card_pos
  have hS : Nat.card (U.image (↑) : Set (G ⧸ V)) = n := by
    have h : n * Nat.card ↥V =
        Nat.card (U.image (↑) : Set (G ⧸ V)) * Nat.card ↥V := by
      rw [← hcard]
      exact hcount.trans (mul_comm (Nat.card ↥V)
        (Nat.card (U.image (↑) : Set (G ⧸ V))))
    exact (Nat.eq_of_mul_eq_mul_right hVpos h).symm
  let e : ↥(U.image (↑) : Set (G ⧸ V)) ≃ Fin n := Finite.equivFinOfCardEq hS
  refine ⟨fun u => if h : (u : G ⧸ V) ∈ (U.image (↑) : Set (G ⧸ V)) then e ⟨_, h⟩
    else ⟨0, hn⟩, ?_, ?_⟩
  · intro u hu u' hu'
    have huS : (u : G ⧸ V) ∈ (U.image (↑) : Set (G ⧸ V)) := ⟨u, hu, rfl⟩
    have huS' : (u' : G ⧸ V) ∈ (U.image (↑) : Set (G ⧸ V)) := ⟨u', hu', rfl⟩
    dsimp only
    rw [dif_pos huS, dif_pos huS']
    constructor
    · intro h
      exact QuotientGroup.eq.mp (congrArg Subtype.val (e.injective h))
    · intro h
      exact congrArg e (Subtype.ext (QuotientGroup.eq.mpr h))
  · intro i
    obtain ⟨q, hq⟩ := e.surjective i
    obtain ⟨u, hu, hqu⟩ := q.property
    refine ⟨u, hu, ?_⟩
    have huS : (u : G ⧸ V) ∈ (U.image (↑) : Set (G ⧸ V)) := ⟨u, hu, rfl⟩
    have hq' : (⟨(u : G ⧸ V), huS⟩ : ↥(U.image (↑) : Set (G ⧸ V))) = q :=
      Subtype.ext hqu
    dsimp only
    rw [dif_pos huS, hq']
    exact hq

theorem y6_act_exists {G : Type} [Group G] {n : ℕ} {X V : Subgroup G} {U : Set G}
    (hXV : X ≤ normalizer (V : Set G)) (hXU : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (lab : G → Fin n) (hlab : ∀ u ∈ U, ∀ u' ∈ U, lab u = lab u' ↔ u⁻¹ * u' ∈ V)
    (hsurj : ∀ i : Fin n, ∃ u ∈ U, lab u = i) :
    ∃ ψ : ↥X →* Equiv.Perm (Fin n),
      (∀ x : ↥X, ∀ u ∈ U, ψ x (lab u) = lab ((x : G) * u * (x : G)⁻¹)) ∧
      ∀ x : ↥X, ψ x = 1 ↔ ∀ u ∈ U, u⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ V := by
  choose rep hrepU hrepLab using hsurj
  let fx : G → Fin n → Fin n := fun a i => lab (a * rep i * a⁻¹)
  have key1 : ∀ {a : G}, a ∈ X → ∀ u ∈ U, fx a (lab u) = lab (a * u * a⁻¹) := by
    intro a ha u hu
    have h1 : (rep (lab u))⁻¹ * u ∈ V :=
      (hlab (rep (lab u)) (hrepU (lab u)) u hu).mp (hrepLab (lab u))
    have h2 : (a * rep (lab u) * a⁻¹)⁻¹ * (a * u * a⁻¹) ∈ V := by
      have h3 := (mem_normalizer_iff.mp (hXV ha) ((rep (lab u))⁻¹ * u)).mp h1
      convert h3 using 1
      group
    have h4 : lab (a * rep (lab u) * a⁻¹) = lab (a * u * a⁻¹) :=
      (hlab (a * rep (lab u) * a⁻¹) (hXU a ha (rep (lab u)) (hrepU (lab u)))
        (a * u * a⁻¹) (hXU a ha u hu)).mpr h2
    simpa only [fx] using h4
  have key2 : ∀ {a b : G}, a ∈ X → b ∈ X → fx (a * b) = fx a ∘ fx b := by
    intro a b ha hb
    funext i
    have hbi : b * rep i * b⁻¹ ∈ U := hXU b hb (rep i) (hrepU i)
    have h1 : (rep (lab (b * rep i * b⁻¹)))⁻¹ * (b * rep i * b⁻¹) ∈ V :=
      (hlab (rep (lab (b * rep i * b⁻¹))) (hrepU _) (b * rep i * b⁻¹) hbi).mp
        (hrepLab _)
    have h2 : (a * rep (lab (b * rep i * b⁻¹)) * a⁻¹)⁻¹ *
        (a * (b * rep i * b⁻¹) * a⁻¹) ∈ V := by
      have h3 := (mem_normalizer_iff.mp (hXV ha)
        ((rep (lab (b * rep i * b⁻¹)))⁻¹ * (b * rep i * b⁻¹))).mp h1
      convert h3 using 1
      group
    have h4 : lab (a * rep (lab (b * rep i * b⁻¹)) * a⁻¹) =
        lab (a * (b * rep i * b⁻¹) * a⁻¹) :=
      (hlab (a * rep (lab (b * rep i * b⁻¹)) * a⁻¹) (hXU a ha _ (hrepU _))
        (a * (b * rep i * b⁻¹) * a⁻¹) (hXU a ha _ hbi)).mpr h2
    change lab ((a * b) * rep i * (a * b)⁻¹) =
      lab (a * rep (lab (b * rep i * b⁻¹)) * a⁻¹)
    rw [show (a * b) * rep i * (a * b)⁻¹ = a * (b * rep i * b⁻¹) * a⁻¹ by group]
    exact h4.symm
  have key3 : fx 1 = id := by
    funext i
    show fx 1 i = i
    simpa only [fx, one_mul, inv_one, mul_one] using hrepLab i
  let F : ↥X → Equiv.Perm (Fin n) := fun x =>
    { toFun := fx (x : G)
      invFun := fx ((x : G)⁻¹)
      left_inv := by
        intro i
        have h := congrFun (key2 (X.inv_mem x.property) x.property) i
        rw [inv_mul_cancel, key3, Function.comp_apply] at h
        simpa using h.symm
      right_inv := by
        intro i
        have h := congrFun (key2 x.property (X.inv_mem x.property)) i
        rw [mul_inv_cancel, key3, Function.comp_apply] at h
        simpa using h.symm }
  have hF_apply : ∀ (x : ↥X) (i : Fin n), (F x) i = fx (x : G) i := fun _ _ => rfl
  have hFmul : ∀ x y : ↥X, F (x * y) = F x * F y := by
    intro x y
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.mul_apply]
    rw [hF_apply (x * y) i, hF_apply x ((F y) i), hF_apply y i]
    exact congrFun (key2 x.property y.property) i
  refine ⟨MonoidHom.mk' F hFmul, ?_, ?_⟩
  · intro x u hu
    change fx (x : G) (lab u) = lab ((x : G) * u * (x : G)⁻¹)
    exact key1 x.property u hu
  · intro x
    constructor
    · intro hx u hu
      have hfix : fx (x : G) (lab u) = lab u := by
        have h := congrArg (fun e : Equiv.Perm (Fin n) => e (lab u)) hx
        rw [show (MonoidHom.mk' F hFmul) x = F x from rfl] at h
        rw [hF_apply, Equiv.Perm.one_apply] at h
        exact h
      rw [key1 x.property u hu] at hfix
      exact (hlab u hu ((x : G) * u * (x : G)⁻¹)
        (hXU (x : G) x.property u hu)).mp hfix.symm
    · intro hR
      have hx1 : F x = 1 := by
        apply Equiv.ext
        intro i
        have h1 : (rep i)⁻¹ * ((x : G) * rep i * (x : G)⁻¹) ∈ V := hR (rep i) (hrepU i)
        have h2 : lab (rep i) = lab ((x : G) * rep i * (x : G)⁻¹) :=
          (hlab (rep i) (hrepU i) ((x : G) * rep i * (x : G)⁻¹)
            (hXU (x : G) x.property (rep i) (hrepU i))).mpr h1
        rw [hrepLab i] at h2
        rw [hF_apply, Equiv.Perm.one_apply]
        simpa only [fx] using h2.symm
      show (MonoidHom.mk' F hFmul) x = 1
      exact hx1

theorem y6_mem_centSec_iff {G : Type} [Group G] {C V : Subgroup G} {U : Set G}
    (hVC : V ≤ C) (hCV : C ≤ normalizer (V : Set G)) (hU : U ⊆ C)
    (hgen : closure (U ∪ (V : Set G)) = C) {x : G}
    (hxC : x ∈ normalizer (C : Set G)) (hxV : x ∈ normalizer (V : Set G)) :
    x ∈ CFSG.GH74.GLS.centralizerSection C V ↔ ∀ u ∈ U, u⁻¹ * (x * u * x⁻¹) ∈ V := by
  let S : Subgroup G :=
    { carrier := {c : G | c ∈ C ∧ ⁅c, x⁆ ∈ V}
      one_mem' := ⟨C.one_mem, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro a b ⟨haC, ha⟩ ⟨hbC, hb⟩
        refine ⟨C.mul_mem haC hbC, ?_⟩
        have h1 : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact V.mul_mem ((mem_normalizer_iff.mp (hCV haC) ⁅b, x⁆).mp hb) ha
      inv_mem' := by
        rintro a ⟨haC, ha⟩
        refine ⟨C.inv_mem haC, ?_⟩
        have h1 : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [h1]
        simpa only [inv_inv] using
          (mem_normalizer_iff.mp (hCV (C.inv_mem haC)) ⁅a, x⁆⁻¹).mp (V.inv_mem ha) }
  constructor
  · intro hx u hu
    have h1 : ⁅u⁻¹, x⁆ ∈ V := hx.2.2 u⁻¹ (C.inv_mem (hU hu))
    convert h1 using 1
    simp only [commutatorElement_def, inv_inv]
    group
  · intro hR
    have hUS : U ⊆ S := by
      intro u hu
      refine ⟨hU hu, ?_⟩
      have h1 : ⁅u⁻¹, x⁆ ∈ V := by
        have := hR u hu
        convert this using 1
        simp only [commutatorElement_def, inv_inv]
        group
      have h2 : u * ⁅u⁻¹, x⁆ * u⁻¹ ∈ V :=
        (mem_normalizer_iff.mp (hCV (hU hu)) ⁅u⁻¹, x⁆).mp h1
      have h3 : ⁅u, x⁆ = (u * ⁅u⁻¹, x⁆ * u⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h3]
      exact V.inv_mem h2
    have hVS : (V : Set G) ⊆ S := by
      intro v hv
      refine ⟨hVC hv, ?_⟩
      have h1 : x * v⁻¹ * x⁻¹ ∈ V := (mem_normalizer_iff.mp hxV v⁻¹).mp (V.inv_mem hv)
      have h2 : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h2]
      exact V.mul_mem hv h1
    have hCS : C ≤ S := by
      rw [← hgen]
      exact (closure_le S).mpr (Set.union_subset hUS hVS)
    refine ⟨hxC, hxV, ?_⟩
    intro c hc
    exact (hCS hc).2

end CFSG.OddStandard.HigherRank.YamadaG23
