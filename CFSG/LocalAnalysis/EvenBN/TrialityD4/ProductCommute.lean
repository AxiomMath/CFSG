module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductDefs
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

section Pair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

structure DiagonalPair (d : TrialityD4Data L q) (t : G) where
  A₁ : Subgroup G
  A₂ : Subgroup G
  P₀ : Subgroup G
  comm₁ : ⁅A₁, A₁ᵍ[t]⁆ = ⊥
  comm₂ : ⁅A₂, A₂ᵍ[t]⁆ = ⊥
  le₁ : P₀ ≤ A₁
  le₂ : P₀ ≤ A₂
  injective₁ : Function.Injective (diagonalHom A₁ t comm₁)
  injective₂ : Function.Injective (diagonalHom A₂ t comm₂)
  range₁ : (diagonalHom A₁ t comm₁).range = cLV d
  range₂ : (diagonalHom A₂ t comm₂).range = lvM d
  rangeP : (P₀.subgroupOf A₁).map (diagonalHom A₁ t comm₁) = d.S.map L.subtype

namespace DiagonalPair

variable {d : TrialityD4Data L q} {t : G} (X : DiagonalPair d t)

@[expose] def Δ₁ : X.A₁ →* G :=
  diagonalHom X.A₁ t X.comm₁

@[expose] def Δ₂ : X.A₂ →* G :=
  diagonalHom X.A₂ t X.comm₂

@[expose] def diag₁ (T : Subgroup G) : Subgroup G :=
  (T.subgroupOf X.A₁).map X.Δ₁

@[expose] def diag₂ (T : Subgroup G) : Subgroup G :=
  (T.subgroupOf X.A₂).map X.Δ₂

@[expose] def hat (T : Subgroup G) : Subgroup G :=
  ((T.comap X.Δ₁) ⊓ X.P₀.subgroupOf X.A₁).map X.A₁.subtype

end DiagonalPair

end Pair

namespace ProductCommuteAux

section Conj

variable {G : Type*} [Group G]

theorem mem_conjSub_iff {A : Subgroup G} {g x : G} : x ∈ Aᵍ[g] ↔ g * x * g⁻¹ ∈ A :=
  mem_map_conj_inv_iff

theorem conjSub_conjSub (A : Subgroup G) (g h : G) : (Aᵍ[g])ᵍ[h] = Aᵍ[g * h] := by
  ext x
  simp only [mem_conjSub_iff]
  rw [show g * (h * x * h⁻¹) * g⁻¹ = g * h * x * (g * h)⁻¹ by group]

theorem conjSub_one (A : Subgroup G) : Aᵍ[(1 : G)] = A := by
  ext x
  simp [mem_conjSub_iff]

theorem conjSub_le_of_mem {K A : Subgroup G} {g : G} (hg : g ∈ K) (hA : A ≤ K) : Aᵍ[g] ≤ K := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h := mul_mem (mul_mem (inv_mem hg) (hA hx)) hg
  simpa [mul_assoc] using h

theorem conjSub_eq_of_mem_normalizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    Aᵍ[g] = A := by
  ext x
  rw [mem_conjSub_iff]
  exact (mem_normalizer_iff.1 hg x).symm

theorem conjSub_mono {A B : Subgroup G} (h : A ≤ B) (g : G) : Aᵍ[g] ≤ Bᵍ[g] :=
  Subgroup.map_mono h

theorem conjSub_sup (A B : Subgroup G) (g : G) : (A ⊔ B)ᵍ[g] = Aᵍ[g] ⊔ Bᵍ[g] :=
  Subgroup.map_sup _ _ _

theorem commutator_conjSub (A B : Subgroup G) (g : G) : ⁅Aᵍ[g], Bᵍ[g]⁆ = ⁅A, B⁆ᵍ[g] :=
  (Subgroup.map_commutator _ _ _).symm

theorem conjSub_bot (g : G) : (⊥ : Subgroup G)ᵍ[g] = ⊥ :=
  Subgroup.map_bot _

theorem mem_normalizer_of_conjSub_eq {A : Subgroup G} {g : G} (h : Aᵍ[g] = A) :
    g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have := mem_conjSub_iff (A := A) (g := g) (x := x)
  rw [h] at this
  exact this

theorem conjSub_sup_conjSub_self {g : G} (hg : g * g = 1) (B : Subgroup G) :
    (B ⊔ Bᵍ[g])ᵍ[g] = B ⊔ Bᵍ[g] := by
  rw [conjSub_sup, conjSub_conjSub, hg, conjSub_one, sup_comm]

end Conj

section I1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ} (d : TrialityD4Data L q)

theorem map_conjSub_subtype (A : Subgroup L) (g : L) :
    (A.map L.subtype)ᵍ[(g : G)] = (Aᵍ[g]).map L.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem rangeSubgroup_conj {X A : Type*} [Group X] [AddGroup A] {x y : A → X}
    (hx : ∀ a b, x (a + b) = x a * x b) (hy : ∀ a b, y (a + b) = y a * y b) {w : X}
    (hw : w * w = 1) (h : ∀ a, w * x a * w = y a) : (rangeSubgroup hx)ᵍ[w] = rangeSubgroup hy := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  ext z
  rw [mem_conjSub_iff, mem_rangeSubgroup, mem_rangeSubgroup]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← h a, ha, hwi]
    calc w * (w * z * w) * w = (w * w) * z * (w * w) := by group
      _ = z := by rw [hw]; simp
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [← h a, hwi]
    calc x a = (w * w) * x a * (w * w) := by rw [hw]; simp
      _ = w * (w * x a * w) * w := by group

theorem swap_conj {X A : Type*} [Group X] {x y : A → X} {w : X} (hw : w * w = 1)
    (h : ∀ a, w * x a * w = y a) : ∀ a, w * y a * w = x a := by
  intro a
  rw [← h a]
  calc w * (w * x a * w) * w = (w * w) * x a * (w * w) := by group
    _ = x a := by rw [hw]; simp

theorem uv_pow_three_eq : (d.u * d.v) ^ 3 = (d.v * d.u) ^ 3 := by
  have h := d.uvuvuv_eq
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

theorem conj_facts :
    ((d.U₁.map L.subtype)ᵍ[vG d] = d.U₃.map L.subtype ∧
      (d.U₃.map L.subtype)ᵍ[vG d] = d.U₁.map L.subtype ∧
      (d.U₄.map L.subtype)ᵍ[vG d] = d.U₄.map L.subtype ∧
      (d.U₅.map L.subtype)ᵍ[vG d] = d.U₆.map L.subtype ∧
      (d.U₆.map L.subtype)ᵍ[vG d] = d.U₅.map L.subtype ∧
      (d.U₂.map L.subtype)ᵍ[uG d] = d.U₅.map L.subtype ∧
      (d.U₅.map L.subtype)ᵍ[uG d] = d.U₂.map L.subtype ∧
      (d.U₃.map L.subtype)ᵍ[uG d] = d.U₄.map L.subtype ∧
      (d.U₄.map L.subtype)ᵍ[uG d] = d.U₃.map L.subtype ∧
      (d.U₆.map L.subtype)ᵍ[uG d] = d.U₆.map L.subtype) := by
  have hu := d.u_mul_self
  have hv := d.v_mul_self
  have e1 : d.U₁ᵍ[d.v] = d.U₃ := rangeSubgroup_conj d.x₁_add d.x₃_add hv d.v_x₁
  have e2 : d.U₃ᵍ[d.v] = d.U₁ := rangeSubgroup_conj d.x₃_add d.x₁_add hv (swap_conj hv d.v_x₁)
  have e3 : d.U₄ᵍ[d.v] = d.U₄ := rangeSubgroup_conj d.x₄_add d.x₄_add hv d.v_x₄
  have e4 : d.U₅ᵍ[d.v] = d.U₆ := rangeSubgroup_conj d.x₅_add d.x₆_add hv d.v_x₅
  have e5 : d.U₆ᵍ[d.v] = d.U₅ := rangeSubgroup_conj d.x₆_add d.x₅_add hv (swap_conj hv d.v_x₅)
  have e6 : d.U₂ᵍ[d.u] = d.U₅ := rangeSubgroup_conj d.x₂_add d.x₅_add hu d.u_x₂
  have e7 : d.U₅ᵍ[d.u] = d.U₂ := rangeSubgroup_conj d.x₅_add d.x₂_add hu (swap_conj hu d.u_x₂)
  have e8 : d.U₃ᵍ[d.u] = d.U₄ := rangeSubgroup_conj d.x₃_add d.x₄_add hu d.u_x₃
  have e9 : d.U₄ᵍ[d.u] = d.U₃ := rangeSubgroup_conj d.x₄_add d.x₃_add hu (swap_conj hu d.u_x₃)
  have e10 : d.U₆ᵍ[d.u] = d.U₆ := rangeSubgroup_conj d.x₆_add d.x₆_add hu d.u_x₆
  exact ⟨(map_conjSub_subtype d.U₁ d.v).trans (congrArg _ e1),
    (map_conjSub_subtype d.U₃ d.v).trans (congrArg _ e2),
    (map_conjSub_subtype d.U₄ d.v).trans (congrArg _ e3),
    (map_conjSub_subtype d.U₅ d.v).trans (congrArg _ e4),
    (map_conjSub_subtype d.U₆ d.v).trans (congrArg _ e5),
    (map_conjSub_subtype d.U₂ d.u).trans (congrArg _ e6),
    (map_conjSub_subtype d.U₅ d.u).trans (congrArg _ e7),
    (map_conjSub_subtype d.U₃ d.u).trans (congrArg _ e8),
    (map_conjSub_subtype d.U₄ d.u).trans (congrArg _ e9),
    (map_conjSub_subtype d.U₆ d.u).trans (congrArg _ e10)⟩

theorem normal_subgroupOf_map {H K : Subgroup L} (hKH : K ≤ normalizer (H : Set L)) :
    ((H.map L.subtype).subgroupOf (K.map L.subtype)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨h, hh, hhn⟩ := hn
  obtain ⟨k, hk, hkg⟩ := g.2
  refine ⟨k * h * k⁻¹, (mem_normalizer_iff.1 (hKH hk) h).1 hh, ?_⟩
  rw [map_mul, map_mul, map_inv]
  change _ = (g : G) * (n : G) * (g : G)⁻¹
  rw [hkg, hhn]

theorem D_normal : ((d.D.map L.subtype).subgroupOf (cLV d)).Normal := by
  refine normal_subgroupOf_map ?_
  rw [d.centralizer_V_eq]
  exact sup_le le_normalizer d.leviShort_le_normalizer_D

theorem M_normal : ((d.M.map L.subtype).subgroupOf (lvM d)).Normal := by
  refine normal_subgroupOf_map (K := d.leviLong ⊔ d.M) ?_
  exact sup_le d.leviLong_le_normalizer_M le_normalizer

theorem D_conj_u : (d.D.map L.subtype)ᵍ[uG d] = d.D.map L.subtype :=
  (map_conjSub_subtype d.D d.u).trans
    (congrArg _ (conjSub_eq_of_mem_normalizer d.u_mem_normalizer_D))

theorem M_conj_v : (d.M.map L.subtype)ᵍ[vG d] = d.M.map L.subtype :=
  (map_conjSub_subtype d.M d.v).trans
    (congrArg _ (conjSub_eq_of_mem_normalizer d.v_mem_normalizer_M))

theorem S_eq_U₁_D : d.S.map L.subtype = d.U₁.map L.subtype ⊔ d.D.map L.subtype := by
  rw [d.S_eq_sup, Subgroup.map_sup]

theorem S_eq_U₂_M : d.S.map L.subtype = d.U₂.map L.subtype ⊔ d.M.map L.subtype := by
  rw [d.S_eq_U₂_sup_M, Subgroup.map_sup]

theorem v_eq_x₂_conj : d.x₂ 1 * (d.v * d.x₂ 1 * d.v) * d.x₂ 1 = d.v := by
  set a : d.leviLong := ⟨d.x₂ 1, d.x₂_mem_leviLong 1⟩ with ha
  set w : d.leviLong := ⟨d.v, d.v_mem_leviLong⟩ with hw
  have h1 : ((d.slX₂ 1 * (d.slV * d.slX₂ 1 * d.slV) * d.slX₂ 1 :
      Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) : Matrix (Fin 2) (Fin 2) d.Γ₀) = !![0, 1; 1, 0] := by
    simpa using d.coe_slX₂_slV_mul (one_ne_zero (α := d.Γ₀))
  have hrep : d.leviLongRep (a * (w * a * w) * a) = d.leviLongRep w := by
    simp only [map_mul, ha, hw, d.leviLongRep_x₂, d.leviLongRep_v]
    apply Subtype.ext
    rw [h1]
    rfl
  exact congrArg Subtype.val (d.leviLongRep_bijective.1 hrep)

theorem v_mem_S_sup_conj : d.v ∈ d.S ⊔ d.Sᵍ[d.v] := by
  have h1 : d.x₂ 1 ∈ d.S := d.U₂_le_S (d.x₂_mem_U₂ 1)
  have h2 : d.v * d.x₂ 1 * d.v ∈ d.Sᵍ[d.v] := by
    rw [mem_conjSub_iff, d.v_inv]
    have : d.v * (d.v * d.x₂ 1 * d.v) * d.v = d.x₂ 1 := by
      calc d.v * (d.v * d.x₂ 1 * d.v) * d.v = (d.v * d.v) * d.x₂ 1 * (d.v * d.v) := by group
        _ = d.x₂ 1 := by rw [d.v_mul_self]; simp
    rw [this]
    exact h1
  have hv : d.x₂ 1 * (d.v * d.x₂ 1 * d.v) * d.x₂ 1 ∈ d.S ⊔ d.Sᵍ[d.v] :=
    mul_mem (mul_mem (mem_sup_left h1) (mem_sup_right h2)) (mem_sup_left h1)
  rwa [v_eq_x₂_conj d] at hv

theorem centralizer_V_eq_S_sup : centralizer (d.V : Set L) = d.S ⊔ d.Sᵍ[d.u] := by
  apply le_antisymm
  · rw [d.centralizer_V_eq]
    refine sup_le (d.D_le_S.trans le_sup_left) ?_
    have hN : d.leviShort ≤ d.U₁ ⊔ d.U₁ᵍ[d.u] := by
      refine d.leviShort_le_of_U₁_le le_sup_left ?_
      rw [TrialityD4Data.leviShort, closure_le]
      rintro g (hg | hg)
      · exact le_normalizer (mem_sup_left hg)
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact mem_normalizer_of_conjSub_eq (conjSub_sup_conjSub_self d.u_mul_self _)
    exact hN.trans (sup_le_sup d.U₁_le_S (conjSub_mono d.U₁_le_S _))
  · exact sup_le d.S_le_centralizer_V
      (conjSub_le_of_mem d.u_mem_centralizer_V d.S_le_centralizer_V)

theorem leviLong_sup_M_eq : d.leviLong ⊔ d.M = d.S ⊔ d.Sᵍ[d.v] := by
  have hS : d.S ≤ d.leviLong ⊔ d.M := by
    rw [d.S_eq_U₂_sup_M]
    exact sup_le_sup_right d.U₂_le_leviLong _
  apply le_antisymm
  · refine sup_le ?_ (d.M_le_S.trans le_sup_left)
    rw [TrialityD4Data.leviLong, closure_le]
    rintro g (hg | hg)
    · exact mem_sup_left (d.U₂_le_S hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact v_mem_S_sup_conj d
  · exact sup_le hS (conjSub_le_of_mem (mem_sup_left d.v_mem_leviLong) hS)

theorem cLV_eq : cLV d = d.S.map L.subtype ⊔ (d.S.map L.subtype)ᵍ[uG d] := by
  rw [map_conjSub_subtype, ← Subgroup.map_sup, ← centralizer_V_eq_S_sup d]
  rfl

theorem lvM_eq : lvM d = d.S.map L.subtype ⊔ (d.S.map L.subtype)ᵍ[vG d] := by
  rw [map_conjSub_subtype, ← Subgroup.map_sup, ← leviLong_sup_M_eq d]
  rfl

theorem cLV_sup_lvM : cLV d ⊔ lvM d = L := by
  have h : centralizer (d.V : Set L) ⊔ (d.leviLong ⊔ d.M) = ⊤ := by
    refine top_le_iff.1 ?_
    calc (⊤ : Subgroup L) = d.S ⊔ closure ({d.u, d.v} : Set L) := d.sup_closure_eq_top.symm
      _ ≤ _ := by
        refine sup_le (d.S_le_centralizer_V.trans le_sup_left) ?_
        rw [closure_le]
        rintro g (rfl | hg)
        · exact mem_sup_left d.u_mem_centralizer_V
        · rw [Set.mem_singleton_iff] at hg
          subst hg
          exact mem_sup_right (mem_sup_left d.v_mem_leviLong)
  change (centralizer (d.V : Set L)).map L.subtype ⊔ (d.leviLong ⊔ d.M).map L.subtype = L
  rw [← Subgroup.map_sup, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem cLV_perfect : ⁅cLV d, cLV d⁆ = cLV d := by
  change ⁅(centralizer (d.V : Set L)).map L.subtype, (centralizer (d.V : Set L)).map L.subtype⁆ =
    (centralizer (d.V : Set L)).map L.subtype
  rw [← Subgroup.map_commutator, d.centralizer_V_eq, d.commutator_D_sup_leviShort]

theorem leviLong_sup_M_perfect (hq : 4 ≤ q) :
    ⁅d.leviLong ⊔ d.M, d.leviLong ⊔ d.M⁆ = d.leviLong ⊔ d.M := by
  have := d.finite
  set K := d.leviLong ⊔ d.M with hK
  obtain ⟨β, hβ⟩ : ∃ β : (d.Γ₀)ˣ, β ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (d.Γ₀)ˣ := ⟨fun x y => by rw [hcon x, hcon y]⟩
    have h1 := Finite.card_le_one_iff_subsingleton.2 this
    rw [d.card_units_Γ₀] at h1
    omega
  have hβ' : (β : d.Γ₀) ≠ 1 := fun h => hβ (Units.ext h)
  have hβi : ((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) ≠ 1 := fun h => hβ (inv_eq_one.1 (Units.ext h))
  have hβ2 : ((β ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) ≠ 1 :=
    fun h => hβ (d.units₀_eq_one_of_sq (Units.ext h))
  set hb := d.hA β with hhb
  have hbK : hb ∈ K := mem_sup_left (d.hA_mem_leviLong β)
  have hcoe : ∀ l l' : (d.Γ₀)ˣ, ((l * l' : (d.Γ₀)ˣ) : d.Γ₀) = (l : d.Γ₀) * (l' : d.Γ₀) :=
    fun _ _ => rfl
  have hc₁ : ∀ a, hb * d.x₁ a * hb⁻¹ = d.x₁ (((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, d.hA_apply, d.torus_x₁, d.coe_unitsIncl]
  have hc₃ : ∀ a, hb * d.x₃ a * hb⁻¹ = d.x₃ (((β : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, d.hA_apply, d.torus_x₃, d.coe_unitsIncl, ← Subfield.coe_mul, ← hcoe,
      show β ^ 2 * β⁻¹ = β by group]
  have hc₂ : ∀ a, hb * d.x₂ a * hb⁻¹ = d.x₂ (((β ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, d.hA_apply, d.torus_x₂]
  have hU₁ : d.U₁ ≤ ⁅K, K⁆ := by
    rintro _ ⟨a, rfl⟩
    exact mem_commutator_of_conj_eq d.x₁_add hbK
      (fun h => hβi (Subtype.ext (by simpa using h))) hc₁ (mem_sup_right (d.x₁_mem_M _))
  have hU₃ : d.U₃ ≤ ⁅K, K⁆ := by
    rintro _ ⟨a, rfl⟩
    exact mem_commutator_of_conj_eq d.x₃_add hbK
      (fun h => hβ' (Subtype.ext (by simpa using h))) hc₃
      (mem_sup_right (d.F_le_M (d.x₃_mem_F _)))
  have hU₂ : d.U₂ ≤ ⁅K, K⁆ := by
    rintro _ ⟨a, rfl⟩
    exact mem_commutator_of_conj_eq d.x₂_add hbK hβ2 hc₂
      (mem_sup_left (d.x₂_mem_leviLong _))
  have hW : d.W ≤ ⁅K, K⁆ := by
    rw [← d.commutator_M_eq]
    exact commutator_mono le_sup_right le_sup_right
  have hM : d.M ≤ ⁅K, K⁆ := sup_le hU₁ (sup_le hU₃ hW)
  have hL : d.leviLong ≤ ⁅K, K⁆ := by
    rw [TrialityD4Data.leviLong, closure_le]
    rintro g (hg | hg)
    · exact hU₂ hg
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      have hx : d.x₂ 1 ∈ ⁅K, K⁆ := hU₂ (d.x₂_mem_U₂ 1)
      have hvK : d.v ∈ K := mem_sup_left d.v_mem_leviLong
      have hx2K : d.x₂ 1 ∈ K := mem_sup_left (d.x₂_mem_leviLong 1)
      have hc : ⁅d.v, d.x₂ 1⁆ ∈ ⁅K, K⁆ := commutator_mem_commutator hvK hx2K
      have h2 : d.v * d.x₂ 1 * d.v ∈ ⁅K, K⁆ := by
        have e : d.v * d.x₂ 1 * d.v = ⁅d.v, d.x₂ 1⁆ * d.x₂ 1 := by
          calc d.v * d.x₂ 1 * d.v = d.v * d.x₂ 1 * d.v⁻¹ := by rw [d.v_inv]
            _ = ⁅d.v, d.x₂ 1⁆ * d.x₂ 1 := by rw [commutatorElement_def]; group
        rw [e]
        exact mul_mem hc hx
      have h3 := mul_mem (mul_mem hx h2) hx
      rwa [v_eq_x₂_conj d] at h3
  exact le_antisymm (Subgroup.commutator_le_self K) (sup_le hL hM)

theorem lvM_perfect (hq : 4 ≤ q) : ⁅lvM d, lvM d⁆ = lvM d := by
  change ⁅(d.leviLong ⊔ d.M).map L.subtype, (d.leviLong ⊔ d.M).map L.subtype⁆ =
    (d.leviLong ⊔ d.M).map L.subtype
  rw [← Subgroup.map_commutator, leviLong_sup_M_perfect d hq]

end I1

section Diag

variable {G : Type*} [Group G] {t : G}

@[expose] def dg (A : Subgroup G) (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (T : Subgroup G) : Subgroup G :=
  (T.subgroupOf A).map (diagonalHom A t hc)

theorem mem_dg_iff {A : Subgroup G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {T : Subgroup G} {y : G} :
    y ∈ dg A hc T ↔ ∃ x : G, x ∈ A ∧ x ∈ T ∧ x * (t⁻¹ * x * t) = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.2, hx, rfl⟩
  · rintro ⟨x, hxA, hxT, rfl⟩
    exact ⟨⟨x, hxA⟩, hxT, rfl⟩

theorem dg_sup {A : Subgroup G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {T₁ T₂ : Subgroup G} (h₁ : T₁ ≤ A)
    (h₂ : T₂ ≤ A) : dg A hc (T₁ ⊔ T₂) = dg A hc T₁ ⊔ dg A hc T₂ := by
  unfold dg
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem eq_of_dg_eq {A : Subgroup G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥}
    (hinj : Function.Injective (diagonalHom A t hc)) {T₁ T₂ : Subgroup G} (h₁ : T₁ ≤ A)
    (h₂ : T₂ ≤ A) (h : dg A hc T₁ = dg A hc T₂) : T₁ = T₂ := by
  have h' := Subgroup.map_injective hinj h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left h₁, inf_of_le_left h₂] at h'
  exact h'

theorem dg_eq_of_le {A A' : Subgroup G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {hc' : ⁅A', A'ᵍ[t]⁆ = ⊥}
    {T : Subgroup G} (h : T ≤ A) (h' : T ≤ A') : dg A hc T = dg A' hc' T := by
  ext y
  rw [mem_dg_iff, mem_dg_iff]
  constructor
  · rintro ⟨x, -, hxT, hx⟩
    exact ⟨x, h' hxT, hxT, hx⟩
  · rintro ⟨x, -, hxT, hx⟩
    exact ⟨x, h hxT, hxT, hx⟩

theorem delta_conj_eq {A : Subgroup G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥) {a y : G} (ha : a ∈ A)
    (hy : y ∈ A) :
    (a * (t⁻¹ * a * t))⁻¹ * y * (a * (t⁻¹ * a * t)) = a⁻¹ * y * a := by
  have hb : a⁻¹ * y * a ∈ A := mul_mem (mul_mem (inv_mem ha) hy) ha
  have h := commute_conj_of_commutator_eq_bot hc ha hb
  calc (a * (t⁻¹ * a * t))⁻¹ * y * (a * (t⁻¹ * a * t))
      = (t⁻¹ * a * t)⁻¹ * (a⁻¹ * y * a) * (t⁻¹ * a * t) := by group
    _ = a⁻¹ * y * a := by rw [mul_assoc (t⁻¹ * a * t)⁻¹, h]; group

theorem conj_eq_of_delta {A : Subgroup G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (a : A) {T : Subgroup G}
    (hT : T ≤ A) : Tᵍ[(diagonalHom A t hc a : G)] = Tᵍ[(a : G)] := by
  have hg : (diagonalHom A t hc a : G) = (a : G) * (t⁻¹ * (a : G) * t) := rfl
  rw [hg]
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (delta_conj_eq hc a.2 (hT hy)).symm ▸ rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, delta_conj_eq hc a.2 (hT hy)⟩

theorem dg_conj {A : Subgroup G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (a : A) (T : Subgroup G) :
    dg A hc (Tᵍ[(a : G)]) = (dg A hc T)ᵍ[(diagonalHom A t hc a : G)] := by
  ext y
  rw [mem_conjSub_iff, mem_dg_iff, mem_dg_iff]
  constructor
  · rintro ⟨x, hxA, hxT, rfl⟩
    rw [mem_conjSub_iff] at hxT
    refine ⟨a * x * a⁻¹, mul_mem (mul_mem a.2 hxA) (inv_mem a.2), hxT, ?_⟩
    have h : diagonalHom A t hc (a * ⟨x, hxA⟩ * a⁻¹) =
        diagonalHom A t hc a * diagonalHom A t hc ⟨x, hxA⟩ * (diagonalHom A t hc a)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    exact h
  · rintro ⟨z, hzA, hzT, hz⟩
    refine ⟨(a : G)⁻¹ * z * a, mul_mem (mul_mem (inv_mem a.2) hzA) a.2, ?_, ?_⟩
    · rw [mem_conjSub_iff]
      have e : (a : G) * ((a : G)⁻¹ * z * a) * (a : G)⁻¹ = z := by group
      rw [e]
      exact hzT
    · have h : diagonalHom A t hc ((a⁻¹ : A) * ⟨z, hzA⟩ * a) =
          (diagonalHom A t hc a)⁻¹ * diagonalHom A t hc ⟨z, hzA⟩ * diagonalHom A t hc a := by
        rw [map_mul, map_mul, map_inv]
      have hz' : diagonalHom A t hc ⟨z, hzA⟩ =
          diagonalHom A t hc a * y * (diagonalHom A t hc a)⁻¹ := hz
      rw [hz'] at h
      have e : (diagonalHom A t hc a : G)⁻¹ *
          (diagonalHom A t hc a * y * (diagonalHom A t hc a)⁻¹) * diagonalHom A t hc a = y := by
        group
      rw [e] at h
      exact h

theorem transport_all {A P₀ Sg : Subgroup G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥)
    (hinj : Function.Injective (diagonalHom A t hc)) (hP : P₀ ≤ A) (hS : dg A hc P₀ = Sg)
    (a : A) {g : G} (hg : diagonalHom A t hc a = g) {T : Subgroup G} (hT : T ≤ P₀) :
    (Tᵍ[g] = Tᵍ[(a : G)] ∧ Tᵍ[g] ≤ A ∧ dg A hc (Tᵍ[g]) = (dg A hc T)ᵍ[g]) ∧
      ((dg A hc T)ᵍ[g] ≤ Sg → Tᵍ[g] ≤ P₀ ∧
        ∀ y, y ∈ Tᵍ[g] ↔ y ∈ P₀ ∧ y * (t⁻¹ * y * t) ∈ (dg A hc T)ᵍ[g]) := by
  subst hg
  have hTA : T ≤ A := hT.trans hP
  have e1 := conj_eq_of_delta hc a hTA
  have hle : Tᵍ[(a : G)] ≤ A := conjSub_le_of_mem a.2 hTA
  have e3 : dg A hc (Tᵍ[(diagonalHom A t hc a : G)]) =
      (dg A hc T)ᵍ[(diagonalHom A t hc a : G)] := by
    rw [e1]
    exact dg_conj hc a T
  refine ⟨⟨e1, e1 ▸ hle, e3⟩, fun hSle => ?_⟩
  have hsub : Tᵍ[(diagonalHom A t hc a : G)] ≤ P₀ := by
    intro x hx
    have hxA : x ∈ A := hle (e1 ▸ hx)
    have h1 : x * (t⁻¹ * x * t) ∈ dg A hc (Tᵍ[(diagonalHom A t hc a : G)]) :=
      mem_dg_iff.2 ⟨x, hxA, hx, rfl⟩
    rw [e3] at h1
    have h2 : x * (t⁻¹ * x * t) ∈ dg A hc P₀ := hS ▸ hSle h1
    obtain ⟨p, hpA, hpP, hp⟩ := mem_dg_iff.1 h2
    have hpx : p = x := congrArg Subtype.val (hinj (a₁ := ⟨p, hpA⟩) (a₂ := ⟨x, hxA⟩) hp)
    exact hpx ▸ hpP
  refine ⟨hsub, fun y => ⟨fun hy => ⟨hsub hy, ?_⟩, fun ⟨hyP, hyD⟩ => ?_⟩⟩
  · rw [← e3]
    exact mem_dg_iff.2 ⟨y, hP (hsub hy), hy, rfl⟩
  · rw [← e3] at hyD
    obtain ⟨x, hxA, hxT, hx⟩ := mem_dg_iff.1 hyD
    have hxy : x = y :=
      congrArg Subtype.val (hinj (a₁ := ⟨x, hxA⟩) (a₂ := ⟨y, hP hyP⟩) hx)
    exact hxy ▸ hxT

end Diag

section DP

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ} {d : TrialityD4Data L q} {t : G}
  (X : DiagonalPair d t)

theorem u_mem_cLV (d : TrialityD4Data L q) : uG d ∈ cLV d :=
  ⟨d.u, d.u_mem_centralizer_V, rfl⟩

theorem v_mem_lvM (d : TrialityD4Data L q) : vG d ∈ lvM d :=
  ⟨d.v, mem_sup_left d.v_mem_leviLong, rfl⟩

theorem mem_hat_iff {T : Subgroup G} {y : G} :
    y ∈ X.hat T ↔ y ∈ X.P₀ ∧ y * (t⁻¹ * y * t) ∈ T := by
  constructor
  · rintro ⟨x, ⟨hxT, hxP⟩, rfl⟩
    exact ⟨hxP, hxT⟩
  · rintro ⟨hy, hyT⟩
    exact ⟨⟨y, X.le₁ hy⟩, ⟨hyT, hy⟩, rfl⟩

theorem hat_le (T : Subgroup G) : X.hat T ≤ X.P₀ := fun _ hy => ((mem_hat_iff X).1 hy).1

theorem dg₁_P₀ : dg X.A₁ X.comm₁ X.P₀ = d.S.map L.subtype := X.rangeP

theorem dg₂_P₀ : dg X.A₂ X.comm₂ X.P₀ = d.S.map L.subtype := by
  rw [← dg₁_P₀ X]
  exact dg_eq_of_le X.le₂ X.le₁

theorem diag₁_hat {T : Subgroup G} (hT : T ≤ d.S.map L.subtype) : X.diag₁ (X.hat T) = T := by
  ext y
  change y ∈ dg X.A₁ X.comm₁ (X.hat T) ↔ y ∈ T
  rw [mem_dg_iff]
  constructor
  · rintro ⟨x, -, hxT, rfl⟩
    exact ((mem_hat_iff X).1 hxT).2
  · intro hy
    have hy' : y ∈ dg X.A₁ X.comm₁ X.P₀ := by rw [dg₁_P₀ X]; exact hT hy
    obtain ⟨x, hxA, hxP, rfl⟩ := mem_dg_iff.1 hy'
    exact ⟨x, hxA, (mem_hat_iff X).2 ⟨hxP, hy⟩, rfl⟩

theorem diag₂_hat {T : Subgroup G} (hT : T ≤ d.S.map L.subtype) : X.diag₂ (X.hat T) = T := by
  ext y
  change y ∈ dg X.A₂ X.comm₂ (X.hat T) ↔ y ∈ T
  rw [mem_dg_iff]
  constructor
  · rintro ⟨x, -, hxT, rfl⟩
    exact ((mem_hat_iff X).1 hxT).2
  · intro hy
    have hy' : y ∈ dg X.A₂ X.comm₂ X.P₀ := by rw [dg₂_P₀ X]; exact hT hy
    obtain ⟨x, hxA, hxP, rfl⟩ := mem_dg_iff.1 hy'
    exact ⟨x, hxA, (mem_hat_iff X).2 ⟨hxP, hy⟩, rfl⟩

theorem exists_a₁ : ∃ a : X.A₁, X.Δ₁ a = uG d := by
  have hu : uG d ∈ (diagonalHom X.A₁ t X.comm₁).range := X.range₁ ▸ u_mem_cLV d
  obtain ⟨a, ha⟩ := hu
  exact ⟨a, ha⟩

theorem exists_a₂ : ∃ a : X.A₂, X.Δ₂ a = vG d := by
  have hv : vG d ∈ (diagonalHom X.A₂ t X.comm₂).range := X.range₂ ▸ v_mem_lvM d
  obtain ⟨a, ha⟩ := hv
  exact ⟨a, ha⟩

theorem hat_conj_u_eq {T T' : Subgroup G} (hT : T ≤ d.S.map L.subtype)
    (hT' : T' ≤ d.S.map L.subtype) (h : Tᵍ[uG d] = T') : (X.hat T)ᵍ[uG d] = X.hat T' := by
  subst h
  obtain ⟨a, ha⟩ := exists_a₁ X
  have h2 := (transport_all X.comm₁ X.injective₁ X.le₁ (dg₁_P₀ X) a ha (hat_le X T)).2
  rw [show dg X.A₁ X.comm₁ (X.hat T) = T from diag₁_hat X hT] at h2
  obtain ⟨-, hiff⟩ := h2 hT'
  ext y
  rw [hiff y, mem_hat_iff]

theorem hat_conj_v_eq {T T' : Subgroup G} (hT : T ≤ d.S.map L.subtype)
    (hT' : T' ≤ d.S.map L.subtype) (h : Tᵍ[vG d] = T') : (X.hat T)ᵍ[vG d] = X.hat T' := by
  subst h
  obtain ⟨a, ha⟩ := exists_a₂ X
  have h2 := (transport_all X.comm₂ X.injective₂ X.le₂ (dg₂_P₀ X) a ha (hat_le X T)).2
  rw [show dg X.A₂ X.comm₂ (X.hat T) = T from diag₂_hat X hT] at h2
  obtain ⟨-, hiff⟩ := h2 hT'
  ext y
  rw [hiff y, mem_hat_iff]

end DP

section Comm

variable {G : Type*} [Group G]

theorem comm_eq_bot_of_le {A B A₀ B₀ : Subgroup G} (hA : A₀ ≤ A) (hB : B₀ ≤ B)
    (h : ⁅A, B⁆ = ⊥) : ⁅A₀, B₀⁆ = ⊥ :=
  le_bot_iff.1 (h ▸ commutator_mono hA hB)

theorem comm_sup_left_eq_bot {A A' B : Subgroup G} (h₁ : ⁅A, B⁆ = ⊥) (h₂ : ⁅A', B⁆ = ⊥) :
    ⁅A ⊔ A', B⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer] at h₁ h₂ ⊢
  exact sup_le h₁ h₂

theorem comm_sup_right_eq_bot {A B B' : Subgroup G} (h₁ : ⁅A, B⁆ = ⊥) (h₂ : ⁅A, B'⁆ = ⊥) :
    ⁅A, B ⊔ B'⁆ = ⊥ := by
  rw [commutator_comm] at h₁ h₂ ⊢
  exact comm_sup_left_eq_bot h₁ h₂

theorem comm_sup_sup_eq_bot {A A' B B' : Subgroup G} (h₁ : ⁅A, B⁆ = ⊥) (h₂ : ⁅A, B'⁆ = ⊥)
    (h₃ : ⁅A', B⁆ = ⊥) (h₄ : ⁅A', B'⁆ = ⊥) : ⁅A ⊔ A', B ⊔ B'⁆ = ⊥ :=
  comm_sup_left_eq_bot (comm_sup_right_eq_bot h₁ h₂) (comm_sup_right_eq_bot h₃ h₄)

end Comm

end ProductCommuteAux
section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q f : ℕ} {t : G}

theorem I1_facts (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    (uG d * uG d = (1 : G) ∧ vG d * vG d = (1 : G) ∧
      (uG d * vG d) ^ 3 = (vG d * uG d) ^ 3) ∧
    ((d.U₁.map L.subtype)ᵍ[vG d] = d.U₃.map L.subtype ∧
      (d.U₃.map L.subtype)ᵍ[vG d] = d.U₁.map L.subtype ∧
      (d.U₄.map L.subtype)ᵍ[vG d] = d.U₄.map L.subtype ∧
      (d.U₅.map L.subtype)ᵍ[vG d] = d.U₆.map L.subtype ∧
      (d.U₆.map L.subtype)ᵍ[vG d] = d.U₅.map L.subtype ∧
      (d.U₂.map L.subtype)ᵍ[uG d] = d.U₅.map L.subtype ∧
      (d.U₅.map L.subtype)ᵍ[uG d] = d.U₂.map L.subtype ∧
      (d.U₃.map L.subtype)ᵍ[uG d] = d.U₄.map L.subtype ∧
      (d.U₄.map L.subtype)ᵍ[uG d] = d.U₃.map L.subtype ∧
      (d.U₆.map L.subtype)ᵍ[uG d] = d.U₆.map L.subtype) ∧
    (d.S.map L.subtype = d.U₁.map L.subtype ⊔ d.D.map L.subtype ∧
      d.S.map L.subtype = d.U₂.map L.subtype ⊔ d.M.map L.subtype ∧
      ((d.D.map L.subtype).subgroupOf (cLV d)).Normal ∧
      ((d.M.map L.subtype).subgroupOf (lvM d)).Normal ∧
      (d.D.map L.subtype)ᵍ[uG d] = d.D.map L.subtype ∧
      (d.M.map L.subtype)ᵍ[vG d] = d.M.map L.subtype) ∧
    (cLV d = d.S.map L.subtype ⊔ (d.S.map L.subtype)ᵍ[uG d] ∧
      lvM d = d.S.map L.subtype ⊔ (d.S.map L.subtype)ᵍ[vG d]) ∧
    cLV d ⊔ lvM d = L ∧
    (⁅cLV d, cLV d⁆ = cLV d ∧ ⁅lvM d, lvM d⁆ = lvM d) := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact ⟨⟨congrArg Subtype.val d.u_mul_self, congrArg Subtype.val d.v_mul_self,
      congrArg Subtype.val (ProductCommuteAux.uv_pow_three_eq d)⟩, ProductCommuteAux.conj_facts d,
    ⟨ProductCommuteAux.S_eq_U₁_D d, ProductCommuteAux.S_eq_U₂_M d, ProductCommuteAux.D_normal d,
      ProductCommuteAux.M_normal d, ProductCommuteAux.D_conj_u d, ProductCommuteAux.M_conj_v d⟩,
    ⟨ProductCommuteAux.cLV_eq d, ProductCommuteAux.lvM_eq d⟩, ProductCommuteAux.cLV_sup_lvM d,
    ⟨ProductCommuteAux.cLV_perfect d, ProductCommuteAux.lvM_perfect d h4⟩⟩

theorem I2_transport {d : TrialityD4Data L q} (X : DiagonalPair d t) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    (∃ a₁ : X.A₁, X.Δ₁ a₁ = uG d ∧ ∀ T : Subgroup G, T ≤ X.P₀ →
      (Tᵍ[uG d] = Tᵍ[(a₁ : G)] ∧ Tᵍ[uG d] ≤ X.A₁ ∧ X.diag₁ (Tᵍ[uG d]) = (X.diag₁ T)ᵍ[uG d])) ∧
    (∃ a₂ : X.A₂, X.Δ₂ a₂ = vG d ∧ ∀ T : Subgroup G, T ≤ X.P₀ →
      (Tᵍ[vG d] = Tᵍ[(a₂ : G)] ∧ Tᵍ[vG d] ≤ X.A₂ ∧ X.diag₂ (Tᵍ[vG d]) = (X.diag₂ T)ᵍ[vG d])) ∧
    (∀ T : Subgroup G, T ≤ X.P₀ → (X.diag₁ T)ᵍ[uG d] ≤ d.S.map L.subtype →
      (Tᵍ[uG d] ≤ X.P₀ ∧ Tᵍ[uG d] = X.hat ((X.diag₁ T)ᵍ[uG d]))) ∧
    (∀ T : Subgroup G, T ≤ X.P₀ → (X.diag₂ T)ᵍ[vG d] ≤ d.S.map L.subtype →
      (Tᵍ[vG d] ≤ X.P₀ ∧ Tᵍ[vG d] = X.hat ((X.diag₂ T)ᵍ[vG d]))) := by
  obtain ⟨a₁, ha₁⟩ := ProductCommuteAux.exists_a₁ X
  obtain ⟨a₂, ha₂⟩ := ProductCommuteAux.exists_a₂ X
  refine ⟨⟨a₁, ha₁, fun T hT => (ProductCommuteAux.transport_all X.comm₁ X.injective₁ X.le₁
      (ProductCommuteAux.dg₁_P₀ X) a₁ ha₁ hT).1⟩,
    ⟨a₂, ha₂, fun T hT => (ProductCommuteAux.transport_all X.comm₂ X.injective₂ X.le₂
      (ProductCommuteAux.dg₂_P₀ X) a₂ ha₂ hT).1⟩, fun T hT hle => ?_, fun T hT hle => ?_⟩
  · obtain ⟨h1, h2⟩ := (ProductCommuteAux.transport_all X.comm₁ X.injective₁ X.le₁
      (ProductCommuteAux.dg₁_P₀ X) a₁ ha₁ hT).2 hle
    exact ⟨h1, Subgroup.ext fun y => (h2 y).trans (ProductCommuteAux.mem_hat_iff X).symm⟩
  · obtain ⟨h1, h2⟩ := (ProductCommuteAux.transport_all X.comm₂ X.injective₂ X.le₂
      (ProductCommuteAux.dg₂_P₀ X) a₂ ha₂ hT).2 hle
    exact ⟨h1, Subgroup.ext fun y => (h2 y).trans (ProductCommuteAux.mem_hat_iff X).symm⟩

theorem I3_paths {d : TrialityD4Data L q} (X : DiagonalPair d t) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    ((X.hat (d.U₁.map L.subtype))ᵍ[vG d] = X.hat (d.U₃.map L.subtype) ∧
      ((X.hat (d.U₁.map L.subtype))ᵍ[vG d])ᵍ[uG d] = X.hat (d.U₄.map L.subtype) ∧
      (((X.hat (d.U₁.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d] = X.hat (d.U₄.map L.subtype) ∧
      ((((X.hat (d.U₁.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d])ᵍ[uG d] =
        X.hat (d.U₃.map L.subtype) ∧
      (((((X.hat (d.U₁.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d])ᵍ[uG d])ᵍ[vG d] =
        X.hat (d.U₁.map L.subtype) ∧
      (X.hat (d.U₁.map L.subtype))ᵍ[uG d] ≤ X.P₀ᵍ[(uG d * vG d) ^ 3]) ∧
    ((X.hat (d.U₆.map L.subtype))ᵍ[uG d] = X.hat (d.U₆.map L.subtype) ∧
      ((X.hat (d.U₆.map L.subtype))ᵍ[uG d])ᵍ[vG d] = X.hat (d.U₅.map L.subtype) ∧
      (((X.hat (d.U₆.map L.subtype))ᵍ[uG d])ᵍ[vG d])ᵍ[uG d] = X.hat (d.U₂.map L.subtype) ∧
      (X.hat (d.U₆.map L.subtype))ᵍ[vG d] = X.hat (d.U₅.map L.subtype) ∧
      ((X.hat (d.U₆.map L.subtype))ᵍ[vG d])ᵍ[uG d] = X.hat (d.U₂.map L.subtype) ∧
      (((X.hat (d.U₆.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d] ≤ X.P₀ᵍ[(uG d * vG d) ^ 3]) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := ProductCommuteAux.conj_facts d
  have hU₁ : d.U₁.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₁_le_S
  have hU₂ : d.U₂.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₂_le_S
  have hU₃ : d.U₃.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₃_le_S
  have hU₄ : d.U₄.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₄_le_S
  have hU₅ : d.U₅.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₅_le_S
  have hU₆ : d.U₆.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.V_le_S
  have p1 := ProductCommuteAux.hat_conj_v_eq X hU₁ hU₃ c1
  have p2 := ProductCommuteAux.hat_conj_u_eq X hU₃ hU₄ c8
  have p3 := ProductCommuteAux.hat_conj_v_eq X hU₄ hU₄ c3
  have p4 := ProductCommuteAux.hat_conj_u_eq X hU₄ hU₃ c9
  have p5 := ProductCommuteAux.hat_conj_v_eq X hU₃ hU₁ c2
  have q1 := ProductCommuteAux.hat_conj_u_eq X hU₆ hU₆ c10
  have q2 := ProductCommuteAux.hat_conj_v_eq X hU₆ hU₅ c5
  have q3 := ProductCommuteAux.hat_conj_u_eq X hU₅ hU₂ c7
  have hw : (uG d * vG d) ^ 3 = (vG d * uG d) ^ 3 :=
    congrArg Subtype.val (ProductCommuteAux.uv_pow_three_eq d)
  have hu : uG d * uG d = 1 := congrArg Subtype.val d.u_mul_self
  have hv : vG d * vG d = 1 := congrArg Subtype.val d.v_mul_self
  refine ⟨⟨p1, by rw [p1, p2], by rw [p1, p2, p3], by rw [p1, p2, p3, p4],
    by rw [p1, p2, p3, p4, p5], ?_⟩, ⟨q1, by rw [q1, q2], by rw [q1, q2, q3], q2,
    by rw [q2, q3], ?_⟩⟩
  · have h5 : (X.hat (d.U₁.map L.subtype))ᵍ[vG d * uG d * vG d * uG d * vG d] =
        X.hat (d.U₁.map L.subtype) := by
      have h : (((((X.hat (d.U₁.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d])ᵍ[uG d])ᵍ[vG d] =
          X.hat (d.U₁.map L.subtype) := by rw [p1, p2, p3, p4, p5]
      simpa only [ProductCommuteAux.conjSub_conjSub] using h
    have h6 := ProductCommuteAux.conjSub_mono (A := (X.hat (d.U₁.map L.subtype)))
      (ProductCommuteAux.hat_le X _) (vG d * uG d * vG d * uG d * vG d)
    rw [h5] at h6
    have h7 := ProductCommuteAux.conjSub_mono h6 (uG d)
    rw [ProductCommuteAux.conjSub_conjSub] at h7
    have e : vG d * uG d * vG d * uG d * vG d * uG d = (uG d * vG d) ^ 3 := by
      rw [hw]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e] at h7
    exact h7
  · have hW : (X.hat (d.U₆.map L.subtype))ᵍ[uG d * vG d * uG d] = X.hat (d.U₂.map L.subtype) := by
      have h : (((X.hat (d.U₆.map L.subtype))ᵍ[uG d])ᵍ[vG d])ᵍ[uG d] =
          X.hat (d.U₂.map L.subtype) := by rw [q1, q2, q3]
      simpa only [ProductCommuteAux.conjSub_conjSub] using h
    have huvu : (uG d * vG d * uG d) * (uG d * vG d * uG d) = 1 := by
      calc (uG d * vG d * uG d) * (uG d * vG d * uG d)
          = uG d * vG d * (uG d * uG d) * vG d * uG d := by group
        _ = uG d * (vG d * vG d) * uG d := by rw [hu, mul_one]; group
        _ = 1 := by rw [hv, mul_one, hu]
    have h1 : X.hat (d.U₆.map L.subtype) ≤ X.P₀ᵍ[uG d * vG d * uG d] := by
      have h2 := ProductCommuteAux.conjSub_mono (ProductCommuteAux.hat_le X (d.U₂.map L.subtype))
        (uG d * vG d * uG d)
      rw [← hW, ProductCommuteAux.conjSub_conjSub, huvu, ProductCommuteAux.conjSub_one] at h2
      exact h2
    have h3 := ProductCommuteAux.conjSub_mono h1 (vG d * uG d * vG d)
    rw [ProductCommuteAux.conjSub_conjSub] at h3
    have e : uG d * vG d * uG d * (vG d * uG d * vG d) = (uG d * vG d) ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e] at h3
    simpa only [ProductCommuteAux.conjSub_conjSub] using h3

theorem I4_factorizations {d : TrialityD4Data L q} (X : DiagonalPair d t) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    (X.P₀ᵍ[uG d] = (X.hat (d.U₁.map L.subtype))ᵍ[uG d] ⊔ X.hat (d.D.map L.subtype) ∧
      (X.hat (d.U₁.map L.subtype))ᵍ[uG d] ≤ X.A₁) ∧
    (X.P₀ᵍ[vG d] = X.hat (d.M.map L.subtype) ⊔
        (((X.hat (d.U₆.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d] ∧
      (((X.hat (d.U₆.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d] ≤ X.A₂) := by
  obtain ⟨-, -, -, -, q6, -⟩ := (I3_paths X htt htL).2
  obtain ⟨a₁, ha₁⟩ := ProductCommuteAux.exists_a₁ X
  obtain ⟨a₂, ha₂⟩ := ProductCommuteAux.exists_a₂ X
  have hU₁ : d.U₁.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₁_le_S
  have hU₂ : d.U₂.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.U₂_le_S
  have hD : d.D.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.D_le_S
  have hM : d.M.map L.subtype ≤ d.S.map L.subtype := Subgroup.map_mono d.M_le_S
  refine ⟨?_, ?_⟩
  · have T1 := ProductCommuteAux.transport_all X.comm₁ X.injective₁ X.le₁
      (ProductCommuteAux.dg₁_P₀ X) a₁ ha₁ (T := X.P₀) le_rfl
    have T2 := ProductCommuteAux.transport_all X.comm₁ X.injective₁ X.le₁
      (ProductCommuteAux.dg₁_P₀ X) a₁ ha₁ (T := X.hat (d.U₁.map L.subtype))
      (ProductCommuteAux.hat_le X _)
    have hA : (X.hat (d.U₁.map L.subtype))ᵍ[uG d] ≤ X.A₁ := T2.1.2.1
    have hD' : X.hat (d.D.map L.subtype) ≤ X.A₁ := (ProductCommuteAux.hat_le X _).trans X.le₁
    refine ⟨ProductCommuteAux.eq_of_dg_eq X.injective₁ T1.1.2.1 (sup_le hA hD') ?_, hA⟩
    rw [T1.1.2.2, ProductCommuteAux.dg_sup hA hD', T2.1.2.2, ProductCommuteAux.dg₁_P₀ X,
      show ProductCommuteAux.dg X.A₁ X.comm₁ (X.hat (d.U₁.map L.subtype)) = d.U₁.map L.subtype
        from ProductCommuteAux.diag₁_hat X hU₁,
      show ProductCommuteAux.dg X.A₁ X.comm₁ (X.hat (d.D.map L.subtype)) = d.D.map L.subtype
        from ProductCommuteAux.diag₁_hat X hD, ProductCommuteAux.S_eq_U₁_D d,
      ProductCommuteAux.conjSub_sup, ProductCommuteAux.D_conj_u d]
  · rw [q6]
    have T1 := ProductCommuteAux.transport_all X.comm₂ X.injective₂ X.le₂
      (ProductCommuteAux.dg₂_P₀ X) a₂ ha₂ (T := X.P₀) le_rfl
    have T2 := ProductCommuteAux.transport_all X.comm₂ X.injective₂ X.le₂
      (ProductCommuteAux.dg₂_P₀ X) a₂ ha₂ (T := X.hat (d.U₂.map L.subtype))
      (ProductCommuteAux.hat_le X _)
    have hA : (X.hat (d.U₂.map L.subtype))ᵍ[vG d] ≤ X.A₂ := T2.1.2.1
    have hM' : X.hat (d.M.map L.subtype) ≤ X.A₂ := (ProductCommuteAux.hat_le X _).trans X.le₂
    refine ⟨ProductCommuteAux.eq_of_dg_eq X.injective₂ T1.1.2.1 (sup_le hM' hA) ?_, hA⟩
    rw [T1.1.2.2, ProductCommuteAux.dg_sup hM' hA, T2.1.2.2, ProductCommuteAux.dg₂_P₀ X,
      show ProductCommuteAux.dg X.A₂ X.comm₂ (X.hat (d.U₂.map L.subtype)) = d.U₂.map L.subtype
        from ProductCommuteAux.diag₂_hat X hU₂,
      show ProductCommuteAux.dg X.A₂ X.comm₂ (X.hat (d.M.map L.subtype)) = d.M.map L.subtype
        from ProductCommuteAux.diag₂_hat X hM, ProductCommuteAux.S_eq_U₂_M d,
      ProductCommuteAux.conjSub_sup, ProductCommuteAux.M_conj_v d, sup_comm]

theorem I5_commute {d : TrialityD4Data L q} (X : DiagonalPair d t) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    ⁅X.A₁, X.A₂ᵍ[t]⁆ = ⊥ ∧ ⁅X.A₁ᵍ[t], X.A₂⁆ = ⊥ := by
  obtain ⟨a₁, ha₁⟩ := ProductCommuteAux.exists_a₁ X
  obtain ⟨a₂, ha₂⟩ := ProductCommuteAux.exists_a₂ X
  obtain ⟨⟨-, -, -, -, -, hÛ₁⟩, ⟨-, -, -, -, -, hŴ⟩⟩ := I3_paths X htt htL
  obtain ⟨⟨hI4a, hÛA⟩, ⟨hI4b, hŴA⟩⟩ := I4_factorizations X htt htL
  have T₁ := ProductCommuteAux.transport_all X.comm₁ X.injective₁ X.le₁
    (ProductCommuteAux.dg₁_P₀ X) a₁ ha₁ (T := X.P₀) le_rfl
  have T₂ := ProductCommuteAux.transport_all X.comm₂ X.injective₂ X.le₂
    (ProductCommuteAux.dg₂_P₀ X) a₂ ha₂ (T := X.P₀) le_rfl
  have hPu : X.P₀ᵍ[uG d] ≤ X.A₁ := T₁.1.2.1
  have hPv : X.P₀ᵍ[vG d] ≤ X.A₂ := T₂.1.2.1
  have hA₁ : X.A₁ = X.P₀ ⊔ X.P₀ᵍ[uG d] := by
    have e1 : ProductCommuteAux.dg X.A₁ X.comm₁ X.A₁ = cLV d := by
      unfold ProductCommuteAux.dg
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact X.range₁
    have e2 : ProductCommuteAux.dg X.A₁ X.comm₁ (X.P₀ ⊔ X.P₀ᵍ[uG d]) = cLV d := by
      rw [ProductCommuteAux.dg_sup X.le₁ hPu, T₁.1.2.2, ProductCommuteAux.dg₁_P₀ X,
        ProductCommuteAux.cLV_eq d]
    exact ProductCommuteAux.eq_of_dg_eq X.injective₁ le_rfl (sup_le X.le₁ hPu) (e1.trans e2.symm)
  have hA₂ : X.A₂ = X.P₀ ⊔ X.P₀ᵍ[vG d] := by
    have e1 : ProductCommuteAux.dg X.A₂ X.comm₂ X.A₂ = lvM d := by
      unfold ProductCommuteAux.dg
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact X.range₂
    have e2 : ProductCommuteAux.dg X.A₂ X.comm₂ (X.P₀ ⊔ X.P₀ᵍ[vG d]) = lvM d := by
      rw [ProductCommuteAux.dg_sup X.le₂ hPv, T₂.1.2.2, ProductCommuteAux.dg₂_P₀ X,
        ProductCommuteAux.lvM_eq d]
    exact ProductCommuteAux.eq_of_dg_eq X.injective₂ le_rfl (sup_le X.le₂ hPv) (e1.trans e2.symm)
  have hP₁ : ⁅X.P₀, X.P₀ᵍ[t]⁆ = ⊥ :=
    ProductCommuteAux.comm_eq_bot_of_le X.le₁ (ProductCommuteAux.conjSub_mono X.le₁ t) X.comm₁
  have hP₂ : ⁅X.P₀, (X.P₀ᵍ[vG d])ᵍ[t]⁆ = ⊥ :=
    ProductCommuteAux.comm_eq_bot_of_le X.le₂ (ProductCommuteAux.conjSub_mono hPv t) X.comm₂
  have hP₃ : ⁅X.P₀ᵍ[uG d], X.P₀ᵍ[t]⁆ = ⊥ :=
    ProductCommuteAux.comm_eq_bot_of_le hPu (ProductCommuteAux.conjSub_mono X.le₁ t) X.comm₁
  have hwL : (uG d * vG d) ^ 3 ∈ L := Subgroup.pow_mem L (mul_mem d.u.2 d.v.2) 3
  have hwt : (uG d * vG d) ^ 3 * t = t * (uG d * vG d) ^ 3 := mem_centralizer_iff.1 htL _ hwL
  have hP₄ : ⁅X.P₀ᵍ[uG d], (X.P₀ᵍ[vG d])ᵍ[t]⁆ = ⊥ := by
    rw [hI4a, hI4b, ProductCommuteAux.conjSub_sup]
    have hM₀ : X.hat (d.M.map L.subtype) ≤ X.A₁ := (ProductCommuteAux.hat_le X _).trans X.le₁
    have hD₀ : X.hat (d.D.map L.subtype) ≤ X.A₁ := (ProductCommuteAux.hat_le X _).trans X.le₁
    refine ProductCommuteAux.comm_sup_sup_eq_bot ?_ ?_ ?_ ?_
    · exact ProductCommuteAux.comm_eq_bot_of_le hÛA (ProductCommuteAux.conjSub_mono hM₀ t)
        X.comm₁
    · have h1 : (((((X.hat (d.U₆.map L.subtype))ᵍ[vG d])ᵍ[uG d])ᵍ[vG d])ᵍ[t]) ≤
          (X.P₀ᵍ[t])ᵍ[(uG d * vG d) ^ 3] := by
        have h2 : (X.P₀ᵍ[(uG d * vG d) ^ 3])ᵍ[t] = (X.P₀ᵍ[t])ᵍ[(uG d * vG d) ^ 3] := by
          rw [ProductCommuteAux.conjSub_conjSub, ProductCommuteAux.conjSub_conjSub, hwt]
        exact (ProductCommuteAux.conjSub_mono hŴ t).trans h2.le
      have h4 : ⁅X.P₀ᵍ[(uG d * vG d) ^ 3], (X.P₀ᵍ[t])ᵍ[(uG d * vG d) ^ 3]⁆ = ⊥ := by
        rw [ProductCommuteAux.commutator_conjSub, hP₁, ProductCommuteAux.conjSub_bot]
      exact ProductCommuteAux.comm_eq_bot_of_le hÛ₁ h1 h4
    · exact ProductCommuteAux.comm_eq_bot_of_le hD₀ (ProductCommuteAux.conjSub_mono hM₀ t)
        X.comm₁
    · exact ProductCommuteAux.comm_eq_bot_of_le ((ProductCommuteAux.hat_le X _).trans X.le₂)
        (ProductCommuteAux.conjSub_mono hŴA t) X.comm₂
  have h2 : ⁅X.A₁, X.A₂ᵍ[t]⁆ = ⊥ := by
    rw [hA₁, hA₂, ProductCommuteAux.conjSub_sup]
    exact ProductCommuteAux.comm_sup_sup_eq_bot hP₁ hP₂ hP₃ hP₄
  refine ⟨h2, ?_⟩
  have h3 : ⁅X.A₁, X.A₂ᵍ[t]⁆ᵍ[t] = (⊥ : Subgroup G)ᵍ[t] := by rw [h2]
  rw [← ProductCommuteAux.commutator_conjSub, ProductCommuteAux.conjSub_bot,
    map_conj_inv_map_conj_inv htt] at h3
  exact h3

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
