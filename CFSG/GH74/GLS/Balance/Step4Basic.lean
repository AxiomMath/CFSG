module

public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace Step4

section Generic

variable {X : Type} [Group X]

theorem isPGroup_of_forall_mem {p : ℕ} {H : Subgroup X} (h : ∀ g ∈ H, ∃ k : ℕ, g ^ (p ^ k) = 1) :
    IsPGroup p H := by
  intro g
  obtain ⟨k, hk⟩ := h g g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem exists_pow_eq_one_of_mem {p : ℕ} {H : Subgroup X} (hH : IsPGroup p H) {g : X}
    (hg : g ∈ H) : ∃ k : ℕ, g ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_sup_of_commute {H K : Subgroup X} (h : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {g : X}
    (hg : g ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, g = a * b := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩
    · exact ⟨1, one_mem _, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
      _ = a * a' * (b * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = a⁻¹ * b⁻¹ := by
        have := h a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
        exact this.symm

theorem commutator_le_of_le_normalizer {T U : Subgroup X} (h : U ≤ normalizer (T : Set X)) :
    ⁅T, U⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro t ht g hg
  rw [commutatorElement_def]
  have := (Subgroup.mem_normalizer_iff.mp (h hg) t⁻¹).mp (inv_mem ht)
  have h2 : t * g * t⁻¹ * g⁻¹ = t * (g * t⁻¹ * g⁻¹) := by group
  rw [h2]
  exact mul_mem ht this

theorem closure_comm {s : Set X} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, a * b = b * a := by
  have h1 : Subgroup.closure s ≤ centralizer s := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact hc b hb a ha
  have h2 : Subgroup.closure s ≤ centralizer (Subgroup.closure s : Set X) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp (h1 hb) a ha).symm
  intro a ha b hb
  exact (mem_centralizer_iff.mp (h2 ha) b hb).symm

theorem isPGroup_closure_of_commute {p : ℕ} {s : Set X} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (h : ∀ a ∈ s, ∃ k : ℕ, a ^ (p ^ k) = 1) : IsPGroup p (Subgroup.closure s) := by
  refine isPGroup_of_forall_mem fun g hg => ?_
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact ⟨0, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨k, hk⟩ := ihx
    obtain ⟨l, hl⟩ := ihy
    refine ⟨k + l, ?_⟩
    have hxy : Commute x y := closure_comm hc x hx y hy
    have hx' : x ^ (p ^ (k + l)) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have hy' : y ^ (p ^ (k + l)) = 1 := by rw [pow_add, mul_comm, pow_mul, hl, one_pow]
    rw [hxy.mul_pow, hx', hy', one_mul]
  | inv x _ ihx =>
    obtain ⟨k, hk⟩ := ihx
    exact ⟨k, by rw [inv_pow, hk, inv_one]⟩

end Generic

section Finite

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_of_forall_mem {H : Subgroup X} {g : X}
    (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have hcard : Nat.card H ≤ Nat.card (H.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem mem_normalizer_closure {s : Set X} {g : X}
    (h : ∀ y ∈ s, g * y * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ normalizer (Subgroup.closure s : Set X) := by
  refine mem_normalizer_of_forall_mem fun y hy => ?_
  have hle : Subgroup.closure s ≤ (Subgroup.closure s).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    exact fun a ha => h a ha
  exact hle hy

end Finite

section Conj

variable {X : Type} [Group X]

@[expose] def cj (g : X) (K : Subgroup X) : Subgroup X := K.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g y : X} {K : Subgroup X} : y ∈ cj g K ↔ g⁻¹ * y * g ∈ K := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conj_mem_cj {g k : X} {K : Subgroup X} (hk : k ∈ K) : g * k * g⁻¹ ∈ cj g K := by
  rw [mem_cj]
  simpa [mul_assoc] using hk

theorem cj_mul (g h : X) (K : Subgroup X) : cj (g * h) K = cj g (cj h K) := by
  ext y
  simp only [mem_cj, mul_inv_rev]
  have : h⁻¹ * g⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
  rw [this]

theorem cj_one (K : Subgroup X) : cj 1 K = K := by
  ext y
  simp [mem_cj]

theorem cj_le_cj_iff {g : X} {K L : Subgroup X} : cj g K ≤ cj g L ↔ K ≤ L := by
  constructor
  · intro h k hk
    have := h (conj_mem_cj (g := g) hk)
    rw [mem_cj] at this
    simpa [mul_assoc] using this
  · intro h y hy
    rw [mem_cj] at hy ⊢
    exact h hy

theorem cj_injective (g : X) : Function.Injective (cj g) := fun _ _ h =>
  le_antisymm (cj_le_cj_iff.mp h.le) (cj_le_cj_iff.mp h.ge)

theorem mem_normalizer_iff_cj_eq {g : X} {K : Subgroup X} :
    g ∈ normalizer (K : Set X) ↔ cj g K = K := Subgroup.mem_normalizer_iff_map_conj_eq

theorem cj_pow_succ (w : X) (n : ℕ) (K : Subgroup X) : cj (w ^ (n + 1)) K = cj w (cj (w ^ n) K) := by
  rw [pow_succ', cj_mul]

theorem isComponent_cj {g : X} {K : Subgroup X} (hK : IsComponent K) : IsComponent (cj g K) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

end Conj

section Layer

variable {X : Type} [Group X]

@[expose] def compProd (S : Set (Subgroup X)) : Subgroup X := ⨆ K ∈ S, K

theorem le_compProd {S : Set (Subgroup X)} {K : Subgroup X} (hK : K ∈ S) : K ≤ compProd S :=
  le_iSup₂ (f := fun (K : Subgroup X) (_ : K ∈ S) => K) K hK

theorem compProd_le {S : Set (Subgroup X)} {H : Subgroup X} (h : ∀ K ∈ S, K ≤ H) :
    compProd S ≤ H :=
  iSup₂_le h

theorem compProd_union (S S' : Set (Subgroup X)) :
    compProd (S ∪ S') = compProd S ⊔ compProd S' :=
  iSup_union

theorem compProd_empty : compProd (∅ : Set (Subgroup X)) = ⊥ := by
  simp [compProd]

theorem compProd_le_layer {S : Set (Subgroup X)} (hS : ∀ K ∈ S, IsComponent K) :
    compProd S ≤ layer X :=
  compProd_le fun _ hK => CFSG.LocalCores.component_le_layer (hS _ hK)

@[expose] def layerZ (X : Type) [Group X] : Subgroup X := layer X ⊓ centralizer (layer X : Set X)

theorem mem_centralizer_layer_iff {g : X} :
    g ∈ centralizer (layer X : Set X) ↔
      ∀ K : Subgroup X, IsComponent K → g ∈ centralizer (K : Set X) := by
  constructor
  · intro h K hK
    exact Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer hK) h
  · intro h
    have hle : layer X ≤ centralizer ({g} : Set X) := by
      refine sSup_le fun K hK k hk => ?_
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp (h K hK) k hk
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hle hk)

theorem mem_layerZ_iff {g : X} :
    g ∈ layerZ X ↔ g ∈ layer X ∧ ∀ K : Subgroup X, IsComponent K → g ∈ centralizer (K : Set X) := by
  rw [layerZ, Subgroup.mem_inf, mem_centralizer_layer_iff]

theorem layerZ_comm {a b : X} (ha : a ∈ layerZ X) (hb : b ∈ layerZ X) : a * b = b * a := by
  have := mem_centralizer_iff.mp ha.2 b hb.1
  exact this.symm

theorem layerZ_normal [Finite X] : (layerZ X).Normal := by
  have : (layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  unfold layerZ
  infer_instance

theorem layerZ_isPGroup [Finite X] (hO : pPrimeCore 2 X = ⊥) : IsPGroup 2 (layerZ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (layerZ X).Normal := layerZ_normal
  have : IsMulCommutative (layerZ X) :=
    ⟨⟨fun a b => Subtype.ext (layerZ_comm a.2 b.2)⟩⟩
  exact CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO

theorem inf_centralizer_le_layerZ [Finite X] {K : Subgroup X} (hK : IsComponent K) :
    K ⊓ centralizer (K : Set X) ≤ layerZ X := by
  intro g hg
  rw [mem_layerZ_iff]
  refine ⟨CFSG.LocalCores.component_le_layer hK hg.1, fun K' hK' => ?_⟩
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with rfl | h
  · exact hg.2
  · rw [mem_centralizer_iff]
    intro k hk
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hg.1
    exact (mem_centralizer_iff.mp this k hk)

theorem compProd_le_centralizer [Finite X] {S : Set (Subgroup X)} (hS : ∀ K ∈ S, IsComponent K)
    {K' : Subgroup X} (hK' : IsComponent K') (hnot : K' ∉ S) :
    compProd S ≤ centralizer (K' : Set X) := by
  refine compProd_le fun K hK => ?_
  rcases CFSG.LocalCores.distinct_components_commute (hS K hK) hK' with h | h
  · exact absurd (h ▸ hK) hnot
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem compProd_commute [Finite X] {S₁ S₂ : Set (Subgroup X)} (h₁ : ∀ K ∈ S₁, IsComponent K)
    (h₂ : ∀ K ∈ S₂, IsComponent K) (hd : Disjoint S₁ S₂) :
    ∀ a ∈ compProd S₁, ∀ b ∈ compProd S₂, a * b = b * a := by
  have hle : compProd S₂ ≤ centralizer (compProd S₁ : Set X) := by
    refine compProd_le fun K' hK' => ?_
    have hnot : K' ∉ S₁ := fun h => Set.disjoint_left.mp hd h hK'
    have h1 := compProd_le_centralizer h₁ (h₂ K' hK') hnot
    have h2 : ⁅compProd S₁, K'⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [Subgroup.commutator_comm] at h2
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  intro a ha b hb
  exact mem_centralizer_iff.mp (hle hb) a ha

theorem compProd_inf_le_layerZ [Finite X] {S₁ S₂ : Set (Subgroup X)}
    (h₁ : ∀ K ∈ S₁, IsComponent K) (h₂ : ∀ K ∈ S₂, IsComponent K) (hd : Disjoint S₁ S₂) :
    compProd S₁ ⊓ compProd S₂ ≤ layerZ X := by
  intro g hg
  rw [mem_layerZ_iff]
  refine ⟨compProd_le_layer h₁ hg.1, fun K hK => ?_⟩
  by_cases hK1 : K ∈ S₁
  · have hK2 : K ∉ S₂ := fun h => Set.disjoint_left.mp hd hK1 h
    exact compProd_le_centralizer h₂ hK hK2 hg.2
  · exact compProd_le_centralizer h₁ hK hK1 hg.1

theorem mem_normalizer_compProd [Finite X] {S : Set (Subgroup X)} {g : X}
    (h : ∀ K ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ compProd S) : g ∈ normalizer (compProd S : Set X) := by
  refine mem_normalizer_of_forall_mem fun y hy => ?_
  have hle : compProd S ≤ (compProd S).comap (MulAut.conj g).toMonoidHom :=
    compProd_le fun K hK k hk => h K hK k hk
  exact hle hy

end Layer

end Step4

section API

variable {X : Type} [Group X] {x : X} {V : Subgroup X}

theorem SolvAPI.w_mul_x (A : SolvAPI x V) : A.w * x = x * A.w :=
  mem_centralizer_singleton_iff.mp (A.hVC A.w_mem)

theorem SolvAPI.x_mem_centralizer_P (A : SolvAPI x V) : x ∈ centralizer (A.P : Set X) := by
  rw [mem_centralizer_iff]
  intro p hp
  exact mem_centralizer_singleton_iff.mp (A.hVC (A.P_le hp))

end API

end CFSG.GH74.GLS.Balance
