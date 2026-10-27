module

public import CFSG.Certificates.Kernel.OrbRow.Tight
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorization.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover
public import Certificates.Data.Kernel.Misc.PermClos
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KC.ThreeChain

open Subgroup Equiv CFSG.KC.OrbRow CFSG.KC.Misc.Clos CFSG.KC.LQT

variable {α : Type*}

theorem stabB_le (G : Subgroup (Perm α)) (b : ℕ → α) (i : ℕ) : stabB G b i ≤ G :=
  fun _ hg => hg.1

theorem stabB_finite (G : Subgroup (Perm α)) [Finite G] (b : ℕ → α) (i : ℕ) :
    Finite (stabB G b i) :=
  Finite.of_injective (Subgroup.inclusion (stabB_le G b i)) (Subgroup.inclusion_injective _)

theorem card_orbit_mul_le (G : Subgroup (Perm α)) [Finite G] (b : ℕ → α) (i : ℕ)
    (K : Subgroup (Perm α)) (hK : K ≤ stabB G b i) :
    Nat.card {y : α // ∃ g ∈ K, g • b i = y} * Nat.card (stabB G b (i + 1)) ≤
      Nat.card (stabB G b i) := by
  classical
  have := stabB_finite G b i
  set Y : Set α := {y | ∃ g ∈ K, g • b i = y}
  have hY : Y.Finite := by
    refine (Set.finite_range fun h : stabB G b i => (h : Perm α) (b i)).subset ?_
    rintro y ⟨g, hg, rfl⟩
    exact ⟨⟨g, hK hg⟩, rfl⟩
  change Nat.card Y * _ ≤ _
  rw [Nat.card_eq_card_finite_toFinset hY]
  refine card_ge_of_orbit (stabB G b i) (b i) hY.toFinset (fun x hx => ?_) _ (fun g hg => ?_)
  · obtain ⟨g, hg, rfl⟩ := hY.mem_toFinset.1 hx
    exact ⟨g, hK hg, rfl⟩
  · exact ⟨⟨hg.1, fun t ht => hg.2 t (by omega)⟩, hg.2 i (by omega)⟩

theorem card_fix_mul_le (G : Subgroup (Perm α)) [Finite G] (b : ℕ → α) (m : ℕ)
    (S : ℕ → List (Perm α)) (N : ℕ → ℕ)
    (hS : ∀ i < m, ∀ s ∈ S i, s ∈ G ∧ ∀ j < i, s (b j) = b j)
    (hN : ∀ i < m, N i ≤ Nat.card {y : α // ∃ g ∈ closure {g | g ∈ S i}, g • b i = y}) :
    Nat.card (stabB G b m) * ∏ i ∈ Finset.range m, N i ≤ Nat.card G := by
  have key : ∀ k ≤ m, Nat.card (stabB G b k) * ∏ i ∈ Finset.range k, N i ≤ Nat.card G := by
    intro k
    induction k with
    | zero =>
      intro _
      have := stabB_finite G b 0
      rw [Finset.prod_range_zero, mul_one]
      exact Nat.card_le_card_of_injective (Subgroup.inclusion (stabB_le G b 0))
        (Subgroup.inclusion_injective _)
    | succ k ih =>
      intro hk
      have hK : closure {g | g ∈ S k} ≤ stabB G b k :=
        (closure_le _).2 fun s hs => hS k (by omega) s hs
      have h1 := card_orbit_mul_le G b k _ hK
      have h2 : N k * Nat.card (stabB G b (k + 1)) ≤ Nat.card (stabB G b k) :=
        (Nat.mul_le_mul_right _ (hN k (by omega))).trans h1
      calc Nat.card (stabB G b (k + 1)) * ∏ i ∈ Finset.range (k + 1), N i
          = (N k * Nat.card (stabB G b (k + 1))) * ∏ i ∈ Finset.range k, N i := by
            rw [Finset.prod_range_succ]; ring
        _ ≤ Nat.card (stabB G b k) * ∏ i ∈ Finset.range k, N i := Nat.mul_le_mul_right _ h2
        _ ≤ Nat.card G := ih (by omega)
  exact key m le_rfl

theorem stabB_eq_inf_fixing (G : Subgroup (Perm α)) (b : ℕ → α) (m : ℕ) (F : Set α)
    (hF : ∀ a, a ∈ F ↔ ∃ t < m, b t = a) :
    stabB G b m = G ⊓ fixingSubgroup (Perm α) F := by
  ext g
  rw [mem_stabB, mem_inf, mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨hg, hf⟩
    refine ⟨hg, fun y hy => ?_⟩
    obtain ⟨t, ht, rfl⟩ := (hF y).1 hy
    exact hf t ht
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun t ht => hf (b t) ((hF _).2 ⟨t, ht, rfl⟩)⟩

@[expose] def setStab (G : Subgroup (Perm α)) (F : Finset α) : Subgroup (Perm α) where
  carrier := {t | t ∈ G ∧ ∀ i, t i ∈ F ↔ i ∈ F}
  one_mem' := ⟨G.one_mem, fun _ => Iff.rfl⟩
  mul_mem' {s t} hs ht := ⟨G.mul_mem hs.1 ht.1, fun i => by
    rw [Perm.mul_apply, hs.2, ht.2]⟩
  inv_mem' {t} ht := ⟨G.inv_mem ht.1, fun i => by
    rw [← ht.2 (t⁻¹ i), ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]⟩

noncomputable def restrF (G : Subgroup (Perm α)) (F : Finset α) : setStab G F →* Perm F where
  toFun t := (t : Perm α).subtypePerm fun i => t.2.2 i
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem card_setStab_le (G : Subgroup (Perm α)) [Finite G] (F : Finset α) :
    Nat.card (setStab G F) ≤ Nat.card ↥(G ⊓ fixingSubgroup (Perm α) (F : Set α)) * F.card.factorial := by
  classical
  have hle : setStab G F ≤ G := fun _ h => h.1
  have : Finite (setStab G F) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  have : Finite ↥(G ⊓ fixingSubgroup (Perm α) (F : Set α)) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : G ⊓ _ ≤ G))
      (Subgroup.inclusion_injective _)
  set φ := restrF G F
  have hk : Nat.card φ.ker ≤ Nat.card ↥(G ⊓ fixingSubgroup (Perm α) (F : Set α)) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨k.1.1, k.1.2.1, ?_⟩) ?_
    · change _ ∈ fixingSubgroup (Perm α) (F : Set α)
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h := congrArg (fun σ : Perm F => (σ ⟨y, hy⟩ : α)) (MonoidHom.mem_ker.1 k.2)
      exact h
    · intro a c h
      have h2 := Subtype.ext_iff.1 h
      exact Subtype.ext (Subtype.ext h2)
  have hr : Nat.card φ.range ≤ F.card.factorial := by
    calc Nat.card φ.range ≤ Nat.card (Perm F) :=
          Nat.card_le_card_of_injective _ (Subgroup.subtype_injective _)
      _ = F.card.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
  calc Nat.card (setStab G F) = Nat.card φ.ker * φ.ker.index := (card_mul_index _).symm
    _ = Nat.card φ.ker * Nat.card φ.range := by rw [index_ker]
    _ ≤ _ := Nat.mul_le_mul hk hr

theorem comm_of_mem_cent' {x c : Perm α} (hc : c ∈ centralizer ({x} : Set (Perm α))) :
    c * x = x * c :=
  ((mem_centralizer_iff.1 hc) x (Set.mem_singleton x)).symm

theorem two_card_cent_le (G : Subgroup (Perm α)) [Finite G] {x g : Perm α} (hg : g ∈ G)
    (F : Finset α) (hF : ∀ i, x i = i ↔ i ∈ F) (hgx : g * x * g⁻¹ = x⁻¹) (hne : x⁻¹ ≠ x) :
    2 * Nat.card ↥(G ⊓ centralizer ({x} : Set (Perm α))) ≤
      Nat.card ↥(G ⊓ fixingSubgroup (Perm α) (F : Set α)) * F.card.factorial := by
  classical
  set C := G ⊓ centralizer ({x} : Set (Perm α))
  have : Finite C :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : C ≤ G)) (Subgroup.inclusion_injective _)
  have hCT : ∀ c ∈ C, c ∈ setStab G F := by
    intro c hc
    have hcx := comm_of_mem_cent' (mem_inf.1 hc).2
    refine ⟨(mem_inf.1 hc).1, fun i => ?_⟩
    rw [← hF, ← hF, ← Perm.mul_apply x c, ← hcx, Perm.mul_apply]
    exact c.injective.eq_iff
  have hgT : g ∈ setStab G F := by
    refine ⟨hg, fun i => ?_⟩
    have hgx' : g * x = x⁻¹ * g := by rw [← hgx]; group
    rw [← hF, ← hF]
    constructor
    · intro h
      have : x⁻¹ (g i) = g i := by rw [Perm.inv_eq_iff_eq, h]
      rw [← Perm.mul_apply, ← hgx', Perm.mul_apply] at this
      exact g.injective this
    · intro h
      have : x⁻¹ (g i) = g i := by rw [← Perm.mul_apply, ← hgx', Perm.mul_apply, h]
      rw [Perm.inv_eq_iff_eq] at this
      exact this.symm
  have hgC : g ∉ C := by
    intro h
    apply hne
    rw [← hgx, comm_of_mem_cent' (mem_inf.1 h).2]
    group
  let f : C ⊕ C → setStab G F
    | .inl c => ⟨c.1, hCT c.1 c.2⟩
    | .inr c => ⟨g * c.1, (setStab G F).mul_mem hgT (hCT c.1 c.2)⟩
  have hf : Function.Injective f := by
    rintro (a | a) (c | c) h <;> simp only [f, Subtype.mk.injEq] at h
    · rw [Subtype.ext h]
    · exfalso
      apply hgC
      have : g = a.1 * c.1⁻¹ := by rw [h]; group
      rw [this]
      exact C.mul_mem a.2 (C.inv_mem c.2)
    · exfalso
      apply hgC
      have : g = c.1 * a.1⁻¹ := by rw [← h]; group
      rw [this]
      exact C.mul_mem c.2 (C.inv_mem a.2)
    · rw [Subtype.ext (mul_left_cancel h)]
  have : Finite (setStab G F) :=
    Finite.of_injective (Subgroup.inclusion (fun _ h => h.1 : setStab G F ≤ G))
      (Subgroup.inclusion_injective _)
  have h2 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, ← two_mul] at h2
  exact h2.trans (card_setStab_le G F)

theorem conj_cover_of_sylow {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (G P₀ : Subgroup M) (hPG : P₀ ≤ G) (hP : Nat.card P₀ = p ^ (Nat.card G).factorization p)
    {x : M} (h : ∀ s ∈ P₀, orderOf s = p → ∃ g ∈ G, s = g * x * g⁻¹) :
    ∀ t ∈ G, orderOf t = p → ∃ g ∈ G, t = g * x * g⁻¹ := by
  intro t ht htp
  obtain ⟨y, hy, hs⟩ :=
    CFSG.EvenSporadicStandard.HNRecog.TwoHSData.exists_conj_mem_of_orderOf_eq_prime hPG hP ht htp
  have hos : orderOf (y⁻¹ * t * y) = p := by
    rw [← htp]
    exact (SemiconjBy.orderOf_eq y⁻¹ (by simp [SemiconjBy, mul_assoc])).symm
  obtain ⟨g, hg, hsg⟩ := h _ hs hos
  refine ⟨y * g, G.mul_mem hy hg, ?_⟩
  calc t = y * (y⁻¹ * t * y) * y⁻¹ := by group
    _ = y * g * x * (y * g)⁻¹ := by rw [hsg]; group

variable {n : ℕ}

end CFSG.KC.ThreeChain

end
