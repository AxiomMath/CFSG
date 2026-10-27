module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdxDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup
open scoped commutatorElement

structure IdxModel {G : Type*} [Group G] (m : ℕ) (e : ℕ → G) (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ)
    (o : ℕ) : Prop where
  T_lt : ∀ i < m, ∀ j < m, T i j < m
  e_T : ∀ i < m, ∀ j < m, e (T i j) = e i * e j
  I_lt : ∀ i < m, I i < m
  e_I : ∀ i < m, e (I i) = (e i)⁻¹
  o_lt : o < m
  e_o : e o = 1
  inj : ∀ i < m, ∀ j < m, e i = e j → i = j

namespace IdxModel

variable {G : Type*} [Group G] {m : ℕ} {e : ℕ → G} {T : ℕ → ℕ → ℕ} {I : ℕ → ℕ} {o : ℕ}

@[expose] def sub (h : IdxModel m e T I o) : Subgroup G where
  carrier := {x | ∃ i < m, e i = x}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨T i j, h.T_lt i hi j hj, h.e_T i hi j hj⟩
  one_mem' := ⟨o, h.o_lt, h.e_o⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨I i, h.I_lt i hi, h.e_I i hi⟩

variable (h : IdxModel m e T I o)
include h

theorem e_mem {i : ℕ} (hi : i < m) : e i ∈ h.sub := ⟨i, hi, rfl⟩

theorem ci_lt {i j : ℕ} (hi : i < m) (hj : j < m) : ci T I i j < m :=
  h.T_lt _ (h.T_lt _ (h.T_lt i hi j hj) _ (h.I_lt i hi)) _ (h.I_lt j hj)

theorem e_ci {i j : ℕ} (hi : i < m) (hj : j < m) : e (ci T I i j) = ⁅e i, e j⁆ := by
  rw [ci, h.e_T _ (h.T_lt _ (h.T_lt i hi j hj) _ (h.I_lt i hi)) _ (h.I_lt j hj),
    h.e_T _ (h.T_lt i hi j hj) _ (h.I_lt i hi), h.e_T i hi j hj, h.e_I i hi, h.e_I j hj,
    commutatorElement_def]

theorem card_sub : Nat.card h.sub = m := by
  have hbij : Function.Bijective (fun i : Fin m => (⟨e i, h.e_mem i.2⟩ : h.sub)) := by
    refine ⟨fun i j hij => Fin.ext (h.inj i i.2 j j.2 (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨_, i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem pullback {G' : Type*} [Group G'] {V : Subgroup G'} (φ : ↥V →* G)
    (hφ : Function.Injective φ) (hrange : φ.range = h.sub) :
    ∃ e' : ℕ → G', ∃ h' : IdxModel m e' T I o, h'.sub = V ∧
      ∀ i < m, ∃ hv : e' i ∈ V, φ ⟨e' i, hv⟩ = e i := by
  have hpre : ∀ i < m, ∃ v : ↥V, φ v = e i := fun i hi => by
    have : e i ∈ φ.range := hrange ▸ h.e_mem hi
    exact this
  classical
  set e' : ℕ → G' := fun i => if hi : i < m then ((hpre i hi).choose : G') else 1 with he'
  have he'V : ∀ i < m, e' i ∈ V := fun i hi => by
    simp only [he', hi, ↓reduceDIte]
    exact (hpre i hi).choose.2
  have he'φ : ∀ i (hi : i < m), φ ⟨e' i, he'V i hi⟩ = e i := fun i hi => by
    have : (⟨e' i, he'V i hi⟩ : ↥V) = (hpre i hi).choose := by
      apply Subtype.ext
      simp only [he', hi, ↓reduceDIte]
    rw [this]
    exact (hpre i hi).choose_spec
  have key : ∀ i < m, ∀ (v : ↥V), φ v = e i → (v : G') = e' i := fun i hi v hv => by
    have := hφ (show φ v = φ ⟨e' i, he'V i hi⟩ by rw [hv, he'φ i hi])
    exact congrArg Subtype.val this
  refine ⟨e', ⟨h.T_lt, fun i hi j hj => ?_, h.I_lt, fun i hi => ?_, h.o_lt, ?_,
    fun i hi j hj hij => ?_⟩, ?_, fun i hi => ⟨he'V i hi, he'φ i hi⟩⟩
  · have := key (T i j) (h.T_lt i hi j hj) (⟨e' i, he'V i hi⟩ * ⟨e' j, he'V j hj⟩)
      (by rw [map_mul, he'φ i hi, he'φ j hj, h.e_T i hi j hj])
    rw [← this]
    rfl
  · have := key (I i) (h.I_lt i hi) (⟨e' i, he'V i hi⟩)⁻¹
      (by rw [map_inv, he'φ i hi, h.e_I i hi])
    rw [← this]
    rfl
  · have := key o h.o_lt 1 (by rw [map_one, h.e_o])
    rw [← this]
    rfl
  · apply h.inj i hi j hj
    rw [← he'φ i hi, ← he'φ j hj]
    congr 1
    exact Subtype.ext hij
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact he'V i hi
    · intro hx
      have : φ ⟨x, hx⟩ ∈ h.sub := hrange ▸ (⟨⟨x, hx⟩, rfl⟩ : φ ⟨x, hx⟩ ∈ φ.range)
      obtain ⟨i, hi, hie⟩ := this
      exact ⟨i, hi, (key i hi ⟨x, hx⟩ hie.symm).symm⟩

theorem center_eq {z : ℕ} (hc : ∀ i < m, (∀ j < m, T i j = T j i) → i = o ∨ i = z)
    {x : G} (hx : x ∈ h.sub) (hxc : ∀ y ∈ h.sub, x * y = y * x) : x = 1 ∨ x = e z := by
  obtain ⟨i, hi, rfl⟩ := hx
  rcases hc i hi fun j hj => h.inj _ (h.T_lt i hi j hj) _ (h.T_lt j hj i hi) (by
    rw [h.e_T i hi j hj, h.e_T j hj i hi]
    exact hxc _ (h.e_mem hj)) with h1 | h1
  · left
    rw [h1, h.e_o]
  · right
    rw [h1]

theorem centralizer_idx {L : List ℕ} (hL : ∀ l ∈ L, l < m) {z : ℕ}
    (hc : ∀ i < m, (∀ l ∈ L, T i l = T l i) → i = o ∨ i = z)
    {x : G} (hx : x ∈ h.sub) (hxc : ∀ l ∈ L, x * e l = e l * x) : x = 1 ∨ x = e z := by
  obtain ⟨i, hi, rfl⟩ := hx
  rcases hc i hi fun l hl => h.inj _ (h.T_lt i hi l (hL l hl)) _ (h.T_lt l (hL l hl) i hi) (by
    rw [h.e_T i hi l (hL l hl), h.e_T l (hL l hl) i hi]
    exact hxc l hl) with h1 | h1
  · left
    rw [h1, h.e_o]
  · right
    rw [h1]

end IdxModel

end CFSG.ComponentClassification.HarrisLit.EndB
