module

public import CFSG.LocalAnalysis.OddStandard.Seitz77V1ActModel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.Seitz77.V1Act

open Subgroup CFSG.ABGLocalTools CFSG.PSL3Four CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

section Identification

structure RadicalIdent {G : Type*} [Group G] (A W : Subgroup G) where
  F : Subgroup (Equiv.Perm (Fin 42))
  hF : Enumerates F (enumBFS 42 fGens 16).tabs.toList
  g : normalizer (A : Set G) →* Equiv.Perm (Fin 42)
  r₀ : Equiv.Perm (Fin 42)
  r₀_mem : r₀ ∈ R
  g_mem : ∀ n, g n ∈ R
  g_ker : ∀ n, g n = 1 ↔ (n : G) ∈ centralizer (A : Set G)
  W_le : W ≤ A
  W_comm : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w
  g_inj : ∀ n n' : normalizer (A : Set G), (n : G) ∈ W → (n' : G) ∈ W → g n = g n' → n = n'
  img : ∀ y, y ∈ (W.subgroupOf (normalizer (A : Set G))).map g ↔ r₀⁻¹ * y * r₀ ∈ F
  F_cent : ∀ x ∈ R, (∀ f ∈ F, x * f = f * x) → x ∈ F
  F_comm : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f

variable {G : Type*} [Group G] {A W : Subgroup G} (I : RadicalIdent A W)

namespace RadicalIdent

include I

def conj (n : normalizer (A : Set G)) : Equiv.Perm (Fin 42) := I.r₀⁻¹ * I.g n * I.r₀

theorem conj_mem (n : normalizer (A : Set G)) : I.conj n ∈ R :=
  R.mul_mem (R.mul_mem (R.inv_mem I.r₀_mem) (I.g_mem n)) I.r₀_mem

theorem conj_mem_F {n : normalizer (A : Set G)} (hn : (n : G) ∈ W) : I.conj n ∈ I.F :=
  (I.img _).1 ⟨n, Subgroup.mem_subgroupOf.2 hn, rfl⟩

theorem exists_of_mem_F {f : Equiv.Perm (Fin 42)} (hf : f ∈ I.F) :
    ∃ n : normalizer (A : Set G), (n : G) ∈ W ∧ I.g n = I.r₀ * f * I.r₀⁻¹ := by
  have : I.r₀⁻¹ * (I.r₀ * f * I.r₀⁻¹) * I.r₀ ∈ I.F := by
    simpa [mul_assoc] using hf
  obtain ⟨n, hn, hgn⟩ := (I.img _).2 this
  exact ⟨n, Subgroup.mem_subgroupOf.1 hn, hgn⟩

theorem exists_decomp_of_conj_mem {x : G} (hx : x ∈ normalizer (A : Set G))
    (hc : I.conj ⟨x, hx⟩ ∈ I.F) : ∃ n ∈ W, ∃ k ∈ centralizer (A : Set G), x = n * k := by
  obtain ⟨n, hn, hgn⟩ := (I.img (I.g ⟨x, hx⟩)).2 (by simpa [conj] using hc)
  have hn' : (n : G) ∈ W := Subgroup.mem_subgroupOf.1 hn
  have h1 : I.g (n⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hgn, inv_mul_cancel]
  have h2 : (n : G)⁻¹ * x ∈ centralizer (A : Set G) := (I.g_ker _).1 h1
  exact ⟨n, hn', _, h2, by group⟩

theorem mem_sup_of_conj_mem {x : G} (hx : x ∈ normalizer (A : Set G))
    (hc : I.conj ⟨x, hx⟩ ∈ I.F) : x ∈ W ⊔ centralizer (A : Set G) := by
  obtain ⟨n, hn, k, hk, rfl⟩ := I.exists_decomp_of_conj_mem hx hc
  exact mul_mem_sup hn hk

theorem centralizes_of_conj_mem {x : G} (hx : x ∈ normalizer (A : Set G))
    (hc : I.conj ⟨x, hx⟩ ∈ I.F) : x ∈ centralizer (W : Set G) := by
  obtain ⟨n, hn, k, hk, rfl⟩ := I.exists_decomp_of_conj_mem hx hc
  rw [mem_centralizer_iff]
  intro w hw
  have h1 : w * k = k * w := mem_centralizer_iff.1 hk w (I.W_le hw)
  have h2 : w * n = n * w := I.W_comm w hw n hn
  calc w * (n * k) = (w * n) * k := by group
    _ = n * (w * k) := by rw [h2]; group
    _ = n * (k * w) := by rw [h1]
    _ = n * k * w := by group

theorem conj_mem_F_of_centralizes {x : G} (hx : x ∈ normalizer (A : Set G))
    (hxW : ∀ w ∈ W, w * x = x * w) : I.conj ⟨x, hx⟩ ∈ I.F := by
  refine I.F_cent _ (I.conj_mem _) fun f hf => ?_
  obtain ⟨n, hn, hgn⟩ := I.exists_of_mem_F hf
  have h1 : (n : G) * x = x * n := hxW _ hn
  have hcomm : I.g n * I.g ⟨x, hx⟩ = I.g ⟨x, hx⟩ * I.g n := by
    rw [← map_mul, ← map_mul]
    exact congrArg I.g (Subtype.ext h1)
  rw [hgn] at hcomm
  unfold conj
  calc I.r₀⁻¹ * I.g ⟨x, hx⟩ * I.r₀ * f
      = I.r₀⁻¹ * (I.g ⟨x, hx⟩ * (I.r₀ * f * I.r₀⁻¹)) * I.r₀ := by group
    _ = I.r₀⁻¹ * ((I.r₀ * f * I.r₀⁻¹) * I.g ⟨x, hx⟩) * I.r₀ := by rw [← hcomm]
    _ = f * (I.r₀⁻¹ * I.g ⟨x, hx⟩ * I.r₀) := by group

theorem centralizer_le :
    normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ W ⊔ centralizer (A : Set G) := by
  rintro x ⟨hx, hxc⟩
  exact I.mem_sup_of_conj_mem hx
    (I.conj_mem_F_of_centralizes hx fun w hw => mem_centralizer_iff.1 hxc w hw)

theorem norm_conj {x : G} (hx : x ∈ normalizer (A : Set G)) (hxW : x ∈ normalizer (W : Set G)) :
    Norm I.F (I.conj ⟨x, hx⟩) := by
  unfold Norm
  intro f hf
  obtain ⟨n, hn, hgn⟩ := I.exists_of_mem_F hf
  have hxw : x * n * x⁻¹ ∈ W := (mem_normalizer_iff.1 hxW (n : G)).1 hn
  have hxwN : x * n * x⁻¹ ∈ normalizer (A : Set G) :=
    mul_mem (mul_mem hx n.2) (inv_mem hx)
  have h1 := I.conj_mem_F (n := ⟨x * n * x⁻¹, hxwN⟩) hxw
  have h2 : I.g ⟨x * n * x⁻¹, hxwN⟩ = I.g ⟨x, hx⟩ * I.g n * (I.g ⟨x, hx⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [conj, h2, hgn] at h1
  unfold conj
  have e : I.r₀⁻¹ * (I.g ⟨x, hx⟩ * (I.r₀ * f * I.r₀⁻¹) * (I.g ⟨x, hx⟩)⁻¹) * I.r₀ =
      I.r₀⁻¹ * I.g ⟨x, hx⟩ * I.r₀ * f * (I.r₀⁻¹ * I.g ⟨x, hx⟩ * I.r₀)⁻¹ := by group
  rw [e] at h1
  exact h1

theorem mem_sup_of_conj_centralizes {x : G} (hx : x ∈ normalizer (A : Set G))
    (h : ∀ f ∈ I.F, I.conj ⟨x, hx⟩ * f * (I.conj ⟨x, hx⟩)⁻¹ = f) :
    x ∈ W ⊔ centralizer (A : Set G) :=
  I.mem_sup_of_conj_mem hx (I.F_cent _ (I.conj_mem _) fun f hf => by
    have := h f hf
    calc I.conj ⟨x, hx⟩ * f = (I.conj ⟨x, hx⟩ * f * (I.conj ⟨x, hx⟩)⁻¹) * I.conj ⟨x, hx⟩ := by
          group
      _ = f * I.conj ⟨x, hx⟩ := by rw [this])

theorem card_fixed_le_four (hcard : ActCard I.F) {x : G} (hx : x ∈ normalizer (A : Set G))
    (hxW : x ∈ normalizer (W : Set G)) (hxout : x ∉ W ⊔ centralizer (A : Set G)) :
    Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ 4 := by
  have hne : ∃ f ∈ I.F, I.conj ⟨x, hx⟩ * f * (I.conj ⟨x, hx⟩)⁻¹ ≠ f := by
    by_contra hcon
    push Not at hcon
    exact hxout (I.mem_sup_of_conj_centralizes hx hcon)
  unfold ActCard at hcard
  have h4 := hcard _ (I.conj_mem _) (I.norm_conj hx hxW) hne
  refine le_trans ?_ h4
  have hmemN : ∀ w : ↥(W ⊓ centralizer ({x} : Set G)),
      (w : G) ∈ normalizer (A : Set G) := fun w => le_normalizer (I.W_le w.2.1)
  let φ : ↥(W ⊓ centralizer ({x} : Set G)) →
      ↥(I.F ⊓ centralizer ({I.conj ⟨x, hx⟩} : Set (Equiv.Perm (Fin 42)))) := fun w =>
    ⟨I.conj ⟨w, hmemN w⟩, Subgroup.mem_inf.2 ⟨I.conj_mem_F (n := ⟨w, hmemN w⟩) w.2.1,
      Subgroup.mem_centralizer_singleton_iff.2 (by
        have h1 : (w : G) * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 w.2.2
        have h2 : I.g ⟨w, hmemN w⟩ * I.g ⟨x, hx⟩ = I.g ⟨x, hx⟩ * I.g ⟨w, hmemN w⟩ := by
          rw [← map_mul, ← map_mul]
          exact congrArg I.g (Subtype.ext h1)
        unfold conj
        calc I.r₀⁻¹ * I.g ⟨w, hmemN w⟩ * I.r₀ * (I.r₀⁻¹ * I.g ⟨x, hx⟩ * I.r₀)
            = I.r₀⁻¹ * (I.g ⟨w, hmemN w⟩ * I.g ⟨x, hx⟩) * I.r₀ := by group
          _ = I.r₀⁻¹ * (I.g ⟨x, hx⟩ * I.g ⟨w, hmemN w⟩) * I.r₀ := by rw [h2]
          _ = I.r₀⁻¹ * I.g ⟨x, hx⟩ * I.r₀ * (I.r₀⁻¹ * I.g ⟨w, hmemN w⟩ * I.r₀) := by
            group)⟩⟩
  have hinj : Function.Injective φ := by
    intro w w' hww
    have h1 : I.conj ⟨w, hmemN w⟩ = I.conj ⟨w', hmemN w'⟩ := congrArg Subtype.val hww
    unfold conj at h1
    have h2 : I.g ⟨w, hmemN w⟩ = I.g ⟨w', hmemN w'⟩ := by
      have h3 : I.r₀⁻¹ * (I.g ⟨w, hmemN w⟩ * I.r₀) = I.r₀⁻¹ * (I.g ⟨w', hmemN w'⟩ * I.r₀) := by
        simpa only [mul_assoc] using h1
      exact mul_right_cancel (mul_left_cancel h3)
    have h3 := I.g_inj _ _ w.2.1 w'.2.1 h2
    have h4 := congrArg Subtype.val h3
    exact Subtype.ext h4
  exact Nat.card_le_card_of_injective φ hinj

theorem relIndex_le_four (hT : ActTriple I.F) {E : Subgroup G}
    (hE : E ≤ normalizer (A : Set G) ⊓ normalizer (W : Set G))
    (h : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ centralizer (W : Set G) ∧ x * x ∈ centralizer (W : Set G)) :
    (centralizer (W : Set G)).relIndex E ≤ 4 := by
  have hEN : E ≤ normalizer (A : Set G) := hE.trans inf_le_left
  have hEW : E ≤ normalizer (W : Set G) := hE.trans inf_le_right
  let c' : ↥E →* Equiv.Perm (Fin 42) :=
    ((MulAut.conj I.r₀⁻¹).toMonoidHom.comp I.g).comp (Subgroup.inclusion hEN)
  have hc' : ∀ x : ↥E, c' x = I.conj ⟨x, hEN x.2⟩ := fun x => by
    simp only [c', conj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
    rfl
  have hcrit : ∀ x : ↥E, c' x ∈ I.F ↔ (x : G) ∈ centralizer (W : Set G) := by
    intro x
    rw [hc']
    exact ⟨I.centralizes_of_conj_mem (hEN x.2), fun hxc =>
      I.conj_mem_F_of_centralizes (hEN x.2) fun w hw => mem_centralizer_iff.1 hxc w hw⟩
  have hsub : (centralizer (W : Set G)).subgroupOf E = I.F.comap c' := by
    ext x
    exact (hcrit x).symm
  rw [Subgroup.relIndex, hsub, Subgroup.index_comap]
  refine relIndex_le_four_of_triple I.F_cent I.F_comm hT ?_ ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [hc']
    exact I.conj_mem _
  · rintro _ ⟨x, rfl⟩
    rw [hc']
    exact I.norm_conj (hEN x.2) (hEW x.2)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hxy : c' x * c' y * (c' x)⁻¹ * (c' y)⁻¹ = c' (x * y * x⁻¹ * y⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hxy, hcrit]
    have := (h x x.2 y y.2).1
    rwa [commutatorElement_def] at this
  · rintro _ ⟨x, rfl⟩
    have hxx : c' x * c' x = c' (x * x) := by simp only [map_mul]
    rw [hxx, hcrit]
    exact (h x x.2 x x.2).2

end RadicalIdent

end Identification

end CFSG.OddStandard.Seitz77.V1Act
