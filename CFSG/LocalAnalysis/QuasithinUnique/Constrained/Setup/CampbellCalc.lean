module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.BlueprintB2Frattini

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup

section Calc

variable {G : Type*} [Group G]

open scoped commutatorElement in
@[expose] def commModIn (F V N : Subgroup G) (hNV : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V) :
    Subgroup G where
  carrier := {x | x ∈ N ∧ ∀ f ∈ F, ⁅f, x⁆ ∈ V}
  one_mem' := ⟨one_mem _, fun f _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨mul_mem hxN hyN, fun f hf => ?_⟩
    have h1 : ⁅f, x * y⁆ = ⁅f, x⁆ * (x * ⁅f, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hx f hf) (hNV x hxN _ (hy f hf))
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨inv_mem hxN, fun f hf => ?_⟩
    have h1 : ⁅f, x⁻¹⁆ = x⁻¹ * ⁅f, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact hNV x⁻¹ (inv_mem hxN) _ (inv_mem (hx f hf))

open scoped commutatorElement in
theorem mem_commModIn {F V N : Subgroup G} {hNV : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V} {x : G} :
    x ∈ commModIn F V N hNV ↔ x ∈ N ∧ ∀ f ∈ F, ⁅f, x⁆ ∈ V := Iff.rfl

theorem commutator_iSup_le {ι : Sort*} (X : ι → Subgroup G) {F V N : Subgroup G}
    (hNV : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V) (hX : ∀ i, X i ≤ N)
    (h : ∀ i, ⁅F, X i⁆ ≤ V) : ⁅F, ⨆ i, X i⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro f hf x hx
  have hle : (⨆ i, X i) ≤ commModIn F V N hNV :=
    iSup_le fun i y hy => ⟨hX i hy, fun f' hf' => Subgroup.commutator_le.mp (h i) f' hf' y hy⟩
  exact (hle hx).2 f hf

theorem commutator_sup_le {F V N X Y : Subgroup G}
    (hNV : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V) (hX : X ≤ N) (hY : Y ≤ N)
    (hXV : ⁅F, X⁆ ≤ V) (hYV : ⁅F, Y⁆ ≤ V) : ⁅F, X ⊔ Y⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro f hf x hx
  have hle : X ⊔ Y ≤ commModIn F V N hNV :=
    sup_le (fun y hy => ⟨hX hy, fun f' hf' => Subgroup.commutator_le.mp hXV f' hf' y hy⟩)
      (fun y hy => ⟨hY hy, fun f' hf' => Subgroup.commutator_le.mp hYV f' hf' y hy⟩)
  exact (hle hx).2 f hf

theorem commutator_iSup_le_normal {ι : Sort*} (X : ι → Subgroup G) {F V : Subgroup G} [V.Normal]
    (h : ∀ i, ⁅F, X i⁆ ≤ V) : ⁅F, ⨆ i, X i⁆ ≤ V :=
  commutator_iSup_le X (N := ⊤) (fun n _ v hv => (inferInstance : V.Normal).conj_mem v hv n)
    (fun _ => le_top) h

open scoped commutatorElement in
instance commModIn_top_normal (F V : Subgroup G) [F.Normal] [V.Normal] :
    (commModIn F V ⊤ (fun n _ v hv => (inferInstance : V.Normal).conj_mem v hv n)).Normal := by
  refine ⟨fun n hn g => ⟨Subgroup.mem_top _, fun f hf => ?_⟩⟩
  have h1 : ⁅f, g * n * g⁻¹⁆ = g * ⁅g⁻¹ * f * g, n⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  have h2 : g⁻¹ * f * g ∈ F := by
    have := (inferInstance : F.Normal).conj_mem f hf g⁻¹
    simpa using this
  exact (inferInstance : V.Normal).conj_mem _ (hn.2 _ h2) g

theorem pPrimeGen_top_le_of_sup_eq_top {p : ℕ} [Fact p.Prime] [Finite G] {N P : Subgroup G}
    [N.Normal] (hP : IsPGroup p P) (htop : N ⊔ P = ⊤) :
    CFSG.Quasithin.BlueprintB2.pPrimeGen p (⊤ : Subgroup G) ≤ N := by
  refine CFSG.Quasithin.BlueprintB2.pPrimeGen_le_of_pow_mem fun x _ => ?_
  have hx : x ∈ N ⊔ P := htop ▸ Subgroup.mem_top x
  obtain ⟨n, hn, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨j, hj⟩ := hP ⟨q, hq⟩
  refine ⟨j, ?_⟩
  have hj' : q ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  have : QuotientGroup.mk' N ((n * q) ^ p ^ j) = 1 := by
    rw [map_pow, map_mul, hn1, one_mul, ← map_pow, hj', map_one]
  exact (QuotientGroup.eq_one_iff _).mp this

end Calc

end CFSG.QuasithinUnique.Setup.Campbell
