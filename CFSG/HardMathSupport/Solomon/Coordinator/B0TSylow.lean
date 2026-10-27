module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem exists_sylow_inf_normal {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime]
    (S : Sylow p D) (M : Subgroup D) [M.Normal] :
    ∃ Q : Sylow p M, (Q : Subgroup M).map M.subtype = (S : Subgroup D) ⊓ M := by
  set R : Subgroup D := (S : Subgroup D) ⊓ M with hR
  have hRp : IsPGroup p R := S.isPGroup'.to_inf_left
  have h1 : R.relIndex (S : Subgroup D) * (S : Subgroup D).relIndex ((S : Subgroup D) ⊔ M) =
      R.relIndex ((S : Subgroup D) ⊔ M) :=
    Subgroup.relIndex_mul_relIndex (H := R) (K := (S : Subgroup D)) (L := (S : Subgroup D) ⊔ M)
      inf_le_left le_sup_left
  have h2 : R.relIndex M * M.relIndex ((S : Subgroup D) ⊔ M) =
      R.relIndex ((S : Subgroup D) ⊔ M) :=
    Subgroup.relIndex_mul_relIndex (H := R) (K := M) (L := (S : Subgroup D) ⊔ M)
      inf_le_right le_sup_right
  have h3 : M.relIndex ((S : Subgroup D) ⊔ M) = M.relIndex (S : Subgroup D) :=
    Subgroup.relIndex_sup_right (H := (S : Subgroup D)) (K := M)
  have h4 : R.relIndex (S : Subgroup D) = M.relIndex (S : Subgroup D) :=
    Subgroup.inf_relIndex_left (S : Subgroup D) M
  have ha : M.relIndex (S : Subgroup D) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (H := M.subgroupOf (S : Subgroup D))
  have h5 : R.relIndex M = (S : Subgroup D).relIndex ((S : Subgroup D) ⊔ M) := by
    have e : R.relIndex M * M.relIndex ((S : Subgroup D) ⊔ M) =
        M.relIndex (S : Subgroup D) * (S : Subgroup D).relIndex ((S : Subgroup D) ⊔ M) := by
      rw [h2, ← h1, h4]
    rw [h3] at e
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha) (by rw [e, mul_comm])
  have hidx : ¬ p ∣ (R.subgroupOf M).index := by
    have : (R.subgroupOf M).index = R.relIndex M := rfl
    rw [this, h5]
    intro hd
    exact S.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hp : IsPGroup p (R.subgroupOf M) := hRp.comap_subtype
  refine ⟨hp.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.2 inf_le_right

theorem exists_sylow_fixed_of_pGroup {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {B E : Subgroup G} (hB : IsPGroup q B) (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hq : ¬ q ∣ Nat.card E) :
    ∃ P : Sylow p E, ∀ b ∈ B, ∀ x ∈ (P : Subgroup E), b * (x : G) * b⁻¹ ∈ (P : Subgroup E).map E.subtype := by
  let φ : B →* MulAut E := (Subgroup.normalizerMonoidHom E).comp (Subgroup.inclusion hBE)
  let _ : MulDistribMulAction B E := MulDistribMulAction.compHom E φ
  have hdvd : Nat.card (Sylow p E) ∣ Nat.card E :=
    (Sylow.card_dvd_index (p := p) (Sylow.nonempty (p := p) (G := E)).some).trans (Subgroup.index_dvd_card _)
  obtain ⟨P, hP⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card (α := Sylow p E)
    (fun h => hq (h.trans hdvd))
  refine ⟨P, fun b hb x hx => ?_⟩
  have h1 : (⟨b, hb⟩ : B) • P = P := hP ⟨b, hb⟩
  have h2 : (⟨b, hb⟩ : B) • (P : Subgroup E) = P := congrArg (fun T : Sylow p E => (T : Subgroup E)) h1
  have h3 : φ ⟨b, hb⟩ x ∈ (P : Subgroup E) := by
    rw [← h2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
  exact ⟨_, h3, by simp [φ]⟩

end CFSG.HardMathSupport.Solomon.Coordinator
