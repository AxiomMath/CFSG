module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type*} [Group X]

theorem sylow_normal_of_comm (h : ∀ a b : X, a * b = b * a) {p : ℕ} (S : Sylow p X) :
    (S : Subgroup X).Normal :=
  ⟨fun n hn g => by rw [h g n, mul_inv_cancel_right]; exact hn⟩

theorem sylow_normal_of_isCyclic [IsCyclic X] {p : ℕ} (S : Sylow p X) :
    (S : Subgroup X).Normal :=
  sylow_normal_of_comm (fun a b => (IsCyclic.isMulCommutative (α := X)).is_comm.comm a b) S

theorem sylow_normal_of_not_dvd [Finite X] {p : ℕ} [Fact p.Prime] (h : ¬ p ∣ Nat.card X)
    (S : Sylow p X) : (S : Subgroup X).Normal := by
  have h1 : Nat.card (S : Subgroup X) = 1 := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd h, pow_zero]
  rw [Subgroup.eq_bot_of_card_eq _ h1]
  infer_instance

private theorem card_sylow_eq_one_of_index_le [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (S : Sylow p X) (h : (S : Subgroup X).index ≤ p) : Nat.card (Sylow p X) = 1 := by
  have h1 := card_sylow_modEq_one p X
  have hpos : 0 < (S : Subgroup X).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : Nat.card (Sylow p X) ≤ p := (Nat.le_of_dvd hpos S.card_dvd_index).trans h
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt hp.out.one_lt
  have h4 : Nat.card (Sylow p X) ≠ p := by
    intro he
    have h1' := h1
    rw [he, Nat.ModEq, Nat.mod_self, h1p] at h1'
    exact zero_ne_one h1'
  have h6 : Nat.card (Sylow p X) < p := lt_of_le_of_ne h3 h4
  have h1' := h1
  rw [Nat.ModEq, Nat.mod_eq_of_lt h6, h1p] at h1'
  exact h1'

theorem sylow_normal_of_card_dvd [Finite X] {p a m : ℕ} [hp : Fact p.Prime]
    (h : Nat.card X ∣ p ^ a * m) (hm0 : 0 < m) (hm : m ≤ p) (S : Sylow p X) :
    (S : Subgroup X).Normal := by
  have hidx : (S : Subgroup X).index ∣ m := by
    have hcop : Nat.Coprime (S : Subgroup X).index (p ^ a) :=
      (Nat.Coprime.pow_left a
        ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr S.not_dvd_index)).symm
    exact hcop.dvd_of_dvd_mul_left ((Subgroup.index_dvd_card _).trans h)
  haveI : Subsingleton (Sylow p X) :=
    (Nat.card_eq_one_iff_unique.mp
      (card_sylow_eq_one_of_index_le S ((Nat.le_of_dvd hm0 hidx).trans hm))).1
  exact Sylow.normal_of_subsingleton S

private theorem relIndex_sup_left_of_normal [Finite X] (N H : Subgroup X) [N.Normal] :
    H.relIndex (N ⊔ H) = H.relIndex N := by
  have h1 := Subgroup.relIndex_mul_relIndex (N ⊓ H) H (N ⊔ H) inf_le_right le_sup_right
  have h2 := Subgroup.relIndex_mul_relIndex (N ⊓ H) N (N ⊔ H) inf_le_left le_sup_left
  rw [Subgroup.inf_relIndex_right] at h1
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_sup_left] at h2
  have hpos : 0 < N.relIndex H :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card N H) Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (h2.symm.trans (mul_comm _ _)))

theorem sylow_normal_of_quotient [Finite X] {p : ℕ} [hp : Fact p.Prime] (N : Subgroup X)
    [N.Normal] (hN : Nat.card N ≤ p)
    (h : ∀ S : Sylow p (X ⧸ N), (S : Subgroup (X ⧸ N)).Normal) (S : Sylow p X) :
    (S : Subgroup X).Normal := by
  have hφ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hT : (N ⊔ (S : Subgroup X)).Normal := by
    have e : ((S : Subgroup X).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) =
        N ⊔ (S : Subgroup X) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    rw [← e]
    have h' := h (S.mapSurjective hφ)
    rw [Sylow.coe_mapSurjective] at h'
    exact h'.comap _
  have hST : (S : Subgroup X) ≤ N ⊔ (S : Subgroup X) := le_sup_right
  have hidx : ((S.subtype hST : Sylow p ↥(N ⊔ (S : Subgroup X))) :
      Subgroup ↥(N ⊔ (S : Subgroup X))).index ≤ p := by
    rw [Sylow.coe_subtype]
    change (S : Subgroup X).relIndex (N ⊔ (S : Subgroup X)) ≤ p
    rw [relIndex_sup_left_of_normal N (S : Subgroup X)]
    exact (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)).trans hN
  haveI : Subsingleton (Sylow p ↥(N ⊔ (S : Subgroup X))) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_eq_one_of_index_le _ hidx)).1
  have hall : ∀ P : Sylow p X, (P : Subgroup X) ≤ N ⊔ (S : Subgroup X) := by
    intro P
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X S P
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have h' := hT.conj_mem _ (hST hx) g
    simpa [MulAut.smul_def, MulAut.conj_symm_apply, mul_assoc] using h'
  haveI : Subsingleton (Sylow p X) := ⟨fun P Q =>
    Sylow.subtype_injective (Subsingleton.elim (P.subtype (hall P)) (Q.subtype (hall Q)))⟩
  exact Sylow.normal_of_subsingleton S

theorem finite_outer (X : Type*) [Group X] [Finite X] : Finite (Outer X) := by
  unfold Outer
  infer_instance

theorem sylow_normal_outer_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    [Fact p.Prime] (e : A ≃* B) (h : ∀ S : Sylow p (Outer B), (S : Subgroup (Outer B)).Normal) :
    ∀ S : Sylow p (Outer A), (S : Subgroup (Outer A)).Normal := by
  intro S
  set f : Outer A →* Outer B := (equivalence e).toMonoidHom
  have hS := h (S.mapSurjective (f := f) (equivalence e).surjective)
  change ((S : Subgroup (Outer A)).map f).Normal at hS
  have e2 : ((S : Subgroup (Outer A)).map f).comap f = (S : Subgroup (Outer A)) :=
    Subgroup.comap_map_eq_self_of_injective (equivalence e).injective _
  rw [← e2]
  exact hS.comap _

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
