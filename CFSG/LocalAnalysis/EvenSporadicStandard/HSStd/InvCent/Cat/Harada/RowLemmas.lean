module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OneStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.EvenSporadicStandard.HSStd.HL34

theorem mul_self_mem_alternatingGroup {α : Type*} [DecidableEq α] [Fintype α]
    (s : Equiv.Perm α) : s * s ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Int.units_mul_self]

theorem sq_mem_centralizerDerived_of_equiv {G : Type*} [Group G] {t : G}
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))
    {c : G} (hc : c ∈ centralizer ({t} : Set G)) : c * c ∈ centralizerDerived t := by
  rw [centralizerDerived_eq_alt ζ]
  refine ⟨(ζ ⟨c, hc⟩).2 * (ζ ⟨c, hc⟩).2, mul_self_mem_alternatingGroup _, ?_⟩
  have h1 : (ζ ⟨c, hc⟩).1 * (ζ ⟨c, hc⟩).1 = 1 := by
    generalize (ζ ⟨c, hc⟩).1 = a
    revert a
    decide
  have h2 : (⟨c, hc⟩ : ↥(centralizer ({t} : Set G))) * ⟨c, hc⟩ =
      ζ.symm (1, (ζ ⟨c, hc⟩).2 * (ζ ⟨c, hc⟩).2) := by
    apply ζ.injective
    rw [map_mul, MulEquiv.apply_symm_apply]
    ext
    · exact h1
    · rfl
  exact (congrArg Subtype.val h2).symm

namespace TwoCfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem sq_mem_centralizerDerived (htop : centralizer ({t} : Set G) ≠ ⊤) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) : c * c ∈ centralizerDerived t := by
  obtain ⟨e⟩ := h.hJ
  rw [h.centralizerDerived_eq htop, commutator_eq_map_alt J e]
  rw [h.hC] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute h.hcomm).1 hc
  have hab : a * b = b * a := h.hcomm a ha b hb
  have haa := h.mul_self_of_mem_fourGroup ha
  have hsq : a * b * (a * b) = b * b := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = b * b := by rw [haa, one_mul]
  rw [hsq]
  refine ⟨e ⟨b, hb⟩ * e ⟨b, hb⟩, mul_self_mem_alternatingGroup _, ?_⟩
  rw [map_mul, embJ_apply, MulEquiv.symm_apply_apply]

end TwoCfg

theorem exists_card_eq_mul_outer_of_sq_mem {D : Type*} [Group D] [Finite D] (S : Subgroup D)
    [S.Normal] (hC : centralizer (S : Set D) = ⊥) {A : Subgroup D} (hA : ∀ a ∈ A, a * a ∈ S) :
    ∃ R : Subgroup (Outer ↥S), Nat.card A = Nat.card ↥(A ⊓ S) * Nat.card R ∧
      ∀ x ∈ R, x * x = 1 := by
  let ρ : D →* MulAut ↥S := actionHom S (MulEquiv.refl ↥S)
  let f : ↥A →* Outer ↥S := (QuotientGroup.mk' (inner ↥S)).comp (ρ.comp A.subtype)
  have hρS : ∀ s : ↥S, ρ (s : D) = MulAut.conj s := fun s => by
    refine MulEquiv.ext fun x => ?_
    show MulAut.conjNormal (s : D) x = _
    rw [MulAut.conjNormal_val]
  have hker : ∀ a : ↥A, a ∈ f.ker ↔ (a : D) ∈ S := by
    intro a
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (ρ (a : D)) : Outer ↥S) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨s, hs⟩
      have h1 : ρ ((a : D) * (s : D)⁻¹) = 1 := by
        rw [map_mul, map_inv, hρS, hs, mul_inv_cancel]
      have h2 := (actionHom_eq_one_iff S (MulEquiv.refl ↥S) _).1 h1
      rw [hC, mem_bot, mul_inv_eq_one] at h2
      rw [h2]
      exact s.2
    · intro h
      exact ⟨⟨a, h⟩, (hρS ⟨a, h⟩).symm⟩
  have hkc : Nat.card f.ker = Nat.card ↥(A ⊓ S) :=
    Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, (hker a.1).1 a.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, (hker ⟨b.1, b.2.1⟩).2 b.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card A = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  refine ⟨f.range, by rw [hcard, hkc], ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [← map_mul]
  have : a * a ∈ f.ker := (hker (a * a)).2 (hA a a.2)
  exact this

theorem card_le_two_of_sq_eq_one_of_isCyclic {Q : Type*} [Group Q] (hQ : IsCyclic Q)
    (R : Subgroup Q) (hR : ∀ x ∈ R, x * x = 1) : Nat.card R ≤ 2 := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic R).exists_generator
  have hcard : Nat.card R = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]; exact Subtype.ext (hR g g.2))
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
