module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma620B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem card_T0_sup_z : Nat.card ↥(T₀ ⊔ zpowers z) = 2 * Nat.card T₀ := by
  have hc := h.conf.cfg
  let f : ↥T₀ × ↥(zpowers z) → ↥(T₀ ⊔ zpowers z) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
    have hu : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [hab']
        _ = (b' : G) * (b : G)⁻¹ := by group
    have hmemL : (a' : G)⁻¹ * (a : G) ∈ T₀ := mul_mem (inv_mem a'.2) a.2
    have hmemZ : (a' : G)⁻¹ * (a : G) ∈ zpowers z := by
      rw [hu]; exact mul_mem b'.2 (inv_mem b.2)
    have h1 : (a' : G)⁻¹ * (a : G) = 1 :=
      (Subgroup.disjoint_def.1 hc.T₀_disjoint) hmemL hmemZ
    have ha : a = a' := Subtype.ext (by
      calc (a : G) = (a' : G) * ((a' : G)⁻¹ * (a : G)) := by group
        _ = (a' : G) := by rw [h1, mul_one])
    subst ha
    have hb : (b : G) = (b' : G) := mul_left_cancel hab'
    exact Prod.ext rfl (Subtype.ext hb)
  have hsurj : Function.Surjective f := by
    rintro ⟨c, hcC⟩
    have hzc : zpowers z ≤ centralizer (T₀ : Set G) :=
      zpowers_le.2 (mem_centralizer_iff.2 fun a ha => hc.z_comm_of_mem_A (hc.T₀_le ha))
    obtain ⟨l, hl, a, ha, hca⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc hcC
    exact ⟨(⟨l, hl⟩, ⟨a, ha⟩), Subtype.ext hca.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hc.z_sq
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hc.z_ne
  rw [hord]
  exact Nat.mul_comm _ _

theorem T0_le_M : T₀ ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
  intro x hx
  have hmem : x ∈ (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers z :=
    mem_sup_left ⟨h.conf.cfg.T₀_le hx,
      mem_centralizer_singleton_iff.2 (h.conf.cfg.t_central x hx)⟩
  rw [← h.CMz_eq] at hmem
  exact hmem.1

theorem exists_Rs {α : G} (hα : AlphaSpec S z t α) :
    ∃ Rs : Subgroup G, IsPGroup 2 Rs ∧ z ∈ Rs ∧ T₀ ≤ Rs ∧
      Rs ≤ normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) ∧
      (∀ P : Subgroup G, IsPGroup 2 P →
        P ≤ normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) →
          Rs ≤ P → P = Rs) ∧
      ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) := by
  have hc := h.conf.cfg
  have hDcard := h.card_T0_sup_z
  have hDp : IsPGroup 2 ↥(T₀ ⊔ zpowers z) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hc.T₀_pgroup
    exact IsPGroup.of_card (n := k + 1) (by rw [hDcard, hk, pow_succ'])
  have hDM : T₀ ⊔ zpowers z ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) :=
    sup_le h.T0_le_M (zpowers_le.2 h.z_mem_M)
  have hMN : normalizer ((S ⊔ E : Subgroup G) : Set G) ≤
      normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => h.QF_normal hα hg hq, fun hq => ?_⟩
    have e := h.QF_normal hα (inv_mem hg) hq
    rwa [show g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q by group] at e
  have hDC : T₀ ⊔ zpowers z ≤ centralizer ({z} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hc.z_comm_of_mem_A (hc.T₀_le ha)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  set N := normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) with hN
  obtain ⟨Rs, ⟨h1, h2, h3⟩, hmax⟩ :=
    (Set.toFinite {P : Subgroup G | IsPGroup 2 P ∧ T₀ ⊔ zpowers z ≤ P ∧ P ≤ N}).exists_maximalFor
      id _ ⟨T₀ ⊔ zpowers z, hDp, le_rfl, hDM.trans hMN⟩
  refine ⟨Rs, h1, h2 (mem_sup_right (mem_zpowers z)), (le_sup_left.trans h2), h3,
    fun P hP hPN hle => le_antisymm (hmax ⟨hP, h2.trans hle, hPN⟩ hle) hle, ?_⟩
  refine h.relIndex_cent_z_odd h1 ?_
  calc 2 * Nat.card T₀ = Nat.card ↥(T₀ ⊔ zpowers z) := hDcard.symm
    _ ≤ Nat.card ↥(Rs ⊓ centralizer ({z} : Set G)) :=
      Subgroup.card_le_of_le (le_inf h2 hDC)

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
