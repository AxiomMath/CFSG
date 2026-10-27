module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.SqCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Blueprint.NativeSporadic

theorem orderOf_eq_two_of_center {G : Type} [Group G] {L : Subgroup G}
    (h2 : Nat.card (center L) = 2) {t : G} (ht : (center L).map L.subtype = zpowers t) :
    orderOf t = 2 := by
  rw [← Nat.card_zpowers, ← ht, Subgroup.card_map_of_injective L.subtype_injective, h2]

theorem fi23_of_centralizer_quasisimple
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) (hq : CFSG.Open.IsQuasisimple (centralizer ({t} : Set G)))
    (h2 : Nat.card (center (centralizer ({t} : Set G))) = 2)
    (hQ : IsSporadic (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) .Fi22) :
    IsSporadic G .Fi23 := by
  have ht1 : t ≠ 1 := fun e => by rw [e, orderOf_one] at ht; exact absurd ht (by norm_num)
  have htc : (⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({t} : Set G)) ∈
      center (centralizer ({t} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have htc1 : (⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({t} : Set G)) ≠ 1 :=
    fun e => ht1 (congrArg Subtype.val e)
  obtain ⟨ψ, hψ⟩ := TwoFi22.exists_iso_Cd hq h2 hQ htc htc1
  let M := TwoFi22.modelOfIso ψ (Subtype.ext hψ)
  have hF : TwoFi22.SquareFacts :=
    ⟨TwoFi22.sqStatement_d.1, TwoFi22.sqStatement_d.2⟩
  exact TwoFi22.isSporadic_fi23_of_threeTransposition hnonab hq ht rfl hQ
    (fun x y hx hy => TwoFi22.orderOf_mul_mem_class M hF TwoFi22.fi23_frame hnonab ht x y hx hy)

theorem twoFi22_fi23
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G}
    (ht : (center L).map L.subtype = zpowers t) (hC : centralizer ({t} : Set G) = L) :
    IsSporadic G .Fi23 := by
  have := h.simple
  have hq := h.standard.1
  subst hC
  exact fi23_of_centralizer_quasisimple h.nonabelian (orderOf_eq_two_of_center h2 ht) hq h2 hQ

@[expose] def Fi24Branch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → Nat.card (center L) = 2 →
    IsSporadic (L ⧸ center L) .Fi22 → ∀ {t : G}, (center L).map L.subtype = zpowers t →
      centralizer ({t} : Set G) ≠ L → IsSporadic G .Fi24Prime

theorem twoFi22Gives_of_branch
    (hB : Fi24Branch) : TwoFi22Gives := by
  intro G _ _ L h h2 hQ
  obtain ⟨t, -, htZ⟩ := exists_map_center_eq_zpowers h2
  by_cases hC : centralizer ({t} : Set G) = L
  · exact Or.inl (twoFi22_fi23 h h2 hQ htZ hC)
  · exact Or.inr (hB G L h h2 hQ htZ hC)

end CFSG.EvenSporadicStandard
