module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888X75b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XS

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

theorem strongly_closed_of_hyp [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hC : ∀ y ∈ normalizer (V : Set X), y * y = 1 → y ∈ centralizer (V : Set X) → y ∈ V)
    (h518 : ∀ (E : Subgroup X) (n : ℕ), ActsElemAb V E →
      (centralizer (V : Set X)).relIndex E = 2 ^ n → n ≤ 3)
    (h73 : ∀ v : V, SuppTwo hS v → centralizer ({(v : X)} : Set X) ≤ normalizer (V : Set X))
    {T : Subgroup X} (hT : IsSylow2Of T (⊤ : Subgroup X)) (hVT : V ≤ T)
    (hTN : T ≤ normalizer (V : Set X)) :
    ∀ u ∈ T, (∃ k : X, u ∈ CFSG.conjugate V k) → u ∈ V := by
  classical
  intro u hu hconj
  by_contra huV
  have hVC : V ≤ centralizer (V : Set X) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hS.comm w hw v hv
  have hweak : ∀ k : X, CFSG.conjugate V k ≤ T → CFSG.conjugate V k = V := fun k hk =>
    conjugate_eq_of_le_normalizer hS hpar hC (hk.trans hTN)
  obtain ⟨Xm, k, hXm, hk1, hrk, -, hI⟩ := exists_member_of_conj hS hT hVT hweak hu huV hconj
  have hk2 : k ≤ 2 := member_rank_le_two hS hpar hC h518 hT hVT hTN hXm hrk
  obtain ⟨hXmT, hXmV, g, hXmg⟩ := hXm
  have hcomm : ∀ a ∈ Xm, ∀ b ∈ Xm, a * b = b * a := fun a ha b hb =>
    hS.conjugate_comm (hXmg ha) (hXmg hb)
  have hsq : ∀ a ∈ Xm, a * a = 1 := fun a ha => hS.conjugate_sq (hXmg ha)
  have hF : ActsElemAb V Xm := ActsElemAb.of_exact (hXmT.trans hTN) hcomm hsq
  have hCV : Xm ⊓ centralizer (V : Set X) = Xm ⊓ V := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, hC x (hTN (hXmT hx1)) (hsq x hx1) hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, hVC hx2⟩
  have hrk' : (centralizer (V : Set X)).relIndex Xm = 2 ^ k := by
    rw [← hrk, ← Subgroup.inf_relIndex_right (centralizer (V : Set X)) Xm, inf_comm, hCV]
  have hm : ∀ s ∈ Xm, s ∉ centralizer (V : Set X) →
      2 ^ 6 ≤ Nat.card {v : V // s * (v : X) * s⁻¹ = v} := by
    intro s hs hsC
    have hsV : s ∉ V := fun h => hsC (hVC h)
    obtain ⟨Xm', k', hXm', -, hrk', hcs, -⟩ :=
      exists_member_of_conj hS hT hVT hweak (hXmT hs) hsV ⟨g, hXmg hs⟩
    have hk2' : k' ≤ 2 := member_rank_le_two hS hpar hC h518 hT hVT hTN hXm' hrk'
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcs
  have hIF : ∀ v ∈ Xm ⊓ V, ∀ a ∈ Xm, a * v * a⁻¹ = v := by
    intro v hv a ha
    rw [hcomm a ha v hv.1]
    group
  obtain ⟨d, hdI, hd2⟩ := exists_suppTwo hS hpar hF hk1 hk2 hrk' hm
    (I := Xm ⊓ V) inf_le_right hIF hI
  have hle : CFSG.conjugate V g ≤ normalizer (V : Set X) := by
    intro x hx
    refine h73 d hd2 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hS.conjugate_comm hx (hXmg hdI.1)
  have hVg : CFSG.conjugate V g = V := conjugate_eq_of_le_normalizer hS hpar hC hle
  exact hXmV (hVg ▸ hXmg)

end CFSG.OddStandard.SmallF3.Omega
