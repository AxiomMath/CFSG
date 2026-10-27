module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace GL83.PiGen

open GL83.CompFam CFSG.Open

variable {G : Type*} [Group G]

theorem isElemAbelian_iSup {p : ℕ} {ι : Type*} (S : ι → Subgroup G)
    (hS : ∀ i, IsElemAbelian p (S i))
    (hc : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) :
    IsElemAbelian p (⨆ i, S i) := by
  have hcomm : ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, x * y = y * x := by
    refine comm_of_iSup S S fun i j x hx y hy => ?_
    by_cases hij : i = j
    · subst hij
      exact elem_comm (hS i) hx hy
    · exact hc i j hij x hx y hy
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  have key : ∀ y ∈ ⨆ i, S i, y ^ p = 1 := by
    intro y hy
    have h := Subgroup.iSup_induction S (C := fun z => z ∈ ⨆ i, S i ∧ z ^ p = 1) hy
      (fun i z hz => ⟨Subgroup.mem_iSup_of_mem i hz, (hS i).2 z hz⟩) ⟨one_mem _, one_pow _⟩ ?_
    · exact h.2
    · rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
      refine ⟨mul_mem hu hv, ?_⟩
      have hcm : Commute u v := hcomm u hu v hv
      rw [hcm.mul_pow, hu', hv', one_mul]
  exact key x hx

theorem isElemAbelian_sup {p : ℕ} {H K : Subgroup G} (hH : IsElemAbelian p H)
    (hK : IsElemAbelian p K) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    IsElemAbelian p (H ⊔ K) := CFSG.Open.IsElemAbelian.sup_of_commute hH hK hc

theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem mem_normalizer_iSup {ι : Type*} (S : ι → Subgroup G) {g : G}
    (hg : ∀ i, g ∈ Subgroup.normalizer (S i : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ i, S i : Subgroup G) : Set G) := by
  rw [← cj_eq_iff_mem_normalizer, cj_iSup]
  refine iSup_congr fun i => ?_
  exact cj_eq_iff_mem_normalizer.2 (hg i)

variable {ι : Type*} [DecidableEq ι] (K S : ι → Subgroup G) (C : Subgroup G)

theorem card_sup_iSup [Finite G] (hSK : ∀ i, S i ≤ K i)
    (hcen : ∀ i, K i ⊓ Subgroup.centralizer (K i : Set G) = ⊥)
    (hKK : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hC : ∀ i, ∀ c ∈ C, ∀ x ∈ K i, c * x = x * c) (s : Finset ι) :
    Nat.card (C ⊔ ⨆ i ∈ s, S i : Subgroup G) = Nat.card C * ∏ i ∈ s, Nat.card (S i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hle : (C ⊔ ⨆ i ∈ s, S i) ≤ Subgroup.centralizer (K j : Set G) := by
      refine sup_le (fun c hc' => ?_) (iSup₂_le fun i hi => fun x hx => ?_)
      · exact Subgroup.mem_centralizer_iff.2 fun x hx => (hC j c hc' x hx).symm
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        exact Subgroup.mem_centralizer_iff.2 fun y hy => (hKK i j hij x (hSK i hx) y hy).symm
    have hcomm : ∀ h ∈ (C ⊔ ⨆ i ∈ s, S i), ∀ k ∈ S j, h * k = k * h := fun h hh k hk =>
      (Subgroup.mem_centralizer_iff.1 (hle hh) k (hSK j hk)).symm
    have hdisj : (C ⊔ ⨆ i ∈ s, S i) ⊓ S j = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have : x ∈ K j ⊓ Subgroup.centralizer (K j : Set G) := ⟨hSK j hx.2, hle hx.1⟩
      rw [hcen j] at this
      exact this
    have hrw : (C ⊔ ⨆ i ∈ insert j s, S i) = (C ⊔ ⨆ i ∈ s, S i) ⊔ S j := by
      rw [Finset.iSup_insert, sup_comm (S j), ← sup_assoc]
    rw [hrw, card_sup_of_commute_of_inf_eq_bot hcomm hdisj, ih, Finset.prod_insert hj]
    ring

theorem sup_iSup_le_normalizer (V E : ι → Subgroup G)
    (hVK : ∀ i, V i ≤ K i) (hEK : ∀ i, E i ≤ K i)
    (hEV : ∀ i, E i ≤ Subgroup.normalizer (V i : Set G))
    (hKK : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hC : ∀ i, ∀ c ∈ C, ∀ x ∈ K i, c * x = x * c) (s : Finset ι) :
    (C ⊔ ⨆ i ∈ s, E i) ≤ Subgroup.normalizer ((⨆ i ∈ s, V i : Subgroup G) : Set G) := by
  have hnorm : ∀ g, (∀ i ∈ s, g ∈ Subgroup.normalizer (V i : Set G)) →
      g ∈ Subgroup.normalizer ((⨆ i ∈ s, V i : Subgroup G) : Set G) := by
    intro g hg
    rw [← cj_eq_iff_mem_normalizer, cj_iSup]
    refine iSup_congr fun i => ?_
    rw [cj_iSup]
    refine iSup_congr fun hi => ?_
    exact cj_eq_iff_mem_normalizer.2 (hg i hi)
  refine sup_le (fun c hc => hnorm c fun i _ => ?_)
    (iSup₂_le fun j hj x hx => hnorm x fun i _ => ?_)
  · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun v hv =>
      (hC i c hc v (hVK i hv)).symm)
  · by_cases hij : i = j
    · subst hij
      exact hEV i hx
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun v hv =>
        (hKK j i (Ne.symm hij) x (hEK j hx) v (hVK i hv)).symm)

end GL83.PiGen
