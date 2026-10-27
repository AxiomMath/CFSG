module

public import CFSG.CGT.PushingUpLit.SolK.FourA
public import CFSG.CGT.PushingUpLit.SolK.ThetaKer

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem not_P_le_Q (hT : TightData S) {x : G} (hxQ : x ∈ pCoreOf 2 M) (hx1 : x ≠ 1)
    (hKM : ¬ CGOf x ≤ M) : ¬ pCoreOf 2 (CGOf x) ≤ pCoreOf 2 M := by
  intro hPQ
  apply hKM
  have hQK : pCoreOf 2 M ≤ CGOf x := S.Q_le_CGOf hT hxQ
  have hB : Subgroup.zpowers x ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers x) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hxQ)
  have hcons := centralizer_two_constrained S.hyp.charTwo hB hB2
  have hQP : pCoreOf 2 M ≤ pCoreOf 2 (CGOf x) := by
    intro q hq
    apply hcons
    refine Subgroup.mem_inf.2 ⟨hQK hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact hT.abelian p (hPQ hp) q hq
  have hPeq : pCoreOf 2 (CGOf x) = pCoreOf 2 M := le_antisymm hPQ hQP
  intro k hk
  rw [← S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
  intro q
  rw [← hPeq]
  refine ⟨fun hq => pCoreOf_normalized _ hk hq, fun hq => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) hq
  simpa [mul_assoc] using this

theorem sup_eq_TOf (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) :
    pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M = TOf M (w * r) := by
  classical
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hH2 := S.isPGroup_sup hT hxQ
  have hUT : (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M ≤ TOf M (w * r) :=
    S.sup_inf_le_TOf hT hxQ
  have hPQ : ¬ pCoreOf 2 (CGOf (w * r)) ≤ pCoreOf 2 M := S.not_P_le_Q hT hxQ hx1 hKM
  have hQH : pCoreOf 2 M ≠ pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M := fun h' =>
    hPQ (by rw [h']; exact le_sup_left)
  obtain ⟨t, htH, htQ, htN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
  have htM : t ∈ M := by rw [← S.normalizer_Q_eq]; exact htN
  have htU : t ∈ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M := ⟨htH, htM⟩
  have hUM : (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M ≤ M := inf_le_right
  have hUC : (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M ≤ CMOf M (w * r) := fun u hu =>
    TOf_le_C M (w * r) (hUT hu)
  have hU2 : IsPGroup 2 ↥((pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M) :=
    isPGroup_of_le hH2 inf_le_left
  have hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M,
      k * u * k⁻¹ ∈ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M := fun k hk u hu =>
    ⟨sup_norm hk hu.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.1 hk).1 hu.2)
      (M.inv_mem (Subgroup.mem_inf.1 hk).1)⟩
  have hFU := S.fourGroup_theta hw hr hcard hUM hUC hU2 hUn
  have hFT : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hle : (((pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M).subgroupOf M).map S.θ ≤
      S.TN (w * r) := by
    intro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    exact S.mem_TN.2 ⟨m, hUT (Subgroup.mem_subgroupOf.1 hm), rfl⟩
  have hne : (((pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M).subgroupOf M).map S.θ ≠ ⊥ := by
    intro hbot
    apply htQ
    have hmem : S.θ ⟨t, htM⟩ ∈
        (((pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M).subgroupOf M).map S.θ :=
      Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 htU, rfl⟩
    rw [hbot] at hmem
    exact S.mem_Q_of_theta_eq_one hR htM (Subgroup.mem_bot.1 hmem)
  have hEq := hFT.eq_of_le hcard hle hne hFU.norm
  have hTU : TOf M (w * r) ≤ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M := by
    intro t' ht'
    have ht'M : t' ∈ M := TOf_le_M M _ ht'
    have hσ : S.θ ⟨t', ht'M⟩ ∈ S.TN (w * r) := S.mem_TN.2 ⟨⟨t', ht'M⟩, ht', rfl⟩
    rw [← hEq] at hσ
    obtain ⟨u, hu, hθ⟩ := Subgroup.mem_map.1 hσ
    have huU : (u : G) ∈ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M :=
      Subgroup.mem_subgroupOf.1 hu
    have hM : t' * (u : G)⁻¹ ∈ M := M.mul_mem ht'M (M.inv_mem u.2)
    have hdiv : t' * (u : G)⁻¹ ∈ pCoreOf 2 M := by
      refine S.mem_Q_of_theta_eq_one hR hM ?_
      have : (⟨t' * (u : G)⁻¹, hM⟩ : ↥M) = ⟨t', ht'M⟩ * u⁻¹ := rfl
      rw [this, map_mul, map_inv, ← hθ, mul_inv_cancel]
    have hQU : pCoreOf 2 M ≤ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M :=
      le_inf le_sup_right (pCoreOf_le_self M)
    have e : t' = (t' * (u : G)⁻¹) * u := by group
    rw [e]
    exact Subgroup.mul_mem _ (hQU hdiv) huU
  have hTH : TOf M (w * r) ≤ pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M := hTU.trans inf_le_left
  by_contra hne'
  obtain ⟨h, hhH, hhT, hhN⟩ := exists_mem_normalizer_of_lt hH2 hTH (Ne.symm hne')
  have hhM : h ∈ M := S.normalizer_TOf_le_M hT hQe hw hr hcard hhN
  exact hhT (hUT ⟨hhH, hhM⟩)

theorem not_Q_le_P (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) : ¬ pCoreOf 2 M ≤ pCoreOf 2 (CGOf (w * r)) := by
  intro hQP
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) = TOf M (w * r) :=
    (sup_eq_left.2 hQP).symm.trans hsup
  apply hKM
  intro k hk
  apply S.normalizer_TOf_le_M hT hQe hw hr hcard
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [← hPT]
  refine ⟨fun ht => pCoreOf_normalized _ hk ht, fun ht => ?_⟩
  have := pCoreOf_normalized _ ((CGOf (w * r)).inv_mem hk) ht
  simpa [mul_assoc] using this

theorem theta_P_eq (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) :
    ((pCoreOf 2 (CGOf (w * r))).subgroupOf M).map S.θ = S.TN (w * r) := by
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) ≤ TOf M (w * r) := le_sup_left.trans hsup.le
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := hPT.trans (TOf_le_M M _)
  have hFP := S.fourGroup_theta hw hr hcard hPM (hPT.trans (TOf_le_C M _))
    (isPGroup_pCoreOf' _) (fun k hk p hp => pCoreOf_normalized _ (Subgroup.mem_inf.1 hk).2 hp)
  have hFT : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hle : ((pCoreOf 2 (CGOf (w * r))).subgroupOf M).map S.θ ≤ S.TN (w * r) := by
    intro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    exact S.mem_TN.2 ⟨m, hPT (Subgroup.mem_subgroupOf.1 hm), rfl⟩
  have hne : ((pCoreOf 2 (CGOf (w * r))).subgroupOf M).map S.θ ≠ ⊥ := by
    intro hbot
    apply S.not_P_le_Q hT hxQ hx1 hKM
    intro p hp
    have hpM : p ∈ M := hPM hp
    have hmem : S.θ ⟨p, hpM⟩ ∈ ((pCoreOf 2 (CGOf (w * r))).subgroupOf M).map S.θ :=
      Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
    rw [hbot] at hmem
    exact S.mem_Q_of_theta_eq_one hR hpM (Subgroup.mem_bot.1 hmem)
  exact hFT.eq_of_le hcard hle hne hFP.norm

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
