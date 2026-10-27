module

public import CFSG.CGT.PushingUpLit.SolK.Delta
public import CFSG.CGT.PushingUpLit.SolK.FourB

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

theorem center_conj_mem {G : Type} [Group G] {K P : Subgroup G}
    (hP : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P) {k : G} (hk : k ∈ K) {e : G}
    (he : e ∈ P ⊓ Subgroup.centralizer (P : Set G)) :
    k * e * k⁻¹ ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
  refine Subgroup.mem_inf.2 ⟨hP k hk e he.1, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro p hp
  have hp' : k⁻¹ * p * k ∈ P := by
    have := hP k⁻¹ (K.inv_mem hk) p hp
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 he.2 _ hp'
  calc p * (k * e * k⁻¹) = k * ((k⁻¹ * p * k) * e) * k⁻¹ := by group
    _ = k * (e * (k⁻¹ * p * k)) * k⁻¹ := by rw [h1]
    _ = k * e * k⁻¹ * p := by group

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem mem_W_of_rOf_bot (hrbot : rOf M X = ⊥) {e : G} (he : e ∈ pCoreOf 2 M) : e ∈ S.D.W := by
  obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq e he
  have hr1 : r = 1 := Subgroup.mem_bot.1 (hrbot ▸ hr)
  rw [hr1, mul_one]
  exact hw

theorem TN_ne_bot (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) : S.TN (w * r) ≠ ⊥ := by
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hθP := S.theta_P_eq hT hQe hR hw hr hcard hKM
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := (le_sup_left.trans hsup.le).trans (TOf_le_M M _)
  intro hbot
  apply S.not_P_le_Q hT hxQ hx1 hKM
  intro p hp
  have hpM : p ∈ M := hPM hp
  have hmem : S.θ ⟨p, hpM⟩ ∈ ((pCoreOf 2 (CGOf (w * r))).subgroupOf M).map S.θ :=
    Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  rw [hθP, hbot] at hmem
  exact S.mem_Q_of_theta_eq_one hR hpM (Subgroup.mem_bot.1 hmem)

theorem DeltaJ_le_E (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) {J : Finset (Fin (2 * n + 1))}
    (hJ : J ⊆ (vsupp (S.D.β ⟨w, hw⟩))ᶜ) :
    S.DeltaJ J ≤ pCoreOf 2 (CGOf (w * r)) ⊓
      Subgroup.centralizer ((pCoreOf 2 (CGOf (w * r)) : Subgroup G) : Set G) := by
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hθP := S.theta_P_eq hT hQe hR hw hr hcard hKM
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := (le_sup_left.trans hsup.le).trans (TOf_le_M M _)
  have hFT : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hB : Subgroup.zpowers (w * r) ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers (w * r)) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hxQ)
  have hcons := centralizer_two_constrained S.hyp.charTwo hB hB2
  intro g hg
  have hgW : g ∈ S.D.W := hg.1
  have hgK : g ∈ CGOf (w * r) := S.Q_le_CGOf hT hxQ (S.DeltaJ_le_Q J hg)
  have hcent : ∀ p ∈ pCoreOf 2 (CGOf (w * r)), p * g = g * p := by
    intro p hp
    have hpM : p ∈ M := hPM hp
    have hσ : S.θ ⟨p, hpM⟩ ∈ S.TN (w * r) := by
      rw [← hθP]
      exact Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
    have h1 := S.centralizes_DeltaJ_of_fix (J := J) (m := ⟨p, hpM⟩)
      (fun j hj => hFT.fix _ hσ j (Finset.mem_compl.1 (hJ hj))) g hg
    calc p * g = (p * g * p⁻¹) * p := by group
      _ = g * p := by rw [h1]
  have hgP : g ∈ pCoreOf 2 (CGOf (w * r)) :=
    hcons (Subgroup.mem_inf.2 ⟨hgK, Subgroup.mem_centralizer_iff.2 hcent⟩)
  exact Subgroup.mem_inf.2 ⟨hgP, Subgroup.mem_centralizer_iff.2 hcent⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
