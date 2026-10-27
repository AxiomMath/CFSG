module

public import CFSG.CGT.PushingUpLit.SolK.FourB

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem hasLen_zero {r : G} (hr : r ∈ rOf M X) : S.HasLen r 0 := by
  refine ⟨1, S.D.W.one_mem, r, hr, (one_mul r).symm, ?_⟩
  have h1 : S.D.β ⟨1, S.D.W.one_mem⟩ = 1 := by
    have : (⟨1, S.D.W.one_mem⟩ : ↥S.D.W) = 1 := rfl
    rw [this, map_one]
  have : vsupp (S.D.β ⟨1, S.D.W.one_mem⟩) = ∅ := by
    rw [h1]
    ext i
    simp [mem_vsupp, vcoord_one]
  rw [this]
  rfl

theorem beta_commutator {q : ↥S.D.W} {m : ↥M} {a d' : Fin (2 * n + 1)}
    (hq : S.D.β q = pairVec a d') (hd' : S.θ m d' = d')
    (hW : (m : G) * ((q⁻¹ : ↥S.D.W) : G) * (m : G)⁻¹ ∈ S.D.W) :
    S.D.β (q * ⟨(m : G) * ((q⁻¹ : ↥S.D.W) : G) * (m : G)⁻¹, hW⟩) = pairVec a (S.θ m a) := by
  have h1 : S.D.β ⟨(m : G) * ((q⁻¹ : ↥S.D.W) : G) * (m : G)⁻¹, hW⟩ =
      coreAct (2 * n + 1) (S.θ m) (S.D.β q⁻¹) := S.θ_spec m q⁻¹ hW
  have hinv : S.D.β q⁻¹ = pairVec a d' := by
    rw [map_inv, hq]
    exact coreMod_inv_eq _
  rw [hinv] at h1
  rw [map_mul, h1, hq, coreAct_pairVec, hd', pairVec_comm a d', pairVec_comm (S.θ m a) d',
    pairVec_mul]

theorem center_P_le_Q (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) {z : G} (hzP : z ∈ pCoreOf 2 (CGOf (w * r)))
    (hz : ∀ p ∈ pCoreOf 2 (CGOf (w * r)), p * z = z * p) : z ∈ pCoreOf 2 M := by
  classical
  by_contra hzQ
  have hn : 2 ≤ n := S.hyp.two_le
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) ≤ TOf M (w * r) := le_sup_left.trans hsup.le
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := hPT.trans (TOf_le_M M _)
  have hzM : z ∈ M := hPM hzP
  have hθz : S.θ ⟨z, hzM⟩ ≠ 1 := fun h => hzQ (S.mem_Q_of_theta_eq_one hR hzM h)
  have hθP := S.theta_P_eq hT hQe hR hw hr hcard hKM
  have hFT : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hzN : S.θ ⟨z, hzM⟩ ∈ S.TN (w * r) := S.mem_TN.2 ⟨⟨z, hzM⟩, hPT hzP, rfl⟩
  have hNne : S.TN (w * r) ≠ ⊥ := fun h => hθz (Subgroup.mem_bot.1 (h ▸ hzN))
  obtain ⟨σ', hσ'N, hσ'1, hσ'z⟩ := hFT.exists_ne hcard hNne (S.θ ⟨z, hzM⟩)
  have hσ'P : σ' ∈ ((pCoreOf 2 (CGOf (w * r))).subgroupOf M).map S.θ := by
    rw [hθP]
    exact hσ'N
  obtain ⟨pm, hpm, hpmσ⟩ := Subgroup.mem_map.1 hσ'P
  have hpP : (pm : G) ∈ pCoreOf 2 (CGOf (w * r)) := Subgroup.mem_subgroupOf.1 hpm
  obtain ⟨a, haI⟩ : (vsupp (S.D.β ⟨w, hw⟩)).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨d', hd'I⟩ : (vsupp (S.D.β ⟨w, hw⟩))ᶜ.Nonempty := Finset.card_pos.1 (by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega)
  have hd'fix : σ' d' = d' := hFT.fix σ' hσ'N d' (Finset.mem_compl.1 hd'I)
  let q : ↥S.D.W := S.D.β.symm (pairVec a d')
  have hβq : S.D.β q = pairVec a d' := S.D.β.apply_symm_apply _
  have hqQ : (q : G) ∈ pCoreOf 2 M := S.W_le_Q q.2
  have hqK : (q : G) ∈ CGOf (w * r) := S.Q_le_CGOf hT hxQ hqQ
  have hconjW : (pm : G) * ((q⁻¹ : ↥S.D.W) : G) * (pm : G)⁻¹ ∈ S.D.W :=
    S.W_normalized pm.2 (q⁻¹).2
  have hβc := S.beta_commutator (q := q) (m := pm) (a := a) (d' := d') hβq
    (by rw [hpmσ]; exact hd'fix) hconjW
  rw [hpmσ] at hβc
  let cW : ↥S.D.W := q * ⟨(pm : G) * ((q⁻¹ : ↥S.D.W) : G) * (pm : G)⁻¹, hconjW⟩
  have hcP : (cW : G) ∈ pCoreOf 2 (CGOf (w * r)) := by
    have e : (cW : G) = ((q : G) * (pm : G) * (q : G)⁻¹) * (pm : G)⁻¹ := by
      show (q : G) * ((pm : G) * ((q : G))⁻¹ * (pm : G)⁻¹) = _
      group
    rw [e]
    exact (pCoreOf (2) (CGOf (w * r))).mul_mem (pCoreOf_normalized _ hqK hpP)
      ((pCoreOf 2 (CGOf (w * r))).inv_mem hpP)
  have hcz : z * (cW : G) * z⁻¹ = (cW : G) := by
    have := hz _ hcP
    calc z * (cW : G) * z⁻¹ = ((cW : G) * z) * z⁻¹ := by rw [this]
      _ = (cW : G) := by group
  have hczW : z * (cW : G) * z⁻¹ ∈ S.D.W := S.W_normalized hzM cW.2
  have h2 : S.D.β ⟨z * (cW : G) * z⁻¹, hczW⟩ =
      coreAct (2 * n + 1) (S.θ ⟨z, hzM⟩) (S.D.β cW) := S.θ_spec ⟨z, hzM⟩ cW hczW
  have h3 : (⟨z * (cW : G) * z⁻¹, hczW⟩ : ↥S.D.W) = cW := Subtype.ext hcz
  rw [h3, hβc] at h2
  exact hFT.pair_move hcard hzN hθz hσ'N hσ'1 (Ne.symm hσ'z) haI h2.symm

theorem rOf_eq_bot (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) : rOf M X = ⊥ := by
  classical
  by_contra hRbot
  obtain ⟨⟨r0, hr0⟩, hr01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRbot
  have hr01' : r0 ≠ 1 := fun h => hr01 (Subtype.ext h)
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) ≤ TOf M (w * r) := le_sup_left.trans hsup.le
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := hPT.trans (TOf_le_M M _)
  have hr0Q : r0 ∈ pCoreOf 2 M := hr0.1
  have hr0K : r0 ∈ CGOf (w * r) := S.Q_le_CGOf hT hxQ hr0Q
  have hB : Subgroup.zpowers (w * r) ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers (w * r)) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hxQ)
  have hcons := centralizer_two_constrained S.hyp.charTwo hB hB2
  have hr0cent : ∀ p ∈ pCoreOf 2 (CGOf (w * r)), p * r0 = r0 * p := by
    intro p hp
    have hpM : p ∈ M := hPM hp
    have h1 := SolCfg.RSmall.central S hR hpM hr0
    calc p * r0 = (p * r0 * p⁻¹) * p := by group
      _ = r0 * p := by rw [h1]
  have hr0P : r0 ∈ pCoreOf 2 (CGOf (w * r)) := by
    apply hcons
    exact Subgroup.mem_inf.2 ⟨hr0K, Subgroup.mem_centralizer_iff.2 hr0cent⟩
  let E : Subgroup G := pCoreOf 2 (CGOf (w * r)) ⊓
    Subgroup.centralizer ((pCoreOf 2 (CGOf (w * r)) : Subgroup G) : Set G)
  have hEQ : E ≤ pCoreOf 2 M := fun z hz =>
    S.center_P_le_Q hT hQe hR hw hr hcard hKM hz.1
      (fun p hp => Subgroup.mem_centralizer_iff.1 hz.2 p hp)
  have hr0E : r0 ∈ E := Subgroup.mem_inf.2 ⟨hr0P, Subgroup.mem_centralizer_iff.2 hr0cent⟩
  have hKE : ∀ k ∈ CGOf (w * r), ∀ e ∈ E, k * e * k⁻¹ ∈ E := by
    intro k hk e he
    have hkinv : k⁻¹ ∈ CGOf (w * r) := (CGOf (w * r)).inv_mem hk
    refine Subgroup.mem_inf.2 ⟨pCoreOf_normalized _ hk he.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro p hp
    have hp' : k⁻¹ * p * k ∈ pCoreOf 2 (CGOf (w * r)) := by
      have := pCoreOf_normalized _ hkinv hp
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 he.2 _ hp'
    calc p * (k * e * k⁻¹) = k * ((k⁻¹ * p * k) * e) * k⁻¹ := by group
      _ = k * (e * (k⁻¹ * p * k)) * k⁻¹ := by rw [h1]
      _ = k * e * k⁻¹ * p := by group
  have hKN : ∀ k ∈ CGOf (w * r), k ∈ Subgroup.normalizer (E : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hKE k hk e he, fun he => ?_⟩
    have := hKE k⁻¹ ((CGOf (w * r)).inv_mem hk) _ he
    simpa [mul_assoc] using this
  have hCEM : Subgroup.centralizer (E : Set G) ≤ M := by
    intro c hc
    have h1 : r0 * c = c * r0 := Subgroup.mem_centralizer_iff.1 hc r0 hr0E
    have hcK : c ∈ CGOf r0 := mem_centralizer_zpowers_iff.2
      (calc c * r0 * c⁻¹ = (r0 * c) * c⁻¹ := by rw [h1]
        _ = r0 := by group)
    have hN := (S.centralizer_eq_of_len S.hyp.charTwo hT hr0Q hr01' (S.hasLen_zero hr0)
      (by norm_num) (by norm_num)).2
    exact hN (Subgroup.centralizer_le_normalizer ((Subgroup.zpowers r0 : Subgroup G) : Set G) hcK)
  have hQC : pCoreOf 2 M ≤ Subgroup.centralizer (E : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun e he => hT.abelian e (hEQ he) q hq
  have hQO : pCoreOf 2 M ≤ pCoreOf 2 (Subgroup.centralizer (E : Set G)) :=
    le_pCoreOf_of_normalized hQC (fun c hc q hq => pCoreOf_normalized M (hCEM hc) hq)
      (isPGroup_pCoreOf' M)
  have hnormC : ∀ n' ∈ CGOf (w * r), ∀ c ∈ Subgroup.centralizer (E : Set G),
      n' * c * n'⁻¹ ∈ Subgroup.centralizer (E : Set G) := fun n' hn' c hc =>
    centralizer_normalized (hKN n' hn') hc
  let B' : Subgroup G := pCoreOf 2 (Subgroup.centralizer (E : Set G)) ⊓ CGOf (w * r)
  have hB'P : B' ≤ pCoreOf 2 (CGOf (w * r)) := by
    refine le_pCoreOf_of_normalized inf_le_right (fun k hk b hb => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' _) inf_le_left)
    exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized_of_normal hnormC hk hb.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hb.2) ((CGOf (w * r)).inv_mem hk)⟩
  exact S.not_Q_le_P hT hQe hR hw hr hcard hKM fun q hq =>
    hB'P (Subgroup.mem_inf.2 ⟨hQO hq, S.Q_le_CGOf hT hxQ hq⟩)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
