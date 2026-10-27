module

public import CFSG.CGT.PushingUpLit.SolK.TwoC

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem sup_eq_TOf_two (hT : TightData S) (hQe : QElem S) (hR : RSmall S) (hn4 : 4 ≤ n)
    {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2)
    (hKM : ¬ CGOf (w * r) ≤ M) :
    pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M = TOf M (w * r) := by
  classical
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.1 hcard
  have hH2 := S.isPGroup_sup hT hxQ
  have hUT : (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M ≤ TOf M (w * r) :=
    S.sup_inf_le_TOf hT hxQ
  have hPQ : ¬ pCoreOf 2 (CGOf (w * r)) ≤ pCoreOf 2 M := S.not_P_le_Q hT hxQ hx1 hKM
  have hQH : pCoreOf 2 M ≠ pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M := fun h' =>
    hPQ (by rw [h']; exact le_sup_left)
  obtain ⟨t, htH, htQ, htN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
  have htM : t ∈ M := by rw [← S.normalizer_Q_eq]; exact htN
  have htU : t ∈ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M := ⟨htH, htM⟩
  have hQU : pCoreOf 2 M ≤ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M :=
    le_inf le_sup_right (pCoreOf_le_self M)
  have hTU : TOf M (w * r) ≤ (pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M) ⊓ M :=
    S.le_of_swap hw hr hcard hij hI hR hQU htU (hUT htU) htQ
  have hTH : TOf M (w * r) ≤ pCoreOf 2 (CGOf (w * r)) ⊔ pCoreOf 2 M := hTU.trans inf_le_left
  by_contra hne'
  obtain ⟨h, hhH, hhT, hhN⟩ := exists_mem_normalizer_of_lt hH2 hTH (Ne.symm hne')
  have hhM : h ∈ M := S.normalizer_TOf_le_M_two hT hQe hR hn4 hw hr hcard hKM hhN
  exact hhT (hUT ⟨hhH, hhM⟩)

theorem not_Q_le_P_two (hT : TightData S) (hQe : QElem S) (hR : RSmall S) (hn4 : 4 ≤ n)
    {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2)
    (hKM : ¬ CGOf (w * r) ≤ M) : ¬ pCoreOf 2 M ≤ pCoreOf 2 (CGOf (w * r)) := by
  intro hQP
  have hsup := S.sup_eq_TOf_two hT hQe hR hn4 hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) = TOf M (w * r) :=
    (sup_eq_left.2 hQP).symm.trans hsup
  apply hKM
  intro k hk
  apply S.normalizer_TOf_le_M_two hT hQe hR hn4 hw hr hcard hKM
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [← hPT]
  refine ⟨fun ht => pCoreOf_normalized _ hk ht, fun ht => ?_⟩
  have := pCoreOf_normalized _ ((CGOf (w * r)).inv_mem hk) ht
  simpa [mul_assoc] using this

theorem centralizer_le_M_of_len_two (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hn4 : 4 ≤ n) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) : CGOf (w * r) ≤ M := by
  classical
  by_contra hKM
  obtain ⟨g, hgK, hgM⟩ := IsConcreteLE.not_le_iff_exists.1 hKM
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.1 hcard
  have hsup := S.sup_eq_TOf_two hT hQe hR hn4 hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) ≤ TOf M (w * r) := le_sup_left.trans hsup.le
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := hPT.trans (TOf_le_M M _)
  have hPQ : ¬ pCoreOf 2 (CGOf (w * r)) ≤ pCoreOf 2 M := S.not_P_le_Q hT hxQ hx1 hKM
  have hQP : ¬ pCoreOf 2 M ≤ pCoreOf 2 (CGOf (w * r)) :=
    S.not_Q_le_P_two hT hQe hR hn4 hw hr hcard hKM
  have hB0 : Subgroup.zpowers (w * r) ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers (w * r)) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hxQ)
  have hcons := centralizer_two_constrained S.hyp.charTwo hB0 hB2
  obtain ⟨t', ht'P, ht'Q⟩ := IsConcreteLE.not_le_iff_exists.1 hPQ
  have ht'M : t' ∈ M := hPM ht'P
  have hcasesP : ∀ s : G, ∀ hs : s ∈ pCoreOf 2 (CGOf (w * r)),
      S.θ ⟨s, hPM hs⟩ = 1 ∨ S.θ ⟨s, hPM hs⟩ = swap i j := fun s hs =>
    S.eq_one_or_swap_of_two hw hr hcard hij hI (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
      (Subgroup.mem_map.2 ⟨⟨s, hPM hs⟩, Subgroup.mem_subgroupOf.2 (hPT hs), rfl⟩)
  have hθt' : S.θ ⟨t', ht'M⟩ = swap i j :=
    (hcasesP t' ht'P).resolve_left fun h => ht'Q (S.mem_Q_of_theta_eq_one hR ht'M h)
  have hCP : pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) ≤ pCoreOf 2 (CGOf (w * r)) := by
    intro q hq
    have hqK : q ∈ CGOf (w * r) := S.Q_le_CGOf hT hxQ hq.1
    have hqt : q * t' = t' * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    refine hcons (Subgroup.mem_inf.2 ⟨hqK, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩)
    rcases hcasesP p hp with h | h
    · exact hT.abelian _ (S.mem_Q_of_theta_eq_one hR (hPM hp) h) q hq.1
    · have hM' : p * t'⁻¹ ∈ M := M.mul_mem (hPM hp) (M.inv_mem ht'M)
      have hdiv : p * t'⁻¹ ∈ pCoreOf 2 M := by
        refine S.mem_Q_of_theta_eq_one hR hM' ?_
        have : (⟨p * t'⁻¹, hM'⟩ : ↥M) = ⟨p, hPM hp⟩ * ⟨t', ht'M⟩⁻¹ := rfl
        rw [this, map_mul, map_inv, h, hθt', mul_inv_cancel]
      have h1 : (p * t'⁻¹) * q = q * (p * t'⁻¹) := hT.abelian _ hdiv q hq.1
      calc p * q = (p * t'⁻¹) * (t' * q) := by group
        _ = (p * t'⁻¹) * (q * t') := by rw [hqt]
        _ = ((p * t'⁻¹) * q) * t' := by group
        _ = (q * (p * t'⁻¹)) * t' := by rw [h1]
        _ = q * p := by group
  have hcentQ := S.card_Q_le_two_mul_cent hR ht'M hij hθt'
  have hCB : pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) ≤
      pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M := fun q hq => ⟨hCP hq, hq.1⟩
  have hBQ : pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M ≠ pCoreOf 2 M := fun h => hQP (by
    calc pCoreOf 2 M = pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M := h.symm
      _ ≤ pCoreOf 2 (CGOf (w * r)) := inf_le_left)
  have hBle : 2 * Nat.card ↥(pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M) ≤ Nat.card ↥(pCoreOf 2 M) := by
    have hBQ' : (pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M) ≠ ⊤ := by
      intro h
      apply hBQ
      refine le_antisymm inf_le_right fun q hq => ?_
      have : (⟨q, hq⟩ : ↥(pCoreOf 2 M)) ∈
          (pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M) := by
        rw [h]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    have h1 := Subgroup.card_mul_index
      ((pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M))
    have h2 : ((pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M)).index ≠ 1 :=
      fun h => hBQ' (Subgroup.index_eq_one.1 h)
    have h3 : ((pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M)).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h4 : Nat.card ↥((pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M)) =
        Nat.card ↥(pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h4] at h1
    have h5 : 2 ≤ ((pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M)).index := by
      omega
    nlinarith [h1, h5]
  have hBC : pCoreOf 2 (CGOf (w * r)) ⊓ pCoreOf 2 M =
      pCoreOf 2 M ⊓ Subgroup.centralizer ({t'} : Set G) :=
    (Subgroup.eq_of_le_of_card_ge hCB (by omega)).symm
  set P : Subgroup G := pCoreOf 2 (CGOf (w * r)) with hP
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set B : Subgroup G := P ⊓ Q with hB
  have hBP : B ≤ P := inf_le_left
  have hBQle : B ≤ Q := inf_le_right
  have hswapmem : swap i j ∈ (P.subgroupOf M).map S.θ :=
    Subgroup.mem_map.2 ⟨⟨t', ht'M⟩, Subgroup.mem_subgroupOf.2 ht'P, hθt'⟩
  have hN'2 : Nat.card ↥((P.subgroupOf M).map S.θ) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : ↥((P.subgroupOf M).map S.θ))]
    refine ⟨⟨swap i j, hswapmem⟩, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun f : Perm (Fin (2 * n + 1)) => f i) (congrArg Subtype.val h)
      simp at h1
      exact hij h1.symm
    · intro y hy
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 y.2
      have hmP : (m : G) ∈ P := Subgroup.mem_subgroupOf.1 hm
      rcases hcasesP m hmP with h | h
      · exact absurd (Subtype.ext (hmy.symm.trans (by rw [h]; rfl))) hy
      · exact Subtype.ext (hmy.symm.trans h)
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥B := by
    have h1 := S.card_eq_card_inf_mul hT hPM (isPGroup_pCoreOf' _)
    rw [h1, hN'2, mul_comm]
  have hBgP : conjSubgroup g B ≤ P := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ B := mem_conjSubgroup.1 hx
    have := pCoreOf_normalized (CGOf (w * r)) hgK (hBP hx')
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  have hcardg : Nat.card ↥(conjSubgroup g B) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hidx : ∀ A : Subgroup G, A ≤ P → Nat.card ↥A = Nat.card ↥B → (A.subgroupOf P).index = 2 := by
    intro A hAP hAB
    have h1 := Subgroup.card_mul_index (A.subgroupOf P)
    have h2 : Nat.card ↥(A.subgroupOf P) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
    rw [h2, hAB, hPcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hBpos (h1.trans (mul_comm _ _))
  set D : Subgroup G := B ⊓ conjSubgroup g B with hD
  have hDP : D ≤ P := inf_le_left.trans hBP
  have hDidx : (D.subgroupOf P).index ≤ 4 := by
    have h1 : D.subgroupOf P = B.subgroupOf P ⊓ (conjSubgroup g B).subgroupOf P := by
      ext x
      simp only [hD, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [h1]
    refine Subgroup.index_inf_le.trans ?_
    rw [hidx B hBP rfl, hidx _ hBgP hcardg]
  have hDcard : Nat.card ↥D * (D.subgroupOf P).index = Nat.card ↥P := by
    have h1 := Subgroup.card_mul_index (D.subgroupOf P)
    have h2 : Nat.card ↥(D.subgroupOf P) = Nat.card ↥D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
    rwa [h2] at h1
  have hDQ : D ≤ Q := inf_le_left.trans hBQle
  have hDg : ∀ h ∈ D, g⁻¹ * h * g ∈ Q := by
    intro h hh
    exact hBQle (mem_conjSubgroup.1 hh.2)
  have hA := S.hAway_of_four_le hT hQe hR hn4
  have hcl := S.card_le_of_conj_inter hT hQe hA hgM hDQ hDg
  have hD2 := S.card_D2_le (D := D) hDQ hij (fun h => by
    refine S.coord_eq_of_comm hR ht'M hθt' (z := ⟨h, hDQ h.2⟩) ?_
    have hhB : (h : G) ∈ Q ⊓ Subgroup.centralizer ({t'} : Set G) := by
      rw [← hBC]; exact h.2.1
    have h1 : (h : G) * t' = t' * (h : G) := Subgroup.mem_centralizer_singleton_iff.1 hhB.2
    show t' * (h : G) * t'⁻¹ = (h : G)
    calc t' * (h : G) * t'⁻¹ = ((h : G) * t') * t'⁻¹ := by rw [h1]
      _ = (h : G) := by group)
  have hQ2 := S.card_Q2_le
  have hRpos : 1 ≤ Nat.card ↥(rOf M X) := Nat.card_pos
  have hcardQ := S.card_Q
  have hW : Nat.card ↥S.D.W = Nat.card ↥(coreMod (2 * n + 1)) := Nat.card_congr S.D.β.toEquiv
  have hmul := card_coreMod_mul_two (n := 2 * n + 1) (odd_two_mul_add_one n)
  have hineq := counting_ineq (2 * n + 1) (Nat.card ↥(rOf M X)) (by omega) hRpos
  have hpow : (2 : ℕ) ^ (2 * n + 1) = 8 * 2 ^ (2 * n + 1 - 3) := by
    have : 2 * n + 1 = (2 * n + 1 - 3) + 3 := by omega
    conv_lhs => rw [this]
    rw [pow_add]
    ring
  rw [hcardQ, hW] at hcentQ hBle
  have hCeq : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t'} : Set G)) = Nat.card ↥B := by
    rw [← hBC]
  have hmain : Nat.card ↥(coreMod (2 * n + 1)) * 2 = 2 ^ (2 * n + 1) := hmul
  have hP4 : Nat.card ↥P ≤ 4 * Nat.card ↥D := by
    rw [← hDcard]
    exact Nat.mul_le_mul_left _ hDidx |>.trans (by rw [mul_comm])
  nlinarith [hcentQ, hBle, hCeq, hcl, hD2, hQ2, hineq, hpow, hmain, hP4, hPcard]

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
