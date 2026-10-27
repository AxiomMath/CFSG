module

public import CFSG.CGT.PushingUpLit.SolK.SevenFusion
public import CFSG.CGT.PushingUpLit.SolK.TwoA
public import CFSG.CGT.PushingUpLit.SolK.TwoB

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

theorem coreAct_swap_fix {d : ℕ} {i j a b : Fin d} (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i)
    (hbj : b ≠ j) :
    coreAct d (swap i j) (pairVec i j * pairVec a b) = pairVec i j * pairVec a b := by
  rw [map_mul, coreAct_pairVec, coreAct_pairVec, swap_apply_left, swap_apply_right,
    swap_apply_of_ne_of_ne hai haj, swap_apply_of_ne_of_ne hbi hbj, pairVec_comm j i]

theorem card_vsupp_pairVec_mul {d : ℕ} {i j a b : Fin d} (hij : i ≠ j) (hab : a ≠ b)
    (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) :
    (vsupp (pairVec i j * pairVec a b)).card = 4 := by
  classical
  have h1 : ∀ m, vcoord (pairVec i j) m = 1 → vcoord (pairVec a b) m = 0 := by
    intro m hm
    rw [vcoord_pairVec] at hm ⊢
    by_cases hmi : m = i
    · subst hmi
      simp [hai.symm, hbi.symm]
    · by_cases hmj : m = j
      · subst hmj
        simp [haj.symm, hbj.symm]
      · simp [hmi, hmj] at hm
  have h2 : ∀ m, vcoord (pairVec a b) m = 1 → vcoord (pairVec i j) m = 0 := by
    intro m hm
    rw [vcoord_pairVec] at hm ⊢
    by_cases hma : m = a
    · subst hma
      simp [hai, haj]
    · by_cases hmb : m = b
      · subst hmb
        simp [hbi, hbj]
      · simp [hma, hmb] at hm
  rw [card_vsupp_mul_of_disjoint h1 h2, vsupp_pairVec hij, vsupp_pairVec hab, Finset.card_pair hij,
    Finset.card_pair hab]

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

@[expose] noncomputable def elemOf (v : ↥(coreMod (2 * n + 1))) : G :=
  ((S.D.β.symm v : ↥S.D.W) : G)

theorem elemOf_mem (v : ↥(coreMod (2 * n + 1))) : S.elemOf v ∈ S.D.W := (S.D.β.symm v).2

theorem beta_elemOf (v : ↥(coreMod (2 * n + 1))) : S.D.β ⟨S.elemOf v, S.elemOf_mem v⟩ = v :=
  S.D.β.apply_symm_apply v

theorem elemOf_mul (u v : ↥(coreMod (2 * n + 1))) :
    S.elemOf (u * v) = S.elemOf u * S.elemOf v := by
  unfold elemOf
  rw [map_mul]
  rfl

theorem elemOf_inv (v : ↥(coreMod (2 * n + 1))) : S.elemOf v⁻¹ = (S.elemOf v)⁻¹ := by
  unfold elemOf
  rw [map_inv]
  rfl

theorem hasLen_elemOf {v : ↥(coreMod (2 * n + 1))} {l : ℕ} (h : (vsupp v).card = l) :
    S.HasLen (S.elemOf v) l :=
  ⟨S.elemOf v, S.elemOf_mem v, 1, one_mem _, (mul_one _).symm, by rw [S.beta_elemOf]; exact h⟩

theorem elemOf_comm {t : G} (htM : t ∈ M) {v : ↥(coreMod (2 * n + 1))}
    (hv : coreAct (2 * n + 1) (S.θ ⟨t, htM⟩) v = v) : t * S.elemOf v * t⁻¹ = S.elemOf v := by
  have hW : t * S.elemOf v * t⁻¹ ∈ S.D.W := S.W_normalized htM (S.elemOf_mem v)
  have h1 := S.θ_spec ⟨t, htM⟩ ⟨S.elemOf v, S.elemOf_mem v⟩ hW
  rw [S.beta_elemOf, hv] at h1
  have h2 : (⟨t * S.elemOf v * t⁻¹, hW⟩ : ↥S.D.W) = ⟨S.elemOf v, S.elemOf_mem v⟩ :=
    S.D.β.injective (h1.trans (S.beta_elemOf v).symm)
  exact congrArg Subtype.val h2

theorem normalizer_TOf_le_M_two_seven (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hn : n = 3) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) (hKM : ¬ CGOf (w * r) ≤ M) :
    Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) ≤ M := by
  classical
  intro g hg
  by_contra hgM
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.1 hcard
  have hTQ := S.not_TOf_le_Q hT hxQ hx1 hKM
  obtain ⟨t, htT, htQ⟩ := IsConcreteLE.not_le_iff_exists.1 hTQ
  have htM : t ∈ M := TOf_le_M M _ htT
  have hθt : S.θ ⟨t, htM⟩ = swap i j := by
    rcases S.eq_one_or_swap_of_two hw hr hcard hij hI (TOf_le_M M _) (TOf_le_C M _)
      (isPGroup_TOf M _) (fun k hk u hu => normalized_TOf M (w * r) hk hu)
      (Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 htT, rfl⟩) with h | h
    · exact absurd (S.mem_Q_of_theta_eq_one hR htM h) htQ
    · exact h
  set Z : Subgroup G := TOf M (w * r) ⊓ Subgroup.centralizer ((TOf M (w * r) : Subgroup G) : Set G)
    with hZ
  have hQT := S.Q_le_TOf hT hxQ
  have hZQ : Z ≤ pCoreOf 2 M := by
    intro z hz
    have hzM : z ∈ M := TOf_le_M M _ hz.1
    refine S.mem_Q_of_theta_eq_one hR hzM ?_
    refine (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨z, hzM⟩).2 fun w' hw' => ?_
    have h1 := Subgroup.mem_centralizer_iff.1 hz.2 w' (hQT (S.W_le_Q hw'))
    show z * w' * z⁻¹ = w'
    calc z * w' * z⁻¹ = (w' * z) * z⁻¹ := by rw [h1]
      _ = w' := by group
  have hDg : ∀ h ∈ Z, g⁻¹ * h * g ∈ pCoreOf 2 M := by
    intro h hh
    have hginv : g⁻¹ ∈ Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).inv_mem hg
    have hmemT : g⁻¹ * h * g ∈ TOf M (w * r) := by
      have := (Subgroup.mem_normalizer_iff.1 hginv h).1 hh.1
      simpa using this
    have hcentT : ∀ τ ∈ TOf M (w * r), τ * (g⁻¹ * h * g) = (g⁻¹ * h * g) * τ := by
      intro τ hτ
      have hτ' : g * τ * g⁻¹ ∈ TOf M (w * r) := (Subgroup.mem_normalizer_iff.1 hg τ).1 hτ
      have h1 := Subgroup.mem_centralizer_iff.1 hh.2 _ hτ'
      calc τ * (g⁻¹ * h * g) = g⁻¹ * ((g * τ * g⁻¹) * h) * g := by group
        _ = g⁻¹ * (h * (g * τ * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * h * g) * τ := by group
    exact hZQ ⟨hmemT, Subgroup.mem_centralizer_iff.2 hcentT⟩
  have hCt : pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G) ≤ Z := by
    intro q hq
    have hqt : q * t = t * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    refine ⟨hQT hq.1, Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_⟩
    have hτM : τ ∈ M := TOf_le_M M _ hτ
    have hcases : S.θ ⟨τ, hτM⟩ = 1 ∨ S.θ ⟨τ, hτM⟩ = swap i j :=
      S.eq_one_or_swap_of_two hw hr hcard hij hI (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
        (fun k hk u hu => normalized_TOf M (w * r) hk hu)
        (Subgroup.mem_map.2 ⟨⟨τ, hτM⟩, Subgroup.mem_subgroupOf.2 hτ, rfl⟩)
    rcases hcases with h | h
    · exact (hT.abelian _ (S.mem_Q_of_theta_eq_one hR hτM h) q hq.1)
    · have hM' : τ * t⁻¹ ∈ M := M.mul_mem hτM (M.inv_mem htM)
      have hdiv : τ * t⁻¹ ∈ pCoreOf 2 M := by
        refine S.mem_Q_of_theta_eq_one hR hM' ?_
        have : (⟨τ * t⁻¹, hM'⟩ : ↥M) = ⟨τ, hτM⟩ * ⟨t, htM⟩⁻¹ := rfl
        rw [this, map_mul, map_inv, h, hθt, mul_inv_cancel]
      have h1 : (τ * t⁻¹) * q = q * (τ * t⁻¹) := (hT.abelian _ hdiv q hq.1)
      calc τ * q = (τ * t⁻¹) * (t * q) := by group
        _ = (τ * t⁻¹) * (q * t) := by rw [hqt]
        _ = ((τ * t⁻¹) * q) * t := by group
        _ = (q * (τ * t⁻¹)) * t := by rw [h1]
        _ = q * τ := by group
  obtain ⟨a, b, c, e, hai, haj, hbi, hbj, -, -, -, -, hab, -, -, -, -, -⟩ :=
    exists_four_distinct (by omega : 7 ≤ 2 * n + 1) i j
  have hzfix : coreAct (2 * n + 1) (S.θ ⟨t, htM⟩) (pairVec i j * pairVec a b) =
      pairVec i j * pairVec a b := by
    rw [hθt]
    exact coreAct_swap_fix hai haj hbi hbj
  have hzcomm := S.elemOf_comm htM hzfix
  have hzW := S.elemOf_mem (pairVec i j * pairVec a b)
  have hzQ : S.elemOf (pairVec i j * pairVec a b) ∈ pCoreOf 2 M := S.W_le_Q hzW
  have hzZ : S.elemOf (pairVec i j * pairVec a b) ∈ Z := by
    refine hCt ⟨hzQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc S.elemOf (pairVec i j * pairVec a b) * t
        = (t * S.elemOf (pairVec i j * pairVec a b) * t⁻¹) * t := by rw [hzcomm]
      _ = t * S.elemOf (pairVec i j * pairVec a b) := by group
  have hl4 : S.HasLen (S.elemOf (pairVec i j * pairVec a b)) 4 :=
    S.hasLen_elemOf (card_vsupp_pairVec_mul hij hab hai haj hbi hbj)
  exact S.not_conj_len_four_seven hT hQe hR hn hgM hzQ (hDg _ hzZ) hl4

theorem sup_eq_TOf_two' (hT : TightData S) (hR : RSmall S)
    {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2)
    (hKM : ¬ CGOf (w * r) ≤ M)
    (hNT : Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) ≤ M) :
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
  have hhM : h ∈ M := hNT hhN
  exact hhT (hUT ⟨hhH, hhM⟩)

theorem not_Q_le_P_two' (hT : TightData S) (hR : RSmall S)
    {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2)
    (hKM : ¬ CGOf (w * r) ≤ M)
    (hNT : Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) ≤ M) :
    ¬ pCoreOf 2 M ≤ pCoreOf 2 (CGOf (w * r)) := by
  intro hQP
  have hsup := S.sup_eq_TOf_two' hT hR hw hr hcard hKM hNT
  have hPT : pCoreOf 2 (CGOf (w * r)) = TOf M (w * r) :=
    (sup_eq_left.2 hQP).symm.trans hsup
  apply hKM
  intro k hk
  apply hNT
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [← hPT]
  refine ⟨fun ht => pCoreOf_normalized _ hk ht, fun ht => ?_⟩
  have := pCoreOf_normalized _ ((CGOf (w * r)).inv_mem hk) ht
  simpa [mul_assoc] using this

theorem centralizer_le_M_of_len_two_seven (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hn : n = 3) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) : CGOf (w * r) ≤ M := by
  classical
  by_contra hKM
  obtain ⟨g, hgK, hgM⟩ := IsConcreteLE.not_le_iff_exists.1 hKM
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.1 hcard
  have hNT := S.normalizer_TOf_le_M_two_seven hT hQe hR hn hw hr hcard hKM
  have hsup := S.sup_eq_TOf_two' hT hR hw hr hcard hKM hNT
  have hPT : pCoreOf 2 (CGOf (w * r)) ≤ TOf M (w * r) := le_sup_left.trans hsup.le
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := hPT.trans (TOf_le_M M _)
  have hPQ : ¬ pCoreOf 2 (CGOf (w * r)) ≤ pCoreOf 2 M := S.not_P_le_Q hT hxQ hx1 hKM
  have hQP : ¬ pCoreOf 2 M ≤ pCoreOf 2 (CGOf (w * r)) :=
    S.not_Q_le_P_two' hT hR hw hr hcard hKM hNT
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
  have hP4 : Nat.card ↥P ≤ 4 * Nat.card ↥D := by
    rw [← hDcard]
    exact Nat.mul_le_mul_left _ hDidx |>.trans (by rw [mul_comm])
  have hDpos : 0 < Nat.card ↥D := Nat.card_pos
  have hBD : D ≤ B := inf_le_left
  have hDno4 : ∀ h ∈ D, ¬ S.HasLen h 4 := fun h hh hl =>
    S.not_conj_len_four_seven hT hQe hR hn hgM (hDQ hh) (hDg h hh) hl
  have hDB : (D.subgroupOf B).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (D.subgroupOf B)
    have h2 : Nat.card ↥(D.subgroupOf B) = Nat.card ↥D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBD).toEquiv
    rw [h2] at h1
    have hB2D : Nat.card ↥B ≤ 2 * Nat.card ↥D := by omega
    have h3 : Nat.card ↥D * (D.subgroupOf B).index ≤ Nat.card ↥D * 2 := by
      rw [h1]
      omega
    exact Nat.le_of_mul_le_mul_left h3 hDpos
  obtain ⟨a, b, c, e, hai, haj, hbi, hbj, hci, hcj, hei, hej, hab, hac, hae, hbc, hbe, hce⟩ :=
    exists_four_distinct (by omega : 7 ≤ 2 * n + 1) i j
  have hmemB : ∀ (v : ↥(coreMod (2 * n + 1))),
      coreAct (2 * n + 1) (S.θ ⟨t', ht'M⟩) v = v → S.elemOf v ∈ B := by
    intro v hv
    have hvQ : S.elemOf v ∈ Q := S.W_le_Q (S.elemOf_mem v)
    have hcomm := S.elemOf_comm ht'M hv
    rw [hBC]
    refine Subgroup.mem_inf.2 ⟨hvQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc S.elemOf v * t' = (t' * S.elemOf v * t'⁻¹) * t' := by rw [hcomm]
      _ = t' * S.elemOf v := by group
  have hfixu : coreAct (2 * n + 1) (S.θ ⟨t', ht'M⟩) (pairVec i j * pairVec a b) =
      pairVec i j * pairVec a b := by
    rw [hθt']
    exact coreAct_swap_fix hai haj hbi hbj
  have hfixv : coreAct (2 * n + 1) (S.θ ⟨t', ht'M⟩) (pairVec i j * pairVec c e) =
      pairVec i j * pairVec c e := by
    rw [hθt']
    exact coreAct_swap_fix hci hcj hei hej
  have huB := hmemB _ hfixu
  have hvB := hmemB _ hfixv
  have hu4 : S.HasLen (S.elemOf (pairVec i j * pairVec a b)) 4 :=
    S.hasLen_elemOf (card_vsupp_pairVec_mul hij hab hai haj hbi hbj)
  have hv4 : S.HasLen (S.elemOf (pairVec i j * pairVec c e)) 4 :=
    S.hasLen_elemOf (card_vsupp_pairVec_mul hij hce hci hcj hei hej)
  have huD : S.elemOf (pairVec i j * pairVec a b) ∉ D := fun h => hDno4 _ h hu4
  have hvD : S.elemOf (pairVec i j * pairVec c e) ∉ D := fun h => hDno4 _ h hv4
  have hq := mul_inv_mem_of_index_le_two hDB
    (u := (⟨S.elemOf (pairVec i j * pairVec a b), huB⟩ : ↥B))
    (v := (⟨S.elemOf (pairVec i j * pairVec c e), hvB⟩ : ↥B))
    (fun h => huD (Subgroup.mem_subgroupOf.1 h)) (fun h => hvD (Subgroup.mem_subgroupOf.1 h))
  have hq' : S.elemOf (pairVec i j * pairVec a b) *
      (S.elemOf (pairVec i j * pairVec c e))⁻¹ ∈ D := Subgroup.mem_subgroupOf.1 hq
  have hprod : S.elemOf (pairVec i j * pairVec a b) *
      (S.elemOf (pairVec i j * pairVec c e))⁻¹ = S.elemOf (pairVec a b * pairVec c e) := by
    rw [← S.elemOf_inv, ← S.elemOf_mul]
    congr 1
    rw [coreMod_inv_eq]
    refine vcoord_ext fun m => ?_
    simp only [vcoord_mul]
    generalize vcoord (pairVec i j) m = x
    generalize vcoord (pairVec a b) m = y
    generalize vcoord (pairVec c e) m = z
    revert x y z
    decide
  rw [hprod] at hq'
  exact hDno4 _ hq' (S.hasLen_elemOf (card_vsupp_pairVec_mul hab hce hac.symm hbc.symm hae.symm
    hbe.symm))

theorem centInM_seven (hT : TightData S) (hR : RSmall S) (hn : n = 3) : CentInM S := by
  have hQe : QElem S := SolCfg.RSmall.elem S hR
  intro x hx hx1 k hk
  obtain ⟨l, hl⟩ := S.exists_hasLen hx
  have hkC : k ∈ CGOf x := by
    rw [CGOf, ← centralizer_singleton_eq_zpowers]
    exact hk
  by_cases hl2 : l = 2
  · subst hl2
    obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl
    exact S.centralizer_le_M_of_len_two_seven hT hQe hR hn hw hr hcard hkC
  · exact S.hAway_seven hT hQe hR hn x hx hx1 (fun h2 => hl2 (SolCfg.HasLen.unique S hl h2)) k
      (mem_centralizer_zpowers_iff.1 hkC)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
