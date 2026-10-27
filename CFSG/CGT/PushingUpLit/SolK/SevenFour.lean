module

public import CFSG.CGT.PushingUpLit.SolK.NoIndexThree
public import CFSG.CGT.PushingUpLit.SolK.OrbitIndex
public import CFSG.CGT.PushingUpLit.SolK.FourC
public import CFSG.CGT.PushingUpLit.SolK.FourD

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

theorem vsupp_pairVec {d : ℕ} {a b : Fin d} (hab : a ≠ b) : vsupp (pairVec a b) = {a, b} := by
  classical
  ext i
  rw [mem_vsupp, vcoord_pairVec]
  by_cases hia : i = a
  · subst hia
    simp [hab]
  · by_cases hib : i = b
    · subst hib
      simp [hia]
    · simp [hia, hib]

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem no_index_three_CMOf (hT : TightData S) (hR : RSmall S) (hn : n = 3) {y : G}
    (hy : y ∈ S.D.W) (hcard : (vsupp (S.D.β ⟨y, hy⟩)).card = 6) {N' : Subgroup G}
    (hN'le : N' ≤ CMOf M y) (hcardN : Nat.card ↥(CMOf M y) = 3 * Nat.card ↥N') : False := by
  classical
  have hyQ : y ∈ pCoreOf 2 M := S.W_le_Q hy
  have hQC : pCoreOf 2 M ≤ CMOf M y := fun q hq =>
    Subgroup.mem_inf.2 ⟨pCoreOf_le_self M hq,
      mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (hT.abelian q hq y hyQ))⟩
  let Q : Subgroup ↥(CMOf M y) := (pCoreOf 2 M).subgroupOf (CMOf M y)
  have hQn : Q.Normal := ⟨fun q hq h => by
    show ((h : G) * (q : G) * (h : G)⁻¹) ∈ pCoreOf 2 M
    exact pCoreOf_normalized M h.2.1 hq⟩
  have hQ2 : IsPGroup 2 Q :=
    (isPGroup_pCoreOf' M).of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  let ψ : ↥(CMOf M y) →* Perm (Fin (2 * n + 1)) :=
    S.θ.comp (Subgroup.inclusion (inf_le_left : CMOf M y ≤ M))
  have hψ : ∀ h : ↥(CMOf M y), ψ h = S.θ ⟨(h : G), h.2.1⟩ := fun h => rfl
  have hker : ψ.ker ≤ Q := by
    intro h hh
    rw [MonoidHom.mem_ker, hψ] at hh
    exact S.mem_Q_of_theta_eq_one hR h.2.1 hh
  set B := vsupp (S.D.β ⟨y, hy⟩) with hB
  have hrange : ψ.range ≤ setStab B := by
    rintro _ ⟨h, rfl⟩
    have hc : (h : G) * (y * 1) * (h : G)⁻¹ = y * 1 := by
      have := mem_centralizer_zpowers_iff.1 h.2.2
      simpa using this
    rw [hψ]
    exact (coreAct_eq_iff _ _).1 (S.fix_of_comm hy (one_mem _) ⟨(h : G), h.2.1⟩ hc)
  have halt : altOn B ≤ ψ.range := by
    intro τ hτ
    have hτalt : τ ∈ alternatingGroup (Fin (2 * n + 1)) :=
      Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2
    obtain ⟨c, hcM, hcτ⟩ := S.exists_lift_J hτalt
    have hcy : c * y * c⁻¹ = y := by
      have hW : c * y * c⁻¹ ∈ S.D.W := S.W_normalized hcM hy
      have h1 := S.θ_spec ⟨c, hcM⟩ ⟨y, hy⟩ hW
      rw [hcτ] at h1
      have h2 : coreAct (2 * n + 1) τ (S.D.β ⟨y, hy⟩) = S.D.β ⟨y, hy⟩ :=
        (coreAct_eq_iff _ _).2 (altOn_le_setStab B hτ)
      rw [h2] at h1
      exact congrArg Subtype.val (S.D.β.injective h1)
    have hcC : c ∈ CMOf M y := Subgroup.mem_inf.2 ⟨hcM, mem_centralizer_zpowers_iff.2 hcy⟩
    exact ⟨⟨c, hcC⟩, by rw [hψ]; exact hcτ⟩
  have hN : (N'.subgroupOf (CMOf M y)).index = 3 := by
    have h1 := Subgroup.card_mul_index (N'.subgroupOf (CMOf M y))
    have h2 : Nat.card ↥(N'.subgroupOf (CMOf M y)) = Nat.card ↥N' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN'le).toEquiv
    rw [h2, hcardN] at h1
    have hpos : 0 < Nat.card ↥N' := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  exact no_index_three hQ2 ψ hker (by omega) (by omega) hrange halt hN

theorem centralizer_le_M_of_len_four_seven (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hn : n = 3) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4) : CGOf (w * r) ≤ M := by
  classical
  by_contra hKM
  have hrbot := S.rOf_eq_bot hT hQe hR hw hr hcard hKM
  have hr1 : r = 1 := Subgroup.mem_bot.1 (hrbot ▸ hr)
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hsup := S.sup_eq_TOf hT hQe hR hw hr hcard hKM
  have hPT : pCoreOf 2 (CGOf (w * r)) ≤ TOf M (w * r) := le_sup_left.trans hsup.le
  have hPM : pCoreOf 2 (CGOf (w * r)) ≤ M := hPT.trans (TOf_le_M M _)
  have hθP := S.theta_P_eq hT hQe hR hw hr hcard hKM
  have hFT : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hNne := S.TN_ne_bot hT hQe hR hw hr hcard hKM
  set I : Finset (Fin (2 * n + 1)) := vsupp (S.D.β ⟨w, hw⟩) with hI
  set E : Subgroup G := pCoreOf 2 (CGOf (w * r)) ⊓
    Subgroup.centralizer ((pCoreOf 2 (CGOf (w * r)) : Subgroup G) : Set G) with hE
  have hEQ : E ≤ pCoreOf 2 M := fun z hz =>
    S.center_P_le_Q hT hQe hR hw hr hcard hKM hz.1
      (fun p hp => Subgroup.mem_centralizer_iff.1 hz.2 p hp)
  have hB : Subgroup.zpowers (w * r) ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers (w * r)) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hxQ)
  have hcons := centralizer_two_constrained S.hyp.charTwo hB hB2
  have hxE : w * r ∈ E := by
    have hxK : w * r ∈ CGOf (w * r) := S.Q_le_CGOf hT hxQ hxQ
    have hcentx : ∀ p ∈ pCoreOf 2 (CGOf (w * r)), p * (w * r) = (w * r) * p := by
      intro p hp
      have h1 := mem_centralizer_zpowers_iff.1 (pCoreOf_le_self _ hp)
      calc p * (w * r) = (p * (w * r) * p⁻¹) * p := by group
        _ = (w * r) * p := by rw [h1]
    exact Subgroup.mem_inf.2
      ⟨hcons (Subgroup.mem_inf.2 ⟨hxK, Subgroup.mem_centralizer_iff.2 hcentx⟩),
        Subgroup.mem_centralizer_iff.2 hcentx⟩
  have hwE : w ∈ E := by simpa [hr1] using hxE
  have hvfix : ∀ (z : G) (hzW : z ∈ S.D.W), z ∈ E → ∀ σ ∈ S.TN (w * r),
      coreAct (2 * n + 1) σ (S.D.β ⟨z, hzW⟩) = S.D.β ⟨z, hzW⟩ := by
    intro z hzW hzE σ hσ
    rw [← hθP] at hσ
    obtain ⟨pm, hpm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hpP : (pm : G) ∈ pCoreOf 2 (CGOf (w * r)) := Subgroup.mem_subgroupOf.1 hpm
    have hcomm : (pm : G) * z * (pm : G)⁻¹ = z := by
      have h1 := Subgroup.mem_centralizer_iff.1 hzE.2 _ hpP
      calc (pm : G) * z * (pm : G)⁻¹ = (z * (pm : G)) * (pm : G)⁻¹ := by rw [h1]
        _ = z := by group
    have hW' : (pm : G) * z * (pm : G)⁻¹ ∈ S.D.W := S.W_normalized pm.2 hzW
    have h2 := S.θ_spec pm ⟨z, hzW⟩ hW'
    have h3 : (⟨(pm : G) * z * (pm : G)⁻¹, hW'⟩ : ↥S.D.W) = ⟨z, hzW⟩ := Subtype.ext hcomm
    rw [h3] at h2
    exact h2.symm
  have hconst : ∀ (z : G) (hzW : z ∈ S.D.W), z ∈ E → ∀ i ∈ I, ∀ j ∈ I,
      vcoord (S.D.β ⟨z, hzW⟩) i = vcoord (S.D.β ⟨z, hzW⟩) j := by
    intro z hzW hzE i hi j hj
    obtain ⟨σ, hσN, hσ⟩ := hFT.transitive hcard hNne hi hj
    subst hσ
    have h1 := congrArg (fun u => vcoord u (σ i)) (hvfix z hzW hzE σ hσN)
    simp only [vcoord_coreAct] at h1
    simpa using h1
  have hIc : Iᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < Iᶜ.card)
  have haI : a ∉ I := Finset.mem_compl.1 ha
  have hbI : b ∉ I := Finset.mem_compl.1 hb
  have hJ : ({a, b} : Finset (Fin (2 * n + 1))) ⊆ Iᶜ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hDE := S.DeltaJ_le_E hT hQe hR hw hr hcard hKM hJ
  have hδE : ((S.D.β.symm (pairVec a b) : ↥S.D.W) : G) ∈ E :=
    hDE (S.pairVec_lift_mem (by simp) (by simp))
  have hδW : ((S.D.β.symm (pairVec a b) : ↥S.D.W) : G) ∈ S.D.W := (S.D.β.symm (pairVec a b)).2
  set y : G := w * ((S.D.β.symm (pairVec a b) : ↥S.D.W) : G) with hy
  have hyW : y ∈ S.D.W := S.D.W.mul_mem hw hδW
  have hyE : y ∈ E := E.mul_mem hwE hδE
  have hβy : S.D.β ⟨y, hyW⟩ = S.D.β ⟨w, hw⟩ * pairVec a b := by
    have : (⟨y, hyW⟩ : ↥S.D.W) = ⟨w, hw⟩ * S.D.β.symm (pairVec a b) := rfl
    rw [this, map_mul, MulEquiv.apply_symm_apply]
  have hycard : (vsupp (S.D.β ⟨y, hyW⟩)).card = 6 := by
    rw [hβy, card_vsupp_mul_of_disjoint, vsupp_pairVec hab, Finset.card_pair hab, ← hI, hcard]
    · intro i hi
      rw [vcoord_pairVec]
      have hia : i ≠ a := fun h => haI (h ▸ mem_vsupp.2 hi)
      have hib : i ≠ b := fun h => hbI (h ▸ mem_vsupp.2 hi)
      simp [hia, hib]
    · intro i hi
      rw [vcoord_pairVec] at hi
      by_cases hia : i = a
      · exact vcoord_eq_zero_of_not_mem (hia ▸ haI)
      · by_cases hib : i = b
        · exact vcoord_eq_zero_of_not_mem (hib ▸ hbI)
        · simp [hia, hib] at hi
  have hy1 : y ≠ 1 := by
    have := S.mul_ne_one hyW (one_mem _) (by omega : 0 < (vsupp (S.D.β ⟨y, hyW⟩)).card)
    simpa using this
  have hyQ : y ∈ pCoreOf 2 M := S.W_le_Q hyW
  have hl6 : S.HasLen y 6 := ⟨y, hyW, 1, one_mem _, (mul_one y).symm, hycard⟩
  have hCGy : CGOf y ≤ M := fun k hk =>
    ((S.centralizer_eq_of_len S.hyp.charTwo hT hyQ hy1 hl6 (by norm_num) (by norm_num)).2)
      (Subgroup.centralizer_le_normalizer _ hk)
  obtain ⟨g, hgK, hgM⟩ := IsConcreteLE.not_le_iff_exists.1 hKM
  have hP : ∀ k ∈ CGOf (w * r), ∀ p ∈ pCoreOf 2 (CGOf (w * r)),
      k * p * k⁻¹ ∈ pCoreOf 2 (CGOf (w * r)) := fun k hk p hp => pCoreOf_normalized _ hk hp
  have hy'E : g * y * g⁻¹ ∈ E := center_conj_mem hP hgK hyE
  have hy'Q : g * y * g⁻¹ ∈ pCoreOf 2 M := hEQ hy'E
  have hy'W : g * y * g⁻¹ ∈ S.D.W := S.mem_W_of_rOf_bot hrbot hy'Q
  have hy'1 : g * y * g⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  set v'' : ↥(coreMod (2 * n + 1)) := S.D.β ⟨g * y * g⁻¹, hy'W⟩ with hv''
  have hl'even : Even (vsupp v'').card := even_card_vsupp v''
  have hl'le : (vsupp v'').card ≤ 2 * n + 1 := (Finset.card_le_univ _).trans (by simp)
  have hl'pos : 0 < (vsupp v'').card := by
    rcases Nat.eq_zero_or_pos (vsupp v'').card with h0 | h0
    · exfalso
      apply hy'1
      have hv1 : v'' = 1 := by
        refine vcoord_ext fun i => ?_
        rw [vcoord_one]
        exact vcoord_eq_zero_of_not_mem (by rw [Finset.card_eq_zero.1 h0]; simp)
      have : (⟨g * y * g⁻¹, hy'W⟩ : ↥S.D.W) = 1 :=
        S.D.β.injective (by rw [← hv'', hv1, map_one])
      exact congrArg Subtype.val this
    · exact h0
  have hl' : S.HasLen (g * y * g⁻¹) (vsupp v'').card :=
    ⟨g * y * g⁻¹, hy'W, 1, one_mem _, (mul_one _).symm, rfl⟩
  have hcases : (vsupp v'').card = 2 ∨ (vsupp v'').card = 4 ∨ (vsupp v'').card = 6 := by
    obtain ⟨k, hk⟩ := hl'even
    omega
  rcases hcases with h2 | h4 | h6
  ·
    have hoy := S.card_eq_choose_mul_card hR hyW (one_mem _)
    have hoz : Nat.card ↥M = (2 * n + 1).choose 2 * Nat.card ↥(CMOf M (g * y * g⁻¹)) := by
      have h := S.card_eq_choose_mul_card hR hy'W (one_mem _)
      have e1 : (vsupp (S.D.β ⟨g * y * g⁻¹, hy'W⟩)).card = 2 := h2
      rw [e1] at h
      simpa only [mul_one] using h
    rw [hycard] at hoy
    simp only [mul_one] at hoy
    set N' : Subgroup G := conjSubgroup g⁻¹ (CMOf M (g * y * g⁻¹)) with hN'
    have hN'le : N' ≤ CMOf M y := by
      intro x hx
      have hx' : (g⁻¹)⁻¹ * x * g⁻¹ ∈ CMOf M (g * y * g⁻¹) := mem_conjSubgroup.1 hx
      have hx'' : g * x * g⁻¹ ∈ CMOf M (g * y * g⁻¹) := by simpa using hx'
      have hcomm : (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * y * g⁻¹ :=
        mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hx'').2
      have hxy : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹) * g := by
              group
          _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hcomm]
          _ = y := by group
      have hxM : x ∈ M := hCGy (mem_centralizer_zpowers_iff.2 hxy)
      exact Subgroup.mem_inf.2 ⟨hxM, mem_centralizer_zpowers_iff.2 hxy⟩
    have hcardN' : Nat.card ↥N' = Nat.card ↥(CMOf M (g * y * g⁻¹)) :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hc6 : (2 * n + 1).choose 6 = 7 := by rw [hn]; decide
    have hc2 : (2 * n + 1).choose 2 = 21 := by rw [hn]; decide
    rw [hc6] at hoy
    rw [hc2] at hoz
    have hcardN : Nat.card ↥(CMOf M y) = 3 * Nat.card ↥N' := by
      rw [hcardN']
      omega
    exact S.no_index_three_CMOf hT hR hn hyW hycard hN'le hcardN
  ·
    exfalso
    have hconst' := hconst _ hy'W hy'E
    obtain ⟨i₀, hi₀⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
    by_cases hc : vcoord v'' i₀ = 1
    · have hIsub : I ⊆ vsupp v'' := fun i hi =>
        mem_vsupp.2 ((hconst' i₀ hi₀ i hi).symm.trans hc)
      have heq : I = vsupp v'' := Finset.eq_of_subset_of_card_le hIsub (by omega)
      have hv : v'' = S.D.β ⟨w, hw⟩ := eq_of_vsupp_eq heq.symm
      have hyw' : g * y * g⁻¹ = w := congrArg Subtype.val (S.D.β.injective hv)
      have hgw : g * w * g⁻¹ = w := by
        have := mem_centralizer_zpowers_iff.1 hgK
        simpa [hr1] using this
      have hyw : y = w := by
        have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [e, hyw']
        calc g⁻¹ * w * g = g⁻¹ * (g * w * g⁻¹) * g := by rw [hgw]
          _ = w := by group
      have h1 : S.D.β ⟨y, hyW⟩ = S.D.β ⟨w, hw⟩ := by
        have : (⟨y, hyW⟩ : ↥S.D.W) = ⟨w, hw⟩ := Subtype.ext hyw
        rw [this]
      rw [hβy] at h1
      have h2 : pairVec a b = 1 := by
        have h3 : S.D.β ⟨w, hw⟩ * pairVec a b = S.D.β ⟨w, hw⟩ * 1 := by rw [h1, mul_one]
        exact mul_left_cancel h3
      have h3 := congrArg (fun v => vcoord v a) h2
      simp [vcoord_pairVec, vcoord_one, hab] at h3
    · have hzero : ∀ i ∈ I, vcoord v'' i = 0 := by
        intro i hi
        rw [← hconst' i₀ hi₀ i hi]
        generalize vcoord v'' i₀ = c at hc ⊢
        revert c
        decide
      have hsub : vsupp v'' ⊆ Iᶜ := fun i hi => Finset.mem_compl.2 fun hiI => by
        rw [mem_vsupp, hzero i hiI] at hi
        exact zero_ne_one hi
      have := Finset.card_le_card hsub
      omega
  ·
    exfalso
    have hl'6 : S.HasLen (g * y * g⁻¹) 6 := by
      rw [← h6]
      exact hl'
    exact hgM (S.mem_of_conj_of_len S.hyp.charTwo hT hyQ hy1 hy'Q hy'1 hl6 hl'6 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) rfl)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
