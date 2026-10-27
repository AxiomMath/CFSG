module

public import CFSG.CGT.PushingUpLit.SolK.FourD
public import CFSG.CGT.PushingUpLit.SolK.FourC

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem fourGroup_theta_of_lifts {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) {U : Subgroup G}
    (hUM : U ≤ M) (hUC : U ≤ CMOf M (w * r)) (hU2 : IsPGroup 2 U)
    (hUn : ∀ τ ∈ altOn (vsupp (S.D.β ⟨w, hw⟩)), ∀ (c : G) (hcM : c ∈ M), S.θ ⟨c, hcM⟩ = τ →
      ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    (hfix : ∀ σ ∈ (U.subgroupOf M).map S.θ, ∀ y, y ∉ vsupp (S.D.β ⟨w, hw⟩) → σ y = y) :
    FourGroup (vsupp (S.D.β ⟨w, hw⟩)) ((U.subgroupOf M).map S.θ) where
  two := S.theta_isPGroup hUM hU2
  stab := S.theta_le_setStab hw hr hUC
  fix := hfix
  norm := by
    intro τ hτ σ hσ
    obtain ⟨c, hcM, hcτ⟩ := S.exists_lift_J (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hcm := hUn τ hτ c hcM hcτ m (Subgroup.mem_subgroupOf.1 hm)
    have hcmM : c * (m : G) * c⁻¹ ∈ M :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcM m.2) (M.inv_mem hcM)
    refine Subgroup.mem_map.2 ⟨⟨c * (m : G) * c⁻¹, hcmM⟩, Subgroup.mem_subgroupOf.2 hcm, ?_⟩
    have : (⟨c * (m : G) * c⁻¹, hcmM⟩ : ↥M) = ⟨c, hcM⟩ * m * ⟨c, hcM⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hcτ]

theorem alt_fixes_E (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) (hrbot : rOf M X = ⊥) {e : G}
    (he : e ∈ pCoreOf 2 (CGOf (w * r)) ⊓
      Subgroup.centralizer ((pCoreOf 2 (CGOf (w * r)) : Subgroup G) : Set G))
    {c : G} (hcM : c ∈ M) (hc : S.θ ⟨c, hcM⟩ ∈ altOn (vsupp (S.D.β ⟨w, hw⟩))) :
    c * e * c⁻¹ = e := by
  classical
  have hθP := S.theta_P_eq hT hQe hR hw hr hcard hKM
  have hFT : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hNne := S.TN_ne_bot hT hQe hR hw hr hcard hKM
  have heQ : e ∈ pCoreOf 2 M := S.center_P_le_Q hT hQe hR hw hr hcard hKM he.1
    (fun p hp => Subgroup.mem_centralizer_iff.1 he.2 p hp)
  have heW : e ∈ S.D.W := S.mem_W_of_rOf_bot hrbot heQ
  have hvfix : ∀ σ ∈ S.TN (w * r),
      coreAct (2 * n + 1) σ (S.D.β ⟨e, heW⟩) = S.D.β ⟨e, heW⟩ := by
    intro σ hσ
    rw [← hθP] at hσ
    obtain ⟨pm, hpm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hpP : (pm : G) ∈ pCoreOf 2 (CGOf (w * r)) := Subgroup.mem_subgroupOf.1 hpm
    have hcomm : (pm : G) * e * (pm : G)⁻¹ = e := by
      have h1 := Subgroup.mem_centralizer_iff.1 he.2 _ hpP
      calc (pm : G) * e * (pm : G)⁻¹ = (e * (pm : G)) * (pm : G)⁻¹ := by rw [h1]
        _ = e := by group
    have hW' : (pm : G) * e * (pm : G)⁻¹ ∈ S.D.W := S.W_normalized pm.2 heW
    have h2 := S.θ_spec pm ⟨e, heW⟩ hW'
    have h3 : (⟨(pm : G) * e * (pm : G)⁻¹, hW'⟩ : ↥S.D.W) = ⟨e, heW⟩ := Subtype.ext hcomm
    rw [h3] at h2
    exact h2.symm
  have hτfix : coreAct (2 * n + 1) (S.θ ⟨c, hcM⟩) (S.D.β ⟨e, heW⟩) = S.D.β ⟨e, heW⟩ := by
    refine vcoord_ext fun i => ?_
    rw [vcoord_coreAct]
    by_cases hi : i ∈ vsupp (S.D.β ⟨w, hw⟩)
    · have hτinv : (S.θ ⟨c, hcM⟩)⁻¹ ∈ altOn (vsupp (S.D.β ⟨w, hw⟩)) :=
        Subgroup.inv_mem _ hc
      have hτi : (S.θ ⟨c, hcM⟩)⁻¹ i ∈ vsupp (S.D.β ⟨w, hw⟩) :=
        (mem_setStab.1 (altOn_le_setStab _ hτinv) i).2 hi
      obtain ⟨σ, hσN, hσ⟩ := hFT.transitive hcard hNne hτi hi
      have h1 := congrArg (fun u => vcoord u i) (hvfix σ hσN)
      simp only [vcoord_coreAct] at h1
      have h2 : σ⁻¹ i = (S.θ ⟨c, hcM⟩)⁻¹ i := (Equiv.Perm.inv_eq_iff_eq).2 hσ.symm
      rw [h2] at h1
      exact h1
    · have h1 : S.θ ⟨c, hcM⟩ i = i := (mem_altOn.1 hc).1 i hi
      have : (S.θ ⟨c, hcM⟩)⁻¹ i = i := (Equiv.Perm.inv_eq_iff_eq).2 h1.symm
      rw [this]
  have hW' : c * e * c⁻¹ ∈ S.D.W := S.W_normalized hcM heW
  have h2 := S.θ_spec ⟨c, hcM⟩ ⟨e, heW⟩ hW'
  exact congrArg Subtype.val (S.D.β.injective (h2.trans hτfix))

theorem normalizer_E_le_M (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hn4 : 4 ≤ n) (hKM : ¬ CGOf (w * r) ≤ M) (hrbot : rOf M X = ⊥) :
    Subgroup.normalizer ((pCoreOf 2 (CGOf (w * r)) ⊓
      Subgroup.centralizer ((pCoreOf 2 (CGOf (w * r)) : Subgroup G) : Set G) : Subgroup G) :
        Set G) ≤ M := by
  classical
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
  have hIc : (vsupp (S.D.β ⟨w, hw⟩))ᶜ.card = 2 * n + 1 - 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
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
  have hDE : S.DeltaJ (vsupp (S.D.β ⟨w, hw⟩))ᶜ ≤ E :=
    S.DeltaJ_le_E hT hQe hR hw hr hcard hKM (subset_refl _)
  have hCEM : Subgroup.centralizer (E : Set G) ≤ M := by
    obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (vsupp (S.D.β ⟨w, hw⟩))ᶜ.card by omega)
    have hDJ : S.DeltaJ J ≤ E := (S.DeltaJ_mono hJsub).trans hDE
    have hJc : Jᶜ.card = 2 * n + 1 - 4 := by
      rw [Finset.card_compl, Fintype.card_fin, hJcard]
    exact (Subgroup.centralizer_le (show ((S.DeltaJ J : Subgroup G) : Set G) ⊆ (E : Set G) from
      hDJ)).trans (S.centralizer_DeltaJ_le_M hT hR (J := J) (by omega)
      (Or.inr (Or.inr (by omega)))).1
  have hmemC : ∀ c : G, c ∈ Subgroup.centralizer (E : Set G) → c ∈ CMOf M (w * r) := by
    intro c hc
    refine Subgroup.mem_inf.2 ⟨hCEM hc, mem_centralizer_zpowers_iff.2 ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hc (w * r) hxE
    calc c * (w * r) * c⁻¹ = ((w * r) * c) * c⁻¹ := by rw [h1]
      _ = w * r := by group
  have hnormTE : ∀ g ∈ Subgroup.normalizer (E : Set G),
      ∀ t ∈ pCoreOf 2 (Subgroup.centralizer (E : Set G)),
        g * t * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer (E : Set G)) := fun g hg t ht =>
    pCoreOf_normalized_of_normal (fun n' hn' k hk => centralizer_normalized hn' hk) hg ht
  have hTE : pCoreOf 2 (Subgroup.centralizer (E : Set G)) = TOf M (w * r) := by
    apply le_antisymm
    ·
      set TE : Subgroup G := pCoreOf 2 (Subgroup.centralizer (E : Set G)) with hTEdef
      have hTEC : TE ≤ Subgroup.centralizer (E : Set G) := pCoreOf_le_self _
      have hUM : TE ≤ M := hTEC.trans hCEM
      have hUC : TE ≤ CMOf M (w * r) := fun t ht => hmemC t (hTEC ht)
      have hU2 : IsPGroup 2 ↥TE := isPGroup_pCoreOf' _
      have hUn : ∀ τ ∈ altOn (vsupp (S.D.β ⟨w, hw⟩)), ∀ (c : G) (hcM : c ∈ M),
          S.θ ⟨c, hcM⟩ = τ → ∀ u ∈ TE, c * u * c⁻¹ ∈ TE := by
        intro τ hτ c hcM hcτ u hu
        have hcC : c ∈ Subgroup.centralizer (E : Set G) := by
          refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
          have h1 := S.alt_fixes_E hT hQe hR hw hr hcard hKM hrbot he hcM (by rw [hcτ]; exact hτ)
          calc e * c = (c * e * c⁻¹) * c := by rw [h1]
            _ = c * e := by group
        exact pCoreOf_normalized _ hcC hu
      have hfix : ∀ σ ∈ (TE.subgroupOf M).map S.θ, ∀ y, y ∉ vsupp (S.D.β ⟨w, hw⟩) → σ y = y := by
        intro σ hσ y hy
        obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
        have hmC : (m : G) ∈ Subgroup.centralizer (E : Set G) := hTEC (Subgroup.mem_subgroupOf.1 hm)
        refine S.fix_of_centralizes_DeltaJ (J := (vsupp (S.D.β ⟨w, hw⟩))ᶜ) (by omega) ?_ y
          (Finset.mem_compl.2 hy)
        intro g hg
        have h1 := Subgroup.mem_centralizer_iff.1 hmC g (hDE hg)
        calc (m : G) * g * (m : G)⁻¹ = (g * (m : G)) * (m : G)⁻¹ := by rw [h1]
          _ = g := by group
      have hFE := S.fourGroup_theta_of_lifts hw hr hUM hUC hU2 hUn hfix
      have hTTE : TOf M (w * r) ≤ TE := by
        refine le_pCoreOf_of_normalized ?_
          (fun c hc t ht => normalized_TOf M (w * r) (hmemC c hc) ht) (isPGroup_TOf M _)
        rw [← hsup]
        refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.2 fun e he => ?_)
          (fun q hq => Subgroup.mem_centralizer_iff.2 fun e he => hT.abelian e (hEQ he) q hq)
        exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 he).2 p hp).symm
      have hle : S.TN (w * r) ≤ (TE.subgroupOf M).map S.θ := by
        intro σ hσ
        obtain ⟨t, ht, rfl⟩ := S.mem_TN.1 hσ
        exact Subgroup.mem_map.2 ⟨t, Subgroup.mem_subgroupOf.2 (hTTE ht), rfl⟩
      have hEq := hFE.eq_of_le hcard hle hNne hFT.norm
      intro t ht
      have htM : t ∈ M := hUM ht
      have hσ : S.θ ⟨t, htM⟩ ∈ S.TN (w * r) := by
        rw [hEq]
        exact Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
      obtain ⟨t', ht'T, hθ⟩ := S.mem_TN.1 hσ
      have hM' : t * (t' : G)⁻¹ ∈ M := M.mul_mem htM (M.inv_mem t'.2)
      have hdiv : t * (t' : G)⁻¹ ∈ pCoreOf 2 M := by
        refine S.mem_Q_of_theta_eq_one hR hM' ?_
        have : (⟨t * (t' : G)⁻¹, hM'⟩ : ↥M) = ⟨t, htM⟩ * t'⁻¹ := rfl
        rw [this, map_mul, map_inv, ← hθ, mul_inv_cancel]
      have hQT := S.Q_le_TOf hT hxQ
      have e : t = (t * (t' : G)⁻¹) * t' := by group
      rw [e]
      exact (TOf M (w * r)).mul_mem (hQT hdiv) ht'T
    ·
      refine le_pCoreOf_of_normalized ?_ (fun c hc t ht => normalized_TOf M (w * r) (hmemC c hc) ht)
        (isPGroup_TOf M _)
      rw [← hsup]
      refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.2 fun e he => ?_)
        (fun q hq => Subgroup.mem_centralizer_iff.2 fun e he => hT.abelian e (hEQ he) q hq)
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 he).2 p hp).symm
  intro g hg
  have hgT : g ∈ Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [← hTE]
    refine ⟨fun ht => hnormTE g hg t ht, fun ht => ?_⟩
    have := hnormTE g⁻¹ ((Subgroup.normalizer _).inv_mem hg) _ ht
    simpa [mul_assoc] using this
  exact S.normalizer_TOf_le_M hT hQe hw hr hcard hgT

theorem centralizer_le_M_of_len_four (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hn4 : 4 ≤ n) : CGOf (w * r) ≤ M := by
  by_contra hKM
  have hrbot := S.rOf_eq_bot hT hQe hR hw hr hcard hKM
  apply hKM
  intro k hk
  refine S.normalizer_E_le_M hT hQe hR hw hr hcard hn4 hKM hrbot ?_
  rw [Subgroup.mem_normalizer_iff]
  intro e
  have hP : ∀ k ∈ CGOf (w * r), ∀ p ∈ pCoreOf 2 (CGOf (w * r)),
      k * p * k⁻¹ ∈ pCoreOf 2 (CGOf (w * r)) := fun k hk p hp => pCoreOf_normalized _ hk hp
  refine ⟨fun he => center_conj_mem hP hk he, fun he => ?_⟩
  have := center_conj_mem hP ((CGOf (w * r)).inv_mem hk) he
  simpa [mul_assoc] using this


end SolCfg

end CFSG.CGT.PushingUpLit.SolK
