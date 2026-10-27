module

public import CFSG.GH74.GLS.C3.Layer1.BkW5Api
public import CFSG.GH74.GLS.C3.Layer1.BkP46Cnt
public import CFSG.GH74.GLS.C3.Layer2.L5C11

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.W5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfigW 5 x K T Q S a}

namespace Coord

section Planes

variable (c : Coord h)

open Classical in
@[expose] noncomputable def planeOf
    (V : Subgroup G) : Finset (Fin 16) :=
  Finset.univ.filter fun i => c.liftEl i ∈ V

variable {c}

theorem mem_planeOf
    {V : Subgroup G} {i : Fin 16} : i ∈ c.planeOf V ↔ c.liftEl i ∈ V := by
  classical
  simp only [planeOf, Finset.mem_filter, Finset.mem_univ, true_and]

theorem planeOf_inf
    {V W : Subgroup G} : c.planeOf (V ⊓ W) = c.planeOf V ∩ c.planeOf W := by
  ext i
  simp only [mem_planeOf, Finset.mem_inter, Subgroup.mem_inf]

theorem planeOf_bot :
    c.planeOf (⊥ : Subgroup G) = {0} := by
  ext i
  rw [mem_planeOf, Subgroup.mem_bot, Finset.mem_singleton]
  constructor
  · intro hi
    exact liftEl_inj c (hi.trans (liftEl_zero c).symm)
  · rintro rfl
    exact liftEl_zero c

theorem planeOf_inj
    {V W : Subgroup G} (hV : V ≤ c.lift Rm) (hW : W ≤ c.lift Rm)
    (hVW : c.planeOf V = c.planeOf W) : V = W := by
  apply le_antisymm
  · intro g hg
    have hgR := hV hg
    have hj : idx16 (c.rco g) ∈ c.planeOf V := by
      rw [mem_planeOf, ← exists_liftEl c hgR]; exact hg
    rw [hVW, mem_planeOf, ← exists_liftEl c hgR] at hj
    exact hj
  · intro g hg
    have hgR := hW hg
    have hj : idx16 (c.rco g) ∈ c.planeOf W := by
      rw [mem_planeOf, ← exists_liftEl c hgR]; exact hg
    rw [← hVW, mem_planeOf, ← exists_liftEl c hgR] at hj
    exact hj

theorem planeOf_cj
    {n : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    {V : Subgroup G} (hV : V ≤ c.lift Rm) :
    c.planeOf (cj n V) = (c.planeOf V).image (c.rhoG ⟨n, hn⟩) := by
  ext i
  rw [mem_planeOf, Finset.mem_image]
  constructor
  · intro hi
    obtain ⟨z, hz, hzi⟩ := mem_cj.1 hi
    have hzj := exists_liftEl c (hV hz)
    refine ⟨idx16 (c.rco z), ?_, ?_⟩
    · rw [mem_planeOf, ← hzj]; exact hz
    · apply liftEl_inj c
      rw [rhoG_spec, ← hzj]
      exact hzi
  · rintro ⟨j, hj, rfl⟩
    rw [rhoG_spec]
    exact mem_cj_self ((mem_planeOf).1 hj)

theorem planeOf_Q :
    c.planeOf Q = QplG := by
  ext i
  rw [mem_planeOf, SetLike.ext_iff.1 (Q_eq_lift (c := c)) (c.liftEl i),
    mem_lift_rco, c.rco_liftEl]
  constructor
  · rintro ⟨_, hi⟩
    exact (el16_Qm_iff i).1 hi
  · intro hi
    exact ⟨c.liftEl_mem_T i, (el16_Qm_iff i).2 hi⟩

theorem planeOf_P :
    c.planeOf (T ⊓ K) = PplG := by
  ext i
  rw [mem_planeOf, SetLike.ext_iff.1 (P_eq_lift (c := c)) (c.liftEl i),
    mem_lift_rco, c.rco_liftEl]
  constructor
  · rintro ⟨_, hi⟩
    exact (el16_Pm_iff i).1 hi
  · intro hi
    exact ⟨c.liftEl_mem_T i, (el16_Pm_iff i).2 hi⟩

end Planes

theorem Q_le_R {c : Coord h} :
    Q ≤ c.lift Rm :=
  (Q_eq_lift (c := c)).le.trans (lift_mono Qm_le_Rm)

end Coord

omit [Finite G] in
theorem FamQ_eq_NRConj (R Q : Subgroup G) : FamQ R Q = NRConj R Q := by
  ext V
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g⁻¹, (normalizer _).inv_mem hg, ?_⟩
    rw [Stage1.Thm2.Recip.conjugate_eq_cj, inv_inv]
    rfl
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g⁻¹, (normalizer _).inv_mem hg, ?_⟩
    rw [Stage1.Thm2.Recip.conjugate_eq_cj]
    rfl

namespace Coord

theorem rco_ne_one (c : Coord h) {g : G} (hg : g ∈ T) (hg1 : g ≠ 1) : c.rco g ≠ 1 := by
  intro h1
  exact hg1 (rco_inj c hg T.one_mem (h1.trans (rco_one c).symm))

theorem fam_TI {c : Coord h}
    {V₁ V₂ : Subgroup G} (h₁ : V₁ ∈ FamQ (c.lift Rm) Q) (h₂ : V₂ ∈ FamQ (c.lift Rm) Q)
    (hne : V₁ ≠ V₂) : V₁ ⊓ V₂ = ⊥ := by
  rw [← R_eq_lift (c := c), FamQ_eq_NRConj] at h₁ h₂
  obtain ⟨g₁, hg₁, rfl⟩ := h₁
  obtain ⟨g₂, hg₂, rfl⟩ := h₂
  by_contra hbot
  exact hne (aconfigW_five_TI' h hg₁ hg₂ hbot)

theorem fam_planeOf_inj
    {c : Coord h} {V W : Subgroup G} (hV : V ∈ FamQ (c.lift Rm) Q)
    (hW : W ∈ FamQ (c.lift Rm) Q) (hVW : c.planeOf V = c.planeOf W) : V = W :=
  planeOf_inj (fam_le_R Q_le_R hV) (fam_le_R Q_le_R hW) hVW

theorem exists_famFinset
    (c : Coord h) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ F : Finset (Finset (Fin 16)), F.card = 4 ∧
      ∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V := by
  classical
  have hfin : (FamQ (c.lift Rm) Q).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have himg : (c.planeOf '' FamQ (c.lift Rm) Q).Finite := hfin.image _
  refine ⟨himg.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ himg, Set.InjOn.ncard_image, hncard]
    intro V hV W hW hVW
    exact fam_planeOf_inj hV hW hVW
  · intro V
    rw [Set.Finite.mem_toFinset, Set.mem_image]

theorem fam_stable
    {c : Coord h} {F : Finset (Finset (Fin 16))}
    (hF : ∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V) {n : G}
    (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G)) :
    ∀ V ∈ F, V.image (c.rhoG ⟨n, hn⟩) ∈ F := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := (hF V).1 hV
  rw [← planeOf_cj hn (fam_le_R Q_le_R hW)]
  exact (hF _).2 ⟨cj n W, fam_cj hn hW, rfl⟩

theorem exists_move
    (c : Coord h) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ n : G, n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) ∧ cj n Q ≠ Q := by
  by_contra hcon
  have hsub : FamQ (c.lift Rm) Q ⊆ {Q} := by
    rintro V ⟨g, hg, rfl⟩
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  have := Set.ncard_le_ncard hsub (Set.finite_singleton Q)
  rw [Set.ncard_singleton, hncard] at this
  omega

theorem fam_w_fixed
    (c : Coord h) {V : Subgroup G}
    (hV : V ∈ FamQ (c.lift Rm) Q) (hw : cj (c.wC : G) V = V) : V = T ⊓ K ∨ V = Q := by
  have hVR : V ≤ c.lift Rm := fam_le_R Q_le_R hV
  have hV4 : Nat.card V = 4 := by rw [card_fam hV, h.card_Q]
  have hsq : ∀ z ∈ V, z * z = 1 := fun z hz =>
    lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) (hVR hz)
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ := exists_klein_basis hV4
  have hbasis := klein_elems hV4 hsq hu hv hu1 hv1 huv
  have huT : u ∈ T := (hVR hu).1
  have hvT : v ∈ T := (hVR hv).1
  have huC := lift_mem_cent (hVR hu)
  have hvC := lift_mem_cent (hVR hv)
  have hw' : ∀ z ∈ V, (c.wC : G) * z * (c.wC : G)⁻¹ ∈ V := fun z hz => hw ▸ mem_cj_self hz
  have hcoord : ∀ z ∈ V, z ≠ 1 → c.rco z = c.rco u ∨ c.rco z = c.rco v ∨
      c.rco z = c.rco u * c.rco v := by
    intro z hz hz1
    rcases hbasis z hz with h1 | h1 | h1 | h1
    · exact absurd h1 hz1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inr (Or.inr (by rw [h1, rco_mul c huC hvC]))
  have hwconj : ∀ z ∈ V, z ≠ 1 → wm * c.rco z * wm⁻¹ ∈ [c.rco u, c.rco v, c.rco u * c.rco v] := by
    intro z hz hz1
    have hzC := lift_mem_cent (hVR hz)
    have h1 : (c.wC : G) * z * (c.wC : G)⁻¹ ≠ 1 := by
      intro h2
      apply hz1
      have : z = (c.wC : G)⁻¹ * ((c.wC : G) * z * (c.wC : G)⁻¹) * (c.wC : G) := by group
      rw [this, h2]
      group
    rw [← rco_conj_w c hzC]
    have := hcoord _ (hw' z hz) h1
    simpa using this
  have hu'1 := rco_ne_one c huT hu1
  have hv'1 := rco_ne_one c hvT hv1
  have huv' : c.rco u ≠ c.rco v := fun h1 => huv (rco_inj c huT hvT h1)
  have hFIN := FIN1 (rco_mem c (hVR hu)) (rco_mem c (hVR hv)) hu'1 hv'1 huv'
    (hwconj u hu hu1) (hwconj v hv hv1)
  rcases hFIN with ⟨hup, hvp⟩ | ⟨huq, hvq⟩
  · left
    have hu' : u ∈ T ⊓ K := (SetLike.ext_iff.1 (P_eq_lift (c := c)) u).2
      ((mem_lift_rco c).2 ⟨huT, hup⟩)
    have hv' : v ∈ T ⊓ K := (SetLike.ext_iff.1 (P_eq_lift (c := c)) v).2
      ((mem_lift_rco c).2 ⟨hvT, hvp⟩)
    have hle : V ≤ T ⊓ K := by
      intro z hz
      rcases hbasis z hz with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hu'
      · exact hv'
      · exact mul_mem hu' hv'
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hV4, P_eq_lift (c := c)]
    exact (card_lift_Pm (c := c)).le
  · right
    have hu' : u ∈ Q := (SetLike.ext_iff.1 (Q_eq_lift (c := c)) u).2
      ((mem_lift_rco c).2 ⟨huT, huq⟩)
    have hv' : v ∈ Q := (SetLike.ext_iff.1 (Q_eq_lift (c := c)) v).2
      ((mem_lift_rco c).2 ⟨hvT, hvq⟩)
    have hle : V ≤ Q := by
      intro z hz
      rcases hbasis z hz with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hu'
      · exact hv'
      · exact mul_mem hu' hv'
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hV4, h.card_Q])

theorem fam_meet_P
    (c : Coord h)
    {V : Subgroup G} (hV : V ∈ FamQ (c.lift Rm) Q) (hVQ : V ≠ Q)
    (hw : cj (c.wC : G) V ≠ V) : V ⊓ (T ⊓ K) = ⊥ := by
  by_contra hne
  have hVQ' : V ⊓ Q = ⊥ := fam_TI hV Q_mem_fam hVQ
  have hVR : V ≤ c.lift Rm := fam_le_R Q_le_R hV
  have hV4 : Nat.card V = 4 := by rw [card_fam hV, h.card_Q]
  have hsq : ∀ z ∈ V, z * z = 1 := fun z hz =>
    lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) (hVR hz)
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ := exists_klein_basis hV4
  have hbasis := klein_elems hV4 hsq hu hv hu1 hv1 huv
  have huT : u ∈ T := (hVR hu).1
  have hvT : v ∈ T := (hVR hv).1
  have huC := lift_mem_cent (hVR hu)
  have hvC := lift_mem_cent (hVR hv)
  have huvC : u * v ∈ centralizer ({x} : Set G) := mul_mem huC hvC
  have huvT : u * v ∈ T := T.mul_mem huT hvT
  have hu'R := rco_mem c (hVR hu)
  have hv'R := rco_mem c (hVR hv)
  have hu'1 := rco_ne_one c huT hu1
  have hv'1 := rco_ne_one c hvT hv1
  have huv' : c.rco u ≠ c.rco v := fun h1 => huv (rco_inj c huT hvT h1)
  have hnotQ : ∀ z ∈ V, z ≠ 1 → c.rco z ∉ Qm := by
    intro z hz hz1 hzQ
    have hzT : z ∈ T := (hVR hz).1
    have hzQ' : z ∈ Q := (SetLike.ext_iff.1 (Q_eq_lift (c := c)) z).2
      ((mem_lift_rco c).2 ⟨hzT, hzQ⟩)
    have : z ∈ V ⊓ Q := ⟨hz, hzQ'⟩
    rw [hVQ'] at this
    exact hz1 (Subgroup.mem_bot.1 this)
  have hQ : c.rco u ∉ Qm ∧ c.rco v ∉ Qm ∧ c.rco u * c.rco v ∉ Qm := by
    refine ⟨hnotQ u hu hu1, hnotQ v hv hv1, ?_⟩
    have := hnotQ (u * v) (mul_mem hu hv) (by
      intro h1
      apply huv
      have : v = u⁻¹ * (u * v) := by group
      rw [this, h1, mul_one]
      exact (inv_eq_of_mul_eq_one_right (hsq u hu)).symm)
    rwa [rco_mul c huC hvC] at this
  have hP : c.rco u ∈ Pm ∨ c.rco v ∈ Pm ∨ c.rco u * c.rco v ∈ Pm := by
    obtain ⟨z, hzmem⟩ : ∃ z, z ∈ V ⊓ (T ⊓ K) ∧ z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [eq_bot_iff]
      intro z hz
      exact Subgroup.mem_bot.2 (hcon z hz)
    obtain ⟨⟨hzV, hzP⟩, hz1⟩ := hzmem
    have hzP' : z ∈ c.lift Pm := (SetLike.ext_iff.1 (P_eq_lift (c := c)) z).1 hzP
    have hzm := rco_mem c hzP'
    rcases hbasis z hzV with h1 | h1 | h1 | h1
    · exact absurd h1 hz1
    · exact Or.inl (h1 ▸ hzm)
    · exact Or.inr (Or.inl (h1 ▸ hzm))
    · refine Or.inr (Or.inr ?_)
      rw [← rco_mul c huC hvC, ← h1]
      exact hzm
  have hF := FIN2 hu'R hv'R hu'1 hv'1 huv' hQ hP
  have hwV : ∃ s ∈ V, s ≠ 1 ∧ (c.wC : G) * s * (c.wC : G)⁻¹ ∈ V := by
    have hconv : ∀ s ∈ V, wm * c.rco s * wm⁻¹ ∈ [c.rco u, c.rco v, c.rco u * c.rco v] →
        (c.wC : G) * s * (c.wC : G)⁻¹ ∈ V := by
      intro s hs hmem
      have hsC := lift_mem_cent (hVR hs)
      have hwC : (c.wC : G) ∈ centralizer ({x} : Set G) := c.wC.2
      have hcon : (c.wC : G) * s * (c.wC : G)⁻¹ ∈ centralizer ({x} : Set G) :=
        mul_mem (mul_mem hwC hsC) (inv_mem hwC)
      have hwRs : (c.wC : G) * s * (c.wC : G)⁻¹ ∈ c.lift Rm :=
        (mem_normalizer_iff.1 (w_mem_N (c := c)) s).1 (hVR hs)
      have hconT : (c.wC : G) * s * (c.wC : G)⁻¹ ∈ T := hwRs.1
      rw [← rco_conj_w c hsC] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1 | h1
      · rwa [rco_inj c hconT huT h1]
      · rwa [rco_inj c hconT hvT h1]
      · rw [← rco_mul c huC hvC] at h1
        rw [rco_inj c hconT huvT h1]
        exact V.mul_mem hu hv
    rcases hF with h1 | h1 | h1
    · exact ⟨u, hu, hu1, hconv u hu h1⟩
    · exact ⟨v, hv, hv1, hconv v hv h1⟩
    · refine ⟨u * v, mul_mem hu hv, ?_, ?_⟩
      · intro h2
        apply huv
        have : v = u⁻¹ * (u * v) := by group
        rw [this, h2, mul_one]
        exact (inv_eq_of_mul_eq_one_right (hsq u hu)).symm
      · apply hconv _ (mul_mem hu hv)
        rwa [rco_mul c huC hvC]
  obtain ⟨s, hsV, hs1, hws⟩ := hwV
  have hTI := fam_TI (fam_cj (w_mem_N (c := c)) hV) hV hw
  have : (c.wC : G) * s * (c.wC : G)⁻¹ ∈ cj (c.wC : G) V ⊓ V := ⟨mem_cj_self hsV, hws⟩
  rw [hTI] at this
  have h2 := Subgroup.mem_bot.1 this
  apply hs1
  have : s = (c.wC : G)⁻¹ * ((c.wC : G) * s * (c.wC : G)⁻¹) * (c.wC : G) := by group
  rw [this, h2]
  group

end Coord

namespace Coord

theorem cj_w_Q (c : Coord h) :
    cj (c.wC : G) Q = Q := by
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_cj])
  obtain ⟨z, hz, rfl⟩ := mem_cj.1 hy
  have : (c.wC : G) * z * (c.wC : G)⁻¹ = z := by
    rw [wG_cent_Q' z hz, mul_inv_cancel_right]
  rw [this]
  exact hz

theorem fam_shadow (c : Coord h)
    (hnP : ∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q g ≠ T ⊓ K) :
    (∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) ∧ (FamQ (c.lift Rm) Q).ncard = 4 := by
  classical
  have hwN : (c.wC : G) ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := w_mem_N (c := c)
  have hcjwQ := cj_w_Q c
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  have hP : T ⊓ K ∉ FamQ (c.lift Rm) Q := by
    intro hPF
    rw [← R_eq_lift (c := c), FamQ_eq_NRConj] at hPF
    obtain ⟨g, hg, hgP⟩ := hPF
    exact hnP g hg hgP.symm
  have hQfix : ∀ V : Subgroup G, cj (c.wC : G) V = Q → V = Q := fun V hV => by
    have h1 : cj (c.wC : G) V = cj (c.wC : G) Q := by rw [hV, hcjwQ]
    exact cj_inj h1
  have hPQ : (T ⊓ K) ⊓ Q = ⊥ := (aconfigW_five_commDisj h).inf
  refine ⟨?_, ?_⟩
  · intro V hV
    by_cases hVQ : V = Q
    · rw [hVQ, inf_comm]
      exact hPQ
    · have hfix : cj (c.wC : G) V ≠ V := by
        intro hfix
        rcases fam_w_fixed c hV hfix with h1 | h1
        · exact hP (h1 ▸ hV)
        · exact hVQ h1
      exact fam_meet_P c hV hVQ hfix
  · have hFfin : (FamQ (c.lift Rm) Q).Finite := Set.toFinite _
    have hset : FamQ (c.lift Rm) Q = NRConj ((T ⊓ K) ⊔ Q) Q := by
      rw [FamQ_eq_NRConj, ← R_eq_lift (c := c)]
    have hcardN : (FamQ (c.lift Rm) Q).ncard = Nat.card ↥(NRConj ((T ⊓ K) ⊔ Q) Q) := by
      rw [hset, Nat.card_coe_set_eq]
    have hle5 : (FamQ (c.lift Rm) Q).ncard ≤ 5 := by
      rw [hcardN]
      refine card_le_five_of_disjoint hRcard (fun Q' hQ' => (NRConj_le h hQ').1)
        (fun Q' hQ' => (NRConj_le h hQ').2) (fun Q₁ h₁ Q₂ h₂ hne => ?_)
      by_contra hbot
      obtain ⟨g₁, hg₁, rfl⟩ := h₁
      obtain ⟨g₂, hg₂, rfl⟩ := h₂
      exact hne (aconfigW_five_TI' h hg₁ hg₂ hbot)
    have heven : Even (FamQ (c.lift Rm) Q).ncard := by
      rw [hcardN]
      exact aconfigW_five_NRConj_even h
    have haN : a ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
      rw [← R_eq_lift (c := c)]
      exact aconfigW_five_a_mem_normalizer h
    have hV₀F : cj a Q ∈ FamQ (c.lift Rm) Q := ⟨a, haN, rfl⟩
    have hV₀Q : cj a Q ≠ Q := by
      intro heq
      have h1 : conjugate Q a = Q := by
        rw [Stage1.Thm2.Recip.conjugate_eq_cj]
        show cj a⁻¹ Q = Q
        calc cj a⁻¹ Q = cj a⁻¹ (cj a Q) := by rw [heq]
          _ = Q := cj_inv_cj a Q
      have h2 := aconfigW_Q_inf_conj h
      rw [h1, inf_idem] at h2
      have := h.card_Q
      rw [h2, Subgroup.card_bot] at this
      omega
    have hsub2 : ({Q, cj a Q} : Set (Subgroup G)) ⊆ FamQ (c.lift Rm) Q := by
      intro U hU
      rcases hU with rfl | hU
      · exact Q_mem_fam
      · rw [Set.mem_singleton_iff.1 hU]
        exact hV₀F
    have h2 : 2 ≤ (FamQ (c.lift Rm) Q).ncard := by
      have := Set.ncard_le_ncard hsub2 hFfin
      rwa [Set.ncard_pair hV₀Q.symm] at this
    have hne2 : (FamQ (c.lift Rm) Q).ncard ≠ 2 := by
      intro h22
      have heq : ({Q, cj a Q} : Set (Subgroup G)) = FamQ (c.lift Rm) Q :=
        Set.eq_of_subset_of_ncard_le hsub2 (by rw [h22, Set.ncard_pair hV₀Q.symm]) hFfin
      have hw₀ : cj (c.wC : G) (cj a Q) ∈ ({Q, cj a Q} : Set (Subgroup G)) := by
        rw [heq]
        exact fam_cj hwN hV₀F
      rcases hw₀ with h1 | h1
      · exact hV₀Q (hQfix _ h1)
      · rw [Set.mem_singleton_iff] at h1
        rcases fam_w_fixed c hV₀F h1 with h3 | h3
        · exact hP (h3 ▸ hV₀F)
        · exact hV₀Q h3
    obtain ⟨k, hk⟩ := heven
    omega

end Coord

namespace Coord

theorem exists_nbar
    (hF : C1Facts) (c : Coord h)
    (hP : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ F : Finset (Finset (Fin 16)), F.card = 4 ∧ (F = fam0G ∨ F = fam1G) ∧
      (∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V) ∧
      (∀ n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)), PplG.image (c.rhoG n) = PplG) ∧
      (F = fam0G → ∀ A ∈ n24L,
        ∃ n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)), c.rhoG n = A) ∧
      (F = fam1G → ∀ A ∈ n24L,
        ∃ n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)), c.rhoG n = twG * A * twG⁻¹) := by
  obtain ⟨F, hFcard, hFmem⟩ := exists_famFinset c hncard
  obtain ⟨n, hn, hnQ⟩ := exists_move c hncard
  have hQR : Q ≤ c.lift Rm := Q_le_R (c := c)
  have hQF : QplG ∈ F := by
    refine (hFmem _).2 ⟨Q, Q_mem_fam, ?_⟩
    exact planeOf_Q
  obtain ⟨yG, hyT, hy⟩ := exists_T_rco c yy5_mem
  have hyN : yG ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := T_le_N c hyT
  have hρy : c.rhoG ⟨yG, hyN⟩ = yHat := Equiv.ext fun i => by
    rw [rhoG_T c hyT, hy, actF_yy5]
  have hwN := w_mem_N (c := c)
  have hρw : c.rhoG ⟨(c.wC : G), hwN⟩ = wHat := Equiv.ext fun i => rhoG_wC c i
  set m := c.rhoG ⟨n, hn⟩ with hm
  have hlin : IsLinG m := fun i j => rhoG_xor c ⟨n, hn⟩ i j
  have hcjF : cj n Q ∈ FamQ (c.lift Rm) Q := ⟨n, hn, rfl⟩
  have hcjR : cj n Q ≤ c.lift Rm := fam_le_R hQR hcjF
  have hplane : c.planeOf (cj n Q) = QplG.image m := by
    rw [planeOf_cj hn hQR, planeOf_Q]
  have hmQ : QplG.image m ≠ QplG := by
    intro heq
    apply hnQ
    apply planeOf_inj hcjR hQR
    rw [hplane, heq, planeOf_Q]
  have hTIQ : QplG.image m ∩ QplG = {0} := by
    have := fam_TI hcjF Q_mem_fam hnQ
    rw [← hplane, ← planeOf_Q (c := c), ← planeOf_inf, this, planeOf_bot]
  have hTIP : QplG.image m ∩ PplG = {0} := by
    have := hP _ hcjF
    rw [← hplane, ← planeOf_P (c := c), ← planeOf_inf, this, planeOf_bot]
  have hstab : ∀ V ∈ F, V.image yHat ∈ F ∧ V.image wHat ∈ F ∧ V.image m ∈ F := by
    intro V hV
    refine ⟨?_, ?_, fam_stable hFmem hn V hV⟩
    · have := fam_stable hFmem hyN V hV
      rwa [hρy] at this
    · have := fam_stable hFmem hwN V hV
      rwa [hρw] at this
  obtain ⟨_, hdis⟩ := hF.gen m hlin hmQ hTIQ hTIP F hFcard.le hQF hstab
  have hFfam : F = fam0G ∨ F = fam1G := hdis.elim (fun h0 => Or.inl h0.1) (fun h1 => Or.inr h1.1)
  have hle : Subgroup.closure ({yHat, wHat, m} : Set (Perm (Fin 16))) ≤ (c.rhoG).range := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨⟨yG, hyN⟩, hρy⟩
    · exact ⟨⟨(c.wC : G), hwN⟩, hρw⟩
    · exact ⟨⟨n, hn⟩, rfl⟩
  refine ⟨F, hFcard, hFfam, hFmem, ?_, ?_, ?_⟩
  · intro n'
    have hlin' : IsLinG (c.rhoG n') := fun i j => rhoG_xor c n' i j
    have hst := fam_stable hFmem n'.2
    rcases hFfam with hf | hf
    · exact hF.presP _ hlin' (Or.inl (by rw [← hf]; exact hst))
    · exact hF.presP _ hlin' (Or.inr (by rw [← hf]; exact hst))
  · intro hf A hA
    rcases hdis with ⟨h0, hcl⟩ | ⟨h1, _⟩
    · obtain ⟨n', hn'⟩ := hle (hcl A hA)
      exact ⟨n', hn'⟩
    · exact absurd (h1.symm.trans hf) (by decide)
  · intro hf A hA
    rcases hdis with ⟨h0, _⟩ | ⟨h1, hcl⟩
    · exact absurd (h0.symm.trans hf) (by decide)
    · obtain ⟨n', hn'⟩ := hle (hcl A hA)
      exact ⟨n', hn'⟩

@[expose] noncomputable def twist (c : Coord h) : Coord h where
  co := (conjF5 : ↥(Fgrp 5) ≃* ↥(Fgrp 5)).toMonoidHom.comp c.co
  co_surj := conjF5.surjective.comp c.co_surj
  co_ker := fun g => by
    show conjF5 (c.co g) = 1 ↔ g ∈ Wc x
    rw [map_eq_one_iff conjF5 conjF5.injective]
    exact c.co_ker g
  hι1 := by
    show gTw * (((c.co (xC x) : Fgrp 5) : Amb 5)) * gTw⁻¹ = x0 5
    rw [c.hι1, gTw_x0]
  hιQ := fun g => by
    show (gTw * ((c.co g : Fgrp 5) : Amb 5) * gTw⁻¹).1 = 1 ↔ (g : G) ∈ CxK x K
    rw [gTw_fst]
    exact c.hιQ g
  hιT := fun g hg => by
    show gTw * ((c.co g : Fgrp 5) : Amb 5) * gTw⁻¹ ∈ T5
    rw [gTw_conj_T5_iff]
    exact c.hιT g hg

theorem rco_twist (c : Coord h) (g : G) :
    c.twist.rco g = gTw * c.rco g * gTw⁻¹ := by
  by_cases hg : g ∈ centralizer ({x} : Set G)
  · rw [rco_of_mem c.twist hg, rco_of_mem c hg]
    rfl
  · rw [rco_of_not_mem c.twist hg, rco_of_not_mem c hg]
    group

theorem lift_twist_of (c : Coord h) {M : Subgroup (Amb 5)}
    (hM : ∀ p, gTw * p * gTw⁻¹ ∈ M ↔ p ∈ M) : c.twist.lift M = c.lift M := by
  ext g
  rw [mem_lift_rco c.twist, mem_lift_rco c, rco_twist, hM]

theorem lift_twist_Rm (c : Coord h) :
    c.twist.lift Rm = c.lift Rm :=
  lift_twist_of c gTw_conj_Rm_iff

theorem eq_liftEl
    (c : Coord h) {g : G} (hg : g ∈ c.lift Rm) {i : Fin 16}
    (hrc : c.rco g = el16 i) : g = c.liftEl i :=
  rco_inj c hg.1 (c.liftEl_mem_T i) (hrc.trans (c.rco_liftEl i).symm)

theorem liftEl_twist
    (c : Coord h) (i : Fin 16) :
    c.twist.liftEl i = c.liftEl (twG i) := by
  symm
  have hR : c.liftEl (twG i) ∈ c.twist.lift Rm := by
    rw [lift_twist_Rm]; exact c.liftEl_mem _
  exact eq_liftEl c.twist hR (by
    rw [rco_twist, c.rco_liftEl, gTw_el16])

theorem planeOf_twist
    (c : Coord h) (V : Subgroup G) :
    c.twist.planeOf V = (c.planeOf V).image twG := by
  ext i
  rw [mem_planeOf, Finset.mem_image, liftEl_twist]
  constructor
  · intro hi
    exact ⟨twG i, mem_planeOf.2 hi, twG_twG i⟩
  · rintro ⟨j, hj, rfl⟩
    rw [twG_twG]
    exact mem_planeOf.1 hj

theorem exists_nbar0
    (hF : C1Facts) (c : Coord h)
    (hP : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ c' : Coord h, c'.lift Rm = c.lift Rm ∧ ∃ F : Finset (Finset (Fin 16)), F.card = 4 ∧
      F = fam0G ∧ (∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c'.lift Rm) Q, c'.planeOf W = V) ∧
      (∀ n : ↥(normalizer ((c'.lift Rm : Subgroup G) : Set G)), PplG.image (c'.rhoG n) = PplG) ∧
      (∀ A ∈ n24L, ∃ n : ↥(normalizer ((c'.lift Rm : Subgroup G) : Set G)), c'.rhoG n = A) := by
  obtain ⟨F, hFcard, hFfam, hFmem, hFP, hF0, hF1⟩ := exists_nbar hF c hP hncard
  rcases hFfam with hf | hf
  · exact ⟨c, rfl, F, hFcard, hf, hFmem, hFP, hF0 hf⟩
  ·
    have hTR : c.twist.lift Rm = c.lift Rm := lift_twist_Rm c
    have hP' : ∀ V ∈ FamQ (c.twist.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥ := by
      rw [hTR]; exact hP
    have hn' : (FamQ (c.twist.lift Rm) Q).ncard = 4 := by rw [hTR]; exact hncard
    obtain ⟨F', hF'card, hF'fam, hF'mem, hF'P, hF'0, hF'1⟩ :=
      exists_nbar hF c.twist hP' hn'
    have hFF' : F' = F.image (fun V => V.image twG) := by
      ext V
      rw [hF'mem, Finset.mem_image]
      constructor
      · rintro ⟨W, hW, rfl⟩
        refine ⟨c.planeOf W, (hFmem _).2 ⟨W, ?_, rfl⟩, ?_⟩
        · rwa [hTR] at hW
        · rw [planeOf_twist]
      · rintro ⟨U, hU, rfl⟩
        obtain ⟨W, hW, rfl⟩ := (hFmem U).1 hU
        refine ⟨W, ?_, planeOf_twist c W⟩
        rwa [hTR]
    have hF'eq : F' = fam0G := by
      rw [hFF', hf, fam1G_image_tw]
    exact ⟨c.twist, hTR, F', hF'card, hF'eq, hF'mem, hF'P, hF'0 hF'eq⟩

abbrev N (c : Coord h) : Subgroup G :=
  normalizer ((c.lift Rm : Subgroup G) : Set G)

structure Red
    (c : Coord h) : Prop where
  fam : ∀ V, V ∈ fam0G ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V
  pres : ∀ n : ↥c.N, PplG.image (c.rhoG n) = PplG
  nbar : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A

theorem exists_red
    (hF : C1Facts) (c : Coord h)
    (hP : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ c' : Coord h, c'.Red := by
  obtain ⟨c', -, F, -, hF0, hmem, hpres, hnbar⟩ := exists_nbar0 hF c hP hncard
  subst hF0
  exact ⟨c', ⟨hmem, hpres, hnbar⟩⟩

theorem rho_stable
    {c : Coord h} (hRed : c.Red) (n : ↥c.N) :
    IsLinG (c.rhoG n) ∧ ∀ V ∈ fam0G, V.image (c.rhoG n) ∈ fam0G :=
  ⟨fun i j => rhoG_xor c n i j, fun V hV => fam_stable hRed.fam n.2 V hV⟩

end Coord

end CFSG.GH74.GLS.C3.Layer1.Bk.W5
