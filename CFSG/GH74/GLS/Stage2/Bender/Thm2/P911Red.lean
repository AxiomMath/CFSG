module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Lift
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911H2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.PerfectAutomorphisms

section Assembly

variable {N : Type} [Group N]

theorem layer_ne_bot_of_isComponent {J : Subgroup N} (hJ : IsComponent J) : layer ↥J ≠ ⊥ := by
  intro h
  have hq : IsQuasisimple ↥(⊤ : Subgroup ↥J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hJ.1
  have hc : IsComponent (⊤ : Subgroup ↥J) := ⟨hq, Subgroup.IsSubnormal.top⟩
  have hle : (⊤ : Subgroup ↥J) ≤ layer ↥J := le_sSup hc
  rw [h] at hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥J)
  exact ha (Subgroup.mem_bot.mp (hle (Subgroup.mem_top a)))

theorem not_le_centralizer_of_layer_eq_bot {J : Subgroup N} (hJ : IsComponent J) {v : N}
    (h : layer ↥(J ⊓ centralizer ({v} : Set N)) = ⊥) : ¬ J ≤ centralizer ({v} : Set N) := by
  intro hle
  rw [inf_eq_left.mpr hle] at h
  exact layer_ne_bot_of_isComponent hJ h


theorem actCenterQuot_of_mem {J : Subgroup N} {x : N} (hx : x ∈ J) :
    actCenterQuot J ⟨x, Subgroup.le_normalizer hx⟩ =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨x, hx⟩) := by
  ext y
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y
  change onCenterQuotient (J.normalizerMonoidHom ⟨x, Subgroup.le_normalizer hx⟩)
    (QuotientGroup.mk' (Subgroup.center ↥J) d) = _
  rw [onCenterQuotient_apply_mk]
  simp only [MulAut.conj_apply, ← map_mul, ← map_inv]
  congr 1

theorem map_J_eq_range_conj (J : Subgroup N) :
    (J.subgroupOf (normalizer (J : Set N))).map (actCenterQuot J) =
      (MulAut.conj : (↥J ⧸ Subgroup.center ↥J) →* MulAut (↥J ⧸ Subgroup.center ↥J)).range := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : N) ∈ J := Subgroup.mem_subgroupOf.mp hx
    have : x = ⟨(x : N), Subgroup.le_normalizer hx'⟩ := rfl
    rw [this, actCenterQuot_of_mem hx']
    exact ⟨_, rfl⟩
  · rintro ⟨y', rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y'
    refine ⟨⟨(a : N), Subgroup.le_normalizer a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, ?_⟩
    exact actCenterQuot_of_mem a.2

theorem zpowers_subgroupOf {K : Subgroup N} {z : N} (hz : z ∈ K) :
    (Subgroup.zpowers z).subgroupOf K = Subgroup.zpowers (⟨z, hz⟩ : ↥K) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem hbar_eq {J V : Subgroup N} {z : N} (hVn : V ≤ normalizer (J : Set N))
    (hzn : z ∈ normalizer (J : Set N)) :
    hbar (↥J ⧸ Subgroup.center ↥J) ((V.subgroupOf (normalizer (J : Set N))).map (actCenterQuot J))
        (actCenterQuot J ⟨z, hzn⟩) =
      ((J ⊔ V ⊔ Subgroup.zpowers z).subgroupOf (normalizer (J : Set N))).map (actCenterQuot J) := by
  have hJn : J ≤ normalizer (J : Set N) := fun x hx => Subgroup.le_normalizer hx
  have hzp : Subgroup.zpowers z ≤ normalizer (J : Set N) := (Subgroup.zpowers_le).mpr hzn
  rw [Subgroup.subgroupOf_sup (sup_le hJn hVn) hzp, Subgroup.subgroupOf_sup hJn hVn,
    zpowers_subgroupOf hzn, Subgroup.map_sup, Subgroup.map_sup, map_J_eq_range_conj,
    MonoidHom.map_zpowers]
  rfl

end Assembly

@[expose] def CF911Fam (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (J : Subgroup N), IsComponent J →
    F (↥J ⧸ Subgroup.center ↥J) →
    ∀ (p : ℕ), p.Prime → Odd p → ∀ (V O : Subgroup N) (z : N),
      IsElementaryAbelian p ↥V → Nat.card ↥V = p ^ 2 → z * z = 1 →
      V ≤ O → IsPGroup p ↥O → (∀ o ∈ O, o * z = z * o) →
      (∀ c : N, c * z = z * c → ∀ o ∈ O, c * o * c⁻¹ ∈ O) →
      V ≤ normalizer (J : Set N) → z ∈ normalizer (J : Set N) →
      Odd (Nat.card ↥(Subgroup.center ↥J)) →
      (∀ v ∈ V, v ≠ 1 → layer ↥(J ⊓ centralizer ({v} : Set N)) = ⊥) →
      False

theorem cf911Fam_of_core {F : (Y : Type) → [Group Y] → Prop} (hF : Core911Fam F) :
    CF911Fam F := by
  intro N _ _ J hJ hFJ p hp hpodd V O z hVe hVc hzz hVO hOp hOz hON hVn hzn hZodd hH2
  have : Fact p.Prime := ⟨hp⟩
  have := hVe
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  have hs : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.1.2.1
  have hna : ∃ a b : ↥J ⧸ Subgroup.center ↥J, a * b ≠ b * a := hJ.1.2.2
  set N' : Subgroup N := normalizer (J : Set N) with hN'
  set ψ : ↥N' →* MulAut (↥J ⧸ Subgroup.center ↥J) := actCenterQuot J with hψ
  have hJn : J ≤ N' := fun x hx => Subgroup.le_normalizer hx
  have hfaith : ∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N) :=
    fun v hv hv1 => not_le_centralizer_of_layer_eq_bot hJ (hH2 v hv hv1)
  set Vn : Subgroup ↥N' := V.subgroupOf N' with hVn'
  set zn : ↥N' := ⟨z, hzn⟩ with hzn'
  have hVinj : Function.Injective (ψ.domRestrict Vn) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨v, hv⟩ hv1
    have hcen := commute_of_actCenterQuot_eq_one J v hv1
    have hv' : (v : N) ∈ V := mem_subgroupOf.mp hv
    by_contra hne
    have hne' : (v : N) ≠ 1 := fun h => hne (Subtype.ext (Subtype.ext h))
    refine hfaith _ hv' hne' ?_
    intro c hc
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hcen c hc
  have hVcard : Nat.card ↥Vn = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVn).toEquiv
  have hVe' : IsElementaryAbelian p ↥(Vn.map ψ) := by
    have : IsElementaryAbelian p ↥Vn := IsElementaryAbelian.subgroupOf hVn
    exact IsElementaryAbelian.map ψ
  have hVc' : Nat.card ↥(Vn.map ψ) = p ^ 2 := by
    rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hVinj).toEquiv,
      hVcard, hVc]
  have hVz : ∀ v ∈ V, v * z = z * v := fun v hv => hOz v (hVO hv)
  have hVpg : IsPGroup p ↥V := IsPGroup.of_card hVc
  have hz1 : ψ zn ≠ 1 := by
    intro h1
    have hzc := commute_of_actCenterQuot_eq_one J zn h1
    set O₁ : Subgroup N := O ⊓ N' with hO₁
    have hO₁p : IsPGroup p ↥O₁ := hOp.to_le inf_le_left
    have hJnorm : ∀ a ∈ J, ∀ y ∈ O₁, a * y * a⁻¹ ∈ O₁ := by
      intro a ha y hy
      have haz : a * z = z * a := (hzc a ha).symm
      exact ⟨hON a haz y hy.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (hJn ha) hy.2) (Subgroup.inv_mem _ (hJn ha))⟩
    have hJO : ∀ x ∈ J, x ∈ normalizer (O₁ : Set N) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨hJnorm x hx y, fun hy => ?_⟩
      have := hJnorm x⁻¹ (Subgroup.inv_mem _ hx) _ hy
      simpa [mul_assoc] using this
    have hcomm := L915.commute_of_normal_pgroup_of_normal_quasisimple (Y := N) hp
      (H := N' ⊓ normalizer (O₁ : Set N)) (U := O₁) (I := J) hJ.1
      (le_inf hJn fun x hx => hJO x hx) (fun h hh => hh.1)
      (fun x hx => ⟨hx.2, Subgroup.le_normalizer hx⟩) (fun h hh => hh.2) hO₁p
    have hntV : Nontrivial ↥V := (Finite.one_lt_card_iff_nontrivial).mp (by
      rw [hVc]; exact Nat.one_lt_pow two_ne_zero hp.one_lt)
    obtain ⟨⟨v, hv⟩, hv1⟩ : ∃ w : ↥V, w ≠ 1 := exists_ne 1
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    refine hfaith v hv hv1' fun c hc => ?_
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((mem_centralizer_iff.mp (hcomm ⟨hVO hv, hVn hv⟩)) c hc).symm
  have hzz' : ψ zn * ψ zn = 1 := by
    rw [← map_mul]
    have : zn * zn = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hcomm' : ∀ w ∈ Vn.map ψ, w * ψ zn = ψ zn * w := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hVz _ (Subgroup.mem_subgroupOf.mp hw))
  set Hn : Subgroup N := J ⊔ V ⊔ Subgroup.zpowers z with hHn
  have hHn_le : Hn ≤ N' := sup_le (sup_le hJn hVn) ((Subgroup.zpowers_le).mpr hzn)
  have hVHn : V ≤ Hn := le_trans le_sup_right le_sup_left
  have hbarEq := hbar_eq hVn hzn
  set OY : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    ((O ⊓ Hn).subgroupOf N').map ψ with hOY
  have hsub : (O ⊓ Hn).subgroupOf N' ≤ Hn.subgroupOf N' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).2
  have hOY_le : OY ≤ hbar (↥J ⧸ Subgroup.center ↥J) (Vn.map ψ) (ψ zn) := by
    rw [hbarEq]
    exact Subgroup.map_mono hsub
  have hVOY : Vn.map ψ ≤ OY := by
    refine Subgroup.map_mono fun x hx => ?_
    have hx' : (x : N) ∈ V := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hVO hx', hVHn hx'⟩
  have hOYodd : Odd (Nat.card ↥OY) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hOp
    have h1 : Nat.card ↥OY ∣ Nat.card ↥((O ⊓ Hn).subgroupOf N') := Subgroup.card_map_dvd _ ψ
    have h2 : Nat.card ↥((O ⊓ Hn).subgroupOf N') ∣ Nat.card ↥O := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hHn_le)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat (hk ▸ hpodd.pow) (h1.trans h2)
  have hOYz : ∀ o ∈ OY, o * ψ zn = ψ zn * o := by
    rintro _ ⟨o, ho, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hOz _ (Subgroup.mem_subgroupOf.mp ho).1)
  have hOYn : ∀ c ∈ hbar (↥J ⧸ Subgroup.center ↥J) (Vn.map ψ) (ψ zn), c * ψ zn = ψ zn * c →
      ∀ o ∈ OY, c * o * c⁻¹ ∈ OY := by
    intro c hc hcz o ho
    rw [hbarEq] at hc
    obtain ⟨cn, hcn, rfl⟩ := hc
    have hcnHn : (cn : N) ∈ Hn := Subgroup.mem_subgroupOf.mp hcn
    obtain ⟨h', hh'n, hh'H, hh'z, hψh'⟩ := lift_commute hJ hp hpodd hZodd hVpg hzz hVz hVn hzn
      hcnHn cn.2 (by simpa using hcz)
    obtain ⟨on, hon, rfl⟩ := ho
    have honO : (on : N) ∈ O := (Subgroup.mem_subgroupOf.mp hon).1
    have honH : (on : N) ∈ Hn := (Subgroup.mem_subgroupOf.mp hon).2
    refine ⟨⟨h', hh'n⟩ * on * ⟨h', hh'n⟩⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      show h' * (on : N) * h'⁻¹ ∈ O ⊓ Hn
      refine ⟨hON h' hh'z _ honO, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh'H honH) (Subgroup.inv_mem _ hh'H)
    · rw [map_mul, map_mul, map_inv, hψh']
  have hH2' : ∀ w ∈ Vn.map ψ, w ≠ 1 → layer ↥(fixSub w) = ⊥ := by
    rintro _ ⟨w, hw, rfl⟩ hne
    have hw1 : w ≠ 1 := fun h => hne (by rw [h, map_one])
    have hw1' : (w : N) ≠ 1 := fun h => hw1 (Subtype.ext h)
    exact layer_fixSub_actCenterQuot hJ w.2 (hH2 (w : N) (Subgroup.mem_subgroupOf.mp hw) hw1')
  exact hF (↥J ⧸ Subgroup.center ↥J) hs hna hFJ p (Vn.map ψ) (ψ zn)
    ⟨hp, hpodd, hVe', hVc', hz1, hzz', hcomm', ⟨OY, hOY_le, hVOY, hOYodd, hOYz, hOYn⟩, hH2'⟩


@[expose] def CF911 : Prop :=
  CF911Fam (fun Y _ => GHList Y ∧ ¬ LieModel Y .PSL 3 2 2)

theorem cf911_of_families (hAlt : Core911Alt) (hSpor : Core911Spor) (hMcLy : Core911McLy)
    (hTwo : Core911Two) (hL2 : Core911L2) (hL3 : Core911L3) (hU3 : Core911U3)
    (hSp4 : Core911Sp4) (hG2 : Core911G2) (hD4 : Core911D4) (hL4 : Core911L4)
    (hU4 : Core911U4) (hL5 : Core911L5) (hU5 : Core911U5) (hRee : Core911Ree) : CF911 :=
  cf911Fam_of_core fun Y _ _ hs hna hF =>
    no911_of_families hAlt hSpor hMcLy hTwo hL2 hL3 hU3 hSp4 hG2 hD4 hL4 hU4 hL5 hU5 hRee Y hs hna
      hF.1 hF.2

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
