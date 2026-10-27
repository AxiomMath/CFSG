module

public import CFSG.LargeExtraspecial.S8FiveB
public import CFSG.LargeExtraspecial.S3Fourteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

section Generic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem dvd_and_two_mul_of_invariant {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ ⊥ ⊤ p p₁) {N' : Submodule (ZMod 2) M}
    (hN' : ∀ e : omegaGroup q hq, ∀ v ∈ N', ρ e v ∈ N') :
    2 ^ (m - 1) ∣ finrank (ZMod 2) N' ∧ (IsMinusType q ⊥ m → 2 ^ m ∣ finrank (ZMod 2) N') ∧
      finrank (ZMod 2) N' =
        2 * finrank (ZMod 2) (N' ⊓ fixOf ρ (radFix q ⊥ p : Set (V ≃ₗ[ZMod 2] V)) :
          Submodule (ZMod 2) M) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hpp₁' : polar q p₁ p = 1 := by rw [polar_comm]; exact hpp₁
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hdimV : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * m := by
    rw [perp_bot, finrank_top]; exact hdim
  have h3 : 3 ≤ finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) := by omega
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have htop : OmegaInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨c, -, -, hcR, hc1, hca⟩ := exists_mem_radFix_not_isTypeA hq hF h3 (hmem p) (hmem p₁)
    hp0 hp hpp₁
  obtain ⟨c₁, -, -, hc₁R, hc₁1, hc₁a⟩ := exists_mem_radFix_not_isTypeA hq hF h3 (hmem p₁)
    (hmem p) hp₁0 hp₁ hpp₁'
  have hN'inv : OmegaInvariant ρ ⊥ N' := fun e _ v hv => hN' e v hv
  have hD' : RadDecomp ρ ⊥ N' p p₁ :=
    radDecomp_mono ρ hF hm hdimV htop (hmem _) (hmem _) hp0 hp hp₁ hpp₁ hD le_rfl le_top
      (x := ⟨_, (radFix_le_omegaFix hq hp₁0 hp₁ hc₁R).1⟩)
      (y := ⟨_, (radFix_le_omegaFix hq hp0 hp hcR).1⟩) hc₁R hc₁1 hc₁a hcR hc1 hca
      (fun v hv => hN' _ v hv) (fun v hv => hN' _ v hv)
  refine ⟨timmesfeld_2_1_b_dvd ρ m hF (by omega) hdimV hN'inv (hmem p) (hmem p₁) hp0 hp hp₁ hpp₁
    hD', fun hmin => timmesfeld_2_1_b_dvd_minus ρ m hF hm hdimV hmin hN'inv (hmem p) (hmem p₁)
    hp0 hp hp₁ hpp₁ hD', ?_⟩
  exact (finrank_eq_two_mul ρ hF h3 hN'inv (hmem p) (hmem p₁) hp0 hp₁0 hp hp₁ hD').2

end Generic

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def Zbar (t : S.O) : Subgroup S.O :=
  Nbar S g t ⊓ centralizer (Nbar S g t : Set S.O)

theorem mem_Zbar {t x : S.O} :
    x ∈ Zbar S g t ↔ x ∈ Nbar S g t ∧ ∀ n ∈ Nbar S g t, n * x = x * n := by
  rw [Zbar, mem_inf, mem_centralizer_iff]
  simp only [SetLike.mem_coe]

theorem A1_eq {t : S.O} : A1 S g t = S.Lbar g ⊓ Zbar S g t := by
  rw [A1, Zbar, inf_assoc]

theorem t_mem_Zbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ Zbar S g t :=
  mem_Zbar.mpr ⟨self_mem_Nbar H ht, fun _ hn =>
    commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar hn)⟩

theorem t_mem_A1 (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ A1 S g t := by
  rw [A1_eq]; exact ⟨ht, t_mem_Zbar H ht⟩

theorem conj_mem_Zbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {t r : S.O} (hr : r ∈ Rbar S g t) {z : S.O}
    (hz : z ∈ Zbar S g t) : r * z * r⁻¹ ∈ Zbar S g t := by
  obtain ⟨hzN, hzc⟩ := mem_Zbar.mp hz
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hkt := commute_of_mem_Rbar haQ hr
  refine mem_Zbar.mpr ⟨conj_mem_Nbar haQ hkt hzN, fun n hn => ?_⟩
  have hk' : S.ρ k⁻¹ ∈ Rbar S g t := by rw [map_inv]; exact inv_mem hr
  have hn' : (S.ρ k)⁻¹ * n * S.ρ k ∈ Nbar S g t := by
    have h := conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hk') hn
    rwa [map_inv, inv_inv] at h
  have h1 := hzc _ hn'
  calc n * (S.ρ k * z * (S.ρ k)⁻¹) = S.ρ k * ((S.ρ k)⁻¹ * n * S.ρ k * z) * (S.ρ k)⁻¹ := by
        group
    _ = S.ρ k * (z * ((S.ρ k)⁻¹ * n * S.ρ k)) * (S.ρ k)⁻¹ := by rw [h1]
    _ = S.ρ k * z * (S.ρ k)⁻¹ * n := by group

theorem nqSub_inf {t : S.O} [NQHyp S g t] {X Y : Subgroup S.O} (htX : t ∈ X) (htY : t ∈ Y) :
    nqSub S g t X ⊓ nqSub S g t Y = nqSub S g t (X ⊓ Y) := by
  ext v
  obtain ⟨n, rfl⟩ := nqMk_surjective v
  rw [Submodule.mem_inf, mem_nqSub htX, mem_nqSub htY, mem_nqSub (mem_inf.mpr ⟨htX, htY⟩),
    mem_inf]

theorem nqRep_mem_nqSub_Zbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) [NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) (e : Y)
    {v : NQ S g t} (hv : v ∈ nqSub S g t (Zbar S g t)) :
    nqRep S g t hY e v ∈ nqSub S g t (Zbar S g t) := by
  obtain ⟨n, rfl⟩ := nqMk_surjective v
  have htZ := t_mem_Zbar H ht
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV H.conj_mem t).range := by
    rw [range_resV, hY]; exact e.2
  obtain ⟨x, hx⟩ := heR
  rw [nqRep_apply hY hx.symm n, mem_nqSub htZ, coe_nConj]
  exact conj_mem_Zbar H.conj_mem x.2 ((mem_nqSub htZ n).mp hv)

theorem finrank_nqSub_Zbar_pos (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) [NQHyp S g t]
    (hZ : ¬ Zbar S g t ≤ zpowers t) : 0 < finrank (ZMod 2) (nqSub S g t (Zbar S g t)) := by
  have : FiniteDimensional (ZMod 2) (NQ S g t) := inferInstance
  have htZ := t_mem_Zbar H ht
  obtain ⟨z, hzZ, hzt⟩ := IsConcreteLE.not_le_iff_exists.mp hZ
  have hzN : z ∈ Nbar S g t := (mem_Zbar.mp hzZ).1
  refine Nat.pos_of_ne_zero fun h0 => hzt ?_
  rw [Submodule.finrank_eq_zero] at h0
  have hmem : nqMk (⟨z, hzN⟩ : Nbar S g t) ∈ nqSub S g t (Zbar S g t) :=
    (mem_nqSub htZ _).mpr hzZ
  rw [h0, Submodule.mem_bot, nqMk_eq_zero_iff] at hmem
  exact hmem

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem fixOf_nqRep_radFix_eq (hNo : NoA2 S g) (D : Std H C ht ht1 hVQ) [NQHyp S g t] :
    S2.fixOf (nqRep S g t D.hX)
        (radFix D.Q ⊥ (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      nqSub S g t (S.Lbar g) := by
  have h1R : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
  have hL1 : ((radFix D.Q ⊥ (aV ht) : Subgroup _) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      LhmodN S g t 1 := by
    rw [radFix_bot, ← D.hE]
    ext e
    simp only [SetLike.mem_coe, LmodN, LhmodN, OneMemClass.coe_one, one_mul]
  have h := fixOf_nqRep_eq H hNo C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb D.hX h1R hL1
  simpa only [OneMemClass.coe_one, one_mul] using h

theorem finrank_nqSub_Zbar (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) [NQHyp S g t] :
    2 ^ (D.m - 1) ∣ finrank (ZMod 2) (nqSub S g t (Zbar S g t)) ∧
      (D.IsMinus → 2 ^ D.m ∣ finrank (ZMod 2) (nqSub S g t (Zbar S g t))) ∧
      finrank (ZMod 2) (nqSub S g t (Zbar S g t)) =
        2 * finrank (ZMod 2) (nqSub S g t (A1 S g t)) := by
  have hD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ D.hN0 D.hh D.hb D.hX D.hE
  have : FiniteDimensional (ZMod 2) (NQ S g t) := inferInstance
  obtain ⟨hdvd, hdvd', htwo⟩ := dvd_and_two_mul_of_invariant (nqRep S g t D.hX) D.hm D.hdim
    (aV_ne_zero H ht) D.hQa D.Q_bV D.polar_aV_bV hD
    (fun e v hv => nqRep_mem_nqSub_Zbar H ht D.hX e hv)
  refine ⟨hdvd, fun hmin => hdvd' fun T _ hT => hmin T hT, ?_⟩
  have h2 := htwo.trans (congrArg (fun K => 2 * finrank (ZMod 2) ↥(nqSub S g t (Zbar S g t) ⊓ K))
    (fixOf_nqRep_radFix_eq hNo D))
  have e : nqSub S g t (Zbar S g t) ⊓ nqSub S g t (S.Lbar g) = nqSub S g t (A1 S g t) := by
    rw [inf_comm, nqSub_inf ht (t_mem_Zbar H ht), ← A1_eq]
  exact h2.trans (congrArg (fun K : Submodule (ZMod 2) (NQ S g t) => 2 * finrank (ZMod 2) ↥K) e)

theorem A1_le_zpowers (D : Std H C ht ht1 hVQ) : A1 S g t ≤ zpowers t := by
  intro α hα
  by_cases hα1 : α = 1
  · rw [hα1]
    exact one_mem _
  · rw [eq_t_of_commSpace_eq H C ht ht1 hVQ (mem_A1.mp hα).1 (commSpace_eq_Vt_of_mem_A1 D hα hα1)]
    exact mem_zpowers t

theorem Zbar_le_zpowers (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) : Zbar S g t ≤ zpowers t := by
  by_contra hZ
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb
  obtain ⟨-, -, htwo⟩ := finrank_nqSub_Zbar hNo hΩ D
  have hpos := finrank_nqSub_Zbar_pos H ht hZ
  have hne : nqSub S g t (A1 S g t) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at htwo
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, rfl⟩ := nqMk_surjective v
  have hnA1 : (n : S.O) ∈ A1 S g t := (mem_nqSub (t_mem_A1 H ht) n).mp hv
  exact hv0 ((nqMk_eq_zero_iff n).mpr (A1_le_zpowers D hnA1))

theorem timmesfeld_8_5 (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    IsExtraspecialPGroup 2 (Nbar S g t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htN := self_mem_Nbar H ht
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hZ := Zbar_le_zpowers hNo hΩ D
  have hct : ∀ n ∈ Nbar S g t, ∀ z ∈ zpowers t, n * z = z * n := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar hn)) k).eq
  have hcenter : ∀ x : Nbar S g t, x ∈ center (Nbar S g t) ↔ (x : S.O) ∈ zpowers t := by
    intro x
    rw [mem_center_iff]
    constructor
    · intro h
      refine hZ (mem_Zbar.mpr ⟨x.2, fun n hn => ?_⟩)
      exact congrArg Subtype.val (h ⟨n, hn⟩)
    · intro h y
      exact Subtype.ext (hct y y.2 x h)
  have hle : zpowers t ≤ Nbar S g t := zpowers_le.mpr htN
  refine isExtraspecialPGroup_of_card_center D.isPGroup_Nbar ?_ (fun x y => ?_) (fun x => ?_) ?_
  · have e : center (Nbar S g t) = (zpowers t).subgroupOf (Nbar S g t) :=
      Subgroup.ext fun x => (hcenter x).trans mem_subgroupOf.symm
    rw [e, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  · rw [hcenter, commutatorElement_def]
    exact D.hNc x x.2 y y.2
  · rw [hcenter, pow_two]
    exact D.hNsq x x.2
  ·
    have hnle : ¬ S.Lbar g ⊓ Nbar S g t ≤ zpowers t := fun h =>
      hA7 (le_antisymm h (zpowers_le.mpr ⟨ht, htN⟩))
    obtain ⟨x, hxA, hxt⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    have hxc : (⟨x, hxA.2⟩ : Nbar S g t) ∉ center (Nbar S g t) := fun h =>
      hxt ((hcenter _).mp h)
    rw [mem_center_iff] at hxc
    push Not at hxc
    obtain ⟨y, hy⟩ := hxc
    exact ⟨⟨x, hxA.2⟩, y, fun h => hy h.symm⟩

end CFSG.LargeExtraspecial.S8
