module

public import CFSG.GH74.GLS.IVK.Lifted32.Classes
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafIVK31b
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

namespace Zw

section NoFinite

variable {G : Type} [Group G] {z : G}

theorem mem_Oz_of_toBar_eq_one {w : G} (hwC : w ∈ Cen z) (h : toBar z ⟨w, hwC⟩ = 1) : w ∈ Oz z := by
  have hker : (⟨w, hwC⟩ : ↥(Cen z)) ∈ (toBar z).ker := h
  rw [ker_toBar] at hker
  exact Subgroup.mem_map.2 ⟨_, hker, rfl⟩

theorem toBar_eq_one_of_mem_Oz {w : G} (hw : w ∈ Oz z) (hwC : w ∈ Cen z) : toBar z ⟨w, hwC⟩ = 1 := by
  obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.1 hw
  have e : (⟨w, hwC⟩ : ↥(Cen z)) = c := Subtype.ext hcw.symm
  rw [e]
  have : c ∈ (toBar z).ker := by rwa [ker_toBar]
  exact this

theorem card_barOf_dvd {X : Subgroup G} (hX : X ≤ Cen z) : Nat.card ↥(barOf z X) ∣ Nat.card ↥X := by
  have h1 := Subgroup.card_map_dvd (X.subgroupOf (Cen z)) (toBar z)
  have h2 : Nat.card ↥(X.subgroupOf (Cen z)) = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rwa [h2] at h1

end NoFinite

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem normalizer_conj (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) {c n : G} (hc : c ∈ Cen z)
    (hn : n ∈ Cen z) (hn1 : n ∈ normalizer (K₁ : Set G)) : c * n * c⁻¹ ∈ normalizer (K₁ : Set G) := by
  have hM := m4_of_std hII h
  have hM' := m4_of_std hII h.swap
  have hcn : c * n * c⁻¹ ∈ Cen z := mul_mem (mul_mem hc hn) (inv_mem hc)
  have key : ∀ X : Subgroup G, n ∈ normalizer (X : Set G) →
      c * n * c⁻¹ ∈ normalizer ((M.cj X c⁻¹ : Subgroup G) : Set G) := by
    intro X hX
    rw [Subgroup.mem_normalizer_iff] at hX ⊢
    intro y
    rw [M.mem_cj, M.mem_cj]
    have e : c⁻¹ * (c * n * c⁻¹ * y * (c * n * c⁻¹)⁻¹) * c⁻¹⁻¹ = n * (c⁻¹ * y * c⁻¹⁻¹) * n⁻¹ := by
      group
    rw [e]
    exact hX _
  rcases hM.perm c⁻¹ (inv_mem hc) with ⟨h1, -⟩ | ⟨h1, -⟩
  · have := key K₁ hn1
    rwa [h1] at this
  · have := key K₁ hn1
    rw [h1] at this
    exact normalizer_other hM' h.ne.symm hcn this


theorem sylow_CP₁ (hII : II4_4_4_center) (hctr : Ctr5 G z S K₁ K₂ a x) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Wof S a ⊓ (K₁ ⊓ centralizer ({a} : Set G)))
      (K₁ ⊓ centralizer ({a} : Set G)) := by
  have hstd : Std4 G z S K₁ K₂ := hctr.cfg.std
  have hM := m4_of_std hII hstd
  have hK₁C : K₁ ≤ Cen z := hM.K₁_le
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (Wof S a ⊓ ((Cen z ⊓ centralizer ({a} : Set G)) ⊓
      normalizer (K₁ : Set G))) ((Cen z ⊓ centralizer ({a} : Set G)) ⊓ normalizer (K₁ : Set G)) := by
    refine hctr.extr.inf_of_le_normalizer inf_le_left ?_
    rw [Subgroup.le_normalizer_iff]
    intro c hc d hd
    obtain ⟨hcC, hca⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨hd0, hdN⟩ := Subgroup.mem_inf.1 hd
    obtain ⟨hdC, hda⟩ := Subgroup.mem_inf.1 hd0
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hcC hdC) (inv_mem hcC), ?_⟩,
      normalizer_conj hII hstd hcC hdC hdN⟩
    have hc' : Commute c a := Subgroup.mem_centralizer_singleton_iff.1 hca
    have hd' : Commute d a := Subgroup.mem_centralizer_singleton_iff.1 hda
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hc'.mul_left hd').mul_left hc'.inv_left)
  have h2 := h1.inf_of_le_normalizer (N := K₁ ⊓ centralizer ({a} : Set G)) (by
      intro y hy
      obtain ⟨hyK, hya⟩ := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hK₁C hyK, hya⟩, Subgroup.le_normalizer hyK⟩) (by
      rw [Subgroup.le_normalizer_iff]
      intro d hd y hy
      obtain ⟨hd0, hdN⟩ := Subgroup.mem_inf.1 hd
      obtain ⟨hdC, hda⟩ := Subgroup.mem_inf.1 hd0
      obtain ⟨hyK, hya⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hdN y).1 hyK, ?_⟩
      have hd' : Commute d a := Subgroup.mem_centralizer_singleton_iff.1 hda
      have hy' : Commute y a := Subgroup.mem_centralizer_singleton_iff.1 hya
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hd'.mul_left hy').mul_left hd'.inv_left))
  have e : (Wof S a ⊓ ((Cen z ⊓ centralizer ({a} : Set G)) ⊓ normalizer (K₁ : Set G))) ⊓
      (K₁ ⊓ centralizer ({a} : Set G)) = Wof S a ⊓ (K₁ ⊓ centralizer ({a} : Set G)) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hyW, -⟩, hyX⟩
      exact ⟨hyW, hyX⟩
    · rintro ⟨hyW, hyK, hya⟩
      exact ⟨⟨hyW, ⟨hK₁C hyK, hya⟩, Subgroup.le_normalizer hyK⟩, hyK, hya⟩
  rwa [e] at h2


theorem bar_centralizer_le {K : Subgroup G} (haC : a ∈ Cen z) (ha2 : a * a = 1)
    (haK : a ∈ normalizer (K : Set G)) :
    barOf z K ⊓ centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)) ≤
      barOf z (K ⊓ centralizer ({a} : Set G)) := by
  intro y hy
  obtain ⟨hyK, hyc⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨k, hkK, hkC, rfl⟩ := Pull.exists_of_mem_barOf hyK
  have hyc' : toBar z ⟨k, hkC⟩ * toBar z ⟨a, haC⟩ = toBar z ⟨a, haC⟩ * toBar z ⟨k, hkC⟩ :=
    Subgroup.mem_centralizer_singleton_iff.1 hyc
  have hOodd : Odd (Nat.card ↥(K ⊓ Oz z)) :=
    Odd.of_dvd_nat card_Oz_odd (Subgroup.card_dvd_of_le inf_le_right)
  have hzO : ∀ o ∈ K ⊓ Oz z, a * o * a⁻¹ ∈ K ⊓ Oz z := fun o ho =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 haK o).1 (Subgroup.mem_inf.1 ho).1,
      Oz_conj haC (Subgroup.mem_inf.1 ho).2⟩
  have hakC : a * k * a⁻¹ ∈ Cen z := mul_mem (mul_mem haC hkC) (inv_mem haC)
  have hmC : k⁻¹ * (a * k * a⁻¹) ∈ Cen z := mul_mem (inv_mem hkC) hakC
  have hx : k⁻¹ * (a * k * a⁻¹) ∈ K ⊓ Oz z := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hkK) ((Subgroup.mem_normalizer_iff.1 haK k).1 hkK),
      mem_Oz_of_toBar_eq_one hmC ?_⟩
    rw [Cls.toBar_mul (inv_mem hkC) hakC, Cls.toBar_inv hkC, Cls.toBar_conj haC hkC, ← hyc']
    group
  obtain ⟨o, ho, hc⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf.exists_centralized_in_coset hOodd ha2 hzO hx
  obtain ⟨hoK, hoO⟩ := Subgroup.mem_inf.1 ho
  have hoC : o ∈ Cen z := by
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hoO
    exact c.2
  have hkoC : k * o ∈ Cen z := mul_mem hkC hoC
  have hko : k * o ∈ K ⊓ centralizer ({a} : Set G) :=
    Subgroup.mem_inf.2 ⟨mul_mem hkK hoK, Subgroup.mem_centralizer_singleton_iff.2
      (mul_inv_eq_iff_eq_mul.1 hc).symm⟩
  have himg : toBar z ⟨k * o, hkoC⟩ = toBar z ⟨k, hkC⟩ := by
    rw [Cls.toBar_mul hkC hoC, toBar_eq_one_of_mem_Oz hoO hoC, mul_one]
  rw [← himg]
  exact Pull.mem_barOf hko hkoC


theorem sixteen_dvd {r : ℕ} (hr : Odd r) : 16 ∣ r ^ 2 * ((r ^ 2) ^ 2 - 1) := by
  have h2 : r % 2 = 1 := Nat.odd_iff.1 hr
  have h16 : ∀ k : ℕ, k < 16 → k % 2 = 1 → k ^ 4 % 16 = 1 := by decide
  have hmod : (r ^ 2) ^ 2 % 16 = 1 := by
    have e : (r ^ 2) ^ 2 = r ^ 4 := by ring
    rw [e, Nat.pow_mod]
    exact h16 (r % 16) (Nat.mod_lt _ (by norm_num)) (by omega)
  have hpos : 1 ≤ (r ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hr.pos)
  have : 16 ∣ (r ^ 2) ^ 2 - 1 := (Nat.modEq_iff_dvd' hpos).1 (by
    unfold Nat.ModEq
    rw [hmod])
  exact Dvd.dvd.mul_left this _

theorem sixteen_dvd_card_sl2 {F : Type} [Field F] [Finite F] {r : ℕ} (hr : Odd r)
    (hF : Nat.card F = r ^ 2) : 16 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedSL 2 F) := by
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  exact sixteen_dvd hr

theorem sixteen_dvd_card_CK {K₁ K₂ : Subgroup G} (hK₁C : K₁ ≤ Cen z) (haC : a ∈ Cen z) (ha2 : a * a = 1)
    (haK : a ∈ normalizer (K₁ : Set G)) {r : ℕ} (hr : Odd r)
    (hCh : IVK.Prod3.Ch (barOf z K₁) (barOf z K₂) (toBar z ⟨a, haC⟩) r) :
    16 ∣ Nat.card ↥(K₁ ⊓ centralizer ({a} : Set G)) := by
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := (hCh.2 (barOf z K₁) (by simp)).1
  have h1 : 16 ∣ Nat.card ↥(IVK.Prod3.ELayer (barOf z K₁ ⊓
      centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)))) := by
    rw [Nat.card_congr e.toEquiv]
    exact sixteen_dvd_card_sl2 hr hq
  have h2 : IVK.Prod3.ELayer (barOf z K₁ ⊓
      centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z))) ≤ barOf z K₁ ⊓
      centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)) := Subgroup.map_subtype_le _
  have h3 := bar_centralizer_le haC ha2 haK
  have h4 := card_barOf_dvd (X := K₁ ⊓ centralizer ({a} : Set G)) (z := z)
    (fun y hy => hK₁C (Subgroup.mem_inf.1 hy).1)
  exact h1.trans ((Subgroup.card_dvd_of_le h2).trans ((Subgroup.card_dvd_of_le h3).trans h4))


theorem Q_inf_Q (hII : II4_4_4_center) (h : Cfg5 G z S K₁ K₂) :
    Qof S K₁ ⊓ Qof S K₂ ≤ zpowers z := by
  have hM := m4_of_std hII h.std
  rintro c ⟨⟨hcS, hc1⟩, ⟨-, hc2⟩⟩
  obtain ⟨-, -, hc1'⟩ := hc1
  obtain ⟨-, -, hc2'⟩ := hc2
  have hcC : c ∈ centralizer ({z} : Set G) := hM.S_syl.1 hcS
  have h1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun x hx =>
    hM.O_le_OK (Or.inl rfl) (hc1' x hx)
  have h2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun y hy =>
    hM.O_le_OK (Or.inr rfl) (hc2' y hy)
  have hcs := hM.secCent_of_gen hcC h1 h2
  have hcQ : c ∈ Qz S z := by
    rw [Qz_eq h.std]
    exact ⟨hcS, hcs⟩
  rw [h.hQ] at hcQ
  exact hcQ

end Zw

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem l53_ZW (hII : II4_4_4_center) (_h2A7 : IVK.Lifted.II4_2A7)
    (hctr : Ctr5 G z S K₁ K₂ a x) (h52 : L52 S K₁ K₂) (haC : a ∈ Cen z)
    {Y A : Subgroup (CentralizerBar z)} {r : ℕ} (hD : AbsData z S K₁ K₂ a haC Y A r) :
    ∀ w ∈ Wof S a, (∀ v ∈ Wof S a, w * v = v * w) → w ∈ zpowers a ⊔ zpowers z := by
  intro w hwW hZ
  have hstd : Std4 G z S K₁ K₂ := hctr.cfg.std
  have hM := m4_of_std hII hstd
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := hstd.sylow
  have hSC : S ≤ Cen z := hS.le
  have hK₁ : IsPCompIn 2 (Cen z) K₁ := hstd.comp_isPCompIn (Or.inl rfl)
  have haS : a ∈ S := hctr.elt.mem
  have ha2 : a * a = 1 := Cls.mul_self_of_orderOf_two hctr.elt.inv
  have haK₁ : a ∈ normalizer (K₁ : Set G) := hctr.elt.f₁.1
  have hwS : w ∈ S := (Subgroup.mem_inf.1 hwW).1
  have hwC : w ∈ Cen z := hSC hwS
  have hwa : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hwW).2
  have hzC : z ∈ Cen z := mem_Cen_self z
  have hzS : z ∈ S := hM.z_mem_S
  by_cases hw1 : w ∈ normalizer (K₁ : Set G)
  ·
    have hwbar : toBar z ⟨w, hwC⟩ ∈ IVK.Prod3.T1 (barOf z S) (barOf z K₁) ⊓
        centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Pull.mem_barOf hwS hwC,
        (Lat.mem_normalizer_iff_bar hK₁ hwC).1 hw1⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← Cls.toBar_mul hwC haC, ← Cls.toBar_mul haC hwC]
      exact congrArg (toBar z) (Subtype.ext hwa)
    have hcent : (⟨toBar z ⟨w, hwC⟩, hwbar⟩ : ↥(IVK.Prod3.T1 (barOf z S) (barOf z K₁) ⊓
        centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)))) ∈ Subgroup.center ↥(
        IVK.Prod3.T1 (barOf z S) (barOf z K₁) ⊓
          centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z))) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨gb, hg⟩
      obtain ⟨hgT1, hgc⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨hgT, hgN⟩ := Subgroup.mem_inf.1 hgT1
      obtain ⟨s, hsS, hsC, rfl⟩ := Pull.exists_of_mem_barOf hgT
      have hsa : s * a = a * s := by
        refine Pull.toBar_injOn hS (S.mul_mem hsS haS) (S.mul_mem haS hsS) ?_
        rw [Cls.toBar_mul hsC haC, Cls.toBar_mul haC hsC]
        exact Subgroup.mem_centralizer_singleton_iff.1 hgc
      have hsW : s ∈ Wof S a := Subgroup.mem_inf.2 ⟨hsS, Subgroup.mem_centralizer_singleton_iff.2 hsa⟩
      have hws := hZ s hsW
      apply Subtype.ext
      show toBar z ⟨s, hsC⟩ * toBar z ⟨w, hwC⟩ = toBar z ⟨w, hwC⟩ * toBar z ⟨s, hsC⟩
      rw [← Cls.toBar_mul hsC hwC, ← Cls.toBar_mul hwC hsC]
      exact congrArg (toBar z) (Subtype.ext hws.symm)
    have hCj : (Subgroup.center ↥(IVK.Prod3.T1 (barOf z S) (barOf z K₁) ⊓
        centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)))).map
        (IVK.Prod3.T1 (barOf z S) (barOf z K₁) ⊓
          centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z))).subtype =
        zpowers (toBar z ⟨a, haC⟩) ⊔ zpowers (zBar z) := hD.Cj
    have hmem : toBar z ⟨w, hwC⟩ ∈ zpowers (toBar z ⟨a, haC⟩) ⊔ zpowers (zBar z) := by
      rw [← hCj]
      exact Subgroup.mem_map.2 ⟨⟨_, hwbar⟩, hcent, rfl⟩
    have hpull : w ∈ pull z S (zpowers (toBar z ⟨a, haC⟩) ⊔ zpowers (zBar z)) :=
      Pull.mem_pull_of hwS hwC hmem
    have e : zBar z = toBar z ⟨z, hzC⟩ := rfl
    have hA' : zpowers (toBar z ⟨a, haC⟩) ≤ barOf z S := zpowers_le.2 (Pull.mem_barOf haS haC)
    have hZ' : zpowers (zBar z) ≤ barOf z S := zpowers_le.2 (by
      rw [e]
      exact Pull.mem_barOf hzS hzC)
    rw [Pull.pull_sup hSC hA' hZ', e, Pull.pull_zpowers hS haS haC,
      Pull.pull_zpowers hS hzS hzC] at hpull
    exact hpull
  ·
    exfalso
    have hcj : M.cj K₁ w = K₂ := by
      rcases hM.perm w hwC with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (M.cj_eq_iff_normalizer.1 h1) hw1
      · exact h1
    have hsyl := Zw.sylow_CP₁ hII hctr
    have hcard : Nat.card ↥(Wof S a ⊓ (K₁ ⊓ centralizer ({a} : Set G))) =
        2 ^ (Nat.card ↥(K₁ ⊓ centralizer ({a} : Set G))).factorization 2 := hsyl.card_eq
    have h16 : 16 ∣ Nat.card ↥(K₁ ⊓ centralizer ({a} : Set G)) :=
      Zw.sixteen_dvd_card_CK hM.K₁_le haC ha2 haK₁ hD.Cb.2.1 hD.Ch
    have hv : 4 ≤ (Nat.card ↥(K₁ ⊓ centralizer ({a} : Set G))).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h16
    have hge : 16 ≤ Nat.card ↥(Wof S a ⊓ (K₁ ⊓ centralizer ({a} : Set G))) := by
      rw [hcard]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (Nat.card ↥(K₁ ⊓ centralizer ({a} : Set G))).factorization 2 :=
          Nat.pow_le_pow_right (by norm_num) hv
    have hle : Wof S a ⊓ (K₁ ⊓ centralizer ({a} : Set G)) ≤ zpowers z := by
      intro y hy
      obtain ⟨hyW, hyX⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨hyK₁, -⟩ := Subgroup.mem_inf.1 hyX
      have hyw : w * y * w⁻¹ = y := by
        rw [hZ y hyW]
        group
      have hyK₂ : y ∈ K₂ := by
        rw [← hcj, M.mem_cj, hyw]
        exact hyK₁
      have hyS : y ∈ S := (Subgroup.mem_inf.1 hyW).1
      have hq1 : y ∈ Qof S K₁ := by
        rw [h52.1]
        exact Subgroup.mem_inf.2 ⟨hyS, hyK₂⟩
      have hq2 : y ∈ Qof S K₂ := by
        rw [h52.2]
        exact Subgroup.mem_inf.2 ⟨hyS, hyK₁⟩
      exact Zw.Q_inf_Q hII hctr.cfg ⟨hq1, hq2⟩
    have hle2 : Nat.card ↥(Wof S a ⊓ (K₁ ⊓ centralizer ({a} : Set G))) ≤ 2 := by
      calc _ ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hle
        _ = 2 := by rw [Nat.card_zpowers, hstd.orderOf_z]
    omega

end Main

end CFSG.GH74.GLS.IVK.Lifted32
