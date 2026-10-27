module

public import CFSG.GH74.GLS.C3.Layer1.BkIv10Bal
public import CFSG.GH74.GLS.C3.Layer1.BkIvk10Stmt
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.St1Bal
public import CFSG.GH74.GLS.C3.Layer1.BkL92Lift

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

section Abstract

variable {F : Type} [Group F]

theorem pPrimeCoreOf_ne_bot_of_lift (hcen : ∀ a : F, (∀ b : F, a * b = b * a) → a = 1)
    {Cc W : Subgroup (MulAut F)} {yb : MulAut F} (hCc : ∀ c ∈ Cc, c * yb = yb * c)
    (hlift : ∀ k : F, yb k = k → (MulAut.conj k : MulAut F) ∈ Cc) (hWCc : W ≤ Cc)
    (hWn : ∀ c ∈ Cc, ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hodd : Odd (Nat.card W)) (hW : W ≠ ⊥) :
    pPrimeCoreOf 2 (((MulAut.conj : F →* MulAut F).range ⊔ Cc) ⊓
      centralizer ({yb} : Set (MulAut F))) ≠ ⊥ := by
  have : ((MulAut.conj : F →* MulAut F).range).Normal := conj_range_normal
  set Zp : Subgroup (MulAut F) :=
    ((MulAut.conj : F →* MulAut F).range ⊔ Cc) ⊓ centralizer ({yb} : Set (MulAut F)) with hZp
  have hZCc : Zp ≤ Cc := by
    intro z hz
    obtain ⟨i, hi, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hz.1
    have hzy : Commute (i * c) yb := (mem_centralizer_singleton_iff.1 hz.2)
    have hcy : Commute c yb := hCc c hc
    have hiy : Commute i yb := by
      have := hzy.mul_left hcy.inv_left
      simpa using this
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hi
    have hfix : yb k = k := by
      have h1 : yb * MulAut.conj k * yb⁻¹ = MulAut.conj k := by
        rw [← hiy.eq]
        group
      rw [mul_conj_mul_inv] at h1
      exact conj_injective_of_center_bot hcen h1
    exact Cc.mul_mem (hlift k hfix) hc
  have hWZ : W ≤ Zp := fun w hw =>
    ⟨Subgroup.mem_sup_right (hWCc hw), mem_centralizer_singleton_iff.2 (hCc w (hWCc hw))⟩
  have hnormal : (W.subgroupOf Zp).Normal :=
    (Subgroup.normal_subgroupOf_iff hWZ).2 fun h k hh hk => hWn k (hZCc hk) h hh
  have hle : W ≤ pPrimeCoreOf 2 Zp :=
    le_pPrimeCoreOf_of_normal_odd hWZ hnormal (Nat.coprime_two_left.2 hodd)
  intro hbot
  rw [hbot] at hle
  exact hW (le_bot_iff.1 hle)

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def actImg {M K : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ K, m * l * m⁻¹ ∈ K)
    (S : Subgroup G) : Subgroup (MulAut (kBar K)) :=
  (S.subgroupOf M).map (Back.actHom hLn)

omit [Finite G] in
theorem mem_actImg_iff {M K S : Subgroup G} (hLn : ∀ m ∈ M, ∀ l ∈ K, m * l * m⁻¹ ∈ K)
    {φ : MulAut (kBar K)} :
    φ ∈ actImg hLn S ↔ ∃ m : ↥M, (m : G) ∈ S ∧ Back.actHom hLn m = φ := by
  unfold actImg
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem exists_lift_fixed {M K : Subgroup G} {y : G} (hy2 : orderOf y = 2) (hyM : y ∈ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ K, m * l * m⁻¹ ∈ K) (kb : kBar K)
    (hfix : Back.actHom hLn ⟨y, hyM⟩ kb = kb) :
    ∃ c : ↥K, (c : G) * y = y * c ∧ (QuotientGroup.mk c : kBar K) = kb := by
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
  rw [Back.actHom_mk, QuotientGroup.eq_iff_div_mem] at hfix
  have hk1 : y * (k₀ : G) * y⁻¹ ∈ K := hLn y hyM k₀ k₀.2
  have hdiv : ((⟨y * (k₀ : G) * y⁻¹, hk1⟩ : ↥K) / k₀ : ↥K) =
      ⟨y * (k₀ : G) * y⁻¹ * (k₀ : G)⁻¹, K.mul_mem hk1 (K.inv_mem k₀.2)⟩ :=
    Subtype.ext (by simp [div_eq_mul_inv])
  have hfix' : (⟨y * (k₀ : G) * y⁻¹ * (k₀ : G)⁻¹, K.mul_mem hk1 (K.inv_mem k₀.2)⟩ : ↥K) ∈
      pPrimeCore 2 ↥K := by
    rw [← hdiv]
    exact hfix
  have hfixO : y * (k₀ : G) * y⁻¹ * (k₀ : G)⁻¹ ∈ pPrimeCoreOf 2 K :=
    Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨_, hfix'⟩
  obtain ⟨c, hcK, hcy, hcO⟩ := exists_comm_mem_coset_of_fixed hy2
    (fun k hk => hLn y hyM k hk) k₀.2 hfixO
  refine ⟨⟨c, hcK⟩, hcy, ?_⟩
  obtain ⟨hh, hh2⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 hcO
  exact (QuotientGroup.eq.2 hh2).symm

theorem no_central_involution {K : Subgroup G} {x : G}
    (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hsimple : IsSimpleGroup (kBar K)) :
    (∀ a : kBar K, (∀ b : kBar K, a * b = b * a) → a = 1) ∧
      ∀ c ∈ K, orderOf c = 2 → ¬ ∀ l ∈ K, ⁅c, l⁆ ∈ pPrimeCoreOf 2 K := by
  obtain ⟨a₀, b₀, hab₀⟩ := Back.nonab_of_quasisimple (TwoThin.isQuasisimple_hat hKc)
  have hcen : ∀ a : kBar K, (∀ b : kBar K, a * b = b * a) → a = 1 := by
    intro a ha
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (kBar K)) with hb | ht
    · have : a ∈ Subgroup.center (kBar K) := Subgroup.mem_center_iff.2 fun g => (ha g).symm
      rw [hb] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      apply hab₀
      have h1 : a₀ ∈ Subgroup.center (kBar K) := by rw [ht]; exact Subgroup.mem_top _
      exact (Subgroup.mem_center_iff.1 h1 b₀).symm
  refine ⟨hcen, fun c hcK hc2 hcl => ?_⟩
  have h1 : (QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : kBar K) = 1 := by
    apply hcen
    intro b
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    obtain ⟨hh, hh2⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 (hcl l l.2)
    have e : ((⟨c, hcK⟩ : ↥K) * l / (l * ⟨c, hcK⟩) : ↥K) = ⟨⁅c, (l : G)⁆, hh⟩ :=
      Subtype.ext (by simp [commutatorElement_def, div_eq_mul_inv, mul_assoc])
    rw [e]
    exact hh2
  rw [QuotientGroup.eq_one_iff] at h1
  have hcO : c ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hcK, h1⟩
  have := Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hcO)
  rw [hc2] at this
  exact absurd this (by decide)

omit [Finite G] in
theorem hLn_normalizer (K : Subgroup G) :
    ∀ m ∈ normalizer (K : Set G), ∀ l ∈ K, m * l * m⁻¹ ∈ K :=
  fun _ hm _ hl => (mem_normalizer_iff.1 hm _).1 hl

theorem ivk10_bridge
    (h : B_ivk_10_2L) {x y : G} {K : Subgroup G} (hlu : IsLocallyUnbalancing x y K)
    {q : ℕ} (hq : IsFM9 q) (hL2 : HasL2Model (kBar K) (fun r => r = q)) :
    Back.actHom (hLn_normalizer K) ⟨y, hlu.2.2.2.1⟩ ∉
        (MulAut.conj : kBar K →* MulAut (kBar K)).range ∧
      IVK.IsPGL2 ↥((MulAut.conj : kBar K →* MulAut (kBar K)).range ⊔
        zpowers (Back.actHom (hLn_normalizer K) ⟨y, hlu.2.2.2.1⟩)) (fun r => r = q) := by
  obtain ⟨⟨hx2, hKc⟩, hy2, hyC, hyN, hWnot⟩ := hlu
  have hKx : K ≤ centralizer ({x} : Set G) := hKc.1
  have hsimple : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hL2
  obtain ⟨hcen, hZ⟩ := no_central_involution hKc hsimple
  have hWN := pPrimeCoreOf_centralizer_le_normalizer hKc hy2 hyN hZ
  set M₀ : Subgroup G := normalizer (K : Set G) with hM₀
  have hLn := hLn_normalizer K
  set Zxy : Subgroup G := centralizer ({x, y} : Set G) with hZxy
  have hZmem : ∀ z, z ∈ Zxy ↔ z * x = x * z ∧ z * y = y * z := by
    intro z
    simp only [hZxy, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  set W : Subgroup G := pPrimeCoreOf 2 Zxy with hWdef
  set N₁ : Subgroup G := Zxy ⊓ normalizer (K : Set G) with hN₁
  have hWZ : W ≤ Zxy := TwoThin.pPrimeCoreOf_le Zxy
  have hWM : W ≤ M₀ := hWN
  have hWN₁ : W ≤ N₁ := fun w hw => ⟨hWZ hw, hWN hw⟩
  have hlift : ∀ kb : kBar K, Back.actHom hLn ⟨y, hyN⟩ kb = kb →
      (MulAut.conj kb : MulAut (kBar K)) ∈ actImg hLn N₁ := by
    intro kb hfix
    obtain ⟨c, hcy, rfl⟩ := exists_lift_fixed hy2 hyN hLn kb hfix
    have hcM : (c : G) ∈ M₀ := le_normalizer c.2
    refine mem_actImg_iff hLn |>.2 ⟨⟨c, hcM⟩, ⟨(hZmem c).2 ⟨?_, hcy⟩, le_normalizer c.2⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.1 (hKx c.2)
    · exact Back.actHom_of_mem hLn c.2 hcM
  have hCc : ∀ φ ∈ actImg hLn N₁,
      φ * Back.actHom hLn ⟨y, hyN⟩ = Back.actHom hLn ⟨y, hyN⟩ * φ := by
    intro φ hφ
    obtain ⟨m, hmN, rfl⟩ := (mem_actImg_iff hLn).1 hφ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((hZmem m).1 hmN.1).2
  have hWCc : actImg hLn W ≤ actImg hLn N₁ := by
    intro φ hφ
    obtain ⟨m, hmW, rfl⟩ := (mem_actImg_iff hLn).1 hφ
    exact (mem_actImg_iff hLn).2 ⟨m, hWN₁ hmW, rfl⟩
  have hWn : ∀ c ∈ actImg hLn N₁, ∀ w ∈ actImg hLn W, c * w * c⁻¹ ∈ actImg hLn W := by
    intro c hc w hw
    obtain ⟨n, hnN, rfl⟩ := (mem_actImg_iff hLn).1 hc
    obtain ⟨m, hmW, rfl⟩ := (mem_actImg_iff hLn).1 hw
    refine (mem_actImg_iff hLn).2 ⟨n * m * n⁻¹, ?_, by simp⟩
    exact TwoThin.pPrimeCoreOf_normalized Zxy hnN.1 hmW
  have hodd : Odd (Nat.card ↥(actImg hLn W)) := by
    have h1 : Nat.card ↥(actImg hLn W) ∣ Nat.card ↥(W.subgroupOf M₀) :=
      Subgroup.card_map_dvd (W.subgroupOf M₀) (Back.actHom hLn)
    have h2 : Nat.card ↥(W.subgroupOf M₀) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
    exact Odd.of_dvd_nat (by rw [h2]; exact TwoThin.card_pPrimeCoreOf_odd Zxy) h1
  have hWbot : actImg hLn W ≠ ⊥ := by
    intro hbot
    apply hWnot
    intro w hw
    have h1 : Back.actHom hLn ⟨w, hWM hw⟩ = 1 := by
      have : Back.actHom hLn ⟨w, hWM hw⟩ ∈ actImg hLn W :=
        (mem_actImg_iff hLn).2 ⟨⟨w, hWM hw⟩, hw, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    exact ⟨hWN hw, TwoThin.mem_normalizer_pPrimeCoreOf (hWN hw),
      fun k hk => (Back.actHom_eq_one_iff_commutator_mem hLn ⟨w, hWM hw⟩).1 h1 k hk⟩
  have hne := pPrimeCoreOf_ne_bot_of_lift hcen hCc hlift hWCc hWn hodd hWbot
  have hy2' : (Back.actHom hLn ⟨y, hyN⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥M₀) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hy2]
      exact pow_orderOf_eq_one y
    rw [this, map_one]
  exact h (kBar K) q hq hL2 (Back.actHom hLn ⟨y, hyN⟩)
    ((MulAut.conj : kBar K →* MulAut (kBar K)).range ⊔ actImg hLn N₁) le_sup_left hy2' hne

omit [Finite G] in
theorem actHom_mem_range_of_mem_sup {y : G} {K : Subgroup G} (hyN : y ∈ normalizer (K : Set G))
    (hyin : y ∈ K ⊔ centralizerSection K (pPrimeCoreOf 2 K)) :
    Back.actHom (hLn_normalizer K) ⟨y, hyN⟩ ∈ (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
  have hLn := hLn_normalizer K
  have hcsn : centralizerSection K (pPrimeCoreOf 2 K) ≤ normalizer (K : Set G) := fun c hc => hc.1
  have hy' : y ∈ ((K ⊔ centralizerSection K (pPrimeCoreOf 2 K) : Subgroup G) : Set G) := hyin
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ hcsn] at hy'
  obtain ⟨k, hk, c, hc, hkc⟩ := hy'
  have hcM : c ∈ normalizer (K : Set G) := hc.1
  have hkM : k ∈ normalizer (K : Set G) := le_normalizer hk
  have hρc : Back.actHom hLn ⟨c, hcM⟩ = 1 :=
    (Back.actHom_eq_one_iff_commutator_mem hLn _).2 fun l hl => hc.2.2 l hl
  have hyeq : (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) = ⟨k, hkM⟩ * ⟨c, hcM⟩ :=
    Subtype.ext hkc.symm
  rw [hyeq, map_mul, hρc, mul_one, Back.actHom_of_mem hLn hk hkM]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem b_ivk_10_2a_of
    (h : B_ivk_10_2L) : B_ivk_10_2a := by
  intro G _ _ _ x y K hV2 hL2
  obtain ⟨p, f, hp, hf, hq, hLie⟩ := hL2
  have hL2' : HasL2Model (kBar K) (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hLie⟩
  intro hyin
  exact (ivk10_bridge h hV2.1 hq hL2').1 (actHom_mem_range_of_mem_sup hV2.1.2.2.2.1 hyin)

end Concrete

end CFSG.GH74.GLS.C3.Layer1.Bk
