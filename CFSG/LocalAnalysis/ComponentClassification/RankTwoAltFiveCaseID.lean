module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseILabel
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIGW

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv Equiv.Perm CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

open IsMulCommutative in
theorem eq_one_of_isMulCommutative {D : Type*} [Group D] [Finite D]
    (hD : commutator D = ⊤) {P : Subgroup D} [IsMulCommutative P] {z : D} (hzc : z ∈ center D)
    (hcop : Nat.Coprime (orderOf z) P.index) : z = 1 := by
  set V : D →* P := (MonoidHom.id P).transfer with hV
  have hV1 : ∀ g, V g = 1 := fun g => by
    have h1 : g ∈ commutator D := hD ▸ mem_top g
    exact Abelianization.commutator_subset_ker V h1
  have hkey : ∀ (k : ℕ) (g₀ : D), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ center D := pow_mem hzc k
    rw [mul_assoc, ← (mem_center_iff.mp hzk g₀), inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id P) z hkey
  rw [hV1] at h1
  have h2 : z ^ P.index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  have h3 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.mp h3

section ActionE

variable {M : Type*} [Group M] {v w : M}

@[expose] def ew (v w : M) (p : ZMod 3 × ZMod 3) : M := v ^ p.1.val * w ^ p.2.val

theorem pow_val_add {u : M} (hu : u ^ 3 = 1) (a b : ZMod 3) :
    u ^ a.val * u ^ b.val = u ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add, pow_eq_pow_mod _ hu]

theorem ew_mul (hvw : Commute v w) (hv : v ^ 3 = 1) (hw : w ^ 3 = 1) (p q : ZMod 3 × ZMod 3) :
    ew v w p * ew v w q = ew v w (p + q) := by
  simp only [ew, Prod.fst_add, Prod.snd_add]
  rw [← pow_val_add hv, ← pow_val_add hw]
  have h : Commute (w ^ p.2.val) (v ^ q.1.val) := (hvw.symm.pow_pow _ _)
  calc v ^ p.1.val * w ^ p.2.val * (v ^ q.1.val * w ^ q.2.val)
      = v ^ p.1.val * (w ^ p.2.val * v ^ q.1.val) * w ^ q.2.val := by group
    _ = v ^ p.1.val * (v ^ q.1.val * w ^ p.2.val) * w ^ q.2.val := by rw [h.eq]
    _ = _ := by group

@[expose] def ewHom (hvw : Commute v w) (hv : v ^ 3 = 1) (hw : w ^ 3 = 1) :
    Multiplicative (ZMod 3 × ZMod 3) →* M where
  toFun p := ew v w p.toAdd
  map_one' := by
    show v ^ (0 : ZMod 3).val * w ^ (0 : ZMod 3).val = 1
    rw [ZMod.val_zero, pow_zero, pow_zero, mul_one]
  map_mul' p q := by
    show ew v w (p * q).toAdd = ew v w p.toAdd * ew v w q.toAdd
    rw [toAdd_mul, ew_mul hvw hv hw]

end ActionE

@[expose] def a6c345 : alternatingGroup (Fin 6) :=
  ⟨swap 3 4 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩

theorem a6c012_comm_a6c345 : a6c012 * a6c345 = a6c345 * a6c012 := by decide

theorem a6c012_pow_three : a6c012 ^ 3 = 1 := by decide

theorem a6c345_pow_three : a6c345 ^ 3 = 1 := by decide

theorem ew_a6_eq_zero : ∀ p : ZMod 3 × ZMod 3, ew a6c012 a6c345 p = 1 → p = 0 := by decide

@[expose] def s9Hom : Multiplicative (ZMod 3 × ZMod 3) →* alternatingGroup (Fin 6) :=
  ewHom a6c012_comm_a6c345 a6c012_pow_three a6c345_pow_three

theorem s9Hom_injective : Function.Injective s9Hom := by
  rw [injective_iff_map_eq_one]
  intro p hp
  exact congrArg Multiplicative.ofAdd (ew_a6_eq_zero p.toAdd hp)

theorem card_range_s9Hom : Nat.card s9Hom.range = 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective s9Hom_injective).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem conj45_a6c345 : conjPerm 6 (swap 4 5) a6c345 = a6c345⁻¹ :=
  Subtype.ext (by rw [conjPerm_apply]; decide)

theorem commutatorElement_central_mul {M : Type*} [Group M] {a b z : M} (hza : z * a = a * z)
    (hzb : z * b = b * z) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have hc : Commute z ⁅a, b⁆ := by
    rw [commutatorElement_def]
    have ha : Commute z a := hza
    have hb : Commute z b := hzb
    exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = (a * z) * b * a⁻¹ * b⁻¹ * z⁻¹ := by group
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by rw [← hza]; group
    _ = a * b * a⁻¹ * b⁻¹ := by
        rw [← commutatorElement_def, hc.eq, mul_inv_cancel_right]

theorem commutatorElement_inv_right_of_commute {M : Type*} [Group M] {a b : M}
    (h : ⁅a, b⁆ * b = b * ⁅a, b⁆) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have h1 : b⁻¹ * ⁅a, b⁆ * b = ⁅a, b⁆ := by
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : b⁻¹ * ⁅a, b⁆⁻¹ * b = ⁅a, b⁆⁻¹ := by
    calc b⁻¹ * ⁅a, b⁆⁻¹ * b = (b⁻¹ * ⁅a, b⁆ * b)⁻¹ := by group
      _ = ⁅a, b⁆⁻¹ := by rw [h1]
  rw [← h2, commutatorElement_def, commutatorElement_def]
  group

namespace CaseICoords

variable {A B R T : Subgroup G} (c : CaseICoords A B R T)

@[expose] def D : Subgroup G := B ⊔ c.Bx

theorem D_le_H : c.D ≤ c.H := sup_le c.B_le_H c.Bx_le_H

omit [Finite G] in
theorem x_mul_self : c.x * c.x = 1 := by
  rw [x, ← Subgroup.coe_mul, ← map_mul, show x0 * x0 = 1 by decide, map_one, Subgroup.coe_one]

omit [Finite G] in
theorem x_inv : c.x⁻¹ = c.x := inv_eq_of_mul_eq_one_right c.x_mul_self

theorem x_mem_normalizer_D : c.x ∈ normalizer (c.D : Set G) := by
  refine RankTwoAlt.mem_normalizer_of_conj_le fun d hd => ?_
  have h : c.D ≤ (c.D).comap (MulAut.conj c.x).toMonoidHom := by
    refine sup_le (fun b hb => ?_) ?_
    · exact mem_comap.mpr (mem_sup_right ⟨b, hb, rfl⟩)
    · rintro _ ⟨b, hb, rfl⟩
      refine mem_comap.mpr (mem_sup_left ?_)
      show c.x * (c.x * b * c.x⁻¹) * c.x⁻¹ ∈ B
      rw [c.x_inv]
      have : c.x * (c.x * b * c.x) * c.x = (c.x * c.x) * b * (c.x * c.x) := by group
      rw [this, c.x_mul_self, one_mul, mul_one]
      exact hb
  exact h hd

theorem x_mem_normalizer_O : c.x ∈ normalizer (c.O : Set G) :=
  mem_normalizer_of_map_conj_eq (map_conj_map_subtype_of_characteristic _ c.x_mem_normalizer)

theorem O_le_centralizer_Bx : c.O ≤ centralizer (c.Bx : Set G) := by
  intro o ho
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have ho' : c.x⁻¹ * o * c.x⁻¹⁻¹ ∈ c.O :=
    (mem_normalizer_iff.mp (inv_mem c.x_mem_normalizer_O) o).mp ho
  rw [inv_inv] at ho'
  have h1 := mem_centralizer_iff.mp (c.O_le_centralizer ho') b hb
  show c.x * b * c.x⁻¹ * o = o * (c.x * b * c.x⁻¹)
  calc c.x * b * c.x⁻¹ * o = c.x * (b * (c.x⁻¹ * o * c.x)) * c.x⁻¹ := by group
    _ = c.x * ((c.x⁻¹ * o * c.x) * b) * c.x⁻¹ := by rw [h1]
    _ = o * (c.x * b * c.x⁻¹) := by group

theorem O_le_centralizer_D : c.O ≤ centralizer (c.D : Set G) := by
  intro o ho
  have h1 : B ≤ centralizer ({o} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (c.O_le_centralizer ho) b hb)
  have h2 : c.Bx ≤ centralizer ({o} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (c.O_le_centralizer_Bx ho) b hb)
  rw [mem_centralizer_iff]
  intro d hd
  exact (mem_centralizer_singleton_iff.mp ((sup_le h1 h2) hd))

omit [Finite G] in
theorem commutator_eq_self_of_equiv {M : Subgroup G} (e : M ≃* A5) : ⁅M, M⁆ = M := by
  have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup M := e.isSimpleGroup
  have hc : commutator M = ⊤ := by
    rcases (inferInstance : (commutator M).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      have hmem : ⁅e.symm k1, e.symm y0⁆ ∈ commutator M := by
        rw [commutator_def]
        exact commutator_mem_commutator (mem_top _) (mem_top _)
      rw [h, mem_bot] at hmem
      exact commutatorElement_k1_y0_ne_one
        (e.symm.injective (by rw [map_commutatorElement, hmem, map_one]))
    · exact h
  rw [← M.map_subtype_commutator, hc, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
theorem commutator_D : commutator c.D = ⊤ := by
  have hB := commutator_eq_self_of_equiv c.ψB.symm
  have hBx := commutator_eq_self_of_equiv c.equivBx
  have hle : c.D ≤ ⁅c.D, c.D⁆ := by
    refine sup_le ?_ ?_
    · calc B = ⁅B, B⁆ := hB.symm
        _ ≤ ⁅c.D, c.D⁆ := commutator_mono le_sup_left le_sup_left
    · calc c.Bx = ⁅c.Bx, c.Bx⁆ := hBx.symm
        _ ≤ ⁅c.D, c.D⁆ := commutator_mono le_sup_right le_sup_right
  apply map_injective c.D.subtype_injective
  rw [c.D.map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact le_antisymm (commutator_le_self _) hle

theorem map_D_surjective (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) :
    Function.Surjective (c.barOf c.D_le_H) := by
  obtain ⟨θ0⟩ := hA6
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup c.Hbar := θ0.isSimpleGroup
  have hQcard : Nat.card c.Hbar = 360 := by rw [Nat.card_congr θ0.toEquiv, card_alt6]
  rw [← MonoidHom.range_eq_top]
  set M := (c.barOf c.D_le_H).range with hM
  have hBM : (c.barOf c.B_le_H).range ≤ M := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, mem_sup_left b.2⟩, rfl⟩
  have hBxM : (c.barOf c.Bx_le_H).range ≤ M := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, mem_sup_right b.2⟩, rfl⟩
  have hne : M ≠ (c.barOf c.B_le_H).range := fun h => c.false_of_range_le (h ▸ hBxM)
  have h60 : 60 ∣ Nat.card M := c.card_range_B ▸ Subgroup.card_dvd_of_le hBM
  have hgt : 60 < Nat.card M := by
    have hle := Subgroup.card_le_of_le hBM
    rw [c.card_range_B] at hle
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (eq_of_le_of_card_ge hBM (by rw [c.card_range_B, h])).symm hne
  by_contra htop
  have hi := M.card_mul_index
  rw [hQcard] at hi
  obtain ⟨k, hk⟩ := h60
  have hidx : M.index ≤ 3 := by
    rw [hk] at hi hgt
    have : 2 ≤ k := by omega
    have h1 : 60 * k * M.index ≤ 360 := le_of_eq hi
    nlinarith
  have hinj := CFSG.Sporadic.Recognition.JankoWong.PSLNineStep.injective_toPermHom_of_ne_top htop
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hQcard, Nat.card_perm, ← index_eq_card] at hle
  have : (M.index).factorial ≤ 6 := by
    calc (M.index).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hidx
      _ = 6 := rfl
  omega

theorem ker_le_center : (c.barOf c.D_le_H).ker ≤ center c.D := by
  intro d hd
  rw [MonoidHom.mem_ker, barOf_apply, c.mk_eq_one_iff] at hd
  rw [mem_center_iff]
  intro g
  exact Subtype.ext ((mem_centralizer_iff.mp (c.O_le_centralizer_D hd)) g g.2)

theorem odd_card_ker : Odd (Nat.card (c.barOf c.D_le_H).ker) := by
  set f : (c.barOf c.D_le_H).ker →* c.O :=
    (c.D.subtype.comp (c.barOf c.D_le_H).ker.subtype).codRestrict c.O fun d =>
      (c.mk_eq_one_iff ⟨d, c.D_le_H (d : c.D).2⟩).mp d.2 with hf
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  exact c.odd_card_O.of_dvd_nat (Subgroup.card_dvd_of_injective f hinj)

theorem card_ker_dvd_six
    (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) :
    Nat.card (c.barOf c.D_le_H).ker ∣ 6 := by
  obtain ⟨θ⟩ := hA6
  have : Group.IsPerfect c.D := ⟨c.commutator_D⟩
  set q := θ.toMonoidHom.comp (c.barOf c.D_le_H) with hq
  have hqs : Function.Surjective q := θ.surjective.comp (c.map_D_surjective ⟨θ⟩)
  have hker : q.ker = (c.barOf c.D_le_H).ker := by
    ext d
    simp [hq, MonoidHom.mem_ker]
  have hqc : q.ker ≤ center c.D := hker ▸ c.ker_le_center
  have hM := Alternating.Multipliers.hopfMultiplier_alternatingGroup_six
  have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) :=
    Nat.finite_of_card_ne_zero (by rw [hM.2]; norm_num)
  have hs := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs hqc
  have hd := Subgroup.card_range_dvd (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hqs hqc)
  rw [MonoidHom.range_eq_top.mpr hs, card_top, hM.2, hker] at hd
  exact hd

theorem card_ker_dvd_three
    (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) :
    Nat.card (c.barOf c.D_le_H).ker ∣ 3 := by
  have hodd := c.odd_card_ker
  have h6 : Nat.card (c.barOf c.D_le_H).ker ∈ Nat.divisors 6 :=
    Nat.mem_divisors.mpr ⟨c.card_ker_dvd_six hA6, by norm_num⟩
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at h6
  simp only [Finset.mem_insert, Finset.mem_singleton] at h6
  rcases h6 with h' | h' | h' | h'
  · exact h' ▸ one_dvd 3
  · rw [h'] at hodd
    exact absurd hodd (by decide)
  · exact h' ▸ dvd_rfl
  · rw [h'] at hodd
    exact absurd hodd (by decide)

@[expose] def vB : G := (c.ψB y0 : G)

omit [Finite G] in
theorem vB_mem_B : c.vB ∈ B := (c.ψB y0).2

omit [Finite G] in
theorem vB_mem_D : c.vB ∈ c.D := mem_sup_left c.vB_mem_B

theorem vB_mem_centralizer : c.vB ∈ centralizer (A : Set G) :=
  c.pair.inf_normalizer_le (c.psiB_mem_normalizer y0_norm)

theorem x_comm_vB : c.x * c.vB = c.vB * c.x :=
  mem_centralizer_iff.mp c.vB_mem_centralizer c.x c.x_mem

omit [Finite G] in
theorem w_mem_O : c.w ∈ c.O := by
  have hwH : c.w ∈ c.H := mem_centralizer_singleton_iff.mpr rfl
  have hle : (zpowers (⟨c.w, hwH⟩ : c.H)) ≤ CFSG.pPrimeCore 2 c.H := by
    refine le_sSup ⟨⟨fun n hn g => ?_⟩, ?_⟩
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      have hg : (g : G) * c.w = c.w * g := mem_centralizer_singleton_iff.mp g.2
      have : g * (⟨c.w, hwH⟩ : c.H) * g⁻¹ = ⟨c.w, hwH⟩ := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hg, mul_inv_cancel_right])
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, this]
      exact mem_zpowers_iff.mpr ⟨k, rfl⟩
    · rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_eq_prime c.w_pow_three (fun h => by
        have := congrArg c.ψA.symm (Subtype.ext h : (c.ψA y0 : A) = 1)
        rw [MulEquiv.symm_apply_apply, map_one] at this
        exact absurd this (by decide))]
      norm_num
  exact ⟨⟨c.w, hwH⟩, hle (mem_zpowers _), rfl⟩

omit [Finite G] in
theorem orderOf_w : orderOf c.w = 3 := by
  refine orderOf_eq_prime c.w_pow_three fun h => ?_
  have := congrArg c.ψA.symm (Subtype.ext h : (c.ψA y0 : A) = 1)
  rw [MulEquiv.symm_apply_apply, map_one] at this
  exact absurd this (by decide)

omit [Finite G] in
theorem w_mem_zpowers_of_pow_ne_one {i : ℕ} (hi : c.w ^ i ≠ 1) :
    c.w ∈ zpowers (c.w ^ i) := by
  have h3 := c.orderOf_w
  have hi3 : i % 3 = 1 ∨ i % 3 = 2 := by
    rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
    · exact absurd (by rw [← pow_mod_orderOf, h3, h, pow_zero]) hi
    · exact Or.inl h
    · exact Or.inr h
  rcases hi3 with h | h
  · exact mem_zpowers_iff.mpr ⟨1, by rw [zpow_one, ← pow_mod_orderOf, h3, h, pow_one]⟩
  · refine mem_zpowers_iff.mpr ⟨2, ?_⟩
    rw [zpow_two, ← pow_add, ← pow_mod_orderOf, h3]
    have : (i + i) % 3 = 1 := by omega
    rw [this, pow_one]

variable {c}
variable {θ : c.Hbar ≃* alternatingGroup (Fin 6)}
  (hθ : ∀ σ : A5, θ (c.barOf c.B_le_H (c.ψB σ)) = ι56 σ)
include hθ

theorem theta_vB : θ (c.barOf c.D_le_H ⟨c.vB, c.vB_mem_D⟩) = a6c012 := by
  rw [← ι56_y0, ← hθ]
  rfl

theorem commutator_mem_ker {h : c.D} (hh : θ (c.barOf c.D_le_H h) = a6c345) :
    ⁅(⟨c.vB, c.vB_mem_D⟩ : c.D), h⁆ ∈ (c.barOf c.D_le_H).ker := by
  rw [MonoidHom.mem_ker]
  apply θ.injective
  rw [map_commutatorElement, map_commutatorElement, theta_vB hθ, hh, map_one,
    commutatorElement_eq_one_iff_mul_comm, a6c012_comm_a6c345]

theorem x_conj_mul_mem_O {h : c.D} (hh : θ (c.barOf c.D_le_H h) = a6c345) :
    c.x * (h : G) * c.x⁻¹ * h ∈ c.O := by
  have hxh : c.x * (h : G) * c.x⁻¹ ∈ c.H :=
    (mem_normalizer_iff.mp c.x_mem_normalizer h).mp (c.D_le_H h.2)
  have h1 : ((⟨c.x * (h : G) * c.x⁻¹, hxh⟩ : c.H) : c.Hbar) =
      quotAut ⟨c.x, c.x_mem_normalizer⟩ (c.barOf c.D_le_H h) := rfl
  have h2 : θ ((⟨c.x * (h : G) * c.x⁻¹, hxh⟩ : c.H) : c.Hbar) = a6c345⁻¹ := by
    rw [h1, c.label_x hθ, hh, conj45_a6c345]
  have hmem : c.x * (h : G) * c.x⁻¹ * h ∈ c.H := mul_mem hxh (c.D_le_H h.2)
  have h3 : ((⟨c.x * (h : G) * c.x⁻¹ * h, hmem⟩ : c.H) : c.Hbar) = 1 := by
    apply θ.injective
    have : (⟨c.x * (h : G) * c.x⁻¹ * h, hmem⟩ : c.H) =
        ⟨c.x * (h : G) * c.x⁻¹, hxh⟩ * ⟨h, c.D_le_H h.2⟩ := rfl
    rw [this, QuotientGroup.mk_mul, map_mul, h2, map_one]
    have : θ ((⟨h, c.D_le_H h.2⟩ : c.H) : c.Hbar) = a6c345 := hh
    rw [this, inv_mul_cancel]
  exact (c.mk_eq_one_iff _).mp h3

theorem x_conj_commutator {h : c.D} (hh : θ (c.barOf c.D_le_H h) = a6c345) :
    c.x * ⁅c.vB, (h : G)⁆ * c.x⁻¹ = ⁅c.vB, (h : G)⁆⁻¹ := by
  set z := c.x * (h : G) * c.x⁻¹ * h with hz
  have hzO := x_conj_mul_mem_O hθ hh
  have hzc : ∀ d ∈ c.D, z * d = d * z := fun d hd =>
    ((mem_centralizer_iff.mp (c.O_le_centralizer_D hzO)) d hd).symm
  have hcm := commutator_mem_ker hθ hh
  rw [MonoidHom.mem_ker, barOf_apply, c.mk_eq_one_iff] at hcm
  have hcc : ⁅c.vB, (h : G)⁆ * h = h * ⁅c.vB, (h : G)⁆ :=
    ((mem_centralizer_iff.mp (c.O_le_centralizer_D hcm)) h h.2).symm
  have hxh : c.x * (h : G) * c.x⁻¹ = z * (h : G)⁻¹ := by rw [hz]; group
  have hxv : c.x * c.vB * c.x⁻¹ = c.vB := by rw [c.x_comm_vB, mul_inv_cancel_right]
  have h1 : c.x * ⁅c.vB, (h : G)⁆ * c.x⁻¹ = ⁅c.x * c.vB * c.x⁻¹, c.x * (h : G) * c.x⁻¹⁆ := by
    rw [← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply]
  rw [h1, hxv, hxh, commutatorElement_central_mul (hzc _ c.vB_mem_D) (hzc _ (inv_mem h.2)),
    commutatorElement_inv_right_of_commute hcc]

theorem exists_commutator_eq_w_pow {h : c.D} (hh : θ (c.barOf c.D_le_H h) = a6c345) :
    ∃ i : ℕ, ⁅c.vB, (h : G)⁆ = c.w ^ i := by
  set c₀ := ⁅c.vB, (h : G)⁆ with hc₀
  have hc0O : c₀ ∈ c.O := by
    have h1 := commutator_mem_ker hθ hh
    rw [MonoidHom.mem_ker, barOf_apply, c.mk_eq_one_iff] at h1
    exact h1
  obtain ⟨s, hs, hs1, -, -, -⟩ := c.exists_mem_R
  have hc0s : c₀ * s = s * c₀ :=
    ((mem_centralizer_iff.mp (c.O_le_centralizer hc0O)) s (c.pair.R_le hs)).symm
  have hodd : Odd (orderOf c₀) := by
    have h1 : orderOf c₀ ∣ Nat.card c.O := by
      rw [← Subgroup.orderOf_mk c₀ hc0O]
      exact orderOf_dvd_natCard _
    exact c.odd_card_O.of_dvd_nat h1
  obtain ⟨i, hi⟩ := c.exists_mem_of_odd hs hs1 (c.O_le_H hc0O) hc0s hodd
  set k := (c.w ^ i)⁻¹ * c₀ with hk
  have hkA : k ∈ centralizer (A : Set G) := (mem_inf.mp hi).1
  have hxk : c.x * k * c.x⁻¹ = k := by
    rw [mem_centralizer_iff.mp hkA c.x c.x_mem, mul_inv_cancel_right]
  have hwk : c.w * k = k * c.w := (mem_centralizer_iff.mp hkA c.w c.w_mem)
  have hxw : c.x * c.w ^ i * c.x⁻¹ = (c.w ^ i)⁻¹ := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, c.x_conj_w, inv_pow]
  have hinv := x_conj_commutator hθ hh
  rw [← hc₀] at hinv
  have hc0 : c₀ = c.w ^ i * k := by rw [hk]; group
  have hk2 : k * k = 1 := by
    have hwik : Commute (c.w ^ i) k := Commute.pow_left hwk i
    have h1 : c.x * c₀ * c.x⁻¹ = (c.w ^ i)⁻¹ * k := by
      rw [hc0, show c.x * (c.w ^ i * k) * c.x⁻¹ = (c.x * c.w ^ i * c.x⁻¹) * (c.x * k * c.x⁻¹) by
        group, hxw, hxk]
    have h2 : c₀⁻¹ = (c.w ^ i)⁻¹ * k⁻¹ := by
      rw [hc0, mul_inv_rev, hwik.inv_inv.eq]
    rw [hinv, h2] at h1
    have h3 : k⁻¹ = k := mul_left_cancel h1
    have h4 := inv_mul_cancel k
    rwa [h3] at h4
  have hkodd : Odd (orderOf k) := by
    have hkK0 : k ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G) := hi
    have h1 : orderOf k ∣ Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) :
        Subgroup G) := by
      rw [← Subgroup.orderOf_mk k hkK0]
      exact orderOf_dvd_natCard _
    exact c.pair.odd_card_inf.of_dvd_nat h1
  have hk1 : k = 1 := by
    have hd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hk2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h' | h'
    · exact orderOf_eq_one_iff.mp h'
    · rw [h'] at hkodd
      exact absurd hkodd (by decide)
  exact ⟨i, by rw [hc0, hk1, mul_one]⟩

theorem commutator_ne_one
    (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) {h : c.D}
    (hh : θ (c.barOf c.D_le_H h) = a6c345) (hZ : (c.barOf c.D_le_H).ker ≠ ⊥) :
    ⁅c.vB, (h : G)⁆ ≠ 1 := by
  intro hc
  set q : c.D →* alternatingGroup (Fin 6) := θ.toMonoidHom.comp (c.barOf c.D_le_H) with hq
  have hqs : Function.Surjective q := θ.surjective.comp (c.map_D_surjective hA6)
  have hker : q.ker = (c.barOf c.D_le_H).ker := by
    ext d
    simp [hq, MonoidHom.mem_ker]
  set v' : c.D := ⟨c.vB, c.vB_mem_D⟩ with hv'
  have hvh : v' * h = h * v' := by
    have : ⁅v', h⁆ = 1 := Subtype.ext hc
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hqv : q v' = a6c012 := theta_vB hθ
  have hqh : q h = a6c345 := hh
  set P := s9Hom.range.comap q with hP
  have hform : ∀ p ∈ P, ∃ i j : ℕ, ∃ zz ∈ center c.D, p = v' ^ i * h ^ j * zz := by
    intro p hp
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp (mem_comap.mp hp)
    refine ⟨r.toAdd.1.val, r.toAdd.2.val, (v' ^ r.toAdd.1.val * h ^ r.toAdd.2.val)⁻¹ * p, ?_,
      by group⟩
    have hmem : (v' ^ r.toAdd.1.val * h ^ r.toAdd.2.val)⁻¹ * p ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_pow, map_pow, hqv, hqh, ← hr]
      exact inv_mul_cancel _
    exact c.ker_le_center (hker ▸ hmem)
  have hcomm : IsMulCommutative P := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, j, z₁, hz₁, ha⟩ := hform a a.2
    obtain ⟨k, l, z₂, hz₂, hb⟩ := hform b b.2
    simp only [Subgroup.coe_mul]
    rw [ha, hb]
    have hvh' : Commute v' h := hvh
    have h1 : Commute (v' ^ i * h ^ j) (v' ^ k * h ^ l) :=
      (((Commute.refl v').pow_pow i k).mul_right (hvh'.pow_pow i l)).mul_left
        ((hvh'.symm.pow_pow j k).mul_right ((Commute.refl h).pow_pow j l))
    have hz₁c : ∀ g, Commute z₁ g := fun g => (mem_center_iff.mp hz₁ g).symm
    have hz₂c : ∀ g, Commute z₂ g := fun g => (mem_center_iff.mp hz₂ g).symm
    exact ((h1.mul_right (hz₂c _).symm).mul_left (hz₁c _)).eq
  have hidx : P.index = 40 := by
    rw [hP, Subgroup.index_comap_of_surjective _ hqs]
    have := s9Hom.range.card_mul_index
    rw [card_range_s9Hom, card_alt6] at this
    omega
  obtain ⟨⟨z, hzK⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1' : z ≠ 1 := fun h' => hz1 (Subtype.ext h')
  have hzc : z ∈ center c.D := c.ker_le_center hzK
  have h3 : orderOf z ∣ 3 := by
    have hd : orderOf z ∣ Nat.card (c.barOf c.D_le_H).ker := by
      rw [← Subgroup.orderOf_mk z hzK]
      exact orderOf_dvd_natCard _
    exact hd.trans (c.card_ker_dvd_three hA6)
  have hcop : Nat.Coprime (orderOf z) P.index := by
    rw [hidx]
    exact Nat.Coprime.coprime_dvd_left h3 (by norm_num)
  exact hz1' (eq_one_of_isMulCommutative c.commutator_D hzc hcop)

theorem map_D_injective_of_not_mem
    (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) (hw : c.w ∉ c.D) :
    Function.Injective (c.barOf c.D_le_H) := by
  by_contra hninj
  have hZ : (c.barOf c.D_le_H).ker ≠ ⊥ := fun h => hninj ((MonoidHom.ker_eq_bot_iff _).mp h)
  obtain ⟨h, hh⟩ := c.map_D_surjective hA6 (θ.symm a6c345)
  have hh' : θ (c.barOf c.D_le_H h) = a6c345 := by rw [hh, MulEquiv.apply_symm_apply]
  have hne := commutator_ne_one hθ hA6 hh' hZ
  obtain ⟨i, hi⟩ := exists_commutator_eq_w_pow hθ hh'
  rw [hi] at hne
  have hmem : ⁅c.vB, (h : G)⁆ ∈ c.D := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem c.vB_mem_D h.2) (inv_mem c.vB_mem_D)) (inv_mem h.2)
  rw [hi] at hmem
  exact hw ((zpowers_le.mpr hmem) (c.w_mem_zpowers_of_pow_ne_one hne))

theorem commutator_eq_of_mem
    (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) (hw : c.w ∈ c.D) {h : c.D}
    (hh : θ (c.barOf c.D_le_H h) = a6c345) :
    ⁅c.vB, (h : G)⁆ = c.w ∨ ⁅c.vB, (h : G)⁆ = c.w⁻¹ := by
  have hZ : (c.barOf c.D_le_H).ker ≠ ⊥ := by
    intro hbot
    have hmem : (⟨c.w, hw⟩ : c.D) ∈ (c.barOf c.D_le_H).ker := by
      rw [MonoidHom.mem_ker, barOf_apply, c.mk_eq_one_iff]
      exact c.w_mem_O
    rw [hbot, mem_bot] at hmem
    have h1 : c.w = 1 := congrArg Subtype.val hmem
    have := congrArg c.ψA.symm (Subtype.ext h1 : (c.ψA y0 : A) = 1)
    rw [MulEquiv.symm_apply_apply, map_one] at this
    exact absurd this (by decide)
  have hne := commutator_ne_one hθ hA6 hh hZ
  obtain ⟨i, hi⟩ := exists_commutator_eq_w_pow hθ hh
  rw [hi] at hne ⊢
  have h3 := c.orderOf_w
  rw [← pow_mod_orderOf, h3] at hne ⊢
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · rw [h, pow_zero] at hne
    exact absurd rfl hne
  · left
    rw [h, pow_one]
  · right
    rw [h, eq_inv_iff_mul_eq_one, ← pow_succ, c.w_pow_three]

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive
