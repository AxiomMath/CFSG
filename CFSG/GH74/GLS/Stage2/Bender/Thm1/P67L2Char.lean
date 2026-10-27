module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Char
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.PSL2Table
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped Pointwise MatrixGroups

section Inner

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem center_eq_bot_of_L2 (e : K ≃* L2 F) : Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  apply conj_injective_of_L2 e
  rw [map_one]
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply]
  have h := Subgroup.mem_center_iff.mp hc x
  rw [← h]
  exact mul_inv_cancel_right x c

theorem mem_innAut_of_odd_pow (hF : L2Field F) (e : K ≃* L2 F) {α : MulAut K}
    (hα : α ∈ innDiagSub e) {m : ℕ} (hm : Odd m) (hαm : α ^ m = 1) : α ∈ innAut K := by
  have hidx : ((innAut K).subgroupOf (innDiagSub e)).index = 2 := innAut_relIndex_two e hF
  set I : Subgroup ↥(innDiagSub e) := (innAut K).subgroupOf (innDiagSub e) with hI
  set a : ↥(innDiagSub e) := ⟨α, hα⟩ with ha
  obtain ⟨k, hk⟩ := hm
  have ham : a ^ m = 1 := Subtype.ext (by simpa using hαm)
  have hsq : a * a ∈ I := (Subgroup.mul_mem_iff_of_index_two hidx).mpr Iff.rfl
  have h1 : (a * a) ^ k * a ∈ I := by
    have : (a * a) ^ k * a = a ^ m := by
      rw [hk, pow_succ, pow_mul, sq]
    rw [this, ham]
    exact one_mem _
  have h2 := (Subgroup.mul_mem_iff_of_index_two hidx).mp h1
  exact (Subgroup.mem_subgroupOf.mp (h2.mp (pow_mem hsq k)))

theorem exists_ne_one_inn_of_elem (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} (hr : r.Prime)
    (hr2 : Odd r) {V : Subgroup (MulAut K)} (hVe : IsElementaryAbelian r ↥V)
    (hVc : Nat.card ↥V = r ^ 2) : ∃ v ∈ V, v ≠ 1 ∧ v ∈ innAut K := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have := hVe
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 2 hr.ne_zero)
  by_contra hcon
  push Not at hcon
  have hDn : (innDiagSub e).Normal := innDiagSub_normal e
  let f : ↥V →* (MulAut K ⧸ innDiagSub e) := (QuotientGroup.mk' (innDiagSub e)).comp V.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    by_contra hv1
    have hvD : (v : MulAut K) ∈ innDiagSub e := (QuotientGroup.eq_one_iff _).mp hv
    have hvr : (v : MulAut K) ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian (A := V) _ v.2
    exact hcon v v.2 (fun h => hv1 (Subtype.ext h)) (mem_innAut_of_odd_pow hF e hvD hr2 hvr)
  have : IsCyclic ↥(fieldAutSub e) := isCyclic_fieldAutSub e
  have : IsCyclic (MulAut K ⧸ innDiagSub e) := by
    refine isCyclic_of_surjective
      ((QuotientGroup.mk' (innDiagSub e)).comp (fieldAutSub e).subtype) ?_
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ ((innDiagSub e : Set (MulAut K)) * (fieldAutSub e : Set (MulAut K))) := by
      rw [← Subgroup.normal_mul, innDiagSub_sup_fieldAutSub e]
      exact Subgroup.mem_top a
    obtain ⟨d, hd, φ, hφ, rfl⟩ := ha
    refine ⟨⟨φ, hφ⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype,
      QuotientGroup.mk_mul]
    rw [(QuotientGroup.eq_one_iff d).mpr hd, one_mul]
  have : IsCyclic ↥V := isCyclic_of_injective f hf
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hVc this

end Inner

section Char

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem exists_std_centralizer (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} (hr : r.Prime)
    (hrF : ringChar F = r) {u : K} (hu1 : u ≠ 1) (hur : u ^ r = 1) :
    ∃ (n : ℕ) (ψ : K ≃* PSL(2, F)), Nat.card F = r ^ n ∧
      ∀ g : K, g * u = u * g ↔ ψ g ∈ unipotent F := by
  classical
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd hF.1
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hY : IsPGroup r ↥(Subgroup.zpowers u) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hur).isPGroup r _
  have hrdvd : r ∣ Nat.card F := hrF ▸ ringChar_dvd_card F
  obtain ⟨n, ψ, hn, hYU⟩ := exists_std_position e hr hrdvd (Subgroup.zpowers u) hY
  have hx : ψ u ∈ unipotent F := hYU ⟨u, Subgroup.mem_zpowers u, rfl⟩
  have hx1 : ψ u ≠ 1 := fun h => hu1 (ψ.injective (by rw [h, map_one]))
  refine ⟨n, ψ, hn, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · have hfix : ψ g * ψ u * (ψ g)⁻¹ = ψ u := by
      rw [← map_mul, ← map_inv, ← map_mul, hg]
      simp
    have hB : ψ g ∈ borel F :=
      (unipotent_conj_mem_iff h2 hx hx1 (ψ g)).mp (by rw [hfix]; exact hx)
    by_contra hgU
    obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists (ψ u)).mp hx
    have ht0 : t ≠ 0 := fun h0 => hx1 (by rw [ht, h0, mk_unip_eq_one_iff h2 0 |>.mpr rfl])
    exact borel_not_fix_unip h2 hB hgU ht0 (by rw [← ht]; exact hfix)
  · have hcomm := unipotent_mul_comm hg hx
    apply ψ.injective
    rw [map_mul, map_mul, hcomm]

end Char

section Main

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem cf67_L2_char (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} {V Z : Subgroup (MulAut K)}
    (h2 : N2Cfg K r V Z) (h3 : N3Full K V Z) (hr : ringChar F = r) : False := by
  classical
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_L2 e
  have h2s := h2
  obtain ⟨hrp, hr2, hVe, hVc, -, -, -, -, hVZ⟩ := h2
  have : Fact r.Prime := ⟨hrp⟩
  have := hVe
  obtain ⟨v, hvV, hv1, u, hu⟩ := exists_ne_one_inn_of_elem hF e hrp hr2 hVe hVc
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hv1 (by rw [← hu, map_one])
  have hvr : v ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian (A := V) v hvV
  have hur : u ^ r = 1 := by
    apply conj_injective_of_L2 e
    rw [map_pow, hu, hvr, map_one]
  obtain ⟨n, ψ, hn, hψ⟩ := exists_std_centralizer hF e hrp hr hu1 hur
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd hF.1
  have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have : Fintype F := Fintype.ofFinite F
  have hcardU : Nat.card (unipotent F) = r ^ n := by
    rw [card_unipotent h2', ← Nat.card_eq_fintype_card, hn]
  have hfix : ∀ g : K, g ∈ fixSub v ↔ ψ g ∈ unipotent F := by
    intro g
    rw [← hψ g, mem_fixSub, ← hu, MulAut.conj_apply]
    constructor
    · intro h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    · intro h
      exact mul_inv_eq_iff_eq_mul.mpr h.symm
  have hQp : IsPGroup r ↥(fixSub v) := by
    have hUp : IsPGroup r ↥(unipotent F) := IsPGroup.of_card hcardU
    let f : ↥(fixSub v) →* ↥(unipotent F) :=
      ((ψ : K →* PSL(2, F)).comp (fixSub v).subtype).codRestrict (unipotent F)
        (fun g => (hfix g.1).mp g.2)
    exact hUp.of_injective f (fun a b hab => Subtype.ext (ψ.injective (congrArg Subtype.val hab)))
  have hQinv : ∀ z ∈ Z, ∀ c ∈ fixSub v, z c ∈ fixSub v := by
    intro z hz c hc
    rw [mem_fixSub] at hc ⊢
    have hvz := hVZ v hvV z hz
    calc v (z c) = (v * z) c := rfl
      _ = (z * v) c := by rw [hvz]
      _ = z (v c) := rfl
      _ = z c := by rw [hc]
  have hR : ∀ z : MulAut K, Odd (orderOf z) → Nat.Coprime (orderOf z) r →
      (∀ c ∈ fixSub v, z c = c) → z = 1 := by
    intro z _ hcop hzfix
    set z' : MulAut PSL(2, F) := MulAut.congr ψ z with hz'
    have hz'fix : ∀ w ∈ unipotent F, z' w = w := by
      intro w hw
      have hc : ψ.symm w ∈ fixSub v := (hfix _).mpr (by simpa using hw)
      have := hzfix _ hc
      change ψ (z (ψ.symm w)) = w
      rw [this]
      simp
    obtain ⟨w, hw, hzw⟩ := CFSG.AGLEmbedding.exists_eq_conj_of_forall_unipotent h2' z' hz'fix
    have hzc : z = MulAut.conj (ψ.symm w) := by
      apply (MulAut.congr ψ).injective
      change z' = MulAut.congr ψ (MulAut.conj (ψ.symm w))
      rw [hzw]
      ext y
      simp [MulAut.conj_apply, MulAut.congr_apply]
    have hwr : orderOf w ∣ r ^ n := by
      have h1 : orderOf w ∣ Nat.card (unipotent F) := by
        have := orderOf_dvd_natCard (⟨w, hw⟩ : unipotent F)
        rwa [Subgroup.orderOf_mk] at this
      rwa [hcardU] at h1
    have hord : orderOf z ∣ r ^ n := by
      rw [hzc]
      refine (orderOf_map_dvd (MulAut.conj : K →* MulAut K) _).trans ?_
      rw [MulEquiv.orderOf_eq]
      exact hwr
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop) hord)
  exact false_of_rstep hcen h2s h3 hvV hv1 (Q := fixSub v) le_rfl hQp hQinv hR

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
