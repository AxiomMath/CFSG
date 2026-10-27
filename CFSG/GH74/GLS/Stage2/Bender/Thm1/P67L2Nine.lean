module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2Char
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Char
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.PSL2Table
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped Pointwise MatrixGroups

section Nine

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mem_innDiagSub_of_pow_three (e : K ≃* L2 F) (hq : Nat.card F = 9) {α : MulAut K}
    (hα : α ^ 3 = 1) : α ∈ innDiagSub e := by
  have hDn : (innDiagSub e).Normal := innDiagSub_normal e
  have hΦcard : Nat.card ↥(fieldAutSub e) = 2 := by
    have h1 : Nat.card ↥(fieldAutHom e).range = Nat.card (F ≃+* F) :=
      (Nat.card_congr (MonoidHom.ofInjective (fieldAutHom_injective e)).toEquiv).symm
    change Nat.card ↥(fieldAutHom e).range = 2
    rw [h1]
    exact card_ringAut F 3 2 Nat.prime_three (by rw [hq]; norm_num)
  have hΦ2 : ∀ φ ∈ fieldAutSub e, φ ^ 2 = 1 := by
    intro φ hφ
    have h := pow_card_eq_one' (G := ↥(fieldAutSub e)) (x := ⟨φ, hφ⟩)
    rw [hΦcard] at h
    simpa using congrArg Subtype.val h
  have ha : α ∈ ((innDiagSub e : Set (MulAut K)) * (fieldAutSub e : Set (MulAut K))) := by
    rw [← Subgroup.normal_mul, innDiagSub_sup_fieldAutSub e]
    exact Subgroup.mem_top α
  obtain ⟨d, hd, φ, hφ, rfl⟩ := ha
  have hα' : (d * φ) ^ 3 = 1 := hα
  have hd1 : (QuotientGroup.mk' (innDiagSub e)) d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
  have h1 : (QuotientGroup.mk' (innDiagSub e)) (d * φ) = (QuotientGroup.mk' (innDiagSub e)) φ := by
    rw [map_mul, hd1, one_mul]
  have h2 : ((QuotientGroup.mk' (innDiagSub e)) (d * φ)) ^ 2 = 1 := by
    rw [h1, ← map_pow, hΦ2 φ hφ, map_one]
  have h3 : ((QuotientGroup.mk' (innDiagSub e)) (d * φ)) ^ 3 = 1 := by
    rw [← map_pow, hα', map_one]
  have h4 : (QuotientGroup.mk' (innDiagSub e)) (d * φ) = 1 := by
    have : (QuotientGroup.mk' (innDiagSub e)) (d * φ) =
        ((QuotientGroup.mk' (innDiagSub e)) (d * φ)) ^ 3 *
          (((QuotientGroup.mk' (innDiagSub e)) (d * φ)) ^ 2)⁻¹ := by group
    rw [this, h2, h3]
    simp
  exact (QuotientGroup.eq_one_iff (d * φ)).mp h4

omit [Finite K] in
theorem aut_eq_one_of_fix_unipotent (hF : L2Field F) {r n : ℕ} (hn : Nat.card F = r ^ n)
    (ψ : K ≃* PSL(2, F)) {z : MulAut K} (hcop : Nat.Coprime (orderOf z) r)
    (hzfix : ∀ g : K, ψ g ∈ unipotent F → z g = g) : z = 1 := by
  classical
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd hF.1
  have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have : Fintype F := Fintype.ofFinite F
  have hcardU : Nat.card (unipotent F) = r ^ n := by
    rw [card_unipotent h2', ← Nat.card_eq_fintype_card, hn]
  set z' : MulAut PSL(2, F) := MulAut.congr ψ z with hz'
  have hz'fix : ∀ w ∈ unipotent F, z' w = w := by
    intro w hw
    have := hzfix (ψ.symm w) (by simpa using hw)
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

theorem cf67_L2_nine (hF : L2Field F) (e : K ≃* L2 F) (hq : Nat.card F = 9)
    {V Z : Subgroup (MulAut K)} (h2 : N2Cfg K 3 V Z) : False := by
  classical
  obtain ⟨hrp, hr2, hVe, hVc, -, -, hZcop, hZbot, hVZ⟩ := h2
  have : Fact (Nat.Prime 3) := ⟨hrp⟩
  have := hVe
  have hch : ringChar F = 3 := by
    have hpp : (ringChar F).Prime := by
      have := Fintype.ofFinite F
      have hc : CharP F (ringChar F) := ringChar.charP F
      exact CharP.char_is_prime F _
    have hdvd : ringChar F ∣ 3 ^ 2 := by
      have := ringChar_dvd_card F
      rwa [hq, show (9 : ℕ) = 3 ^ 2 by norm_num] at this
    exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow hdvd)
  have hvpow : ∀ v ∈ V, v ^ 3 = 1 := fun v hv =>
    elemPow_eq_one_of_isElementaryAbelian (A := V) v hv
  have hVinn : ∀ v ∈ V, v ∈ innAut K := fun v hv =>
    mem_innAut_of_odd_pow hF e (mem_innDiagSub_of_pow_three e hq (hvpow v hv)) hr2 (hvpow v hv)
  let E : Subgroup K := V.comap (MulAut.conj : K →* MulAut K)
  have hVE : E.map (MulAut.conj : K →* MulAut K) = V :=
    Subgroup.map_comap_eq_self (fun v hv => hVinn v hv)
  have hEcard : Nat.card E = 9 := by
    have h1 : Nat.card ↥(E.map (MulAut.conj : K →* MulAut K)) = Nat.card E :=
      Subgroup.card_map_of_injective (conj_injective_of_L2 e)
    rw [hVE, hVc] at h1
    rw [← h1]
    norm_num
  obtain ⟨v, hvV, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hcon
    rw [hbot, Subgroup.card_bot] at hVc
    have : 1 < 3 ^ 2 := by norm_num
    omega
  obtain ⟨u, hu⟩ := hVinn v hvV
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hv1 (by rw [← hu, map_one])
  have hur : u ^ 3 = 1 := by
    apply conj_injective_of_L2 e
    rw [map_pow, hu, hvpow v hvV, map_one]
  obtain ⟨n, ψ, hn, hψ⟩ := exists_std_centralizer hF e hrp hch hu1 hur
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd hF.1
  have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have : Fintype F := Fintype.ofFinite F
  have huE : u ∈ E := by
    show MulAut.conj u ∈ V
    rw [hu]
    exact hvV
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h := (IsMulCommutative.is_comm (M := V)).comm ⟨MulAut.conj a, ha⟩ ⟨MulAut.conj b, hb⟩
    have h' : MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a :=
      congrArg Subtype.val h
    apply conj_injective_of_L2 e
    rw [map_mul, map_mul, h']
  let P : Subgroup K := (unipotent F).comap ψ.toMonoidHom
  have hPcard : Nat.card P = 9 := by
    have hP : P = (unipotent F).map ψ.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm ψ _
    rw [hP, Subgroup.card_map_of_injective ψ.symm.injective, card_unipotent h2',
      ← Nat.card_eq_fintype_card, hq]
  have hEP : E ≤ P := fun w hw => (hψ w).mp (hEab w hw u huE)
  have hEeqP : E = P := Subgroup.eq_of_le_of_card_ge hEP (by rw [hPcard, hEcard])
  have hz1 : ∀ z ∈ Z, z = 1 := by
    intro z hz
    have hdvd : orderOf z ∣ Nat.card ↥Z := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
      rwa [Subgroup.orderOf_mk] at this
    refine aut_eq_one_of_fix_unipotent hF hn ψ (Nat.Coprime.coprime_dvd_left hdvd hZcop) ?_
    intro g hg
    have hgE : g ∈ E := by
      rw [hEeqP]
      exact hg
    have hgV : MulAut.conj g ∈ V := hgE
    have hcomm := hVZ _ hgV z hz
    have key : MulAut.conj (z g) = MulAut.conj g := by
      rw [← mulAut_conj_conj z g, ← hcomm]
      group
    exact conj_injective_of_L2 e key
  exact hZbot ((Subgroup.eq_bot_iff_forall Z).mpr hz1)

end Nine

end CFSG.GH74.GLS.Stage2.Bender.Thm1
