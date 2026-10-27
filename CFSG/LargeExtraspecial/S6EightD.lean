module

public import CFSG.LargeExtraspecial.S6EightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Vt_le_clSub_of_conj (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hF : FusionCtl S g) {t : S.O} {ht : t ∈ S.Lbar g} (ht1 : t ≠ 1) (hL : LinCase S g ht)
    {τ : S.M} (hτ : S.ρ τ = t) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u) (hβ : ∃ q ∈ S.QG, q * (τ : G) * q⁻¹ = (τ : G) * S.z) :
    Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa u) := by
  by_contra hVP
  have hU8 := inf_commSpace_le_Vt ht1 hτ hτu hF hβ
  have hU8lt : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa u) ⊓
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) < finrank (ZMod 2) (Vt S g t) := by
    have hle : S.clSub (S.QG ⊓ S.Qa u) ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        Vt S g t ⊓ S.clSub (S.QG ⊓ S.Qa u) := le_inf hU8 inf_le_left
    have hlt : Vt S g t ⊓ S.clSub (S.QG ⊓ S.Qa u) < Vt S g t :=
      lt_of_le_of_ne inf_le_left fun h => hVP (h ▸ inf_le_right)
    exact (Submodule.finrank_mono hle).trans_lt (Submodule.finrank_lt_finrank_of_lt hlt)
  have hP4 := finrank_clSub_le H ht ht1 hτ hτu
  have hpm : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u)) ≤ finrank (ZMod 2) (Vt S g t) := by
    omega
  set X := (S.Qa g ⊓ S.Qa u) ⊓ S.M with hX
  set Xbar := (X.subgroupOf S.M).map S.ρ with hXbar
  set LN := S.Lbar g ⊓ Nbar S g t with hLN
  set n := S.width with hn
  set m := finrank (ZMod 2) (Vt S g t) with hm
  set p := finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u)) with hp
  set A := Nat.card LN with hA
  set B := Nat.card Xbar with hB
  set Kc := Nat.card (S.ρ.ker ⊓ X.subgroupOf S.M : Subgroup S.M) with hKc
  set C0 := Nat.card (S.Qa g ⊓ S.Qa u : Subgroup G) with hC0
  set P0 := Nat.card (S.QG ⊓ S.Qa u : Subgroup G) with hP0
  have hXbarLN : Xbar ≤ LN := map_le_Lbar_inf_Nbar H hτ hτu hNo ht1 hL hU8
  have hX0 : C0 = 2 ^ (n + 1) := card_Qa_inf_Qa H ht1 hτ hτu C hF haQt
  have hX01 : C0 ≤ 2 * Nat.card X := card_le_two_mul H u
  have hXc : Nat.card X = B * Kc := card_eq_card_map_mul (S := S) (X := X) inf_le_right
  have hK : Kc ≤ P0 := card_ker_inf_le (S := S) (X := X) (u := u) (inf_le_left.trans inf_le_right)
  have hzP : S.z ∉ S.QG ⊓ S.Qa u := fun h => z_not_mem_Qa_of_tau ht1 hτ hτu h.2
  have hPcard : P0 = 2 ^ p := by
    rw [hP0, card_eq_card_clSub inf_le_left hzP, S.card_submodule]
  have hLcard : 2 ^ (n - 1) = 2 ^ (m - 1) * A := by
    have h1 := card_Lbar_eq_mul H.conj_mem ht
    rwa [C.card_Lbar, hL.LmodN_eq, card_centreGroup (aV_ne_zero H ht)] at h1
  have hXbarle : B ≤ A := Subgroup.card_le_of_le hXbarLN
  have hn1 : 1 ≤ n := by
    have := H.two_lt_width
    omega
  have hm1 : 1 ≤ m := by
    have := hL.two_le_finrank
    omega
  have hApos : 0 < A := Nat.card_pos
  have hBpos : 0 < B := Nat.card_pos
  have hKpos : 0 < Kc := Nat.card_pos
  have e1 : 2 ^ n = 2 ^ m * A := by
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h1, h2, hLcard, mul_assoc]
  have e2 : 2 ^ n ≤ B * Kc := by
    have h1 : 2 ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
    omega
  have e3 : B * Kc ≤ A * 2 ^ p := Nat.mul_le_mul hXbarle (hK.trans hPcard.le)
  have e4 : A * 2 ^ m ≤ A * 2 ^ p := by
    rw [mul_comm A]
    omega
  have hmp : m ≤ p :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_left e4 hApos)
  have hpm' : p = m := le_antisymm hpm hmp
  rw [hpm'] at e3 hPcard
  have hBA : B = A := by
    by_contra hne
    have hlt : B < A := lt_of_le_of_ne hXbarle hne
    have h1 : B * Kc < A * 2 ^ m :=
      calc B * Kc < A * Kc := Nat.mul_lt_mul_of_pos_right hlt hKpos
        _ ≤ A * 2 ^ m := Nat.mul_le_mul_left _ (hK.trans hPcard.le)
    rw [mul_comm A] at h1
    omega
  have hKP : Kc = Nat.card (S.QG ⊓ S.Qa u : Subgroup G) := by
    by_contra hne
    have hlt : Kc < Nat.card (S.QG ⊓ S.Qa u : Subgroup G) := lt_of_le_of_ne hK hne
    have h1 : B * Kc < A * 2 ^ m :=
      calc B * Kc < B * 2 ^ m := Nat.mul_lt_mul_of_pos_left (hPcard ▸ hlt) hBpos
        _ ≤ A * 2 ^ m := Nat.mul_le_mul_right _ hXbarle
    rw [mul_comm A] at h1
    omega
  have hXbarEq : Xbar = LN := Subgroup.eq_of_le_of_card_ge hXbarLN (by rw [← hA, ← hB, hBA])
  have hPle : S.QG ⊓ S.Qa u ≤ S.Qa g := by
    have hle : (S.ρ.ker ⊓ X.subgroupOf S.M).map S.M.subtype ≤ S.QG ⊓ S.Qa u := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨(S.ρ_eq_one_iff y).mp hy1, (mem_subgroupOf.mp hy2).1.2⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective S.M.subtype_injective, ← hKc, hKP])
    intro x hx
    rw [← heq] at hx
    obtain ⟨y, ⟨-, hy2⟩, rfl⟩ := hx
    exact (mem_subgroupOf.mp hy2).1.1
  have hcomm : ∀ x ∈ S.Qa g ⊓ S.Qa u, ∀ y ∈ S.Qa g ⊓ S.Qa u, x * y = y * x := by
    intro x hx y hy
    have hTa : (S.conjBy u).Qa (g * u⁻¹) = S.Qa g := by
      rw [S.Qa_conjBy, inv_mul_cancel_right]
    have hne : (g * u⁻¹) * (S.conjBy u).z * (g * u⁻¹)⁻¹ ≠ (S.conjBy u).z := by
      rw [Setting.conjBy_z, show g * u⁻¹ * (u * S.z * u⁻¹) * (g * u⁻¹)⁻¹ = g * S.z * g⁻¹ by
        group, ← hτu]
      intro h
      exact tau_not_mem_QG ht1 hτ (h ▸ H.conj_mem)
    exact (S.conjBy u).QG_inf_Qa_comm hne ⟨hx.2, by rw [hTa]; exact hx.1⟩
      ⟨hy.2, by rw [hTa]; exact hy.1⟩
  have hfixP : S.clSub (S.QG ⊓ S.Qa u) ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S LN := by
    intro v hv
    obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hv
    have hqg : q ∈ S.Qa g := hPle hq
    refine ⟨S.cl_mem_clSub ⟨hqQ, hqg⟩ hqQ, fun ξ hξ => ?_⟩
    rw [← hXbarEq] at hξ
    obtain ⟨x, hx, rfl⟩ := hξ
    obtain ⟨⟨hxg, hxu⟩, -⟩ := mem_subgroupOf.mp hx
    rw [S.ρ_cl x hqQ, hcomm _ ⟨hxg, hxu⟩ _ ⟨hqg, hq.2⟩, mul_inv_cancel_right]
  have hfixdim := card_mul_two_pow_finrank_fix H C (K := LN) inf_le_left
  have hd : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S LN) = m := by
    have h1 : A * 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S LN) =
        A * 2 ^ m := by
      rw [hfixdim, ← hn, e1, mul_comm]
    exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left hApos h1)
  have hVle : Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S LN := fun v hv =>
    ⟨Vt_le_clSub_of_V_le hL.le_Qa hv, fun ξ hξ => hξ.2.2 v hv⟩
  have hVeq : Vt S g t = S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S LN :=
    Submodule.eq_of_le_of_finrank_le hVle (by rw [hd])
  have hPV : S.clSub (S.QG ⊓ S.Qa u) ≤ Vt S g t := hVeq ▸ hfixP
  have hPVeq : S.clSub (S.QG ⊓ S.Qa u) = Vt S g t :=
    Submodule.eq_of_le_of_finrank_le hPV (by rw [← hp, ← hm, hpm'])
  exact hVP hPVeq.ge

theorem timmesfeld_6_8 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (hF : FusionCtl S g)
    {t : S.O} {ht : t ∈ S.Lbar g} (ht1 : t ≠ 1) (hL : LinCase S g ht) {τ : S.M}
    (hτ : S.ρ τ = t) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u) : Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa u) := by
  by_cases hβ : ∃ q ∈ S.QG, q * (τ : G) * q⁻¹ = (τ : G) * S.z
  · exact Vt_le_clSub_of_conj H hNo C hF ht1 hL hτ hτu haQt hβ
  · exact Vt_le_clSub_of_not_conj H hL hτ hτu haQt hβ

end CFSG.LargeExtraspecial.S6
