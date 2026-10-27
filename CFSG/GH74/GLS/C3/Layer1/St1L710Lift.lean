module

public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.TwoThin.Equivariance

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.L710

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_lift_inner
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hL : HasL2Model (kBar K) (fun q => q = 9))
    {y w : G} (hy2 : orderOf y = 2) (hyK : y ∈ normalizer (K : Set G))
    (hwK : w ∈ normalizer (K : Set G)) (hwy : w * y = y * w) (hw : Odd (orderOf w)) :
    ∃ k ∈ K, y * k = k * y ∧ ∀ k' ∈ K, ⁅k', k⁻¹ * w⁆ ∈ pPrimeCoreOf 2 K := by
  have hconj : ∀ m ∈ normalizer (K : Set G), ∀ l ∈ K, m * l * m⁻¹ ∈ K :=
    fun m hm l hl => (Subgroup.mem_normalizer_iff.mp hm l).mp hl
  set A := Back.actHom (M := normalizer (K : Set G)) (L := K) hconj with hA
  have h9 : IsFM9 9 := Or.inl rfl
  obtain ⟨F, _, _, e, hF, hFq⟩ := IVK.Proofs2.exists_l2Field_of_hasL2Model h9 hL
  have hfm : IsFM9 (Nat.card F) := Or.inl hFq
  have hwodd : Odd (orderOf (A ⟨w, hwK⟩)) :=
    Odd.of_dvd_nat hw ((orderOf_map_dvd A ⟨w, hwK⟩).trans (by rw [Subgroup.orderOf_mk]))
  obtain ⟨κ, hκ⟩ := IVK.Proofs2.mem_innAut_of_odd_orderOf hF hfm e hwodd
  have hinj : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) :=
    IVK.conj_injective_of_L2 e
  have hcomm : A ⟨y, hyK⟩ * A ⟨w, hwK⟩ = A ⟨w, hwK⟩ * A ⟨y, hyK⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hwy.symm
  have hfix : A ⟨y, hyK⟩ κ = κ := by
    apply hinj
    have h1 := IVK.Proofs2.mul_conj_mul_inv (A ⟨y, hyK⟩) κ
    have h2 : MulAut.conj κ = A ⟨w, hwK⟩ := hκ
    rw [← h1, h2, hcomm]
    group
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective κ
  set σ : ↥K ≃* ↥K := TwoThin.conjAut hyK with hσ
  have hαy_mk : A ⟨y, hyK⟩ (QuotientGroup.mk k₀) = QuotientGroup.mk (σ k₀) :=
    Back.actHom_mk hconj ⟨y, hyK⟩ k₀
  have hm : k₀⁻¹ * σ k₀ ∈ pPrimeCore 2 ↥K := by
    rw [hαy_mk] at hfix
    exact QuotientGroup.eq.1 hfix.symm
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  have hσσ : ∀ a : ↥K, σ (σ a) = a := by
    intro a
    apply Subtype.ext
    show y * (y * (a : G) * y⁻¹) * y⁻¹ = a
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    rw [hyi]
    calc y * (y * (a : G) * y) * y = (y * y) * a * (y * y) := by group
      _ = a := by rw [hyy]; group
  set m : ↥K := k₀⁻¹ * σ k₀ with hmdef
  have hσm : σ m = m⁻¹ := by
    rw [hmdef, map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
  have hmodd : Odd (orderOf m) :=
    Odd.of_dvd_nat (TwoThin.odd_card_pPrimeCore ↥K) (Subgroup.orderOf_dvd_natCard _ hm)
  obtain ⟨s, hs⟩ := hmodd
  have hmpow : m ^ (2 * s + 1) = 1 := hs ▸ pow_orderOf_eq_one m
  set k : ↥K := k₀ * m ^ (s + 1) with hkdef
  have hσk : σ k = k := by
    have h1 : σ k₀ = k₀ * m := by rw [hmdef, mul_inv_cancel_left]
    have h2 : m * (m ^ (s + 1))⁻¹ = m ^ (s + 1) := by
      rw [mul_inv_eq_iff_eq_mul, ← pow_add, show s + 1 + (s + 1) = (2 * s + 1) + 1 by ring,
        pow_succ, hmpow, one_mul]
    rw [hkdef, map_mul, map_pow, hσm, h1, inv_pow, mul_assoc, h2]
  have hyk : y * (k : G) = (k : G) * y := by
    have h := congrArg Subtype.val hσk
    change y * (k : G) * y⁻¹ = k at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hkmk : (QuotientGroup.mk k : kBar K) = QuotientGroup.mk k₀ := by
    refine (QuotientGroup.eq.2 ?_).symm
    rw [hkdef, inv_mul_cancel_left]
    exact (pPrimeCore 2 ↥K).pow_mem hm _
  refine ⟨(k : G), k.2, hyk, ?_⟩
  have hkM : (k : G) ∈ normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hkw : (k : G)⁻¹ * w ∈ normalizer (K : Set G) := mul_mem (inv_mem hkM) hwK
  rw [← Back.actHom_eq_one_iff_commutator_mem hconj ⟨(k : G)⁻¹ * w, hkw⟩]
  have hsplit : (⟨(k : G)⁻¹ * w, hkw⟩ : ↥(normalizer (K : Set G))) =
      (⟨(k : G), hkM⟩ : ↥(normalizer (K : Set G)))⁻¹ * ⟨w, hwK⟩ := rfl
  have hAk : A ⟨(k : G), hkM⟩ = MulAut.conj (QuotientGroup.mk k₀ : kBar K) := by
    rw [hA, Back.actHom_of_mem hconj k.2 hkM, hkmk]
  rw [hsplit, map_mul, map_inv, hAk]
  have h2 : MulAut.conj (QuotientGroup.mk k₀ : kBar K) = A ⟨w, hwK⟩ := hκ
  rw [h2, inv_mul_cancel]

end CFSG.GH74.GLS.C3.Layer1.EndN.L710
