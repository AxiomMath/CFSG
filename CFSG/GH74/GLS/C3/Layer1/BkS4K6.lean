module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim
public import CFSG.GH74.GLS.C3.Layer1.BkA6K
public import CFSG.GH74.GLS.IVK.L2.Lemma14j

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK

theorem a6_sylow_package
    {H : Type} [Group H] [Finite H] (e0 : H ≃* alternatingGroup (Fin 6))
    (X0 : Subgroup (MulAut H)) (hX0 : X0 ≤ innAut H) (hcard : Nat.card ↥X0 = 8) :
    IsD8 X0 ∧ Nat.card ↥(centralizer (X0 : Set (MulAut H))) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, eL, hF9⟩ := exists_L2_nine_equiv e0
  have hF : L2Field F := ⟨by rw [hF9]; decide, by rw [hF9]; norm_num⟩
  have hH360 : Nat.card H = 360 := by
    rw [Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hinn : Nat.card ↥(innAut H) = 360 := by
    rw [← hH360]
    exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_L2 eL)).toEquiv).symm
  have hX2 : IsPGroup 2 ↥X0 := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨T₀, hT₀⟩ := hX2.exists_le_sylow
  obtain ⟨e', N, hNT⟩ := ivk_1_2a_exists F hF H eL T₀
  have hNP : N.P = (T₀ : Subgroup (MulAut H)) ⊓ innAut H := by
    rw [L2Notation.P, hNT]
  have hX0N : X0 ≤ N.P := by
    rw [hNP]
    exact le_inf hT₀ hX0
  have hNP2 : IsPGroup 2 ↥N.P := by
    rw [hNP]
    exact T₀.isPGroup'.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hNP2
  have hdvd : Nat.card ↥N.P ∣ 360 := by
    rw [← hinn]
    exact Subgroup.card_dvd_of_le (by rw [hNP]; exact inf_le_right)
  have hk3 : k ≤ 3 := by
    by_contra hk4
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [← hk] at h16
    have := h16.trans hdvd
    norm_num at this
  have hle8 : Nat.card ↥N.P ≤ 8 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hXN : X0 = N.P :=
    Subgroup.eq_of_le_of_card_ge hX0N (by rw [hcard]; exact hle8)
  have hNPcard : Nat.card ↥N.P = 8 := by rw [← hXN]; exact hcard
  obtain ⟨n, hn2, k', hk'8, hk'2, ⟨d⟩⟩ := ivk_1_2c F hF H e' N
  have hk'4 : k' = 4 := by
    have h1 : Nat.card ↥N.P = 2 * k' := by
      have : NeZero k' := ⟨by omega⟩
      rw [Nat.card_congr d.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    omega
  subst hk'4
  have hD8 : IsD8 X0 := ⟨(MulEquiv.subgroupCongr hXN).trans d⟩
  refine ⟨hD8, ?_⟩
  obtain ⟨E, -, hEF, -, hcent, -, -⟩ := ivk_1_4j F hF H e' N
  have hE2 : Nat.card ↥E ≤ 2 := by
    have := Subgroup.card_le_of_le hEF
    rwa [card_fieldAutSub_nine hF hF9 e'] at this
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := hD8.exists_z
  set A : Subgroup (MulAut H) := (center ↥N.P).map N.P.subtype with hA
  have hAle : Nat.card ↥A ≤ 2 := by
    classical
    have hsub : (A : Set (MulAut H)) ⊆ (({1, z} : Finset (MulAut H)) : Set (MulAut H)) := by
      rintro w ⟨c, hc, rfl⟩
      have hcP : (c : MulAut H) ∈ X0 := hXN ▸ c.2
      have := hzu c hcP (fun p hp => by
        have hp' : p ∈ N.P := hXN ▸ hp
        have := Subgroup.mem_center_iff.1 hc ⟨p, hp'⟩
        exact congrArg Subtype.val this)
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h3 : (A : Set (MulAut H)).ncard ≤ 2 := by
      calc (A : Set (MulAut H)).ncard ≤ (({1, z} : Finset (MulAut H)) : Set (MulAut H)).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ({1, z} : Finset (MulAut H)).card := Set.ncard_coe_finset _
        _ ≤ 2 := Finset.card_le_two
    have h4 : Nat.card ↥A = (A : Set (MulAut H)).ncard := Nat.card_coe_set_eq (A : Set (MulAut H))
    omega
  have hAE : ∀ a ∈ A, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨c, hc, rfl⟩ b hb
    have hbC : b ∈ centralizer (N.P : Set (MulAut H)) := by
      rw [hcent]
      exact Subgroup.mem_sup_right hb
    exact Subgroup.mem_centralizer_iff.1 hbC (c : MulAut H) c.2
  have hX0C : centralizer (X0 : Set (MulAut H)) = centralizer (N.P : Set (MulAut H)) := by
    rw [hXN]
  rw [hX0C, hcent]
  calc Nat.card ↥(A ⊔ E) ≤ Nat.card ↥A * Nat.card ↥E := card_sup_le_of_commute hAE
    _ ≤ 2 * 2 := Nat.mul_le_mul hAle hE2

end CFSG.GH74.GLS.C3.Layer1.Bk
