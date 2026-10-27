module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6KleinInn
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Norm
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6CQ
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Inv

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Inner

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem card_centralizer_of_five (hF : L2Field F) (h5 : Nat.card F = 5) (e : K ≃* L2 F) {u : K}
    (hu : orderOf u = 2) : Nat.card ↥(centralizer ({u} : Set K)) = 4 := by
  obtain ⟨-, ⟨k, hk, -, ⟨ψ⟩⟩, -⟩ := ivk_1_3a F hF K e 1 (Or.inl rfl)
    (by rw [h5]; unfold Int.ModEq; norm_num) 4 (by rw [h5]; norm_num) u hu
  rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  omega

theorem false_of_inner_involution (hF : L2Field F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F)
    {U W : Subgroup (MulAut K)} (hUW : U ≤ W) (hU : IsFourSubgroup U) (hUinn : U ≤ innAut K)
    {z s : MulAut K} (hz : z ∈ U) (hz1 : z ≠ 1) (hsW : s ∈ W) (hsI : s ∈ innAut K) (hsU : s ∉ U)
    (hs2 : s ^ 2 = 1) (hcomm : z * s = s * z)
    (hΓ : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W ≠ ⊤) : False := by
  have hinj := conj_injective_of_L2 e
  have hUsq : ∀ a ∈ U, a ^ 2 = 1 := fun a ha => by
    have := hU.1
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    comm_of_sq_eq_one (hUsq a ha) (hUsq b hb) (hUsq _ (U.mul_mem ha hb))
  obtain ⟨s₀, rfl⟩ := hsI
  obtain ⟨z₀, rfl⟩ := hUinn hz
  set V₀ : Subgroup K := U.comap (MulAut.conj : K →* MulAut K) with hV₀
  have hVmap : V₀.map (MulAut.conj : K →* MulAut K) = U := Subgroup.map_comap_eq_self hUinn
  have hV₀4 : Nat.card ↥V₀ = 4 := by
    rw [← Subgroup.card_map_of_injective hinj, hVmap]
    exact hU.2
  have hVmem : ∀ u : K, u ∈ V₀ ↔ MulAut.conj u ∈ U := fun u => Iff.rfl
  have hV₀comm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    hinj (by rw [map_mul, map_mul]; exact hUc _ ha _ hb)
  have hV₀sq : ∀ a ∈ V₀, a ^ 2 = 1 := fun a ha =>
    hinj (by rw [map_pow, hUsq _ ha, map_one])
  have hz₀V : z₀ ∈ V₀ := hz
  have hz₀1 : z₀ ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hs₀1 : s₀ ≠ 1 := fun h => hsU (by rw [h, map_one]; exact U.one_mem)
  have hs₀2 : orderOf s₀ = 2 :=
    orderOf_eq_prime (hinj (by rw [map_pow, hs2, map_one])) hs₀1
  have hs₀V : s₀ ∉ V₀ := hsU
  have hcomm₀ : s₀ * z₀ = z₀ * s₀ := hinj (by rw [map_mul, map_mul]; exact hcomm.symm)
  have hordconj : ∀ u : K, orderOf (MulAut.conj u) = orderOf u := fun u =>
    orderOf_injective _ hinj u
  have hΓV : ∀ u ∈ V₀, u ≠ 1 → centralizer ({u} : Set K) ≤
      CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W := fun u hu hu1 =>
    centralizer_le_gammaAut (hUW hu)
      (by rw [hordconj]; exact orderOf_eq_prime (hV₀sq u hu) hu1)
  have hΓs : centralizer ({s₀} : Set K) ≤ CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W :=
    centralizer_le_gammaAut hsW (by rw [hordconj]; exact hs₀2)
  rcases hq with h5 | h79
  ·
    have hz₀2 : orderOf z₀ = 2 := orderOf_eq_prime (hV₀sq z₀ hz₀V) hz₀1
    have hC4 := card_centralizer_of_five hF h5 e hz₀2
    have hVC : V₀ ≤ centralizer ({z₀} : Set K) := fun v hv =>
      mem_centralizer_singleton_iff.2 (hV₀comm v hv z₀ hz₀V)
    have heq : V₀ = centralizer ({z₀} : Set K) :=
      Subgroup.eq_of_le_of_card_ge hVC (by rw [hC4, hV₀4])
    apply hs₀V
    rw [heq]
    exact mem_centralizer_singleton_iff.2 hcomm₀
  · have hq79 : Nat.card F = 7 ∨ Nat.card F = 9 := by
      rcases h79 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hD4 : HasD4Centralizers K := fun u hu => (centralizer_dih_of_seven_nine hF hq79 e hu).1
    exact false_of_centralizer_le_of_not_mem hD4 (isSimpleGroup_of_l2 hF e)
      (card_eq_of_seven_nine hF hq79 e) hV₀4 hV₀comm hV₀sq hz₀V hz₀1 hs₀2 hs₀V hcomm₀ hΓ hΓV hΓs

end Inner

section Main

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem eq_of_gammaAut_ne_top (hF : L2Field F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F) (N : L2Notation e)
    {U W : Subgroup (MulAut K)} (hUW : U ≤ W) (hW2 : IsPGroup 2 ↥W) (hU : IsFourSubgroup U)
    (hUinn : U ≤ innAut K)
    (hC : ∀ w ∈ centralizer (U : Set (MulAut K)), w ∈ U ∨ (w ∉ innDiagSub e ∧ w ^ 2 = 1))
    (hΓ : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W ≠ ⊤) : W = U := by
  by_contra hne
  have hne' : U ≠ W := fun h => hne h.symm
  obtain ⟨w, hwW, hwU, hwN, hw2U⟩ := exists_mem_normalizer_sq_mem hUW hne' hW2
  have hUsq : ∀ a ∈ U, a ^ 2 = 1 := fun a ha => by
    have := hU.1
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hUD : ∀ a ∈ U, a ∈ innDiagSub e := fun a ha => innAut_le_innDiagSub e (hUinn ha)
  by_cases hwc : w ∈ centralizer (U : Set (MulAut K))
  ·
    rcases hC w hwc with h | ⟨hwD, hw2⟩
    · exact hwU h
    · obtain ⟨u, hu, -, -, hu1, -, -⟩ := CFSG.QuasithinUnique.Unc25Small.exists_two_nonid hU.2
      have huw : u * w = w * u := mem_centralizer_iff.1 hwc u hu
      have hu2 : u * u = 1 := by rw [← pow_two]; exact hUsq u hu
      have hwu2 : (w * u) ^ 2 = 1 := by
        have hw2' : w * w = 1 := by rw [← pow_two]; exact hw2
        calc (w * u) ^ 2 = (w * u) * (w * u) := pow_two _
          _ = w * (u * w) * u := by group
          _ = w * (w * u) * u := by rw [huw]
          _ = (w * w) * (u * u) := by group
          _ = 1 := by rw [hw2', hu2, one_mul]
      have hwuD : w * u ∉ innDiagSub e := by
        intro h
        apply hwD
        have : w = (w * u) * u⁻¹ := by group
        rw [this]
        exact (innDiagSub e).mul_mem h ((innDiagSub e).inv_mem (hUD u hu))
      exact hΓ (gammaAut_eq_top_of_outer_outer hF hq e N hwW (W.mul_mem hwW (hUW hu)) hw2 hwu2
        hwD hwuD (fun h => hu1 (mul_left_cancel (a := w) (by rw [mul_one]; exact h.symm)))
        (by
          calc w * (w * u) = w * (u * w) := by rw [huw]
            _ = (w * u) * w := by group))
  ·
    have hwc' : ¬ ∀ u ∈ U, u * w = w * u := fun h => hwc (mem_centralizer_iff.2 h)
    obtain ⟨z, hz, x, hx, hz1, hsU, hs2, hcomm⟩ :=
      exists_involution_of_normalizing hU.2 hUsq hwN hw2U hwc' hwU
    set s : MulAut K := x * w with hs
    have hsW : s ∈ W := W.mul_mem (hUW hx) hwW
    have hzW : z ∈ W := hUW hz
    by_cases hsD : s ∈ innDiagSub e
    · by_cases hsI : s ∈ innAut K
      · exact false_of_inner_involution hF hq e hUW hU hUinn hz hz1 hsW hsI hsU hs2 hcomm hΓ
      · exact hΓ (gammaAut_eq_top_of_inner_outer hF hq e hzW hsW (hUinn hz) hz1 (hUsq z hz) hsD hsI
          hs2 hcomm)
    ·
      have hz2 : z * z = 1 := by rw [← pow_two]; exact hUsq z hz
      have hszc : s * z = z * s := hcomm.symm
      have hsz2 : (s * z) ^ 2 = 1 := by
        have hs2' : s * s = 1 := by rw [← pow_two]; exact hs2
        calc (s * z) ^ 2 = (s * z) * (s * z) := pow_two _
          _ = s * (z * s) * z := by group
          _ = s * (s * z) * z := by rw [← hszc]
          _ = (s * s) * (z * z) := by group
          _ = 1 := by rw [hs2', hz2, one_mul]
      have hszD : s * z ∉ innDiagSub e := by
        intro h
        apply hsD
        have : s = (s * z) * z⁻¹ := by group
        rw [this]
        exact (innDiagSub e).mul_mem h ((innDiagSub e).inv_mem (hUD z hz))
      exact hΓ (gammaAut_eq_top_of_outer_outer hF hq e N hsW (W.mul_mem hsW hzW) hs2 hsz2 hsD hszD
        (fun h => hz1 (mul_left_cancel (a := s) (by rw [mul_one]; exact h.symm)))
        (by
          calc s * (s * z) = s * (z * s) := by rw [hszc]
            _ = (s * z) * s := by group))

end Main

end CFSG.GH74.GLS.IVK.Proofs2
