module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableA4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAut

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GorensteinWalter

section Orbit

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem k32_ncard_conj_mul_card (Q : Subgroup Γ) (ω : Γ) :
    {x : Γ | ∃ r ∈ Q, x = r * ω * r⁻¹}.ncard * Nat.card ↥(Q ⊓ Subgroup.centralizer ({ω} : Set Γ)) =
      Nat.card ↥Q := by
  let : MulAction Q Γ := MulAction.compHom Γ ((MulAut.conj : Γ →* MulAut Γ).comp Q.subtype)
  have hsmul : ∀ (h : Q) (x : Γ), h • x = (h : Γ) * x * (h : Γ)⁻¹ := fun _ _ => rfl
  have horbit : MulAction.orbit Q ω = {x : Γ | ∃ r ∈ Q, x = r * ω * r⁻¹} := by
    ext x
    simp only [MulAction.mem_orbit_iff, hsmul, Set.mem_ofPred_eq]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, c.2, hc.symm⟩, fun ⟨c, hc, hx⟩ => ⟨⟨c, hc⟩, hx.symm⟩⟩
  have hstab : (MulAction.stabilizer Q ω).map Q.subtype =
      Q ⊓ Subgroup.centralizer ({ω} : Set Γ) := by
    ext x
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, hsmul, Subgroup.coe_subtype,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      calc (c : Γ) * ω = (c : Γ) * ω * (c : Γ)⁻¹ * c := by group
        _ = ω * c := by rw [hc]
    · rintro ⟨hx, hxu⟩
      exact ⟨⟨x, hx⟩, by
        show (x : Γ) * ω * (x : Γ)⁻¹ = ω
        calc (x : Γ) * ω * (x : Γ)⁻¹ = ω * x * (x : Γ)⁻¹ := by rw [hxu]
          _ = ω := by group, rfl⟩
  have hidx := MulAction.index_stabilizer (G := Q) (x := ω)
  have hmul := (MulAction.stabilizer Q ω).card_mul_index
  rw [← hstab, Subgroup.card_map_of_injective Q.subtype_injective, ← horbit, ← hidx, mul_comm]
  exact hmul

theorem k32_card_le_of_orbit {Q : Subgroup Γ} {ω : Γ} {S : Set Γ}
    (hS : ∀ r ∈ Q, r * ω * r⁻¹ ∈ S) :
    Nat.card ↥Q ≤ S.ncard * Nat.card ↥(Q ⊓ Subgroup.centralizer ({ω} : Set Γ)) := by
  rw [← k32_ncard_conj_mul_card Q ω]
  refine Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite S))
  rintro _ ⟨r, hr, rfl⟩
  exact hS r hr

theorem k32_inf_le_of_not_mem {A V J : Subgroup Γ} [J.Normal] (hA : IsA4Block A V) {c : Γ}
    (hc : c ∈ A) (hcJ : c ∉ J) : A ⊓ J ≤ V := by
  by_cases hbot : A ⊓ J = ⊥
  · rw [hbot]; exact bot_le
  · have hnorm : A ≤ Subgroup.normalizer ((A ⊓ J : Subgroup Γ) : Set Γ) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨A.mul_mem (A.mul_mem ha hy1) (A.inv_mem ha), ‹J.Normal›.conj_mem y hy2 a⟩
      · rintro ⟨hy1, hy2⟩
        refine ⟨?_, ?_⟩
        · have := A.mul_mem (A.mul_mem (A.inv_mem ha) hy1) ha
          simpa [mul_assoc] using this
        · have := ‹J.Normal›.conj_mem _ hy2 a⁻¹
          simpa [mul_assoc] using this
    have hVN : V ≤ A ⊓ J := k32_le_of_normal_ne_bot hA inf_le_left hnorm hbot
    have hdvd : Nat.card ↥(A ⊓ J) ∣ 12 := by
      rw [← hA.card_L]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h4 : 4 ∣ Nat.card ↥(A ⊓ J) := by
      rw [← hA.card_U]
      exact Subgroup.card_dvd_of_le hVN
    have hne12 : Nat.card ↥(A ⊓ J) ≠ 12 := by
      intro h12
      have hAJ : A ⊓ J = A := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [h12, hA.card_L]
      exact hcJ (by
        have : c ∈ A ⊓ J := by rw [hAJ]; exact hc
        exact this.2)
    have hcard : Nat.card ↥(A ⊓ J) = 4 := by
      obtain ⟨k, hk⟩ := h4
      rw [hk] at hdvd hne12 ⊢
      have hk12 : 4 * k ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          norm_num at hdvd
        · exact h
      have hk3 : k ≤ 3 := by omega
      interval_cases k <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hVN (by rw [hcard, hA.card_U])).symm.le

end Orbit

section Crit2

variable {K : Type} [Group K] [Finite K]

theorem k32_crit2 {X P R A V : Subgroup (MulAut K)} (hd : K32Datum K X P R A V) :
    ∃ ω ∈ A, orderOf ω = 3 ∧ ∃ W : Subgroup (MulAut K), W ≤ innAut K ∧ IsPGroup 2 ↥W ∧
      W ≤ Subgroup.centralizer ({ω} : Set (MulAut K)) ∧
      (ω ∈ innAut K → twoPart (innAut K) ≤ 16 * Nat.card ↥W) ∧
      (ω ∉ innAut K → twoPart (innAut K) ≤ 8 * Nat.card ↥W) := by
  obtain ⟨c, hcA, hc3, -⟩ := hd.a4.exists_c
  have hJn : (innAut K).Normal := innAut_normal K
  have hXJ : X ≤ Subgroup.normalizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top (innAut K)]
    exact le_top
  have hPJ : IsSylowTwoOf (P ⊓ innAut K) (innAut K) :=
    A4.isSylowTwoOf_inf_normal hd.sylow hd.inn_le hXJ
  set R₀ := R ⊓ innAut K with hR₀
  have hR₀R : R₀ ≤ R := inf_le_left
  have hR₀P : R₀ ≤ P := hR₀R.trans hd.R_le
  have hPJcard : Nat.card ↥(P ⊓ innAut K) ≤ 2 * Nat.card ↥R₀ := by
    have hne : R.relIndex P ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    have h1 : R.relIndex (P ⊓ innAut K) ≤ 2 :=
      le_trans (Subgroup.relIndex_le_of_le_right inf_le_left hne) hd.idx
    have h2 := Subgroup.relIndex_mul_card R (P ⊓ innAut K)
    have h3 : R ⊓ (P ⊓ innAut K) = R₀ := by
      rw [← inf_assoc, inf_eq_left.mpr hd.R_le]
    rw [h3] at h2
    calc Nat.card ↥(P ⊓ innAut K) = R.relIndex (P ⊓ innAut K) * Nat.card ↥R₀ := h2.symm
      _ ≤ 2 * Nat.card ↥R₀ := Nat.mul_le_mul_right _ h1
  have hcard := hPJ.card_eq
  set W := R₀ ⊓ Subgroup.centralizer ({c} : Set (MulAut K)) with hW
  have hWR₀ : W ≤ R₀ := inf_le_left
  have hRA : ∀ r ∈ R₀, r * c * r⁻¹ ∈ A := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hd.R_norm (hR₀R hr)) c).mp hcA
  have hV2 : ∀ x ∈ V, orderOf x ≠ 3 := by
    intro x hx h3
    have h2 : x ^ 2 = 1 := hd.a4.sq_U x hx
    have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    omega
  refine ⟨c, hcA, hc3, W, (hWR₀.trans inf_le_right), hd.sylow.2.1.to_le (hWR₀.trans hR₀P),
    inf_le_right, ?_, ?_⟩
  · intro _
    have hS : ∀ r ∈ R₀, r * c * r⁻¹ ∈ ((A : Set (MulAut K)) \ (V : Set (MulAut K))) := by
      intro r hr
      refine ⟨hRA r hr, fun hV => hV2 _ hV ?_⟩
      rw [← hc3]
      exact (MulEquiv.orderOf_eq (MulAut.conj r) c)
    have hb : Nat.card ↥R₀ ≤ ((A : Set (MulAut K)) \ (V : Set (MulAut K))).ncard * Nat.card ↥W :=
      k32_card_le_of_orbit hS
    have hn : ((A : Set (MulAut K)) \ (V : Set (MulAut K))).ncard = 8 := by
      have h1 : ((A : Set (MulAut K)) \ (V : Set (MulAut K))).ncard =
          (A : Set (MulAut K)).ncard - (V : Set (MulAut K)).ncard :=
        Set.ncard_sdiff (SetLike.coe_subset_coe.mpr hd.a4.le) (Set.toFinite _)
      have h2 : (A : Set (MulAut K)).ncard = 12 := by
        rw [← Nat.card_coe_set_eq]
        exact hd.a4.card_L
      have h3 : (V : Set (MulAut K)).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hd.a4.card_U
      omega
    rw [hn] at hb
    omega
  · intro hout
    have hJA : A ⊓ innAut K ≤ V := k32_inf_le_of_not_mem hd.a4 hcA hout
    have hS : ∀ r ∈ R₀, r * c * r⁻¹ ∈ ((fun v => v * c) '' (V : Set (MulAut K))) := by
      intro r hr
      refine ⟨r * c * r⁻¹ * c⁻¹, hJA ⟨?_, ?_⟩, by group⟩
      · exact A.mul_mem (hRA r hr) (A.inv_mem hcA)
      · have h1 : r ∈ innAut K := hr.2
        have h2 : c * r⁻¹ * c⁻¹ ∈ innAut K := hJn.conj_mem _ (inv_mem h1) c
        have := (innAut K).mul_mem h1 h2
        simpa [mul_assoc] using this
    have hb : Nat.card ↥R₀ ≤ ((fun v => v * c) '' (V : Set (MulAut K))).ncard * Nat.card ↥W :=
      k32_card_le_of_orbit hS
    have hn : ((fun v => v * c) '' (V : Set (MulAut K))).ncard = 4 := by
      rw [Set.ncard_image_of_injective _ (mul_left_injective c), ← Nat.card_coe_set_eq]
      exact hd.a4.card_U
    rw [hn] at hb
    omega

end Crit2

end CFSG.QuasithinUnique.DoubleA3
