module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSA6

public noncomputable section

namespace CFSG.QuasithinUnique.Id2519.UHS

open CFSG.Sporadic.Schreier

theorem card_centralizer_of_isConj {x y : PP} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set PP)) =
      Nat.card (Subgroup.centralizer ({y} : Set PP)) := by
  have hcls : conjugatesOf x = conjugatesOf y := isConj_iff_conjugatesOf_eq.1 h
  have h1 := Subgroup.index_centralizer_eq_ncard x
  have h2 := Subgroup.index_centralizer_eq_ncard y
  have e : (Subgroup.centralizer ({x} : Set PP)).index =
      (Subgroup.centralizer ({y} : Set PP)).index := by rw [h1, h2, hcls]
  have m1 := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set PP))
  have m2 := Subgroup.card_mul_index (Subgroup.centralizer ({y} : Set PP))
  have hpos : 0 < (Subgroup.centralizer ({y} : Set PP)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [e] at m1
  exact Nat.eq_of_mul_eq_mul_right hpos (m1.trans m2.symm)

theorem hs_fusion
    (s : PP) (hs2 : s * s = 1) (hs1 : s ≠ 1) (K : Subgroup PP)
    (hK : Nat.card K = 360) (hKc : ∀ k ∈ K, k * s = s * k)
    (hnorm : ∀ c : PP, c * s = s * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    ∀ u ∈ K, u * u = 1 → ∃ x : PP, x * s * x⁻¹ = s * u := by
  have hord : orderOf (s : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  rcases hs_invol_cover s.2 hord with h | h
  ·
    exfalso
    obtain ⟨c, hc, hce⟩ := hsE1_conj _ h
    have hconj : IsConj (⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ : PP) s :=
      isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hce.symm⟩
    have h1 := card_centralizer_of_isConj hconj
    rw [card_centralizer_a0] at h1
    have hKle : K ≤ Subgroup.centralizer ({s} : Set PP) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.2 (hKc k hk)
    have h2 := Subgroup.card_dvd_of_le hKle
    rw [hK, ← h1] at h2
    norm_num at h2
  ·
    obtain ⟨c, hc, hce⟩ := hsE2_conj _ h
    set c' : PP := ⟨c, hc⟩ with hc'
    have hs_eq : s = c' * sC * c'⁻¹ := Subtype.ext hce
    let K' : Subgroup PP := K.map (MulAut.conj c'⁻¹).toMonoidHom
    have hK' : Nat.card K' = 360 := by
      rw [← hK]
      exact Subgroup.card_map_of_injective (MulAut.conj c'⁻¹).injective
    have hmemK' : ∀ k, k ∈ K' ↔ c' * k * c'⁻¹ ∈ K := by
      intro k
      constructor
      · rintro ⟨k₀, hk₀, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hk₀
      · intro hk
        exact ⟨c' * k * c'⁻¹, hk, by simp [mul_assoc]⟩
    have hKc' : ∀ k ∈ K', k * sC = sC * k := by
      intro k hk
      have h1 := hKc _ ((hmemK' k).1 hk)
      rw [hs_eq] at h1
      calc k * sC = c'⁻¹ * ((c' * k * c'⁻¹) * (c' * sC * c'⁻¹)) * c' := by group
        _ = c'⁻¹ * ((c' * sC * c'⁻¹) * (c' * k * c'⁻¹)) * c' := by rw [h1]
        _ = sC * k := by group
    have hnorm' : ∀ x : PP, x * sC = sC * x → ∀ k ∈ K', x * k * x⁻¹ ∈ K' := by
      intro x hx k hk
      rw [hmemK']
      have hy : (c' * x * c'⁻¹) * s = s * (c' * x * c'⁻¹) := by
        rw [hs_eq]
        calc c' * x * c'⁻¹ * (c' * sC * c'⁻¹) = c' * (x * sC) * c'⁻¹ := by group
          _ = c' * (sC * x) * c'⁻¹ := by rw [hx]
          _ = c' * sC * c'⁻¹ * (c' * x * c'⁻¹) := by group
      have := hnorm _ hy _ ((hmemK' k).1 hk)
      have e : c' * (x * k * x⁻¹) * c'⁻¹ =
          c' * x * c'⁻¹ * (c' * k * c'⁻¹) * (c' * x * c'⁻¹)⁻¹ := by group
      rw [e]
      exact this
    intro u hu hu2
    have hu' : c'⁻¹ * u * c' ∈ K' := (hmemK' _).2 (by simpa [mul_assoc] using hu)
    have hu2' : (c'⁻¹ * u * c') * (c'⁻¹ * u * c') = 1 := by
      calc (c'⁻¹ * u * c') * (c'⁻¹ * u * c') = c'⁻¹ * (u * u) * c' := by group
        _ = 1 := by rw [hu2]; group
    obtain ⟨d, hd⟩ := hs_core_c K' hK' hKc' hnorm' _ hu' hu2'
    refine ⟨c' * d * c'⁻¹, ?_⟩
    rw [hs_eq]
    calc c' * d * c'⁻¹ * (c' * sC * c'⁻¹) * (c' * d * c'⁻¹)⁻¹
        = c' * (d * sC * d⁻¹) * c'⁻¹ := by group
      _ = c' * (sC * (c'⁻¹ * u * c')) * c'⁻¹ := by rw [hd]
      _ = c' * sC * c'⁻¹ * u := by group

end CFSG.QuasithinUnique.Id2519.UHS
