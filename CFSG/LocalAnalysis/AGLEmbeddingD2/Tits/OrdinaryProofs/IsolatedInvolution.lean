module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.IsolatedInvolution

theorem conj_cocycle {W : Type} [Group W] {s t : W} (ht2 : t * t = 1) (hs : s * s = 1) :
    t * (s * t⁻¹) * t⁻¹ = (s * t⁻¹)⁻¹ := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [mul_inv_rev, inv_inv, hsi, ht]
  simp only [mul_assoc, ht2, mul_one]

theorem conj_of_sq {W : Type} [Group W] (n m t : W) (hnn : n * n = m)
    (h3 : n⁻¹ = t⁻¹ * n * t) : n * t * n⁻¹ = m * t := by
  rw [h3, ← hnn]
  group

theorem isSolvable_of_isolated {W : Type} [Group W] [Finite W] {t : W} (ht1 : t ≠ 1)
    (ht2 : t * t = 1)
    (hiso : ∀ g : W, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t)
    (hC : Group.IsSolvable (Subgroup.centralizer ({t} : Set W))) : Group.IsSolvable W := by
  obtain ⟨N, hN, hNodd, hNmem⟩ : ∃ N : Subgroup W, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : W, g * t * g⁻¹ * t⁻¹ ∈ N := by
    have := Fintype.ofFinite W
    exact CFSG.ZStar.glauberman_zStar W t ht1 ht2 hiso
  have := hN
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have := hNsolv
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨k, hk⟩ := hNodd
  have hcover : ∀ g : W, ∃ n ∈ N, g * t * g⁻¹ = n * t * n⁻¹ := by
    intro g
    obtain ⟨m, hm⟩ : ∃ m : W, m = g * t * g⁻¹ * t⁻¹ := ⟨_, rfl⟩
    have hmN : m ∈ N := hm ▸ hNmem g
    have hs : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2]
      group
    have hcm : t * m * t⁻¹ = m⁻¹ := by
      rw [hm]
      exact conj_cocycle ht2 hs
    have hsm : g * t * g⁻¹ = m * t := by
      rw [hm, ht_inv]
      simp only [mul_assoc, ht2, mul_one]
    have hmpow : m ^ ((k + 1) + (k + 1)) = m := by
      have h1 : m ^ Nat.card N = 1 :=
        congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨m, hmN⟩))
      rw [show (k + 1) + (k + 1) = Nat.card N + 1 by omega, pow_succ, h1, one_mul]
    have hnn : m ^ (k + 1) * m ^ (k + 1) = m := by
      rw [← pow_add]
      exact hmpow
    have hpow : t * m ^ (k + 1) * t⁻¹ = (m ^ (k + 1))⁻¹ := by
      have := map_pow (MulAut.conj t) m (k + 1)
      simp only [MulAut.conj_apply] at this
      rw [this, hcm, inv_pow]
    have h2 : t * (m ^ (k + 1))⁻¹ * t⁻¹ = m ^ (k + 1) := by
      have := map_inv (MulAut.conj t) (m ^ (k + 1))
      simp only [MulAut.conj_apply] at this
      rw [this, hpow, inv_inv]
    have h3 : (m ^ (k + 1))⁻¹ = t⁻¹ * m ^ (k + 1) * t := by
      calc (m ^ (k + 1))⁻¹ = t⁻¹ * (t * (m ^ (k + 1))⁻¹ * t⁻¹) * t := by group
        _ = t⁻¹ * m ^ (k + 1) * t := by rw [h2]
    refine ⟨m ^ (k + 1), N.pow_mem hmN _, ?_⟩
    rw [hsm]
    exact (conj_of_sq _ _ _ hnn h3).symm
  have hW : ∀ g : W, ∃ n ∈ N, ∃ u ∈ Subgroup.centralizer ({t} : Set W), g = n * u := by
    intro g
    obtain ⟨n, hn, hcov⟩ := hcover g
    refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [mul_inv_eq_iff_eq_mul] at hcov
    calc h * (n⁻¹ * g) = n⁻¹ * (n * h * n⁻¹ * g) := by group
      _ = n⁻¹ * (g * h) := by rw [← hcov]
      _ = n⁻¹ * g * h := by group
  have := hC
  have hsolvQ : Group.IsSolvable (W ⧸ N) := by
    let f : Subgroup.centralizer ({t} : Set W) →* W ⧸ N :=
      (QuotientGroup.mk' N).comp (Subgroup.subtype _)
    have hsurj : Function.Surjective f := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
      obtain ⟨n, hn, u, hu, rfl⟩ := hW g
      refine ⟨⟨u, hu⟩, ?_⟩
      show QuotientGroup.mk' N u = QuotientGroup.mk' N (n * u)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := hN.conj_mem n hn u⁻¹
      simpa [mul_assoc] using this
    exact Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_subgroup_quotient N

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.IsolatedInvolution

end
