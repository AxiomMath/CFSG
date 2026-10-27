module

public import CFSG.GroupTheory.ConjCommuteModCoprime

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_mem_normalizer_of_conj_le_sup {K Bs L : Subgroup G}
    (hKc : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hBsK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card Bs)) {n : G} (hn : n ∈ L)
    (hle : ∀ b ∈ Bs, n * b * n⁻¹ ∈ K ⊔ Bs) :
    ∃ k ∈ K, k * n ∈ Subgroup.normalizer (Bs : Set G) := by
  classical
  let H : Subgroup G := Bs.map (MulAut.conj n).toMonoidHom
  have hHle : H ≤ K ⊔ Bs := by
    rintro _ ⟨b, hb, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hle b hb
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨b, hb, rfl⟩ k hk
    have hbK : b ∈ Subgroup.normalizer (K : Set G) := hBsK hb
    have hbk : b * k * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbK k).mp hk
    have hkn : n⁻¹ * k * n = k := by
      calc n⁻¹ * k * n = n⁻¹ * (k * n) := by group
        _ = n⁻¹ * (n * k) := by rw [hKc k hk n hn]
        _ = k := by group
    have hconv : MulAut.conj n b * k * (MulAut.conj n b)⁻¹ = b * k * b⁻¹ := by
      rw [MulAut.conj_apply]
      calc (n * b * n⁻¹) * k * (n * b * n⁻¹)⁻¹
          = n * (b * (n⁻¹ * k * n) * b⁻¹) * n⁻¹ := by group
        _ = n * (b * k * b⁻¹) * n⁻¹ := by rw [hkn]
        _ = b * k * b⁻¹ := by
            calc n * (b * k * b⁻¹) * n⁻¹ = ((b * k * b⁻¹) * n) * n⁻¹ := by
                  rw [← hKc _ hbk n hn]
              _ = b * k * b⁻¹ := by group
    change MulAut.conj n b * k * (MulAut.conj n b)⁻¹ ∈ K
    rw [hconv]
    exact hbk
  have hHcard : Nat.card H = Nat.card Bs :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hcopH : Nat.Coprime (Nat.card K) (Nat.card H) := by rw [hHcard]; exact hcop
  obtain ⟨k, hk, hconj⟩ :=
    exists_conj_mem_of_le_sup (U := K) (H := H) (W := Bs) hHK hBsK
      (Subgroup.inf_eq_bot_of_coprime hcop) hHle hcopH
  have hmaple : Bs.map (MulAut.conj (k * n)).toMonoidHom ≤ Bs := by
    rintro _ ⟨b, hb, rfl⟩
    have hnb : n * b * n⁻¹ ∈ H := ⟨b, hb, rfl⟩
    have h1 := hconj _ hnb
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, mul_assoc] using h1
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcard : Nat.card ↥(Bs.map (MulAut.conj (k * n)).toMonoidHom) = Nat.card Bs :=
    Subgroup.card_map_of_injective (MulAut.conj (k * n)).injective
  exact Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)

end CFSG.GroupTheory

end
