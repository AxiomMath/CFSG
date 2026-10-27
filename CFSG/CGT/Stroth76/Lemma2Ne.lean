module

public import CFSG.CGT.Stroth76.Lemma1
public import CFSG.CGT.Stroth76.Lemma2Two

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

theorem co_two_nsmul_ne_xy :
    ∀ v : Co, 2 • v ≠ (0, 1, 0) ∧ 2 • v ≠ (0, 0, 1) ∧ 2 • v ≠ (0, 1, 1) := by
  decide +kernel

variable {X : Type*} [Group X] [Finite X] (K : Config X)

theorem false_of_card_of_sq {C : Subgroup X} (hAC : K.A ≤ C) (hCab : IsMulCommutative C)
    (hcard : Nat.card C = 2 ^ 6) {a b : X} (haC : a ∈ C) (hbC : b ∈ C) (ha2 : a ^ 2 = K.x)
    (hb2 : b ^ 2 = K.y) : False := by
  have hsq : ∀ {g : X}, g ∈ K.A → ∃ v : Co, g ^ 2 = K.ev (2 • v) := fun {g} hg => by
    obtain ⟨v, rfl⟩ := K.exists_ev hg
    exact ⟨v, (K.ev_nsmul 2 v).symm⟩
  have haA : a ∉ K.A := fun h => by
    obtain ⟨v, hv⟩ := hsq h
    exact (co_two_nsmul_ne_xy v).1 (K.ev_injective (by rw [← hv, ha2, K.ev_x]))
  have hbA : b ∉ K.A := fun h => by
    obtain ⟨v, hv⟩ := hsq h
    exact (co_two_nsmul_ne_xy v).2.1 (K.ev_injective (by rw [← hv, hb2, K.ev_y]))
  have hidx : (K.A.subgroupOf C).index = 2 := by
    have h1 := (K.A.subgroupOf C).card_mul_index
    rw [show Nat.card (K.A.subgroupOf C) = Nat.card K.A from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, K.hAcard, hcard] at h1
    omega
  have hab : a * b ∈ K.A := by
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, haC⟩ : C))
      (b := ⟨b, hbC⟩)).mpr (by
        simp only [Subgroup.mem_subgroupOf]
        exact iff_of_false haA hbA)
    simpa [Subgroup.mem_subgroupOf] using h
  obtain ⟨v, hv⟩ := hsq hab
  have hba : b * a = a * b := Subgroup.mul_comm_of_mem_isMulCommutative C hbC haC
  have hxy : (a * b) ^ 2 = K.x * K.y := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a ^ 2 * b ^ 2 := by rw [hba, pow_two, pow_two]; group
      _ = K.x * K.y := by rw [ha2, hb2]
  exact (co_two_nsmul_ne_xy v).2.2 (K.ev_injective (by rw [← hv, hxy, xy_eq, tElt_ev]))

theorem arch76Lemma2_of_ne [K.A.Normal] (hρodd : Odd (orderOf K.ρ))
    {C : Subgroup X} (hCA : Subgroup.centralizer (K.A : Set X) = C) (hC : Nat.card C ∣ 2 ^ 7)
    (hne : C ≠ K.A) (P : Sylow 2 X) (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P)
    (hP : Nat.card P ∣ 2 ^ 10)
    (hE : ∀ g ∈ (P : Subgroup X), g ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) →
        g ∈ K.A ⊔ Subgroup.closure {K.uv, K.t, K.u}) :
    (P : Subgroup X) = C ⊔ Subgroup.closure {K.uv, K.t, K.u} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal := by rw [← hCA]; infer_instance
  have hAC : K.A ≤ C := by
    rw [← hCA]
    exact fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => K.comm hb ha
  have hCP : C ≤ P := (IsPGroup.of_card_dvd_pow hC).le_sylow_of_normal P
  have hE1 : ∀ g ∈ C, g ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) → g ∈ K.A :=
    fun g hg hgE => mem_A_of_mem_Tsub_of_mem_K K (hE g (hCP hg) hgE)
      (centralizer_A_le_K K (by rw [hCA]; exact hg))
  obtain ⟨hab, hshape⟩ := arch76Lemma1 K hρodd hCA hC hne hE1
  have hcard : Nat.card C = 2 ^ 6 ∨ Nat.card C = 2 ^ 7 := by
    have h := card_centralizer_of_ne K (by rw [hCA]; exact hC) (by rw [hCA]; exact hne)
    rw [hCA, K.hAcard] at h
    omega
  rcases hcard with h64 | h128
  · have hmem : ∀ {a b : X}, C = Subgroup.closure {K.w, a, b} → a ∈ C ∧ b ∈ C := by
      intro a b h
      rw [h]
      exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
    rcases hshape with ⟨a, b, hCab, ha2, hb2, -⟩ | ⟨a, b, hCab, ha2, hb2, -⟩ |
        ⟨c, hCc, hc2, h1, h2, h3, h4⟩ | ⟨c, hCc, hc2, h1, h2, h3, h4⟩
    · exact (false_of_card_of_sq K hAC hab h64 (hmem hCab).1 (hmem hCab).2 ha2 hb2).elim
    · exact (false_of_card_of_sq K hAC hab h64 (hmem hCab).1 (hmem hCab).2 ha2 hb2).elim
    · exact arch76Lemma2_index_two K hρodd hCA hC hne P hTP hP hE hCc hc2
        (Or.inl ⟨h1, h2, h3, h4⟩)
    · exact arch76Lemma2_index_two K hρodd hCA hC hne P hTP hP hE hCc hc2
        (Or.inr ⟨h1, h2, h3, h4⟩)
  · exact arch76Lemma2_index_four K hCA h128 P hTP hP

end CFSG.CGT.Stroth76
