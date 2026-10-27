module

public import CFSG.ClassicalInvolution.AschTight.Sec71Cap2
public import CFSG.ClassicalInvolution.AschTight.Sec71Rel

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

omit [Finite G] in
theorem orderOf_conj' (g u : G) : orderOf (g * u * g⁻¹) = orderOf u := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) u
  rwa [MulAut.conj_apply] at this

omit [Finite G] in
theorem DData.conj (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    DData Ω W (conjSub g R) (conjSub g K) (g * u * g⁻¹) (g * r * g⁻¹) (g * z * g⁻¹) := by
  have hgW : conjSub g W = W := mem_normalizer_iff_conjSub_eq.mp hg
  have hU : conjSub g (Subgroup.zpowers u) = Subgroup.zpowers (g * u * g⁻¹) :=
    AscL62.conjSub_zpowers_eq g u
  refine ⟨hΩ.conjInvariant g K hd.memK, hd.sylow.conj g, ⟨RSet.conj hΩ.conjInvariant hd.memD.1 g,
    hgW ▸ Sec7.conjSub_le_normalizer hd.memD.2 g⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hU, ← hd.inf_eq, conjSub_inf, hgW]
  · rw [← hU]
    exact conjSub_mono hd.U_le_R
  · rw [← hU]
    exact USet.conj hΩ.conjInvariant hd.memU g
  · rw [← hgW]
    exact Sec7.conjSub_le_normalizer hd.le_normalizer g
  · rw [orderOf_conj', natCard_conjSub]
    exact hd.card
  · rw [orderOf_conj']
    exact hd.orderOf_eq
  · rw [orderOf_conj']
    exact hd.four_le
  · exact hd.uinv.conj g
  · rw [orderOf_conj', conj_pow, hd.z_eq]
  · exact conj_mem_conjSub hd.r_mem
  · rw [← hU, mem_conjSub_iff]
    intro h
    apply hd.r_not_mem
    simpa [mul_assoc] using h
  · calc g * r * g⁻¹ * (g * u * g⁻¹) * (g * r * g⁻¹)⁻¹ = g * (r * u * r⁻¹) * g⁻¹ := by group
      _ = (g * u * g⁻¹)⁻¹ := by rw [hd.conj_u]; group
  · calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hd.sq_r]
  · intro x hx
    rw [mem_conjSub_iff] at hx
    rw [← hU]
    rcases hd.cover _ hx with h | ⟨y, hy, he⟩
    · left
      rw [mem_conjSub_iff]
      exact h
    · right
      refine ⟨g * y * g⁻¹, conj_mem_conjSub hy, ?_⟩
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * (y * r) * g⁻¹ := by rw [he]
        _ = g * y * g⁻¹ * (g * r * g⁻¹) := by group

theorem DData.r_mem_normalizer_Y₀ (hd : DData Ω W R K u r z) {i : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) : r ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
  refine mem_normalizer_Y₀ hd.r_normW (mem_normalizer_UV ?_ ?_)
  · rw [hd.conj_u]
    exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
  · rw [hi]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) i))

theorem DData.t_mem_normalizer_Y₀ (hd' : DData Ω W T J v t j) {k : ℤ}
    (hk : t * u * t⁻¹ = u * v ^ k) : t ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
  refine mem_normalizer_Y₀ hd'.r_normW (mem_normalizer_UV ?_ ?_)
  · rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) k))
  · rw [hd'.conj_u]
    exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers v))

theorem inf_eq_bot_of_ne (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hzj : z ≠ j) : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨n, hn⟩ := hd'.orderOf_eq
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) := hV2.to_le (Subgroup.zpowers_le.mpr hx.2)
  have hxc : 2 ≤ Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    omega
  have hjx : j ∈ Subgroup.zpowers x :=
    hd'.uinv.mem_of_le ((Subgroup.zpowers_le.mpr hx.2).trans hd'.U_le_K) hx2 hxc
  have hjK : j ∈ K := hd.U_le_K ((Subgroup.zpowers_le.mpr hx.1) hjx)
  exact hzj ((hd.uinv.unique j hjK hd'.uinv.sq).resolve_left hd'.uinv.ne_one).symm

omit [Finite G] in
theorem eq_one_of_mul_eq_one {u v a b : G}
    (hUV : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) (ha : a ∈ Subgroup.zpowers u)
    (hb : b ∈ Subgroup.zpowers v) (hab : a * b = 1) : a = 1 := by
  have h : a ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
    refine ⟨ha, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hab]
    exact Subgroup.inv_mem _ hb
  rw [hUV] at h
  exact h

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
