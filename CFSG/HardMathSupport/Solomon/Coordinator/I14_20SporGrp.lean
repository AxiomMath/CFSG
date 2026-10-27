module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Fi22
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem five_mul_card_dvd {S Q : Type} [Group S] [Finite S] [Group Q]
    (hcenQ : Subgroup.center Q = ⊥) {x : S} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    {H : Subgroup S} (hHx : H ≤ Subgroup.centralizer ({x} : Set S))
    (N : Subgroup H) [N.Normal] (hc : Nat.Coprime 5 (Nat.card N)) (φ : H ⧸ N ≃* Q) :
    5 * Nat.card Q ∣ Nat.card S := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  set K : Subgroup S := Subgroup.zpowers x with hK
  have hKcard : Nat.card K = 5 := by
    rw [hK, Nat.card_zpowers, hord]
  have hcomm : ∀ h ∈ H, Commute h x := fun h hh =>
    (Subgroup.mem_centralizer_iff.1 (hHx hh) x rfl).symm
  have hxH : x ∉ H := by
    intro hx
    let xh : H := ⟨x, hx⟩
    have hz : φ (QuotientGroup.mk xh) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨q, rfl⟩ := φ.surjective b
      obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective q
      rw [← map_mul, ← map_mul]
      congr 1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (hcomm h' h'.2).eq
    rw [hcenQ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hz
    have hord' : orderOf (⟨xh, hz⟩ : N) = 5 := by
      calc orderOf (⟨xh, hz⟩ : N) = orderOf (((⟨xh, hz⟩ : N) : H)) :=
            (Subgroup.orderOf_coe _).symm
        _ = orderOf ((xh : H) : S) := (Subgroup.orderOf_coe _).symm
        _ = 5 := hord
    have : 5 ∣ Nat.card N := hord' ▸ orderOf_dvd_natCard _
    have := Nat.Coprime.eq_one_of_dvd hc this
    omega
  have hinf : H ⊓ K = ⊥ := by
    have hle : H ⊓ K ≤ K := inf_le_right
    have hd : Nat.card (H ⊓ K : Subgroup S) ∣ 5 := hKcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h5
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : H ⊓ K = K := Subgroup.eq_of_le_of_card_ge hle (by
        rw [hKcard, h5])
      apply hxH
      have : x ∈ H ⊓ K := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact this.1
  let f : H × K →* S := (H.subtype).noncommCoprod K.subtype (by
    rintro h ⟨k, hk⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((hcomm h h.2).zpow_right m))
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨h, k⟩ hhk
    rw [MonoidHom.mem_ker] at hhk
    have hh : f (h, k) = (h : S) * k := rfl
    rw [hh] at hhk
    have hmem : (h : S) ∈ H ⊓ K := by
      refine ⟨h.2, ?_⟩
      have : (h : S) = (k : S)⁻¹ := eq_inv_of_mul_eq_one_left hhk
      rw [this]
      exact K.inv_mem k.2
    rw [hinf, Subgroup.mem_bot] at hmem
    have h1 : h = 1 := Subtype.ext hmem
    have hk1 : (k : S) = 1 := by
      rw [h1] at hhk
      simpa using hhk
    rw [Subgroup.mem_bot]
    exact Prod.ext h1 (Subtype.ext hk1)
  have hD : Nat.card f.range = Nat.card H * 5 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod, hKcard]
  have hH : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hHQ : Nat.card (H ⧸ N) = Nat.card Q := Nat.card_congr φ.toEquiv
  have hdvd : Nat.card f.range ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _
  refine Dvd.dvd.trans ?_ hdvd
  rw [hD, hH, hHQ]
  exact ⟨Nat.card N, by ring⟩

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
