module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {K : Type*} [Group K] [Finite K]

theorem eq_one_of_mem_oddCore {D : Subgroup K} (hD : IsPGroup 2 D) {x : K} (hxD : x ∈ D)
    (hxO : x ∈ fusionOddCore K) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hD) ⟨x, hxD⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x ∣ Nat.card (fusionOddCore K) := Subgroup.orderOf_dvd_natCard _ hxO
  have hodd := odd_natCard_fusionOddCore K
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  · exfalso
    have : 2 ∣ Nat.card (fusionOddCore K) := (dvd_pow_self 2 hk0).trans (hk ▸ hdvd)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)

theorem quotient_injOn_of_isPGroup {D : Subgroup K} (hD : IsPGroup 2 D) {x x' : K} (hx : x ∈ D)
    (hx' : x' ∈ D) (h : (x : K ⧸ fusionOddCore K) = (x' : K ⧸ fusionOddCore K)) : x = x' := by
  have h1 : x⁻¹ * x' ∈ fusionOddCore K := QuotientGroup.eq.1 h
  have := eq_one_of_mem_oddCore hD (D.mul_mem (D.inv_mem hx) hx') h1
  exact inv_mul_eq_one.1 this

theorem exists_equiv_map_quotient {D : Subgroup K} (hD : IsPGroup 2 D) :
    Nonempty (↥D ≃* ↥(D.map (QuotientGroup.mk' (fusionOddCore K)))) := by
  let φ : ↥D →* K ⧸ fusionOddCore K := (QuotientGroup.mk' (fusionOddCore K)).comp D.subtype
  have hφ : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext (quotient_injOn_of_isPGroup hD a.2 b.2 hab)
  have hr : φ.range = D.map (QuotientGroup.mk' (fusionOddCore K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)⟩

theorem wreathData_of_conj {Γ : Type*} [Group Γ] {N₁ N₂ : Subgroup Γ} {σ : Γ}
    (hσ2 : σ * σ = 1) (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : Disjoint N₁ N₂)
    (hconj : N₁.map (MulAut.conj σ).toMonoidHom = N₂) : WreathData N₁ N₂ σ where
  comm := hcomm
  disj := hdisj
  sq := hσ2
  swap₁ a ha := by
    rw [← hconj]
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  swap₂ b hb := by
    rw [← hconj] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have h1 : σ * ((MulAut.conj σ).toMonoidHom a) * σ⁻¹ = a := by
      show σ * (σ * a * σ⁻¹) * σ⁻¹ = a
      calc σ * (σ * a * σ⁻¹) * σ⁻¹ = (σ * σ) * a * (σ * σ)⁻¹ := by group
        _ = a := by rw [hσ2]; group
    rw [h1]
    exact ha

theorem commutator_le_of_index_two {Γ : Type*} [Group Γ] {H : Subgroup Γ} (h : H.index = 2) :
    _root_.commutator Γ ≤ H := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  simp only [Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff]
  tauto

theorem swap_inner_on_D_wreath {z t y : K} (hz2 : z * z = 1)
    {N₁ N₂ : Subgroup (K ⧸ fusionOddCore K)} (e₁ : ↥N₁ ≃* alternatingGroup (Fin 6))
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : Disjoint N₁ N₂)
    (hidx : (N₁ ⊔ N₂).index = 2)
    (hzN : (QuotientGroup.mk z : K ⧸ fusionOddCore K) ∉ N₁ ⊔ N₂)
    (hconj : N₁.map (MulAut.conj (QuotientGroup.mk z : K ⧸ fusionOddCore K)).toMonoidHom = N₂)
    {D : Subgroup K} (hD8 : Nat.card D = 8) (hD2 : IsPGroup 2 D)
    (hDK : D ≤ _root_.commutator K) (hDz : ∀ x ∈ D, z * x = x * z) (htD : t ∈ D)
    (htc : ∀ x ∈ D, t * x = x * t) (hyD : ∀ x ∈ D, y * x * y⁻¹ ∈ D)
    (hyD' : ∀ x ∈ D, y⁻¹ * x * y ∈ D) (hyz : y * z * y⁻¹ = z * t) :
    ∃ d ∈ D, ∀ x ∈ D, y * x * y⁻¹ = d * x * d⁻¹ := by
  classical
  let q : K →* K ⧸ fusionOddCore K := QuotientGroup.mk' (fusionOddCore K)
  let σ : K ⧸ fusionOddCore K := QuotientGroup.mk z
  have hσ2 : σ * σ = 1 := by
    show (QuotientGroup.mk z : K ⧸ fusionOddCore K) * QuotientGroup.mk z = 1
    rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
  have hW : WreathData N₁ N₂ σ := wreathData_of_conj hσ2 hcomm hdisj hconj
  let P : Subgroup (K ⧸ fusionOddCore K) := D.map q
  obtain ⟨eDP⟩ := exists_equiv_map_quotient hD2
  have hP8 : Nat.card P = 8 := by
    rw [← hD8]
    exact (Nat.card_congr eDP.toEquiv).symm
  have hPN : P ≤ N₁ ⊔ N₂ := by
    rintro _ ⟨x, hx, rfl⟩
    apply commutator_le_of_index_two hidx
    have := map_derivedSeries_le_derivedSeries q 1
    rw [derivedSeries_one, derivedSeries_one] at this
    exact this ⟨x, hDK hx, rfl⟩
  have hqσ : q z = σ := rfl
  have hPσ : ∀ x ∈ P, σ * x * σ⁻¹ = x := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : z * x * z⁻¹ = x := by rw [hDz x hx]; group
    calc σ * q x * σ⁻¹ = q z * q x * (q z)⁻¹ := rfl
      _ = q (z * x * z⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = q x := by rw [h1]
  have htP : q t ∈ P := ⟨t, htD, rfl⟩
  have htc' : ∀ x ∈ P, q t * x = x * q t := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, htc x hx]
  have key : ∀ y' : K, q y' ∈ N₁ ⊔ N₂ → (∀ x ∈ D, y' * x * y'⁻¹ ∈ D) →
      (∀ x ∈ D, y'⁻¹ * x * y' ∈ D) → y' * z * y'⁻¹ = z * t →
      ∃ d ∈ D, ∀ x ∈ D, y' * x * y'⁻¹ = d * x * d⁻¹ := by
    intro y' hy'N hy'D hy'D' hy'z
    have hyP : ∀ x ∈ P, q y' * x * (q y')⁻¹ ∈ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨y' * x * y'⁻¹, hy'D x hx, by rw [map_mul, map_mul, map_inv]⟩
    have hyP' : ∀ x ∈ P, (q y')⁻¹ * x * q y' ∈ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨y'⁻¹ * x * y', hy'D' x hx, by rw [map_mul, map_mul, map_inv]⟩
    have hyσ : q y' * σ * (q y')⁻¹ = σ * q t := by
      calc q y' * σ * (q y')⁻¹ = q y' * q z * (q y')⁻¹ := rfl
        _ = q (y' * z * y'⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = σ * q t := by rw [hy'z, map_mul]; rfl
    obtain ⟨db, hdbP, hdb⟩ := wreath_inner_on_diag hW e₁ hP8 hPN hPσ htP htc' hy'N hyP hyP'
      hyσ
    obtain ⟨d, hdD, rfl⟩ := hdbP
    refine ⟨d, hdD, fun x hx => ?_⟩
    refine quotient_injOn_of_isPGroup hD2 (hy'D x hx) (D.mul_mem (D.mul_mem hdD hx) (D.inv_mem hdD))
      ?_
    have := hdb (q x) ⟨x, hx, rfl⟩
    show q (y' * x * y'⁻¹) = q (d * x * d⁻¹)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    exact this
  by_cases hyN : q y ∈ N₁ ⊔ N₂
  · exact key y hyN hyD hyD' hyz
  · have hyzN : q (y * z) ∈ N₁ ⊔ N₂ := by
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hyN hzN
    have h1 : ∀ x ∈ D, y * z * x * (y * z)⁻¹ = y * x * y⁻¹ := by
      intro x hx
      calc y * z * x * (y * z)⁻¹ = y * (z * x) * z⁻¹ * y⁻¹ := by group
        _ = y * (x * z) * z⁻¹ * y⁻¹ := by rw [hDz x hx]
        _ = y * x * y⁻¹ := by group
    have h2 : ∀ x ∈ D, (y * z)⁻¹ * x * (y * z) = y⁻¹ * x * y := by
      intro x hx
      have hzx : z⁻¹ * x * z = x := by
        calc z⁻¹ * x * z = z⁻¹ * (x * z) := by group
          _ = z⁻¹ * (z * x) := by rw [hDz x hx]
          _ = x := by group
      calc (y * z)⁻¹ * x * (y * z) = z⁻¹ * (y⁻¹ * x * y) * z := by group
        _ = y⁻¹ * x * y := by
          have hm := hyD' x hx
          have hzc : z⁻¹ * (y⁻¹ * x * y) * z = y⁻¹ * x * y := by
            have := hDz (y⁻¹ * x * y) hm
            calc z⁻¹ * (y⁻¹ * x * y) * z = z⁻¹ * ((y⁻¹ * x * y) * z) := by group
              _ = z⁻¹ * (z * (y⁻¹ * x * y)) := by rw [this]
              _ = y⁻¹ * x * y := by group
          exact hzc
    have hyzz : y * z * z * (y * z)⁻¹ = z * t := by
      calc y * z * z * (y * z)⁻¹ = y * z * y⁻¹ := by group
        _ = z * t := hyz
    obtain ⟨d, hdD, hd⟩ := key (y * z) hyzN (fun x hx => by rw [h1 x hx]; exact hyD x hx)
      (fun x hx => by rw [h2 x hx]; exact hyD' x hx) (by
        calc y * z * z * (y * z)⁻¹ = y * z * y⁻¹ := by group
          _ = z * t := hyz)
    exact ⟨d, hdD, fun x hx => by rw [← h1 x hx]; exact hd x hx⟩

end CFSG.EvenSporadicStandard.Fin76b
