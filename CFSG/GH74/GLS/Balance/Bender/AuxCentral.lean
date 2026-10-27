module

public import CFSG.GH74.GLS.Balance.Bender.Aux2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance.BenderExt

theorem aux52_mem_and_coprime_of_mem_oResOf {p : ℕ} {H : Type} [Group H] {X N : Subgroup H}
    (hNX : N ≤ X) (hcent : ∀ n ∈ N, ∀ x ∈ X, n * x = x * n) {t : H} (ht : t ∈ oResOf p N) :
    t ∈ N ∧ Nat.Coprime (orderOf t) p := by
  rw [oResOf_eq_closure] at ht
  induction ht using Subgroup.closure_induction with
  | mem x hx => exact ⟨hx.1, hx.2⟩
  | one => exact ⟨N.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    refine ⟨N.mul_mem hx.1 hy.1, ?_⟩
    have hc : Commute x y := hcent x hx.1 y (hNX hy.1)
    exact Nat.Coprime.coprime_dvd_left hc.orderOf_mul_dvd_mul_orderOf (Nat.Coprime.mul_left hx.2 hy.2)
  | inv x _ hx => exact ⟨N.inv_mem hx.1, by rw [orderOf_inv]; exact hx.2⟩

theorem aux52_coprime_card_oResOf {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] {X N : Subgroup H}
    (hNX : N ≤ X) (hcent : ∀ n ∈ N, ∀ x ∈ X, n * x = x * n) :
    Nat.Coprime p (Nat.card ↥(oResOf p N)) := by
  have hp : p.Prime := Fact.out
  by_contra h
  rw [Nat.Prime.coprime_iff_not_dvd hp, not_not] at h
  obtain ⟨⟨t, ht⟩, hord⟩ := exists_prime_orderOf_dvd_card' p h
  have h1 : Nat.Coprime (orderOf t) p := (aux52_mem_and_coprime_of_mem_oResOf hNX hcent ht).2
  have h2 : orderOf t = p := by rw [← hord]; exact (Subgroup.orderOf_mk t ht).symm
  rw [h2] at h1
  exact hp.one_lt.ne' ((Nat.coprime_self p).mp h1)


theorem bender_q42iii {p : ℕ} [Fact p.Prime] : BenderQ42iii p := by
  intro H _ _ X A N hNn _hAX hA hNX hcent
  have hp : p.Prime := Fact.out
  have hgN : ∀ g : H, g ∈ normalizer (N : Set H) := fun g => by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hNn.conj_mem h hh g, fun hh => ?_⟩
    have := hNn.conj_mem _ hh g⁻¹
    simpa [mul_assoc] using this
  apply le_antisymm
  ·
    refine oResOf_le_of fun z hz hzcop => ?_
    obtain ⟨hzX, hzC⟩ := hz
    obtain ⟨x₀, hx₀X, hx₀z⟩ := hzX
    obtain ⟨⟨x, hxX⟩, hxz, hxcop'⟩ :=
      exists_coprime_lift hp ((QuotientGroup.mk' N).comp X.subtype) hzcop (a₀ := ⟨x₀, hx₀X⟩) hx₀z
    have hxcop : Nat.Coprime (orderOf x) p := by simpa using hxcop'
    have hxz' : QuotientGroup.mk' N x = z := hxz
    have hna : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N := by
      intro a ha
      have hcomm : QuotientGroup.mk' N a * z = z * QuotientGroup.mk' N a :=
        mem_centralizer_iff.mp hzC (QuotientGroup.mk' N a) ⟨a, ha, rfl⟩
      rw [← hxz'] at hcomm
      have h1 : QuotientGroup.mk' N (x⁻¹ * (a * x * a⁻¹)) = 1 := by
        have : (QuotientGroup.mk' N x)⁻¹ * (QuotientGroup.mk' N a * QuotientGroup.mk' N x *
            (QuotientGroup.mk' N a)⁻¹) = 1 := by rw [hcomm]; group
        simpa [map_mul, map_inv] using this
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hna' : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ oResOf p N := by
      intro a ha
      refine mem_oResOf (hna a ha) ?_
      have hnN : x⁻¹ * (a * x * a⁻¹) ∈ N := hna a ha
      set n := x⁻¹ * (a * x * a⁻¹) with hn
      have hxn : Commute x n := (hcent n hnN x hxX).symm
      have hconj : a * x * a⁻¹ = x * n := by rw [hn]; group
      have hord : orderOf (x * n) = orderOf x := by
        rw [← hconj]
        exact orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective x
      have hc1 : Commute x⁻¹ (x * n) := ((Commute.refl x).inv_left).mul_right hxn.inv_left
      have hnorder : orderOf n ∣ orderOf x * orderOf x := by
        have h1 := hc1.orderOf_mul_dvd_mul_orderOf
        rw [orderOf_inv, hord] at h1
        have : x⁻¹ * (x * n) = n := by group
        rwa [this] at h1
      exact Nat.Coprime.coprime_dvd_left hnorder (Nat.Coprime.mul_left hxcop hxcop)
    have hN'n : (oResOf p N).Normal := ⟨fun t ht g => conj_mem_oResOf (hgN g) ht⟩
    have hcop : Nat.Coprime p (Nat.card ↥(oResOf p N)) := aux52_coprime_card_oResOf hNX hcent
    have : Fact (IsPGroup p ↥A) := ⟨hA⟩
    have hcentral : centralizer ((A.map (QuotientGroup.mk' (oResOf p N)) :
        Subgroup (H ⧸ oResOf p N)) : Set (H ⧸ oResOf p N)) =
        (centralizer (A : Set H)).map (QuotientGroup.mk' (oResOf p N)) :=
      centralizer_map_quotient_eq_map_centralizer p A (oResOf p N) hN'n hcop
    have hxmem : QuotientGroup.mk' (oResOf p N) x ∈ centralizer ((A.map (QuotientGroup.mk' (oResOf p N)) :
        Subgroup (H ⧸ oResOf p N)) : Set (H ⧸ oResOf p N)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have h1 : QuotientGroup.mk' (oResOf p N) (x⁻¹ * (a * x * a⁻¹)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (hna' a ha)
      simp only [map_mul, map_inv] at h1
      calc QuotientGroup.mk' (oResOf p N) a * QuotientGroup.mk' (oResOf p N) x
          = QuotientGroup.mk' (oResOf p N) x * ((QuotientGroup.mk' (oResOf p N) x)⁻¹ *
              (QuotientGroup.mk' (oResOf p N) a * QuotientGroup.mk' (oResOf p N) x *
                (QuotientGroup.mk' (oResOf p N) a)⁻¹)) * QuotientGroup.mk' (oResOf p N) a := by group
        _ = QuotientGroup.mk' (oResOf p N) x * QuotientGroup.mk' (oResOf p N) a := by rw [h1]; group
    rw [hcentral] at hxmem
    obtain ⟨c, hcA, hcx⟩ := hxmem
    have hm : x⁻¹ * c ∈ oResOf p N := QuotientGroup.eq.mp hcx.symm
    obtain ⟨hmN, hmcop⟩ := aux52_mem_and_coprime_of_mem_oResOf hNX hcent hm
    have hcxm : c = x * (x⁻¹ * c) := by group
    have hcX : c ∈ X := by
      rw [hcxm]; exact X.mul_mem hxX (hNX hmN)
    have hqc : QuotientGroup.mk' N c = z := by
      have h1 : QuotientGroup.mk' N (x⁻¹ * c) = 1 := (QuotientGroup.eq_one_iff _).mpr hmN
      rw [hcxm, map_mul, h1, mul_one]; exact hxz'
    have hccop : Nat.Coprime (orderOf c) p := by
      have hxm : Commute x (x⁻¹ * c) := (hcent _ hmN x hxX).symm
      have h1 := hxm.orderOf_mul_dvd_mul_orderOf
      rw [← hcxm] at h1
      exact Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.mul_left hxcop hmcop)
    exact ⟨c, mem_oResOf (Subgroup.mem_inf.mpr ⟨hcX, hcA⟩) hccop, hqc⟩
  ·
    rw [Subgroup.map_le_iff_le_comap]
    refine oResOf_le_of fun x hx hxcop => ?_
    obtain ⟨hxX, hxA⟩ := hx
    rw [Subgroup.mem_comap]
    refine mem_oResOf (Subgroup.mem_inf.mpr ⟨⟨x, hxX, rfl⟩, ?_⟩)
      (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd (QuotientGroup.mk' N) x) hxcop)
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hcomm : a * x = x * a := (mem_centralizer_iff.mp hxA a ha)
    rw [← map_mul, ← map_mul, hcomm]
