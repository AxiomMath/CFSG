module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits

variable {q : ℕ} [Fact q.Prime]

theorem isPGroup_of_forall_coprime {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, Nat.Coprime (orderOf x) q → x = 1) : IsPGroup q G := by
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro r hr hdvd
  by_contra hrq
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) r hdvd
  have hcop : Nat.Coprime (orderOf x) q := by
    rw [hx]
    exact (Nat.coprime_primes hr Fact.out).2 hrq
  have h1 := h x hcop
  rw [h1, orderOf_one] at hx
  exact hr.one_lt.ne hx

theorem orderOf_conj_eq {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

theorem eq_one_of_commute_of_orderOf_mul {G : Type*} [Group G] [Finite G] {x z : G}
    (hxz : Commute z x) (hz : ∃ k, orderOf z = q ^ k) (hx : Nat.Coprime (orderOf x) q)
    (hord : orderOf (z * x) = orderOf x) : z = 1 := by
  obtain ⟨k, hk⟩ := hz
  have hcop : Nat.Coprime (orderOf z) (orderOf x) := by
    rw [hk]
    exact Nat.Coprime.pow_left k hx.symm
  have h1 := hxz.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  rw [hord] at h1
  have hpos : 0 < orderOf x := orderOf_pos x
  have h2 : orderOf z = 1 := by
    have h3 : orderOf z * orderOf x = 1 * orderOf x := by rw [one_mul]; exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  exact orderOf_eq_one_iff.1 h2

theorem eq_one_of_mem_pGroup_of_coprime {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup q P) {x : G} (hx : x ∈ P) (hxo : Nat.Coprime (orderOf x) q) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨x, hx⟩
  have hk' : orderOf x = q ^ k := by
    have := Subgroup.orderOf_coe (⟨x, hx⟩ : P)
    rw [hk] at this
    exact this
  rw [hk'] at hxo
  have hk0 : k = 0 := by
    by_contra hk0
    have hq : q ∣ q ^ k := dvd_pow_self q hk0
    have := Nat.Coprime.eq_one_of_dvd hxo.symm hq
    exact (Fact.out : q.Prime).one_lt.ne' this
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
  exact hk'

theorem centralizer_pCoreOf_le {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    (hkey : ∀ x ∈ N, (∀ t ∈ pCoreOf q N, x * t = t * x) → Nat.Coprime (orderOf x) q → x = 1) :
    ∀ h ∈ N, (∀ t ∈ pCoreOf q N, h * t = t * h) → h ∈ pCoreOf q N := by
  intro h hh hc
  set T := pCoreOf q N with hT
  have hNT : N ≤ Subgroup.normalizer (T : Set H) := le_normalizer_pCoreOf q N
  set C : Subgroup H := N ⊓ Subgroup.centralizer (T : Set H) with hC
  have hCp : IsPGroup q C := by
    refine isPGroup_of_forall_coprime fun x hx => ?_
    have hxC := x.2
    obtain ⟨hxN, hxT⟩ := Subgroup.mem_inf.1 hxC
    have hxT' : ∀ t ∈ T, (x : H) * t = t * x := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 hxT t ht).symm
    have hord : Nat.Coprime (orderOf (x : H)) q := by
      rw [Subgroup.orderOf_coe]
      exact hx
    exact Subtype.ext (hkey x hxN hxT' hord)
  have hCN : C ≤ N := inf_le_left
  have hCnorm : (C.subgroupOf N).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxN, hxT⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨N.mul_mem (N.mul_mem g.2 hxN) (N.inv_mem g.2), ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
    have hgt : (g : H)⁻¹ * t * (g : H) ∈ T := by
      have hginv : (g : H)⁻¹ ∈ Subgroup.normalizer (T : Set H) := inv_mem (hNT g.2)
      have := (Subgroup.mem_normalizer_iff.1 hginv t).1 ht
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hxT _ hgt
    calc t * ((g : H) * x * (g : H)⁻¹) = (g : H) * (((g : H)⁻¹ * t * (g : H)) * x) * (g : H)⁻¹ := by
          group
      _ = (g : H) * (x * ((g : H)⁻¹ * t * (g : H))) * (g : H)⁻¹ := by rw [h1]
      _ = ((g : H) * x * (g : H)⁻¹) * t := by group
  have hle : C ≤ pCoreOf q N := le_pCoreOf q hCN hCnorm hCp
  exact hle (Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun t ht => (hc t ht).symm⟩)

theorem constrained_normalizer_of_le_core {H : Type*} [Group H] [Finite H] (M : Subgroup H)
    (hM : ∀ h ∈ M, (∀ r ∈ pCoreOf q M, h * r = r * h) → h ∈ pCoreOf q M)
    {Q : Subgroup H} (hQ : Q ≤ pCoreOf q M)
    (hNM : Subgroup.normalizer (Q : Set H) ≤ M) :
    ∀ h ∈ Subgroup.normalizer (Q : Set H),
      (∀ t ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)), h * t = t * h) →
      h ∈ pCoreOf q (Subgroup.normalizer (Q : Set H)) := by
  set O := pCoreOf q M with hO
  set N := Subgroup.normalizer (Q : Set H) with hN
  set T := pCoreOf q N with hT
  have hOp : IsPGroup q O := pCoreOf_isPGroup q M
  have hMO : M ≤ Subgroup.normalizer (O : Set H) := le_normalizer_pCoreOf q M
  have hON : O ⊓ N ≤ T := by
    refine le_pCoreOf q inf_le_right ?_ (hOp.to_le inf_le_left)
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxO, hxN⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, N.mul_mem (N.mul_mem g.2 hxN) (N.inv_mem g.2)⟩
    have hgO := (Subgroup.mem_normalizer_iff.1 (hMO (hNM g.2)) (x : H)).1 hxO
    exact hgO
  have key : ∀ x ∈ N, (∀ t ∈ T, x * t = t * x) → Nat.Coprime (orderOf x) q → x = 1 := by
    intro x hxN hxT hxo
    have hxM : x ∈ M := hNM hxN
    have hxnO : x ∈ Subgroup.normalizer (O : Set H) := hMO hxM
    have hQN : Q ≤ O ⊓ N := le_inf hQ Subgroup.le_normalizer
    set D : Subgroup H := O ⊓ Subgroup.centralizer ({x} : Set H) with hD
    have hmemD : ∀ d, d ∈ D ↔ d ∈ O ∧ x * d = d * x := fun d => by
      rw [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      exact and_congr_right fun _ => eq_comm
    have hQD : Q ≤ D := fun r hr =>
      (hmemD r).2 ⟨hQ hr, hxT r (hON (hQN hr))⟩
    have hcentO : ∀ o ∈ O, x * o = o * x := by
      by_contra hcon
      push Not at hcon
      obtain ⟨o₀, ho₀, ho₀ne⟩ := hcon
      haveI : Group.IsNilpotent ↥O := hOp.isNilpotent
      set D' : Subgroup ↥O := D.subgroupOf O with hD'
      have hlt : D' < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have h1 : (⟨o₀, ho₀⟩ : ↥O) ∈ D' := by rw [htop]; exact Subgroup.mem_top _
        have h2 : o₀ ∈ D := h1
        exact ho₀ne ((hmemD o₀).1 h2).2
      obtain ⟨y, hyN, hyD⟩ : ∃ y : ↥O, y ∈ Subgroup.normalizer ((D' : Subgroup ↥O) : Set ↥O) ∧
          y ∉ D' := by
        have h1 := Group.normalizerCondition_of_isNilpotent (G := ↥O) D' hlt
        by_contra hcon
        push Not at hcon
        apply h1.not_ge
        intro y hy
        by_contra hy'
        exact hy' (hcon y hy)
      set yH : H := (y : H) with hyH
      have hyO : yH ∈ O := y.2
      have hyxne : x * yH ≠ yH * x := fun h => hyD ((hmemD yH).2 ⟨hyO, h⟩)
      have hyD' : ∀ d ∈ D, yH * d * yH⁻¹ ∈ D := by
        intro d hd
        have hdO : d ∈ O := ((hmemD d).1 hd).1
        have h1 : (⟨d, hdO⟩ : ↥O) ∈ D' := hd
        have h2 := (Subgroup.mem_normalizer_iff.1 hyN ⟨d, hdO⟩).1 h1
        exact h2
      obtain ⟨u, hu⟩ : ∃ u : H, u = x * yH * x⁻¹ := ⟨_, rfl⟩
      obtain ⟨z, hz⟩ : ∃ z : H, z = yH⁻¹ * u := ⟨_, rfl⟩
      have huO : u ∈ O := by
        have := (Subgroup.mem_normalizer_iff.1 hxnO yH).1 hyO
        rwa [← hu] at this
      have hzO : z ∈ O := by
        rw [hz]
        exact O.mul_mem (O.inv_mem hyO) huO
      have hzcent : ∀ d ∈ D, z * d = d * z := by
        intro d hd
        have hxd : x * d = d * x := ((hmemD d).1 hd).2
        have hw := hyD' d hd
        have hxw : x * (yH * d * yH⁻¹) = (yH * d * yH⁻¹) * x := ((hmemD _).1 hw).2
        have h1 : x⁻¹ * d * x = d := by
          calc x⁻¹ * d * x = x⁻¹ * (d * x) := by group
            _ = x⁻¹ * (x * d) := by rw [hxd]
            _ = d := by group
        have h2 : u * d * u⁻¹ = yH * d * yH⁻¹ := by
          calc u * d * u⁻¹ = x * yH * (x⁻¹ * d * x) * yH⁻¹ * x⁻¹ := by rw [hu]; group
            _ = x * (yH * d * yH⁻¹) * x⁻¹ := by rw [h1]; group
            _ = (yH * d * yH⁻¹) := by rw [hxw]; group
        have h3 : z * d * z⁻¹ = d := by
          calc z * d * z⁻¹ = yH⁻¹ * (u * d * u⁻¹) * yH := by rw [hz]; group
            _ = yH⁻¹ * (yH * d * yH⁻¹) * yH := by rw [h2]
            _ = d := by group
        calc z * d = (z * d * z⁻¹) * z := by group
          _ = d * z := by rw [h3]
      have hzN : z ∈ N := by
        rw [hN, Subgroup.mem_normalizer_iff]
        intro r
        constructor
        · intro hr
          have hzr : z * r * z⁻¹ = r := by
            have := hzcent r (hQD hr)
            calc z * r * z⁻¹ = (r * z) * z⁻¹ := by rw [this]
              _ = r := by group
          rw [hzr]
          exact hr
        · intro h
          have hc := hzcent _ (hQD h)
          have hzr : z * r * z⁻¹ = r := by
            calc z * r * z⁻¹ = z⁻¹ * (z * (z * r * z⁻¹)) := by group
              _ = z⁻¹ * ((z * r * z⁻¹) * z) := by rw [hc]
              _ = r := by group
          rw [hzr] at h
          exact h
      have hzT : z ∈ T := hON (Subgroup.mem_inf.2 ⟨hzO, hzN⟩)
      have hxz : x * z = z * x := hxT z hzT
      have hzx : z * x = yH⁻¹ * x * yH⁻¹⁻¹ := by
        calc z * x = yH⁻¹ * (x * yH * x⁻¹) * x := by rw [hz, hu]
          _ = yH⁻¹ * x * yH⁻¹⁻¹ := by group
      have hord : orderOf (z * x) = orderOf x := by
        rw [hzx]
        exact orderOf_conj_eq yH⁻¹ x
      have hzo : ∃ k, orderOf z = q ^ k := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hOp) ⟨z, hzO⟩
        exact ⟨k, by rw [← Subgroup.orderOf_coe (⟨z, hzO⟩ : O)] at hk; exact hk⟩
      have hz1 : z = 1 :=
        eq_one_of_commute_of_orderOf_mul (show Commute z x from hxz.symm) hzo hxo hord
      apply hyxne
      have h7 : yH⁻¹ * (x * yH * x⁻¹) = 1 := by rw [← hu, ← hz]; exact hz1
      calc x * yH = (x * yH * x⁻¹) * x := by group
        _ = yH * x := by
          have h8 : x * yH * x⁻¹ = yH := by
            calc x * yH * x⁻¹ = yH * (yH⁻¹ * (x * yH * x⁻¹)) := by group
              _ = yH := by rw [h7, mul_one]
          rw [h8]
    have hxO : x ∈ O := hM x hxM hcentO
    exact eq_one_of_mem_pGroup_of_coprime hOp hxO hxo
  exact centralizer_pCoreOf_le N key

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
