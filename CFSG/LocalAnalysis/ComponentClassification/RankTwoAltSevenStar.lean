module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenGW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsS5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenConj

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

theorem exists_perm_of_mulAut {Q : Type*} [Group Q] (θ : Q ≃* alternatingGroup (Fin 5))
    (ξ : MulAut Q) : ∃ ζ : Perm (Fin 5), ∀ q : Q,
      (θ (ξ q) : Perm (Fin 5)) = ζ * θ q * ζ⁻¹ := by
  obtain ⟨ζ, hζ⟩ := conjPerm_surjective (n := 5) (Or.inl rfl) (MulAut.congr θ ξ)
  refine ⟨ζ, fun q => ?_⟩
  rw [← conjPerm_apply, hζ, MulAut.congr_apply]
  simp

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 7)} {ψB : B ≃* alternatingGroup (Fin 7)}

theorem quotAut_bar {g : G} (hg : g ∈ normalizer (H7 ψA ψB : Set G)) {a b : G}
    (ha : a ∈ H7 ψA ψB) (hb : b ∈ H7 ψA ψB) (h : g * a * g⁻¹ = b) :
    quotAut ⟨g, hg⟩ ((⟨a, ha⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) =
      ((⟨b, hb⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) := by
  rw [quotAut_mk]
  congr 1
  exact Subtype.ext h

theorem star_quot
    [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))) :
    (⟨(c1 ψA * cr ψB) ^ 2, pow_mem (mul_mem (c1_mem_H7 hco) (cr_mem_H7 hco)) 2⟩ : H7 ψA ψB) ∈
      pPrimeCore 2 (H7 ψA ψB) ∧ y0 ψB * c1 ψA * (y0 ψB)⁻¹ = (c1 ψA)⁻¹ := by
  obtain ⟨θ⟩ := nonempty_quot_equiv_alt5 hco hN ht1B
  have hu := u_mem_H7 hco
  have hc := c1_mem_H7 hco
  have hr := cr_mem_H7 hco
  have core : ∀ {g : G} (hg : g ∈ H7 ψA ψB),
      ((⟨g, hg⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) = 1 → InOmega ψA ψB g :=
    fun hg h => inOmega_of_mem_core hco hN ht1B hg ((QuotientGroup.eq_one_iff _).mp h)
  set ub := ((⟨u ψA, hu⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) with hub
  set cb := ((⟨c1 ψA, hc⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) with hcb
  set rb := ((⟨cr ψB, hr⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) with hrb
  set φ : (H7 ψA ψB ⧸ pPrimeCore 2 (H7 ψA ψB)) →* Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Subtype.coe_injective.comp θ.injective
  have hφapp : ∀ q, φ q = (θ q : Perm (Fin 5)) := fun q => rfl
  obtain ⟨hu1, hu3⟩ := u_bar hco hN ht1B
  have hc3 : cb ^ 3 = 1 := by
    rw [hcb, ← QuotientGroup.mk_pow, show (⟨c1 ψA, hc⟩ : H7 ψA ψB) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact c1_pow_three), QuotientGroup.mk_one]
  have hr3 : rb ^ 3 = 1 := by
    rw [hrb, ← QuotientGroup.mk_pow, show (⟨cr ψB, hr⟩ : H7 ψA ψB) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact cr_pow_three), QuotientGroup.mk_one]
  have huc : (ub * cb) ^ 2 = 1 := by
    rw [hub, hcb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
      show ((⟨u ψA, hu⟩ : H7 ψA ψB) * ⟨c1 ψA, hc⟩) ^ 2 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact u_mul_c1_sq),
      QuotientGroup.mk_one]
  have hur : (ub * rb) ^ 2 = 1 := by
    rw [hub, hrb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
      show ((⟨u ψA, hu⟩ : H7 ψA ψB) * ⟨cr ψB, hr⟩) ^ 2 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact u_mul_cr_sq hco hodd),
      QuotientGroup.mk_one]
  have hnA := not_inOmega_A hco
  have hc1 : cb ≠ 1 := fun h => hnA.2.1 (core hc h)
  have hcu : cb ≠ ub⁻¹ := fun h => hnA.2.2 (core (mul_mem hc hu) (by
    rw [show ((⟨c1 ψA * u ψA, mul_mem hc hu⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 _) =
      cb * ub from rfl, h, inv_mul_cancel]))
  have hr1 : rb ≠ 1 := fun h => (not_inOmega_B hco (one_mem A)).1 (by
    rw [inv_one, one_mul]; exact core hr h)
  have hru : rb ≠ ub⁻¹ := fun h => (not_inOmega_B hco (inv_mem (u_mem ψA))).1 (by
    rw [inv_inv]
    exact core (mul_mem hu hr) (by
      rw [show ((⟨u ψA * cr ψB, mul_mem hu hr⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 _) =
        ub * rb from rfl, h, mul_inv_cancel]))
  have hrc : rb ≠ cb := fun h => (not_inOmega_B hco (a := c1 ψA) (ψA.symm a450).2).1
    (core (mul_mem (inv_mem hc) hr) (by
      rw [show ((⟨(c1 ψA)⁻¹ * cr ψB, mul_mem (inv_mem hc) hr⟩ : H7 ψA ψB) :
        H7 ψA ψB ⧸ pPrimeCore 2 _) = cb⁻¹ * rb from rfl, h, inv_mul_cancel]))
  have hrc' : rb ≠ cb⁻¹ := fun h =>
    (not_inOmega_B hco (a := (c1 ψA)⁻¹) (inv_mem (ψA.symm a450).2)).1 (by
    rw [inv_inv]
    exact core (mul_mem hc hr) (by
      rw [show ((⟨c1 ψA * cr ψB, mul_mem hc hr⟩ : H7 ψA ψB) : H7 ψA ψB ⧸ pPrimeCore 2 _) =
        cb * rb from rfl, h, mul_inv_cancel]))
  have hxN := xa_mem_normalizer hco
  have hyN := y0_mem_normalizer hco
  obtain ⟨ζ, hζ⟩ := exists_perm_of_mulAut θ (quotAut ⟨xa ψA, hxN⟩)
  obtain ⟨ζ', hζ'⟩ := exists_perm_of_mulAut θ (quotAut ⟨y0 ψB, hyN⟩)
  have tζ : ∀ q, ζ * φ q * ζ⁻¹ = φ (quotAut ⟨xa ψA, hxN⟩ q) := fun q => (hζ q).symm
  have tζ' : ∀ q, ζ' * φ q * ζ'⁻¹ = φ (quotAut ⟨y0 ψB, hyN⟩ q) := fun q => (hζ' q).symm
  have ξu : quotAut ⟨xa ψA, hxN⟩ ub = ub⁻¹ := quotAut_bar hxN hu (inv_mem hu) xa_conj_u
  have ξc : quotAut ⟨xa ψA, hxN⟩ cb = cb⁻¹ := quotAut_bar hxN hc (inv_mem hc) xa_conj_c1
  have ξr : quotAut ⟨xa ψA, hxN⟩ rb = rb⁻¹ := quotAut_bar hxN hr (inv_mem hr) (xa_conj_cr hco)
  have ξ'u : quotAut ⟨y0 ψB, hyN⟩ ub = ub⁻¹ :=
    quotAut_bar hyN hu (inv_mem hu) (y0_conj_u hco hodd)
  have ξ'r : quotAut ⟨y0 ψB, hyN⟩ rb = rb⁻¹ := quotAut_bar hyN hr (inv_mem hr) y0_conj_cr
  have hU3 : φ ub ^ 3 = 1 := by rw [← map_pow, show ub ^ 3 = 1 from hu3, map_one]
  have hU1 : φ ub ≠ 1 := fun h => hu1 (hφ (by rw [h, map_one]))
  have hX3 : φ cb ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hX1 : φ cb ≠ 1 := fun h => hc1 (hφ (by rw [h, map_one]))
  have hX'3 : φ rb ^ 3 = 1 := by rw [← map_pow, hr3, map_one]
  have hX'1 : φ rb ≠ 1 := fun h => hr1 (hφ (by rw [h, map_one]))
  have hUX : (φ ub * φ cb) ^ 2 = 1 := by rw [← map_mul, ← map_pow, huc, map_one]
  have hUX' : (φ ub * φ rb) ^ 2 = 1 := by rw [← map_mul, ← map_pow, hur, map_one]
  have hXU : φ cb ≠ (φ ub)⁻¹ := fun h => hcu (hφ (by rw [h, map_inv]))
  have hX'U : φ rb ≠ (φ ub)⁻¹ := fun h => hru (hφ (by rw [h, map_inv]))
  have hX'X : φ rb ≠ φ cb := fun h => hrc (hφ h)
  have hX'Xi : φ rb ≠ (φ cb)⁻¹ := fun h => hrc' (hφ (by rw [h, map_inv]))
  have hζU : ζ * φ ub * ζ⁻¹ = (φ ub)⁻¹ := by rw [tζ, ξu, map_inv]
  have hζX : ζ * φ cb * ζ⁻¹ = (φ cb)⁻¹ := by rw [tζ, ξc, map_inv]
  have hζX' : ζ * φ rb * ζ⁻¹ = (φ rb)⁻¹ := by rw [tζ, ξr, map_inv]
  have hζ'U : ζ' * φ ub * ζ'⁻¹ = (φ ub)⁻¹ := by rw [tζ', ξ'u, map_inv]
  have hζ'X' : ζ' * φ rb * ζ'⁻¹ = (φ rb)⁻¹ := by rw [tζ', ξ'r, map_inv]
  have key1 := sq_mul_eq_one_five hU3 hU1 hζU ⟨hX3, hX1, hζX, hUX, hXU⟩
    ⟨hX'3, hX'1, hζX', hUX', hX'U⟩ hX'X hX'Xi
  have hcr2 : (cb * rb) ^ 2 = 1 := hφ (by rw [map_pow, map_mul, key1, map_one])
  refine ⟨(QuotientGroup.eq_one_iff _).mp ?_, ?_⟩
  · have e : (⟨(c1 ψA * cr ψB) ^ 2, pow_mem (mul_mem hc hr) 2⟩ : H7 ψA ψB) =
        ((⟨c1 ψA, hc⟩ : H7 ψA ψB) * ⟨cr ψB, hr⟩) ^ 2 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul])
    rw [e, QuotientGroup.mk_pow, QuotientGroup.mk_mul]
    exact hcr2
  have hc5 := conj_ne_five hU3 hU1 hζ'U ⟨hX3, hX1, hUX, hXU⟩ ⟨hX'3, hX'1, hUX', hX'U⟩ hX'X hX'Xi
    key1 hζ'X'
  rcases y0_conj_c1 hco with h | h | h
  · exact h
  · exfalso
    have ξ'c : quotAut ⟨y0 ψB, hyN⟩ cb = ub⁻¹ * cb := quotAut_bar hyN hc (mul_mem (inv_mem hu) hc) h
    exact hc5.1 (by rw [tζ', ξ'c, map_mul, map_inv])
  · exfalso
    have ξ'c : quotAut ⟨y0 ψB, hyN⟩ cb = cb * ub⁻¹ := quotAut_bar hyN hc (mul_mem hc (inv_mem hu)) h
    exact hc5.2 (by rw [tζ', ξ'c, map_mul, map_inv])

theorem w_pow_three : w ψA ^ 3 = 1 := by
  show ((ψA.symm a123 : A) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, a123_pow_three, map_one, Subgroup.coe_one]

theorem star_seven
    [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))) :
    ((ψA.symm a450 : G) * (ψB.symm a450 : G)) ^ 2 = 1 := by
  obtain ⟨hcore, hy0⟩ := star_quot hco hN ht1B hodd
  have hO := inOmega_of_mem_core hco hN ht1B _ hcore
  show (c1 ψA * cr ψB) ^ 2 = 1
  set u7 := (c1 ψA * cr ψB) ^ 2 with hu7
  obtain ⟨k, hk, i, j, hkij⟩ := hO
  have hkA := (mem_inf.mp hk).1
  have hkB := (mem_inf.mp hk).2
  set W := w ψA ^ i with hW
  set V := v ψB ^ j with hV
  have hkW : Commute k W :=
    (show Commute k (w ψA) from ((mem_centralizer_iff.mp hkA) _ (w_mem ψA)).symm).zpow_right i
  have hkV : Commute k V :=
    (show Commute k (v ψB) from ((mem_centralizer_iff.mp hkB) _ (v_mem ψB)).symm).zpow_right j
  have hWV : Commute W V := (w_comm_v hco).zpow_zpow i j
  have hc1H := c1_mem_H7 hco
  have hcu7 : Commute (c1 ψA) u7 := by
    rw [hkij]
    have e1 : Commute (c1 ψA) k := (mem_centralizer_iff.mp hkA) _ (ψA.symm a450).2
    have e2 : Commute (c1 ψA) (w ψA) := mem_centralizer_singleton_iff.mp (mem_inf.mp hc1H).1
    have e3 : Commute (c1 ψA) (v ψB) := mem_centralizer_singleton_iff.mp (mem_inf.mp hc1H).2
    exact (e1.mul_right (e2.zpow_right i)).mul_right (e3.zpow_right j)
  have hx1 : xa ψA * u7 * (xa ψA)⁻¹ = u7⁻¹ := by
    have h1 : xa ψA * u7 * (xa ψA)⁻¹ = ((c1 ψA)⁻¹ * (cr ψB)⁻¹) ^ 2 := by
      rw [hu7, ← xa_conj_c1, ← xa_conj_cr hco]
      simp only [sq]
      group
    have h2 : ((c1 ψA)⁻¹ * (cr ψB)⁻¹) ^ 2 = (c1 ψA)⁻¹ * u7⁻¹ * c1 ψA := by
      rw [hu7]
      simp only [sq]
      group
    rw [h1, h2, mul_assoc, (hcu7.inv_right.symm).eq, inv_mul_cancel_left]
  have hx2 : xa ψA * u7 * (xa ψA)⁻¹ = k * W⁻¹ * V := by
    have e : ∀ a b : G, xa ψA * (a * b) * (xa ψA)⁻¹ =
        (xa ψA * a * (xa ψA)⁻¹) * (xa ψA * b * (xa ψA)⁻¹) := fun a b => by group
    rw [hkij, e, e, xa_conj_of_mem_centralizer hkA, hW, hV, ← conj_zpow, ← conj_zpow, xa_conj_w,
      xa_conj_v hco, inv_zpow]
  have hkV2 : k * k * (V * V) = 1 := by
    have h := hx1.symm.trans hx2
    rw [hkij] at h
    have h' : (k * W * V) * (k * W⁻¹ * V) = 1 := by rw [← h, mul_inv_cancel]
    have hc2 : W * V * k = k * (W * V) := ((hkW.mul_right hkV).symm).eq
    have hc3 : V * W⁻¹ = W⁻¹ * V := (hWV.inv_left.symm).eq
    calc k * k * (V * V) = k * (k * (W * V)) * W⁻¹ * V := by
          rw [show k * (k * (W * V)) * W⁻¹ * V = k * k * (W * (V * W⁻¹)) * V by group, hc3]
          group
      _ = k * (W * V * k) * W⁻¹ * V := by rw [hc2]
      _ = (k * W * V) * (k * W⁻¹ * V) := by group
      _ = 1 := h'
  have hVB : V ∈ B := zpow_mem (v_mem ψB) j
  have hkk : k * k = 1 := by
    have e : k * k = (V * V)⁻¹ := eq_inv_of_mul_eq_one_left hkV2
    exact eq_one_of_mem_of_mem_centralizer ψB (e ▸ inv_mem (mul_mem hVB hVB)) (mul_mem hkB hkB)
  have hk1 : k = 1 := by
    have hd2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hkk)
    have hko : Odd (orderOf k) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hk)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hko
      exact absurd hko (by decide)
  have hVV : V * V = 1 := by rw [hkk, one_mul] at hkV2; exact hkV2
  have hV1 : V = 1 := by
    have h3 : V ^ 3 = 1 := by
      rw [hV, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, v_pow_three,
        one_zpow]
    have h3' : V ^ 3 = V := by rw [pow_succ, sq, hVV, one_mul]
    rw [← h3', h3]
  have hu7W : u7 = W := by rw [hkij, hk1, hV1, one_mul, mul_one]
  have hy : y0 ψB * u7 * (y0 ψB)⁻¹ = u7 := by
    rw [hu7W, hW, ← conj_zpow, y0_conj_w hco]
  have hW3 : W ^ 3 = 1 := by
    rw [hW, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, w_pow_three, one_zpow]
  have hodd7 : Odd (orderOf u7) := by
    rw [hu7W]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hW3)
  exact eq_one_of_conj_inv hy0 y0_conj_cr hy hcu7.eq hodd7

end Seven

theorem AltPair.star_seven
    {G : Type} [Group G] [Finite G] {A B : Subgroup G} (hp : AltPair 7 A B) :
    ∃ (ψA : A ≃* alternatingGroup (Fin 7)) (ψB : B ≃* alternatingGroup (Fin 7)),
      AltCoords 7 A B ψA ψB ∧ ((ψA.symm a450 : G) * (ψB.symm a450 : G)) ^ 2 = 1 ∧
        (ψA.symm a456 : G) = (ψB.symm a456 : G) := by
  obtain ⟨ψA, ψB, hco⟩ := hp.exists_altCoords
  exact ⟨ψA, ψB, hco, Seven.star_seven hco hp.normalizer_le hp.centralizer_le_B hp.odd_inf,
    Seven.overlap hco hp.odd_inf⟩

end CFSG.ComponentClassification.RankTwoAlt
